{-# Language LambdaCase, GADTs, ImportQualifiedPost, BlockArguments, TypeFamilies, RankNTypes, PatternSynonyms, TypeOperators, MonadComprehensions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-|
Module      : Data.RME.What4
Description : What4 solver adapter for the RME backend.
Copyright   : (c) 2025 Galois
License     : BSD3
Maintainer  : cryptol@galois.com

This module implements a What4 solver adapter that translates What4 expressions
into RME (Reed–Muller expansion) terms and uses the RME backend for
symbolic reasoning.

Reference:
  * https://en.wikipedia.org/wiki/Reed–Muller_expansion

-}
module Data.RME.What4 (rmeAdapter) where

import Control.Monad (replicateM, ap, (<$!>))
import Data.BitVector.Sized qualified as BV
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Parameterized (TestEquality(..), TraversableFC(..), (::>), OrdF (compareF), OrderingF (..), type (:~:)(Refl), lexCompareF, joinOrderingF, fromOrdering, Pair (Pair))
import Data.Parameterized.Context (Assignment, pattern Empty, pattern (:>))
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.NatRepr ( NatRepr(..) )
import Data.Parameterized.Nonce qualified as Nonce
import Data.RME
import Data.Vector qualified as V
import What4.Expr.App qualified as W4
import What4.Expr.BoolMap qualified as W4
import What4.Expr.Builder qualified as W4
import What4.Expr.GroundEval qualified as W4
import What4.Expr.UnaryBV qualified as UnaryBV
import What4.Expr.WeightedSum qualified as Sum
import What4.Interface qualified as W4
import What4.SatResult qualified as W4
import What4.SemiRing qualified as W4
import What4.Solver

rmeAdapter :: SolverAdapter st
rmeAdapter =
  SolverAdapter
  { solver_adapter_name = "RME"
  , solver_adapter_config_options = []
  , solver_adapter_check_sat = rmeAdapterCheckSat
  , solver_adapter_write_smt2 = \_ _ _ -> pure ()
  }

rmeAdapterCheckSat ::
  W4.ExprBuilder t st fs ->
  LogData ->
  [W4.BoolExpr t] ->
  (SatResult (W4.GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) ->
  IO a
rmeAdapterCheckSat _ logger asserts k =
 do logCallback logger "Starting RME"
    let m = foldl conj true <$!> traverse evalExpr asserts
    case runM m of
      Left e ->
       do logCallback logger e
          putStrLn e
          k W4.Unknown
      Right (rme, s :: S t) ->
        case sat rme of
          Nothing -> k (W4.Unsat ())
          Just model ->
           do let trueVars = IntSet.fromList [i | (i, True) <- model]
                  evaluate = W4.GroundEvalFn (groundEval trueVars (nonceCache s))
              if checkConsistent trueVars MapF.empty (MapF.toList (abstracts s))
                then k (W4.Sat (evaluate, Nothing))
                else k Unknown

-- | The checks whether the point-wise definition of a symbolic function
-- was actually consistent in a satisfying model. It is possible that a
-- function can have different outputs for the same concrete inputs.
--
-- For example, if we find `f a` and `f b` in the term the system
-- will assign each of those fresh variables not knowing if they
-- if `a` and `b` might eventually be equal.
checkConsistent ::
  IntSet {- ^ Variables assigned true in the satisfying model -} ->
  MapF (ConcreteKey t) W4.GroundValueWrapper {- ^ Summary of previously checked function points -} ->
  [Pair (AbstractKey t) R'] {- ^ List of defined points in the function -} ->
  Bool
checkConsistent _ _ [] = True
checkConsistent trueVars seen (Pair (AbstractKey f argTys retTy args) v : rest) =
  case MapF.lookup k' seen of
    Nothing -> checkConsistent trueVars seen' rest
    Just old -> same retTy old v' && checkConsistent trueVars seen rest
  where
    k' = ConcreteKey f argTys (Ctx.zipWith (evalR trueVars) argTys args)
    v' = evalR trueVars retTy v
    seen' = MapF.insert k' v' seen

    same :: RMERepr a -> W4.GroundValueWrapper a -> W4.GroundValueWrapper a -> Bool
    same BitRepr (W4.GVW x) (W4.GVW y) = x == y
    same BVRepr{} (W4.GVW x) (W4.GVW y) = x == y

-- | Given a satisfying model compute the ground value of an RME term.
evalR :: IntSet -> RMERepr a -> R' a -> W4.GroundValueWrapper a
evalR trueVars BitRepr (R x) = W4.GVW (evalRME trueVars x)
evalR trueVars (BVRepr w) (R x) = W4.GVW (bitsToBV w (fmap (evalRME trueVars) x))

-- | Evaluate an RME term given the set of true variables.
evalRME :: IntSet -> RME -> Bool
evalRME trueVars x = eval x (`IntSet.member` trueVars)

-- | Ground evaluation function. Given a satisfying assignment (set of true variables)
-- this function will used the cached results to evaluate an expression.
groundEval :: IntSet -> MapF (Nonce.Nonce t) R' -> W4.Expr t tp -> IO (W4.GroundValue tp)
groundEval trueVars nonces e =
  case (flip MapF.lookup nonces =<< W4.exprMaybeId e, W4.exprType e) of
    (Just (R n), W4.BaseBoolRepr) -> pure $! evalRME trueVars n
    (Just (R n), W4.BaseBVRepr w) -> pure $! bitsToBV w (fmap (evalRME trueVars) n)
    _ -> W4.evalGroundExpr (groundEval trueVars nonces) e

-- | Build a 'BV' from a vector of booleans.
bitsToBV :: NatRepr w -> V.Vector Bool -> BV.BV w
bitsToBV w bs = BV.mkBV w (foldl (\acc x -> if x then 1 + acc*2 else acc*2) 0 bs)

-- | Evaluation is run in a context with a state, an error continuation, and a success continuation.
newtype M t a = M { unM :: forall k. S t -> (String -> k) -> (a -> S t -> k) -> k }

runM :: M t a -> Either String (a, S t)
runM m = unM m emptyS Left (curry Right)

instance Functor (M t) where
  fmap f (M m) = M (\s e k -> m s e (k . f))

instance Applicative (M t) where
  pure x = M (\s _ k -> k x s)
  (<*>) = ap

instance Monad (M t) where
  M m1 >>= f = M (\s0 e t -> m1 s0 e (\a s1 -> unM (f a) s1 e t))

instance MonadFail (M t) where
  fail str = M (\_ e _ -> e str)

-- | Get the current evaluation state
get :: M t (S t)
get = M (\s _ t -> t s s)

-- | Set the current evaluation state
set :: S t -> M t ()
set s = M (\_ _ t -> t () s)

-- | The state of evaluating an Expr into an RME term
data S t = S
  { nextVar :: !Int -- ^ next fresh variable to be used with RME lit
  , nonceCache :: !(MapF (Nonce.Nonce t) R') -- ^ previously translated w4 expressions
  , abstracts :: !(MapF (AbstractKey t) R') -- ^ previously assigned function applications
  }

-- | The application of a symbolic function to arguments in the RME domain.
data AbstractKey t ret where
  AbstractKey ::
    Nonce.Nonce t (args ::> ret) ->
    Assignment RMERepr args ->
    RMERepr ret ->
    Assignment R' args ->
    AbstractKey t ret

instance TestEquality (AbstractKey t) where
  testEquality (AbstractKey f ts_ _ xs_) (AbstractKey g _ _ ys_) =
    [Refl | Refl <- testEquality f g, Refl <- go ts_ xs_ ys_]
    where
      same :: RMERepr a -> R a -> R a -> Bool
      same BitRepr = (==)
      same BVRepr{} = (==)

      go :: Assignment RMERepr a -> Assignment R' a -> Assignment R' a -> Maybe (a :~: a)
      go Empty Empty Empty = Just Refl
      go (ts :> t) (xs :> R x) (ys :> R y) = [Refl | same t x y, Refl <- go ts xs ys]

instance OrdF (AbstractKey t) where
  compareF (AbstractKey f ts_ _ xs_) (AbstractKey g _ _ ys_) =
    lexCompareF f g (joinOrderingF (go ts_ xs_ ys_) EQF)
    where
      same :: RMERepr a -> R a -> R a -> OrderingF a a
      same BitRepr x y = fromOrdering (compare x y)
      same BVRepr{} x y = fromOrdering (compare x y)

      go :: Assignment RMERepr a -> Assignment R' a -> Assignment R' a -> OrderingF a a
      go Empty Empty Empty = EQF
      go (ts :> t) (xs :> R x) (ys :> R y) = joinOrderingF (same t x y) (joinOrderingF (go ts xs ys) EQF)

-- | The application of a symbolic function to concrete arguments.
data ConcreteKey t ret where
  ConcreteKey ::
    Nonce.Nonce t (args ::> ret) ->
    Assignment RMERepr args ->
    Assignment W4.GroundValueWrapper args ->
    ConcreteKey t ret

instance TestEquality (ConcreteKey t) where
  testEquality (ConcreteKey f ts_ xs_) (ConcreteKey g _ ys_) =
    [Refl | Refl <- testEquality f g, Refl <- go ts_ xs_ ys_]
    where
      same :: RMERepr a -> W4.GroundValue a -> W4.GroundValue a -> Bool
      same BitRepr = (==)
      same BVRepr{} = (==)

      go :: Assignment RMERepr a -> Assignment W4.GroundValueWrapper a -> Assignment W4.GroundValueWrapper a -> Maybe (a :~: a)
      go Empty Empty Empty = Just Refl
      go (ts :> t) (xs :> W4.GVW x) (ys :> W4.GVW y) = [Refl | same t x y, Refl <- go ts xs ys]

instance OrdF (ConcreteKey t) where
  compareF (ConcreteKey f ts_ xs_) (ConcreteKey g _ ys_) =
    lexCompareF f g (joinOrderingF (go ts_ xs_ ys_) EQF)
    where
      same :: RMERepr a -> W4.GroundValue a -> W4.GroundValue a -> OrderingF a a
      same BitRepr x y = fromOrdering (compare x y)
      same BVRepr{} x y = fromOrdering (compare x y)

      go :: Assignment RMERepr a -> Assignment W4.GroundValueWrapper a -> Assignment W4.GroundValueWrapper a -> OrderingF a a
      go Empty Empty Empty = EQF
      go (ts :> t) (xs :> W4.GVW x) (ys :> W4.GVW y) = joinOrderingF (same t x y) (joinOrderingF (go ts xs ys) EQF)

-- | The initial evaluation state
emptyS :: S t
emptyS = S
  { nextVar = 0
  , nonceCache = MapF.empty
  , abstracts = MapF.empty
  }

-- | Produce a fresh RME term
freshRME :: M t RME
freshRME =
 do s <- get
    if nextVar s == maxBound then
      fail "Fresh variables exhausted"
    else do
      set $! s{ nextVar = nextVar s + 1 }
      pure (lit (nextVar s))

-- | Map what4 base types to RME representations
type family R (t :: W4.BaseType) where
  R W4.BaseBoolType = RME
  R (W4.BaseBVType n) = RMEV

-- | Newtype wrapper for 'R' type for use with 'MapF'
newtype R' tp = R (R tp)

-- | Representation type use to determine which RME representation is being used
data RMERepr (t :: W4.BaseType) where
  -- | A single RME bit
  BitRepr :: RMERepr W4.BaseBoolType
  -- | A vector of w RME bits
  BVRepr  :: !(NatRepr w) -> RMERepr (W4.BaseBVType w)

-- | Helper for memoizing evaluation. Given a nonced and a way to evaluation
-- action this will either return the cached value for that nonce or
-- evaluate the given action and store it in the cache before returning it.
cached :: Nonce.Nonce t tp -> M t (R tp) -> M t (R tp)
cached nonce gen =
 do mb <- fmap (MapF.lookup nonce . nonceCache) get
    case mb of
      Just (R r) -> pure r
      Nothing ->
       do r <- gen
          s <- get
          set s{ nonceCache = MapF.insert nonce (R r) (nonceCache s) }
          pure r

-- | A version of what4's SemiRingRepr that matches the semi-rings that this backend supports
data SemiRingRepr sr where
  SemiRingRepr :: !(W4.BVFlavorRepr fv) -> !Int -> SemiRingRepr (W4.SemiRingBV fv w)

-- | Converts a BV width into the Int type used by Vector.
-- In the extreme case that the NatRepr is out of range of
-- Int, this operation will fail.
evalWidth :: NatRepr w -> M t Int
evalWidth w =
  let n = natValue w in
  if n > fromIntegral (maxBound :: Int)
    then fail "Bit-vector width too wide!"
    else pure (fromIntegral n)

-- | Convert a generic what4 base type to an RME base-type.
-- Reports an error for unsupported base types.
evalTypeRepr :: W4.BaseTypeRepr tp -> M t (RMERepr tp)
evalTypeRepr = \case
  W4.BaseBoolRepr -> pure BitRepr
  W4.BaseBVRepr w -> pure $! BVRepr w
  r -> fail ("RME does not support " ++ show r)

-- | Convert a generic what4 semiring type to an RME semiring type.
-- Reports an error for unsupported semiring types.
evalSemiRingRepr :: W4.SemiRingRepr sr -> M t (SemiRingRepr sr)
evalSemiRingRepr = \case
      W4.SemiRingIntegerRepr -> fail "RME does not support integers"
      W4.SemiRingRealRepr -> fail "RME does not support real numbers"
      W4.SemiRingBVRepr flv w ->
       do w' <- evalWidth w
          pure $! SemiRingRepr flv w'

-- | Evaluate an expression, if possible, into an RME term.
evalExpr :: W4.Expr t tp -> M t (R tp)
evalExpr = \case
  W4.BoolExpr x _ -> pure $! constant x
  W4.AppExpr x -> cached (W4.appExprId x) (evalApp (W4.appExprApp x))
  W4.BoundVarExpr x -> cached (W4.bvarId x) (allocateVar =<< evalTypeRepr (W4.bvarType x))
  W4.SemiRingLiteral rpr c _ ->
   do SemiRingRepr _ w <- evalSemiRingRepr rpr
      case c of
        BV.BV ci -> pure $! integer w ci
  W4.FloatExpr{} -> fail "RME does not support floating point numbers"
  W4.StringExpr{} -> fail "RME does not support string literals"
  W4.NonceAppExpr x -> cached (W4.nonceExprId x) (evalNonceApp (W4.nonceExprApp x))

-- | Evaluate a NonceApp expression. In most cases this will result in
-- failure with a message explaining what feature was unsupported.
evalNonceApp :: W4.NonceApp t (W4.Expr t) tp -> M t (R tp)
evalNonceApp = \case
  W4.Annotation _ _ e -> evalExpr e
  W4.Forall{} -> fail "RME does not support 'Forall' quantifiers"
  W4.Exists{} -> fail "RME does not support 'Exists' quantifiers"
  W4.ArrayFromFn{} -> fail "RME does not support symbolic 'ArrayFromFn' expressions"
  W4.MapOverArrays{} -> fail "RME does not support symbolic 'MapOverArrays' expressions"
  W4.ArrayTrueOnEntries{} -> fail "RME does not support symbolic 'ArrayTrueOnEntries' expressions"
  W4.FnApp fn args ->
   do args' <- traverseFC (\x -> R <$> evalExpr x) args
      argTypes <- traverseFC evalTypeRepr (W4.symFnArgTypes fn)
      retType <- evalTypeRepr (W4.symFnReturnType fn)
      let key = AbstractKey (W4.symFnId fn) argTypes retType args'
      mb <- fmap (MapF.lookup key . abstracts) get
      case mb of
        Just (R r) -> pure r
        Nothing ->
         do r <- allocateVar =<< evalTypeRepr (W4.symFnReturnType fn)
            s <- get
            set s{ abstracts = MapF.insert key (R r) (abstracts s) }
            pure r

-- | Allocates an unconstrainted RME term at the given type.
allocateVar :: RMERepr tp -> M t (R tp)
allocateVar = \case
  BitRepr -> freshRME
  BVRepr w ->
   do w' <- evalWidth w
      V.fromList <$!> replicateM w' freshRME

-- | Convert a what4 App into an RME term for the operations that the
-- RME backend supports.
evalApp :: W4.App (W4.Expr t) tp -> M t (R tp)
evalApp = \case

  W4.BaseEq rpr x y ->
   do x1 <- evalExpr x
      y1 <- evalExpr y
      r <- evalTypeRepr rpr
      pure $! case r of
        BitRepr -> iff x1 y1
        BVRepr{} -> eq x1 y1

  W4.BaseIte rpr _ b t e ->
   do b1 <- evalExpr b
      t1 <- evalExpr t
      e1 <- evalExpr e
      r <- evalTypeRepr rpr
      pure $! case r of
        BitRepr -> mux b1 t1 e1
        BVRepr{} -> V.zipWith (mux b1) t1 e1

  W4.NotPred x ->
   do x1 <- evalExpr x
      pure $! compl x1

  W4.ConjPred c ->
    case W4.viewConjMap c of
      W4.ConjTrue -> pure true
      W4.ConjFalse -> pure false
      W4.Conjuncts y ->
       do let f (x, W4.Positive) = evalExpr x
              f (x, W4.Negative) = compl <$!> evalExpr x
          foldl1 conj <$!> traverse f y

  W4.BVTestBit i ve ->
   do v <- evalExpr ve
      pure $! v V.! (length v - fromIntegral i - 1) -- little-endian index

  W4.BVSlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! slt x' y'

  W4.BVUlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! ult x' y'

  W4.BVConcat _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! x' <> y'

  W4.BVShl _ x y ->
    do x' <- evalExpr x
       y' <- evalExpr y
       pure $! shl x' y'

  W4.BVCountTrailingZeros _ v -> countTrailingZeros <$!> evalExpr v

  W4.BVCountLeadingZeros _ v -> countLeadingZeros <$!> evalExpr v

  W4.BVPopcount _ v -> popcount <$!> evalExpr v

  W4.BVOrBits w s ->
   do vs <- traverse evalExpr (W4.bvOrToList s)
      w' <- evalWidth w
      pure $! foldl (V.zipWith disj) (V.replicate w' false) vs

  W4.BVSelect i n v ->
   do v' <- evalExpr v
      i' <- evalWidth i
      n' <- evalWidth n
      let start = length v' - n' - i' -- i is given as a little endian index
      pure $! V.take n' (V.drop start v')

  W4.BVFill w b ->
   do w' <- evalWidth w
      b' <- evalExpr b
      pure $! V.replicate w' b'

  W4.BVLshr _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! lshr x' i'

  W4.BVAshr _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! ashr x' i'

  W4.BVRol _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! rol x' i'

  W4.BVRor _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! ror x' i'

  W4.BVZext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let l = w' - length v'
      pure (V.replicate l false <> v')

  W4.BVSext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let l = w' - length v'
      pure (V.replicate l (V.head v') <> v')

  W4.SemiRingSum s ->
   do SemiRingRepr flv w <- evalSemiRingRepr (Sum.sumRepr s)

      case flv of
        -- modular addition
        W4.BVArithRepr ->
          Sum.evalM
            (\x y -> pure $! add x y)
            (\(BV.BV c) r ->
             do v <- evalExpr r
                pure $! mul v (integer w c))
            (\(BV.BV c) -> pure $! integer w c)
            s

        -- bitwise xor
        W4.BVBitsRepr ->
          Sum.evalM
            (\x y -> pure $! V.zipWith xor x y)
            (\(BV.BV c) r ->
             do v <- evalExpr r
                pure $! V.zipWith conj (integer w c) v)
            (\(BV.BV c) -> pure $! integer w c)
            s

  W4.SemiRingProd p ->
   do SemiRingRepr flv w <- evalSemiRingRepr (Sum.prodRepr p)

      case flv of
      -- arithmetic multiplication
        W4.BVArithRepr ->
         do mb <- Sum.prodEvalM
              (\x y -> pure $! mul x y)
              evalExpr
              p
            pure $! case mb of
              Nothing -> integer w 1
              Just r -> r

        -- bitwise conjunction
        W4.BVBitsRepr ->
         do mb <- Sum.prodEvalM
                  (\x y -> pure $! V.zipWith conj x y)
                  evalExpr
                  p
            pure $! case mb of
              Nothing -> V.replicate w true -- ~0
              Just r -> r

  W4.BVUdiv _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! udiv x' y'

  W4.BVUrem _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! urem x' y'

  W4.BVSdiv _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! sdiv x' y'

  W4.BVSrem _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! srem x' y'

  W4.BVUnaryTerm u ->
   do let constEval x =
           do x' <- evalExpr x
              case isBool x' of
                Nothing -> fail "Unary term not constant"
                Just r -> pure r
      w' <- evalWidth (UnaryBV.width u)
      u' <- UnaryBV.evaluate constEval u
      pure $! integer w' u'

  e -> fail ("RME does not support " ++ show e)
