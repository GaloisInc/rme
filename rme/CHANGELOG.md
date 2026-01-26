# Revision history for rme

## 0.1.2 -- 2026-01-26

* Added partial support for arrays returned from symbolic functions.
  Expressions must be exactly of the form: `select (f args) ix`. This is
  used to support the translation of uninterpreted functions new in
  SAW.

* Added support for concrete integers as needed for SAW's above translation
  used to index the symbolic array results.

## 0.1.1

* Added `Ord` instance for `RME`

## 0.1

* First version.
