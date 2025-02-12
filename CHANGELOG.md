# Revision history for data-elevator

## ?.? -- ????-??-??

* Added support for GHC version 9.12

## 0.2 -- 2024-09-16

No changes to the API, but a significant change to the conversion functions.

* Fix issue #4, which makes `toStrict#` and `fromLazy#` NOINLINE.
  We now have rewrite rules to cancel away, e.g., `fromStrict# . toStrict# = id`.
  This is expected to be a bit more brittle performance-wise compared to the
  0.1.*, but it fixes a major soundness bug (#4).

## 0.1.0.2 -- 2024-08-02

* Added support for GHC versions 9.6, 9.8, and 9.10


## 0.1.0.0 -- 2022-07-31

* First version
