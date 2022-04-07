{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level

module _ (C : Precategory ℓC ℓC')
         (isCatC : isCategory C) where
  open Precategory

  isCatOp : isCategory (C ^op)
  isCatOp .isSetHom = isSetHom isCatC
