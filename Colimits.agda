{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.SumFin using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Limits

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level
    ℓ ℓ' ℓ'' : Level

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'} where
  open Precategory
  open Limit

  Cocone : (F : Functor J C) → C .ob → Type _
  Cocone F x = Cone (F ^opF) x

  module _ (F : Functor J C) where

    isColimit : (tail : C .ob) → Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))
    isColimit tail = isLimit (F ^opF) tail

    Colimit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))
    Colimit = Limit (F ^opF)
  
  coproj = proj


module _ where
  open Precategory

  discreteFinCat : (n : ℕ) → Precategory ℓ-zero ℓ-zero
  discreteFinCat zero = ⊥-cat
    where
    ⊥-cat : Precategory ℓ-zero ℓ-zero
    ⊥-cat .ob = ⊥
    
  discreteFinCat (suc n) = sucCat
    where
    C = discreteFinCat n
    sucCat : Precategory ℓ-zero ℓ-zero
    sucCat .ob = (C .ob) ⊎ ⊤
    sucCat .Hom[_,_] (inl x) (inl y) = C [ x , y ]
    sucCat .Hom[_,_] (inl x) (inr tt) = ⊥
    sucCat .Hom[_,_] (inr tt) (inl y) = ⊥
    sucCat .Hom[_,_] (inr tt) (inr tt) = ⊤
    sucCat .id (inl x) = C .id x
    sucCat .id (inr tt) = tt
    sucCat ._⋆_ {inl x} {inl y} {inl z} f g =  f ⋆⟨ C ⟩ g
    sucCat ._⋆_ {inr tt} {inr tt} {inr tt} tt tt = tt
    sucCat .⋆IdL {inl x} {inl y} f = C .⋆IdL f
    sucCat .⋆IdL {inr tt} {inr tt} tt = refl
    sucCat .⋆IdR {inl x} {inl y} f = C .⋆IdR f
    sucCat .⋆IdR {inr tt} {inr tt} tt = refl
    sucCat .⋆Assoc {inl w} {inl x} {inl y} {inl z} f g h = C .⋆Assoc f g h
    sucCat .⋆Assoc {inr tt} {inr tt} {inr tt} {inr tt} tt tt tt = refl

  isCategoryDisceteFinCat : {n : ℕ} → isCategory (discreteFinCat n)
  isCategoryDisceteFinCat {zero} .isSetHom {()}
  isCategoryDisceteFinCat {suc n} .isSetHom {inl x} {inl y} = isCategoryDisceteFinCat {n} .isSetHom
  isCategoryDisceteFinCat {suc n} .isSetHom {inl x} {inr tt} = isProp→isSet isProp⊥
  isCategoryDisceteFinCat {suc n} .isSetHom {inr tt} {inl y} =  isProp→isSet isProp⊥
  isCategoryDisceteFinCat {suc n} .isSetHom {inr tt} {inr tt} = isSetUnit

  ⊥-cat = discreteFinCat 0
  ⊤+⊤-cat = discreteFinCat 2

  -- Category with 2 objects and 2 parallel arrows
  ⊤+⊤-parallel-cat : Precategory ℓ-zero ℓ-zero
  ⊤+⊤-parallel-cat .ob = ⊤ ⊎ ⊤
  ⊤+⊤-parallel-cat .Hom[_,_] (inl tt) (inl tt) = ⊤
  ⊤+⊤-parallel-cat .Hom[_,_] (inl tt) (inr tt) = ⊤ ⊎ ⊤
  ⊤+⊤-parallel-cat .Hom[_,_] (inr tt) (inl tt) = ⊥
  ⊤+⊤-parallel-cat .Hom[_,_] (inr tt) (inr tt) = ⊤
  ⊤+⊤-parallel-cat .id (inl tt) = tt
  ⊤+⊤-parallel-cat .id (inr tt) = tt
  _⋆_ ⊤+⊤-parallel-cat {inl tt} {inl tt} {z} tt f = f
  _⋆_ ⊤+⊤-parallel-cat {inl tt} {inr tt} {inr tt} f tt = f
  _⋆_ ⊤+⊤-parallel-cat {inr tt} {inr tt} {inr tt} tt tt = tt
  ⊤+⊤-parallel-cat .⋆IdL {inl tt} {inl tt} tt = refl
  ⊤+⊤-parallel-cat .⋆IdL {inl tt} {inr tt} f = refl
  ⊤+⊤-parallel-cat .⋆IdL {inr tt} {inr tt} tt = refl
  ⊤+⊤-parallel-cat .⋆IdR {inl tt} {inl tt} tt = refl
  ⊤+⊤-parallel-cat .⋆IdR {inl tt} {inr tt} f = refl
  ⊤+⊤-parallel-cat .⋆IdR {inr tt} {inr tt} tt = refl
  ⊤+⊤-parallel-cat .⋆Assoc {inl tt} {inl tt} {y} {z} tt g h = refl
  ⊤+⊤-parallel-cat .⋆Assoc {inl tt} {inr tt} {inr tt} {inr tt} f tt tt = refl
  ⊤+⊤-parallel-cat .⋆Assoc {inr tt} {inr tt} {inr tt} {inr tt} tt tt tt = refl

  isCategory-⊤+⊤-par : isCategory ⊤+⊤-parallel-cat
  isCategory-⊤+⊤-par .isSetHom {inl tt} {inl x} = isSetUnit
  isCategory-⊤+⊤-par .isSetHom {inl tt} {inr x} = isSet⊎ isSetUnit isSetUnit
  isCategory-⊤+⊤-par .isSetHom {inr tt} {inr tt} = isSetUnit

  hasCocones-⊥ = {ℓC ℓC' : Level} → (C : Precategory ℓC ℓC') → (K : Functor ⊥-cat C) → Colimit K
  hasCocones-⊤+⊤ = {ℓC ℓC' : Level} → (C : Precategory ℓC ℓC') → (K : Functor ⊤+⊤-cat C) → Colimit K
  hasCocones-⊤+⊤-par = {ℓC ℓC' : Level} → (C : Precategory ℓC ℓC') → (K : Functor ⊤+⊤-parallel-cat C) → Colimit K

  module _ (C : Precategory ℓC ℓC') where

    record isFilteredCategory : Type (ℓ-max ℓC ℓC') where
      field
        cocones-⊥ : (K : Functor ⊥-cat C) → Colimit K
        cocones-⊤+⊤ : (K : Functor ⊤+⊤-cat C) → Colimit K
        cocones-⊤+⊤-par : (K : Functor ⊤+⊤-parallel-cat C) → Colimit K


  record filteredCategory : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    field
      cat : Precategory ℓ ℓ'
      isfiltered : isFilteredCategory cat

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'}
         (K : Functor J C) where

  open filteredCategory
  
  record filteredColimit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC')) where
      field
        colim : Colimit K
        isFilCat : isFilteredCategory J
        

