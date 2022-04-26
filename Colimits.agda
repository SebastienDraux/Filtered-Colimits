{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits
open import Cubical.Categories.Instances.Discrete

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Limits

open Category
open Iso

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level
    ℓ ℓ' : Level

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'} where

  Cocone : (F : Functor J C) → C .ob → Type _
  Cocone F x = Cone (F ^opF) x

  module _ (F : Functor J C) where

    ColimCone : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC'))
    ColimCone = LimCone (F ^opF)

ColimitsOfShape : Category ℓJ ℓJ' → Category ℓC ℓC' → Type (ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓC) ℓC')
ColimitsOfShape J C = (F : Functor J C) → ColimCone F

ColimShape≃LimShape^op : (J : Category ℓJ ℓJ') → (C : Category ℓC ℓC') →  ColimitsOfShape J C ≃ LimitsOfShape (J ^op) (C ^op)
ColimShape≃LimShape^op J C = isoToEquiv isom
  where
  isom : Iso (ColimitsOfShape J C) (LimitsOfShape (J ^op) (C ^op))
  isom .fun colimit F = colimit (F ^opF)
  isom .inv limit F = limit (F ^opF)
  isom .leftInv colimit = funExt (λ F → refl)
  isom .rightInv limit = funExt (λ F → refl)

module _ where

  terminalShape : Category ℓ-zero ℓ-zero
  terminalShape = DiscreteCategory (⊤ , isOfHLevelUnit 3)

  binProdShape : Category ℓ-zero ℓ-zero
  binProdShape = DiscreteCategory ((⊤ ⊎ ⊤) , isOfHLevel⊎ 1 (isOfHLevelUnit 3) (isOfHLevelUnit 3))

  equalizerShape : Category ℓ-zero ℓ-zero
  equalizerShape .ob = ⊤ ⊎ ⊤
  equalizerShape .Hom[_,_] (inl tt) (inl tt) = ⊤
  equalizerShape .Hom[_,_] (inl tt) (inr tt) = ⊤ ⊎ ⊤
  equalizerShape .Hom[_,_] (inr tt) (inl tt) = ⊥
  equalizerShape .Hom[_,_] (inr tt) (inr tt) = ⊤
  equalizerShape .id {inl x} = tt
  equalizerShape .id {inr x} = tt
  equalizerShape ._⋆_ {inl tt} {inl tt} {z} tt f = f
  equalizerShape ._⋆_ {inl tt} {inr tt} {inr tt} f tt = f
  equalizerShape ._⋆_ {inr tt} {inr tt} {inr tt} tt tt = tt
  equalizerShape .⋆IdL {inl tt} {inl tt} tt = refl
  equalizerShape .⋆IdL {inl tt} {inr tt} f = refl
  equalizerShape .⋆IdL {inr tt} {inr tt} tt = refl
  equalizerShape .⋆IdR {inl tt} {inl tt} tt = refl
  equalizerShape .⋆IdR {inl tt} {inr tt} f = refl
  equalizerShape .⋆IdR {inr tt} {inr tt} tt = refl
  equalizerShape .⋆Assoc {inl tt} {inl tt} {y} {z} tt g h = refl
  equalizerShape .⋆Assoc {inl tt} {inr tt} {inr tt} {inr tt} f tt tt = refl
  equalizerShape .⋆Assoc {inr tt} {inr tt} {inr tt} {inr tt} tt tt tt = refl
  equalizerShape .isSetHom {inl tt} {inl tt} = isSetUnit
  equalizerShape .isSetHom {inl tt} {inr tt} = isSet⊎ isSetUnit isSetUnit
  equalizerShape .isSetHom {inr tt} {inl tt} = isProp→isSet isProp⊥
  equalizerShape .isSetHom {inr tt} {inr tt} = isSetUnit

  record isFilteredCategory (C : Category ℓC ℓC') : Type (ℓ-max ℓC ℓC') where
    field
      coconeTerminalShape : (F : Functor terminalShape C) → Σ[ x ∈ ob C ] Cocone F x
      coconeBinProdShape : (F : Functor binProdShape C) → Σ[ x ∈ ob C ] Cocone F x
      coconeEqualizerShape : (F : Functor equalizerShape C) → Σ[ x ∈ ob C ] Cocone F x

  record filteredCategory : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    field
      cat : Category ℓ ℓ'
      isFilteredCat : isFilteredCategory cat

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         (F : Functor J C) where

  open filteredCategory
  
  record filteredColimit : Type (ℓ-max (ℓ-max ℓJ ℓJ') (ℓ-max ℓC ℓC')) where
      field
        colimit : ColimCone F
        isFilteredColim : isFilteredCategory J
        

