{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open NatTrans
open Functor

_^opN : {C : Category ℓC ℓC'} → {D : Category ℓD ℓD'} → {F G : Functor C D} → NatTrans F G → NatTrans (G ^opF) (F ^opF)
_^opN α .N-ob j = α ⟦ j ⟧
_^opN α .N-hom f = sym (N-hom α f)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  ^opN-id : (F : Functor C D) → (idTrans F) ^opN ≡ idTrans (F ^opF)
  ^opN-id F = makeNatTransPath (funExt (λ x → refl))

  ^opN-seq : {F G H : Functor C D} → (α : NatTrans F G) → (β : NatTrans G H) → (α ●ᵛ β) ^opN ≡ (β ^opN) ●ᵛ (α ^opN)
  ^opN-seq α β = makeNatTransPath (funExt (λ x → refl))
