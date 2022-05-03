module Filtered-Colimits.Category.NatTransfo where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Morphism


private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open NatTrans
open Functor
open CatIso
open NatIso
open isIso

_^opN : {C : Category ℓC ℓC'} → {D : Category ℓD ℓD'} → {F G : Functor C D} → NatTrans F G → NatTrans (G ^opF) (F ^opF)
_^opN α .N-ob j = α ⟦ j ⟧
_^opN α .N-hom f = sym (N-hom α f)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  ^opN-id : (F : Functor C D) → (idTrans F) ^opN ≡ idTrans (F ^opF)
  ^opN-id F = makeNatTransPath (funExt (λ x → refl))

  ^opN-seq : {F G H : Functor C D} → (α : NatTrans F G) → (β : NatTrans G H) → (α ●ᵛ β) ^opN ≡ (β ^opN) ●ᵛ (α ^opN)
  ^opN-seq α β = makeNatTransPath (funExt (λ x → refl))

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
         
  natIso→FUNCatIso : {F G : Functor C D} → NatIso F G → CatIso (FUNCTOR C D) F G
  natIso→FUNCatIso α .mor = trans α
  natIso→FUNCatIso α .inv .N-ob x = inv (nIso α x)
  natIso→FUNCatIso {F} {G} α .inv .N-hom {x} {y} f = 
    G ⟪ f ⟫ ⋆⟨ D ⟩ inv (nIso α y)                                                           ≡⟨ sym (⋆IdL D _) ⟩
    id D ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ inv (nIso α y))                                             ≡⟨ cong (λ g → g ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ inv (nIso α y)) ) (sym (sec (nIso α x))) ⟩
    (inv (nIso α x) ⋆⟨ D ⟩ trans α ⟦ x ⟧) ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ inv (nIso α y))            ≡⟨ ⋆Assoc D _ _ _ ⟩
    inv (nIso α x) ⋆⟨ D ⟩ (trans α ⟦ x ⟧ ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ inv (nIso α y)))            ≡⟨ cong (λ g → inv (nIso α x) ⋆⟨ D ⟩ g) (sym (⋆Assoc D _ _ _)) ⟩
    inv (nIso α x) ⋆⟨ D ⟩ ((trans α ⟦ x ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫) ⋆⟨ D ⟩ inv (nIso α y))            ≡⟨ cong (λ g → inv (nIso α x) ⋆⟨ D ⟩ (g ⋆⟨ D ⟩ inv (nIso α y))) (sym (N-hom (trans α) f)) ⟩
    inv (nIso α x) ⋆⟨ D ⟩ ((F ⟪ f ⟫ ⋆⟨ D ⟩ trans α ⟦ y ⟧) ⋆⟨ D ⟩ inv (nIso α y))            ≡⟨ cong (λ g → inv (nIso α x) ⋆⟨ D ⟩ g) (⋆Assoc D _ _ _) ⟩
    inv (nIso α x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ (trans α ⟦ y ⟧ ⋆⟨ D ⟩ inv (nIso α y)))            ≡⟨ cong (λ g → inv (nIso α x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ g)) (ret (nIso α y)) ⟩
    inv (nIso α x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ id D)                                             ≡⟨ cong (λ g → inv (nIso α x) ⋆⟨ D ⟩ g) (⋆IdR D _) ⟩
    inv (nIso α x) ⋆⟨ D ⟩ F ⟪ f ⟫                                                            ∎
    
  natIso→FUNCatIso α .sec = makeNatTransPath (funExt (λ x → sec (nIso α x)))
  natIso→FUNCatIso α .ret = makeNatTransPath (funExt (λ x → ret (nIso α x)))

  FUNCatIso→natIso : {F G : Functor C D} → CatIso (FUNCTOR C D) F G → NatIso F G
  FUNCatIso→natIso α .trans = mor α
  FUNCatIso→natIso α .nIso x .inv = (inv α) ⟦ x ⟧
  FUNCatIso→natIso α .nIso x .sec = cong (λ α → α ⟦ x ⟧) (sec α)
  FUNCatIso→natIso α .nIso x .ret = cong (λ α → α ⟦ x ⟧) (ret α)
