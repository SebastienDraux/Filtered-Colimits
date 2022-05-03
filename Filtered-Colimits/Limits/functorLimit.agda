module Filtered-Colimits.Limits.functorLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits
open import Cubical.Categories.Morphism
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.Category.Functors
open import Filtered-Colimits.Category.NatTransfo
open import Filtered-Colimits.Limits.Limits
open import Filtered-Colimits.Limits.Colimits

private
  variable
    ℓJ ℓJ' ℓC ℓC' : Level

open Category
open NatTrans
open Functor
open Cone
open LimCone
open CatIso
    
module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         (limit : LimitsOfShape J C) where
         
  functLim : Functor (FUNCTOR J C) C
  functLim .F-ob F = lim (limit F)
  functLim .F-hom {F} {G} α = limOfArrows F G (limit F) (limit G) (N-ob α) (λ f → sym (N-hom α f))
  functLim .F-id {F} = limArrowUnique (limit F) (lim (limit F)) _ (id C) (λ j → ⋆IdL C (limOut (limit F) j) ∙ sym (⋆IdR C (limOut (limit F) j)))
  functLim .F-seq {F} {G} {H} α β = limArrowUnique (limit H) (lim (limit F)) _ ((F-hom functLim α) ⋆⟨ C ⟩ (F-hom functLim β)) eq
      where
      eq : (j : ob J) → ((F-hom functLim α) ⋆⟨ C ⟩ (F-hom functLim β)) ⋆⟨ C ⟩ limOut (limit H) j ≡ (limOut (limit F) j) ⋆⟨ C ⟩ (α ⟦ j ⟧ ⋆⟨ C ⟩ β ⟦ j ⟧)
      eq j = 
        (F-hom functLim α ⋆⟨ C ⟩ (F-hom functLim β)) ⋆⟨ C ⟩ limOut (limit H) j
          ≡⟨ ⋆Assoc C (F-hom functLim α) (F-hom functLim β) (limOut (limit H) j) ⟩
        F-hom functLim α ⋆⟨ C ⟩ ((F-hom functLim β) ⋆⟨ C ⟩ limOut (limit H) j)
          ≡⟨ cong (λ f → (F-hom functLim α) ⋆⟨ C ⟩ f) (limArrowCommutes (limit H) (lim (limit G)) _ j) ⟩
        F-hom functLim α ⋆⟨ C ⟩ (limOut (limit G) j ⋆⟨ C ⟩ β ⟦ j ⟧)
          ≡⟨ sym (⋆Assoc C (F-hom functLim α) (limOut (limit G) j) (β ⟦ j ⟧)) ⟩
        (F-hom functLim α ⋆⟨ C ⟩ limOut (limit G) j) ⋆⟨ C ⟩ β ⟦ j ⟧
          ≡⟨ cong (λ f → f ⋆⟨ C ⟩ β ⟦ j ⟧) (limArrowCommutes (limit G) (lim (limit F)) _ j) ⟩
        (limOut (limit F) j ⋆⟨ C ⟩ α ⟦ j ⟧) ⋆⟨ C ⟩ β ⟦ j ⟧
          ≡⟨ ⋆Assoc C (limOut (limit F) j) (α ⟦ j ⟧) (β ⟦ j ⟧) ⟩
        limOut (limit F) j ⋆⟨ C ⟩ (α ⟦ j ⟧ ⋆⟨ C ⟩ β ⟦ j ⟧) ∎

  functLimLimCone : (F : Functor J C) → LimCone F
  functLimLimCone F = limit F

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         (colim : ColimitsOfShape J C) where

  functColim : Functor (FUNCTOR J C) C
  functColim  = Colim
    where
    fLim = functLim (equivFun (ColimShape≃LimShape^op J C) colim)
    
    Colim : Functor (FUNCTOR J C) C
    Colim .F-ob F = fLim ⟅ F ^opF ⟆
    Colim .F-hom {F} {G} α = fLim ⟪ α ^opN ⟫
    Colim .F-id {F} = cong (λ α → fLim ⟪ α ⟫) (^opN-id F) ∙ F-id fLim
    Colim .F-seq {F} {G} {H} α β = cong (λ α → fLim ⟪ α ⟫) (^opN-seq α β) ∙ F-seq fLim (β ^opN) (α ^opN)

  functColimColimCone : (F : Functor J C) → ColimCone F
  functColimColimCone F = functLimLimCone (equivFun (ColimShape≃LimShape^op J C) colim) (F ^opF)
