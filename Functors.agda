{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    E : Precategory ℓE ℓE'

open Functor
open Precategory

module _ {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         (F : Functor C D) where
         
  ^opF-invol : (F ^opF) ^opF ≡ F
  ^opF-invol i .F-ob = F-ob F
  ^opF-invol i .F-hom = F-hom F
  ^opF-invol i .F-id = F-id F
  ^opF-invol i .F-seq = F-seq F

  module _ (P : Functor C D → Type ℓ) where

    elim-^opF : P ((F ^opF) ^opF) → P F
    elim-^opF = subst P ^opF-invol

    intro-^opF : P F → P ((F ^opF) ^opF)
    intro-^opF = subst P (sym ^opF-invol)

    --elim-intro-^opF : (p : P F) → elim-^opF (intro-^opF p) ≡ p
    --elim-intro-^opF p = {!!} ∙ cong (λ q → subst P q p) (lCancel ^opF-invol) ∙ substRefl {B = P} p

^opF-id : (𝟙⟨ C ⟩) ^opF ≡ 𝟙⟨ C ^op ⟩
^opF-id i .F-ob x = x
^opF-id i .F-hom f = f
^opF-id i .F-id = refl
^opF-id i .F-seq f g = refl

^opF-seq : (F : Functor C D) → (G : Functor D E) → (G ∘F F) ^opF ≡ (G ^opF) ∘F (F ^opF)
^opF-seq F G i .F-ob x = G ⟅ F ⟅ x ⟆ ⟆
^opF-seq F G i .F-hom f = G ⟪ F ⟪ f ⟫ ⟫
^opF-seq F G i .F-id = cong (λ f → G ⟪ f ⟫) (F-id F) ∙ F-id G
^opF-seq F G i .F-seq f g = cong (λ f → G ⟪ f ⟫) (F-seq F g f) ∙ F-seq G (F ⟪ g ⟫) (F ⟪ f ⟫)


  


  
  
