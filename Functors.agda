{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    E : Precategory ℓE ℓE'

open Functor
open Precategory

^opF-invol : {C : Precategory ℓC ℓC'} → {D : Precategory ℓD ℓD'} → (F : Functor C D) → (F ^opF) ^opF ≡ F
^opF-invol F i .F-ob = F-ob F
^opF-invol F i .F-hom = F-hom F
^opF-invol F i .F-id = F-id F
^opF-invol F i .F-seq = F-seq F

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


  


  
  
