{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

private
  variable
    ℓC ℓC' : Level

open Precategory
open CatIso

module _ (C : Precategory ℓC ℓC') where

  open Precategory
  open CatIso

  idIso : (x : C .ob) → CatIso {C = C} x x
  idIso x .mor = id C x
  idIso x .inv = id C x
  idIso x .ret = ⋆IdR C (id C x)
  idIso x .sec = ⋆IdR C (id C x)

  compIso : {x y z : C .ob} → CatIso {C = C} x y → CatIso {C = C} y z → CatIso {C = C} x z
  compIso f g .mor = mor f ⋆⟨ C ⟩ mor g
  compIso f g .inv = inv g ⋆⟨ C ⟩ inv f
  compIso {x} {y} {z} f g .sec =
    (inv g ⋆⟨ C ⟩ inv f) ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ mor g)
         ≡⟨ ⋆Assoc C (inv g) (inv f) (mor f ⋆⟨ C ⟩ mor g) ⟩
    inv g ⋆⟨ C ⟩ (inv f ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ mor g))
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ f) (sym (⋆Assoc C (inv f) (mor f) (mor g))) ⟩
    inv g ⋆⟨ C ⟩ ((inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ mor g)
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ mor g)) (sec f) ⟩
    inv g ⋆⟨ C ⟩ (id C y ⋆⟨ C ⟩ mor g)
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ f) (⋆IdL C (mor g)) ⟩
    inv g ⋆⟨ C ⟩ mor g
        ≡⟨ sec g ⟩
    id C z ∎
    
  compIso {x} {y} {z} f g .ret = 
    (mor f ⋆⟨ C ⟩ mor g) ⋆⟨ C ⟩ (inv g ⋆⟨ C ⟩ inv f)
         ≡⟨ ⋆Assoc C (mor f) (mor g) (inv g ⋆⟨ C ⟩ inv f) ⟩
    mor f ⋆⟨ C ⟩ (mor g ⋆⟨ C ⟩ (inv g ⋆⟨ C ⟩ inv f))
        ≡⟨ cong (λ g →  mor f ⋆⟨ C ⟩ g) (sym (⋆Assoc C (mor g) (inv g) (inv f))) ⟩
    mor f ⋆⟨ C ⟩ ((mor g ⋆⟨ C ⟩ inv g) ⋆⟨ C ⟩ inv f)
        ≡⟨ cong (λ g → mor f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ inv f)) (ret g) ⟩
    mor f ⋆⟨ C ⟩ (id C y ⋆⟨ C ⟩ inv f)
        ≡⟨ cong (λ g → mor f ⋆⟨ C ⟩ g) (⋆IdL C (inv f)) ⟩
    mor f ⋆⟨ C ⟩ inv f
        ≡⟨ ret f ⟩
    id C x ∎

  syntax compIso f g = f ⋆ᵢ⟨ C ⟩ g

  module _ ⦃ isCatC : isCategory C ⦄ where
    makeIsoPath : {x y : C .ob} → (f g : CatIso {C = C} x y) → (mor f ≡ mor g) → f ≡ g
    makeIsoPath {x} {y} f g p = path
      where
      q : inv f ≡ inv g
      q = 
        inv f ≡⟨ sym (⋆IdR C (inv f)) ⟩
        inv f ⋆⟨ C ⟩ id C x ≡⟨ cong (λ g → inv f ⋆⟨ C ⟩ g) (sym (ret g)) ⟩
        inv f ⋆⟨ C ⟩ (mor g ⋆⟨ C ⟩ inv g) ≡⟨ sym (⋆Assoc C (inv f) (mor g) (inv g)) ⟩
        (inv f ⋆⟨ C ⟩ mor g) ⋆⟨ C ⟩ inv g ≡⟨ cong (λ h →  (inv f ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ inv g) (sym p) ⟩
        (inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ inv g ≡⟨ cong (λ f → f ⋆⟨ C ⟩ inv g) (sec f) ⟩
        (id C y) ⋆⟨ C ⟩ inv g ≡⟨ ⋆IdL C (inv g) ⟩
        inv g ∎
      
      path : f ≡ g
      path i .mor = p i
      path i .inv = q i
      path i .sec = rem i
        where
        rem : PathP (λ i → q i ⋆⟨ C ⟩ p i ≡ id C y) (sec f) (sec g)
        rem = toPathP (isSetHom isCatC _ _ _ _)
      path i .ret = rem i
        where
        rem : PathP (λ i → p i ⋆⟨ C ⟩ q i ≡ id C x) (ret f) (ret g)
        rem = toPathP (isSetHom isCatC _ _ _ _)

    module _ {x y : C .ob}
             (f : CatIso {C = C} x y) where

      invIso : CatIso {C = C} y x
      invIso .mor = inv f
      invIso .inv = mor f
      invIso .sec = ret f
      invIso .ret = sec f

      ⋆ᵢIdL : (idIso x) ⋆ᵢ⟨ C ⟩ f ≡ f
      ⋆ᵢIdL = makeIsoPath ((idIso x) ⋆ᵢ⟨ C ⟩ f) f (⋆IdL C (mor f))

      ⋆ᵢIdR : f ⋆ᵢ⟨ C ⟩ (idIso y) ≡ f
      ⋆ᵢIdR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ (idIso y)) f (⋆IdR C (mor f))

      ⋆ᵢInvL : invIso ⋆ᵢ⟨ C ⟩ f ≡ idIso y
      ⋆ᵢInvL = makeIsoPath (invIso ⋆ᵢ⟨ C ⟩ f) (idIso y) (sec f)

      ⋆ᵢInvR : f ⋆ᵢ⟨ C ⟩ invIso ≡ idIso x
      ⋆ᵢInvR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ invIso) (idIso x) (ret f)



