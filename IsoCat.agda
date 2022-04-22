{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Precategory
open CatIso

module _ {C : Precategory ℓC ℓC'} where

  open Precategory
  open CatIso
  open Functor

  infix 30 _⦅_⦆
  _⦅_⦆ : {D : Precategory ℓD ℓD'} → {x y : C .ob} → (F : Functor C D) → (f : CatIso {C = C} x y) → CatIso {C = D} (F ⟅ x ⟆) (F ⟅ y ⟆)
  _⦅_⦆ F f .mor = F ⟪ mor f ⟫
  _⦅_⦆ F f .inv = F ⟪ inv f ⟫
  _⦅_⦆ {D = D} {y = y} F f .sec = 
    F ⟪ inv f ⟫ ⋆⟨ D ⟩ F ⟪ mor f ⟫ ≡⟨ sym (F-seq F (inv f) (mor f)) ⟩
    F ⟪ inv f ⋆⟨ C ⟩ mor f ⟫ ≡⟨ cong (λ f → F ⟪ f ⟫) (sec f) ⟩
    F ⟪ id C y ⟫ ≡⟨ F-id F ⟩
    id D (F ⟅ y ⟆) ∎
  _⦅_⦆ {D = D} {x = x} F f .ret = 
    F ⟪ mor f ⟫ ⋆⟨ D ⟩ F ⟪ inv f ⟫ ≡⟨ sym (F-seq F (mor f) (inv f)) ⟩
    F ⟪ mor f ⋆⟨ C ⟩ inv f ⟫ ≡⟨ cong (λ f → F ⟪ f ⟫) (ret f) ⟩
    F ⟪ id C x ⟫ ≡⟨ F-id F ⟩
    id D (F ⟅ x ⟆) ∎

  makeIso : {x y : C .ob} → (f : CatIso {C = C} x y) → (g : C [ x , y ]) → mor f ≡ g → isIso {C = C} g
  makeIso f g p = record { inv = inv f ; sec = cong (λ h → inv f ⋆⟨ C ⟩ h) (sym p) ∙ sec f ; ret = cong (λ h → h ⋆⟨ C ⟩ inv f) (sym p) ∙ ret f }

  idIso : (x : C .ob) → CatIso {C = C} x x
  idIso x .mor = id C x
  idIso x .inv = id C x
  idIso x .ret = ⋆IdL C (id C x)
  idIso x .sec = ⋆IdR C (id C x)

  invIso : {x y : C .ob} → CatIso {C = C} x y → CatIso {C = C} y x
  invIso f .mor = inv f
  invIso f .inv = mor f
  invIso f .sec = ret f
  invIso f .ret = sec f

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

seqIso : (C : Precategory ℓC ℓC') → {x y z : C .ob} → CatIso {C = C} x y → CatIso {C = C} y z → CatIso {C = C} x z
seqIso C f g = compIso {C = C} f g

infixl 15 seqIso
syntax seqIso C f g = f ⋆ᵢ⟨ C ⟩ g

module _ {C : Precategory ℓC ℓC'}
         ⦃ isCatC : isCategory C ⦄ where
         
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
      rem = isProp→PathP (λ i → isSetHom isCatC (q i ⋆⟨ C ⟩ p i) (id C y)) (sec f) (sec g)
    path i .ret = rem i
      where
      rem : PathP (λ i → p i ⋆⟨ C ⟩ q i ≡ id C x) (ret f) (ret g)
      rem = isProp→PathP (λ i → isSetHom isCatC (p i ⋆⟨ C ⟩ q i) (id C x)) (ret f) (ret g)
      
  module _ {x y : C .ob}
           (f : CatIso {C = C} x y) where

    ⋆ᵢIdL : (idIso x) ⋆ᵢ⟨ C ⟩ f ≡ f
    ⋆ᵢIdL = makeIsoPath ((idIso x) ⋆ᵢ⟨ C ⟩ f) f (⋆IdL C (mor f))

    ⋆ᵢIdR : f ⋆ᵢ⟨ C ⟩ (idIso y) ≡ f
    ⋆ᵢIdR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ (idIso y)) f (⋆IdR C (mor f))

    ⋆ᵢInvL : invIso f ⋆ᵢ⟨ C ⟩ f ≡ idIso y
    ⋆ᵢInvL = makeIsoPath (invIso f ⋆ᵢ⟨ C ⟩ f) (idIso y) (sec f)

    ⋆ᵢInvR : f ⋆ᵢ⟨ C ⟩ invIso f ≡ idIso x
    ⋆ᵢInvR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ invIso f) (idIso x) (ret f)

module _ {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄
         (F : Functor C D) where
  open Functor

  iso-F-id : {x : C .ob} → F ⦅ idIso x ⦆ ≡ idIso (F ⟅ x ⟆)
  iso-F-id {x} = makeIsoPath (F ⦅ idIso x ⦆) (idIso (F ⟅ x ⟆)) (F-id F)

  iso-F-seq : {x y z : C .ob} → (f : CatIso {C = C} x y) → (g : CatIso {C = C} y z) → F ⦅ f ⋆ᵢ⟨ C ⟩ g ⦆ ≡ F ⦅ f ⦆ ⋆ᵢ⟨ D ⟩ F ⦅ g ⦆
  iso-F-seq f g = makeIsoPath (F ⦅ f ⋆ᵢ⟨ C ⟩ g ⦆) (F ⦅ f ⦆ ⋆ᵢ⟨ D ⟩ F ⦅ g ⦆) (F-seq F (mor f) (mor g))

  iso-F-inv : {x y : C .ob} → (f : CatIso {C = C} x y) → F ⦅ invIso f ⦆ ≡ invIso (F ⦅ f ⦆)
  iso-F-inv f = makeIsoPath (F ⦅ invIso f ⦆) (invIso (F ⦅ f ⦆)) refl




