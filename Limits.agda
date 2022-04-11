{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Morphism

open import Cubical.Data.Sigma

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level

open Precategory
open Functor
open isLimit
open Limit
open NatTrans
open CatIso

hasLimitShape :  {ℓJ ℓJ' ℓC ℓC' : Level} → (J : Precategory ℓJ ℓJ') → (C : Precategory ℓC ℓC') → Type (ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓC) ℓC')
hasLimitShape J C = (F : Functor J C) → Limit F

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'}
         {F : Functor J C} where

  module _ (L : Limit F) where
  
    proj : (j : J .ob) → C [ head L , F ⟅ j ⟆ ]
    proj j = N-ob (cone (islim L)) j

    canonicalFact : {x : C .ob} → (c : Cone F x) → C [ x , head L ]
    canonicalFact c = fst (fst (up (islim L) c))

    defCanonicalFact : {j : J .ob} → {x : C .ob} → (c : Cone F x) → (canonicalFact c) ⋆⟨ C ⟩ proj j ≡ N-ob c j
    defCanonicalFact {j} {x} c = sym (cong (λ c → N-ob c j) factProof)
      where
      factProof : c ≡ (canonicalFact c) ◼ cone (islim L)
      factProof = snd (fst (up (islim L) c))


    inducedCone : {x : C .ob} → (f : C [ x , head L ]) → Cone F x
    inducedCone {x} f .N-ob j = f ⋆⟨ C ⟩ proj j
    inducedCone {x} f .N-hom {j} {j'} g =
      id C x ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ proj j')
           ≡⟨ ⋆IdL C (f ⋆⟨ C ⟩ proj j') ⟩
      f ⋆⟨ C ⟩ proj j'
           ≡⟨ cong (λ g → f ⋆⟨ C ⟩ g) (sym (⋆IdL C (proj j'))) ⟩
      f ⋆⟨ C ⟩ (id C (head L) ⋆⟨ C ⟩ proj j')
           ≡⟨ cong (λ g → f ⋆⟨ C ⟩ g) (N-hom (cone (islim L)) g) ⟩
      f ⋆⟨ C ⟩ (proj j ⋆⟨ C ⟩ F ⟪ g ⟫)
           ≡⟨ sym (⋆Assoc C f (proj j) (F ⟪ g ⟫) )⟩
      (f ⋆⟨ C ⟩ proj j) ⋆⟨ C ⟩ F ⟪ g ⟫ ∎

    module _ ⦃ isCatC : isCategory C ⦄ where

      carCanFact : {x : C .ob} → (c : Cone F x) → (f : C [ x , head L ])→ ((j : J .ob) → f ⋆⟨ C ⟩ proj j ≡ c .N-ob j) → f ≡ canonicalFact c
      carCanFact {x} c f compProj = sym (cong fst (snd (up (islim L) c) fact))
        where
        fact : cone (islim L) factors c
        fact = (f , makeNatTransPath (funExt (λ j → sym (compProj j))))

      canFactIndCone : {x : C .ob} → (f : C [ x , head L ]) → canonicalFact (inducedCone f) ≡ f
      canFactIndCone f = sym (carCanFact (inducedCone f) f λ j → refl)

      homToLimPath : {x : C .ob} → (f g : C [ x , head L ]) → ((j : J .ob) → f ⋆⟨ C ⟩ proj j ≡ g ⋆⟨ C ⟩ proj j) → f ≡ g
      homToLimPath {x} f g compProj = carCanFact (inducedCone g) f compProj ∙ canFactIndCone g
    
  unicityLim : ⦃ isCatC : isCategory C ⦄ → (L L' : Limit F) → CatIso {C = C} (head L) (head L')
  unicityLim L L' = isom
    where
    f : C [ head L , head L' ]
    f = canonicalFact L' (cone (islim L))
    g : C [ head L' , head L ]
    g = canonicalFact L (cone (islim L'))
    isom : CatIso {C = C} (head L) (head L')
    isom .mor = f
    isom .inv = g
    isom .sec = homToLimPath L' (g ⋆⟨ C ⟩ f) (id C (head L')) p
      where
      p : (j : J .ob) → (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ proj L' j ≡ id C (head L') ⋆⟨ C ⟩ proj L' j
      p j = 
        (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ proj L' j
           ≡⟨ ⋆Assoc C g f (proj L' j) ⟩
        g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ proj L' j)
           ≡⟨ cong (λ f → g ⋆⟨ C ⟩ f) (defCanonicalFact L' (cone (islim L))) ⟩
        g ⋆⟨ C ⟩ proj L j
           ≡⟨ defCanonicalFact L (cone (islim L')) ⟩
        proj L' j
           ≡⟨ sym (⋆IdL C (proj L' j)) ⟩
        id C (head L') ⋆⟨ C ⟩ proj L' j ∎
      
    isom .ret = homToLimPath L (f ⋆⟨ C ⟩ g) (id C (head L)) p
      where
      p : (j : J .ob) → (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ proj L j ≡ id C (head L) ⋆⟨ C ⟩ proj L j
      p j = 
        (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ proj L j
           ≡⟨ ⋆Assoc C f g (proj L j) ⟩
        f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ proj L j)
           ≡⟨ cong (λ g → f ⋆⟨ C ⟩ g) (defCanonicalFact L (cone (islim L'))) ⟩
        f ⋆⟨ C ⟩ proj L' j
           ≡⟨ defCanonicalFact L' (cone (islim L)) ⟩
        proj L j
           ≡⟨ sym (⋆IdL C (proj L j)) ⟩
        id C (head L) ⋆⟨ C ⟩ proj L j ∎
    
module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         (F : Functor J C)
         (G : Functor C D)
         (L : Limit F)
         (L' : Limit (G ∘F F)) where
         
  coneComp : Cone (G ∘F F) (G ⟅ head L ⟆)
  N-ob coneComp  j = G ⟪ N-ob (cone (islim L)) j ⟫
  N-hom coneComp {j} {j'} f =
    id D (G ⟅ head L ⟆) ⋆⟨ D ⟩ G ⟪ N-ob (cone (islim L)) j' ⟫
        ≡⟨ ⋆IdL D (G ⟪ N-ob (cone (islim L)) j' ⟫) ⟩
    G ⟪ N-ob (cone (islim L)) j' ⟫
        ≡⟨ cong (λ f → G ⟪ f ⟫) (sym (⋆IdL C (N-ob (cone (islim L)) j'))) ⟩
    G ⟪ id C (head L) ⋆⟨ C ⟩  N-ob (cone (islim L)) j' ⟫
        ≡⟨ cong (λ f → G ⟪ f ⟫) (N-hom (cone (islim L)) f) ⟩
    G ⟪ (N-ob (cone (islim L)) j) ⋆⟨ C ⟩  F ⟪ f ⟫ ⟫
        ≡⟨ F-seq G (N-ob (cone (islim L)) j) (F ⟪ f ⟫) ⟩
    G ⟪ N-ob (cone (islim L)) j ⟫ ⋆⟨ D ⟩ (G ⟪ F ⟪ f ⟫ ⟫) ∎
    
  canonicalMapComp : D [ G ⟅ head L ⟆ , head L' ]
  canonicalMapComp = canonicalFact L' coneComp

  preservLimit : Type ℓD'
  preservLimit = isIso {C = D} canonicalMapComp 

  
