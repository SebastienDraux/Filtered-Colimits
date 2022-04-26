{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits
open import Cubical.Categories.Morphism

open import Cubical.Data.Sigma

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open Cone
open LimCone
open NatTrans
open CatIso


module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         {F : Functor J C} where
         
  _■_ : {x y : ob C} → (f : C [ x , y ]) → Cone F y → Cone F x
  _■_ f cc .coneOut j = f ⋆⟨ C ⟩ coneOut cc j
  _■_ f cc .coneOutCommutes {j} {j'} g = 
    (f ⋆⟨ C ⟩ coneOut cc j) ⋆⟨ C ⟩ F ⟪ g ⟫
      ≡⟨ ⋆Assoc C f (coneOut cc j) (F ⟪ g ⟫) ⟩
    f ⋆⟨ C ⟩ (coneOut cc j ⋆⟨ C ⟩ F ⟪ g ⟫)
      ≡⟨ cong (λ g → f ⋆⟨ C ⟩ g) (coneOutCommutes cc g) ⟩
    f ⋆⟨ C ⟩ coneOut cc j' ∎

  module _ (L : LimCone F) where
  
    morToLimPath : {x : C .ob} → (f g : C [ x , lim L ]) → ((j : J .ob) → f ⋆⟨ C ⟩ limOut L j ≡ g ⋆⟨ C ⟩ limOut L j) → f ≡ g
    morToLimPath {x} f g compProj = 
      f
        ≡⟨ sym (limArrowUnique L x (g ■ limCone L) f compProj) ⟩
     limArrow L x (g ■ limCone L)
       ≡⟨ limArrowUnique L x (g ■ limCone L) g (λ j → refl) ⟩
     g ∎ 
    
 -- unicityLim : ⦃ isCatC : isCategory C ⦄ → (L L' : Limit F) → CatIso {C = C} (head L) (head L')
--  unicityLim L L' = isom
 --   where
 --   f : C [ head L , head L' ]
 --   f = canonicalFact L' (cone (islim L))
 --   g : C [ head L' , head L ]
 --   g = canonicalFact L (cone (islim L'))
 --   isom : CatIso {C = C} (head L) (head L')
 --   isom .mor = f
 --   isom .inv = g
 --   isom .sec = homToLimPath L' (g ⋆⟨ C ⟩ f) (id C (head L')) p
 --     where
  --    p : (j : J .ob) → (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ proj L' j ≡ id C (head L') ⋆⟨ C ⟩ proj L' j
  --    p j = 
  --      (g ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ proj L' j
   --        ≡⟨ ⋆Assoc C g f (proj L' j) ⟩
  --      g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ proj L' j)
   --        ≡⟨ cong (λ f → g ⋆⟨ C ⟩ f) (defCanonicalFact L' (cone (islim L))) ⟩
--        g ⋆⟨ C ⟩ proj L j
 --          ≡⟨ defCanonicalFact L (cone (islim L')) ⟩
 --       proj L' j
 --          ≡⟨ sym (⋆IdL C (proj L' j)) ⟩
 --      id C (head L') ⋆⟨ C ⟩ proj L' j ∎
  --    
 --   isom .ret = homToLimPath L (f ⋆⟨ C ⟩ g) (id C (head L)) p
 --     where
  --    p : (j : J .ob) → (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ proj L j ≡ id C (head L) ⋆⟨ C ⟩ proj L j
  --    p j = 
   --     (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ proj L j
  --         ≡⟨ ⋆Assoc C f g (proj L j) ⟩
  --      f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ proj L j)
  --         ≡⟨ cong (λ g → f ⋆⟨ C ⟩ g) (defCanonicalFact L (cone (islim L'))) ⟩
  --      f ⋆⟨ C ⟩ proj L' j
 --          ≡⟨ defCanonicalFact L' (cone (islim L)) ⟩
  --      proj L j
   --        ≡⟨ sym (⋆IdL C (proj L j)) ⟩
 --       id C (head L) ⋆⟨ C ⟩ proj L j ∎
    
--module _ {J : Precategory ℓJ ℓJ'}
 --        {C : Precategory ℓC ℓC'}
 --        {D : Precategory ℓD ℓD'}
 --        (F : Functor J C)
 --        (G : Functor C D)
--         (L : Limit F)
--         (L' : Limit (G ∘F F)) where
         
--  coneComp : Cone (G ∘F F) (G ⟅ head L ⟆)
--  N-ob coneComp  j = G ⟪ N-ob (cone (islim L)) j ⟫
--  N-hom coneComp {j} {j'} f =
 --   id D (G ⟅ head L ⟆) ⋆⟨ D ⟩ G ⟪ N-ob (cone (islim L)) j' ⟫
--        ≡⟨ ⋆IdL D (G ⟪ N-ob (cone (islim L)) j' ⟫) ⟩
--    G ⟪ N-ob (cone (islim L)) j' ⟫
 --       ≡⟨ cong (λ f → G ⟪ f ⟫) (sym (⋆IdL C (N-ob (cone (islim L)) j'))) ⟩
 --   G ⟪ id C (head L) ⋆⟨ C ⟩  N-ob (cone (islim L)) j' ⟫
--        ≡⟨ cong (λ f → G ⟪ f ⟫) (N-hom (cone (islim L)) f) ⟩
---    G ⟪ (N-ob (cone (islim L)) j) ⋆⟨ C ⟩  F ⟪ f ⟫ ⟫
 --       ≡⟨ F-seq G (N-ob (cone (islim L)) j) (F ⟪ f ⟫) ⟩
 --   G ⟪ N-ob (cone (islim L)) j ⟫ ⋆⟨ D ⟩ (G ⟪ F ⟪ f ⟫ ⟫) ∎
    
--  canonicalMapComp : D [ G ⟅ head L ⟆ , head L' ]
--  canonicalMapComp = canonicalFact L' coneComp

 -- preservLimit : Type ℓD'
 -- preservLimit = isIso {C = D} canonicalMapComp 

  
