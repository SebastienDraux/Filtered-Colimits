{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits
open import Cubical.Categories.Morphism
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma

open import IsoCat
open import Limits
open import Colimits
open import Lemma
open import Functors
open import NatTransfo

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level


open Category
open NatTrans
open Functor
open Cone
open LimCone
open CatIso

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}  where

  creatFunctLim : LimitsOfShape J D → LimitsOfShape J (FUNCTOR C D)
  creatFunctLim limit F = Lim     
   where
   L : (x : C .ob) → LimCone ((eval x) ∘F F)
   L x = limit ((eval x) ∘F F)

   cx : {H : Functor C D} → (CC : Cone F H) → (x : C .ob) → Cone (eval x ∘F F) (H ⟅ x ⟆)
   cx {H} CC x .coneOut j = (coneOut CC j) ⟦ x ⟧
   cx {H} CC x .coneOutCommutes f = cong (λ α → α ⟦ x ⟧) (coneOutCommutes CC f)
   
   c : {x y : C .ob} → (f : C [ x , y ]) → Cone ((eval y) ∘F F) (lim (L x))
   c {x} {y} f .coneOut j = limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
   c {x} {y} f .coneOutCommutes {j} {j'} g = 
     (limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ y ⟧
       ≡⟨ ⋆Assoc D (limOut (L x) j) ((F ⟅ j ⟆) ⟪ f ⟫) ((F ⟪ g ⟫) ⟦ y ⟧) ⟩
     limOut (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ y ⟧)
       ≡⟨ cong (λ f → limOut (L x) j ⋆⟨ D ⟩ f) (N-hom (F ⟪ g ⟫) f) ⟩  
     limOut (L x) j ⋆⟨ D ⟩ (F ⟪ g ⟫ ⟦ x ⟧ ⋆⟨ D ⟩ (F ⟅ j' ⟆) ⟪ f ⟫)
       ≡⟨ sym (⋆Assoc D (limOut (L x) j) ((F ⟪ g ⟫) ⟦ x ⟧) ((F ⟅ j' ⟆) ⟪ f ⟫)) ⟩
     (limOut (L x) j ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ x ⟧) ⋆⟨ D ⟩ (F ⟅ j' ⟆) ⟪ f ⟫
       ≡⟨ cong (λ g → g ⋆⟨ D ⟩ (F ⟅ j' ⟆) ⟪ f ⟫) (limOutCommutes (L x) g) ⟩
     limOut (L x) j' ⋆⟨ D ⟩ (F ⟅ j' ⟆) ⟪ f ⟫ ∎
   
   G : Functor C D
   G .F-ob x = lim (L x)
   G .F-hom {x} {y} f = limArrow (L y) (lim (L x)) (c f)
   G .F-id {x} = limArrowUnique (L x) (lim (L x)) (c (id C)) (id D) eq
       where
     eq : (j : ob J) → id D ⋆⟨ D ⟩ (coneOut (limCone (L x)) j) ≡ limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ id C ⟫
     eq j = 
       id D ⋆⟨ D ⟩ (coneOut (limCone (L x)) j)
         ≡⟨ ⋆IdL D (limOut (L x) j) ⟩
       limOut (L x) j
         ≡⟨ sym (⋆IdR D (limOut (L x) j)) ⟩
       limOut (L x) j ⋆⟨ D ⟩ id D
         ≡⟨ cong (λ f → limOut (L x) j ⋆⟨ D ⟩ f) (sym (F-id (F ⟅ j ⟆))) ⟩
       limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ id C ⟫ ∎
   G .F-seq {x} {y} {z} f g = limArrowUnique (L z) (lim (L x)) (c (f ⋆⟨ C ⟩ g)) (F-hom G f ⋆⟨ D ⟩ F-hom G g) eq
     where
     eq : (j : ob J) → limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ limArrow (L z) (lim (L y)) (c g) ⋆⟨ D ⟩ coneOut (limCone (L z)) j ≡ limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⋆⟨ C ⟩ g ⟫
     eq j = 
       limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ limArrow (L z) (lim (L y)) (c g) ⋆⟨ D ⟩ limOut (L z) j
         ≡⟨ ⋆Assoc D (limArrow (L y) (lim (L x)) (c f)) (limArrow (L z) (lim (L y)) (c g)) (limOut (L z) j) ⟩
       limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ (limArrow (L z) (lim (L y)) (c g) ⋆⟨ D ⟩ limOut (L z) j)
         ≡⟨ cong (λ g → limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ g) (limArrowCommutes (L z) (lim (L y)) (c g) j) ⟩
       limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ (limOut (L y) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫)
         ≡⟨ sym (⋆Assoc D (limArrow (L y) (lim (L x)) (c f)) (limOut (L y) j) ((F ⟅ j ⟆) ⟪ g ⟫)) ⟩
       (limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ limOut (L y) j) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫
         ≡⟨ cong (λ f → f ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫) (limArrowCommutes (L y) (lim (L x)) (c f) j) ⟩
         (limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫
         ≡⟨ ⋆Assoc D (limOut (L x) j) ((F ⟅ j ⟆) ⟪ f ⟫) ((F ⟅ j ⟆) ⟪ g ⟫) ⟩
       limOut (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫ ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫)
         ≡⟨ cong (λ f → limOut (L x) j ⋆⟨ D ⟩ f) (sym (F-seq (F ⟅ j ⟆) f g)) ⟩
       limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⋆⟨ C ⟩ g ⟫ ∎

   CC : Cone F G
   CC .coneOut j .N-ob x = limOut (L x) j
   CC .coneOut j .N-hom {x} {y} f = limArrowCommutes (L y) (G ⟅ x ⟆) (c f) j 
   CC .coneOutCommutes {j} {j'} f = makeNatTransPath (funExt λ x → limOutCommutes (L x) f)

   α : (H : Functor C D) → Cone F H → NatTrans H G
   α H cc .N-ob x = limArrow (L x) (H ⟅ x ⟆) (cx cc x)
   α H cc .N-hom {x} {y} f = morToLimPath (L y) (H ⟪ f ⟫ ⋆⟨ D ⟩ limArrow (L y) (H ⟅ y ⟆) (cx cc y)) (limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ limArrow (L y) (lim (L x)) (c f)) eq
     where
     eq : (j : ob J) → H ⟪ f ⟫ ⋆⟨ D ⟩ limArrow (L y) (H ⟅ y ⟆) (cx cc y) ⋆⟨ D ⟩ limOut (L y) j ≡ limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ limOut (L y) j
     eq j =
       (H ⟪ f ⟫ ⋆⟨ D ⟩ limArrow (L y) (H ⟅ y ⟆) (cx cc y)) ⋆⟨ D ⟩ limOut (L y) j
         ≡⟨ ⋆Assoc D (H ⟪ f ⟫) (limArrow (L y) (H ⟅ y ⟆) (cx cc y)) (limOut (L y) j) ⟩
       H ⟪ f ⟫ ⋆⟨ D ⟩ (limArrow (L y) (H ⟅ y ⟆) (cx cc y) ⋆⟨ D ⟩ limOut (L y) j)
         ≡⟨ cong (λ g → H ⟪ f ⟫ ⋆⟨ D ⟩ g) (limArrowCommutes (L y) (H ⟅ y ⟆) (cx cc y) j) ⟩
       H ⟪ f ⟫ ⋆⟨ D ⟩ (coneOut cc j) ⟦ y ⟧
         ≡⟨ N-hom (coneOut cc j) f ⟩
       (coneOut cc j) ⟦ x ⟧ ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
         ≡⟨ cong (λ g → g ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) (sym (limArrowCommutes (L x) (H ⟅ x ⟆) (cx cc x) j)) ⟩
       (limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ limOut (L x) j) ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫)
         ≡⟨ ⋆Assoc D (limArrow (L x) (H ⟅ x ⟆) (cx cc x)) (limOut (L x) j) ((F ⟅ j ⟆) ⟪ f ⟫) ⟩
       limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ (limOut (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫)
         ≡⟨ cong (λ g → limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ g) (sym (limArrowCommutes (L y) (lim (L x)) (c f) j)) ⟩
       limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ (limArrow (L y) (lim (L x)) (c f) ⋆⟨ D ⟩ limOut (L y) j)
         ≡⟨ sym (⋆Assoc D (limArrow (L x) (H ⟅ x ⟆) (cx cc x)) (limArrow (L y) (lim (L x)) (c f)) (limOut (L y) j)) ⟩
       (limArrow (L x) (H ⟅ x ⟆) (cx cc x) ⋆⟨ D ⟩ limArrow (L y) (lim (L x)) (c f)) ⋆⟨ D ⟩ limOut (L y) j ∎

   Lim : LimCone F
   Lim .lim = G
   Lim .limCone  = CC
   Lim .univProp H cc .fst .fst = α H cc
   Lim .univProp H cc .fst .snd j = makeNatTransPath (funExt (λ x → limArrowCommutes (L x) (H ⟅ x ⟆) (cx cc x) j))
   Lim .univProp H cc .snd (β , βIsConeMor) = Σ≡Prop (λ β → isPropIsConeMor cc CC β) eq
     where
     eq = makeNatTransPath (funExt λ x → limArrowUnique (L x) (H ⟅ x ⟆) (cx cc x) (β ⟦ x ⟧) (λ j → cong (λ β → β ⟦ x ⟧) (βIsConeMor j)))
     
--  evalPreservLim : {x : C .ob} → preservesLimit (eval x) F {!!} {!!}

--  evalPreservLim : {x : C .ob} → (L' : Limit F) → (l : Limit ((eval x) ∘F F)) → preservLimit F (eval x) L' l
--  evalPreservLim {x} L' l = makeIso isom (canonicalMapComp F (eval x) L' l) mor≡
  --  where
--    isom : CatIso {C = D} (eval x ⟅ head L' ⟆) (head l)
 --   isom = eval x ⦅ unicityLim L' creatFuncLim ⦆ ⋆ᵢ⟨ D ⟩ unicityLim (L x) l

--    p : (j : J .ob) → mor isom ⋆⟨ D ⟩ proj l j ≡ eval x ⟪ proj L' j ⟫
 --   p j = 
--      mor isom ⋆⟨ D ⟩ proj l j
 --         ≡⟨ refl ⟩
--      (canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ canonicalFact l (cone (islim (L x)))) ⋆⟨ D ⟩ proj l j
 --         ≡⟨ ⋆Assoc D (canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧) (canonicalFact l (cone (islim (L x)))) (proj l j) ⟩
 --     canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ (canonicalFact l (cone (islim (L x))) ⋆⟨ D ⟩ proj l j)
--          ≡⟨ cong (λ f →  eval x ⟪ canonicalFact creatFuncLim (cone (islim L')) ⟫ ⋆⟨ D ⟩ f) (defCanonicalFact l (cone (islim (L x)))) ⟩
 --     canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ proj (L x) j
--          ≡⟨ refl ⟩
--      canonicalFact (L x) (cx (cone (islim L')) x) ⋆⟨ D ⟩ proj (L x) j
--          ≡⟨ defCanonicalFact (L x) (cx (cone (islim L')) x) ⟩  
--      proj L' j ⟦ x ⟧ ∎
--
----    mor≡ : mor isom ≡ canonicalMapComp F (eval x) L' l
--    mor≡ = carCanFact l (coneComp F (eval x) L' l) (mor isom) p

module _ {J : Category ℓJ ℓJ'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  creatFunctColim : ColimitsOfShape J D → ColimitsOfShape J (FUNCTOR C D)
  creatFunctColim colimit F .lim = {!!}
  creatFunctColim colimit F .limCone = {!!}
  creatFunctColim colimit F .univProp = {!!}
