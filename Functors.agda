{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import IsoCat
open import Lemma

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Functor
open Category
open NatTrans
open CatIso
open Iso

fComp = funcComp

infixr 30 fComp
syntax fComp G F = F ⋆ᶠ G

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
         
--  makeFactPath : {x y : D .ob} → {F : Functor C D} → (c : Cone F x) → (c' : Cone F y) → (fact1 fact2 : c' factors c) → (fst fact1 ≡ fst fact2) → fact1 ≡ fact2
--  makeFactPath c c' (f , q) (f' , q') p = ΣPathP (p , (toPathP (isSetHom (isCatFUNCTOR C D) c (f' ◼ c') (transport (λ i → c ≡ p i ◼ c') q) q')))

  eval : C .ob → (Functor (FUNCTOR C D) D)
  eval x .F-ob F = F ⟅ x ⟆
  eval x .F-hom α = α ⟦ x ⟧
  eval x .F-id = refl
  eval x .F-seq α β = refl

  evalFunct : Functor C (FUNCTOR (FUNCTOR C D) D)
  evalFunct .F-ob = eval
  evalFunct .F-hom {x} {y} f .N-ob F = F ⟪ f ⟫
  evalFunct .F-hom {x} {y} f .N-hom {F} {G} α = sym (N-hom α f)
  evalFunct .F-id {x} = makeNatTransPath (funExt (λ F → F-id F))
  evalFunct .F-seq {x} {y} {z} f g = makeNatTransPath (funExt (λ F → F-seq F f g))


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  record eqFunct (F G : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      eq-ob : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
      eq-hom : {x y : ob C} → (f : C [ x , y ]) → invP D (eq-ob x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (eq-ob y) ≡ G ⟪ f ⟫

  open eqFunct
  
  eqFunct→≡ : {F G : Functor C D} →  eqFunct F G → F ≡ G
  eqFunct→≡ {F} {G} eq i = H
    where
      pathPFfGf : {x y : ob C} → (f : C [ x , y ]) → PathP (λ i → D [ eq-ob eq x i , eq-ob eq y i ]) (F ⟪ f ⟫) (G ⟪ f ⟫)
      pathPFfGf {x} {y} f = toPathP (sym Gf≡subst2Ff)
        where
        Gf≡subst2Ff : G ⟪ f ⟫ ≡ subst2 (λ x' y' → D [ x' , y' ]) (eq-ob eq x) (eq-ob eq y) (F ⟪ f ⟫)
        Gf≡subst2Ff  = sym (eq-hom eq f) ∙ substHomLR D (eq-ob eq x) (eq-ob eq y) (F ⟪ f ⟫)
          
      H : Functor C D
      H .F-ob x = eq-ob eq x i
      H .F-hom {x} {y} f = pathPFfGf f i
      H .F-id {x} = rem i
        where
        rem : PathP (λ i → pathPFfGf (id C) i ≡ id D) (F-id F) (F-id G)
        rem = isProp→PathP (λ _ → isSetHom D _ _) (F-id F) (F-id G)
      H .F-seq f g = rem i
        where
        rem : PathP (λ i → pathPFfGf (f ⋆⟨ C ⟩ g) i ≡  pathPFfGf f i ⋆⟨ D ⟩ pathPFfGf g i) (F-seq F f g) (F-seq G f g)
        rem = isProp→PathP (λ _ → isSetHom D _ _) (F-seq F f g) (F-seq G f g)

  ≡→eqFunct : {F G : Functor C D} → F ≡ G → eqFunct F G
  ≡→eqFunct {F} {G} p .eq-ob x i = (p i) ⟅ x ⟆
  ≡→eqFunct {F} {G} p .eq-hom {x} {y} f = substHomLR D (eq-ob (≡→eqFunct p) x) (eq-ob (≡→eqFunct p) y) (F ⟪ f ⟫) ∙ fromPathP (λ i → (p i) ⟪ f ⟫)

  eqFunct→≡→eqFunct : {F G : Functor C D} → (eq : eqFunct F G) → ≡→eqFunct (eqFunct→≡ eq) ≡ eq
  eqFunct→≡→eqFunct {F} {G} eq i .eq-ob = eq-ob eq
  eqFunct→≡→eqFunct {F} {G} eq i .eq-hom {x} {y} f = rem i
    where
    rem : PathP (λ i → invP D (eq-ob eq x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (eq-ob eq y) ≡ G ⟪ f ⟫) (eq-hom (≡→eqFunct (eqFunct→≡ eq)) f) (eq-hom eq f)
    rem = isProp→PathP (λ _ → isSetHom D _ _) (eq-hom (≡→eqFunct (eqFunct→≡ eq)) f) (eq-hom eq f)

  ≡→eqFunct→≡ : {F G : Functor C D} → (p : F ≡ G) → eqFunct→≡ (≡→eqFunct p) ≡ p
  ≡→eqFunct→≡ {F} {G} p i j = H
    where
    rem-hom : {x y : ob C} → (f : C [ x , y ]) → PathP (λ j → eqFunct→≡ (≡→eqFunct p) j ⟪ f ⟫ ≡ (p j) ⟪ f ⟫) refl refl
    rem-hom f = isProp→PathP (λ _ → isSetHom D _ _) refl refl

    H : Functor C D
    H .F-ob  x = (p j) ⟅ x ⟆
    H .F-hom f = rem-hom f j i 
    H .F-id {x} k = rem k j i
      where
      rem : PathP (λ k → PathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) refl refl) (rem-hom (id C)) λ j → refl
      rem = isProp→PathP (λ k → isSet→isPropPathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) (λ _ → isProp→isSet (isSetHom D _ _)) _ _) _ _
    H .F-seq {x} {y} {z} f g k = rem k j i
      where
      rem : PathP (λ k → PathP (λ j → F-seq (eqFunct→≡ (≡→eqFunct p) j) f g k ≡ F-seq (p j) f g k) refl refl) (rem-hom (f ⋆⟨ C ⟩ g)) (λ j i → rem-hom f j i ⋆⟨ D ⟩ rem-hom g j i)
      
      rem = isProp→PathP (λ k → isSet→isPropPathP (λ j →  F-seq (eqFunct→≡ (≡→eqFunct p) j) f g k ≡ F-seq (p j) f g k) (λ _ → isProp→isSet (isSetHom D _ _)) _ _) _ _

  ≡≃eqFunct : {F G : Functor C D} → (F ≡ G) ≃ (eqFunct F G)
  ≡≃eqFunct {F} {G} = isoToEquiv isom
    where
    isom : Iso (F ≡ G) (eqFunct F G)
    isom .fun = ≡→eqFunct
    isom .inv = eqFunct→≡
    isom .leftInv = ≡→eqFunct→≡
    isom .rightInv = eqFunct→≡→eqFunct


  makeFunctPathMorP : (F G : Functor C D) → (p : F ≡ G) → (x : ob C) → morP (FUNCTOR C D) p ⟦ x ⟧ ≡ morP D (eq-ob (≡→eqFunct p) x)
  makeFunctPathMorP F G p x = J (λ G p → morP (FUNCTOR C D) p ⟦ x ⟧ ≡ morP D (eq-ob (≡→eqFunct p) x)) eqRefl p
    where
    eqRefl : morP (FUNCTOR C D) {x = F} refl ⟦ x ⟧ ≡ morP D refl
    eqRefl = 
      morP (FUNCTOR C D) {x = F} refl ⟦ x ⟧
        ≡⟨ cong (λ (α : NatTrans F F) → α ⟦ x ⟧) (reflMorP (FUNCTOR C D)) ⟩
      id D
        ≡⟨ sym (reflMorP D) ⟩
      morP D refl ∎
  
  makeFunctPathInvP : (F G : Functor C D) → (p : F ≡ G) → (x : ob C) → invP (FUNCTOR C D) p ⟦ x ⟧ ≡ invP D (eq-ob (≡→eqFunct p) x)
  makeFunctPathInvP F G p x = J (λ G p → invP (FUNCTOR C D) p ⟦ x ⟧ ≡ invP D (eq-ob (≡→eqFunct p) x)) eqRefl p
   where
    eqRefl : invP (FUNCTOR C D) {x = F} refl ⟦ x ⟧ ≡ invP D refl
    eqRefl = 
      morP (FUNCTOR C D) {x = F} refl ⟦ x ⟧
        ≡⟨ cong (λ (α : NatTrans F F) → α ⟦ x ⟧) (reflInvP (FUNCTOR C D)) ⟩
      id D
        ≡⟨ sym (reflInvP D) ⟩
      morP D refl ∎

  eqFunctRefl : (F : Functor C D) → eqFunct F F
  eqFunctRefl F .eq-ob x = refl
  eqFunctRefl F .eq-hom f = substHomLR D refl refl (F ⟪ f ⟫) ∙ subst2Refl (λ x y → D [ F ⟅ x ⟆ , F ⟅ y ⟆ ]) (F ⟪ f ⟫)
