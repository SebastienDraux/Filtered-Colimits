{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

open import Categories
open import Lemma

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Precategory ℓC ℓC'
    D : Precategory ℓD ℓD'
    E : Precategory ℓE ℓE'

open Functor
open Precategory
open NatTrans
open CatIso

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


module _ {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄ where
         
  makeFactPath : {x y : D .ob} → {F : Functor C D} → (c : Cone F x) → (c' : Cone F y) → (fact1 fact2 : c' factors c) → (fst fact1 ≡ fst fact2) → fact1 ≡ fact2
  makeFactPath c c' (f , q) (f' , q') p = ΣPathP (p , (toPathP (isSetHom (isCatFUNCTOR C D) c (f' ◼ c') (transport (λ i → c ≡ p i ◼ c') q) q')))

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


module _ {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄ where

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
        rem : PathP (λ i → pathPFfGf (id C x) i ≡ id D (eq-ob eq x i)) (F-id F) (F-id G)
        rem = isProp→PathP (λ _ → isSetHom isCatD _ _) (F-id F) (F-id G)
      H .F-seq f g = rem i
        where
        rem : PathP (λ i → pathPFfGf (f ⋆⟨ C ⟩ g) i ≡  pathPFfGf f i ⋆⟨ D ⟩ pathPFfGf g i) (F-seq F f g) (F-seq G f g)
        rem = isProp→PathP (λ _ → isSetHom isCatD _ _) (F-seq F f g) (F-seq G f g)

  ≡→eqFunct : {F G : Functor C D} → F ≡ G → eqFunct F G
  ≡→eqFunct {F} {G} p .eq-ob x i = (p i) ⟅ x ⟆
  ≡→eqFunct {F} {G} p .eq-hom {x} {y} f = substHomLR D (eq-ob (≡→eqFunct p) x) (eq-ob (≡→eqFunct p) y) (F ⟪ f ⟫) ∙ fromPathP (λ i → (p i) ⟪ f ⟫)

  eqFunct→≡→eqFunct : {F G : Functor C D} → (eq : eqFunct F G) → ≡→eqFunct (eqFunct→≡ eq) ≡ eq
  eqFunct→≡→eqFunct {F} {G} eq i .eq-ob = eq-ob eq
  eqFunct→≡→eqFunct {F} {G} eq i .eq-hom {x} {y} f = rem i
    where
    rem : PathP (λ i → invP D (eq-ob eq x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (eq-ob eq y) ≡ G ⟪ f ⟫) (eq-hom (≡→eqFunct (eqFunct→≡ eq)) f) (eq-hom eq f)
    rem = isProp→PathP (λ i → isSetHom isCatD (invP D (eq-ob eq x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (eq-ob eq y)) (G ⟪ f ⟫)) (eq-hom (≡→eqFunct (eqFunct→≡ eq)) f) (eq-hom eq f)

  ≡→eqFunct→≡ : {F G : Functor C D} → (p : F ≡ G) → eqFunct→≡ (≡→eqFunct p) ≡ p
  ≡→eqFunct→≡ {F} {G} p i j = {!!} --H
    where
    rem-hom : {x y : ob C} → (f : C [ x , y ]) → PathP (λ j → eqFunct→≡ (≡→eqFunct p) j ⟪ f ⟫ ≡ (p j) ⟪ f ⟫) refl refl
    rem-hom f = isProp→PathP (λ j → isSetHom isCatD (eqFunct→≡ (≡→eqFunct p) j ⟪ f ⟫) ((p j) ⟪ f ⟫)) refl refl

    H : Functor C D
    H .F-ob  x = (p j) ⟅ x ⟆
    H .F-hom f = rem-hom f j i 
    H .F-id {x} k = rem k j i
      where
      rem : PathP (λ k → PathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) refl refl) (rem-hom (id C x)) (λ j i → id D ((p j) ⟅ x ⟆))
      rem = isProp→PathP (λ k → isSet→isPropPathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) (λ j → isProp→isSet (isSetHom isCatD (F-id (eqFunct→≡ (≡→eqFunct p) j) k) (F-id (p j) k))) refl refl) (rem-hom (id C x)) λ j i → id D ((p j) ⟅ x ⟆)
    H .F-seq {x} {y} {z} f g = rem
      where
      B : I → Type _
      B = λ j → (eqFunct→≡ (≡→eqFunct p) j ⟪ f ⋆⟨ C ⟩ g ⟫) ≡ (p j ⟪ f ⋆⟨ C ⟩ g ⟫)
      isPropB : (j : I) → isProp (B j)
      isPropB = λ j → isSetHom isCatD (eqFunct→≡ (≡→eqFunct p) j ⟪ f ⋆⟨ C ⟩ g ⟫) (p j ⟪ f ⋆⟨ C ⟩ g ⟫)
      
      rem : rem-hom (f ⋆⟨ C ⟩ g) j i ≡ (rem-hom f j i) ⋆⟨ D ⟩ (rem-hom g j i)
      rem =
        rem-hom (f ⋆⟨ C ⟩ g) j i
          ≡⟨ refl ⟩
        isProp→PathP isPropB refl refl j i
          ≡⟨ refl ⟩
        toPathP {A = B} (isPropB i1 (transp B i0 refl) refl) j i
          ≡⟨ {!!} ⟩
        isProp→PathP (λ j → isSetHom isCatD (eqFunct→≡ (≡→eqFunct p) j ⟪ f ⟫) ((p j) ⟪ f ⟫)) refl refl j i ⋆⟨ D ⟩ isProp→PathP (λ j → isSetHom isCatD (eqFunct→≡ (≡→eqFunct p) j ⟪ g ⟫) ((p j) ⟪ g ⟫)) refl refl j i
          ≡⟨ refl ⟩
        (rem-hom f j i) ⋆⟨ D ⟩ (rem-hom g j i) ∎
--
   
  
 -- makeFunctPath : (F G : Functor C D) → (p : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆) → ({x y : ob C} → (f : C [ x , y ]) → invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (p y) ≡ G ⟪ f ⟫) → F ≡ G
 -- makeFunctPath F G p q i = H
  --  where
 ----   pathPFfGf : {x y : ob C} → (f : C [ x , y ]) → PathP (λ i → D [ p x i , p y i ]) (F ⟪ f ⟫) (G ⟪ f ⟫)
  --  pathPFfGf {x} {y} f = toPathP (sym Gf≡subst2Ff)
  --    where
  --      Gf≡subst2Ff : G ⟪ f ⟫ ≡ subst2 (λ x' y' → D [ x' , y' ]) (p x) (p y) (F ⟪ f ⟫)
  --      Gf≡subst2Ff  = 
  ---        G ⟪ f ⟫ ≡⟨ sym (q f) ⟩
   --       invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (p y) ≡⟨ sym (substHomR D (p y) (invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫)) ⟩
  --        subst (λ y' → D [ G ⟅ x ⟆ , y' ]) (p y) (invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫) ≡⟨ cong (λ f → subst (λ y' → D [ G ⟅ x ⟆ , y' ]) (p y) f) (sym (substHomL D (p x) (F ⟪ f ⟫))) ⟩
  --        subst (λ y' → D [ G ⟅ x ⟆ , y' ]) (p y) (subst (λ x' → D [ x' , F ⟅ y ⟆ ]) (p x) (F ⟪ f ⟫)) ≡⟨ subst-subst≡subst2 (λ x' y' → D [ x' , y' ]) (p x) (p y) (F ⟪ f ⟫) ⟩
  --        subst2 (λ x' y' → D [ x' , y' ]) (p x) (p y) (F ⟪ f ⟫) ∎
 --         
 --   H : Functor C D
 --   H .F-ob x = p x i
  --  H .F-hom {x} {y} f = pathPFfGf f i
    
  --  H .F-id {x} = rem i
  --    where
  --    rem : PathP (λ i → pathPFfGf (id C x) i ≡ id D (p x i)) (F-id F) (F-id G)
  --    rem = isProp→PathP (λ _ → isSetHom isCatD _ _) (F-id F) (F-id G)
  --  H .F-seq f g = rem i
  --    where
  --    rem : PathP (λ i → pathPFfGf (f ⋆⟨ C ⟩ g) i ≡  pathPFfGf f i ⋆⟨ D ⟩ pathPFfGf g i) (F-seq F f g) (F-seq G f g)
  --    rem = isProp→PathP (λ _ → isSetHom isCatD _ _) (F-seq F f g) (F-seq G f g)

 -- makeFunctPathMorP : (F G : Functor C D) → (p : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆) → (q : {x y : ob C} → (f : C [ x , y ]) → invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (p y) ≡ G ⟪ f ⟫) → (x : ob C) → morP (FUNCTOR C D) (makeFunctPath F G p q) ⟦ x ⟧ ≡ morP D (p x)
 -- makeFunctPathMorP F G p q x = J (λ G P → morP (FUNCTOR C D) P ⟦ x ⟧ ≡ morP D λ i → P i ⟅ x ⟆) (cong (λ α → α ⟦ x ⟧) (reflMorP (FUNCTOR C D) {x = F}) ∙ sym (reflMorP D)) (makeFunctPath F G p q)
  
  --makeFunctPathInvP : (F G : Functor C D) → (p : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆) → (q : {x y : ob C} → (f : C [ x , y ]) → invP D (p x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (p y) ≡ G ⟪ f ⟫) → (x : ob C) → invP (FUNCTOR C D) (makeFunctPath F G p q) ⟦ x ⟧ ≡ invP D (p x)
 -- makeFunctPathInvP F G p q x = J (λ G P → invP (FUNCTOR C D) P ⟦ x ⟧ ≡ invP D λ i → P i ⟅ x ⟆) (cong (λ α → α ⟦ x ⟧) (reflInvP (FUNCTOR C D) {x = F}) ∙ sym (reflInvP D)) (makeFunctPath F G p q)

 -- private
 --   eq : {x y : ob C} → (F : Functor C D) → (f : C [ x , y ]) → invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D refl ≡ F ⟪ f ⟫
  --  eq {x} {y} F f = 
 --     (invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ morP D refl
 --       ≡⟨ cong (λ g → (invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ g) (reflMorP D) ⟩
  --    (invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ id D (F ⟅ y ⟆)
  --      ≡⟨ ⋆IdR D (invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫) ⟩
 --     invP D refl ⋆⟨ D ⟩ F ⟪ f ⟫
 --       ≡⟨ cong (λ g → g ⋆⟨ D ⟩ F ⟪ f ⟫) (reflInvP D) ⟩
  --    id D (F ⟅ x ⟆) ⋆⟨ D ⟩ F ⟪ f ⟫
  --      ≡⟨ ⋆IdL D (F ⟪ f ⟫) ⟩
  --    F ⟪ f ⟫ ∎
      
 -- makeFunctPathRefl : (F : Functor C D) → (F-id2 : {x : C .ob} → F ⟪ id C x ⟫ ≡ id D (F ⟅ x ⟆)) → (F-seq2 : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → F ⟪ f ⋆⟨ C ⟩ g ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ g ⟫) → F ≡ record { F-ob = F-ob F ; F-hom = F-hom F ; F-id = F-id2 ; F-seq = F-seq2 }
 -- makeFunctPathRefl F F-id2 F-seq2 = makeFunctPath F (record { F-ob = F-ob F ; F-hom = F-hom F ; F-id = F-id2 ; F-seq = F-seq2 }) (λ _ → refl) (eq F)

 -- makeFunctPathReflMorP : (F : Functor C D) → (F-id2 : {x : C .ob} → F ⟪ id C x ⟫ ≡ id D (F ⟅ x ⟆)) → (F-seq2 : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → F ⟪ f ⋆⟨ C ⟩ g ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ g ⟫) → (x : ob C) → morP (FUNCTOR C D) (makeFunctPathRefl F F-id2 F-seq2) ⟦ x ⟧ ≡ id D (F ⟅ x ⟆)
 -- makeFunctPathReflMorP F F-id2 F-seq2 x = makeFunctPathMorP F (record { F-ob = F-ob F ; F-hom = F-hom F ; F-id = F-id2 ; F-seq = F-seq2 }) (λ _ → refl) (eq F) x ∙ reflMorP D

 -- makeFunctPathReflInvP : (F : Functor C D) → (F-id2 : {x : C .ob} → F ⟪ id C x ⟫ ≡ id D (F ⟅ x ⟆)) → (F-seq2 : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) → F ⟪ f ⋆⟨ C ⟩ g ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ g ⟫) → (x : ob C) → morP (FUNCTOR C D) (makeFunctPathRefl F F-id2 F-seq2) ⟦ x ⟧ ≡ id D (F ⟅ x ⟆)
 -- makeFunctPathReflInvP F F-id2 F-seq2 x = makeFunctPathInvP F (record { F-ob = F-ob F ; F-hom = F-hom F ; F-id = F-id2 ; F-seq = F-seq2 }) (λ _ → refl) (eq F) x ∙ reflInvP D

fComp = funcComp

infixr 30 fComp
syntax fComp G F = F ⋆ᶠ G

module _ {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄ where
--  ⋆ᶠIdL : (F : Functor C D) → 𝟙⟨ C ⟩ ⋆ᶠ F ≡ F
-- ⋆ᶠIdL F = makeFunctPathRefl (𝟙⟨ C ⟩ ⋆ᶠ F ) (F-id F) (F-seq F)

--  ⋆ᶠIdR : (F : Functor C D) → F ⋆ᶠ 𝟙⟨ D ⟩ ≡ F
--  ⋆ᶠIdR F = makeFunctPathRefl (F ⋆ᶠ 𝟙⟨ D ⟩) (F-id F) (F-seq F)


--module _ ⦃ isCatD : isCategory D ⦄ where
--  ⋆ᶠAssoc : ∀ (F : Functor A B) (G : Functor B C) (H : Functor C D) → (F ⋆ᶠ G) ⋆ᶠ H ≡ F ⋆ᶠ (G ⋆ᶠ H)
 -- ⋆ᶠAssoc F G H = makeFunctPathRefl ((F ⋆ᶠ G) ⋆ᶠ H) (F-id (F ⋆ᶠ (G ⋆ᶠ H))) (F-seq (F ⋆ᶠ (G ⋆ᶠ H)))
