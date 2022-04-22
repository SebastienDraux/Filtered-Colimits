{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Morphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

open import Functors
open import Categories
open import Lemma
open import 2-Cat
open import IsoCat

private
  variable
    ℓC ℓC' : Level

open Precategory
open Functor
open CatIso
open Category
open NatTrans
open NatIso
open Pre-2-Category

module _ (C : Category ℓC ℓC')  where

  record dispCat-ob : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
    field
      dC-ob : ob (cat C) → Type ℓC
      dC-hom : {x y : ob (cat C)} → (cat C) [ x , y ] → dC-ob x → dC-ob y → Type ℓC'
      dC-homSet : {x y : ob (cat C)} → (f : (cat C) [ x , y ]) → (X : dC-ob x) → (Y : dC-ob y) → isSet (dC-hom f X Y)
      dC-id : {x : ob (cat C)} → (X : dC-ob x) → dC-hom (id (cat C) x) X X
      dC-⋆ : {x y z : ob (cat C)} → {X : dC-ob x} → {Y : dC-ob y} → {Z : dC-ob z} → {f : (cat C) [ x , y ]} → {g : (cat C) [ y , z ]} → dC-hom f X Y → dC-hom g Y Z → dC-hom (f ⋆⟨ (cat C) ⟩ g) X Z
      dC-⋆IdL : {x y : ob (cat C)} → {f : (cat C) [ x , y ]}  → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → subst (λ f → dC-hom f X Y) (⋆IdL (cat C) f) (dC-⋆ (dC-id X) F) ≡ F
      dC-⋆IdR : {x y : ob (cat C)} → {f : (cat C) [ x , y ]} → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → subst (λ f → dC-hom f X Y) (⋆IdR (cat C) f) (dC-⋆ F (dC-id Y)) ≡ F
      dC-⋆Assoc : {w x y z : ob (cat C)} → {W : dC-ob w} → {X : dC-ob x} → {Y : dC-ob y} → {Z : dC-ob z} → {f : (cat C) [ w , x ]} → {g : (cat C) [ x , y ]} → {h : (cat C) [ y , z ]} → (F : dC-hom f W X) → (G : dC-hom g X Y) → (H : dC-hom h Y Z) → subst (λ f⋆g⋆h → dC-hom f⋆g⋆h W Z) (⋆Assoc (cat C) f g h) ((dC-⋆ (dC-⋆ F G) H)) ≡ dC-⋆ F (dC-⋆ G H)

  open dispCat-ob
  
  totalPrecat : dispCat-ob → Precategory ℓC ℓC'
  totalPrecat D .ob = Σ[ x ∈ ob (cat C) ] dC-ob D x
  totalPrecat D .Hom[_,_] (x , X) (y , Y) = Σ[ f ∈ (cat C) [ x , y ] ] dC-hom D f X Y
  totalPrecat D .id (x , X) = (id (cat C) x) , dC-id D X
  totalPrecat D ._⋆_ (f , F) (g , G) = (f ⋆⟨ (cat C) ⟩ g) , dC-⋆ D F G
  totalPrecat D .⋆IdL (f , F) = ΣPathP ((⋆IdL (cat C) f) , (toPathP (dC-⋆IdL D F)))
  totalPrecat D .⋆IdR (f , F) = ΣPathP ((⋆IdR (cat C) f) , (toPathP (dC-⋆IdR D F)))
  totalPrecat D .⋆Assoc (f , F) (g , G) (h , H) = ΣPathP ((⋆Assoc (cat C) f g h) , toPathP (dC-⋆Assoc D F G H))
  
  projFunc : (D : dispCat-ob) → Functor (totalPrecat D) (cat C)
  projFunc D .F-ob (x , X) = x
  projFunc D .F-hom (f , F) = f
  projFunc D .F-id = refl
  projFunc D .F-seq f g = refl

  instance
    isCatTotalPrecat : {D : dispCat-ob} → isCategory (totalPrecat D)
    isCatTotalPrecat {D} .isSetHom {x , X} {y , Y} = Σ-Set ((cat C) [ x , y ]) (λ f → dC-hom D f X Y) (isSetHom (isCat C)) (λ f → dC-homSet D f X Y)

  totalCat : dispCat-ob → Category ℓC ℓC'
  totalCat D .cat = totalPrecat D
  totalCat D .isCat = isCatTotalPrecat {D = D}
      
  record dispCat-hom (D D' : dispCat-ob) : Type (ℓ-max ℓC ℓC') where
    field
      funct : Functor (totalPrecat D) (totalPrecat D')
      comProj : funct ⋆ᶠ projFunc D' ≡ projFunc D

  open dispCat-hom

  makeDispCat-homPath : {D D' : dispCat-ob} → (F G : dispCat-hom D D') → (p : (x : ob (totalPrecat D)) → funct F ⟅ x ⟆ ≡ funct G ⟅ x ⟆) →
      (q : {x y : ob (totalPrecat D)} → (f : (totalPrecat D) [ x , y ]) → invP (totalPrecat D') (p x) ⋆⟨ totalPrecat D' ⟩ (funct F) ⟪ f ⟫ ⋆⟨ totalPrecat D' ⟩ morP (totalPrecat D') (p y) ≡ (funct G) ⟪ f ⟫) → F ≡ G
  makeDispCat-homPath {D} {D'} F G p q i .funct = makeFunctPath ⦃ isCatTotalPrecat {D = D'} ⦄ (funct F) (funct G) p q i
  makeDispCat-homPath {D} {D'} F G p q i .comProj = toPathP {A = λ i → functF≡functG i ⋆ᶠ projFunc D' ≡ projFunc D} test i
    where
    functF≡functG = makeFunctPath ⦃ isCatTotalPrecat {D = D'} ⦄ (funct F) (funct G) p q
    test : subst (λ F → F ⋆ᶠ projFunc D' ≡ projFunc D) functF≡functG (comProj F) ≡ comProj G
    test = 
      subst (λ F → F ⋆ᶠ projFunc D' ≡ projFunc D) functF≡functG (comProj F)
        ≡⟨ subst≡ₗ (cong (λ F → F ⋆ᶠ projFunc D') functF≡functG) (comProj F) ⟩
      sym (cong (λ F → F ⋆ᶠ projFunc D') functF≡functG) ∙ comProj F
        ≡⟨ {!!} ⟩
      {!!}
        ≡⟨ {!!} ⟩
      comProj G ∎
  
  dispCat-hom-Precat : (D D' : dispCat-ob) → Precategory (ℓ-max ℓC ℓC') (ℓ-max ℓC ℓC')
  dispCat-hom-Precat D D' .ob = dispCat-hom D D'
  dispCat-hom-Precat D D' .Hom[_,_] F G = NatTrans (funct F) (funct G)
  dispCat-hom-Precat D D' .id F = idTrans (funct F)
  dispCat-hom-Precat D D' ._⋆_ α β = α ●ᵛ β
  dispCat-hom-Precat D D' .⋆IdL α = makeNatTransPath ⦃ isCatTotalPrecat {D = D'}⦄ λ i x → ⋆IdL (totalPrecat D') (α ⟦ x ⟧) i
  dispCat-hom-Precat D D' .⋆IdR α = makeNatTransPath ⦃ isCatTotalPrecat {D = D'}⦄ λ i x → ⋆IdR (totalPrecat D') (α ⟦ x ⟧) i
  dispCat-hom-Precat D D' .⋆Assoc α β γ = makeNatTransPath ⦃ isCatTotalPrecat {D = D'}⦄ λ i x → ⋆Assoc (totalPrecat D') (α ⟦ x ⟧) (β ⟦ x ⟧) (γ ⟦ x ⟧) i


  dispCat : Pre-2-Category (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-max ℓC ℓC') (ℓ-max ℓC ℓC')
  dispCat .ob₀ = dispCat-ob
  dispCat .ob₁[_,_] = dispCat-hom-Precat
  dispCat .id₁ D .funct = 𝟙⟨ totalPrecat D ⟩
  dispCat .id₁ D .comProj = ⋆ᶠIdL (projFunc D)
  dispCat ._⋆₁_ F G .funct = funct F ⋆ᶠ (funct G)
  dispCat ._⋆₁_ {D} {D'} {D''} F G .comProj = ⋆ᶠAssoc (funct F) (funct G) (projFunc D'') ∙ cong (λ G → G ∘F funct F) (comProj G) ∙ comProj F
  dispCat .⋆₁IdL F = {!!}
  --dispcat .functseq .f-ob (f , g) .funct = funct g ∘f funct f
  --dispcat .functseq .f-ob (f , g) .comproj .trans .n-ob x = trans (comproj g) ⟦ (funct f) ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ trans (comproj f) ⟦ x ⟧
  --dispcat .functseq {d} {d'} {d''} .f-ob (f , g) .comproj .trans .n-hom {x} {y} (h , h) =
  --  projfunc d'' ⟪ funct g ⟪ funct f ⟪ h , h ⟫ ⟫ ⟫ ⋆⟨ c ⟩ (trans (comproj g) ⟦ funct f ⟅ y ⟆ ⟧ ⋆⟨ c ⟩ trans (comproj f) ⟦ y ⟧)
 --       ≡⟨ sym (⋆assoc c (projfunc d'' ⟪ funct g ⟪ funct f ⟪ h , h ⟫ ⟫ ⟫) (trans (comproj g) ⟦ funct f ⟅ y ⟆ ⟧) (trans (comproj f) ⟦ y ⟧)) ⟩
  --  (projfunc d'' ⟪ funct g ⟪ funct f ⟪ h , h ⟫ ⟫ ⟫ ⋆⟨ c ⟩ trans (comproj g) ⟦ funct f ⟅ y ⟆ ⟧) ⋆⟨ c ⟩ trans (comproj f) ⟦ y ⟧
 --       ≡⟨ cong (λ f → f ⋆⟨ c ⟩ trans (comproj f) ⟦ y ⟧) (n-hom (trans (comproj g)) (funct f ⟪ h , h ⟫)) ⟩
  --  (trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ projfunc d' ⟪ funct f ⟪ h , h ⟫ ⟫) ⋆⟨ c ⟩ trans (comproj f) ⟦ y ⟧
  --      ≡⟨ ⋆assoc c (trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧) (projfunc d' ⟪ funct f ⟪ h , h ⟫ ⟫) (trans (comproj f) ⟦ y ⟧) ⟩
  --  trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ (projfunc d' ⟪ funct f ⟪ h , h ⟫ ⟫ ⋆⟨ c ⟩ trans (comproj f) ⟦ y ⟧)
  --      ≡⟨ cong (λ f → trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ f) (n-hom (trans (comproj f)) (h , h)) ⟩
  --  trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ (trans (comproj f) ⟦ x ⟧ ⋆⟨ c ⟩ h)
 --       ≡⟨ sym (⋆assoc c (trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧) (trans (comproj f) ⟦ x ⟧) h) ⟩
 --   (trans (comproj g) ⟦ funct f ⟅ x ⟆ ⟧ ⋆⟨ c ⟩ trans (comproj f) ⟦ x ⟧) ⋆⟨ c ⟩ h ∎
 ---- dispcat .functseq .f-ob (f , g) .comproj .niso x = catiso→isiso (isiso→catiso (niso (comproj g) (funct f ⟅ x ⟆)) ⋆ᵢ⟨ c ⟩ isiso→catiso (niso (comproj f) x))
 -- dispcat .functseq .f-hom = {!!}
 -- dispcat .functseq .f-id = {!!}
 -- dispcat .functseq .f-seq = {!!}
  
  --disp→Σ : dispCat-ob → Σ[ E ∈ Category ℓC ℓC' ] (Functor (cat E) C)
--  disp→Σ D = (record { cat = totalPrecat D ; isCat = isCatTotPrecat {D = D}}) , projFunc D

--  Σ→disp : Σ[ E ∈ Category ℓC ℓC' ] (Functor (cat E) C) → dispCat-ob
--  Σ→disp (E , F) .dC-ob x = fiber (F-ob F) x
--  Σ→disp (E , F) .dC-hom {x} {y} f (X , px) (Y , py) = fiber (F-hom F {x = X} {y = Y}) (morP px ⋆⟨ C ⟩ f ⋆⟨ C ⟩ invP py)
--  Σ→disp (E , F) .dC-homSet f (X , px) (Y , py) = Σ-Set (cat E [ X , Y ]) (λ g → F ⟪ g ⟫ ≡ (morP px ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ invP py) (isSetHom (isCat E)) (λ g → isProp→isSet (isSetHom isCatC (F ⟪ g ⟫) ((morP px ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ invP py)))
--  Σ→disp (E , F) .dC-id {x} (X , p) = (id (cat E) X) , eq
 --   where
 --   eq : F ⟪ id (cat E) X ⟫ ≡ (morP p ⋆⟨ C ⟩ id C x) ⋆⟨ C ⟩ invP p
--    eq = 
 --     F ⟪ id (cat E) X ⟫ ≡⟨ F-id F ⟩
 --     id C (F ⟅ X ⟆) ≡⟨ sym (retMorP p) ⟩
--      morP p ⋆⟨ C ⟩ invP p ≡⟨ cong (λ f → f ⋆⟨ C ⟩ invP p) (sym (⋆IdR C (morP p))) ⟩
--      (morP p ⋆⟨ C ⟩ id C x) ⋆⟨ C ⟩ invP p ∎ 
 -- Σ→disp (E , F) .dC-⋆ {x} {y} {z} {X , px} {Y , py} {Z , pz} {g} {h} (G , qG) (H , qH) = (G ⋆⟨ cat E ⟩ H) , eq
 --   where
 --   eq : F ⟪ G ⋆⟨ cat E ⟩ H ⟫ ≡ (morP px ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP pz
  --  eq =
  --    F ⟪ G ⋆⟨ cat E ⟩ H ⟫
  ----        ≡⟨ F-seq F G H ⟩
  --    F ⟪ G ⟫ ⋆⟨ C ⟩ F ⟪ H ⟫
  --        ≡⟨ cong (λ f → f ⋆⟨ C ⟩ F ⟪ H ⟫) qG ⟩
  ----    ((morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP py) ⋆⟨ C ⟩ F ⟪ H ⟫
   --       ≡⟨ cong (λ f → ((morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP py) ⋆⟨ C ⟩ f) qH ⟩ 
   --   ((morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP py) ⋆⟨ C ⟩ ((morP py ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz)
   --       ≡⟨ ⋆Assoc C (morP px ⋆⟨ C ⟩ g) (invP py) ((morP py ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz) ⟩
   --   (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (invP py ⋆⟨ C ⟩ ((morP py ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz))
   --       ≡⟨ cong (λ f → (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ f) (sym (⋆Assoc C (invP py) (morP py ⋆⟨ C ⟩ h) (invP pz))) ⟩
   --   (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((invP py ⋆⟨ C ⟩ (morP py ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP pz)
   --       ≡⟨ cong (λ f →  (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ invP pz)) (sym (⋆Assoc C (invP py) (morP py) h)) ⟩
   --   (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (((invP py ⋆⟨ C ⟩ morP py) ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz)
   --       ≡⟨ cong (λ f → (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((f ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz)) (secMorP py) ⟩
   --   (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((id C y ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz)
    --      ≡⟨ cong (λ f →  (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ invP pz)) (⋆IdL C h) ⟩
   --   (morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (h ⋆⟨ C ⟩ invP pz)
   --       ≡⟨ sym (⋆Assoc C (morP px ⋆⟨ C ⟩ g) h (invP pz)) ⟩
   --    ((morP px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP pz
   --       ≡⟨ cong (λ f → f ⋆⟨ C ⟩ invP pz) (⋆Assoc C (morP px) g h) ⟩
    --  (morP px ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP pz ∎
 -- Σ→disp (E , F) .dC-⋆IdL {x} {y} {f} {X , px} {Y , py} (G , p) = ΣPathP (eq , (toPathP (isSetHom isCatC (F ⟪ G ⟫) (morP px ⋆⟨ C ⟩ f ⋆⟨ C ⟩ invP py) _ p)))
 --   where
  --  eq : subst (λ _ → (cat E) [ X , Y ]) (⋆IdL C f) (id (cat E) X ⋆⟨ cat E ⟩ G) ≡ G
  --  eq = 
  --    subst (λ _ → (cat E) [ X , Y ]) (⋆IdL C f) (id (cat E) X ⋆⟨ cat E ⟩ G) ≡⟨ transportRefl (id (cat E) X ⋆⟨ cat E ⟩ G) ⟩
  --    id (cat E) X ⋆⟨ cat E ⟩ G ≡⟨ ⋆IdL (cat E) G ⟩
   --   G ∎
 -- Σ→disp (E , F) .dC-⋆IdR {x} {y} {f} {X , px} {Y , py} (G , p) = ΣPathP (eq , (toPathP (isSetHom isCatC (F ⟪ G ⟫) (morP px ⋆⟨ C ⟩ f ⋆⟨ C ⟩ invP py) _ p)))
   -- where
  --  eq : subst (λ _ → (cat E) [ X , Y ]) (⋆IdL C f) (G ⋆⟨ cat E ⟩ id (cat E) Y) ≡ G
  --  eq = 
   --   subst (λ _ → (cat E) [ X , Y ]) (⋆IdL C f) (G ⋆⟨ cat E ⟩ id (cat E) Y) ≡⟨ transportRefl (G ⋆⟨ cat E ⟩ id (cat E) Y) ⟩
   --   G ⋆⟨ cat E ⟩ id (cat E) Y ≡⟨ ⋆IdR (cat E) G ⟩
   --   G ∎
 -- Σ→disp (E , F) .dC-⋆Assoc {w} {x} {y} {z} {(W , pw)} {(X , px)} {(Y , py)} {(Z , pz)} {g} {h} {k} (G , pG) (H , pH) (K , pK) = ΣPathP (eq , toPathP (isSetHom isCatC (F ⟪ G ⋆⟨ cat E ⟩ (H ⋆⟨ cat E ⟩ K) ⟫) ((morP pw ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ (h ⋆⟨ C ⟩ k))) ⋆⟨ C ⟩ invP pz) _ _))
  --  where
  -----  eq : subst (λ _ → (cat E) [ W , Z ]) (⋆Assoc C g h k) ((G ⋆⟨ cat E ⟩ H) ⋆⟨ cat E ⟩ K) ≡ G ⋆⟨ cat E ⟩ (H ⋆⟨ cat E ⟩ K)
  --  eq = 
  --     subst (λ _ → (cat E) [ W , Z ]) (⋆Assoc C g h k) ((G ⋆⟨ cat E ⟩ H) ⋆⟨ cat E ⟩ K) ≡⟨ transportRefl ((G ⋆⟨ cat E ⟩ H) ⋆⟨ cat E ⟩ K) ⟩
   --    (G ⋆⟨ cat  E ⟩ H) ⋆⟨ cat E ⟩ K ≡⟨ ⋆Assoc (cat E) G H K ⟩
  --     G ⋆⟨ cat E ⟩ (H ⋆⟨ cat E ⟩ K) ∎


 -- Σ→dips→Σ : ((E , F) : Σ[ E ∈ Category ℓC ℓC' ] (Functor (cat E) C)) → disp→Σ (Σ→disp (E , F)) ≡ (E , F)
 -- Σ→dips→Σ (E , F) = ΣPathP ({!!} , toPathP {!!})
