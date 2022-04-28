{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Sigma

open import Functors
open import IsoCat
open import Lemma
open import PosetCat
open import Poset

private
  variable
     ℓC ℓC' : Level

open Category
open Functor
open isUnivalent
open PosetStr
open IsPoset
open CatIso
open PosetReasoning
open eqFunct

record dispCat (C : Category ℓC ℓC') (ℓD ℓD' : Level) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc (ℓ-max ℓD ℓD'))) where
  field
    dC-ob : ob C → Type ℓD
    dC-hom : {x y : ob C} → C [ x , y ] → dC-ob x → dC-ob y → Type ℓD'
    dC-homSet : {x y : ob C} → (f : C [ x , y ]) → (X : dC-ob x) → (Y : dC-ob y) → isSet (dC-hom f X Y)
    dC-id : {x : ob C} → {X : dC-ob x} → dC-hom (id C) X X
    dC-⋆ : {x y z : ob C} → {X : dC-ob x} → {Y : dC-ob y} → {Z : dC-ob z} → {f : C [ x , y ]} → {g : C [ y , z ]} → dC-hom f X Y → dC-hom g Y Z → dC-hom (f ⋆⟨ C ⟩ g) X Z
    dC-⋆IdL : {x y : ob C} → {f : C [ x , y ]}  → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → subst (λ f → dC-hom f X Y) (⋆IdL C f) (dC-⋆ dC-id F) ≡ F
    dC-⋆IdR : {x y : ob C} → {f : C [ x , y ]} → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → subst (λ f → dC-hom f X Y) (⋆IdR C f) (dC-⋆ F dC-id) ≡ F
    dC-⋆Assoc : {w x y z : ob C} → {W : dC-ob w} → {X : dC-ob x} → {Y : dC-ob y} → {Z : dC-ob z} → {f : C [ w , x ]} → {g : C [ x , y ]} → {h : C [ y , z ]} → (F : dC-hom f W X) → (G : dC-hom g X Y) → (H : dC-hom h Y Z) → subst (λ f⋆g⋆h → dC-hom f⋆g⋆h W Z) (⋆Assoc C f g h) ((dC-⋆ (dC-⋆ F G) H)) ≡ dC-⋆ F (dC-⋆ G H)

open dispCat

module _ {ℓC ℓC' ℓD ℓD' : Level}
         {C : Category ℓC ℓC'} where

  _⦅_⦆ : dispCat C ℓD ℓD' → ob C → Type ℓD
  D ⦅ x ⦆ = dC-ob D x

  _[_,_,_]ᴰ : (D : dispCat C ℓD ℓD') → {x y : ob C} → C [ x , y ] → D ⦅ x ⦆ → D ⦅ y ⦆ → Type ℓD'
  D [ f , X , Y ]ᴰ = dC-hom D f X Y

  dC-seq : (D : dispCat C ℓD ℓD') → {x y z : ob C} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → {Z : D ⦅ z ⦆} → {f : C [ x , y ]} → {g : C [ y , z ]} →
           D [ f , X , Y ]ᴰ → D [ g , Y , Z ]ᴰ → D [ (f ⋆⟨ C ⟩ g) , X , Z ]ᴰ
  dC-seq D F G = dC-⋆ D F G

  infixl 15 dC-seq
  syntax dC-seq D F G = F ⋆⟨ D ⟩ᴰ G

  record dispCat-Funct (D D' : dispCat C ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      dF-ob : {x : ob C} → dC-ob D x → dC-ob D' x
      dF-hom : {x y : ob C} → {f : C [ x , y ]} → {X : dC-ob D x} → {Y : dC-ob D y} → dC-hom D f X Y → dC-hom D' f (dF-ob X) (dF-ob Y)
      dF-id : {x : ob C} → {X : dC-ob D x} → dF-hom (dC-id D {X = X}) ≡ dC-id D'
      dF-seq : {x y z : ob C} → {X : dC-ob D x} → {Y : dC-ob D y} → {Z : dC-ob D z} → {f : C [ x , y ]} → {g : C [ y , z ]} → (F : dC-hom D f X Y) → (G : dC-hom D g Y Z) →
               dF-hom (dC-⋆ D F G) ≡ dC-⋆ D' (dF-hom F) (dF-hom G)

  open dispCat-Funct

  module _ {D D' : dispCat C ℓD ℓD'} where

    infix 30 _⟅_⟆ᴰ
    _⟅_⟆ᴰ : dispCat-Funct D D' → {x : ob C} → D ⦅ x ⦆ → D' ⦅ x ⦆
    𝑭 ⟅ X ⟆ᴰ = dF-ob 𝑭 X

    infix 30 _⟪_⟫ᴰ
    _⟪_⟫ᴰ : (𝑭 : dispCat-Funct D D') → {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → D [ f , X , Y ]ᴰ → D' [ f , 𝑭 ⟅ X ⟆ᴰ ,  𝑭 ⟅ Y ⟆ᴰ ]ᴰ
    𝑭 ⟪ F ⟫ᴰ = dF-hom 𝑭 F


  module _ (D : dispCat C ℓD ℓD')  where

    totalCat : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
    totalCat .ob = Σ[ x ∈ ob C ] D ⦅ x ⦆
    totalCat .Hom[_,_] (x , X) (y , Y) = Σ[ f ∈ C [ x , y ] ] D [ f , X , Y ]ᴰ
    totalCat .id {x , X} = id C , dC-id D
    totalCat ._⋆_ (f , F) (g , G) = f ⋆⟨ C ⟩ g , F ⋆⟨ D ⟩ᴰ G
    totalCat .⋆IdL (f , F) = ΣPathTransport→PathΣ (id C ⋆⟨ C ⟩ f , dC-id D ⋆⟨ D ⟩ᴰ F) (f , F) (⋆IdL C f , dC-⋆IdL D F)
    totalCat .⋆IdR (f , F) = ΣPathTransport→PathΣ (f ⋆⟨ C ⟩ id C , F ⋆⟨ D ⟩ᴰ dC-id D) (f , F) (⋆IdR C f , dC-⋆IdR D F)
    totalCat .⋆Assoc (f , F) (g , G) (h , H) = ΣPathTransport→PathΣ ((f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h , (F ⋆⟨ D ⟩ᴰ G) ⋆⟨ D ⟩ᴰ H) (f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) , F ⋆⟨ D ⟩ᴰ (G ⋆⟨ D ⟩ᴰ H)) (⋆Assoc C f g h , dC-⋆Assoc D F G H)
    totalCat .isSetHom {x , X} {y , Y} = isSetΣ (isSetHom C) (λ f → dC-homSet D f X Y)
  
    projFunct : Functor totalCat C
    projFunct .F-ob (x , X) = x
    projFunct .F-hom (f , F) = f
    projFunct .F-id = refl
    projFunct .F-seq f g = refl

    disp→Σ : dispCat C ℓD ℓD' → Σ[ E ∈ Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD') ] (Functor E C)
    disp→Σ D = totalCat , projFunct

  
    Σ→disp : Σ[ E ∈ Category ℓD ℓD' ] (Functor E C) → dispCat C (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
    Σ→disp (E , F) .dC-ob x = fiber (F-ob F) x
    Σ→disp (E , F) .dC-hom {x} {y} f (X , px) (Y , py) = fiber (F-hom F {x = X} {y = Y}) (morP C px ⋆⟨ C ⟩ f ⋆⟨ C ⟩ invP C py)
    Σ→disp (E , F) .dC-homSet f (X , px) (Y , py) = isSetΣ (isSetHom E) (λ f → isProp→isSet (isSetHom C _ _))
    Σ→disp (E , F) .dC-id {x} {X , p} = (id E) , eq
      where
      eq : F ⟪ id E ⟫ ≡ (morP C p ⋆⟨ C ⟩ id C) ⋆⟨ C ⟩ invP C p
      eq = 
        F ⟪ id E ⟫                               ≡⟨ F-id F ⟩
        id C                                     ≡⟨ sym (retMorP C p) ⟩
        morP C p ⋆⟨ C ⟩ invP C p                 ≡⟨ cong (λ f → f ⋆⟨ C ⟩ invP C p) (sym (⋆IdR C (morP C p))) ⟩
        (morP C p ⋆⟨ C ⟩ id C) ⋆⟨ C ⟩ invP C p   ∎ 
    Σ→disp (E , F) .dC-⋆ {x} {y} {z} {X , px} {Y , py} {Z , pz} {g} {h} (G , qG) (H , qH) = (G ⋆⟨ E ⟩ H) , eq
      where
      eq : F ⟪ G ⋆⟨ E ⟩ H ⟫ ≡ (morP C px ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP C pz
      eq =
        F ⟪ G ⋆⟨ E ⟩ H ⟫
            ≡⟨ F-seq F _ _ ⟩
        F ⟪ G ⟫ ⋆⟨ C ⟩ F ⟪ H ⟫
            ≡⟨ cong (λ f → f ⋆⟨ C ⟩ F ⟪ H ⟫) qG ⟩
        ((morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP C py) ⋆⟨ C ⟩ F ⟪ H ⟫
            ≡⟨ cong (λ f → ((morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP C py) ⋆⟨ C ⟩ f) qH ⟩ 
        ((morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ invP C py) ⋆⟨ C ⟩ ((morP C py ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz)
            ≡⟨ ⋆Assoc C _ _ _ ⟩
        (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (invP C py ⋆⟨ C ⟩ ((morP C py ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz))
            ≡⟨ cong (λ f → (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ f) (sym (⋆Assoc C _ _ _)) ⟩
        (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((invP C py ⋆⟨ C ⟩ (morP C py ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP C pz)
            ≡⟨ cong (λ f →  (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ invP C pz)) (sym (⋆Assoc C _ _ _)) ⟩
        (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (((invP C py ⋆⟨ C ⟩ morP C py) ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz)
            ≡⟨ cong (λ f → (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((f ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz)) (secMorP C py) ⟩
        (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ((id C ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz)
            ≡⟨ cong (λ f →  (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ invP C pz)) (⋆IdL C _) ⟩
        (morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ (h ⋆⟨ C ⟩ invP C pz)
            ≡⟨ sym (⋆Assoc C _ _ _) ⟩
         ((morP C px ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ invP C pz
            ≡⟨ cong (λ f → f ⋆⟨ C ⟩ invP C pz) (⋆Assoc C _ _ _) ⟩
        (morP C px ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h)) ⋆⟨ C ⟩ invP C pz ∎
    Σ→disp (E , F) .dC-⋆IdL {x} {y} {f} {X , px} {Y , py} (G , p) = ΣPathP (eq , (toPathP (isSetHom C _ _ _ _)))
      where
      eq : subst (λ _ → E [ X , Y ]) (⋆IdL C f) (id E ⋆⟨ E ⟩ G) ≡ G
      eq = 
        subst (λ _ → E [ X , Y ]) (⋆IdL C f) (id E ⋆⟨ E ⟩ G)   ≡⟨ transportRefl (id E ⋆⟨ E ⟩ G) ⟩
        id E ⋆⟨ E ⟩ G                                           ≡⟨ ⋆IdL E _ ⟩
        G                                                       ∎
    Σ→disp (E , F) .dC-⋆IdR {x} {y} {f} {X , px} {Y , py} (G , p) = ΣPathP (eq , (toPathP (isSetHom C _ _ _ _)))
      where
      eq : subst (λ _ → E [ X , Y ]) (⋆IdL C f) (G ⋆⟨ E ⟩ id E) ≡ G
      eq = 
        subst (λ _ → E [ X , Y ]) (⋆IdL C f) (G ⋆⟨ E ⟩ id E)   ≡⟨ transportRefl (G ⋆⟨ E ⟩ id E) ⟩
        G ⋆⟨ E ⟩ id E                                           ≡⟨ ⋆IdR E _ ⟩
        G                                                       ∎
    Σ→disp (E , F) .dC-⋆Assoc {w} {x} {y} {z} {(W , pw)} {(X , px)} {(Y , py)} {(Z , pz)} {g} {h} {k} (G , pG) (H , pH) (K , pK) = ΣPathP (eq , toPathP (isSetHom C _ _ _ _))
      where
      eq : subst (λ _ → E [ W , Z ]) (⋆Assoc C g h k) ((G ⋆⟨ E ⟩ H) ⋆⟨ E ⟩ K) ≡ G ⋆⟨ E ⟩ (H ⋆⟨ E ⟩ K)
      eq = 
         subst (λ _ → E [ W , Z ]) (⋆Assoc C g h k) ((G ⋆⟨ E ⟩ H) ⋆⟨ E ⟩ K)   ≡⟨ transportRefl ((G ⋆⟨ E ⟩ H) ⋆⟨ E ⟩ K) ⟩
         (G ⋆⟨ E ⟩ H) ⋆⟨ E ⟩ K                                                 ≡⟨ ⋆Assoc E _ _ _ ⟩
         G ⋆⟨ E ⟩ (H ⋆⟨ E ⟩ K)                                                 ∎

    record dispCatIso {x : ob C} (X X' : D ⦅ x ⦆) : Type ℓD' where
      field
        dC-mor : D [ id C , X , X' ]ᴰ
        dC-inv : D [ id C , X' , X ]ᴰ
        dC-sec : subst (λ f → D [ f , X' , X' ]ᴰ) (⋆IdL C (id C)) (dC-inv ⋆⟨ D ⟩ᴰ dC-mor) ≡ dC-id D
        dC-ret : subst (λ f → D [ f , X , X ]ᴰ) (⋆IdR C (id C)) (dC-mor ⋆⟨ D ⟩ᴰ dC-inv) ≡ dC-id D


    record dispCatIso' {x : ob C} (f : CatIso C x x) (X X' : D ⦅ x ⦆) : Type ℓD' where --iso over iso?
      field
        dC-mor : D [ mor f , X , X' ]ᴰ
        dC-inv : D [ inv f , X' , X ]ᴰ
        dC-sec : subst (λ f → D [ f , X' , X' ]ᴰ) (sec f) (dC-inv ⋆⟨ D ⟩ᴰ dC-mor) ≡ dC-id D
        dC-ret : subst (λ f → D [ f , X , X ]ᴰ) (ret f) (dC-mor ⋆⟨ D ⟩ᴰ dC-inv) ≡ dC-id D
        
    open dispCatIso
  
    idDispCatIso : {x : ob C} → {X : D ⦅ x ⦆} → dispCatIso X X
    idDispCatIso .dC-mor = dC-id D
    idDispCatIso .dC-inv = dC-id D
    idDispCatIso .dC-sec = dC-⋆IdL D (dC-id D)
    idDispCatIso .dC-ret = dC-⋆IdR D (dC-id D)

    dC-pathToIso : {x : ob C} → {X X' : D ⦅ x ⦆} → X ≡ X' → dispCatIso X X'
    dC-pathToIso {X = X} p = J (λ X' p → dispCatIso X X') idDispCatIso p

    record dC-isUnivalent : Type (ℓ-max (ℓ-max ℓC ℓD) ℓD') where
      field
        dC-univ : {x : ob C} → (X X' : D ⦅ x ⦆) → isEquiv (dC-pathToIso {x = x} {X = X} {X' = X'})
    
      dC-univEquiv : {x : ob C} → (X X' : D ⦅ x ⦆) → (X ≡ X') ≃ (dispCatIso X X')
      dC-univEquiv X X' = dC-pathToIso , dC-univ X X'

    open dC-isUnivalent

    isProp-dC-isUnivalent : isProp dC-isUnivalent
    isProp-dC-isUnivalent isUniv isUniv' i .dC-univ = isPropΠ2 (λ _ _ → isPropIsEquiv _) (dC-univ isUniv) (dC-univ isUniv') i

  open dispCatIso

  record isDispOverPoset (D : dispCat C ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      isSetFiber : (x : ob C) → isSet (D ⦅ x ⦆)
      isPropMor : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → isProp (D [ f , X , Y ]ᴰ)
      morImpl : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → ∃![ Y ∈ D ⦅ y ⦆ ] (D [ f , X , Y ]ᴰ) --Σ or ∃ (to have a proposition) instead of ∃!
      isUniv : dC-isUnivalent D
      
  open isDispOverPoset
  
  isProp-isDispOverPoset : (D : dispCat C ℓD ℓD') → isProp (isDispOverPoset D)
  isProp-isDispOverPoset D overPosetD overPosetD' i .isSetFiber = isPropΠ (λ _ → isPropIsSet) (isSetFiber overPosetD) (isSetFiber overPosetD') i
  isProp-isDispOverPoset D overPosetD overPosetD' i .isPropMor = isPropΠ3 (λ _ _ _ → isPropIsProp) (isPropMor overPosetD) (isPropMor overPosetD') i
  isProp-isDispOverPoset D overPosetD overPosetD' i .morImpl = isPropΠ2 (λ _ _ → isPropIsContr) (morImpl overPosetD) (morImpl overPosetD') i
  isProp-isDispOverPoset D overPosetD overPosetD' i .isUniv = isProp-dC-isUnivalent D (isUniv overPosetD) (isUniv overPosetD') i
  
open isDispOverPoset
open dispCatIso
open dC-isUnivalent

module _ {ℓD ℓD' : Level}
         {C : Category ℓC ℓC'} where

  fromPOSET : Functor C (POSET ℓD ℓD') → dispCat C ℓD ℓD'
  fromPOSET F .dC-ob x = fst (F ⟅ x ⟆)
  fromPOSET F .dC-hom {x} {y} f a b = F ⟪ f ⟫ ⟅ a ⟆ ≤[ F ⟅ y ⟆ ] b
  fromPOSET F .dC-homSet {x} {y} f a b = isProp→isSet (is-prop-valued (isPoset (snd (F ⟅ y ⟆))) _ _)
  fromPOSET F .dC-id {x} {a} = ≡→≤ (F ⟅ x ⟆) (cong (λ F → F ⟅ a ⟆) (F-id F))
  fromPOSET F .dC-⋆ {x} {y} {z} {a} {b} {c} {f} {g} p q =
    (F ⟪ f ⋆⟨ C ⟩ g ⟫) ⟅ a ⟆          ≤[ F ⟅ z ⟆ ]⟨ ≡→≤ (F ⟅ z ⟆) (cong (λ F → F ⟅ a ⟆) (F-seq F _ _)) ⟩
    (F ⟪ g ⟫) ⟅ (F ⟪ f ⟫) ⟅ a ⟆ ⟆    ≤[ F ⟅ z ⟆ ]⟨ F ⟪ g ⟫ ⟪ p ⟫ ⟩
    F ⟪ g ⟫ ⟅ b ⟆                    ≤[ F ⟅ z ⟆ ]⟨ q ⟩ 
    c [ F ⟅ z ⟆ ]□
  fromPOSET F .dC-⋆IdL {x} {y} p = is-prop-valued (isPoset (snd (F ⟅ y ⟆))) _ _ _ _
  fromPOSET F .dC-⋆IdR {x} {y} p = is-prop-valued (isPoset (snd (F ⟅ y ⟆))) _ _ _ _
  fromPOSET F .dC-⋆Assoc {z = z} p q r = is-prop-valued (isPoset (snd (F ⟅ z ⟆))) _ _ _ _
  
  toPoset : (D : dispCat C ℓD ℓD') → isDispOverPoset D → ob C → Poset ℓD ℓD'
  toPoset D overPosetD x = D ⦅ x ⦆ , posetStruct
    where
    posetStruct : PosetStr ℓD' (D ⦅ x ⦆)
    posetStruct ._≤_ a b = D [ id C , a , b ]ᴰ --not sure
    posetStruct .isPoset .is-set = isSetFiber overPosetD x
    posetStruct .isPoset .is-prop-valued = isPropMor overPosetD (id C)
    posetStruct .isPoset .is-refl a = dC-id D
    posetStruct .isPoset .is-trans a b c f g = subst (λ f → D [ f , a , c ]ᴰ) (⋆IdL C (id C)) (f ⋆⟨ D ⟩ᴰ g)
    posetStruct .isPoset .is-antisym a b f g = equivFun (invEquiv (dC-univEquiv (isUniv overPosetD) a b)) isom
      where
      isom : dispCatIso D a b
      isom .dC-mor = f
      isom .dC-inv = g
      isom .dC-sec = isPropMor overPosetD (id C) b b _ _
      isom .dC-ret = isPropMor overPosetD (id C) a a _ _
  
  toPOSET : (D : dispCat C ℓD ℓD') → isDispOverPoset D → Functor C (POSET ℓD ℓD')
  toPOSET D overPosetD = F
    where
    toPoset' : (x : ob C) → Poset ℓD ℓD'
    toPoset' x = toPoset D overPosetD x
    
    G : {x y : ob C} → (f : C [ x , y ]) → Functor (PosetCategory (toPoset' x)) (PosetCategory (toPoset' y))
    G {x} {y} f .F-ob a = fst (fst (morImpl overPosetD f a))
    G {x} {y} f .F-hom {a} {b} a≤b = {!!}
    G {x} {y} f .F-id = is-prop-valued (isPoset (snd (toPoset' y))) _ _ _ _
    G {x} {y} f .F-seq a≤b b≤c = is-prop-valued (snd (toPoset' y)) _ _ _ _
    
    F : Functor C (POSET ℓD ℓD')
    F .F-ob x = toPoset' x
    F .F-hom f = G f
    F .F-id {x} = eqFunct→≡ eqG-id
      where
      eqG-id : eqFunct (G (id C {x})) 𝟙⟨ PosetCategory (toPoset' x) ⟩
      eqG-id .eq-ob a = cong fst (snd (morImpl overPosetD (id C) a) (a , (dC-id D)))
      eqG-id .eq-hom a≤b = is-prop-valued (isPoset (snd (toPoset' x))) _ _ _ _
    F .F-seq {x} {y} {z} f g = eqFunct→≡ eqG-seq
      where
      eqG-seq : eqFunct (G (f ⋆⟨ C ⟩ g)) (G f ⋆ᶠ G g)
      eqG-seq .eq-ob a = cong fst (snd (morImpl overPosetD (f ⋆⟨ C ⟩ g) a) (_ , snd (fst (morImpl overPosetD f a)) ⋆⟨ D ⟩ᴰ snd (fst (morImpl overPosetD g _))))
      eqG-seq .eq-hom a≤b = is-prop-valued (isPoset (snd (toPoset' z))) _ _ _ _

--  fromPOSET' : Functor C (POSET' ℓD ℓD') → dispCat C ℓD ℓD'
--  fromPOSET' F .dC-ob x = fst (F ⟅ x ⟆)
--  fromPOSET' F .dC-hom {x} {y} f a b = _≤_ (snd (F ⟅ y ⟆)) ((F ⟪ f ⟫) a) b
--  fromPOSET' F .dC-homSet {x} {y} f a b = isProp→isSet (snd (F ⟅ y ⟆) .isPoset .is-prop-valued _ _)
--  fromPOSET' F .dC-id {x} {a} = subst (λ b → _≤_ (snd (F ⟅ x ⟆)) b a) (funExt⁻ (sym (F-id F)) a) (is-refl (isPoset (snd (F ⟅ x ⟆))) a)
--  fromPOSET' F .dC-⋆ {x} {y} {z} {a} {b} {c} {f} {g} p q =
--    (F ⟪ f ⋆⟨ C ⟩ g ⟫) a       ≤[ F ⟅ z ⟆ ]⟨ ≡→≤ (F ⟅ z ⟆) (funExt⁻ (F-seq F _ _) a) ⟩
--    (F ⟪ g ⟫) ((F ⟪ f ⟫) a)    ≤[ F ⟅ z ⟆ ]⟨ {!!} ⟩
--    (F ⟪ g ⟫) b                ≤[ F ⟅ z ⟆ ]⟨ q ⟩ 
--    c [ F ⟅ z ⟆ ]□
  --fromPOSET' F .dC-⋆IdL {x} {y} p = snd (F ⟅ y ⟆) .isPoset .is-set _ _ _ _
  --fromPOSET' F .dC-⋆IdR {x} {y} p = snd (F ⟅ y ⟆) .isPoset .is-set _ _ _ _
  --fromPOSET' F .dC-⋆Assoc {z = z} p q r = snd (F ⟅ z ⟆) .isPoset .is-set _ _ _ _

--  toPOSET' : (D : dispCat C ℓD ℓD') → isDispOverPoset D → Functor C (POSET' ℓD ℓD')
--  toPOSET' D overPosetD .F-ob x = toPoset D overPosetD x
 -- toPOSET' D overPosetD .F-hom f a = fst (fst (morImpl overPosetD f a))
--  toPOSET' D overPosetD .F-id = funExt (λ a → cong fst (snd (morImpl overPosetD (id C) a) (a , (dC-id D))))
--  toPOSET' D overPosetD .F-seq f g = funExt (λ a → cong fst (snd (morImpl overPosetD (f ⋆⟨ C ⟩ g) a) (_ , snd (fst (morImpl overPosetD f a)) ⋆⟨ D ⟩ᴰ snd (fst (morImpl overPosetD g _)))))

  overPoset-fromPOSET' : (F : Functor C (POSET ℓD ℓD')) → isDispOverPoset (fromPOSET F)
  overPoset-fromPOSET' F .isSetFiber x = is-set (isPoset (snd (F ⟅ x ⟆)))
  overPoset-fromPOSET' F .isPropMor f a b = {!!} --is-prop-valued (isPoset {!!}) a {!!} --Only id ?
  overPoset-fromPOSET' F .morImpl {x} {y} f a = ((F ⟪ f ⟫ ⟅ a ⟆) , is-refl (isPoset (snd (F ⟅ y ⟆))) _) , λ {(b , p) → Σ≡Prop {!!} {!!}} --can't prove unicity
--  overPoset-fromPOSET' F .isUniv .dC-univ {x} a b .equiv-proof f = ({!!} , {!!}) , {!!}
--    where
   -- a≡b : a ≡ b
    --a≡b = sym (funExt⁻ (F-id F) a) ∙ dC-mor f
