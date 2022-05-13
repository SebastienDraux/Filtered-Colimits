module Filtered-Colimits.DisplayedCategories.DisplayedCategories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Sigma

open import Filtered-Colimits.Category.Functors
open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.General.Lemma

private
  variable
     ℓC ℓC' : Level

open Category
open Functor
open isUnivalent
open CatIso
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
        morP C p ⋆⟨ C ⟩ invP C p                  ≡⟨ cong (λ f → f ⋆⟨ C ⟩ invP C p) (sym (⋆IdR C (morP C p))) ⟩
        (morP C p ⋆⟨ C ⟩ id C) ⋆⟨ C ⟩ invP C p    ∎ 
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

module _ {ℓC ℓC' ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  record isDispPreorder : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      isSetFiber : (x : ob C) → isSet (D ⦅ x ⦆)
      isPropMor : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → isProp (D [ f , X , Y ]ᴰ)

  open isDispPreorder

  isProp-isDispPreorder : isProp isDispPreorder
  isProp-isDispPreorder isDisPreoderD isDisPreoderD' i .isSetFiber = isPropΠ (λ _ → isPropIsSet) (isSetFiber isDisPreoderD) (isSetFiber isDisPreoderD') i
  isProp-isDispPreorder isDisPreoderD isDisPreoderD' i .isPropMor = isPropΠ3 (λ _ _ _ → isPropIsProp) (isPropMor isDisPreoderD) (isPropMor isDisPreoderD') i
  isLeftFibration : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))
  isLeftFibration = {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → ∃![ Y ∈ D ⦅ y ⦆ ] (D [ f , X , Y ]ᴰ)

  isProp-isLeftFibration : isProp isLeftFibration
  isProp-isLeftFibration = isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isPropIsContr))

  module _ (isLeftFibD : isLeftFibration)
           {x y : ob C}
           (f : C [ x , y ])
           (X : D ⦅ x ⦆) where
    
    leftFib-getOb : D ⦅ y ⦆
    leftFib-getOb = fst (fst (isLeftFibD f X))
  
    leftFib-getHom :  D [ f , X , leftFib-getOb ]ᴰ
    leftFib-getHom = snd (fst (isLeftFibD f X))

    leftFib-unicityOb : ((Y , F) : Σ[ Y ∈ D ⦅ y ⦆ ] (D [ f , X , Y ]ᴰ)) → leftFib-getOb  ≡ Y
    leftFib-unicityOb (Y , F) = cong fst (snd (isLeftFibD f X) (Y , F))

module _ {ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD')  where

  isCocartesian : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → D [ f , X , Y ]ᴰ → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isCocartesian {x} {y} f X Y F = {z : ob C} → {g : C [ y , z ]} → {h : C [ x , z ]} → (p : f ⋆⟨ C ⟩ g ≡ h) → {Z : D ⦅ z ⦆} → (H : D [ h , X , Z ]ᴰ) →
                                           ∃![ G ∈ D [ g , Y , Z ]ᴰ ] subst (λ h → D [ h , X , Z ]ᴰ) p (F ⋆⟨ D ⟩ᴰ G) ≡ H
                                           
  isCocartesian-getHom : {x y z : ob C} → (f : C [ x , y ])→ {g : C [ y , z ]} → {h : C [ x , z ]} → (p : f ⋆⟨ C ⟩ g ≡ h) →
                         (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (Z : D ⦅ z ⦆)→ (F : D [ f , X , Y ]ᴰ) → D [ h , X , Z ]ᴰ → isCocartesian f X Y F → D [ g , Y , Z ]ᴰ
  isCocartesian-getHom f p X Y Z F H isCocart = fst (fst (isCocart p H))

  isProp-isCocartesian : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F : D [ f , X , Y ]ᴰ) → isProp (isCocartesian f X Y F)
  isProp-isCocartesian F = isPropImplicitΠ2 λ _ _ → isPropImplicitΠ (λ _ → isPropΠ (λ _ → isPropImplicitΠ (λ _ → isPropΠ (λ _ → isPropIsContr))))
  
  isCocartesianFibration : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isCocartesianFibration = {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → ∃![ Y ∈ D ⦅ y ⦆ ] Σ[ F ∈ D [ f , X , Y ]ᴰ ] isCocartesian f X Y F

  isProp-isCocartesianFibration : isProp isCocartesianFibration
  isProp-isCocartesianFibration = isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ _ _ → isPropIsContr))
  
  module _ (isCocartFibD : isCocartesianFibration)
           {x y : ob C}
           (f : C [ x , y ])
           (X : D ⦅ x ⦆) where

    isCocartesianFibration-getOb : D ⦅ y ⦆
    isCocartesianFibration-getOb = fst (fst (isCocartFibD f X))

    isCocartesianFibration-unicityOb : (Y : D ⦅ y ⦆) → Σ[ F ∈ D [ f , X , Y ]ᴰ ] isCocartesian f X Y F → isCocartesianFibration-getOb ≡ Y
    isCocartesianFibration-unicityOb Y (F , isCocartF) = cong fst (snd (isCocartFibD f X) (Y , F , isCocartF))

    isCocartesianFibration-getHom : D [ f , X , isCocartesianFibration-getOb ]ᴰ
    isCocartesianFibration-getHom = fst (snd (fst (isCocartFibD f X)))

    isCocartesianFibration-getIsCocart : isCocartesian f X isCocartesianFibration-getOb isCocartesianFibration-getHom
                                       
    isCocartesianFibration-getIsCocart = snd (snd (fst (isCocartFibD f X)))

open isDispPreorder

module _ (C : Category ℓC ℓC') where

  record dispPreorder (ℓD ℓD' : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))) where
    field
      disp-cat : dispCat C ℓD ℓD'
      is-disp-preorder : isDispPreorder disp-cat



