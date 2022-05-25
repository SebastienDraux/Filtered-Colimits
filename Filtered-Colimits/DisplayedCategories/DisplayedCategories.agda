module Filtered-Colimits.DisplayedCategories.DisplayedCategories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Data.Sigma

open import Filtered-Colimits.Category.Functors
open import Filtered-Colimits.Category.IsoCat

private
  variable
     ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

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
    dC-⋆IdL : {x y : ob C} → {f : C [ x , y ]}  → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → PathP (λ i → dC-hom (⋆IdL C f i) X Y) (dC-⋆ dC-id F) F
    dC-⋆IdR : {x y : ob C} → {f : C [ x , y ]} → {X : dC-ob x} → {Y : dC-ob y} → (F : dC-hom f X Y) → PathP (λ i → dC-hom (⋆IdR C f i) X Y) (dC-⋆ F dC-id) F
    dC-⋆Assoc : {w x y z : ob C} → {W : dC-ob w} → {X : dC-ob x} → {Y : dC-ob y} → {Z : dC-ob z} → {f : C [ w , x ]} → {g : C [ x , y ]} → {h : C [ y , z ]} →
                (F : dC-hom f W X) → (G : dC-hom g X Y) → (H : dC-hom h Y Z) → PathP (λ i → dC-hom (⋆Assoc C f g h i) W Z) (dC-⋆ (dC-⋆ F G) H) (dC-⋆ F (dC-⋆ G H))

open dispCat

module _ {C : Category ℓC ℓC'} where

  module _ where

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

      totalCat : Category _ _
      totalCat .ob = Σ[ x ∈ ob C ] D ⦅ x ⦆
      totalCat .Hom[_,_] (x , X) (y , Y) = Σ[ f ∈ C [ x , y ] ] D [ f , X , Y ]ᴰ
      totalCat .id {x , X} = id C , dC-id D
      totalCat ._⋆_ (f , F) (g , G) = f ⋆⟨ C ⟩ g , F ⋆⟨ D ⟩ᴰ G
      totalCat .⋆IdL (f , F) = ΣPathP (⋆IdL C _ , dC-⋆IdL D F)
      totalCat .⋆IdR (f , F) = ΣPathP (⋆IdR C _ , dC-⋆IdR D F)
      totalCat .⋆Assoc (f , F) (g , G) (h , H) = ΣPathP (⋆Assoc C _ _ _ , dC-⋆Assoc D F G H)
      totalCat .isSetHom {x , X} {y , Y} = isSetΣ (isSetHom C) (λ f → dC-homSet D f X Y)
  
      projFunct : Functor totalCat C
      projFunct .F-ob (x , X) = x
      projFunct .F-hom (f , F) = f
      projFunct .F-id = refl
      projFunct .F-seq f g = refl

      disp→Σ : dispCat C ℓD ℓD' → Σ[ E ∈ Category _ _ ] (Functor E C)
      disp→Σ D = totalCat , projFunct

  
      Σ→disp : Σ[ E ∈ Category ℓD ℓD' ] (Functor E C) → dispCat C _ _
      Σ→disp (E , F) .dC-ob x = fiber (F-ob F) x
      Σ→disp (E , F) .dC-hom {x} {y} f (X , px) (Y , py) = fiber (F-hom F {x = X} {y = Y}) (subst2 (λ x y → C [ x , y ]) (sym px) (sym py) f) --(morP C px ⋆⟨ C ⟩ f ⋆⟨ C ⟩ invP C py)
      Σ→disp (E , F) .dC-homSet f (X , px) (Y , py) = isSetΣ (isSetHom E) (λ f → isProp→isSet (isSetHom C _ _))
      Σ→disp (E , F) .dC-id {x} {X , p} = id E , F-id F ∙ sym (fromPathP (substId C (sym p)))
      Σ→disp (E , F) .dC-⋆ {X = X , px} {Y , py} {Z , pz} {g} {h} (G , qG) (H , qH) = G ⋆⟨ E ⟩ H ,
              F-seq F _ _ ∙ cong₂ (λ FG FH → FG ⋆⟨ C ⟩ FH) qG qH ∙ sym (fromPathP (subst3Seq C (sym px) (sym py) (sym pz) g h))
      Σ→disp (E , F) .dC-⋆IdL (G , p) = ΣPathP (⋆IdL E _ , isProp→PathP (λ _ → isSetHom C _ _) _ _)
      Σ→disp (E , F) .dC-⋆IdR (G , p) = ΣPathP (⋆IdR E _ , isProp→PathP (λ _ → isSetHom C _ _) _ _) 
      Σ→disp (E , F) .dC-⋆Assoc (G , pG) (H , pH) (K , pK) = ΣPathP ((⋆Assoc E _ _ _) , isProp→PathP (λ _ → isSetHom C _ _) _ _)

  module _ (D : dispCat C ℓD ℓD') where
  
    record isDispPreorder : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))) where
      field
        isSetFiber : (x : ob C) → isSet (D ⦅ x ⦆)
        isPropMor : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → isProp (D [ f , X , Y ]ᴰ)
  
    open isDispPreorder
  
    isProp-isDispPreorder : isProp isDispPreorder
    isProp-isDispPreorder isDispPreoderD isDispPreoderD' i .isSetFiber = isPropΠ (λ _ → isPropIsSet) (isSetFiber isDispPreoderD) (isSetFiber isDispPreoderD') i
    isProp-isDispPreorder isDispPreoderD isDispPreoderD' i .isPropMor = isPropΠ3 (λ _ _ _ → isPropIsProp) (isPropMor isDispPreoderD) (isPropMor isDispPreoderD') i
  
  
    isLeftFibration : Type _
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

      leftFib-unicityOb : ((Y , F) : Σ[ Y ∈ D ⦅ y ⦆ ] (D [ f , X , Y ]ᴰ)) → leftFib-getOb ≡ Y
      leftFib-unicityOb (Y , F) = cong fst (snd (isLeftFibD f X) (Y , F))

      leftFib-unicityHom : ((Y , F) : Σ[ Y ∈ D ⦅ y ⦆ ] (D [ f , X , Y ]ᴰ)) → PathP (λ i → D [ f , X , leftFib-unicityOb (Y , F) i ]ᴰ) leftFib-getHom F
      leftFib-unicityHom (Y , F) = cong snd (snd (isLeftFibD f X) (Y , F))

    leftFib-seq : (isLeftFibD : isLeftFibration) → {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : D ⦅ x ⦆) →
                  leftFib-getOb isLeftFibD (f ⋆⟨ C ⟩ g) X ≡ leftFib-getOb isLeftFibD g (leftFib-getOb isLeftFibD f X)
    leftFib-seq isLeftFibD f g X = leftFib-unicityOb isLeftFibD (f ⋆⟨ C ⟩ g) X
                                   (leftFib-getOb isLeftFibD g (leftFib-getOb isLeftFibD f X) , leftFib-getHom isLeftFibD f X ⋆⟨ D ⟩ᴰ leftFib-getHom isLeftFibD g (leftFib-getOb isLeftFibD f X))

  module _ (D : dispCat C ℓD ℓD')  where

    isCocartesian : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → D [ f , X , Y ]ᴰ → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
    isCocartesian {x} {y} f X Y F = {z : ob C} → {g : C [ y , z ]} → {h : C [ x , z ]} → (p : f ⋆⟨ C ⟩ g ≡ h) → {Z : D ⦅ z ⦆} → (H : D [ h , X , Z ]ᴰ) →
                                             ∃![ G ∈ D [ g , Y , Z ]ᴰ ] PathP (λ i →  D [ p i , X , Z ]ᴰ) (F ⋆⟨ D ⟩ᴰ G) H
                                           
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


record dispPreorder (C : Category ℓC ℓC') (ℓD ℓD' : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))) where
  field
    disp-cat : dispCat C ℓD ℓD'
    is-disp-preorder : isDispPreorder disp-cat



