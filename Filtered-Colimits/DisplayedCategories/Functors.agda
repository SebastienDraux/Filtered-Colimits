module Filtered-Colimits.DisplayedCategories.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat
open import Filtered-Colimits.DisplayedCategories.CocartesianMorphisms

private
  variable
    ℓC ℓC' ℓD ℓD' ℓD₁ ℓD₁' ℓD₂ ℓD₂' ℓE ℓE' : Level

open Iso
open Category
open dispCat
open dispCatIso

module _ {C : Category ℓC ℓC'} where

  record dispCat-Funct (D : dispCat C ℓD ℓD') (E : dispCat C ℓE ℓE') : Type (ℓ-max (ℓ-max ℓC (ℓ-max ℓD ℓE)) (ℓ-max ℓC' (ℓ-max ℓD' ℓE'))) where
    field
      dF-ob : {x : ob C} → D ⦅ x ⦆ → E ⦅ x ⦆
      dF-hom : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → D [ f , X , Y ]ᴰ → E [ f , (dF-ob X) , (dF-ob Y) ]ᴰ
      dF-id : {x : ob C} → {X : D ⦅ x ⦆} → dF-hom (dC-id D {X = X}) ≡ dC-id E
      dF-seq : {x y z : ob C} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → {Z : D ⦅ z ⦆} → {f : C [ x , y ]} → {g : C [ y , z ]} → (F : D [ f , X , Y ]ᴰ) → (G : D [ g , Y , Z ]ᴰ) →
                  dF-hom (F ⋆⟨ D ⟩ᴰ G) ≡ (dF-hom F) ⋆⟨ E ⟩ᴰ (dF-hom G)

  open dispCat-Funct

  module _ {D : dispCat C ℓD ℓD'}
           {E : dispCat C ℓE ℓE'} where

    infix 30 _⟅_⟆ᴰ
    _⟅_⟆ᴰ : dispCat-Funct D E → {x : ob C} → D ⦅ x ⦆ → E ⦅ x ⦆
    𝑭 ⟅ X ⟆ᴰ = dF-ob 𝑭 X

    infix 30 _⟪_⟫ᴰ
    _⟪_⟫ᴰ : (𝑭 : dispCat-Funct D E) → {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → D [ f , X , Y ]ᴰ → E [ f , 𝑭 ⟅ X ⟆ᴰ ,  𝑭 ⟅ Y ⟆ᴰ ]ᴰ
    𝑭 ⟪ F ⟫ᴰ = dF-hom 𝑭 F

open dispCat-Funct

module _ {C : Category ℓC ℓC'} where

  _⋆ᵈᶠ_ : {D₀ : dispCat C ℓD ℓD'} {D₁ : dispCat C ℓD₁ ℓD₁'} {D₂ : dispCat C ℓD₂ ℓD₂'} → dispCat-Funct D₀ D₁ →  dispCat-Funct D₁ D₂ →  dispCat-Funct D₀ D₂
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-ob X = 𝑮 ⟅ 𝑭 ⟅ X ⟆ᴰ ⟆ᴰ
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-hom F = 𝑮 ⟪ 𝑭 ⟪ F ⟫ᴰ ⟫ᴰ
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-id = cong (𝑮 ⟪_⟫ᴰ) (dF-id 𝑭) ∙ dF-id 𝑮
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-seq F G = cong (𝑮 ⟪_⟫ᴰ) (dF-seq 𝑭 F G) ∙ dF-seq 𝑮 (𝑭 ⟪ F ⟫ᴰ) (𝑭 ⟪ G ⟫ᴰ)

  dF-Assoc : {D₀ : dispCat C ℓD ℓD'} {D₁ : dispCat C ℓD₁ ℓD₁'} {D₂ : dispCat C ℓD₂ ℓD₂'} {E : dispCat C ℓE ℓE'} →
             (𝑭 : dispCat-Funct D₀ D₁) → (𝑮 : dispCat-Funct D₁ D₂) → (𝑯 : dispCat-Funct D₂ E) → (𝑭 ⋆ᵈᶠ 𝑮) ⋆ᵈᶠ 𝑯 ≡ 𝑭 ⋆ᵈᶠ (𝑮 ⋆ᵈᶠ 𝑯)
  dF-Assoc 𝑭 𝑮 𝑯 i .dF-ob X = 𝑯 ⟅ 𝑮 ⟅ 𝑭 ⟅ X ⟆ᴰ ⟆ᴰ ⟆ᴰ
  dF-Assoc 𝑭 𝑮 𝑯 i .dF-hom F = 𝑯 ⟪ 𝑮 ⟪ 𝑭 ⟪ F ⟫ᴰ ⟫ᴰ ⟫ᴰ
  dF-Assoc 𝑭 𝑮 𝑯 i .dF-id = congAssoc (𝑮 ⟪_⟫ᴰ) (𝑯 ⟪_⟫ᴰ) (dF-id 𝑭) (dF-id 𝑮) (dF-id 𝑯) (~ i)
  dF-Assoc 𝑭 𝑮 𝑯 i .dF-seq F G = congAssoc (𝑮 ⟪_⟫ᴰ) (𝑯 ⟪_⟫ᴰ) (dF-seq 𝑭 _ _) (dF-seq 𝑮 _ _) (dF-seq 𝑯 _ _) (~ i)

module _ {C : Category ℓC ℓC'}
         {D : dispCat C ℓD ℓD'} where

  dC-idFunct : dispCat-Funct D D
  dC-idFunct .dF-ob X = X
  dC-idFunct .dF-hom F = F
  dC-idFunct .dF-id = refl
  dC-idFunct .dF-seq F G = refl

module _ {C : Category ℓC ℓC'}
         {D : dispCat C ℓD ℓD'}
         {E : dispCat C ℓE ℓE'}
         (𝑭 : dispCat-Funct D E) where

  dF-lUnit : dC-idFunct ⋆ᵈᶠ 𝑭 ≡ 𝑭
  dF-lUnit i .dF-ob X = 𝑭 ⟅ X ⟆ᴰ
  dF-lUnit i .dF-hom F = 𝑭 ⟪ F ⟫ᴰ
  dF-lUnit i .dF-id = lUnit (dF-id 𝑭) (~ i)
  dF-lUnit i .dF-seq F G =  lUnit (dF-seq 𝑭 _ _) (~ i)

  dF-rUnit : 𝑭 ⋆ᵈᶠ dC-idFunct ≡ 𝑭
  dF-rUnit i .dF-ob X = 𝑭 ⟅ X ⟆ᴰ
  dF-rUnit i .dF-hom F = 𝑭 ⟪ F ⟫ᴰ
  dF-rUnit i .dF-id = rUnit (dF-id 𝑭) (~ i)
  dF-rUnit i .dF-seq F G =  rUnit (dF-seq 𝑭 _ _) (~ i)

  preservPathToIso : {x : ob C} {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → 𝑭 ⟪ dC-mor (dC-pathToIso D p) ⟫ᴰ ≡ dC-mor (dC-pathToIso E (cong (𝑭 ⟅_⟆ᴰ) p))
  preservPathToIso p = J (λ Y p → 𝑭 ⟪ dC-mor (dC-pathToIso D p) ⟫ᴰ ≡ dC-mor (dC-pathToIso E (cong (𝑭 ⟅_⟆ᴰ) p)))
                         (cong (λ F → 𝑭 ⟪ dC-mor F ⟫ᴰ) (dC-pathToIsoRefl D) ∙ dF-id 𝑭 ∙ sym (cong dC-mor (dC-pathToIsoRefl E))) p

module _ {C : Category ℓC ℓC'}
         {D : dispCat C ℓD ℓD'}
         {E : dispCat C ℓE ℓE'} where

  preservesCocartMor : dispCat-Funct D E → Type (ℓ-max (ℓ-max ℓC (ℓ-max ℓD ℓE)) (ℓ-max ℓC' (ℓ-max ℓD' ℓE')))
  preservesCocartMor 𝑭 = {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F : D [ f , X , Y ]ᴰ) → isCocartesian D f X Y F → isCocartesian E f (𝑭 ⟅ X ⟆ᴰ) (𝑭 ⟅ Y ⟆ᴰ) (𝑭 ⟪ F ⟫ᴰ)
  isProp-preservesCocartMor : (𝑭 : dispCat-Funct D E) → isProp (preservesCocartMor 𝑭)
  isProp-preservesCocartMor 𝑭 = isPropImplicitΠ2 (λ _ _ → isPropImplicitΠ (λ _ →  isPropImplicitΠ2 (λ _ _ → isPropΠ2 (λ F _ → isProp-isCocartesian E (𝑭 ⟪ F ⟫ᴰ)))))

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  preservesCocartMor-id : preservesCocartMor (dC-idFunct {D = D})
  preservesCocartMor-id 𝑭 isCocartF = isCocartF

module _ {C : Category ℓC ℓC'}
         {D₀ : dispCat C ℓD ℓD'}
         {D₁ : dispCat C ℓD₁ ℓD₁'}
         {D₂ : dispCat C ℓD₂ ℓD₂'}where
   
  preservesCocartMor-seq : (𝑭 :  dispCat-Funct D₀ D₁) → (𝑮 :  dispCat-Funct D₁ D₂) → preservesCocartMor 𝑭 → preservesCocartMor 𝑮 → preservesCocartMor (𝑭 ⋆ᵈᶠ 𝑮)
  preservesCocartMor-seq 𝑭 𝑮 preservCocartF preservCocartG F isCocartF = preservCocartG (𝑭 ⟪ F ⟫ᴰ) (preservCocartF F isCocartF)
    
  

module _ {C : Category ℓC ℓC'}
         {D : dispCat C ℓD ℓD'}
         {E : dispCat C ℓE ℓE'} where

  record eq-dF (𝑭 𝑮 : dispCat-Funct D E) : Type (ℓ-max (ℓ-max ℓC (ℓ-max ℓD ℓE)) (ℓ-max ℓC' (ℓ-max ℓD' ℓE'))) where
    field
      eq-dF-ob : {x : ob C} → (X : D ⦅ x ⦆) → 𝑭 ⟅ X ⟆ᴰ ≡ 𝑮 ⟅ X ⟆ᴰ
      eq-dF-hom :  {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F : D [ f , X , Y ]ᴰ) →
                   PathP (λ i → E [ f , eq-dF-ob X i , eq-dF-ob Y i ]ᴰ) (𝑭 ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)

  open eq-dF

  module _ {𝑭 𝑮 : dispCat-Funct D E} where

    eq-dF→≡ : eq-dF 𝑭 𝑮 → 𝑭 ≡ 𝑮
    eq-dF→≡ eqFG i .dF-ob X = eq-dF-ob eqFG X i
    eq-dF→≡ eqFG i .dF-hom F = eq-dF-hom eqFG F i
    eq-dF→≡ eqFG i .dF-id {X = X} j = isSet→SquareP {A = λ i j → E [ id C , eq-dF-ob eqFG X i , eq-dF-ob eqFG X i ]ᴰ} (λ i j → dC-homSet E _ _ _)
                                                      (dF-id 𝑭) (dF-id 𝑮) (eq-dF-hom eqFG (dC-id D)) (λ i → dC-id E) i j
    eq-dF→≡ eqFG i .dF-seq {X = X} {Z = Z} {f} {g} F G j = isSet→SquareP {A = λ i j → E [ f ⋆⟨ C ⟩ g , eq-dF-ob eqFG X i , eq-dF-ob eqFG Z i ]ᴰ} (λ i j → dC-homSet E _ _ _)
                                                            (dF-seq 𝑭 F G) (dF-seq 𝑮 F G) (eq-dF-hom eqFG (F ⋆⟨ D ⟩ᴰ G)) (λ i → eq-dF-hom eqFG F i ⋆⟨ E ⟩ᴰ eq-dF-hom eqFG G i) i j


    ≡→eq-dF : 𝑭 ≡ 𝑮 → eq-dF 𝑭 𝑮
    ≡→eq-dF p .eq-dF-ob X = cong (_⟅ X ⟆ᴰ) p
    ≡→eq-dF p .eq-dF-hom {X = X} {Y} F = cong (_⟪ F ⟫ᴰ) p
   
    Iso-≡-eq-dF : Iso (𝑭 ≡ 𝑮) (eq-dF 𝑭 𝑮)
    Iso-≡-eq-dF .fun = ≡→eq-dF
    Iso-≡-eq-dF .inv = eq-dF→≡
    Iso-≡-eq-dF .leftInv p i j .dF-ob = dF-ob (p j)
    Iso-≡-eq-dF .leftInv p i j .dF-hom = dF-hom (p j)
    Iso-≡-eq-dF .leftInv p i j .dF-id = isSet→SquareP {A = λ i j → dF-hom (p j) (dC-id D) ≡ dC-id E} (λ i j → isProp→isSet (dC-homSet E _ _ _ _ _))
                                                 (λ j → dF-id (eq-dF→≡ (≡→eq-dF p) j)) (λ j → dF-id (p j)) refl refl i j
    Iso-≡-eq-dF .leftInv p i j .dF-seq F G = isSet→SquareP {A = λ i j → dF-hom (p j) (F ⋆⟨ D ⟩ᴰ G) ≡ dF-hom (p j) F ⋆⟨ E ⟩ᴰ dF-hom (p j) G} (λ i j → isProp→isSet (dC-homSet E _ _ _ _ _))
                                                            (λ j → dF-seq (eq-dF→≡ (≡→eq-dF p) j) F G) (λ j → dF-seq (p j) F G) refl refl i j
    Iso-≡-eq-dF .rightInv eq = refl

    ≡≃eq-dF : (𝑭 ≡ 𝑮) ≃ (eq-dF 𝑭 𝑮)
    ≡≃eq-dF = isoToEquiv Iso-≡-eq-dF

    ≡-≡-dF : (p q : 𝑭 ≡ 𝑮) → ({x : ob C} → (X : D ⦅ x ⦆) → cong (_⟅ X ⟆ᴰ) p ≡ cong (_⟅ X ⟆ᴰ) q) → p ≡ q
    ≡-≡-dF p q p-ob≡q-ob = isoFunInjective Iso-≡-eq-dF p q ≡eq-dF
      where
      ≡eq-dF : ≡→eq-dF p ≡ ≡→eq-dF q
      ≡eq-dF i .eq-dF-ob X = p-ob≡q-ob X i
      ≡eq-dF i .eq-dF-hom F = isProp→PathP {B = λ i → PathP (λ j → E [ _ , p-ob≡q-ob _ i j , p-ob≡q-ob _ i j ]ᴰ) (𝑭 ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)}
                                            (λ i → isSet→isPropPathP (λ j → E [ _ , p-ob≡q-ob _ i j , p-ob≡q-ob _ i j ]ᴰ) (λ j → dC-homSet E _ _ _) (𝑭 ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ))
                                            (cong (_⟪ F ⟫ᴰ) p) (cong (_⟪ F ⟫ᴰ) q) i
