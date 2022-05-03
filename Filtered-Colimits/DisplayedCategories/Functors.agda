module Filtered-Colimits.DisplayedCategories.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open dispCat

module _ {C : Category ℓC ℓC'} where

  record dispCat-Funct (D D' : dispCat C ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      dF-ob : {x : ob C} → D ⦅ x ⦆ → D' ⦅ x ⦆
      dF-hom : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → D [ f , X , Y ]ᴰ → D' [ f , (dF-ob X) , (dF-ob Y) ]ᴰ
      dF-id : {x : ob C} → {X : D ⦅ x ⦆} → dF-hom (dC-id D {X = X}) ≡ dC-id D'
      dF-seq : {x y z : ob C} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → {Z : D ⦅ z ⦆} → {f : C [ x , y ]} → {g : C [ y , z ]} → (F : D [ f , X , Y ]ᴰ) → (G : D [ g , Y , Z ]ᴰ) →
                  dF-hom (F ⋆⟨ D ⟩ᴰ G) ≡ (dF-hom F) ⋆⟨ D' ⟩ᴰ (dF-hom G)

  open dispCat-Funct

  module _ {D D' : dispCat C ℓD ℓD'} where

    infix 30 _⟅_⟆ᴰ
    _⟅_⟆ᴰ : dispCat-Funct D D' → {x : ob C} → D ⦅ x ⦆ → D' ⦅ x ⦆
    𝑭 ⟅ X ⟆ᴰ = dF-ob 𝑭 X

    infix 30 _⟪_⟫ᴰ
    _⟪_⟫ᴰ : (𝑭 : dispCat-Funct D D') → {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → D [ f , X , Y ]ᴰ → D' [ f , 𝑭 ⟅ X ⟆ᴰ ,  𝑭 ⟅ Y ⟆ᴰ ]ᴰ
    𝑭 ⟪ F ⟫ᴰ = dF-hom 𝑭 F

open dispCat-Funct

module _ {C : Category ℓC ℓC'} where

  _⋆ᵈᶠ_ : {D D' D'' : dispCat C ℓD ℓD'} → dispCat-Funct D D' →  dispCat-Funct D' D'' →  dispCat-Funct D D''
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-ob X = 𝑮 ⟅ 𝑭 ⟅ X ⟆ᴰ ⟆ᴰ
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-hom F = 𝑮 ⟪ 𝑭 ⟪ F ⟫ᴰ ⟫ᴰ
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-id = cong (𝑮 ⟪_⟫ᴰ) (dF-id 𝑭) ∙ dF-id 𝑮
  _⋆ᵈᶠ_ 𝑭 𝑮 .dF-seq F G = cong (𝑮 ⟪_⟫ᴰ) (dF-seq 𝑭 F G) ∙ dF-seq 𝑮 (𝑭 ⟪ F ⟫ᴰ) (𝑭 ⟪ G ⟫ᴰ)

  dF-Assoc : {D D' D''  D''' : dispCat C ℓD ℓD'} → (𝑭 : dispCat-Funct D D') → (𝑮 : dispCat-Funct D' D'') → (𝑯 : dispCat-Funct D'' D''') → (𝑭 ⋆ᵈᶠ 𝑮) ⋆ᵈᶠ 𝑯 ≡ 𝑭 ⋆ᵈᶠ (𝑮 ⋆ᵈᶠ 𝑯)
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
         {D D' : dispCat C ℓD ℓD'} where

  dF-lUnit : (𝑭 : dispCat-Funct D D') → dC-idFunct ⋆ᵈᶠ 𝑭 ≡ 𝑭
  dF-lUnit 𝑭 i .dF-ob X = 𝑭 ⟅ X ⟆ᴰ
  dF-lUnit 𝑭 i .dF-hom F = 𝑭 ⟪ F ⟫ᴰ
  dF-lUnit 𝑭 i .dF-id = lUnit (dF-id 𝑭) (~ i)
  dF-lUnit 𝑭 i .dF-seq F G =  lUnit (dF-seq 𝑭 _ _) (~ i)

  dF-rUnit : (𝑭 : dispCat-Funct D D') → 𝑭 ⋆ᵈᶠ dC-idFunct ≡ 𝑭
  dF-rUnit 𝑭 i .dF-ob X = 𝑭 ⟅ X ⟆ᴰ
  dF-rUnit 𝑭 i .dF-hom F = 𝑭 ⟪ F ⟫ᴰ
  dF-rUnit 𝑭 i .dF-id = rUnit (dF-id 𝑭) (~ i)
  dF-rUnit 𝑭 i .dF-seq F G =  rUnit (dF-seq 𝑭 _ _) (~ i)


module _ {C : Category ℓC ℓC'}
         {D D' : dispCat C ℓD ℓD'} where

  record eq-dF (𝑭 𝑮 : dispCat-Funct D D') : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      eq-dF-ob : {x : ob C} → (X : D ⦅ x ⦆) → 𝑭 ⟅ X ⟆ᴰ ≡ 𝑮 ⟅ X ⟆ᴰ
      eq-dF-hom :  {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F : D [ f , X , Y ]ᴰ) →
          subst ((λ f → D' [ f , 𝑮 ⟅ X ⟆ᴰ , 𝑮 ⟅ Y ⟆ᴰ ]ᴰ)) (⋆IdR C f) (subst (λ f → D' [ f , 𝑮 ⟅ X ⟆ᴰ , 𝑭 ⟅ Y ⟆ᴰ ]ᴰ) (⋆IdL C f) (dC-invP D' (eq-dF-ob X) ⋆⟨ D' ⟩ᴰ 𝑭 ⟪ F ⟫ᴰ) ⋆⟨ D' ⟩ᴰ dC-morP D' (eq-dF-ob Y)) ≡ 𝑮 ⟪ F ⟫ᴰ

  open eq-dF

  ≡eq-dF : {𝑭 𝑮 : dispCat-Funct D D'} → (eqFG eqFG' : eq-dF 𝑭 𝑮) → ({x : ob C} → (X : D ⦅ x ⦆) → eq-dF-ob eqFG X ≡ eq-dF-ob eqFG' X) → eqFG ≡ eqFG'
  ≡eq-dF {𝑭} {𝑮} eqFG eqFG' ≡eq-dF-ob i .eq-dF-ob X = ≡eq-dF-ob X i
  ≡eq-dF {𝑭} {𝑮} eqFG eqFG' ≡eq-dF-ob i .eq-dF-hom {f = f} {X} {Y} F = isProp→PathP
         {B = λ i → subst ((λ f → D' [ f , 𝑮 ⟅ X ⟆ᴰ , 𝑮 ⟅ Y ⟆ᴰ ]ᴰ)) (⋆IdR C f) (subst (λ f → D' [ f , 𝑮 ⟅ X ⟆ᴰ , 𝑭 ⟅ Y ⟆ᴰ ]ᴰ) (⋆IdL C f) (dC-invP D' (≡eq-dF-ob X i) ⋆⟨ D' ⟩ᴰ 𝑭 ⟪ F ⟫ᴰ) ⋆⟨ D' ⟩ᴰ dC-morP D' (≡eq-dF-ob Y i)) ≡ 𝑮 ⟪ F ⟫ᴰ}
         (λ i → dC-homSet D' f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ Y ⟆ᴰ) _ _) (eq-dF-hom eqFG F) (eq-dF-hom eqFG' F) i

  eq-dF→≡ : {𝑭 𝑮 : dispCat-Funct D D'} → eq-dF 𝑭 𝑮 → 𝑭 ≡ 𝑮
  eq-dF→≡ {𝑭} {𝑮} eqFG = 𝑭≡𝑮
    where
    𝑭hom≡𝑮hom : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F : D [ f , X , Y ]ᴰ) → PathP (λ i → D' [ f , eq-dF-ob eqFG X i , eq-dF-ob eqFG Y i ]ᴰ) (𝑭 ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)
    𝑭hom≡𝑮hom {f = f} {X} {Y} F = toPathP {A = λ i →  D' [ f , eq-dF-ob eqFG X i , eq-dF-ob eqFG Y i ]ᴰ} ((dC-substHomLR D' (eq-dF-ob eqFG X) (eq-dF-ob eqFG Y) (𝑭 ⟪ F ⟫ᴰ)) ∙ eq-dF-hom eqFG F)
    
    𝑭≡𝑮 : 𝑭 ≡ 𝑮
    𝑭≡𝑮 i .dF-ob X = eq-dF-ob eqFG X i
    𝑭≡𝑮 i .dF-hom F = 𝑭hom≡𝑮hom F i
    𝑭≡𝑮 i .dF-id {X = X} = isProp→PathP {B = λ i → 𝑭hom≡𝑮hom (dC-id D {X = X}) i ≡ dC-id D'} (λ i → dC-homSet D' _ _ _ _ _) (dF-id 𝑭) (dF-id 𝑮) i
    𝑭≡𝑮 i .dF-seq F G = isProp→PathP {B = λ i → 𝑭hom≡𝑮hom (F ⋆⟨ D ⟩ᴰ G) i ≡ 𝑭hom≡𝑮hom F i ⋆⟨ D' ⟩ᴰ 𝑭hom≡𝑮hom G i} (λ i → dC-homSet D' _ _ _ _ _) (dF-seq 𝑭 F G) (dF-seq 𝑮 F G) i

  ≡→eq-dF : {𝑭 𝑮 : dispCat-Funct D D'} → 𝑭 ≡ 𝑮 → eq-dF 𝑭 𝑮
  ≡→eq-dF p .eq-dF-ob X = cong (_⟅ X ⟆ᴰ) p
  ≡→eq-dF {𝑭} p .eq-dF-hom {X = X} {Y} F = sym (dC-substHomLR D' (cong (_⟅ X ⟆ᴰ) p) (cong (_⟅ Y ⟆ᴰ) p) (𝑭 ⟪ F ⟫ᴰ)) ∙ fromPathP (λ i → (p i) ⟪ F ⟫ᴰ)

  ≡→eq-dF→≡ : {𝑭 𝑮 : dispCat-Funct D D'} → (p : 𝑭 ≡ 𝑮) → eq-dF→≡ (≡→eq-dF p) ≡ p
  ≡→eq-dF→≡ p i j .dF-ob X = (p j) ⟅ X ⟆ᴰ
  ≡→eq-dF→≡ {𝑭} {𝑮} p i j .dF-hom {f = f} {X} {Y} F =
    isSet→SquareP {A = λ i j → D' [ f , (p j) ⟅ X ⟆ᴰ , (p j) ⟅ Y ⟆ᴰ ]ᴰ}
    (λ i j → dC-homSet D' _ _ _) (λ j → dF-hom (eq-dF→≡ (≡→eq-dF p) j) F) (λ j → dF-hom (p j) F) refl refl i j
  ≡→eq-dF→≡ {𝑭} {𝑮} p i j .dF-id =
    isSet→SquareP {A = λ i j → ≡→eq-dF→≡ p i j .dF-hom (dC-id D) ≡ dC-id D'}
    (λ i j → isProp→isSet (dC-homSet D' _ _ _ _ _)) (λ j → dF-id (eq-dF→≡ (≡→eq-dF p) j)) (λ j → dF-id (p j)) refl refl i j
  ≡→eq-dF→≡ p i j .dF-seq F G =
    isSet→SquareP {A = λ i j → ≡→eq-dF→≡ p i j .dF-hom (F ⋆⟨ D ⟩ᴰ G) ≡ ≡→eq-dF→≡ p i j .dF-hom F ⋆⟨ D' ⟩ᴰ ≡→eq-dF→≡ p i j .dF-hom G}
    (λ i j → isProp→isSet (dC-homSet D' _ _ _ _ _)) (λ j → dF-seq (eq-dF→≡ (≡→eq-dF p) j) _ _) (λ j → dF-seq (p j) _ _) refl refl i j
