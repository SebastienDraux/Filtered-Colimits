module Filtered-Colimits.DisplayedCategories.IsoDispCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open dispCat

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  record dispCatIso {x : ob C} (X Y : D ⦅ x ⦆) : Type ℓD' where
    field
      dC-mor : D [ id C , X , Y ]ᴰ
      dC-inv : D [ id C , Y , X ]ᴰ
      dC-sec : subst (λ f → D [ f , Y , Y ]ᴰ) (⋆IdL C (id C)) (dC-inv ⋆⟨ D ⟩ᴰ dC-mor) ≡ dC-id D
      dC-ret : subst (λ f → D [ f , X , X ]ᴰ) (⋆IdR C (id C)) (dC-mor ⋆⟨ D ⟩ᴰ dC-inv) ≡ dC-id D

    --record dispCatIso' {x y : ob C} (f : CatIso C x y) (X : D ⦅ x ⦆) (Y : D ⦅ y ⦆) : Type ℓD' where  --iso over iso
    --  field
    --    dC-mor : D [ mor f , X , Y ]ᴰ
     --   dC-inv : D [ inv f , Y , X ]ᴰ
     --   dC-sec : subst (λ f → D [ f , Y , Y ]ᴰ) (sec f) (dC-inv ⋆⟨ D ⟩ᴰ dC-mor) ≡ dC-id D
     --   dC-ret : subst (λ f → D [ f , X , X ]ᴰ) (ret f) (dC-mor ⋆⟨ D ⟩ᴰ dC-inv) ≡ dC-id D
        
  open dispCatIso

  makeDispCatIsoPath : {x : ob C} → {X Y : D ⦅ x ⦆} → (F G : dispCatIso X Y) → dC-mor F ≡ dC-mor G → F ≡ G
  makeDispCatIsoPath F G p = F≡G
    where
    q : dC-inv F ≡ dC-inv G
    q = 
       dC-inv F
         ≡⟨ sym (dC-⋆IdR D (dC-inv F)) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ dC-id D)
         ≡⟨ cong (λ G → subst (λ f → dC-hom D f _ _) (⋆IdR C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ G)) (sym (dC-ret G)) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G))
         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) F) (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ id C ⋆⟨ C ⟩ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (λ G → dC-inv F ⋆⟨ D ⟩ᴰ G) _) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → id C ⋆⟨ C ⟩ f) (⋆IdR C (id C))) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G)))
         ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → id C ⋆⟨ C ⟩ f) (⋆IdR C (id C)) ∙ ⋆IdR C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G))
         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → id C ⋆⟨ C ⟩ f) (⋆IdR C (id C)) ∙ ⋆IdR C (id C)) F) (sym (dC-⋆Assoc D _ _ _)) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → id C ⋆⟨ C ⟩ f) (⋆IdR C (id C)) ∙ ⋆IdR C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G))
         ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _ ∙ cong (λ f → id C ⋆⟨ C ⟩ f) (⋆IdR C (id C)) ∙ ⋆IdR C (id C)) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
         ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)) (isSetHom C _ _ _ _) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ id C) (⋆IdL C (id C)) ∙ ⋆IdL C (id C)) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
         ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ id C) (⋆IdL C (id C))) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G))
         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) F) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ f ⋆⟨ C ⟩ id C , _ , _ ]ᴰ) (⋆IdL C (id C)) (λ F → F ⋆⟨ D ⟩ᴰ dC-inv G) _)) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
         ≡⟨ cong (λ H → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ H) ⋆⟨ D ⟩ᴰ dC-inv G)) (sym p) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ dC-inv G)
         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (F ⋆⟨ D ⟩ᴰ dC-inv G)) (dC-sec F) ⟩
       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (dC-id D ⋆⟨ D ⟩ᴰ dC-inv G)
         ≡⟨ dC-⋆IdL D (dC-inv G) ⟩
       dC-inv G ∎

    F≡G : F ≡ G
    F≡G i .dC-mor = p i
    F≡G i .dC-inv = q i
    F≡G i .dC-sec = isProp→PathP {B = λ i → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (q i ⋆⟨ D ⟩ᴰ p i) ≡ dC-id D} (λ i → dC-homSet D _ _ _ _ _) (dC-sec F) (dC-sec G) i
    F≡G i .dC-ret = isProp→PathP {B = λ i → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (p i ⋆⟨ D ⟩ᴰ q i) ≡ dC-id D} (λ i → dC-homSet D _ _ _ _ _) (dC-ret F) (dC-ret G) i

  isSetDispCatIso : {x : ob C} → (X Y : D ⦅ x ⦆) → isSet (dispCatIso X Y)
  isSetDispCatIso X Y f g p q i j .dC-mor = isSet→SquareP {A = λ _ _ → D [ id C , _ , _ ]ᴰ} (λ _ _ → dC-homSet D _ _ _) (λ j → dC-mor (p j)) (λ j → dC-mor (q j)) refl refl i j
  isSetDispCatIso X Y f g p q i j .dC-inv = isSet→SquareP {A = λ _ _ → D [ id C , _ , _ ]ᴰ} (λ _ _ → dC-homSet D _ _ _) (λ j → dC-inv (p j)) (λ j → dC-inv (q j)) refl refl i j
  isSetDispCatIso X Y f g p q i j .dC-sec =
    isSet→SquareP {A = λ i j → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C (id C)) (isSetDispCatIso X Y f g p q i j .dC-inv ⋆⟨ D ⟩ᴰ isSetDispCatIso X Y f g p q i j .dC-mor) ≡ dC-id D}
    (λ i j → isProp→isSet (dC-homSet D _ _ _ _ _)) (λ j → dC-sec (p j)) (λ j → dC-sec (q j)) refl refl i j
  isSetDispCatIso X Y f g p q i j .dC-ret = 
    isSet→SquareP {A = λ i j → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (id C)) (isSetDispCatIso X Y f g p q i j .dC-mor ⋆⟨ D ⟩ᴰ isSetDispCatIso X Y f g p q i j .dC-inv) ≡ dC-id D}
    (λ i j → isProp→isSet (dC-homSet D _ _ _ _ _)) (λ j → dC-ret (p j)) (λ j → dC-ret (q j)) refl refl i j


  idDispCatIso : {x : ob C} → {X : D ⦅ x ⦆} → dispCatIso X X
  idDispCatIso .dC-mor = dC-id D
  idDispCatIso .dC-inv = dC-id D
  idDispCatIso .dC-sec = dC-⋆IdL D (dC-id D)
  idDispCatIso .dC-ret = dC-⋆IdR D (dC-id D)

  dC-pathToIso : {x : ob C} → {X X' : D ⦅ x ⦆} → X ≡ X' → dispCatIso X X'
  dC-pathToIso {X = X} p = J (λ X' p → dispCatIso X X') idDispCatIso p

  dC-pathToIsoRefl : {x : ob C} → {X : D ⦅ x ⦆} → dC-pathToIso refl ≡ idDispCatIso {X = X}
  dC-pathToIsoRefl {X = X} = JRefl (λ X' p → dispCatIso X X') idDispCatIso
  

  isUnivalent-dC : Type (ℓ-max (ℓ-max ℓC ℓD) ℓD')
  isUnivalent-dC = {x : ob C} → (X X' : D ⦅ x ⦆) → isEquiv (dC-pathToIso {x = x} {X = X} {X' = X'})
    
  dC-univEquiv : {x : ob C} → isUnivalent-dC → (X X' : D ⦅ x ⦆) → (X ≡ X') ≃ (dispCatIso X X')
  dC-univEquiv isUnivD X X' = dC-pathToIso , isUnivD X X'


  isProp-isUnivalent-dC : isProp isUnivalent-dC
  isProp-isUnivalent-dC isUnivD isUnivD' = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsEquiv _)) isUnivD isUnivD'


  dC-morP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → D [ id C , X , Y ]ᴰ
  dC-morP p = dC-mor (dC-pathToIso p)

  dC-invP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → D [ id C , Y , X ]ᴰ
  dC-invP p = dC-inv (dC-pathToIso p)

  dC-secMorP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → subst (λ f → D [ f , Y , Y ]ᴰ) (⋆IdL C (id C)) (dC-invP p ⋆⟨ D ⟩ᴰ dC-morP p) ≡ dC-id D
  dC-secMorP p = dC-sec (dC-pathToIso p)

  dC-retMorP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → subst (λ f → D [ f , X , X ]ᴰ) (⋆IdR C (id C)) (dC-morP p ⋆⟨ D ⟩ᴰ dC-invP p) ≡ dC-id D
  dC-retMorP p = dC-ret (dC-pathToIso p)

  dC-reflMorP : {x : ob C} → {X : D ⦅ x ⦆} → dC-morP refl ≡ dC-id D {X = X}
  dC-reflMorP = cong dC-mor dC-pathToIsoRefl

  dC-reflInvP : {x : ob C} → {X : D ⦅ x ⦆} → dC-invP refl ≡ dC-id D {X = X}
  dC-reflInvP = cong dC-inv dC-pathToIsoRefl

  dC-substHomL : {x y : ob C} → {f : C [ x , y ]} → {X X' : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (p : X ≡ X') → (F : D [ f , X , Y ]ᴰ) →
                 subst (λ X → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X' , Y ]ᴰ) (⋆IdL C f) (dC-invP p ⋆⟨ D ⟩ᴰ F)
  dC-substHomL {f = f} {X} {X'} {Y} p F = J (λ X' p → subst (λ X → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X' , Y ]ᴰ) (⋆IdL C f) (dC-invP p ⋆⟨ D ⟩ᴰ F)) eqRefl p
    where
    eqRefl : subst (λ X → D [ f , X , Y ]ᴰ) refl F ≡ subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (dC-invP refl ⋆⟨ D ⟩ᴰ F)
    eqRefl = 
      subst (λ X → D [ f , X , Y ]ᴰ) refl F                               ≡⟨ substRefl {B = λ X → D [ f , X , Y ]ᴰ} F ⟩
      F                                                                    ≡⟨ sym (dC-⋆IdL D F) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (dC-id D ⋆⟨ D ⟩ᴰ F)        ≡⟨ cong (λ G → subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (G ⋆⟨ D ⟩ᴰ F)) (sym dC-reflInvP) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (dC-invP refl ⋆⟨ D ⟩ᴰ F)   ∎

  dC-substHomR : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y Y' : D ⦅ y ⦆} → (p : Y ≡ Y') → (F : D [ f , X , Y ]ᴰ) →
                 subst (λ Y → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X , Y' ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP p)
  dC-substHomR {f = f} {X} {Y} {Y'} p F = J (λ Y' p → subst (λ Y → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X , Y' ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP p)) eqRefl p
    where
    eqRefl : subst (λ Y → D [ f , X , Y ]ᴰ) refl F ≡ subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP refl)
    eqRefl = 
      subst (λ Y → D [ f , X , Y ]ᴰ) refl F                               ≡⟨ substRefl {B = λ Y → D [ f , X , Y ]ᴰ} F ⟩
      F                                                                    ≡⟨ sym (dC-⋆IdR D F) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-id D)        ≡⟨ cong (λ G → subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ G)) (sym dC-reflMorP) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP refl)   ∎

  dC-substHomLR : {x y : ob C} → {f : C [ x , y ]} → {X X' : D ⦅ x ⦆} → {Y Y' : D ⦅ y ⦆} → (p : X ≡ X') → (q : Y ≡ Y') → (F : D [ f , X , Y ]ᴰ) →
                 subst2 (λ X Y → D [ f , X , Y ]ᴰ) p q F ≡ subst ((λ f → D [ f , X' , Y' ]ᴰ)) (⋆IdR C f) (subst (λ f → D [ f , X' , Y ]ᴰ) (⋆IdL C f) (dC-invP p ⋆⟨ D ⟩ᴰ F) ⋆⟨ D ⟩ᴰ dC-morP q)
  dC-substHomLR {f = f} {X} {X'} {Y} {Y'} p q F = 
    subst2 (λ X Y → D [ f , X , Y ]ᴰ) p q F
        ≡⟨ sym (subst-subst≡subst2 (λ X Y → D [ f , X , Y ]ᴰ) p q F) ⟩
    subst (λ Y → D [ f , X' , Y ]ᴰ) q (subst (λ X → D [ f , X , Y ]ᴰ) p F)
        ≡⟨ dC-substHomR q (subst (λ X → D [ f , X , Y ]ᴰ) p F) ⟩
    subst ((λ f → D [ f , X' , Y' ]ᴰ)) (⋆IdR C f) (subst (λ X → D [ f , X , Y ]ᴰ) p F ⋆⟨ D ⟩ᴰ dC-morP q)
        ≡⟨ cong (λ F → subst ((λ f → D [ f , X' , Y' ]ᴰ)) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP q)) (dC-substHomL p F) ⟩
    subst ((λ f → D [ f , X' , Y' ]ᴰ)) (⋆IdR C f) (subst (λ f → D [ f , X' , Y ]ᴰ) (⋆IdL C f) (dC-invP p ⋆⟨ D ⟩ᴰ F) ⋆⟨ D ⟩ᴰ dC-morP q) ∎


  dC-symMorP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → dC-morP (sym p) ≡ dC-invP p
  dC-symMorP {X = X} {Y} p = J (λ Y p → dC-morP (sym p) ≡ dC-invP p) (dC-reflMorP ∙ sym dC-reflInvP) p
