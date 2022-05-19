module Filtered-Colimits.DisplayedCategories.IsoDispCat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv ; iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories


private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category
open dispCat
open CatIso
open isIso

module _ {C : Category ℓC ℓC'}
         {x y : ob C}
         (D : dispCat C ℓD ℓD')  where
         
  module _ (X : D ⦅ x ⦆) (Y : D ⦅ y ⦆) where
  
    record dispCatIso (f : CatIso C x y) : Type ℓD' where
      field
        dC-mor : D [ mor f , X , Y ]ᴰ
        dC-inv : D [ inv f , Y , X ]ᴰ
        dC-sec : PathP (λ i → D [ sec f i , Y , Y ]ᴰ) (dC-inv ⋆⟨ D ⟩ᴰ dC-mor) (dC-id D)
        dC-ret : PathP (λ i → D [ ret f i , X , X ]ᴰ) (dC-mor ⋆⟨ D ⟩ᴰ dC-inv) (dC-id D)

    record dispCatIsIso {f : C [ x , y ]} (isIso-f : isIso C f) (F : D [ f , X , Y ]ᴰ) : Type ℓD' where
      field
        dC-inv : D [ inv isIso-f , Y , X ]ᴰ
        dC-sec : PathP (λ i → D [ sec isIso-f i , Y , Y ]ᴰ) (dC-inv ⋆⟨ D ⟩ᴰ F) (dC-id D)
        dC-ret : PathP (λ i → D [ ret isIso-f i , X , X ]ᴰ) (F ⋆⟨ D ⟩ᴰ dC-inv) (dC-id D)

    open dispCatIso
    open dispCatIsIso
  
    dispCatIso≃ΣdispCatIsIso : (f : CatIso C x y) → dispCatIso f ≃ Σ (D [ mor f , X , Y ]ᴰ) (dispCatIsIso (CatIso→isIso f))
    dispCatIso≃ΣdispCatIsIso f = isoToEquiv (iso (λ F → dC-mor F , record { dC-inv = dC-inv F ; dC-sec = dC-sec F ; dC-ret = dC-ret F }) _ (λ _ → refl) λ _ → refl)
  
    isIsoTotal≃dCIsIso : (f : C [ x , y ]) → (F : D [ f , X , Y ]ᴰ) → isIso (totalCat D) (f , F) ≃ (Σ[ isIso-f ∈ isIso C f ] dispCatIsIso isIso-f F)
    isIsoTotal≃dCIsIso f F = isoToEquiv (iso _ u (λ _ → refl) λ _ → refl)
      where
      u : Σ[ isIso-f ∈ isIso C f ] dispCatIsIso isIso-f F → isIso (totalCat D) (f , F)
      u (isIso-f , isIso-F) .inv = inv isIso-f , dC-inv isIso-F
      u (isIso-f , isIso-F) .sec i = sec isIso-f i , dC-sec isIso-F i
      u (isIso-f , isIso-F) .ret i = ret isIso-f i , dC-ret isIso-F i
  
    isProp-dispCatIsIso : {f : C [ x , y ]} (isIso-f : isIso C f) (F : D [ f , X , Y ]ᴰ) → isProp (dispCatIsIso isIso-f F)
    isProp-dispCatIsIso {f} isIso-f F = isPropΣCancel (isProp-isIso f) (≃→isProp (isIsoTotal≃dCIsIso f F) (isProp-isIso (f , F))) isIso-f
    
  open dispCatIso
  open dispCatIsIso

  module _ {f : CatIso C x y}
           {X : D ⦅ x ⦆} {Y : D ⦅ y ⦆} where

    makeDispCatIsoPath : {X' : D ⦅ x ⦆} → {Y' : D ⦅ y ⦆} → (p : X ≡ X') → (p' : Y ≡ Y') → (F : dispCatIso X Y f) → (F' : dispCatIso X' Y' f) →
                    PathP (λ i → D [ mor f , p i , p' i ]ᴰ) (dC-mor F) (dC-mor F') → PathP (λ i → dispCatIso (p i) (p' i) f) F F'
    makeDispCatIsoPath p p' F F' path-mor = subst2 (PathP (λ i → dispCatIso (p i) (p' i) f)) (retEq (dispCatIso≃ΣdispCatIsIso _ _ f) F)
                                                         (retEq (dispCatIso≃ΣdispCatIsIso _ _ f) F') path-dispCatIso
      where
      path-isIso : PathP (λ i → Σ (D [ mor f , p i , p' i ]ᴰ) (dispCatIsIso (p i) (p' i) (CatIso→isIso f))) (equivFun (dispCatIso≃ΣdispCatIsIso _ _ f) F) (equivFun (dispCatIso≃ΣdispCatIsIso _ _ f) F')
      path-isIso = ΣPathPProp (isProp-dispCatIsIso _ _ (CatIso→isIso f)) path-mor

      path-dispCatIso : PathP (λ i → dispCatIso (p i) (p' i) f) (equivFun (invEquiv (dispCatIso≃ΣdispCatIsIso _ _ f)) (equivFun (dispCatIso≃ΣdispCatIsIso _ _ f) F))
                              (equivFun (invEquiv (dispCatIso≃ΣdispCatIsIso _ _ f)) (equivFun (dispCatIso≃ΣdispCatIsIso _ _ f) F'))
      path-dispCatIso i = equivFun (invEquiv (dispCatIso≃ΣdispCatIsIso _ _ f)) (path-isIso i)                                                           


    makeDispCatIso≡ : (F F' : dispCatIso X Y f) → dC-mor F ≡ dC-mor F' → F ≡ F'
    makeDispCatIso≡ = makeDispCatIsoPath refl refl

    isSetDispCatIso : isSet (dispCatIso X Y f)
    isSetDispCatIso F F' p q i j .dC-mor = isSet→SquareP {A = λ _ _ → D [ mor f , _ , _ ]ᴰ} (λ _ _ → dC-homSet D _ _ _) (cong dC-mor p) (cong dC-mor q) refl refl i j
    isSetDispCatIso F F' p q i j .dC-inv = isSet→SquareP {A = λ _ _ → D [ inv f , _ , _ ]ᴰ} (λ _ _ → dC-homSet D _ _ _) (cong dC-inv p) (cong dC-inv q) refl refl i j
    isSetDispCatIso F F' p q i j .dC-sec = isSet→SquareP {A = λ i j → PathP (λ k → D [ sec f k , _ , _ ]ᴰ)
                                                          (isSetDispCatIso F F' p q i j .dC-inv ⋆⟨ D ⟩ᴰ isSetDispCatIso F F' p q i j .dC-mor) (dC-id D)}
                                                          (λ _ _ → isProp→isSet (isSet→isPropPathP _ (λ _ → dC-homSet D _ _ _) _ _)) (cong dC-sec p) (cong dC-sec q) refl refl i j
    isSetDispCatIso F F' p q i j .dC-ret = isSet→SquareP {A = λ i j → PathP (λ k → D [ ret f k , _ , _ ]ᴰ)
                                                          (isSetDispCatIso F F' p q i j .dC-mor ⋆⟨ D ⟩ᴰ isSetDispCatIso F F' p q i j .dC-inv) (dC-id D)}
                                                          (λ _ _ → isProp→isSet (isSet→isPropPathP _ (λ _ → dC-homSet D _ _ _) _ _)) (cong dC-ret p) (cong dC-ret q) refl refl i j

-- Keep it as en example?
--  makeDispCatIsoPath : {x y : ob C} {f : CatIso C x y} → {X : D ⦅ x ⦆} → {Y : D ⦅ y ⦆} → (F G : dispCatIso f X Y) → dC-mor F ≡ dC-mor G → F ≡ G
--  makeDispCatIsoPath {f = f} F G p = F≡G
--    where
--    q : dC-inv F ≡ dC-inv G
--    q = 
--       dC-inv F
--         ≡⟨ sym (fromPathP (dC-⋆IdR D (dC-inv F))) ⟩
---       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C _) (dC-inv F ⋆⟨ D ⟩ᴰ dC-id D)
--         ≡⟨ cong (λ G → subst (λ f → dC-hom D f _ _) (⋆IdR C (inv f)) (dC-inv F ⋆⟨ D ⟩ᴰ G)) (sym (dC-ret G)) ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C _) (dC-inv F ⋆⟨ D ⟩ᴰ subst (λ f → D [ f , _ , _ ]ᴰ) (ret f) (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G))
--         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C (inv f)) F) (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ inv f ⋆⟨ C ⟩ g , _ , _ ]ᴰ) (ret f) (λ G → dC-inv F ⋆⟨ D ⟩ᴰ G) _) ⟩
--      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdR C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) (ret f)) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G)))
--         ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) (ret f) ∙ ⋆IdR C _) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor G ⋆⟨ D ⟩ᴰ dC-inv G))
--         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) (ret f) ∙ ⋆IdR C _) F) (sym (fromPathP (dC-⋆Assoc D _ _ _))) ⟩
 --      subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) (ret f) ∙ ⋆IdR C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G))
--         ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _ ∙ cong (λ g → inv f ⋆⟨ C ⟩ g) (ret f) ∙ ⋆IdR C _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
 --        ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)) (isSetHom C _ _ _ _) ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → g ⋆⟨ C ⟩ inv f) (sec f) ∙ ⋆IdL C _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
--         ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _) ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → g ⋆⟨ C ⟩ inv f) (sec f)) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G))
 --        ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) F) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ g ⋆⟨ C ⟩ inv f , _ , _ ]ᴰ) (sec f) (λ F → F ⋆⟨ D ⟩ᴰ dC-inv G) _)) ⟩
 --      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor G) ⋆⟨ D ⟩ᴰ dC-inv G)
--         ≡⟨ cong (λ H → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (dC-inv F ⋆⟨ D ⟩ᴰ H) ⋆⟨ D ⟩ᴰ dC-inv G)) (sym p) ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ dC-inv G)
--         ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (F ⋆⟨ D ⟩ᴰ dC-inv G)) (dC-sec F) ⟩
--       subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (dC-id D ⋆⟨ D ⟩ᴰ dC-inv G)
 --        ≡⟨ fromPathP (dC-⋆IdL D (dC-inv G)) ⟩
 --      dC-inv G ∎
--
 --   F≡G : F ≡ G
--    F≡G i .dC-mor = p i
--    F≡G i .dC-inv = q i
--    F≡G i .dC-sec = isProp→PathP {B = λ i → subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (q i ⋆⟨ D ⟩ᴰ p i) ≡ dC-id D} (λ i → dC-homSet D _ _ _ _ _) (dC-sec F) (dC-sec G) i
--    F≡G i .dC-ret = isProp→PathP {B = λ i → subst (λ f → D [ f , _ , _ ]ᴰ) (ret f) (p i ⋆⟨ D ⟩ᴰ q i) ≡ dC-id D} (λ i → dC-homSet D _ _ _ _ _) (dC-ret F) (dC-ret G) i

open dispCatIso
open dispCatIsIso

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  idDispCatIso : {x : ob C} → {X : D ⦅ x ⦆} → dispCatIso D X X idCatIso
  idDispCatIso .dC-mor = dC-id D
  idDispCatIso .dC-inv = dC-id D
  idDispCatIso .dC-sec = dC-⋆IdL D (dC-id D)
  idDispCatIso .dC-ret = dC-⋆IdL D (dC-id D)

  dC-pathToIso : {x : ob C} → {X X' : D ⦅ x ⦆} → X ≡ X' → dispCatIso D X X' idCatIso
  dC-pathToIso {X = X} p = J (λ X' p → dispCatIso D X X' idCatIso) idDispCatIso p

  dC-pathToIsoRefl : {x : ob C} → {X : D ⦅ x ⦆} → dC-pathToIso refl ≡ idDispCatIso {X = X}
  dC-pathToIsoRefl {X = X} = JRefl (λ X' p → dispCatIso D X X' idCatIso) idDispCatIso  

  isUnivalent-dC : Type (ℓ-max (ℓ-max ℓC ℓD) ℓD')
  isUnivalent-dC = {x : ob C} → (X X' : D ⦅ x ⦆) → isEquiv (dC-pathToIso {x = x} {X = X} {X' = X'})
    
  dC-univEquiv : {x : ob C} → isUnivalent-dC → (X X' : D ⦅ x ⦆) → (X ≡ X') ≃ (dispCatIso D X X' idCatIso)
  dC-univEquiv isUnivD X X' = dC-pathToIso , isUnivD X X'


  isProp-isUnivalent-dC : isProp isUnivalent-dC
  isProp-isUnivalent-dC isUnivD isUnivD' = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsEquiv _)) isUnivD isUnivD'

  dC-morP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → D [ id C , X , Y ]ᴰ
  dC-morP p = dC-mor (dC-pathToIso p)

  dC-invP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → D [ id C , Y , X ]ᴰ
  dC-invP p = dC-inv (dC-pathToIso p)

  dC-secMorP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → subst (λ f → D [ f , Y , Y ]ᴰ) (⋆IdL C (id C)) (dC-invP p ⋆⟨ D ⟩ᴰ dC-morP p) ≡ dC-id D
  dC-secMorP p = fromPathP (dC-sec (dC-pathToIso p))

  dC-retMorP : {x : ob C} → {X Y : D ⦅ x ⦆} → (p : X ≡ Y) → subst (λ f → D [ f , X , X ]ᴰ) (⋆IdL C (id C)) (dC-morP p ⋆⟨ D ⟩ᴰ dC-invP p) ≡ dC-id D
  dC-retMorP p = fromPathP (dC-ret (dC-pathToIso p))

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
      F                                                                    ≡⟨ sym (fromPathP (dC-⋆IdL D F)) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (dC-id D ⋆⟨ D ⟩ᴰ F)        ≡⟨ cong (λ G → subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (G ⋆⟨ D ⟩ᴰ F)) (sym dC-reflInvP) ⟩
      subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdL C f) (dC-invP refl ⋆⟨ D ⟩ᴰ F)   ∎

  dC-substHomR : {x y : ob C} → {f : C [ x , y ]} → {X : D ⦅ x ⦆} → {Y Y' : D ⦅ y ⦆} → (p : Y ≡ Y') → (F : D [ f , X , Y ]ᴰ) →
                 subst (λ Y → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X , Y' ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP p)
  dC-substHomR {f = f} {X} {Y} {Y'} p F = J (λ Y' p → subst (λ Y → D [ f , X , Y ]ᴰ) p F ≡ subst (λ f → D [ f , X , Y' ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP p)) eqRefl p
    where
    eqRefl : subst (λ Y → D [ f , X , Y ]ᴰ) refl F ≡ subst (λ f → D [ f , X , Y ]ᴰ) (⋆IdR C f) (F ⋆⟨ D ⟩ᴰ dC-morP refl)
    eqRefl = 
      subst (λ Y → D [ f , X , Y ]ᴰ) refl F                               ≡⟨ substRefl {B = λ Y → D [ f , X , Y ]ᴰ} F ⟩
      F                                                                    ≡⟨ sym (fromPathP (dC-⋆IdR D F)) ⟩
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
