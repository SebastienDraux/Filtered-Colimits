module Filtered-Colimits.DisplayedCategories.CocartesianMorphisms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category

module _ {C : Category ℓC ℓC'} where
  record CatIsIso {x y : ob C} (f : C [ x , y ]) : Type ℓC' where
    field
      inv : C [ y , x ]
      sec : inv ⋆⟨ C ⟩ f ≡ C .id
      ret : f ⋆⟨ C ⟩ inv ≡ C .id

  iso→precompEquiv : {x y : ob C} {f : C [ x , y ]} (f-inv : CatIsIso f) {z : ob C} → isEquiv {A = C [ y , z ]} {B = C [ x , z ]} (λ g → f ⋆⟨ C ⟩ g)
  iso→precompEquiv f-inv = isoToIsEquiv (iso _ ((λ g → inv ⋆⟨ C ⟩ g)) p q) where
     open CatIsIso f-inv

     p : section (λ z → (C ⋆ _) z) (λ g → seq' C inv g)
     p = (λ h → sym (⋆Assoc C _ _ _) ∙ cong (λ u → u ⋆⟨ C ⟩ h) ret ∙ ⋆IdL C _)
     
     q : retract (λ z → (C ⋆ _) z) (λ g → seq' C inv g)
     q = (λ g → sym (⋆Assoc C _ _ _) ∙ cong (λ u → u ⋆⟨ C ⟩ g) sec ∙ ⋆IdL C _)

open dispCat
open dispCatIso
open CatIso
 

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  iso→isCocartesian : {x y : ob C} → {f : CatIso C x y} → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆)→ (F : dispCatIso D f X Y) → isCocartesian D (mor f) X Y (dC-mor F)
  iso→isCocartesian {f = f} X Y F {g = g} {h} p H = uniqueExists (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)) eq (λ _ → dC-homSet D _ _ _ _ _) eq'
    where
    p' : inv f ⋆⟨ C ⟩ h ≡ g
    p' = 
      inv f ⋆⟨ C ⟩ h                  ≡⟨ cong (λ h → inv f ⋆⟨ C ⟩ h) (sym p) ⟩
      inv f ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ g)    ≡⟨ sym (⋆Assoc C _ _ _) ⟩
      (inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ g    ≡⟨ cong (λ f → f ⋆⟨ C ⟩ g) (sec f) ⟩
      id C ⋆⟨ C ⟩ g                   ≡⟨ ⋆IdL C _ ⟩
      g ∎
    eq : subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H))) ≡ H
    eq = 
      subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) p) (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ mor f ⋆⟨ C ⟩ g , _ , _ ]ᴰ) p' (λ H → dC-mor F ⋆⟨ D ⟩ᴰ H) (dC-inv F ⋆⟨ D ⟩ᴰ H)) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) p (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p') (dC-mor F ⋆⟨ D ⟩ᴰ (dC-inv F ⋆⟨ D ⟩ᴰ H)))
        ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p' ) p _ ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p' ∙ p) (dC-mor F ⋆⟨ D ⟩ᴰ (dC-inv F ⋆⟨ D ⟩ᴰ H))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) _) (sym (dC-⋆Assoc D _ _ _)) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) _ (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H))
        ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) _ _ ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) _ ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
        ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)) (isSetHom C _ _ _ _) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f) ∙ ⋆IdL C _) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
        ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f)) (⋆IdL C _) _) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f)) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _)) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ f ⋆⟨ C ⟩ _ , _ , _ ]ᴰ) (ret f) (λ F → F ⋆⟨ D ⟩ᴰ H) (dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F))) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (ret f) (dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
        ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (F ⋆⟨ D ⟩ᴰ H)) (dC-ret F) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (dC-id D ⋆⟨ D ⟩ᴰ H)
        ≡⟨ dC-⋆IdL D H ⟩
      H ∎
      
    eq' : (G : D [ _ , _ , _ ]ᴰ) → subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ G) ≡ H → subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H) ≡ G
    eq' G q = 
      subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)
        ≡⟨ cong (λ G → subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ G)) (sym q) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ G)))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) p') (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ inv f ⋆⟨ C ⟩ g , _ , _ ]ᴰ) p (λ G → dC-inv F ⋆⟨ D ⟩ᴰ G) _) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) p' (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) p) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor F ⋆⟨ D ⟩ᴰ G)))
        ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) _ (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor F ⋆⟨ D ⟩ᴰ G))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) _) (sym (dC-⋆Assoc D _ _ _)) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) _ (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G))
        ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) _ ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
        ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)) (isSetHom C _ _ _ _) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (sec f) ∙ ⋆IdL C _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
        ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (sec f)) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G))
        ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _)) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ f ⋆⟨ C ⟩ _ , _ , _ ]ᴰ) _ (λ F → F ⋆⟨ D ⟩ᴰ G) _)) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
        ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (F ⋆⟨ D ⟩ᴰ G)) (dC-sec F) ⟩
      subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (dC-id D ⋆⟨ D ⟩ᴰ G)
        ≡⟨ dC-⋆IdL D G ⟩
      G ∎
    
  isCocartesian-id : {x : ob C}  → (X : D ⦅ x ⦆) → isCocartesian D (id C) X X (dC-id D)
  isCocartesian-id X = iso→isCocartesian X X (idDispCatIso D)

  record dispCatIsIso {x y : ob C} {f : C [ x , y ]} (f-inv : CatIsIso {C = C} f) {X : D ⦅ x ⦆} {Y : D ⦅ y ⦆} (F : D [ f , X , Y ]ᴰ) : Type ℓD' where
    open CatIsIso
    field
      dC-inv : D [ inv f-inv , Y , X ]ᴰ
      -- equivalent to: subst (λ f → D [ f , Y , Y ]ᴰ) (sec f-inv) (dC-inv ⋆⟨ D ⟩ᴰ F) ≡ dC-id D
      dC-sec : PathP (λ i → D [ sec f-inv i , Y , Y ]ᴰ) (dC-inv ⋆⟨ D ⟩ᴰ F) (dC-id D) 
      dC-ret : PathP (λ i → D [ ret f-inv i , X , X ]ᴰ) (F ⋆⟨ D ⟩ᴰ dC-inv) (dC-id D)

  open CatIsIso
  open dispCatIsIso

  u : {x y : ob C} {f : C [ x , y ]} {X : D ⦅ x ⦆} {Y : D ⦅ y ⦆} {F : D [ f , X , Y ]ᴰ} → Σ (CatIsIso f) (λ f-inv → dispCatIsIso f-inv F) ≃ CatIsIso {C = totalCat D} (f , F)
  u = isoToEquiv (iso α _ (λ _ → refl) (λ _ → refl)) where
    α : _ → _
    α (f-inv , F-inv) .inv = (inv f-inv , dC-inv F-inv)
    α (f-inv , F-inv) .sec i = (sec f-inv i , dC-sec F-inv i)
    α (f-inv , F-inv) .ret i = (ret f-inv i , dC-ret F-inv i)

  private
    variable
      ℓA ℓB : Level

  isCocartesian' : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → D [ f , X , Y ]ᴰ → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isCocartesian' {x} {y} f X Y F = {z : ob C} → {g : C [ y , z ]} → {h : C [ x , z ]} → (p : f ⋆⟨ C ⟩ g ≡ h) → {Z : D ⦅ z ⦆} → (H : D [ h , X , Z ]ᴰ) →
                                           ∃![ G ∈ D [ g , Y , Z ]ᴰ ] PathP (λ i → D [ p i , X , Z ]ᴰ) (F ⋆⟨ D ⟩ᴰ G) H

  isCocartesianFibration' : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  isCocartesianFibration' = {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → ∃![ Y ∈ D ⦅ y ⦆ ] Σ[ F ∈ D [ f , X , Y ]ᴰ ] isCocartesian' f X Y F

  module _ {A : Type ℓA} {B : Type ℓB} where
    postulate
      isContrInvariant : (e : A ≃ B) → isContr A → isContr B

  module _ {A : Type ℓA} {B : A → Type ℓB} where
    postulate
      isContrCancelRight : isContr A → isContr (Σ A B) → (a : A) → isContr (B a)
      isContrCancelLeft : (a : A) → isContr (B a) → isContr (Σ A B) → isContr A
      isContrCompose : isContr A → (a : A) → isContr (B a) → isContr (Σ A B)

  iso→isCocartesian' : {x y : ob C} {f : C [ x , y ]} {f-inv : CatIsIso f} {X : D ⦅ x ⦆} {Y : D ⦅ y ⦆} {F : D [ f , X , Y ]ᴰ} (F-inv : dispCatIsIso f-inv F) → isCocartesian' f X Y F
  iso→isCocartesian' {x} {y} {f} {f-inv} {X} {Y} {F} F-inv {z} {g} {h} p {Z} H = isContrCancelRight
    {A = Σ[ g ∈ C [ y , z ] ] f ⋆⟨ C ⟩ g ≡ h}
    {B = λ {(g , p) → Σ[ G ∈ D [ g , Y , Z ]ᴰ ] PathP (λ i → D [ p i , X , Z ]ᴰ) (F ⋆⟨ D ⟩ᴰ G) H} }
    (iso→precompEquiv {C = C} f-inv .equiv-proof _)
    (isContrInvariant {A = Σ[ gG ∈ totalCat D [ (y , Y) , (z , Z) ] ] (f , F) ⋆⟨ totalCat D ⟩ gG ≡ (h , H)} (isoToEquiv (iso _ (λ { ((g , p) , (G , P)) → (((g , G)) , (λ i → (p i , P i)))}) (λ _ → refl) (λ _ → refl))) ((iso→precompEquiv {C = totalCat D} (equivFun u (f-inv , F-inv)) .equiv-proof _)))
    (g , (λ i → p i))
