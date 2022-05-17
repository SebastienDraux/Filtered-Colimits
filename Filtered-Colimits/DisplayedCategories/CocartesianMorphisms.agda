module Filtered-Colimits.DisplayedCategories.CocartesianMorphisms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open dispCat
open dispCatIso
open dispCatIsIso
open CatIso

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

 --TODO: rewrite this proof without subst
 -- iso→isCocartesian : {x y : ob C} → {f : CatIso C x y} → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆)→ (F : dispCatIso D f X Y) → isCocartesian D (mor f) X Y (dC-mor F)
 -- iso→isCocartesian {f = f} X Y F {g = g} {h} p H = uniqueExists (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)) eq (λ _ → dC-homSet D _ _ _ _ _) eq'
 --   where
 --   p' : inv f ⋆⟨ C ⟩ h ≡ g
 --   p' = 
 --     inv f ⋆⟨ C ⟩ h                  ≡⟨ cong (λ h → inv f ⋆⟨ C ⟩ h) (sym p) ⟩
 --     inv f ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ g)    ≡⟨ sym (⋆Assoc C _ _ _) ⟩
 --     (inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ g    ≡⟨ cong (λ f → f ⋆⟨ C ⟩ g) (sec f) ⟩
 --     id C ⋆⟨ C ⟩ g                   ≡⟨ ⋆IdL C _ ⟩
 --     g ∎
 --   eq : subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H))) ≡ H
  --  eq = 
  --    subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)))
  --      ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) p) (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ mor f ⋆⟨ C ⟩ g , _ , _ ]ᴰ) p' (λ H → dC-mor F ⋆⟨ D ⟩ᴰ H) (dC-inv F ⋆⟨ D ⟩ᴰ H)) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) p (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p') (dC-mor F ⋆⟨ D ⟩ᴰ (dC-inv F ⋆⟨ D ⟩ᴰ H)))
  --      ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p' ) p _ ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → mor f ⋆⟨ C ⟩ g) p' ∙ p) (dC-mor F ⋆⟨ D ⟩ᴰ (dC-inv F ⋆⟨ D ⟩ᴰ H))
  --      ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) _) (sym (fromPathP (dC-⋆Assoc D _ _ _))) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) _ (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H))
  --      ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) _ _ ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) _ ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
  --      ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)) (isSetHom C _ _ _ _) ⟩
   --   subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f) ∙ ⋆IdL C _) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
  --      ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f)) (⋆IdL C _) _) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (ret f)) ((dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H))
 --       ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _)) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ f ⋆⟨ C ⟩ _ , _ , _ ]ᴰ) (ret f) (λ F → F ⋆⟨ D ⟩ᴰ H) (dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F))) ⟩
 --     subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (ret f) (dC-mor F ⋆⟨ D ⟩ᴰ dC-inv F) ⋆⟨ D ⟩ᴰ H)
 --       ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (F ⋆⟨ D ⟩ᴰ H)) (dC-ret F) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (dC-id D ⋆⟨ D ⟩ᴰ H)
  --      ≡⟨ fromPathP (dC-⋆IdL D H) ⟩
  --    H ∎
  --    
  --  eq' : (G : D [ _ , _ , _ ]ᴰ) → subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ G) ≡ H → subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H) ≡ G
  --  eq' G q = 
  --    subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ H)
  --      ≡⟨ cong (λ G → subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ G)) (sym q) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) p' (dC-inv F ⋆⟨ D ⟩ᴰ (subst (λ f → D [ f , _ , _ ]ᴰ) p (dC-mor F ⋆⟨ D ⟩ᴰ G)))
   --     ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) p') (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ g → D [ inv f ⋆⟨ C ⟩ g , _ , _ ]ᴰ) p (λ G → dC-inv F ⋆⟨ D ⟩ᴰ G) _) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) p' (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ g → inv f ⋆⟨ C ⟩ g) p) (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor F ⋆⟨ D ⟩ᴰ G)))
  --      ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) _ (dC-inv F ⋆⟨ D ⟩ᴰ (dC-mor F ⋆⟨ D ⟩ᴰ G))
   --     ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) _) (sym (fromPathP (dC-⋆Assoc D _ _ _))) ⟩
   --   subst (λ f → D [ f , _ , _ ]ᴰ) _ (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆Assoc C _ _ _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G))
   --     ≡⟨ subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _ ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) _ ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
   --     ≡⟨ cong (λ p → subst (λ f → D [ f , _ , _ ]ᴰ) p ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)) (isSetHom C _ _ _ _) ⟩
   --   subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (sec f) ∙ ⋆IdL C _) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
  --      ≡⟨ sym (subst-subst (λ f → D [ f , _ , _ ]ᴰ) _ _ _) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (cong (λ f → f ⋆⟨ C ⟩ _) (sec f)) ((dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G))
  --      ≡⟨ cong (subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _)) (sym (congSubst (λ f → D [ f , _ , _ ]ᴰ) (λ f → D [ f ⋆⟨ C ⟩ _ , _ , _ ]ᴰ) _ (λ F → F ⋆⟨ D ⟩ᴰ G) _)) ⟩
  --    subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (subst (λ f → D [ f , _ , _ ]ᴰ) (sec f) (dC-inv F ⋆⟨ D ⟩ᴰ dC-mor F) ⋆⟨ D ⟩ᴰ G)
  --      ≡⟨ cong (λ F → subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (F ⋆⟨ D ⟩ᴰ G)) (dC-sec F) ⟩
   --   subst (λ f → D [ f , _ , _ ]ᴰ) (⋆IdL C _) (dC-id D ⋆⟨ D ⟩ᴰ G)
   --     ≡⟨ fromPathP (dC-⋆IdL D G) ⟩
     -- G ∎
   -- 
 -- isCocartesian-id : {x : ob C}  → (X : D ⦅ x ⦆) → isCocartesian D (id C) X X (dC-id D)
 -- isCocartesian-id X = iso→isCocartesian X X (idDispCatIso D)

module _ {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD') where

  isCocartesian-id : {x : ob C}  → (X : D ⦅ x ⦆) → isCocartesian D (id C) X X (dC-id D)
  isCocartesian-id X {g = g} p {Z = Z} H = uniqueExists H' path (λ _ → isSet→isPropPathP _ (λ _ → dC-homSet D _ _ _) _ _) λ G path → fromPathP (path' G path)
    where
    q = sym p ∙ ⋆IdL C _
    q' = q ∙ sym (⋆IdL C _)
    H' = subst (λ f → D [ f , X , Z ]ᴰ) q H
    H'' = subst (λ f → D [ f , X , Z ]ᴰ) q' H
    
    s : subst (λ f → D [ f , X , Z ]ᴰ) q' H ≡ dC-id D ⋆⟨ D ⟩ᴰ H'
    s = substComposite (λ f → D [ f , X , Z ]ᴰ) q (sym (⋆IdL C _)) H ∙ fromPathP (symP (dC-⋆IdL D H'))
    
    path : PathP (λ i → D [ p i , X , Z ]ᴰ) (dC-id D ⋆⟨ D ⟩ᴰ H') H
    path = subst (λ F → PathP (λ i → D [ p i , X , Z ]ᴰ) F H) s
                 (subst (λ p → PathP (λ i → D [ p i , X , Z ]ᴰ) H'' H) (isSetHom C _ _ (sym q') p)
                        (symP (subst-filler (λ f → D [ f , X , Z ]ᴰ) q' H)))
                                        
    path' : (G : D [ g , X , Z ]ᴰ) → PathP (λ i → D [ p i , X , Z ]ᴰ) (dC-id D ⋆⟨ D ⟩ᴰ G) H → PathP (λ i → D [ q i , X , Z ]ᴰ) H G
    path' G path = subst (λ F → PathP (λ i → D [ q i , X , Z ]ᴰ) F G) r'
                      (subst (λ p → PathP (λ i → D [ p i , X , Z ]ᴰ) G' G) (isSetHom C _ _ (sym r) q)
                             (symP (subst-filler (λ f → D [ f , X , Z ]ᴰ) r G)))
      where
      r = sym (⋆IdL C _) ∙ p
      G' = subst (λ f → D [ f , X , Z ]ᴰ) r G
      r' : subst (λ f → D [ f , X , Z ]ᴰ) r G ≡ H
      r' = substComposite (λ f → D [ f , X , Z ]ᴰ) (sym (⋆IdL C _)) p G ∙ cong (subst (λ f → D [ f , X , Z ]ᴰ) p) (fromPathP (symP (dC-⋆IdL D G))) ∙ fromPathP path
