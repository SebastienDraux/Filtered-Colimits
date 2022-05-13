module Filtered-Colimits.DisplayedCategories.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Discrete

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat
open import Filtered-Colimits.DisplayedCategories.DispPreorder
open import Filtered-Colimits.DisplayedCategories.LeftFibrations

open Category
open dispCat

module _ {ℓC ℓC' ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD) where

  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
         
  data reflection-ob : (x : ob C) → Type ℓ where
    fromD-ob : {x : ob C} → (X : D ⦅ x ⦆) → reflection-ob x
    leftFib-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → reflection-ob y
    coherence-seq : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : reflection-ob x) → leftFib-ob (f ⋆⟨ C ⟩ g) X ≡ leftFib-ob g (leftFib-ob f X)
    coherence-fromD : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → leftFib-ob f (fromD-ob X) ≡ fromD-ob Y
    coherence-id : {x : ob C} → (X : reflection-ob x) → leftFib-ob (id C) X ≡ X
    coherence-id-fromD : {x : ob C} → (X : D ⦅ x ⦆) → coherence-id (fromD-ob X) ≡ coherence-fromD (id C) X X (dC-id D)
 --   test2 : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x)  → coherence-id (leftFib-ob f X) ≡ sym (coherence-seq f (id C) X) ∙ cong (λ f → leftFib-ob f X) (⋆IdR C _)
   -- is-set : {x : ob C} → isSet (reflection-ob x)

      
  data reflection-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → Type ℓ where
    fromD-hom : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → reflection-hom f (fromD-ob X) (fromD-ob Y)
    leftFib-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) →  reflection-hom f X (leftFib-ob f X)
    coherence-id-hom : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) →
                   PathP (λ i → reflection-hom (id C) (coherence-fromD f X Y F i) (coherence-fromD f X Y F i))
                   (subst (reflection-hom (id C) (leftFib-ob f (fromD-ob X)))
                          (coherence-id (leftFib-ob f (fromD-ob X)))
                          (leftFib-hom (id C) (leftFib-ob f (fromD-ob X))))
                   (fromD-hom (id C) Y Y (dC-id D))
   -- coherence-⋆IdL-fromD : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) →
   --                        PathP (λ i → reflection-hom (⋆IdL C f i) (fromD X) ((coherence-seq (id C) f (fromD X) ∙ cong (leftFib-ob f) (coherence-id (fromD X)) ∙ coherence-fromD f X Y F) i))
   --                              (leftFib-hom (id C ⋆⟨ C ⟩ f) (fromD X))
   --                              (fromD f X Y F)
   -- is-prop : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → isProp (reflection-hom f X Y)

  unicity-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → reflection-hom f X Y → leftFib-ob f X ≡ Y
  unicity-ob f .(fromD-ob X) .(fromD-ob Y) (fromD-hom .f X Y F) = coherence-fromD f X Y F
  unicity-ob f X .(leftFib-ob f X) (leftFib-hom .f .X) = refl
  unicity-ob .(id C) .(coherence-fromD f X Y F i) .(coherence-fromD f X Y F i) (coherence-id-hom f X Y F i) = {!!}
  
--  coherence-id' : {x : ob C} → (X : reflection-ob x) → leftFib-ob (id C) X ≡ X
--  coherence-id' (fromD X) = coherence-fromD (id C) X X (dC-id D)
--  coherence-id' (leftFib-ob f X) = sym (coherence-seq f (id C) X) ∙ cong (λ f → leftFib-ob f X) (⋆IdR C _)
--  coherence-id' {x} (coherence-seq f g X i) = {!!} --isProp→PathP {B = λ i → leftFib-ob (id C) (coherence-seq f g X i) ≡ coherence-seq f g X i}
--                                                            (λ i → is-set _ _)
 --                                                          (coherence-id (leftFib-ob (f ⋆⟨ C ⟩ g) X))
--                                                           (coherence-id (leftFib-ob g (leftFib-ob f X))) i
--  coherence-id' (coherence-fromD f X Y F i) = {!!}
  --isProp→PathP {B = λ i → leftFib-ob (id C) (coherence-fromD f X Y F i) ≡ coherence-fromD f X Y F i}
 --                                                          (λ i → is-set _ _) (coherence-id (leftFib-ob f (fromD X)))
--                                                           (coherence-id (fromD Y)) i
 --  coherence-id (is-set X Y p q i j) = isSet→SquareP {A = λ i j → (leftFib-ob (id C) (is-set X Y p q i j) ≡ is-set X Y p q i j)} (
--                                                     λ i j → isProp→isSet (is-set _ _))
--                                                     (cong coherence-id p) (cong coherence-id q) refl refl
--                                                     i j

  reflection : dispCat C ℓ ℓ
  reflection .dC-ob = reflection-ob
  reflection .dC-hom = reflection-hom
  reflection .dC-id {X = fromD-ob X} = fromD-hom (id C) X X (dC-id D)
  reflection .dC-id {X = leftFib-ob f X} = subst (reflection-hom (id C) (leftFib-ob f X))
                                                 (coherence-id (leftFib-ob f X))
                                                 (leftFib-hom (id C) (leftFib-ob f X))
  reflection .dC-id {X = coherence-seq f g X i} = subst (reflection-hom (id C) (coherence-seq f g X i))
                                                         (cong coherence-id (coherence-seq f g X) i)
                                                         (leftFib-hom (id C) (coherence-seq f g X i))
  reflection .dC-id {X = coherence-fromD f X Y F i} = coherence-id-hom f X Y F i
  reflection .dC-id {X = coherence-id-fromD X i j} = {!!}
  reflection .dC-id {X = coherence-id (fromD-ob X) i} = subst (λ p → PathP (λ i → reflection-hom (id C) (p i) (p i))
                                                                             (subst (reflection-hom (id C) (leftFib-ob (id C) (fromD-ob X)))
                                                                                    (coherence-id (leftFib-ob (id C) (fromD-ob X)))
                                                                                    (leftFib-hom (id C) (leftFib-ob (id C) (fromD-ob X))))
                                                                             (fromD-hom (id C) X X (dC-id D)))
                                                              (sym (coherence-id-fromD X))
                                                              (coherence-id-hom (id C) X X (dC-id D)) i
  reflection .dC-id {X = coherence-id (leftFib-ob f X) i} = subst (reflection-hom (id C) (coherence-id (leftFib-ob f X) i))
                                                                   (coherence-id (coherence-id (leftFib-ob f X) i))
                                                                   (leftFib-hom (id C) (coherence-id (leftFib-ob f X) i))
  reflection .dC-id {X = coherence-id (coherence-seq f g X i) j} = subst (reflection-hom (id C) (coherence-id (coherence-seq f g X i) j))
                                                                         (coherence-id (coherence-id (coherence-seq f g X i) j))
                                                                         (leftFib-hom (id C) (coherence-id (coherence-seq f g X i) j))
  reflection .dC-id {X = coherence-id (coherence-fromD f X Y F i) j} = {!!}
  reflection .dC-id {X = coherence-id (coherence-id X i) j} = {!!}
  reflection .dC-id {X = coherence-id (coherence-id-fromD X i j) k} = {!!}
  reflection .dC-⋆ {X = X} {Y} {Z} {f} {g} F G = subst (reflection-hom (f ⋆⟨ C ⟩ g) X) p (leftFib-hom (f ⋆⟨ C ⟩ g) X) 
    where
    p : leftFib-ob (f ⋆⟨ C ⟩ g) X ≡ Z
    p = coherence-seq f g X ∙ cong (leftFib-ob g) (unicity-ob f X Y F) ∙ (unicity-ob g Y Z G)
  --reflection .dC-⋆IdL {X = .(fromD X)} {.(fromD Y)} (fromD _ X Y F) = {!!}
 -- reflection .dC-⋆IdL {X = X} {.(leftFib-ob _ X)} (leftFib-hom _ .X) = {!!}
  reflection .dC-⋆IdL F = {!!}
  reflection .dC-⋆IdR F = {!!} --is-prop _ _ _ _ _
  reflection .dC-⋆Assoc F G H = {!!} ---is-prop _ _ _ _ _
  reflection .dC-homSet f X Y = {!!} --isProp→isSet (is-prop f X Y)

--subst (λ f → reflection-hom f (fromD X) (fromD Y))
--      (⋆IdL C f)
--      (subst (reflection-hom (seq' C (id C) f) (fromD X))
        --     (coherence-seq (id C) f (fromD X) ∙ cong (leftFib-ob f) (coherence-fromD (id C) X X (subst (reflection-hom (id C) (fromD X)) (coherence-fromD (id C) X X (dC-id D)) (leftFib-hom (id C) (fromD X)))) ∙ coherence-fromD f X Y F)
--             (leftFib-hom (seq' C (id C) f) (fromD X)))
--      ≡ fromD f X Y F
--subst (reflection-hom (id C ⋆⟨ C ⟩ f) (fromD X)) (coherence-seq (id C) f (fromD X) ∙ cong (leftFib-ob f) (coherence-fromD (id C) X X ?) ∙ coherence-fromD f X Y F) (leftFib-hom (f ⋆⟨ C ⟩ g) X)


module _ {ℓC ℓC' ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD) where

  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
    
  mutual
    data reflection-ob' : (x : ob C) → Type ℓ where
      fromD-ob' : {x : ob C} → (X : D ⦅ x ⦆) → reflection-ob' x
      leftFib-ob' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → reflection-ob' y
      unicity-ob' :  {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → reflection-hom' f X Y → leftFib-ob' f X ≡ Y
       
    data reflection-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → Type ℓ where
      fromD-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (D [ f , X , Y ]ᴰ) → reflection-hom' f (fromD-ob' X) (fromD-ob' Y)
      leftFib-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) →  reflection-hom' f X (leftFib-ob' f X)
      unicity-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (F : reflection-hom' f X Y) →
                     PathP (λ i → reflection-hom' f X (unicity-ob' f X Y F i)) (leftFib-hom' f X) F

  unicity-seq' : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : reflection-ob' x) → leftFib-ob' (f ⋆⟨ C ⟩ g) X ≡ leftFib-ob' g (leftFib-ob' f X)
 -- unicity-seq' f g X = unicity-ob' (f ⋆⟨ C ⟩ g) X (leftFib-ob' g (leftFib-ob' f X)) {!!}
  unicity-seq' f g (fromD-ob' X) = unicity-ob' (seq' C f g) (fromD-ob' X) (leftFib-ob' g (leftFib-ob' f (fromD-ob' X))) {!!}
  unicity-seq' f g (leftFib-ob' h X) = sym (unicity-seq' h (f ⋆⟨ C ⟩ g) X) ∙
                                       cong (λ f → leftFib-ob' f X) (sym (⋆Assoc C _ _ _)) ∙
                                       unicity-seq' (h ⋆⟨ C ⟩ f) g X ∙
                                       cong (leftFib-ob' g) (unicity-seq' h f X)
  unicity-seq' f g (unicity-ob' f₁ X X₁ x i) = {!!}
  
  --unicity-seq' f g (fromD' X) = {!!} 
                 --sym (unicity-ob' g (leftFib-ob' f (fromD' X)) (leftFib-ob' (f ⋆⟨ C ⟩ g) (fromD' X)) {!!})
--unicity-ob' (f ⋆⟨ C ⟩ g) (fromD' X) (leftFib-ob' g (leftFib-ob' f (fromD' X))) {!!}
--  unicity-seq' f g (leftFib-ob' h X) =
--      sym (unicity-seq' h (f ⋆⟨ C ⟩ g) X) ∙ cong (λ f → leftFib-ob' f X) (sym (⋆Assoc C _ _ _)) ∙ unicity-seq' (h ⋆⟨ C ⟩ f) g X ∙ cong (leftFib-ob' g) (unicity-seq' h f X)
--  unicity-seq' f g (unicity-ob' h X Y F i) = {!!}

  unicity-id' :  {x : ob C} → (X : reflection-ob' x) → leftFib-ob' (id C) X ≡ X
  unicity-id' (fromD-ob' X) = unicity-ob' (id C) (fromD-ob' X) (fromD-ob' X) (fromD-hom' (id C) X X (dC-id D))
  unicity-id' (leftFib-ob' f X) = {!!}
  unicity-id' (unicity-ob' f X X₁ x i) = {!!}
--  unicity-id' (fromD' X) = unicity-ob' (id C) (fromD' X) (fromD' X) (fromD' (id C) X X (dC-id D))
--  unicity-id' (leftFib-ob' f (fromD' X)) = {!!} --sym (unicity-ob' f (fromD' X) (leftFib-ob' (id C) (leftFib-ob' f (fromD' X))) {!!})
--  unicity-id' (leftFib-ob' f (leftFib-ob' f₁ X)) = {!!}
--  unicity-id' (leftFib-ob' f (unicity-ob' f₁ X X₁ x i)) = {!!}
--  unicity-id' (unicity-ob' f X X₁ x i) = {!!}

  D'' : dispCat C ℓ ℓ
  D'' .dC-ob = reflection-ob'
  D'' .dC-hom = reflection-hom'
  D'' .dC-id {X = fromD-ob' X} = fromD-hom' (id C) X X (dC-id D)
  D'' .dC-id {X = leftFib-ob' f X} = {!!}
    where
    test : leftFib-ob' (id C) X ≡ X
    test = unicity-ob' (id C) X X (D'' .dC-id)
  D'' .dC-id {X = unicity-ob' f X X₁ x i} = {!!}
  --subst (λ Y → reflection-hom' (id C) X Y) {!!} (leftFib-hom' (id C) X)
  D'' .dC-⋆ F G = {!!}
  D'' .dC-⋆IdL = {!!}
  D'' .dC-⋆IdR = {!!}
  D'' .dC-⋆Assoc = {!!}
  D'' .dC-homSet = {!!}
