module Filtered-Colimits.DisplayedCategories.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.Functors
open import Filtered-Colimits.DisplayedCategories.IsoDispCat
open import Filtered-Colimits.DisplayedCategories.DispPreorder
open import Filtered-Colimits.DisplayedCategories.LeftFibrations

open Category
open dispCat
open dispCat-Funct
open dispCatIso
open eq-dF

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
  --reflection .dC-id {X = fromD-ob X} = fromD-hom (id C) X X (dC-id D)
 -- reflection .dC-id {X = leftFib-ob f X} = subst (reflection-hom (id C) (leftFib-ob f X))
--                                                 (coherence-id (leftFib-ob f X))
 --                                                (leftFib-hom (id C) (leftFib-ob f X))
 -- reflection .dC-id {X = coherence-seq f g X i} = subst (reflection-hom (id C) (coherence-seq f g X i))
 --                                                       (cong coherence-id (coherence-seq f g X) i)
 --                                                       (leftFib-hom (id C) (coherence-seq f g X i))
 -- reflection .dC-id {X = coherence-fromD f X Y F i} = coherence-id-hom f X Y F i
 --- reflection .dC-id {X = coherence-id-fromD X i j} = {!!}
 -- reflection .dC-id {X = coherence-id (fromD-ob X) i} = subst (λ p → PathP (λ i → reflection-hom (id C) (p i) (p i))
 ---                                                                            (subst (reflection-hom (id C) (leftFib-ob (id C) (fromD-ob X)))
 --                                                                                   (coherence-id (leftFib-ob (id C) (fromD-ob X)))
 --                                                                                   (leftFib-hom (id C) (leftFib-ob (id C) (fromD-ob X))))
 --                                                                            (fromD-hom (id C) X X (dC-id D)))
 --                                                             (sym (coherence-id-fromD X))
 --                                                             (coherence-id-hom (id C) X X (dC-id D)) i
--  reflection .dC-id {X = coherence-id (leftFib-ob f X) i} = subst (reflection-hom (id C) (coherence-id (leftFib-ob f X) i))
--                                                                   (coherence-id (coherence-id (leftFib-ob f X) i))
--                                                                   (leftFib-hom (id C) (coherence-id (leftFib-ob f X) i))
--  reflection .dC-id {X = coherence-id (coherence-seq f g X i) j} = subst (reflection-hom (id C) (coherence-id (coherence-seq f g X i) j))
--                                                                         (coherence-id (coherence-id (coherence-seq f g X i) j))
--                                                                         (leftFib-hom (id C) (coherence-id (coherence-seq f g X i) j))
--  reflection .dC-id {X = coherence-id (coherence-fromD f X Y F i) j} = {!!}
----  reflection .dC-id {X = coherence-id (coherence-id X i) j} = {!!}
--  reflection .dC-id {X = coherence-id (coherence-id-fromD X i j) k} = {!!}
  reflection .dC-id {X = X} = subst (λ Y → reflection-hom (id C) X Y) (coherence-id X) (leftFib-hom (id C) X)
  reflection .dC-⋆ {X = X} {Y} {Z} {f} {g} F G = subst (reflection-hom (f ⋆⟨ C ⟩ g) X) p (leftFib-hom (f ⋆⟨ C ⟩ g) X)
    where
    p : leftFib-ob (f ⋆⟨ C ⟩ g) X ≡ Z
    p = coherence-seq f g X ∙ cong (leftFib-ob g) (unicity-ob f X Y F) ∙ (unicity-ob g Y Z G)
--  reflection .dC-⋆IdL {X = .(fromD X)} {.(fromD Y)} (fromD _ X Y F) = {!!}
--  reflection .dC-⋆IdL {X = X} {.(leftFib-ob _ X)} (leftFib-hom _ .X) = {!!}
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
         (D : dispCat C ℓD ℓD') where

  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

  mutual
    data reflection-ob' : (x : ob C) → Type ℓ where
      fromD-ob' : {x : ob C} → (X : D ⦅ x ⦆) → reflection-ob' x
      leftFib-ob' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → reflection-ob' y
      unicity-ob' :  {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (F : reflection-hom' f X Y) → leftFib-ob' f X ≡ Y

    data reflection-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → Type ℓ where
      fromD-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → reflection-hom' f (fromD-ob' X) (fromD-ob' Y)
      leftFib-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) →  reflection-hom' f X (leftFib-ob' f X)
      unicity-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (F : reflection-hom' f X Y) →
                     PathP (λ i → reflection-hom' f X (unicity-ob' f X Y F i)) (leftFib-hom' f X) F
      seq-hom' : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (Z : reflection-ob' z)
                 → reflection-hom' f X Y → reflection-hom' g Y Z → reflection-hom' (f ⋆⟨ C ⟩ g) X Z
      fromD-seq' : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (Z : D ⦅ z ⦆) → (F : D [ f , X , Y ]ᴰ) → (G : D [ g , Y , Z ]ᴰ) →
                   fromD-hom' (f ⋆⟨ C ⟩ g) X Z (F ⋆⟨ D ⟩ᴰ G) ≡ seq-hom' f g (fromD-ob' X) (fromD-ob' Y) (fromD-ob' Z) (fromD-hom' f X Y F) (fromD-hom' g Y Z G)
      id-hom' : {x : ob C} → (X : reflection-ob' x) → reflection-hom' (id C) X X
      fromD-id' : {x : ob C} → (X : D ⦅ x ⦆) → fromD-hom' (id C) X X (dC-id D) ≡ id-hom' (fromD-ob' X)
      ⋆-IdL-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (F : reflection-hom' f X Y) →
                   PathP (λ i → reflection-hom' (⋆IdL C f i) X Y) (seq-hom' (id C) f X X Y (id-hom' X) F) F
      ⋆-IdR-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (F : reflection-hom' f X Y) →
                   PathP (λ i → reflection-hom' (⋆IdR C f i) X Y) (seq-hom' f (id C) X Y Y F (id-hom' Y)) F
      ⋆Assoc-hom' : {w x y z : ob C} → (f : C [ w , x ]) → (g : C [ x , y ]) → (h : C [ y , z ]) →
                    (W : reflection-ob' w) → (X : reflection-ob' x) → (Y : reflection-ob' y) → (Z : reflection-ob' z) →
                    (F : reflection-hom' f W X) → (G : reflection-hom' g X Y) →  (H : reflection-hom' h Y Z) →
                    PathP (λ i → reflection-hom' (⋆Assoc C f g h i) W Z)
                          (seq-hom' (f ⋆⟨ C ⟩ g) h W Y Z (seq-hom' f g W X Y F G) H)
                          (seq-hom' f (g ⋆⟨ C ⟩ h) W X Z F (seq-hom' g h X Y Z G H))
      is-set-hom' : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob' x) → (Y : reflection-ob' y) → isSet (reflection-hom' f X Y)

  unicity-id' : {x : ob C} → (X : reflection-ob' x) → leftFib-ob' (id C) X ≡ X
  unicity-id' X = unicity-ob' (id C) X X (id-hom' X)

  reflection' : dispCat C ℓ ℓ
  reflection' .dC-ob = reflection-ob'
  reflection' .dC-hom = reflection-hom'
  reflection' .dC-id = id-hom' _
  reflection' .dC-⋆ = seq-hom' _ _ _ _ _
  reflection' .dC-⋆IdL = ⋆-IdL-hom' _ _ _
  reflection' .dC-⋆IdR = ⋆-IdR-hom' _ _ _
  reflection' .dC-⋆Assoc = ⋆Assoc-hom' _ _ _ _ _ _ _
  reflection' .dC-homSet = is-set-hom'

  fromD : dispCat-Funct D reflection'
  fromD .dF-ob = fromD-ob'
  fromD .dF-hom = fromD-hom' _ _ _
  fromD .dF-id {X = X} = fromD-id' X
  fromD .dF-seq F G = fromD-seq' _ _ _ _ _ F G

  module _ (E : dispCat C ℓD ℓD')
           (isUnivE : isUnivalent-dC E)
           (isLeftFibE : isLeftFibration E)
           (𝑭 : dispCat-Funct D E) where

    mutual
      factorisation-ob : {x : ob C} → reflection' ⦅ x ⦆ → E ⦅ x ⦆
      factorisation-ob  (fromD-ob' X) = 𝑭 ⟅ X ⟆ᴰ
      factorisation-ob  (leftFib-ob' f X) = leftFib-getOb E isLeftFibE f (factorisation-ob X)
      factorisation-ob  (unicity-ob' f X Y F i) = leftFib-unicityOb E isLeftFibE f (factorisation-ob X) ((factorisation-ob Y) , factorisation-hom F) i

      factorisation-hom : {x y : ob C} → {f : C [ x , y ]} → {X : reflection' ⦅ x ⦆} → {Y : reflection' ⦅ y ⦆} → reflection' [ f , X , Y ]ᴰ → E [ f , factorisation-ob X , factorisation-ob Y ]ᴰ
      factorisation-hom (fromD-hom' _ X Y F) = 𝑭 ⟪ F ⟫ᴰ
      factorisation-hom {X = X} (leftFib-hom' _ .X) = leftFib-getHom E isLeftFibE _ (factorisation-ob X)
      factorisation-hom {X = X} {.(unicity-ob' f X Y F i)} (unicity-hom' f X Y F i) = leftFib-unicityHom E isLeftFibE f (factorisation-ob X) (factorisation-ob Y , factorisation-hom F) i
      factorisation-hom {X = X} {Z} (seq-hom' f g .X _ .Z F G) = factorisation-hom F ⋆⟨ E ⟩ᴰ factorisation-hom G
      factorisation-hom {X = .(fromD-ob' X)} {.(fromD-ob' Z)} (fromD-seq' f g X Y Z F G i) = dF-seq 𝑭 F G i
      factorisation-hom {X = X} {.X} (id-hom' .X) = dC-id E
      factorisation-hom {X = .(fromD-ob' X)} {.(fromD-ob' X)} (fromD-id' X i) = dF-id 𝑭 i
      factorisation-hom {X = X} {Y} (⋆-IdL-hom' f X Y F i) = dC-⋆IdL E (factorisation-hom F) i
      factorisation-hom {X = X} {Y} (⋆-IdR-hom' f X Y F i) = dC-⋆IdR E (factorisation-hom F) i
      factorisation-hom {X = .W} {.Z} (⋆Assoc-hom' f g h W X Y Z F G H i) = dC-⋆Assoc E (factorisation-hom F) (factorisation-hom G) (factorisation-hom H) i
      factorisation-hom {X = X} {Y} (is-set-hom' f X Y F G p q i j) = isSet→SquareP {A = λ i j → E [ f , factorisation-ob X , factorisation-ob Y ]ᴰ}
                                                                                     (λ _ _ → dC-homSet E _ _ _) (cong factorisation-hom p) (cong factorisation-hom q) refl refl i j


    factReflection : dispCat-Funct reflection' E
    factReflection .dF-ob = factorisation-ob
    factReflection .dF-hom = factorisation-hom
    factReflection .dF-id = refl
    factReflection .dF-seq F G = refl

    preservLeftFib-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection' ⦅ x ⦆) → leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) ≡ factReflection ⟅ leftFib-ob' f X ⟆ᴰ
    preservLeftFib-ob f X = leftFib-unicityOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) (factReflection ⟅ leftFib-ob' f X ⟆ᴰ , factReflection ⟪ leftFib-hom' f X ⟫ᴰ)

    existFact : (fromD ⋆ᵈᶠ factReflection) ≡ 𝑭
    existFact = eq-dF→≡ (record { eq-dF-ob = λ _ → refl ; eq-dF-hom = λ _ → refl })

    module _ (𝑮 : dispCat-Funct reflection' E)
             (factG : (fromD ⋆ᵈᶠ 𝑮) ≡ 𝑭) where
      mutual
        uniqueFact-ob : {x : ob C} → (X : reflection' ⦅ x ⦆) → 𝑮 ⟅ X ⟆ᴰ ≡ factReflection ⟅ X ⟆ᴰ
        uniqueFact-ob (fromD-ob' X) = cong (_⟅ X ⟆ᴰ) factG
        uniqueFact-ob (leftFib-ob' f X) i = hcomp {φ = i ∨ ~ i} aux (leftFib-getOb E isLeftFibE f (uniqueFact-ob X i))
          where
          p : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ 𝑮 ⟅ leftFib-ob' f X ⟆ᴰ
          p = leftFib-unicityOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ leftFib-ob' f X ⟆ᴰ , 𝑮 ⟪ leftFib-hom' f X ⟫ᴰ)

          q : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ)
          q = cong (leftFib-getOb E isLeftFibE f) (uniqueFact-ob X)

          r : leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) ≡ factReflection ⟅ leftFib-ob' f X ⟆ᴰ
          r = leftFib-unicityOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) (factReflection ⟅ leftFib-ob' f X ⟆ᴰ , factReflection ⟪ leftFib-hom' f X ⟫ᴰ)

          aux : I → Partial (i ∨ ~ i) (dC-ob E _)
          aux j (i = i0) = p j
          aux j (i = i1) = r j

        -- uniqueFact-ob (unicity-ob' f X Y F i) j = test4 j i
        --   where
        --   X' = leftFib-ob' f X
        --   p = sym (leftFib-unicityOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ leftFib-ob' f X ⟆ᴰ , 𝑮 ⟪ leftFib-hom' f X ⟫ᴰ)) ∙
        --       cong (leftFib-getOb E isLeftFibE f) (uniqueFact-ob X) ∙
        --       leftFib-unicityOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) (factReflection ⟅ leftFib-ob' f X ⟆ᴰ , factReflection ⟪ leftFib-hom' f X ⟫ᴰ)
        --  -- p = uniqueFact-ob (leftFib-ob' f X)
        --  -- p = uniqueFact-ob X'
        --   p' = uniqueFact-ob Y
        --   q = cong (λ X → 𝑮 ⟅ X ⟆ᴰ) (unicity-ob' f X Y F)
        --   q' = cong (λ X → factReflection ⟅ X ⟆ᴰ) (unicity-ob' f X Y F)

        --   P = dC-pathToIso reflection' (unicity-ob' f X Y F)
        --   GP : dispCatIso E (𝑮 ⟅ X' ⟆ᴰ) (𝑮 ⟅ Y ⟆ᴰ) idCatIso
        --   GP = dC-pathToIso E q
        --   FP : dispCatIso E (factReflection ⟅ X' ⟆ᴰ) (factReflection ⟅ Y ⟆ᴰ) idCatIso
        --   FP = dC-pathToIso E q'

        --   test : PathP (λ i → E [ id C , p i , p' i ]ᴰ) (𝑮 ⟪ dC-mor P ⟫ᴰ) (factReflection ⟪ dC-mor P ⟫ᴰ)
        --   test = uniqueFact-hom (dC-mor P)

        --   test' : PathP (λ i → E [ id C , p i , p' i ]ᴰ) (dC-mor GP) (dC-mor FP)
        --   test' = subst2 (PathP (λ i → E [ id C , p i , p' i ]ᴰ)) {!!} {!!} test

        --   test2 : PathP (λ i → dispCatIso E (p i) (p' i) idCatIso) GP FP
        --   test2 = makeDispCatIsoPath E p p' GP FP test'

        --   test3 : PathP (λ i → p i ≡ p' i) (equivFun (invEquiv (dC-univEquiv E isUnivE _ _)) GP) (equivFun (invEquiv (dC-univEquiv E isUnivE _ _)) FP)
        --   test3 = equivFun (congPathEquiv (λ _ → invEquiv (dC-univEquiv E isUnivE _ _))) test2

        --   test4 : PathP (λ i → uniqueFact-ob X' i ≡ uniqueFact-ob Y i) q q'
        --   test4 = subst2 (PathP (λ i → p i ≡ p' i)) (retEq (dC-univEquiv E isUnivE _ _) q) (retEq (dC-univEquiv E isUnivE _ _) q')
        --                  (equivFun (congPathEquiv (λ _ → invEquiv (dC-univEquiv E isUnivE _ _))) test2)

        uniqueFact-hom : {x y : ob C} → {f : C [ x , y ]} → {X : reflection' ⦅ x ⦆} → {Y : reflection' ⦅ y ⦆} → (F : reflection' [ f , X , Y ]ᴰ) →
                         PathP (λ i → E [ f , uniqueFact-ob X i , uniqueFact-ob Y i ]ᴰ) (𝑮 ⟪ F ⟫ᴰ) (factReflection ⟪ F ⟫ᴰ)
        uniqueFact-hom {X = .(fromD-ob' X)} {.(fromD-ob' Y)} (fromD-hom' _ X Y F) = cong (_⟪ F ⟫ᴰ) factG
        uniqueFact-hom {x} {y} {f = f} {X = X} {.(leftFib-ob' f X)} (leftFib-hom' _ .X) i = comp
          (λ j → E [ f , uniqueFact-ob X i , hfill {φ = i ∨ ~ i} aux (inS (leftFib-getOb E isLeftFibE f (uniqueFact-ob X i))) j ]ᴰ)
          {φ = i ∨ ~ i}
          (λ j → λ {
            (i = i0) → leftFib-unicityHom E isLeftFibE f (𝑮₀ ⟅ X ⟆ᴰ) ((𝑮₀ ⟅ Y ⟆ᴰ) , (𝑮₀ ⟪ leftFib-hom' f X ⟫ᴰ)) j;
            (i = i1) → leftFib-unicityHom E isLeftFibE f (𝑮₁ ⟅ X ⟆ᴰ) ((𝑮₁ ⟅ Y ⟆ᴰ) , (𝑮₁ ⟪ leftFib-hom' f X ⟫ᴰ)) j}
          )
          ((leftFib-getHom E isLeftFibE f (uniqueFact-ob X i)))
          where
          Y = leftFib-ob' f X

          𝑮₀ = 𝑮
          𝑮₁ = factReflection

          p : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ 𝑮 ⟅ leftFib-ob' f X ⟆ᴰ
          p = leftFib-unicityOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ leftFib-ob' f X ⟆ᴰ , 𝑮 ⟪ leftFib-hom' f X ⟫ᴰ)

          q : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ)
          q = cong (leftFib-getOb E isLeftFibE f) (uniqueFact-ob X)

          r : leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) ≡ factReflection ⟅ leftFib-ob' f X ⟆ᴰ
          r = leftFib-unicityOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) (factReflection ⟅ leftFib-ob' f X ⟆ᴰ , factReflection ⟪ leftFib-hom' f X ⟫ᴰ)

          aux : I → Partial (i ∨ ~ i) (dC-ob E _)
          aux j (i = i0) = p j
          aux j (i = i1) = r j

          z : dC-ob E _
          z = leftFib-getOb E isLeftFibE f (uniqueFact-ob X i)

          α : dC-ob E _
          α = hcomp {A = dC-ob E y} {φ = i ∨ ~ i} aux z

          β : {!!}
          β = hfill {A = dC-ob E y} {φ = i ∨ ~ i} (λ j → λ {(i = i0) → p j; (i = i1) → r j}) (inS z)
        --   test : subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) (p ∙ q ∙ r) (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ) ≡ {!!}
        --   test =
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) (p ∙ q ∙ r) (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ) ≡⟨ {!!} ⟩
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) (q ∙ r) (subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) p (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ)) ≡⟨ {!!} ⟩
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) (q ∙ r) (leftFib-getHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ)) ≡⟨ {!!} ⟩
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) r (subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) q (leftFib-getHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ))) ≡⟨ {!!} ⟩
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) r (subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , leftFib-getOb E isLeftFibE f Y ]ᴰ) (uniqueFact-ob X) (leftFib-getHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ))) ≡⟨ {!!} ⟩
        --     subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) r (subst (λ X' → E [ f , X' , leftFib-getOb E isLeftFibE f (factorisation-ob X) ]ᴰ) (sym (uniqueFact-ob X))
        --                                                   (leftFib-getHom E isLeftFibE f (factReflection ⟅ X ⟆ᴰ))) ≡⟨ {!!} ⟩

        --     subst (λ X' → E [ f , X' , leftFib-getOb E isLeftFibE f (factorisation-ob X) ]ᴰ) (sym (uniqueFact-ob X)) (subst (λ Y → E [ f , factorisation-ob X , Y ]ᴰ) r
        --                                                                                                                    (leftFib-getHom E isLeftFibE f (factReflection ⟅ X ⟆ᴰ))) ≡⟨ {!!} ⟩
        --     subst (λ X' → E [ f , X' , leftFib-getOb E isLeftFibE f (factorisation-ob X) ]ᴰ) (sym (uniqueFact-ob X)) (factReflection ⟪ leftFib-hom' f X ⟫ᴰ) ≡⟨ {!!} ⟩
        --     {!!} ∎

        --   eq : subst2 (λ X Y → E [ f , X , Y ]ᴰ) (uniqueFact-ob X) (p ∙ q ∙ r) (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ) ≡ factReflection ⟪ leftFib-hom' f X ⟫ᴰ
        --   eq =
        --     subst2 (λ X Y → E [ f , X , Y ]ᴰ) (uniqueFact-ob X) (p ∙ q ∙ r) (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ)
        --       ≡⟨ {!!} ⟩
        --     subst (λ X' → E [ f , X' , leftFib-getOb E isLeftFibE f (factorisation-ob X) ]ᴰ) (uniqueFact-ob X) (subst (λ Y → E [ f , 𝑮 ⟅ X ⟆ᴰ , Y ]ᴰ) (p ∙ q ∙ r) (𝑮 ⟪ leftFib-hom' f X ⟫ᴰ))
        --       ≡⟨ {!!} ⟩
        --     {!!} ≡⟨ {!!} ⟩
        --     factReflection ⟪ leftFib-hom' f X ⟫ᴰ ∎


        uniqueFact-hom {X = X} {.(unicity-ob' f X Y F i)} (unicity-hom' f X Y F i) j = {!!} --isSet→SqureP and same for other cases
        uniqueFact-hom {X = X} {Y} (seq-hom' f g .X Y₁ .Y F F₁) j = {!!}
        uniqueFact-hom {X = .(fromD-ob' X)} {.(fromD-ob' Z)} (fromD-seq' f g X Y Z F G i) = {!!}
        uniqueFact-hom {X = X} {.X} (id-hom' .X) = {!!}
        uniqueFact-hom {X = .(fromD-ob' X)} {.(fromD-ob' X)} (fromD-id' X i) = {!!}
        uniqueFact-hom {X = X} {Y} (⋆-IdL-hom' f X Y F i) = {!!}
        uniqueFact-hom {X = X} {Y} (⋆-IdR-hom' f X Y F i) = {!!}
        uniqueFact-hom {X = .W} {.Z} (⋆Assoc-hom' f g h W X Y Z F F₁ F₂ i) = {!!}
        uniqueFact-hom {X = X} {Y} (is-set-hom' f X Y F F₁ x y i i₁) = {!!}
