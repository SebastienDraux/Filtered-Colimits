module Filtered-Colimits.DisplayedCategories.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

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

--module _ {ℓC ℓC' ℓD ℓD' : Level}
--         {C : Category ℓC ℓC'}
 --        (D : dispCat C ℓD ℓD) where

--  private
--    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
         
--  data reflection-ob : (x : ob C) → Type ℓ where
--    fromD-ob : {x : ob C} → (X : D ⦅ x ⦆) → reflection-ob x
 --   leftFib-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → reflection-ob y
 --   coherence-seq : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : reflection-ob x) → leftFib-ob (f ⋆⟨ C ⟩ g) X ≡ leftFib-ob g (leftFib-ob f X)
 --   coherence-fromD : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → leftFib-ob f (fromD-ob X) ≡ fromD-ob Y
--    coherence-id : {x : ob C} → (X : reflection-ob x) → leftFib-ob (id C) X ≡ X
 --   coherence-id-fromD : {x : ob C} → (X : D ⦅ x ⦆) → coherence-id (fromD-ob X) ≡ coherence-fromD (id C) X X (dC-id D)
 --   test2 : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x)  → coherence-id (leftFib-ob f X) ≡ sym (coherence-seq f (id C) X) ∙ cong (λ f → leftFib-ob f X) (⋆IdR C _)
   -- is-set : {x : ob C} → isSet (reflection-ob x)

      
--  data reflection-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → Type ℓ where
--    fromD-hom : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → reflection-hom f (fromD-ob X) (fromD-ob Y)
----    leftFib-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) →  reflection-hom f X (leftFib-ob f X)
 --   coherence-id-hom : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) →
  ----                 PathP (λ i → reflection-hom (id C) (coherence-fromD f X Y F i) (coherence-fromD f X Y F i))
  --                 (subst (reflection-hom (id C) (leftFib-ob f (fromD-ob X)))
 --                         (coherence-id (leftFib-ob f (fromD-ob X)))
  --                        (leftFib-hom (id C) (leftFib-ob f (fromD-ob X))))
  --                 (fromD-hom (id C) Y Y (dC-id D))
   -- coherence-⋆IdL-fromD : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) →
   --                        PathP (λ i → reflection-hom (⋆IdL C f i) (fromD X) ((coherence-seq (id C) f (fromD X) ∙ cong (leftFib-ob f) (coherence-id (fromD X)) ∙ coherence-fromD f X Y F) i))
   --                              (leftFib-hom (id C ⋆⟨ C ⟩ f) (fromD X))
   --                              (fromD f X Y F)
   -- is-prop : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → isProp (reflection-hom f X Y)

 -- unicity-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → reflection-hom f X Y → leftFib-ob f X ≡ Y
--  unicity-ob f .(fromD-ob X) .(fromD-ob Y) (fromD-hom .f X Y F) = coherence-fromD f X Y F
 -- unicity-ob f X .(leftFib-ob f X) (leftFib-hom .f .X) = refl
 -- unicity-ob .(id C) .(coherence-fromD f X Y F i) .(coherence-fromD f X Y F i) (coherence-id-hom f X Y F i) = {!!}
  
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

--  reflection : dispCat C ℓ ℓ
--  reflection .dC-ob = reflection-ob
--  reflection .dC-hom = reflection-hom
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
--  reflection .dC-id {X = X} = subst (λ Y → reflection-hom (id C) X Y) (coherence-id X) (leftFib-hom (id C) X)
--  reflection .dC-⋆ {X = X} {Y} {Z} {f} {g} F G = subst (reflection-hom (f ⋆⟨ C ⟩ g) X) p (leftFib-hom (f ⋆⟨ C ⟩ g) X) 
--    where
--    p : leftFib-ob (f ⋆⟨ C ⟩ g) X ≡ Z
--    p = coherence-seq f g X ∙ cong (leftFib-ob g) (unicity-ob f X Y F) ∙ (unicity-ob g Y Z G)
--  reflection .dC-⋆IdL {X = .(fromD X)} {.(fromD Y)} (fromD _ X Y F) = {!!}
--  reflection .dC-⋆IdL {X = X} {.(leftFib-ob _ X)} (leftFib-hom _ .X) = {!!}
---  reflection .dC-⋆IdL F = {!!}
--  reflection .dC-⋆IdR F = {!!} --is-prop _ _ _ _ _
--  reflection .dC-⋆Assoc F G H = {!!} ---is-prop _ _ _ _ _
--  reflection .dC-homSet f X Y = {!!} --isProp→isSet (is-prop f X Y)

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
    data reflection-ob : (x : ob C) → Type ℓ where
      fromD : {x : ob C} → (X : D ⦅ x ⦆) → reflection-ob x
      leftFib-ob : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → reflection-ob y
      unicity-ob :  {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y Y' : reflection-ob y) → (F : reflection-hom f X Y) → (F' : reflection-hom f X Y') → Y ≡ Y'
       
    data reflection-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → Type ℓ where
      fromD : {x y : ob C} → (f : C [ x , y ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (F : D [ f , X , Y ]ᴰ) → reflection-hom f (fromD X) (fromD Y)
      leftFib-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) →  reflection-hom f X (leftFib-ob f X)
      unicity-hom : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y Y' : reflection-ob y) → (F : reflection-hom f X Y) → (F' : reflection-hom f X Y') → 
                    PathP (λ i → reflection-hom f X (unicity-ob f X Y Y' F F' i)) F F'
      seq : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : reflection-ob x) → (Y : reflection-ob y) → (Z : reflection-ob z) →
            reflection-hom f X Y → reflection-hom g Y Z → reflection-hom (f ⋆⟨ C ⟩ g) X Z
      fromD-seq : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (X : D ⦅ x ⦆) → (Y : D ⦅ y ⦆) → (Z : D ⦅ z ⦆) → (F : D [ f , X , Y ]ᴰ) → (G : D [ g , Y , Z ]ᴰ) →
                   fromD (f ⋆⟨ C ⟩ g) X Z (F ⋆⟨ D ⟩ᴰ G) ≡ seq f g (fromD X) (fromD Y) (fromD Z) (fromD f X Y F) (fromD g Y Z G) 
      refl-id : {x : ob C} → (X : reflection-ob x) → reflection-hom (id C) X X
      fromD-id : {x : ob C} → (X : D ⦅ x ⦆) → fromD (id C) X X (dC-id D) ≡ refl-id (fromD X)
      refl-⋆IdL : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → (F : reflection-hom f X Y) →
                   PathP (λ i → reflection-hom (⋆IdL C f i) X Y) (seq (id C) f X X Y (refl-id X) F) F
      refl-⋆IdR : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → (F : reflection-hom f X Y) →
                   PathP (λ i → reflection-hom (⋆IdR C f i) X Y) (seq f (id C) X Y Y F (refl-id Y)) F
      refl-⋆Assoc : {w x y z : ob C} → (f : C [ w , x ]) → (g : C [ x , y ]) → (h : C [ y , z ]) →
                    (W : reflection-ob w) → (X : reflection-ob x) → (Y : reflection-ob y) → (Z : reflection-ob z) →
                    (F : reflection-hom f W X) → (G : reflection-hom g X Y) →  (H : reflection-hom h Y Z) →
                    PathP (λ i → reflection-hom (⋆Assoc C f g h i) W Z)
                          (seq (f ⋆⟨ C ⟩ g) h W Y Z (seq f g W X Y F G) H)
                          (seq f (g ⋆⟨ C ⟩ h) W X Z F (seq g h X Y Z G H))
      is-set : {x y : ob C} → (f : C [ x , y ]) → (X : reflection-ob x) → (Y : reflection-ob y) → isSet (reflection-hom f X Y)

  reflection : dispCat C ℓ ℓ
  reflection .dC-ob = reflection-ob
  reflection .dC-hom = reflection-hom
  reflection .dC-id = refl-id _
  reflection .dC-⋆ = seq _ _ _ _ _
  reflection .dC-⋆IdL = refl-⋆IdL _ _ _
  reflection .dC-⋆IdR = refl-⋆IdR _ _ _
  reflection .dC-⋆Assoc = refl-⋆Assoc _ _ _ _ _ _ _
  reflection .dC-homSet = is-set

  isLeftFib-Reflection : isLeftFibration reflection
  isLeftFib-Reflection f X = (leftFib-ob f X , leftFib-hom f X) ,
                             λ {(Y , F) → ΣPathP (unicity-ob f X (leftFib-ob f X) Y (leftFib-hom f X) F , unicity-hom f X (leftFib-ob f X) Y (leftFib-hom f X) F)}

  fromD-Funct : dispCat-Funct D reflection
  fromD-Funct .dF-ob = fromD
  fromD-Funct .dF-hom = fromD _ _ _
  fromD-Funct .dF-id {X = X} = fromD-id X
  fromD-Funct .dF-seq = fromD-seq _ _ _ _ _

  module _ (E : dispCat C ℓD ℓD')
           (isUnivE : isUnivalent-dC E)
           (isLeftFibE : isLeftFibration E)
           (𝑭 : dispCat-Funct D E) where

    factorisation-ob : {x : ob C} → reflection ⦅ x ⦆ → E ⦅ x ⦆
    factorisation-hom : {x y : ob C} → {f : C [ x , y ]} → {X : reflection ⦅ x ⦆} → {Y : reflection ⦅ y ⦆} → reflection [ f , X , Y ]ᴰ → E [ f , factorisation-ob X , factorisation-ob Y ]ᴰ
      
    factorisation-ob  (fromD X) = 𝑭 ⟅ X ⟆ᴰ
    factorisation-ob  (leftFib-ob f X) = leftFib-getOb E isLeftFibE f (factorisation-ob X)
    factorisation-ob  (unicity-ob f X Y Y' F F' i) = cong fst (isContr→isProp (isLeftFibE f (factorisation-ob X))
                                                                               (factorisation-ob Y , factorisation-hom F) (factorisation-ob Y' , (factorisation-hom F'))) i

    factorisation-hom (fromD _ X Y F) = 𝑭 ⟪ F ⟫ᴰ
    factorisation-hom {X = X} (leftFib-hom _ .X) = leftFib-getHom E isLeftFibE _ (factorisation-ob X)
    factorisation-hom {X = X} {.(unicity-ob f X Y Y' F F' i)} (unicity-hom f X Y Y' F F' i) =
                         cong snd (isContr→isProp (isLeftFibE f (factorisation-ob X)) (factorisation-ob Y , factorisation-hom F) (factorisation-ob Y' , (factorisation-hom F'))) i
    factorisation-hom {X = X} {Z} (seq f g .X _ .Z F G) = factorisation-hom F ⋆⟨ E ⟩ᴰ factorisation-hom G
    factorisation-hom {X = .(fromD X)} {.(fromD Z)} (fromD-seq f g X Y Z F G i) = dF-seq 𝑭 F G i
    factorisation-hom {X = X} {.X} (refl-id .X) = dC-id E
    factorisation-hom {X = .(fromD X)} {.(fromD X)} (fromD-id X i) = dF-id 𝑭 i
    factorisation-hom {X = X} {Y} (refl-⋆IdL f X Y F i) = dC-⋆IdL E (factorisation-hom F) i
    factorisation-hom {X = X} {Y} (refl-⋆IdR f X Y F i) = dC-⋆IdR E (factorisation-hom F) i
    factorisation-hom {X = .W} {.Z} (refl-⋆Assoc f g h W X Y Z F G H i) = dC-⋆Assoc E (factorisation-hom F) (factorisation-hom G) (factorisation-hom H) i
    factorisation-hom {X = X} {Y} (is-set f X Y F G p q i j) = isSet→SquareP {A = λ i j → E [ f , factorisation-ob X , factorisation-ob Y ]ᴰ}
                                                                              (λ _ _ → dC-homSet E _ _ _) (cong factorisation-hom p) (cong factorisation-hom q) refl refl i j

    factReflection : dispCat-Funct reflection E
    factReflection .dF-ob = factorisation-ob
    factReflection .dF-hom = factorisation-hom
    factReflection .dF-id = refl
    factReflection .dF-seq F G = refl

    fact-factReflection : (fromD-Funct ⋆ᵈᶠ factReflection) ≡ 𝑭
    fact-factReflection = eq-dF→≡ (record { eq-dF-ob = λ _ → refl ; eq-dF-hom = λ _ → refl })

    module _ (𝑮 : dispCat-Funct reflection E)
             (factG : (fromD-Funct ⋆ᵈᶠ 𝑮) ≡ 𝑭) where
             
     -- {-# TERMINATING #-}
      
      uniqueFact-ob : {x : ob C} → (X : reflection ⦅ x ⦆) → factReflection ⟅ X ⟆ᴰ ≡ 𝑮 ⟅ X ⟆ᴰ
      uniqueFact-hom : {x y : ob C} → {f : C [ x , y ]} → (X : reflection ⦅ x ⦆) → (Y : reflection ⦅ y ⦆) → (F : reflection [ f , X , Y ]ᴰ) →
                       PathP (λ i → E [ f , uniqueFact-ob X i , uniqueFact-ob Y i ]ᴰ) (factReflection ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)    

      uniqueFact-ob (fromD X) = cong (_⟅ X ⟆ᴰ) (sym factG)
      uniqueFact-ob (leftFib-ob f X) = q ∙ p
        where
        X' = leftFib-ob f X
          
        p : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ 𝑮 ⟅ X' ⟆ᴰ
        p = leftFib-unicityOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ X' ⟆ᴰ , 𝑮 ⟪ leftFib-hom f X ⟫ᴰ)

        q :  leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) ≡ leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ)
        q = cong (leftFib-getOb E isLeftFibE f) (uniqueFact-ob X)

      uniqueFact-ob (unicity-ob f X Y Y' F F' i) j = {!!} --path-≡ j i
        where
        p₀ = uniqueFact-ob X
        p = uniqueFact-ob Y
        p' = uniqueFact-ob Y'
        
        q = cong (factReflection ⟅_⟆ᴰ) (unicity-ob f X Y Y' F F')
        q' = cong (𝑮 ⟅_⟆ᴰ) (unicity-ob f X Y Y' F F')

        path-p : PathP (λ i → E [ f ,  p₀ i , p i ]ᴰ) (factReflection ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)
        path-p = uniqueFact-hom X Y F

        path-q : PathP (λ i → E [ f , factReflection ⟅ X ⟆ᴰ , q i ]ᴰ) (factReflection ⟪ F ⟫ᴰ) (factReflection ⟪ F' ⟫ᴰ)
        path-q = congP (λ i F → factReflection ⟪ F ⟫ᴰ) (unicity-hom f X Y Y' F F')

        path-p' : PathP (λ i → E [ f ,  p₀ i , p' i ]ᴰ) (factReflection ⟪ F' ⟫ᴰ) (𝑮 ⟪ F' ⟫ᴰ)
        path-p' = uniqueFact-hom X Y' F'

        path-q' : PathP (λ i → E [ f , 𝑮 ⟅ X ⟆ᴰ , (sym q') i ]ᴰ) (𝑮 ⟪ F' ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)
        path-q' = congP (λ i F → 𝑮 ⟪ F ⟫ᴰ) (symP (unicity-hom f X Y Y' F F'))

        path : PathP (λ i → E [ f ,  p₀ i , (q ∙ p' ∙ sym q') i ]ᴰ) (factReflection ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)
        path = {!!}

        goal : q ∙ p' ∙ sym q' ≡ p
        goal = cong (λ P → fst (PathPΣ P)) (isProp→isSet (isContr→isProp (isLeftFibE f (factReflection ⟅ X ⟆ᴰ)))
               (factReflection ⟅ Y ⟆ᴰ , factReflection ⟪ F ⟫ᴰ) (𝑮 ⟅ Y ⟆ᴰ , subst (λ X → E [ f , X , 𝑮 ⟅ Y ⟆ᴰ ]ᴰ) (sym p₀) (𝑮 ⟪ F ⟫ᴰ))
                 (ΣPathP (q ∙ p' ∙ sym q' , {!!})) (ΣPathP (p , {!!})))
         
      uniqueFact-hom .(fromD X) .(fromD Y) (fromD _ X Y F) = cong (_⟪ F ⟫ᴰ) (sym factG)
      uniqueFact-hom {f = f} X .(leftFib-ob f X) (leftFib-hom f .X) =
        subst (λ r → PathP (λ i → E [ f , r i , (q ∙ p) i ]ᴰ) (factReflection ⟪ F ⟫ᴰ) (𝑮 ⟪ F ⟫ᴰ)) (sym (rUnit r))
              (compPathP₂ (λ X Y → E [ f , X , Y ]ᴰ) r refl q p path1 path2)
        where
        Y = leftFib-ob f X
        F = leftFib-hom f X

        p : leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) ≡ 𝑮 ⟅ Y ⟆ᴰ
        p = leftFib-unicityOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ Y ⟆ᴰ , 𝑮 ⟪ F ⟫ᴰ)

        r : factReflection ⟅ X ⟆ᴰ ≡ 𝑮 ⟅ X ⟆ᴰ 
        r = uniqueFact-ob X

        q : leftFib-getOb E isLeftFibE f (factReflection ⟅ X ⟆ᴰ) ≡ leftFib-getOb E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ)
        q = cong (leftFib-getOb E isLeftFibE f) r

        path1 : PathP (λ i → E [ f , r i , q i ]ᴰ) (leftFib-getHom E isLeftFibE f (factReflection ⟅ X ⟆ᴰ)) (leftFib-getHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ)) 
        path1 = congP (λ _ → leftFib-getHom E isLeftFibE f) r
        
        path2 : PathP (λ i → E [ f , 𝑮 ⟅ X ⟆ᴰ , p i ]ᴰ) (leftFib-getHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ)) (𝑮 ⟪ F ⟫ᴰ)
        path2 = leftFib-unicityHom E isLeftFibE f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ Y ⟆ᴰ , 𝑮 ⟪ F ⟫ᴰ)
          
      uniqueFact-hom X .(unicity-ob f X Y Y' F F' i) (unicity-hom f X Y Y' F F' i) = 
        isSet→SquareP {A = λ i j → E [ f , uniqueFact-ob X j , uniqueFact-ob (unicity-ob f X Y Y' F F' i) j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ F) (uniqueFact-hom _ _ F')
                       (λ i → factReflection ⟪ unicity-hom f X Y Y' F F' i ⟫ᴰ) (λ i → 𝑮 ⟪ unicity-hom f X Y Y' F F' i ⟫ᴰ) i
      uniqueFact-hom X Z (seq f g .X Y .Z F G) = {!!}
     --   subst2 (λ F G → PathP (λ i → E [ f ⋆⟨ C ⟩ g , uniqueFact-ob X i , uniqueFact-ob Z i ]ᴰ) F G) (sym (dF-seq factReflection F G)) (sym (dF-seq 𝑮 F G))
     --           λ i → uniqueFact-hom X Y F i ⋆⟨ E ⟩ᴰ uniqueFact-hom Y Z G i
      uniqueFact-hom .(fromD X) .(fromD Z) (fromD-seq f g X Y Z F G i) j =
        isSet→SquareP {A = λ i j → E [ f ⋆⟨ C ⟩ g , uniqueFact-ob (fromD X) j , uniqueFact-ob (fromD Z) j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ (fromD (f ⋆⟨ C ⟩ g) X Z (F ⋆⟨ D ⟩ᴰ G)))
                       (uniqueFact-hom _ _ (seq f g (fromD X) (fromD Y) (fromD Z) (fromD f X Y F) (fromD g Y Z G)))
                       (λ i → factReflection ⟪ fromD-seq f g X Y Z F G i ⟫ᴰ) (λ i → 𝑮 ⟪ fromD-seq f g X Y Z F G i ⟫ᴰ) i j
      uniqueFact-hom X .X (refl-id .X) =
        subst2 (λ F G → PathP (λ i → E [ id C , uniqueFact-ob X i , uniqueFact-ob X i ]ᴰ) F G) (sym (dF-id factReflection {X = X})) (sym (dF-id 𝑮)) λ i → dC-id E 
      uniqueFact-hom .(fromD X) .(fromD X) (fromD-id X i) j =
        isSet→SquareP {A = λ i j → E [ id C , uniqueFact-ob (fromD X) j , uniqueFact-ob (fromD X) j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ (fromD (id C) X X (dC-id D))) (uniqueFact-hom _ _ (refl-id (fromD X)))
                       (λ i → factReflection ⟪ fromD-id X i ⟫ᴰ) (λ i → 𝑮 ⟪ fromD-id X i ⟫ᴰ) i j
      uniqueFact-hom X Y (refl-⋆IdL f X Y F i) j =
        isSet→SquareP {A = λ i j → E [ ⋆IdL C f i , uniqueFact-ob X j , uniqueFact-ob Y j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ (seq (id C) f X X Y (refl-id X) F)) (uniqueFact-hom _ _ F)
                       (λ i → factReflection ⟪ refl-⋆IdL f X Y F i ⟫ᴰ) (λ i → 𝑮 ⟪ refl-⋆IdL f X Y F i ⟫ᴰ) i j
      uniqueFact-hom X Y (refl-⋆IdR f X Y F i) j =
        isSet→SquareP {A = λ i j → E [ ⋆IdR C f i , uniqueFact-ob X j , uniqueFact-ob Y j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ (seq f (id C) X Y Y F (refl-id Y))) (uniqueFact-hom _ _ F)
                       (λ i → factReflection ⟪ refl-⋆IdR f X Y F i ⟫ᴰ) (λ i → 𝑮 ⟪ refl-⋆IdR f X Y F i ⟫ᴰ) i j
      uniqueFact-hom .W .Z (refl-⋆Assoc f g h W X Y Z F G H i) j =
        isSet→SquareP {A = λ i j → E [ ⋆Assoc C f g h i , uniqueFact-ob W j , uniqueFact-ob Z j ]ᴰ} (λ _ _ → dC-homSet E _ _ _)
                       (uniqueFact-hom _ _ (seq (f ⋆⟨ C ⟩ g) h W Y Z (seq f g W X Y F G) H)) (uniqueFact-hom _ _ (seq f (g ⋆⟨ C ⟩ h) W X Z F (seq g h X Y Z G H)))
                       (λ i → factReflection ⟪ refl-⋆Assoc f g h W X Y Z F G H i ⟫ᴰ) (λ i → 𝑮 ⟪ refl-⋆Assoc f g h W X Y Z F G H i ⟫ᴰ) i j
      uniqueFact-hom X Y (is-set f X Y F G p q i j) k =
        isSet→SquareP {A = λ j k → uniqueFact-hom _ _ (p j) k ≡ uniqueFact-hom _ _ (q j) k} (λ _ _ → isProp→isSet (dC-homSet E _ _ _ _ _))
                       (λ k → refl) (λ k → refl) (λ j i → factReflection ⟪ is-set f X Y F G p q i j ⟫ᴰ) (λ j i → 𝑮 ⟪ is-set f X Y F G p q i j ⟫ᴰ) j k i

      unique-dF : factReflection ≡ 𝑮
      unique-dF = eq-dF→≡ (record { eq-dF-ob = uniqueFact-ob ; eq-dF-hom = λ F → uniqueFact-hom _ _ F })

   -- uniqueFact : ∃![ 𝑮 ∈ dispCat-Funct reflection E ] (fromD-Funct ⋆ᵈᶠ 𝑮 ≡ 𝑭)
   -- uniqueFact = (factReflection , fact-factReflection) , λ {(𝑮 , fact) → ΣPathP (unique-dF 𝑮 fact , compPathL→PathP (assoc _ _ _ ∙ sym (rUnit _) ∙ eq 𝑮 fact))}
   --   where
   --   eq : (𝑮 : dispCat-Funct reflection E) → (fact : fromD-Funct ⋆ᵈᶠ 𝑮 ≡ 𝑭) → sym (cong (fromD-Funct ⋆ᵈᶠ_) (unique-dF 𝑮 fact)) ∙ fact-factReflection ≡ fact
   --   eq 𝑮 fact = ≡-≡-dF (sym p ∙ fact-factReflection) fact
   --                         (λ X → cong-∙ (_⟅ X ⟆ᴰ) (sym p) fact-factReflection ∙ sym (rUnit (cong (_⟅ X ⟆ᴰ) (sym p))))
    --    where
   --     p = cong (fromD-Funct ⋆ᵈᶠ_) (unique-dF 𝑮 fact)
        
