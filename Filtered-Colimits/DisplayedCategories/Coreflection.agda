module Filtered-Colimits.DisplayedCategories.Coreflection where

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



module _ {ℓC ℓC' ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispCat C ℓD ℓD) where
         
  --private
  --  ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

  data coreflection-ob (x : ob C) : Type {!!} where
    fromFunct : {ℓE ℓE' : Level} → (E : dispCat C ℓE ℓE') → (isLeftFibE : isLeftFibration E) → (𝑭 : dispCat-Funct E D) → (X : E ⦅ x ⦆) → coreflection-ob x
    coherence : {ℓE ℓE' ℓE1 ℓE1' : Level} → (E : dispCat C ℓE ℓE') → (E' : dispCat C ℓE1 ℓE1') → (isLeftFibE : isLeftFibration E) → (isLeftFibE' : isLeftFibration E') →
                (𝑭 : dispCat-Funct E D) → (𝑭' : dispCat-Funct E' D) → (𝑮 : dispCat-Funct E E') → 𝑮 ⋆ᵈᶠ 𝑭' ≡ 𝑭 → (X : E ⦅ x ⦆) →
                fromFunct E isLeftFibE 𝑭 X ≡ fromFunct E' isLeftFibE' 𝑭' (𝑮 ⟅ X ⟆ᴰ)
    
  data coreflection-hom : {x y : ob C} (f : C [ x , y ]) (X : coreflection-ob x) (Y : coreflection-ob y) → Type {!!} where
    fromFunct : {ℓE ℓE' : Level} → (E : dispCat C ℓE ℓE') → (isLeftFibE : isLeftFibration E) → (𝑭 : dispCat-Funct E D) → {x y : ob C} → (f : C [ x , y ]) → (X : E ⦅ x ⦆) → (Y : E ⦅ y ⦆) →
                (F : E [ f , X , Y ]ᴰ) →  coreflection-hom f (fromFunct E isLeftFibE 𝑭 X) (fromFunct E isLeftFibE 𝑭 Y)
    --coherence : {ℓE ℓE' ℓE1 ℓE1' : Level} → {E : dispCat C ℓE ℓE'} → {E' : dispCat C ℓE1 ℓE1'} → (isLeftFibE : isLeftFibration E) → (isLeftFibE' : isLeftFibration E') →
    --            (𝑭 : dispCat-Funct E D) → (𝑭' : dispCat-Funct E' D) → {x y : ob C} → (f : C [ x , y ])→ (X : E ⦅ x ⦆) → (X' : E' ⦅ x ⦆) →
    --            ((p , path) : Σ[ p ∈ ({y : ob C} → (f : C [ x , y ]) → 𝑭 ⟅ leftFib-getOb E isLeftFibE f X ⟆ᴰ ≡ 𝑭' ⟅ leftFib-getOb E' isLeftFibE' f X' ⟆ᴰ) ]
    --            ({y z : ob C} → {f : C [ x , y ]} → {g : C [ y , z ]} →
    --            PathP (λ i → D [ g , p f i , (cong (𝑭 ⟅_⟆ᴰ) (sym (leftFib-seq E isLeftFibE f g X)) ∙ p (f ⋆⟨ C ⟩ g) ∙ cong (𝑭' ⟅_⟆ᴰ) (leftFib-seq E' isLeftFibE' f g X')) i ]ᴰ)
     --           (𝑭 ⟪ leftFib-getHom E isLeftFibE g (leftFib-getOb E isLeftFibE f X) ⟫ᴰ) (𝑭' ⟪ leftFib-getHom E' isLeftFibE' g (leftFib-getOb E' isLeftFibE' f X') ⟫ᴰ))) →
    --            PathP (λ i → coreflection-hom f (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X' (p , path) i)
    --                  (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' (leftFib-getOb E isLeftFibE f X) (leftFib-getOb E' isLeftFibE' f X')
    --                  ((λ g → cong (𝑭 ⟅_⟆ᴰ) (sym (leftFib-seq E isLeftFibE f g X)) ∙ p (f ⋆⟨ C ⟩ g) ∙ cong (𝑭' ⟅_⟆ᴰ) (leftFib-seq E' isLeftFibE' f g X')) ,
    --                  compPathP₂ (λ X Y → D [ _ , X , Y ]ᴰ) _ _ _ _ {!!} {!!}) i)) {!!} {!!}
                  --(fromFunct isLeftFibE 𝑭 f X (leftFib-getOb E isLeftFibE f X)) (fromFunct isLeftFibE' 𝑭' f X' (leftFib-getOb E' isLeftFibE' f X'))
    coherence : {ℓE ℓE' ℓE1 ℓE1' : Level} → (E : dispCat C ℓE ℓE') → (E' : dispCat C ℓE1 ℓE1') → (isLeftFibE : isLeftFibration E) → (isLeftFibE' : isLeftFibration E') →
                (𝑭 : dispCat-Funct E D) → (𝑭' : dispCat-Funct E' D) → (𝑮 : dispCat-Funct E E') → (p : 𝑮 ⋆ᵈᶠ 𝑭' ≡ 𝑭) → {x y : ob C} → (f : C [ x , y ]) → (X : E ⦅ x ⦆) → (Y : E ⦅ y ⦆) →
                (F : E [ f , X , Y ]ᴰ) → 
                PathP (λ i → coreflection-hom f (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X i)
                                                 (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p Y i))
                                                 (fromFunct E isLeftFibE 𝑭 f X Y F) (fromFunct E' isLeftFibE' 𝑭' f (𝑮 ⟅ X ⟆ᴰ) (𝑮 ⟅ Y ⟆ᴰ) (𝑮 ⟪ F ⟫ᴰ))
                --PathP (λ i → coreflection-hom f (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X i)
                  --                               (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X) i))
                    ---                             (fromFunct E isLeftFibE 𝑭 f X) {!!} --(fromFunct E' isLeftFibE' 𝑭' f (𝑮 ⟅ X ⟆ᴰ))


  test : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → Σ[ Y ∈ coreflection-ob y ] (coreflection-hom f X Y)
  test f (fromFunct E isLeftFibE 𝑭 X) = (fromFunct E isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X)) ,
                                        (fromFunct E isLeftFibE 𝑭 f X (leftFib-getOb E isLeftFibE f X) (leftFib-getHom E isLeftFibE f X))
  test f (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X i) =  (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X) ∙
                                                                   cong (fromFunct E' isLeftFibE' 𝑭') (sym (preservLeftFib-ob 𝑮 isLeftFibE isLeftFibE' f X))) i , {!!}
    where
    q : fromFunct E isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) ≡ fromFunct E' isLeftFibE' 𝑭' (𝑮 ⟅ leftFib-getOb E isLeftFibE f X ⟆ᴰ)
    q = coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X)

 -- test : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → Σ[ Y ∈ coreflection-ob y ] (coreflection-hom f X Y)
--  test f (fromFunct E isLeftFibE 𝑭 X) = fromFunct E isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) , fromFunct E isLeftFibE 𝑭 f X
  --test f (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X X' i) = coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X) (leftFib-getOb E' isLeftFibE' f X') i ,
  --                                                                          coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p f X X' i
                                                                            
 -- test' : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → (Y : coreflection-ob y) → (F : coreflection-hom f X Y) → fst (test f X) ≡ Y
 -- test' f .(fromFunct E isLeftFibE 𝑭 X) .(fromFunct E isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X)) (fromFunct E isLeftFibE 𝑭 .f X) = refl
--  test' f .(coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X X' i) .(coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X) (leftFib-getOb E' isLeftFibE' f X') i) (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p .f X X' i) = refl


--  test'' : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → (Y : coreflection-ob y) → (F : coreflection-hom f X Y) → PathP (λ i → coreflection-hom f X (test' f X Y F i)) (snd (test f X)) F
--  test'' f .(fromFunct E isLeftFibE 𝑭 X) .(fromFunct E isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X)) (fromFunct E isLeftFibE 𝑭 .f X) = refl
 -- test'' f .(coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p X X' i) .(coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p (leftFib-getOb E isLeftFibE f X) (leftFib-getOb E' isLeftFibE' f X') i) (coherence E E' isLeftFibE isLeftFibE' 𝑭 𝑭' 𝑮 p .f X X' i) = refl
  
--  test : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → Σ[ Y ∈ coreflection-ob y ] (coreflection-hom f X Y)
--  test f (fromFunct {E = E} isLeftFibE 𝑭 X) = fromFunct isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) , fromFunct isLeftFibE 𝑭 f X
--  test {w} {x} f (coherence {E = E} {E'} isLeftFibE isLeftFibE' 𝑭 𝑭' W W' (p , path) i) = p' i , {!!}
--    where
--    X = leftFib-getOb E isLeftFibE f W
--    X' = leftFib-getOb E' isLeftFibE' f W'

--    q : {y : ob C} → (g : C [ x , y ]) → 𝑭 ⟅ leftFib-getOb E isLeftFibE g X ⟆ᴰ ≡ 𝑭' ⟅ leftFib-getOb E' isLeftFibE' g X' ⟆ᴰ
--    q g = {!!}

--    p' : fromFunct isLeftFibE 𝑭 X ≡ fromFunct isLeftFibE' 𝑭' X'
--    p' = coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X' (q , {!!})

--  test : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → Σ[ Y ∈ coreflection-ob y ] (coreflection-hom f X Y)
--  test f (fromFunct {E = E} isLeftFibE 𝑭 X) = fromFunct isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) , fromFunct isLeftFibE 𝑭 f X
--  test {w} {x} f (coherence {E = E} {E'} isLeftFibE isLeftFibE' 𝑭 𝑭' W W' (p , p-assoc , path) i) = p' i , {!!}
 -- test f (fromFunct {E = E} isLeftFibE 𝑭 X) = fromFunct isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) , fromFunct isLeftFibE 𝑭 f X
--  test {w} {x} f (coherence {E = E} {E'} isLeftFibE isLeftFibE' 𝑭 𝑭' W W' (p , path) i) =
 --      p' i , coherence (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' W W' (p , path)) p' (fromFunct isLeftFibE 𝑭 f W) (fromFunct isLeftFibE' 𝑭' f W') i
    --where
 --   q : {y : ob C} → (g : C [ x , y ]) → 𝑭 ⟅ leftFib-getOb E isLeftFibE g (leftFib-getOb E isLeftFibE f W) ⟆ᴰ ≡ 𝑭' ⟅ leftFib-getOb E' isLeftFibE' g (leftFib-getOb E' isLeftFibE' f W') ⟆ᴰ
 --   q g = cong (𝑭 ⟅_⟆ᴰ) (sym (leftFib-seq E isLeftFibE f g W)) ∙ p (f ⋆⟨ C ⟩ g) ∙ cong (𝑭' ⟅_⟆ᴰ) (leftFib-seq E' isLeftFibE' f g W')

 --   X = leftFib-getOb E isLeftFibE f W
 --   X' = leftFib-getOb E' isLeftFibE' f W'
--    F = leftFib-getHom E isLeftFibE f W
--    F' = leftFib-getHom E' isLeftFibE' f W'

 --   test2 : {y z : ob C} → {g : C [ x , y ]} → {h : C [ y , z ]} → {Y : E ⦅ y ⦆} → {Y' : E' ⦅ y ⦆} → {Z : E ⦅ z ⦆} → {Z' : E' ⦅ z ⦆} →
 --           (G : E [ g , X , Y ]ᴰ) → (G' : E' [ g , X' , Y' ]ᴰ) → (H : E [ h , Y , Z ]ᴰ) → (H' : E' [ h , Y' , Z' ]ᴰ) →
--           
--            PathP (λ i → D [ h , p (F ⋆⟨ E ⟩ᴰ G) (F' ⋆⟨ E' ⟩ᴰ G') i , p (F ⋆⟨ E ⟩ᴰ (G ⋆⟨ E ⟩ᴰ H)) (F' ⋆⟨ E' ⟩ᴰ (G' ⋆⟨ E' ⟩ᴰ H')) i ]ᴰ) (𝑭 ⟪ H ⟫ᴰ) (𝑭' ⟪ H' ⟫ᴰ)

--    test2 {h = h} G G' H H' = subst (λ q → PathP (λ i → D [ h , p (F ⋆⟨ E ⟩ᴰ G) (F' ⋆⟨ E' ⟩ᴰ G') i , q i ]ᴰ) (𝑭 ⟪ H ⟫ᴰ) (𝑭' ⟪ H' ⟫ᴰ)) p-assoc (path (F ⋆⟨ E ⟩ᴰ G) (F' ⋆⟨ E' ⟩ᴰ G') H H')

    
            
  --  p' : fromFunct isLeftFibE 𝑭 X ≡ fromFunct isLeftFibE' 𝑭' X'
   -- p' = coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X'
 --        ((λ G G' → p (F ⋆⟨ E ⟩ᴰ G) (F' ⋆⟨ E' ⟩ᴰ G')) , {!!} , test2)
     


  --test' : {x y : ob C} → (f : C [ x , y ]) → (X : coreflection-ob x) → (Y : coreflection-ob y) → (F : coreflection-hom f X Y) → Y ≡ fst (test f X)
  --test' f .(fromFunct isLeftFibE 𝑭 X) .(fromFunct isLeftFibE 𝑭 (leftFib-getOb _ isLeftFibE f X)) (fromFunct isLeftFibE 𝑭 .f X) = refl
  --test' f (fromFunct isLeftFibE 𝑭 X) .(q i) (coherence q F F₁ i) = {!!}
--  test' f (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X' x i₁) .(q i) (coherence q F F₁ i) j = {!!}
  --  where
 --   test''' : PathP {!!} {!!} {!!}
 -- 
  --test f (fromFunct {E = E} isLeftFibE 𝑭 X) = (fromFunct isLeftFibE 𝑭 (leftFib-getOb E isLeftFibE f X) , fromFunct isLeftFibE 𝑭 f X) ,
  --                  λ { (fromFunct isLeftFibE' 𝑭' Y , F) → ΣPathP ((coherence isLeftFibE isLeftFibE' 𝑭 𝑭' (leftFib-getOb E isLeftFibE f X) Y
 --                   ((λ g → {!!}) , {!!})) , {!!}) ; (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X' x i , F) → {!!}}
--  test f (coherence isLeftFibE isLeftFibE' 𝑭 𝑭' X X' (p , path) i) = ({!!} , {!!}) , {!!}
--
