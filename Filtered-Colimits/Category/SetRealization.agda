module Filtered-Colimits.Category.SetRealization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Categories.Category

open Category

module _ {ℓC ℓC' : Level}
         (C : Category ℓC ℓC') where

  data setRealization : Type (ℓ-max ℓC ℓC') where
    η : ob C → setRealization
    eq : {x y : ob C} → C [ x , y ] → η x ≡ η y
    is-set : isSet setRealization

  data R' : (x' y' : setRealization) → Type (ℓ-max ℓC ℓC') where
    gen : {x y : ob C} → C [ x , y ] → R' (η x) (η y)
    is-trans : {x' y' z' : setRealization} → R' x' y' → R' y' z' → R' x' z'
    is-prop : {x' y' : setRealization} → isProp (R' x' y')

  isRefl-R' : (x' : setRealization) → R' x' x'
  isRefl-R' (η x) = gen (id C)
  isRefl-R' (eq u i) = isProp→PathP {B = λ i → R' (eq u i) (eq u i)} (λ i → is-prop) (gen (id C)) (gen (id C)) i
  isRefl-R' (is-set x' y' p q i j) = isSet→SquareP {A = λ i j → R' (is-set x' y' p q i j) (is-set x' y' p q i j)} (λ i j → isProp→isSet is-prop)
                                                    (λ j → isRefl-R' (p j)) (λ j → isRefl-R' (q j)) (λ i → isRefl-R' x') (λ i → isRefl-R' y') i j

  ≡→R' : {x' y' : setRealization} → x' ≡ y' → R' x' y'
  ≡→R' {x'} {y'} p = subst (λ y' → R' x' y') p (isRefl-R' x')

  R'→≡ : {x' y' : setRealization} → R' x' y' → x' ≡ y'
  R'→≡ (gen u) = eq u
  R'→≡ (is-trans r r') = R'→≡ r ∙ R'→≡ r'
  R'→≡ (is-prop r r' i) = is-set _ _ (R'→≡ r) (R'→≡ r') i

  data R : ℕ → ob C → ob C → Type (ℓ-max ℓC ℓC') where
    is-refl : {x : ob C} → R 0 x x
    trans1 : {x y z : ob C} → {n : ℕ} → R n x y → C [ y , z ] → R (suc n) x z
    trans2 : {x y z : ob C} → {n : ℕ} → R n x y → C [ z , y ] → R (suc n) x z

 -- R→R' : {x y : ob C} → R x y → R' (η x) (η y)
--  R→R' (gen u) = gen u
 -- R→R' (trans r r') = trans (R→R' r) (R→R' r')
--  R→R' (is-prop r r' i) = is-prop (R→R' r) (R→R' r') i

--  R'→R : {x y : ob C} → R' (η x) (η y) → R x y
--  R'→R r = {!!}

--  R→≡ : {x y : ob C} → R x y → η x ≡ η y
--  R→≡ (gen u) = eq u
--  R→≡ (trans r r') = R→≡ r ∙ R→≡ r'
--  R→≡ (is-prop r r' i) = is-set _ _ (R→≡ r) (R→≡ r') i

----  isRefl-R : (x : ob C) → R x x
--  isRefl-R x = gen (id C)

--  ≡→R : {x y : ob C} → η x ≡ η y → R x y
--  ≡→R p = {!!}


--  mutual
--    Cover : (x' y' : setRealization) → Type (ℓ-max ℓC ℓC')
--    is-prop-cover : (x' y' : setRealization) → isProp (Cover x' y')


 --   Cover (η x) (η y) = R x y
 --   Cover (η x) (eq {y} {y'} u i) = ua (propBiimpl→Equiv is-prop is-prop Rxy→Rxy' Rxy'→Rxy) i
 --     where
 ----     Rxy→Rxy' : R x y → R x y'
--      Rxy→Rxy' r = is-trans r (gen u)
--
 --     Rxy'→Rxy  : R x y' → R x y
 --     Rxy'→Rxy r = is-trans r (is-sym (gen u))
    
 --   Cover (η x) (is-set y y' p q i j) = {!!} --isSet→SquareP {A = λ i j → Type (ℓ-max ℓC ℓC')} {!!}
--                                      --(λ j → Cover (η x) (p j)) (λ j → Cover (η x) (q j)) (λ i → Cover (η x) y) (λ i → Cover (η x) y') i j
  --    where
 --     p≡q = is-set y y' p q
    

  --    test : isProp (Cover (η x) y ≃ Cover (η x) y')
   --   test = {!!}
    
    --isSet→SquareP {!!} (λ j → Cover (η x) (p j)) (λ j → Cover (η x) (q j)) (λ i → Cover (η x) y) (λ i → Cover (η x) y') i j
  --  Cover (eq u i) y' = {!!} --Cover y' (eq u i)
 --   Cover (is-set x x' p q i j) y' = {!!} --Cover y' (is-set x x' p q i j)

  --  is-prop-cover (η x) (η y) = is-prop
  --  is-prop-cover (η x) (eq {y} {y'} u i) = isProp→PathP {B = λ i → isProp (Cover (η x) (eq u i))} (λ i → isPropIsProp)
  --                                                        (is-prop-cover (η x) (η y)) (is-prop-cover (η x) (η y')) i
 --   is-prop-cover (η x) (is-set y y' p q i j) = isSet→SquareP {A = λ i j → isProp (Cover (η x) (is-set y y' p q i j))} (λ i j → isProp→isSet isPropIsProp)
  --                                                             (λ j → is-prop-cover (η x) (p j)) (λ j → is-prop-cover (η x) (q j)) refl refl i j
  --  is-prop-cover (eq {x} {x'} u i) (η y) = isProp→PathP {B = λ i → isProp (Cover (eq u i) (η y))} (λ i → isPropIsProp)
 --                                                         (is-prop-cover (η x) (η y)) (is-prop-cover (η x') (η y)) i
  --  is-prop-cover (eq {x} {x'} u i) (eq {y} {y'} v j) = ? --isSet→SquareP {A = λ i j → isProp (Cover (eq u i) (eq v j))} (λ i j → isProp→isSet isPropIsProp)
  --                                                        --             ? {!!} {!!} {!!} {!!} {!!}
 --   is-prop-cover (eq {x} {x'} u i) (is-set y' y'' x₁ y i₁ i₂) = {!!}
 --   
  --  is-prop-cover (is-set x' x'' x y i i₁) y' = {!!}

  
  Cover : (x y : setRealization) → hProp (ℓ-max ℓC ℓC')
  Cover (η x) (η y) = ∥ Σ[ n ∈ ℕ ] R n x y ∥ , isPropPropTrunc
  Cover (η x) (eq {y} {y'} u i) = Σ≡Prop (λ _ → isPropIsProp) {u = ∥ Σ[ n ∈ ℕ ] (R n x y) ∥ , isPropPropTrunc} {v = ∥ Σ[ n ∈ ℕ ] (R n x y') ∥ , isPropPropTrunc}
                                  (ua (propBiimpl→Equiv isPropPropTrunc isPropPropTrunc (rec isPropPropTrunc Rxy→Rxy') (rec isPropPropTrunc Rxy'→Rxy))) i
    where
    
    Rxy→Rxy' : Σ[ n ∈ ℕ ] (R n x y) → ∥ Σ[ n ∈ ℕ ] (R n x y') ∥
    Rxy→Rxy' (n , r) = ∣ suc n , (trans1 r u) ∣

    Rxy'→Rxy : Σ[ n ∈ ℕ ] (R n x y') → ∥ Σ[ n ∈ ℕ ] (R n x y) ∥
    Rxy'→Rxy (n , r) = ∣ suc n , trans2 r u ∣
      
  Cover (η x) (is-set y y' p q i j) = isSetHProp (Cover (η x) y) (Cover (η x) y') (λ i → Cover (η x) (p i)) (λ i → Cover (η x) (q i)) i j 
    
  Cover (eq {x} {x'} u i) (η y) = Σ≡Prop (λ _ → isPropIsProp) {u = ∥ Σ[ n ∈ ℕ ] (R n x y) ∥ , isPropPropTrunc} {v = ∥ Σ[ n ∈ ℕ ] (R n x' y) ∥ , isPropPropTrunc}
                                  (ua (propBiimpl→Equiv isPropPropTrunc isPropPropTrunc (rec isPropPropTrunc Rxy→∥Rx'y∥) (rec isPropPropTrunc Rx'y→∥Rxy∥))) i
    where
    
    Rxy→Rx'y : {y : ob C} → Σ[ n ∈ ℕ ] (R n x y) → Σ[ n ∈ ℕ ] (R n x' y)
    Rxy→Rx'y (.0 , is-refl) = _ , trans2 is-refl u
    Rxy→Rx'y (.(suc _) , trans1 r v) = _ , trans1 (snd (Rxy→Rx'y (_ , r))) v
    Rxy→Rx'y (.(suc _) , trans2 r v) = _ , trans2 (snd (Rxy→Rx'y (_ , r))) v

    Rxy→∥Rx'y∥ : Σ[ n ∈ ℕ ] (R n x y) → ∥ Σ[ n ∈ ℕ ] (R n x' y) ∥
    Rxy→∥Rx'y∥ (n , r) = ∣ Rxy→Rx'y (n , r) ∣

    Rx'y→Rxy : {y : ob C} → Σ[ n ∈ ℕ ] (R n x' y) → Σ[ n ∈ ℕ ] (R n x y)
    Rx'y→Rxy (.0 , is-refl) = _ , trans1 is-refl u
    Rx'y→Rxy (.(suc _) , trans1 r v) = _ , trans1 (snd (Rx'y→Rxy (_ , r))) v
    Rx'y→Rxy (.(suc _) , trans2 r v) = _ , trans2 (snd (Rx'y→Rxy (_ , r))) v

    Rx'y→∥Rxy∥ : Σ[ n ∈ ℕ ] (R n x' y) → ∥ Σ[ n ∈ ℕ ] (R n x y) ∥
    Rx'y→∥Rxy∥ (n , r) = ∣ Rx'y→Rxy (n , r) ∣
    
  Cover (eq u i) (eq v j) = {!!}
  Cover (eq x i) (is-set y y₁ x₁ y₂ i₁ i₂) = {!!}
  Cover (is-set x x₁ x₂ y₁ i i₁) y = {!!}

  isRefl-Cover : (x : setRealization) → fst (Cover x x)
  isRefl-Cover (η x) = ∣ _ , is-refl ∣
  isRefl-Cover (eq {x} {y} u i) = isProp→PathP {B = λ i → fst (Cover (eq u i) (eq u i))} (λ i → snd (Cover (eq u i) (eq u i))) ∣ _ , is-refl ∣  ∣ _ , is-refl ∣ i
  isRefl-Cover (is-set x y p q i j) = {!!}

  ≡→Cover : {x y : setRealization} → x ≡ y → fst (Cover x y)
  ≡→Cover {x} {y} p = subst (λ y → fst (Cover x y)) p (isRefl-Cover x)

  R→≡ : {x y : ob C} → Σ[ n ∈ ℕ ] (R n x y) → η x ≡ η y
  R→≡ (.0 , is-refl) = refl
  R→≡ (.(suc _) , trans1 r u) = R→≡ (_ , r) ∙ eq u
  R→≡ (.(suc _) , trans2 r u) = R→≡ (_ , r) ∙ sym (eq u)

  Cover→≡ : {x y : setRealization} → fst (Cover x y) → x ≡ y
  Cover→≡ {η x} {η y} r = rec (is-set (η x) (η y)) R→≡ r
  Cover→≡ {η x} {eq {y} {y'} u i} r = {!!} --isProp→PathP {B = λ i → η x ≡ eq u i} (λ i → is-set (η x) (eq u i)) {!!} {!!} {!!}
  Cover→≡ {η x} {is-set y y₁ x₁ y₂ i i₁} r = {!!}
  Cover→≡ {eq x i} {y} r = {!!}
  Cover→≡ {is-set x x₁ x₂ y₁ i i₁} {y} r = {!!}

--i = i0 ⊢ rec (is-set (η x) (η x₁)) R→≡ r j
--i = i1 ⊢ rec (is-set (η x) (η y)) R→≡ r j
--j = i0 ⊢ η x
--j = i1 ⊢ eq u i
