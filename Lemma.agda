{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism

open Iso

isSet→isPropPathP : {ℓ : Level} → (A : I → Type ℓ) → ((i : I) → isSet (A i)) → (a0 : A i0) → (a1 : A i1) → isProp (PathP A a0 a1)
isSet→isPropPathP A set a0 a1 p q i j = pi≡qi j i
  where
  pi≡qi : PathP (λ i → p i ≡ q i) refl refl
  pi≡qi = isProp→PathP (λ i → set i (p i) (q i)) refl refl

fst-Σ-subst : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {a a' : A} → {p : a ≡ a'} →
              (P : A → Type ℓ') → (Q : (a : A) → P a → Type ℓ'') → (x : P a) → (y : Q a x) →
              fst (subst (λ a → Σ (P a) (Q a)) p (x , y)) ≡ subst P p x
fst-Σ-subst P Q x y = refl

subst-subst≡subst2 : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {w x : A} → {y z : B} →
                     (C : A → B → Type ℓ'') → (p : w ≡ x) → (q : y ≡ z) → (c : C w y) →
                     subst (C x) q (subst (λ a → C a y) p c) ≡ subst2 C p q c
subst-subst≡subst2 {w = w} {x = x} {y = y} {z = z} C p q c = J (λ z q → subst (C x) q (subst (λ a → C a y) p c) ≡ subst2 C p q c) (substRefl {B = C x} (subst (λ a → C a y) p c) ∙ refl) q

subst2Refl : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {x : A} → {y : B} →
                     (C : A → B → Type ℓ'') → (c : C x y) → subst2 C refl refl c ≡ c
                  
subst2Refl {x = x} {y = y} C c = sym (subst-subst≡subst2 C refl refl c) ∙ substRefl {B = C x} (subst (C x) refl c) ∙ substRefl {B = C x} c

Σ-Set : {ℓ ℓ' : Level} → (A : Type ℓ) → (B : A → Type ℓ') → isSet A → ((a : A) → isSet (B a)) → isSet (Σ A B)
Σ-Set A B isSetA isSetB (a , b) (a' , b') p q = eq
  where
  p' = PathPΣ p
  q' = PathPΣ q

  p'≡q' : p' ≡ q'
  p'≡q' = Σ≡Prop (λ p → isSet→isPropPathP (λ i → B (p i)) (λ i → isSetB (p i)) b b') (isSetA a a' (fst p') (fst q'))

  eq : p ≡ q
  eq = 
    p ≡⟨ sym (rightInv ΣPathPIsoPathPΣ p) ⟩
    ΣPathP (PathPΣ p) ≡⟨ cong (λ p' → ΣPathP p') p'≡q' ⟩
    ΣPathP (PathPΣ q) ≡⟨ rightInv ΣPathPIsoPathPΣ q ⟩
    q ∎
  

subst≡ᵣ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : a ≡ x) → subst (λ x → a ≡ x) p q ≡ q ∙ p
subst≡ᵣ p q = fromPathP (compPath-filler q p)

subst≡ₗ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : x ≡ a) → subst (λ x → x ≡ a) p q ≡ (sym p) ∙ q
subst≡ₗ p q = fromPathP (compPath-filler' (sym p) q)
