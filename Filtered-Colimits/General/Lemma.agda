module Filtered-Colimits.General.Lemma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma


open Iso

isSet→isPropPathP : {ℓ : Level} → (A : I → Type ℓ) → ((i : I) → isSet (A i)) → (a0 : A i0) → (a1 : A i1) → isProp (PathP A a0 a1)
isSet→isPropPathP A isSetA a0 a1 p q = isSet→SquareP (λ _ → isSetA) p q refl refl

subst-subst≡subst2 : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {w x : A} → {y z : B} →
                     (C : A → B → Type ℓ'') → (p : w ≡ x) → (q : y ≡ z) → (c : C w y) →
                     subst (C x) q (subst (λ a → C a y) p c) ≡ subst2 C p q c
subst-subst≡subst2 {w = w} {x = x} {y = y} {z = z} C p q c = J (λ z q → subst (C x) q (subst (λ a → C a y) p c) ≡ subst2 C p q c) (substRefl {B = C x} (subst (λ a → C a y) p c) ∙ refl) q

subst2Refl : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → {x : A} → {y : B} →
                     (C : A → B → Type ℓ'') → (c : C x y) → subst2 C refl refl c ≡ c
                  
subst2Refl {x = x} {y = y} C c = sym (subst-subst≡subst2 C refl refl c) ∙ substRefl {B = C x} (subst (C x) refl c) ∙ substRefl {B = C x} c

subst≡ᵣ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : a ≡ x) → subst (λ x → a ≡ x) p q ≡ q ∙ p
subst≡ᵣ p q = fromPathP (compPath-filler q p)

subst≡ₗ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : x ≡ a) → subst (λ x → x ≡ a) p q ≡ (sym p) ∙ q
subst≡ₗ p q = fromPathP (compPath-filler' (sym p) q)

subst-subst : {ℓ ℓ' : Level} → {A : Type ℓ} → (B : A → Type ℓ') → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (b : B x) → subst B q (subst B p b) ≡ subst B (p ∙ q) b
subst-subst B p q b = J (λ z q → subst B q (subst B p b) ≡ subst B (p ∙ q) b) (substRefl {B = B} (subst B p b) ∙ cong (λ p → subst B p b) (rUnit p)) q


congSubst : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → (B : A → Type ℓ') → (C : A → Type ℓ'') → {x y : A} → (p : x ≡ y) → (f : {a : A} → B a → C a) → (b : B x) → f (subst B p b) ≡ subst C p (f b)
congSubst B C {x} {y} p f b = J (λ y p → f (subst B p b) ≡ subst C p (f b)) (cong f (substRefl {B = B} b) ∙ sym (substRefl {B = C} (f b))) p

subst2-filler : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {x x' : A} → {B : Type ℓ'} → {y y' : B} → (C : A → B → Type ℓ'') → (p : x ≡ x') → (q : y ≡ y') → (c : C x y) →
                PathP (λ i → C (p i) (q i)) c (subst2 C p q c)
subst2-filler C p q = transport-filler (cong₂ C p q)

isPropΣCancel : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : A → Type ℓ'} → isProp A → isProp (Σ A B) → (a : A) → isProp (B a)
isPropΣCancel {A = A} {B} isPropA isPropΣAB a b b' = subst (λ p → PathP (λ i → B (p i)) b b') q (cong snd p)
  where
  p : (a , b) ≡ (a , b')
  p = isPropΣAB (a , b) (a , b')
  
  q : cong fst p ≡ refl
  q = isProp→isSet isPropA a a (cong fst p) refl

≃→isProp : {ℓ ℓ' : Level} → {A : Type ℓ} → {B : Type ℓ'} → A ≃ B → isProp A → isProp B
≃→isProp f isPropA b b' = sym (secEq f b) ∙ cong (equivFun f) (isPropA _ _) ∙ secEq f b'

compPathP₂ : {ℓ ℓ' ℓ'' : Level} → {A : Type ℓ} → {B : Type ℓ'} → (C : A → B → Type ℓ'') → {a a' a'' : A} → {b b' b'' : B} → {c : C a b} → {c' : C a' b'} → {c'' : C a'' b''}
             (p : a ≡ a') → (p' : a' ≡ a'') → (q : b ≡ b') → (q' : b' ≡ b'') → PathP (λ i → C (p i) (q i)) c c' → PathP (λ i → C (p' i) (q' i)) c' c'' →
             PathP (λ i → C ((p ∙ p') i) ((q ∙ q') i)) c c''
compPathP₂ C {c = c} p p' q q' P Q i = comp (λ j → C (compPath-filler p p' j i) (compPath-filler q q' j i)) (λ j → λ {(i = i0) → c ; (i = i1) → Q j }) (P i)
