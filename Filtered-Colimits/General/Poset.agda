module Filtered-Colimits.General.Poset where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Poset

private
  variable
    ℓ ℓ' : Level

open PosetStr

ieq : (P : Poset ℓ ℓ') → (a b : fst P) → Type ℓ'
ieq P a b = _≤_ (snd P) a b 
syntax ieq P a b = a ≤[ P ] b

≡→≤ : (P : Poset ℓ ℓ') → {a b : fst P} → a ≡ b → a ≤[ P ] b
≡→≤ P {a} {b} p = subst (λ b → a ≤[ P ] b) p (is-refl (snd P) a)


≤-trans : (P : Poset ℓ ℓ') → (x : fst P) {y z : fst P} → x ≤[ P ] y → y ≤[ P ] z → x ≤[ P ] z
≤-trans P x p q = is-trans (snd P) _ _ _ p q

≤-refl : (P : Poset ℓ ℓ') → (x : fst P) → x ≤[ P ] x
≤-refl P x = is-refl (snd P) x

infixr 0 ≤-trans
infix 1 ≤-refl

syntax ≤-trans P x p q = x ≤[ P ]⟨ p ⟩ q
syntax ≤-refl P x = x [ P ]□




