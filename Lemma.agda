{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

isSet→isPropPathP : {ℓ : Level} → (A : I → Type ℓ) → ((i : I) → isSet (A i)) → (a0 : A i0) → (a1 : A i1) → isProp (PathP A a0 a1)
isSet→isPropPathP A set a0 a1 p q i j = pi≡qi j i
  where
  pi≡qi : PathP (λ i → p i ≡ q i) refl refl
  pi≡qi = isProp→PathP (λ i → set i (p i) (q i)) refl refl
