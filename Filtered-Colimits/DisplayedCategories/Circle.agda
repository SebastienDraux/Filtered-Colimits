module Filtered-Colimits.DisplayedCategories.Circle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.S1

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Discrete

open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories

open Category
open isUnivalent
open CatIso
open dispCat
open isEquiv

C : Category ℓ-zero ℓ-zero
C = DiscreteCategory (Unit , isOfHLevelUnit 3)

D : Category ℓ-zero ℓ-zero
D = DiscreteCategory (S¹ , isGroupoidS¹)

isLeftFibD : (x : ob D) → isContr (Σ[ y ∈ ob D ] (D [ x , y ]))
isLeftFibD x = isContrSingl x

isUnivD : isUnivalent D
isUnivD .univ x y .equiv-proof u = (mor u , makeIso≡ (pathToIso (mor u)) u (J (λ y p → mor (pathToIso p) ≡ p) pathToIso-refl (mor u))) , λ { (v , a) → ΣPathP ((cong mor (sym a) ∙ J (λ y p → mor (pathToIso p) ≡ p) pathToIso-refl v) , {!!})}

test : (x : ob D) → (p q : x ≡ x) → p ≡ q
test x p q = {!!}
  where
  p' : PathP (λ i → D [ x , p i ]) refl refl
  p' = {!!}


--D : dispCat C {!!} {!!}
--D .dC-ob tt = S¹
--D .dC-hom {tt} {tt} f = {!!}
--D .dC-homSet = {!!}
--D .dC-id = {!!}
--D .dC-⋆ = {!!}
--D .dC-⋆IdL = {!!}
--D .dC-⋆IdR = {!!}
--D .dC-⋆Assoc = {!!}
