module Filtered-Colimits.DisplayedCategories.DispPreorder where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.Functors

private
  variable
    ℓC ℓC' : Level

open Category
open eq-dF
open dispPreorder
open isDispPreorder


module _ (C : Category ℓC ℓC')
         (ℓD ℓD' : Level) where

  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

  dispPreorderCat : Category (ℓ-suc ℓ) ℓ
  dispPreorderCat .ob = dispPreorder C ℓD ℓD'
  dispPreorderCat .Hom[_,_] D D' = dispCat-Funct (disp-cat D) (disp-cat D')
  dispPreorderCat .id = dC-idFunct
  dispPreorderCat ._⋆_ F G = F ⋆ᵈᶠ G
  dispPreorderCat .⋆IdL = dF-lUnit
  dispPreorderCat .⋆IdR = dF-rUnit
  dispPreorderCat .⋆Assoc = dF-Assoc
  dispPreorderCat .isSetHom {D} {D'} F G p q = sym (≡→eq-dF→≡ p) ∙ cong eq-dF→≡ p'≡q' ∙ ≡→eq-dF→≡ q
    where
    p' = ≡→eq-dF p
    q' = ≡→eq-dF q
    eq : {x : ob C} → (X : disp-cat D ⦅ x ⦆) → eq-dF-ob p' X ≡ eq-dF-ob q' X
    eq X = isSetFiber (is-disp-preorder D') _ (F ⟅ X ⟆ᴰ) (G ⟅ X ⟆ᴰ) (eq-dF-ob p' X) (eq-dF-ob q' X)
    p'≡q' = ≡eq-dF p' q' eq
