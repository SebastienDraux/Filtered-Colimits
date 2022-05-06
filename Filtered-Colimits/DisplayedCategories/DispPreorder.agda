module Filtered-Colimits.DisplayedCategories.DispPreorder where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

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


module _ {ℓD ℓD' : Level}
         {C : Category ℓC ℓC'}
         (D : dispPreorder C ℓD ℓD') where

  isCocart-seq : {x y z : ob C} → (f : C [ x , y ]) → (g : C [ y , z ]) → (a : (disp-cat D) ⦅ x ⦆) → (b : (disp-cat D) ⦅ y ⦆) → (c : (disp-cat D) ⦅ z ⦆) → (u : (disp-cat D) [ f , a , b ]ᴰ) → (v : (disp-cat D) [ g , b , c ]ᴰ) → isCocartesian (disp-cat D) f a b u → isCocartesian (disp-cat D) g b c v → isCocartesian (disp-cat D) (f ⋆⟨ C ⟩ g) a c (u ⋆⟨ disp-cat D ⟩ᴰ v)
  isCocart-seq f g a b c u v isCocart-u isCocart-v {g = g'} p {d} w = uniqueExists v'
                        (isPropMor (is-disp-preorder D) _ _ _ _ _) (λ _ → isProp→isSet (isPropMor (is-disp-preorder D) _ _ _) _ _) λ _ _ → isPropMor (is-disp-preorder D) _ _ _ _ _
          where
          u' = isCocartesian-getHom (disp-cat D) f (sym (⋆Assoc C _ _ _) ∙ p) a b d u w isCocart-u
          v' = isCocartesian-getHom (disp-cat D) g refl b c d v u' isCocart-v
