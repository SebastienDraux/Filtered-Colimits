{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Sigma

open import Functors
open import Lemma
open import IsoCat

open Category
open IsPoset
open PosetStr
open eqFunct

module _ ℓ ℓ' where

  POSET : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ') --Poset with increasing functions
  POSET .ob = Poset ℓ ℓ'
  POSET .Hom[_,_] A B = Functor (PosetCategory A) (PosetCategory B)
  POSET .id {A} = 𝟙⟨ PosetCategory A ⟩
  POSET ._⋆_ F G = F ⋆ᶠ G
  POSET .⋆IdL F = F-lUnit
  POSET .⋆IdR F = F-rUnit
  POSET .⋆Assoc F G H = F-assoc {F = F} {G} {H}
  POSET .isSetHom {A , strA} {B , strB} F G p q = sym (retEq ≡≃eqFunct p) ∙ cong eqFunct→≡ eq ∙ retEq ≡≃eqFunct q
    where
    p' = ≡→eqFunct p
    q' = ≡→eqFunct q
    
    𝑨 = PosetCategory (A , strA)
    𝑩 = PosetCategory (B , strB)
    
    eqOb : I → (x : ob 𝑨) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
    eqOb i x = is-set (isPoset strB) (F ⟅ x ⟆) (G ⟅ x ⟆) (eq-ob p' x) (eq-ob q' x) i
    
    eq : p' ≡ q'
    eq i .eq-ob x = eqOb i x
    eq i .eq-hom {x} {y} x≤y = isProp→PathP (λ j → isSetHom (PosetCategory (B , strB)) (g j) (G ⟪ x≤y ⟫)) (eq-hom p' x≤y) (eq-hom q' x≤y) i
      where
      g : I → 𝑩 [ G ⟅ x ⟆ , G ⟅ y ⟆ ]
      g i = invP 𝑩 (eqOb i x) ⋆⟨ 𝑩 ⟩ F ⟪ x≤y ⟫ ⋆⟨ 𝑩 ⟩ morP 𝑩 (eqOb i y)

  POSET' : Category (ℓ-suc (ℓ-max ℓ ℓ')) ℓ --Poset with standard maps
  POSET' .ob = Poset ℓ ℓ'
  POSET' .Hom[_,_] (A , _) (B , _) = A → B
  POSET' .id = λ x → x
  POSET' ._⋆_ f g = λ x → g (f x)
  POSET' .⋆IdL f = refl
  POSET' .⋆IdR f = refl
  POSET' .⋆Assoc f g h = refl
  POSET' .isSetHom {A , strA} {B , strB} f g p q = isSetΠ (λ _ → is-set (isPoset strB)) f g p q
