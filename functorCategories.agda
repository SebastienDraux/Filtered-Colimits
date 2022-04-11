{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Morphism

open import Cubical.Data.Sigma

open import Categories
open import IsoCat
open import Limits
open import Colimits
open import Lemma
open import Functors
open import NatTransfo

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level


open Precategory
open NatTrans
open Functor
open Limit
open isLimit
open CatIso

module _ (C : Precategory ℓC ℓC')
         (D : Precategory ℓD ℓD') 
         ⦃ isCatD : isCategory D ⦄ where

  functorCat : Precategory (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  functorCat .ob = Functor C D
  functorCat .Hom[_,_] F G = F ⇒ G
  functorCat .id F = 1[ F ]
  functorCat ._⋆_ α β = α ●ᵛ β
  functorCat .⋆IdL α = makeNatTransPath (funExt λ x → D .⋆IdL (α ⟦ x ⟧))
  functorCat .⋆IdR α = makeNatTransPath (funExt λ x → D .⋆IdR (α ⟦ x ⟧))
  functorCat .⋆Assoc α β γ = makeNatTransPath (funExt (λ x → D .⋆Assoc (α ⟦ x ⟧) (β ⟦ x ⟧) (γ ⟦ x ⟧)))

  isCatFunct : isCategory functorCat
  isCatFunct .isSetHom {F} {G} α β p q = p≡q
    where
    eval-p : (x : C .ob) → α ⟦ x ⟧ ≡ β ⟦ x ⟧
    eval-p x = cong (λ f → f x) (cong (λ γ → N-ob γ) p)

    eval-q : (x : C .ob) → α ⟦ x ⟧ ≡ β ⟦ x ⟧
    eval-q x = cong (λ f → f x) (cong (λ γ → N-ob γ) q)

    eval-p≡eval-q : eval-p ≡ eval-q
    eval-p≡eval-q = funExt (λ x → isSetHom isCatD (α ⟦ x ⟧) (β ⟦ x ⟧) (eval-p x) (eval-q x))

    p-ob : N-ob α ≡ N-ob β
    p-ob = cong N-ob p

    q-ob : N-ob α ≡ N-ob β
    q-ob = cong N-ob q

    p-ob≡q-ob : p-ob ≡ q-ob
    p-ob≡q-ob i = funExt (eval-p≡eval-q i)

    p≡q : p ≡ q
    p≡q i j .N-ob = p-ob≡q-ob i j
    p≡q i j .N-hom {x} {y} f = rem j i
      where
      propPathP : (j : I)  → isProp (PathP (λ i → F ⟪ f ⟫ ⋆⟨ D ⟩ p-ob≡q-ob i j y ≡ p-ob≡q-ob i j x ⋆⟨ D ⟩ G ⟪ f ⟫) (N-hom (p j) f) (N-hom (q j) f))
      propPathP j = isSet→isPropPathP (λ i → F ⟪ f ⟫ ⋆⟨ D ⟩ p-ob≡q-ob i j y ≡ p-ob≡q-ob i j x ⋆⟨ D ⟩ G ⟪ f ⟫) (λ i → isProp→isSet (isSetHom isCatD (F ⟪ f ⟫ ⋆⟨ D ⟩ p-ob≡q-ob i j y) (p-ob≡q-ob i j x ⋆⟨ D ⟩ G ⟪ f ⟫))) (N-hom (p j) f) (N-hom (q j) f)

      rem : PathP (λ j → PathP (λ i → F ⟪ f ⟫ ⋆⟨ D ⟩ p-ob≡q-ob i j y ≡ p-ob≡q-ob i j x ⋆⟨ D ⟩ G ⟪ f ⟫) (N-hom (p j) f) (N-hom (q j) f)) refl refl
      rem = isProp→PathP propPathP refl refl

  makeFactPath : {x y : D .ob} → {F : Functor C D} → (c : Cone F x) → (c' : Cone F y) → (fact1 fact2 : c' factors c) → (fst fact1 ≡ fst fact2) → fact1 ≡ fact2
  makeFactPath c c' fact1 fact2 p = ΣPathP (p , (toPathP (isSetHom isCatFunct c (fst fact2 ◼ c') (transport (λ i → c ≡ p i ◼ c') (snd fact1)) (snd fact2))))

  eval : C .ob → (Functor functorCat D)
  eval x .F-ob F = F ⟅ x ⟆
  eval x .F-hom α = α ⟦ x ⟧
  eval x .F-id = refl
  eval x .F-seq α β = refl

evalFunct : (C : Precategory ℓC ℓC') → (D : Precategory ℓD ℓD') → ⦃ isCatD : isCategory D ⦄ → Functor C (functorCat (functorCat C D) D)
evalFunct C D .F-ob = eval C D
evalFunct C D .F-hom {x} {y} f .N-ob F = F ⟪ f ⟫
evalFunct C D .F-hom {x} {y} f .N-hom {F} {G} α = sym (N-hom α f)
evalFunct C D .F-id {x} = makeNatTransPath (funExt (λ F → F-id F))
evalFunct C D .F-seq {x} {y} {z} f g = makeNatTransPath (funExt (λ F → F-seq F f g))


