{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation

open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws

open import IsoCat
open import Functors

private
  variable
    ℓ ℓ' ℓ'' ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open NatTrans
--open CatIso

record 2-Category ℓ ℓ' ℓ'' : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
  field
    ob₀ : Type ℓ
    ob₁[_,_] : ob₀ → ob₀ → Category ℓ' ℓ''
    id₁ : {x : ob₀} → ob ob₁[ x , x ]
    _⋆₁_ : {x y z : ob₀} → ob ob₁[ x , y ] → ob ob₁[ y , z ] → ob ob₁[ x , z ]
    ⋆₁IdL : {x y : ob₀} → (f : ob ob₁[ x , y ]) → id₁ ⋆₁ f ≡ f
    ⋆₁IdR : {x y : ob₀} → (f : ob ob₁[ x , y ]) → f ⋆₁ id₁ ≡ f
    ⋆₁Assoc :  {w x y z : ob₀} → (f : ob ob₁[ w , x ]) → (g : ob ob₁[ x , y ]) → (h : ob ob₁[ y , z ]) → (f ⋆₁ g) ⋆₁ h ≡ f ⋆₁ (g ⋆₁ h)
    _⋆₂_ : {x y z : ob₀} → {f f' : ob ob₁[ x , y ]} → {g g' : ob ob₁[ y , z ]} → ob₁[ x , y ] [ f , f' ] → ob₁[ y , z ] [ g , g' ] → ob₁[ x , z ] [ f ⋆₁ g , f' ⋆₁ g' ]
    ⋆₂IdL : {x y : ob₀} → {f g : ob ob₁[ x , y ]} → (α : ob₁[ x , y ] [ f , g ]) →
      id ob₁[ x , x ] ⋆₂ α ≡ morP ob₁[ x , y ] (⋆₁IdL f) ⋆⟨ ob₁[ x , y ] ⟩ α ⋆⟨ ob₁[ x , y ] ⟩ invP ob₁[ x , y ] (⋆₁IdL g)
    ⋆₂IdR : {x y : ob₀} → {f g : ob ob₁[ x , y ]} → (α : ob₁[ x , y ] [ f , g ]) →
      α ⋆₂ id ob₁[ y , y ] ≡ morP ob₁[ x , y ] (⋆₁IdR f) ⋆⟨ ob₁[ x , y ] ⟩ α ⋆⟨ ob₁[ x , y ] ⟩ invP ob₁[ x , y ] (⋆₁IdR g)
    ⋆₂Assoc : {w x y z : ob₀} → {f f' : ob ob₁[ w , x ]} → {g g' : ob ob₁[ x , y ]} → {h h' : ob ob₁[ y , z ]} →
      (α : ob₁[ w , x ] [ f , f' ]) → (β : ob₁[ x , y ] [ g , g' ]) → (γ : ob₁[ y , z ] [ h , h' ]) →
      (α ⋆₂ β) ⋆₂ γ ≡ (morP ob₁[ w , z ] (⋆₁Assoc f g h) ⋆⟨ ob₁[ w , z ] ⟩ α ⋆₂ (β ⋆₂ γ) ⋆⟨ ob₁[ w , z ] ⟩ invP ob₁[ w , z ] (⋆₁Assoc f' g' h'))
    ⋆₂Id : {x y z : ob₀} → (f : ob ob₁[ x , y ]) → (g : ob ob₁[ y , z ]) → id ob₁[ x , y ] {x = f} ⋆₂ id ob₁[ y , z ] {x = g} ≡ id ob₁[ x , z ]
    compSeq : {x y z : ob₀} → {f g h : ob (ob₁[ x , y ])} → {f' g' h' : ob (ob₁[ y , z ])} →
      (α : ob₁[ x , y ] [ f , g ]) → (β : ob₁[ x , y ] [ g , h ]) → (α' : ob₁[ y , z ] [ f' , g' ]) → (β' : ob₁[ y , z ] [ g' , h' ]) → 
      α ⋆₂ α' ⋆⟨ ob₁[ x , z ] ⟩ (β ⋆₂ β') ≡ (α ⋆⟨ ob₁[ x , y ] ⟩ β) ⋆₂ (α' ⋆⟨ ob₁[ y , z ] ⟩ β')    

open 2-Category

_[_,_]₁ : (C : 2-Category ℓ ℓ' ℓ'') → (x y : C .ob₀) → Category ℓ' ℓ''
_[_,_]₁ = ob₁[_,_]

seq₁ : (C : 2-Category ℓ ℓ' ℓ'') → {x y z : ob₀ C} → ob (C [ x , y ]₁) → ob (C [ y , z ]₁) → ob (C [ x , z ]₁)
seq₁ C = C ._⋆₁_ 

infixl 15 seq₁
syntax seq₁ C f g = f ⋆⟨ C ⟩₁ g

seq₂ : (C : 2-Category ℓ ℓ' ℓ'') → (x y z : ob₀ C) → {f f' : ob (C [ x , y ]₁)} → {g g' : ob (C [ y , z ]₁)} → (α : C [ x , y ]₁ [ f , f' ]) → (β : C [ y , z ]₁ [ g , g' ]) → C [ x , z ]₁ [ f ⋆⟨ C ⟩₁ g , f' ⋆⟨ C ⟩₁ g' ]
seq₂ C x y z = C ._⋆₂_

infixl 15 seq₂
syntax seq₂ C α β = α ⋆⟨ C ⟩₂ β

PrecatCat : {ℓ ℓ' : Level} → 2-Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
PrecatCat {ℓ} {ℓ'} .ob₀ = Category ℓ ℓ'
PrecatCat .ob₁[_,_] C D = FUNCTOR C D
PrecatCat .id₁{C} = 𝟙⟨ C ⟩
PrecatCat ._⋆₁_ F G = F ⋆ᶠ G
PrecatCat .⋆₁IdL F = F-lUnit
PrecatCat .⋆₁IdR F = F-rUnit
PrecatCat .⋆₁Assoc F G H = F-assoc {F = F} {G} {H}
PrecatCat ._⋆₂_ {C} {D} {E} {F} {F'} {G} {G'} α β .N-ob x = β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ G' ⟪ α ⟦ x ⟧ ⟫
PrecatCat ._⋆₂_ {C} {D} {E} {F} {F'} {G} {G'} α β .N-hom {x} {y} f =
 G ⟪ F ⟪ f ⟫ ⟫ ⋆⟨ E ⟩ (β ⟦ F ⟅ y ⟆ ⟧ ⋆⟨ E ⟩ G' ⟪ α ⟦ y ⟧ ⟫)
      ≡⟨ sym (⋆Assoc E (G ⟪ F ⟪ f ⟫ ⟫) (β ⟦ F ⟅ y ⟆ ⟧) (G' ⟪ α ⟦ y ⟧ ⟫)) ⟩
 (G ⟪ F ⟪ f ⟫ ⟫ ⋆⟨ E ⟩ β ⟦ F ⟅ y ⟆ ⟧) ⋆⟨ E ⟩ G' ⟪ α ⟦ y ⟧ ⟫
      ≡⟨ cong (λ g → g ⋆⟨ E ⟩ G' ⟪ α ⟦ y ⟧ ⟫) (N-hom β (F ⟪ f ⟫)) ⟩
 (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ G' ⟪ F ⟪ f ⟫ ⟫) ⋆⟨ E ⟩ G' ⟪ α ⟦ y ⟧ ⟫
      ≡⟨ ⋆Assoc E (β ⟦ F ⟅ x ⟆ ⟧) (G' ⟪ F ⟪ f ⟫ ⟫) (G' ⟪ α ⟦ y ⟧ ⟫) ⟩
 β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ (G' ⟪ F ⟪ f ⟫ ⟫ ⋆⟨ E ⟩ G' ⟪ α ⟦ y ⟧ ⟫)
      ≡⟨ cong (λ g → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ g) (sym (F-seq G' (F ⟪ f ⟫) (α ⟦ y ⟧))) ⟩
 β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ (G' ⟪ F ⟪ f ⟫ ⋆⟨ D ⟩ α ⟦ y ⟧ ⟫)
      ≡⟨ cong (λ g → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ (G' ⟪ g ⟫)) (N-hom α f) ⟩
 β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ (G' ⟪ α ⟦ x ⟧ ⋆⟨ D ⟩ F' ⟪ f ⟫ ⟫)
      ≡⟨ cong (λ g → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ g) (F-seq G' (α ⟦ x ⟧) (F' ⟪ f ⟫)) ⟩
 β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ (G' ⟪ α ⟦ x ⟧ ⟫ ⋆⟨ E ⟩ G' ⟪ F' ⟪ f ⟫ ⟫)
      ≡⟨ sym (⋆Assoc E (β ⟦ F ⟅ x ⟆ ⟧) (G' ⟪ α ⟦ x ⟧ ⟫) (G' ⟪ F' ⟪ f ⟫ ⟫)) ⟩
 (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ E ⟩ G' ⟪ α ⟦ x ⟧ ⟫) ⋆⟨ E ⟩ G' ⟪ F' ⟪ f ⟫ ⟫ ∎
--PrecatCat .⋆₂IdL {C} {D} {F} {G} α = makeNatTransPath (funExt eq)
--  where
--  eq : (x : ob C) →
--    α ⟦ x ⟧ ⋆⟨ D ⟩ G ⟪ id C ⟫ ≡ (morP (FUNCTOR C D) (makeFunctPathRefl (F ∘F 𝟙⟨ C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ D ⟩ α ⟦ x ⟧) ⋆⟨ D ⟩ (invP (FUNCTOR C D) (makeFunctPathRefl (funcComp G 𝟙⟨ C ⟩) (F-id G) (F-seq G))) ⟦ x ⟧
--  eq x = 
 --   α ⟦ x ⟧ ⋆⟨ cat D ⟩ G ⟪ id (cat C) x ⟫
 --     ≡⟨ cong (λ g → α ⟦ x ⟧ ⋆⟨ cat D ⟩ g) (F-id G) ⟩
 --   α ⟦ x ⟧ ⋆⟨ cat D ⟩ id (cat D) (G ⟅ x ⟆)
 --     ≡⟨ ⋆IdR (cat D) (α ⟦ x ⟧) ⟩
 --   α ⟦ x ⟧
  --    ≡⟨ sym (⋆IdL (cat D) (α ⟦ x ⟧)) ⟩
 --   id (cat D) (F ⟅ x ⟆) ⋆⟨ cat D ⟩ α ⟦ x ⟧
 --     ≡⟨ cong (λ f → f ⋆⟨ cat D ⟩ α ⟦ x ⟧) (sym (makeFunctPathReflMorP (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F) x)) ⟩
 --   (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧)
 --     ≡⟨ sym (⋆IdR (cat D) (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧)) ⟩
--    (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ id (cat D) (G ⟅ x ⟆)
--      ≡⟨ cong (λ g → (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ g) (sym (makeFunctPathReflInvP (G ∘F 𝟙⟨ cat C ⟩) (F-id G) (F-seq G) x)) ⟩
 --   (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ (invP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (G ∘F 𝟙⟨ cat C ⟩) (F-id G) (F-seq G))) ⟦ x ⟧ ∎
--PrecatCat .⋆₂IdR {C} {D} {F} {G} α = makeNatTransPath (funExt eq)
--  where
--  eq : (x : ob (cat C)) →
--    id (cat D) (F ⟅ x ⟆) ⋆⟨ cat D ⟩ α ⟦ x ⟧ ≡ (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ (invP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (funcComp G 𝟙⟨ cat C ⟩) (F-id G) (F-seq G))) ⟦ x ⟧
--  eq x = 
--    id (cat D) (F ⟅ x ⟆) ⋆⟨ cat D ⟩ α ⟦ x ⟧
 --     ≡⟨ ⋆IdL (cat D) (α ⟦ x ⟧) ⟩
  --  α ⟦ x ⟧
 --     ≡⟨ sym (⋆IdL (cat D) (α ⟦ x ⟧)) ⟩
 --   id (cat D) (F ⟅ x ⟆) ⋆⟨ cat D ⟩ α ⟦ x ⟧
 --     ≡⟨ cong (λ f → f ⋆⟨ cat D ⟩ α ⟦ x ⟧) (sym (makeFunctPathReflMorP (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F) x)) ⟩
 --   (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧)
--      ≡⟨ sym (⋆IdR (cat D) (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧)) ⟩
 --   (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ id (cat D) (G ⟅ x ⟆)
 --     ≡⟨ cong (λ g → (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ g) (sym (makeFunctPathReflInvP (G ∘F 𝟙⟨ cat C ⟩) (F-id G) (F-seq G) x)) ⟩
  --  (morP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (F ∘F 𝟙⟨ cat C ⟩) (F-id F) (F-seq F)) ⟦ x ⟧ ⋆⟨ cat D ⟩ α ⟦ x ⟧) ⋆⟨ cat D ⟩ (invP (FUNCTOR (cat C) (cat D)) (makeFunctPathRefl (G ∘F 𝟙⟨ cat C ⟩) (F-id G) (F-seq G))) ⟦ x ⟧ ∎
--PrecatCat .⋆₂Assoc {A} {B} {C} {D} {F} {F'} {G} {G'} {H} {H'} α β γ = makeNatTransPath (funExt eq)
 -- where
 -- eq : (x : ob (cat A)) → γ ⟦ G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat C ⟩ G' ⟪ α ⟦ x ⟧ ⟫ ⟫ ≡ (morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫) ⋆⟨ cat D ⟩ invP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H' ∘F G' ∘F F') (F-id (H' ∘F (G' ∘F F'))) (F-seq (H' ∘F (G' ∘F F')))) ⟦ x ⟧
 -- eq x = 
 --   γ ⟦ G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat C ⟩ G' ⟪ α ⟦ x ⟧ ⟫ ⟫
 --     ≡⟨ cong (λ f → γ ⟦ G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ f) (F-seq H' (β ⟦ F ⟅ x ⟆ ⟧) (G' ⟪ α ⟦ x ⟧ ⟫)) ⟩
 --   γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ (H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)
--      ≡⟨ sym (⋆Assoc (cat D) (γ ⟦ G ⟅ F ⟅ x ⟆ ⟆ ⟧) (H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫) (H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)) ⟩ 
 --   γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫
 --     ≡⟨ sym (⋆IdL (cat D) (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)) ⟩
 --   id (cat D) (H ⟅ G ⟅ F ⟅ x ⟆ ⟆ ⟆) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)
 --     ≡⟨ cong (λ f → f ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)) (sym (makeFunctPathReflMorP (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F))) x)) ⟩
 --   (morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫)
 --     ≡⟨ sym (⋆IdR (cat D) ((morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫))) ⟩
 --  (morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫) ⋆⟨ cat D ⟩ id (cat D) (H' ⟅ G' ⟅ F' ⟅ x ⟆ ⟆ ⟆)
  ---   ≡⟨ cong (λ f → (morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫) ⋆⟨ cat D ⟩ f) (sym (makeFunctPathReflInvP (H' ∘F G' ∘F F') (F-id (H' ∘F (G' ∘F F'))) (F-seq (H' ∘F (G' ∘F F'))) x)) ⟩
 --   (morP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H ∘F G ∘F F) (F-id (H ∘F (G ∘F F))) (F-seq (H ∘F (G ∘F F)))) ⟦ x ⟧) ⋆⟨ cat D ⟩ (γ ⟦  G ⟅ F ⟅ x ⟆ ⟆ ⟧ ⋆⟨ cat D ⟩ H' ⟪ β ⟦ F ⟅ x ⟆ ⟧ ⟫ ⋆⟨ cat D ⟩ H' ⟪ G' ⟪ α ⟦ x ⟧ ⟫ ⟫) ⋆⟨ cat D ⟩ invP (FUNCTOR (cat A) (cat D)) (makeFunctPathRefl (H' ∘F G' ∘F F') (F-id (H' ∘F (G' ∘F F'))) (F-seq (H' ∘F (G' ∘F F')))) ⟦ x ⟧ ∎
--PrecatCat .⋆₂Id {C} {D} {E} F G = makeNatTransPath (funExt eq)
--  where
--  eq : (x : ob (cat C)) → idTrans G ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G ⟪ idTrans F ⟦ x ⟧ ⟫ ≡ id (cat E) (G ⟅ F ⟅ x ⟆ ⟆)
--  eq x = 
--    id (cat E) ( G ⟅ F ⟅ x ⟆ ⟆) ⋆⟨ cat E ⟩ G ⟪ idTrans F ⟦ x ⟧ ⟫
--        ≡⟨ ⋆IdL (cat E) (G ⟪ idTrans F ⟦ x ⟧ ⟫) ⟩
 --   G ⟪ id (cat D) (F ⟅ x ⟆) ⟫
 --       ≡⟨ F-id G ⟩
 --   id (cat E) (G ⟅ F ⟅ x ⟆ ⟆) ∎
--PrecatCat .compSeq {C} {D} {E} {F} {F'} {F''} {G} {G'} {G''} α α' β β' = makeNatTransPath (funExt eq)

--  where
--  eq : (x : ob (cat C)) → (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G' ⟪ α ⟦ x ⟧ ⟫) ⋆⟨ cat E ⟩ (β' ⟦ F' ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫) ≡ (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ β' ⟦ F ⟅ x ⟆ ⟧) ⋆⟨ cat E ⟩ G'' ⟪ α ⟦ x ⟧ ⋆⟨ cat D ⟩ α' ⟦ x ⟧ ⟫
--  eq x = 
 --   (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G' ⟪ α ⟦ x ⟧ ⟫) ⋆⟨ cat E ⟩ (β' ⟦ F' ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫)
 --     ≡⟨ ⋆Assoc (cat E) (β ⟦ F ⟅ x ⟆ ⟧) (G' ⟪ α ⟦ x ⟧ ⟫) (β' ⟦ F' ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫) ⟩
 --   β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (G' ⟪ α ⟦ x ⟧ ⟫ ⋆⟨ cat E ⟩ (β' ⟦ F' ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫))
 --     ≡⟨ cong (λ f → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ f) (sym (⋆Assoc (cat E) (G' ⟪ α ⟦ x ⟧ ⟫) (β' ⟦ F' ⟅ x ⟆ ⟧) (G'' ⟪ α' ⟦ x ⟧ ⟫))) ⟩
 --   β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ ((G' ⟪ α ⟦ x ⟧ ⟫ ⋆⟨ cat E ⟩ β' ⟦ F' ⟅ x ⟆ ⟧) ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫)
 --     ≡⟨ cong (λ f → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (f ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫)) (N-hom β' (α ⟦ x ⟧)) ⟩
--    β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ ((β' ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α ⟦ x ⟧ ⟫) ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫)
 --     ≡⟨ cong (λ f → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ f) (⋆Assoc (cat E) (β' ⟦ F ⟅ x ⟆ ⟧) (G'' ⟪ α ⟦ x ⟧ ⟫) (G'' ⟪ α' ⟦ x ⟧ ⟫)) ⟩
 --   β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (β' ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (G'' ⟪ α ⟦ x ⟧ ⟫ ⋆⟨ cat E ⟩ G'' ⟪ α' ⟦ x ⟧ ⟫))
  --    ≡⟨ cong (λ f → β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (β' ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ f)) (sym (F-seq G'' (α ⟦ x ⟧) (α' ⟦ x ⟧))) ⟩
 --   β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ (β' ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ G'' ⟪ α ⟦ x ⟧ ⋆⟨ cat D ⟩ α' ⟦ x ⟧ ⟫)
 --     ≡⟨ sym (⋆Assoc (cat E) (β ⟦ F ⟅ x ⟆ ⟧) (β' ⟦ F ⟅ x ⟆ ⟧) (G'' ⟪ α ⟦ x ⟧ ⋆⟨ cat D ⟩ α' ⟦ x ⟧ ⟫)) ⟩
 --   (β ⟦ F ⟅ x ⟆ ⟧ ⋆⟨ cat E ⟩ β' ⟦ F ⟅ x ⟆ ⟧) ⋆⟨ cat E ⟩ G'' ⟪ α ⟦ x ⟧ ⋆⟨ cat D ⟩ α' ⟦ x ⟧ ⟫ ∎
--
--open 2-Category

--CatCat : {ℓ ℓ' : Level} → 2-Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
--CatCat {ℓ = ℓ} {ℓ' = ℓ'} .2-cat = PrecatCat {ℓ = ℓ} {ℓ' = ℓ'}

