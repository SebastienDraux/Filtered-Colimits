module Filtered-Colimits.Category.Functors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Data.Sigma

open import Filtered-Colimits.Category.IsoCat
open import Filtered-Colimits.General.Lemma

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Functor
open Category
open NatTrans
open CatIso
open Iso
open isUnivalent

fComp = funcComp

infixr 30 fComp
syntax fComp G F = F ⋆ᶠ G

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  eval : C .ob → (Functor (FUNCTOR C D) D)
  eval x .F-ob F = F ⟅ x ⟆
  eval x .F-hom α = α ⟦ x ⟧
  eval x .F-id = refl
  eval x .F-seq α β = refl

  evalFunct : Functor C (FUNCTOR (FUNCTOR C D) D)
  evalFunct .F-ob = eval
  evalFunct .F-hom {x} {y} f .N-ob F = F ⟪ f ⟫
  evalFunct .F-hom {x} {y} f .N-hom {F} {G} α = sym (N-hom α f)
  evalFunct .F-id {x} = makeNatTransPath (funExt (λ F → F-id F))
  evalFunct .F-seq {x} {y} {z} f g = makeNatTransPath (funExt (λ F → F-seq F f g))


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  record eqFunct (F G : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      eq-ob : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
      eq-hom : {x y : ob C} → (f : C [ x , y ]) → invP D (eq-ob x) ⋆⟨ D ⟩ F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (eq-ob y) ≡ G ⟪ f ⟫

  open eqFunct

  eqFunct≡→≡eq-ob : {F G : Functor C D} → {p q : eqFunct F G} → (p ≡ q) → ((x : ob C) → eq-ob p x ≡ eq-ob q x)
  eqFunct≡→≡eq-ob p≡q x = cong (λ p → eq-ob p x) p≡q

  ≡eq-ob→eqFunct≡ : {F G : Functor C D} → (p q : eqFunct F G) → ((x : ob C) → eq-ob p x ≡ eq-ob q x) → (p ≡ q)
  ≡eq-ob→eqFunct≡ p q eq-ob≡ i .eq-ob x = eq-ob≡ x i
  ≡eq-ob→eqFunct≡ {F} {G} p q eq-ob≡ i .eq-hom {x} {y} f = isProp→PathP (λ i → isSetHom D (((invP D (eq-ob≡ x i)) ⋆⟨ D ⟩ (F ⟪ f ⟫)) ⋆⟨ D ⟩ (morP D (eq-ob≡ y i))) (G ⟪ f ⟫)) (eq-hom p f) (eq-hom q f) i

  eqFunct≡ : {F G : Functor C D} → (p q : eqFunct F G) → (p ≡ q) ≃ ((x : ob C) → eq-ob p x ≡ eq-ob q x)
  eqFunct≡ {F} {G} p q = isoToEquiv isom
    where
    isom : Iso (p ≡ q) ((x : ob C) → eq-ob p x ≡ eq-ob q x)
    isom .fun = eqFunct≡→≡eq-ob
    isom .inv = ≡eq-ob→eqFunct≡ p q
    isom .leftInv p≡q i j .eq-ob x = cong (λ p → eq-ob p x) p≡q j
    isom .leftInv p≡q i j .eq-hom {x} {y} f =
                      isSet→SquareP (λ i j → isProp→isSet {A = (invP D (eq-ob (p≡q j) x) ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ morP D (eq-ob (p≡q j) y) ≡ G ⟪ f ⟫} (isSetHom D _ _))
                                     (λ j → eq-hom (≡eq-ob→eqFunct≡ p q (eqFunct≡→≡eq-ob p≡q) j) f) (λ j → eq-hom (p≡q j) f) (λ _ → eq-hom p f) (λ _ → eq-hom q f) i j
    isom .rightInv ≡eq-ob = refl
  
  eqFunct→≡ : {F G : Functor C D} → eqFunct F G → F ≡ G
  eqFunct→≡ {F} {G} eq i = H
    where
      pathPFfGf : {x y : ob C} → (f : C [ x , y ]) → PathP (λ i → D [ eq-ob eq x i , eq-ob eq y i ]) (F ⟪ f ⟫) (G ⟪ f ⟫)
      pathPFfGf {x} {y} f = toPathP (sym Gf≡subst2Ff)
        where
        Gf≡subst2Ff : G ⟪ f ⟫ ≡ subst2 (λ x' y' → D [ x' , y' ]) (eq-ob eq x) (eq-ob eq y) (F ⟪ f ⟫)
        Gf≡subst2Ff  = sym (eq-hom eq f) ∙ substHomLR D (eq-ob eq x) (eq-ob eq y) (F ⟪ f ⟫)
          
      H : Functor C D
      H .F-ob x = eq-ob eq x i
      H .F-hom {x} {y} f = pathPFfGf f i
      H .F-id {x} = rem i
        where
        rem : PathP (λ i → pathPFfGf (id C) i ≡ id D) (F-id F) (F-id G)
        rem = isProp→PathP (λ _ → isSetHom D _ _) (F-id F) (F-id G)
      H .F-seq f g = rem i
        where
        rem : PathP (λ i → pathPFfGf (f ⋆⟨ C ⟩ g) i ≡ pathPFfGf f i ⋆⟨ D ⟩ pathPFfGf g i) (F-seq F f g) (F-seq G f g)
        rem = isProp→PathP (λ _ → isSetHom D _ _) (F-seq F f g) (F-seq G f g)

  ≡→eqFunct : {F G : Functor C D} → F ≡ G → eqFunct F G
  ≡→eqFunct {F} {G} p .eq-ob x i = (p i) ⟅ x ⟆
  ≡→eqFunct {F} {G} p .eq-hom {x} {y} f = substHomLR D (eq-ob (≡→eqFunct p) x) (eq-ob (≡→eqFunct p) y) (F ⟪ f ⟫) ∙ fromPathP (λ i → (p i) ⟪ f ⟫)

  eqFunct→≡→eqFunct : {F G : Functor C D} → (eq : eqFunct F G) → ≡→eqFunct (eqFunct→≡ eq) ≡ eq
  eqFunct→≡→eqFunct {F} {G} eq = ≡eq-ob→eqFunct≡ (≡→eqFunct (eqFunct→≡ eq)) eq (λ _ → refl)

  ≡→eqFunct→≡ : {F G : Functor C D} → (p : F ≡ G) → eqFunct→≡ (≡→eqFunct p) ≡ p
  ≡→eqFunct→≡ {F} {G} p i j = H
    where
    rem-hom : {x y : ob C} → (f : C [ x , y ]) → PathP (λ j → eqFunct→≡ (≡→eqFunct p) j ⟪ f ⟫ ≡ (p j) ⟪ f ⟫) refl refl
    rem-hom f = isProp→PathP (λ _ → isSetHom D _ _) refl refl

    H : Functor C D
    H .F-ob  x = (p j) ⟅ x ⟆
    H .F-hom f = rem-hom f j i 
    H .F-id {x} k = rem k j i
      where
      rem : PathP (λ k → PathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) refl refl) (rem-hom (id C)) λ j → refl
      rem = isProp→PathP (λ k → isSet→isPropPathP (λ j → F-id (eqFunct→≡ (≡→eqFunct p) j) k ≡ F-id (p j) k) (λ _ → isProp→isSet (isSetHom D _ _)) _ _) _ _
    H .F-seq {x} {y} {z} f g k = rem k j i
      where
      rem : PathP (λ k → PathP (λ j → F-seq (eqFunct→≡ (≡→eqFunct p) j) f g k ≡ F-seq (p j) f g k) refl refl) (rem-hom (f ⋆⟨ C ⟩ g)) (λ j i → rem-hom f j i ⋆⟨ D ⟩ rem-hom g j i)
      
      rem = isProp→PathP (λ k → isSet→isPropPathP (λ j →  F-seq (eqFunct→≡ (≡→eqFunct p) j) f g k ≡ F-seq (p j) f g k) (λ _ → isProp→isSet (isSetHom D _ _)) _ _) _ _

  ≡IsoEqFunct : {F G : Functor C D} → Iso (F ≡ G) (eqFunct F G)
  ≡IsoEqFunct .fun = ≡→eqFunct
  ≡IsoEqFunct .inv = eqFunct→≡
  ≡IsoEqFunct .leftInv = ≡→eqFunct→≡
  ≡IsoEqFunct .rightInv = eqFunct→≡→eqFunct

  ≡≃eqFunct : {F G : Functor C D} → (F ≡ G) ≃ (eqFunct F G)
  ≡≃eqFunct {F} {G} = isoToEquiv ≡IsoEqFunct

  ≡of≡Funct : {F G : Functor C D} → (p q : F ≡ G) → (p ≡ q) ≃ ((x : ob C) → cong (λ F → F ⟅ x ⟆) p ≡ cong (λ F → F ⟅ x ⟆) q)
  ≡of≡Funct p q = congEquiv ≡≃eqFunct ∙ₑ eqFunct≡ (≡→eqFunct p) (≡→eqFunct q)

  eqFunctRefl : (F : Functor C D) → eqFunct F F
  eqFunctRefl F .eq-ob x = refl
  eqFunctRefl F .eq-hom f = substHomLR D refl refl (F ⟪ f ⟫) ∙ subst2Refl (λ x y → D [ F ⟅ x ⟆ , F ⟅ y ⟆ ]) (F ⟪ f ⟫)

  isUnivFUNCT : isUnivalent D → isUnivalent (FUNCTOR C D)
  isUnivFUNCT isUnivD .univ F G .equiv-proof α = (F≡G , pathToIso≡α) , unicityF≡G
    where
    γ = mor α
    δ = inv α
    
    iso-ob : (x : ob C) → CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆)
    iso-ob x .mor = γ ⟦ x ⟧
    iso-ob x .inv = δ ⟦ x ⟧
    iso-ob x .sec = cong (λ γ → γ ⟦ x ⟧) (sec α)
    iso-ob x .ret = cong (λ γ → γ ⟦ x ⟧) (ret α)

    univ-FxGx : (x : ob C) → (F ⟅ x ⟆ ≡ G ⟅ x ⟆) ≃ (CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆))
    univ-FxGx x = univEquiv isUnivD (F ⟅ x ⟆) (G ⟅ x ⟆)

    Fx≡Gx : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
    Fx≡Gx x = equivFun (invEquiv (univ-FxGx x)) (iso-ob x)

    morP≡γ : (x : ob C) → morP D (Fx≡Gx x) ≡ γ ⟦ x ⟧
    morP≡γ x = cong mor (secEq (univ-FxGx x) (iso-ob x))
    
    eqFG : eqFunct F G
    eqFG .eq-ob = Fx≡Gx
    eqFG .eq-hom {x} {y} f =
      (invP D (Fx≡Gx x) ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ morP D (Fx≡Gx y)     ≡⟨ ⋆Assoc D _ _ _ ⟩
      invP D (Fx≡Gx x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ morP D (Fx≡Gx y))     ≡⟨ cong (λ g → invP D (Fx≡Gx x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ g)) (morP≡γ y) ⟩
      invP D (Fx≡Gx x) ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ γ ⟦ y ⟧)              ≡⟨ cong (λ g → invP D (Fx≡Gx x) ⋆⟨ D ⟩ g) (N-hom γ f) ⟩
      invP D (Fx≡Gx x) ⋆⟨ D ⟩ (γ ⟦ x ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫)              ≡⟨ cong (λ g → invP D (Fx≡Gx x) ⋆⟨ D ⟩ (g ⋆⟨ D ⟩ G ⟪ f ⟫)) (sym (morP≡γ x)) ⟩
      invP D (Fx≡Gx x) ⋆⟨ D ⟩ (morP D (Fx≡Gx x) ⋆⟨ D ⟩ G ⟪ f ⟫)     ≡⟨ sym (⋆Assoc D _ _ _) ⟩
      (invP D (Fx≡Gx x) ⋆⟨ D ⟩ morP D (Fx≡Gx x)) ⋆⟨ D ⟩ G ⟪ f ⟫     ≡⟨ cong (λ g → g ⋆⟨ D ⟩ G ⟪ f ⟫) (secMorP D (Fx≡Gx x)) ⟩
      id D ⋆⟨ D ⟩ G ⟪ f ⟫                                           ≡⟨ ⋆IdL D _ ⟩
      G ⟪ f ⟫ ∎

    F≡G : F ≡ G
    F≡G = eqFunct→≡ eqFG

    morPathToIso≡γ : (x : ob C) → morP (FUNCTOR C D) F≡G ⟦ x ⟧ ≡ γ ⟦ x ⟧
    morPathToIso≡γ x = 
      morP (FUNCTOR C D) F≡G ⟦ x ⟧                                   ≡⟨ morPFunct F≡G x ⟩
      morP D (cong (λ F → F ⟅ x ⟆) F≡G)                             ≡⟨ refl ⟩
      morP D (Fx≡Gx x)                                               ≡⟨ morP≡γ x ⟩ 
      γ ⟦ x ⟧                                                        ∎

    pathToIso≡α : pathToIso F≡G ≡ α
    pathToIso≡α = makeIsoPath (pathToIso F≡G) α (makeNatTransPath (funExt morPathToIso≡γ))

    unicityF≡G : (pair : Σ[ F≡G' ∈ F ≡ G ] pathToIso F≡G' ≡ α) → (F≡G , pathToIso≡α) ≡ pair
    unicityF≡G (F≡G' , p) = Σ≡Prop (λ F≡G' → isSet-CatIso F G (pathToIso F≡G') α) (equivFun (invEquiv (≡of≡Funct F≡G F≡G')) eq)
      where
      F⟅x⟆≡G⟅x⟆ : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
      F⟅x⟆≡G⟅x⟆ x = cong (λ F → F ⟅ x ⟆) F≡G
      
      F⟅x⟆≡G⟅x⟆' : (x : ob C) → F ⟅ x ⟆ ≡ G ⟅ x ⟆
      F⟅x⟆≡G⟅x⟆' x = cong (λ F → F ⟅ x ⟆) F≡G'
      
      eqMor : (x : ob C) → morP D (F⟅x⟆≡G⟅x⟆ x) ≡ morP D (F⟅x⟆≡G⟅x⟆' x)
      eqMor x = 
        morP D (F⟅x⟆≡G⟅x⟆ x)              ≡⟨ sym (morPFunct F≡G x) ⟩
        morP (FUNCTOR C D) F≡G ⟦ x ⟧       ≡⟨ morPathToIso≡γ x ⟩
        γ ⟦ x ⟧                            ≡⟨ cong (λ α → mor α ⟦ x ⟧) (sym p) ⟩
        morP (FUNCTOR C D) F≡G' ⟦ x ⟧      ≡⟨ morPFunct F≡G' x ⟩
        morP D (F⟅x⟆≡G⟅x⟆' x) ∎
      
      eq : (x : ob C) → cong (λ F → F ⟅ x ⟆) F≡G ≡ cong (λ F → F ⟅ x ⟆) F≡G'
      eq x = injMorP D isUnivD (cong (λ F → F ⟅ x ⟆) F≡G) (cong (λ F → F ⟅ x ⟆) F≡G') (eqMor x)

      
    
  
