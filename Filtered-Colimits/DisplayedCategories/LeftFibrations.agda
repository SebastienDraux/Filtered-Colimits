module Filtered-Colimits.DisplayedCategories.LeftFibrations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Morphism

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.General.Poset
open import Filtered-Colimits.Category.Functors
open import Filtered-Colimits.Category.PosetCat
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat
open import Filtered-Colimits.DisplayedCategories.Functors
open import Filtered-Colimits.DisplayedCategories.DispPreorder

open Category
open dispCat
open dispCat-Funct
open dispPreorder
open eq-dF
open isDispPreorder
open Functor
open NatTrans
open dispCatIso
open NatIso
open isIso
open eqFunct

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC')
         (ℓD ℓD' : Level) where

  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
    
  leftFibrUnivDispPreorderCat : Category (ℓ-suc ℓ) ℓ
  leftFibrUnivDispPreorderCat .ob = Σ[ D ∈ dispPreorder C ℓD ℓD' ] isUnivalent-dC (disp-cat D) × isLeftFibration (disp-cat D)
  leftFibrUnivDispPreorderCat .Hom[_,_] (D , _) (D' , _) = (dispPreorderCat C ℓD ℓD') [ D , D' ]
  leftFibrUnivDispPreorderCat .id {D , _} = id (dispPreorderCat C ℓD ℓD') {D}
  leftFibrUnivDispPreorderCat ._⋆_ {D , _} {D' , _} {D'' , _} = _⋆_ (dispPreorderCat C ℓD ℓD') {x = D} {y = D'} {z = D''}
  leftFibrUnivDispPreorderCat .⋆IdL {D , _} {D' , _} = ⋆IdL (dispPreorderCat C ℓD ℓD') {x = D} {y = D'}
  leftFibrUnivDispPreorderCat .⋆IdR {D , _} {D' , _} = ⋆IdR (dispPreorderCat C ℓD ℓD') {x = D} {y = D'}
  leftFibrUnivDispPreorderCat .⋆Assoc {D , _} {D' , _} {D'' , _} {D''' , _} = ⋆Assoc (dispPreorderCat C ℓD ℓD') {x = D} {y = D'} {z = D''} {w = D'''}
  leftFibrUnivDispPreorderCat .isSetHom {D , _} {D' , _} = isSetHom (dispPreorderCat C ℓD ℓD') {x = D} {y = D'}


module _ {ℓD : Level}
         {C : Category ℓC ℓC'} where

  dispCat→functToSET : Functor (leftFibrUnivDispPreorderCat C ℓD ℓD) (FUNCTOR C (SET ℓD))
  dispCat→functToSET = F
    where
    G : ob (leftFibrUnivDispPreorderCat C ℓD ℓD) → Functor C (SET ℓD)
    G (D , isUNivD , isLeftFibD) .F-ob x = ((disp-cat D) ⦅ x ⦆) , isSetFiber (is-disp-preorder D) x
    G (D , isUNivD , isLeftFibD) .F-hom = leftFib-getOb (disp-cat D) isLeftFibD
    G (D , isUNivD , isLeftFibD) .F-id = funExt (λ a → leftFib-unicityOb (disp-cat D) isLeftFibD (id C) a (a , (dC-id (disp-cat D))))
    G (D , isUNivD , isLeftFibD) .F-seq {x} {y} {z} f g = funExt eq
      where
      eq : (a : (disp-cat D) ⦅ x ⦆) → leftFib-getOb (disp-cat D) isLeftFibD (f ⋆⟨ C ⟩ g) a ≡ leftFib-getOb (disp-cat D) isLeftFibD g (leftFib-getOb (disp-cat D) isLeftFibD f a)
      eq a = leftFib-unicityOb (disp-cat D) isLeftFibD (f ⋆⟨ C ⟩ g) a (c , u ⋆⟨ disp-cat D ⟩ᴰ v)
        where
        b = leftFib-getOb (disp-cat D) isLeftFibD f a
        c = leftFib-getOb (disp-cat D) isLeftFibD g b
        u = leftFib-getHom (disp-cat D) isLeftFibD f a
        v = leftFib-getHom (disp-cat D) isLeftFibD g b

    α : {D D' : ob (leftFibrUnivDispPreorderCat C ℓD ℓD)} → (f : dispCat-Funct (disp-cat (fst D)) (disp-cat (fst D'))) → NatTrans (G D) (G D')
    α f .N-ob x a = f ⟅ a ⟆ᴰ
    α {D , isUNivD , isLeftFibD} {D' , isUNivD' , isLeftFibD'} f .N-hom {x} {y} g = funExt eq
      where
      eq : (a : (disp-cat D) ⦅ x ⦆) → f ⟅ leftFib-getOb (disp-cat D) isLeftFibD g a ⟆ᴰ ≡ leftFib-getOb (disp-cat D') isLeftFibD' g (f ⟅ a ⟆ᴰ)
      eq a = sym (leftFib-unicityOb (disp-cat D') isLeftFibD' g (f ⟅ a ⟆ᴰ) (f ⟅ b ⟆ᴰ , f ⟪ u ⟫ᴰ))
        where
        b = leftFib-getOb (disp-cat D) isLeftFibD g a
        u = leftFib-getHom (disp-cat D) isLeftFibD g a
        
    F : Functor (leftFibrUnivDispPreorderCat C ℓD ℓD) (FUNCTOR C (SET ℓD))
    F .F-ob = G
    F .F-hom {D} {D'} = α {D = D} {D' = D'}
    F .F-id = makeNatTransPath (funExt λ x → funExt (λ a → refl))
    F .F-seq f g = makeNatTransPath (funExt (λ x → funExt (λ a → refl)))

  functToSET→dispCat : Functor (FUNCTOR C (SET ℓD)) (leftFibrUnivDispPreorderCat C ℓD ℓD)
  functToSET→dispCat = 𝑭
    where
    D : Functor C (SET ℓD) → dispCat C ℓD ℓD
    D G .dC-ob x = fst (G ⟅ x ⟆)
    D G .dC-hom f a b = (G ⟪ f ⟫) a ≡ b
    D G .dC-id = funExt⁻ (F-id G) _
    D G .dC-⋆ {f = f} {g} p q = funExt⁻ (F-seq G _ _) _ ∙ cong (G ⟪ g ⟫) p ∙ q
    D G .dC-⋆IdL {y = y} p = snd (G ⟅ y ⟆) _ _ _ _
    D G .dC-⋆IdR  {y = y} p = snd (G ⟅ y ⟆) _ _ _ _
    D G .dC-⋆Assoc {z = z} p q r = snd (G ⟅ z ⟆) _ _ _ _
    D G .dC-homSet {y = y} f a b = isProp→isSet (snd (G ⟅ y ⟆) _ _)

    isdispPreorderDG : (G : Functor C (SET ℓD)) → isDispPreorder (D G)
    isdispPreorderDG G .isSetFiber x = snd (G ⟅ x ⟆)
    isdispPreorderDG G .isPropMor {y = y} f a b = snd (G ⟅ y ⟆) _ _

    D-preorder : Functor C (SET ℓD) → dispPreorder C ℓD ℓD
    D-preorder G .disp-cat = D G
    D-preorder G .is-disp-preorder = isdispPreorderDG G

    isLeftFibDG : (G : Functor C (SET ℓD)) → isLeftFibration (D G)
    isLeftFibDG G f a = isContrSingl ((G ⟪ f ⟫) a)

    isUnivDG : (G : Functor C (SET ℓD)) → isUnivalent-dC (D G)
    isUnivDG G a b .equiv-proof f = (a≡b , makeDispCatIsoPath (D G) (dC-pathToIso (D G) a≡b) f (snd (G ⟅ _ ⟆) _ _ _ _)) ,
                                    λ {(g , p) → Σ≡Prop (λ p → isSetDispCatIso (D G) idCatIso _ _ _ _) (snd (G ⟅ _ ⟆) _ _ _ _)}
      where
      a≡b = sym (funExt⁻ (F-id G) a) ∙ dC-mor f

    F : {G H : Functor C (SET ℓD)} → NatTrans G H → dispCat-Funct (D G) (D H)
    F α .dF-ob {x} a = (α ⟦ x ⟧) a
    F {G} {H} α .dF-hom {x} {y} {f} {a} {b} p = 
      (H ⟪ f ⟫) ((α ⟦ x ⟧) a)    ≡⟨ funExt⁻ (sym (N-hom α f)) a ⟩
      (α ⟦ y ⟧) ((G ⟪ f ⟫) a)    ≡⟨ cong (α ⟦ y ⟧) p ⟩
      (α ⟦ y ⟧) b                ∎
    F {G} {H} α .dF-id = snd (H ⟅ _ ⟆) _ _ _ _
    F {G} {H} α .dF-seq p q = snd (H ⟅ _ ⟆) _ _ _ _

    𝑭 : Functor (FUNCTOR C (SET ℓD)) (leftFibrUnivDispPreorderCat C ℓD ℓD)
    𝑭 .F-ob G = D-preorder G , (isUnivDG G) , isLeftFibDG G
    𝑭 .F-hom = F
    𝑭 .F-id {G} = eq-dF→≡ eq
      where
      eq : eq-dF (F (idTrans G)) dC-idFunct
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom p = snd (G ⟅ _ ⟆) _ _ _ _
    𝑭 .F-seq {G} {G'} {G''} α β = eq-dF→≡ eq
      where
      eq : eq-dF (F (α ●ᵛ β)) ((F α) ⋆ᵈᶠ (F β))
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom p = snd (G'' ⟅ _ ⟆) _ _ _ _


  functToSET→dispCat→functToSet : NatIso (dispCat→functToSET ∘F functToSET→dispCat) 𝟙⟨ FUNCTOR C (SET ℓD) ⟩
  functToSET→dispCat→functToSet = α
    where
    β : (F : Functor C (SET ℓD)) → NatTrans ((dispCat→functToSET ∘F functToSET→dispCat) ⟅ F ⟆) F
    β F .N-ob x a = a
    β F .N-hom f = funExt (λ a → refl)

    invβ : (F : Functor C (SET ℓD)) → NatTrans F ((dispCat→functToSET ∘F functToSET→dispCat) ⟅ F ⟆)
    invβ F .N-ob x a = a
    invβ F .N-hom f = funExt (λ a → refl)

    isIsoβ : (F : Functor C (SET ℓD)) → isIso (FUNCTOR C (SET ℓD)) (β F)
    isIsoβ F .inv = invβ F
    isIsoβ F .sec = makeNatTransPath (funExt λ x → funExt (λ a → refl))
    isIsoβ F .ret = makeNatTransPath (funExt λ x → funExt (λ a → refl))

    α : NatIso (dispCat→functToSET ∘F functToSET→dispCat) 𝟙⟨ FUNCTOR C (SET ℓD) ⟩
    α .trans .N-ob = β
    α .trans .N-hom f = makeNatTransPath (funExt (λ x → funExt (λ a → refl)))
    α .nIso = isIsoβ
    
  dispCat→functToSet→dispCat : NatIso (functToSET→dispCat ∘F dispCat→functToSET) 𝟙⟨ leftFibrUnivDispPreorderCat C ℓD ℓD ⟩
  dispCat→functToSet→dispCat = α
    where
    F : (D : ob (leftFibrUnivDispPreorderCat C ℓD ℓD)) → dispCat-Funct (disp-cat (fst (functToSET→dispCat ⟅ dispCat→functToSET ⟅ D ⟆ ⟆))) (disp-cat (fst D))
    F (D , isUnivD , isLeftFibD) .dF-ob a = a
    F (D , isUnivD , isLeftFibD) .dF-hom {f = f} {a} {b} p = subst (λ b → (disp-cat D) [ f , a , b ]ᴰ) p (leftFib-getHom (disp-cat D) isLeftFibD f a)
    F (D , isUnivD , isLeftFibD) .dF-id = isPropMor (is-disp-preorder D) _ _ _ _ _
    F (D , isUnivD , isLeftFibD) .dF-seq p q = isPropMor (is-disp-preorder D) _ _ _ _ _

    G : (D : ob (leftFibrUnivDispPreorderCat C ℓD ℓD)) → dispCat-Funct (disp-cat (fst D)) (disp-cat (fst (functToSET→dispCat ⟅ dispCat→functToSET ⟅ D ⟆ ⟆)))
    G (D , isUnivD , isLeftFibD) .dF-ob a = a
    G (D , isUnivD , isLeftFibD) .dF-hom {f = f} {a} {b} u = leftFib-unicityOb (disp-cat D) isLeftFibD f a (b , u)
    G (D , isUnivD , isLeftFibD) .dF-id = isPropMor (is-disp-preorder (fst (functToSET→dispCat ⟅ dispCat→functToSET ⟅ (D , isUnivD , isLeftFibD) ⟆ ⟆))) _ _ _ _ _
    G (D , isUnivD , isLeftFibD) .dF-seq u v = isPropMor (is-disp-preorder (fst (functToSET→dispCat ⟅ dispCat→functToSET ⟅ (D , isUnivD , isLeftFibD) ⟆ ⟆))) _ _ _ _ _ 
    
    β : NatTrans (functToSET→dispCat ∘F dispCat→functToSET) 𝟙⟨ leftFibrUnivDispPreorderCat C ℓD ℓD ⟩
    β .N-ob = F
    β .N-hom {D , isUnivD , isLeftFibD} {D' , isUnivD' , isLeftFibD'} H = eq-dF→≡ eq
      where
      eq : eq-dF (functToSET→dispCat ⟪ F-hom dispCat→functToSET {x = D , isUnivD , isLeftFibD} {y = D' , isUnivD' , isLeftFibD'} H ⟫ ⋆ᵈᶠ F (D' , isUnivD' , isLeftFibD')) (F (D , isUnivD , isLeftFibD) ⋆ᵈᶠ H)
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom p = isPropMor (is-disp-preorder D') _ _ _ _ _

    isIsoβ : (D : ob (leftFibrUnivDispPreorderCat C ℓD ℓD)) → isIso (leftFibrUnivDispPreorderCat C ℓD ℓD) {x = functToSET→dispCat ⟅ dispCat→functToSET ⟅ D ⟆ ⟆} {y = D} (F D)
    isIsoβ (D , isUnivD , isLeftFibD) .inv = G (D , isUnivD , isLeftFibD)
    isIsoβ (D , isUnivD , isLeftFibD) .sec = eq-dF→≡ eq
      where
      eq : eq-dF (G (D , isUnivD , isLeftFibD) ⋆ᵈᶠ F (D , isUnivD , isLeftFibD)) dC-idFunct
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom f = isPropMor (is-disp-preorder D) _ _ _ _ _
    isIsoβ (D , isUnivD , isLeftFibD) .ret = eq-dF→≡ eq
      where
      eq : eq-dF (F (D , isUnivD , isLeftFibD) ⋆ᵈᶠ G (D , isUnivD , isLeftFibD)) dC-idFunct
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom f = isPropMor (is-disp-preorder (fst (functToSET→dispCat ⟅ dispCat→functToSET ⟅ (D , isUnivD , isLeftFibD) ⟆ ⟆))) _ _ _ _ _
      
    α : NatIso (functToSET→dispCat ∘F dispCat→functToSET) 𝟙⟨ leftFibrUnivDispPreorderCat C ℓD ℓD ⟩
    α .trans = β
    α .nIso = isIsoβ
