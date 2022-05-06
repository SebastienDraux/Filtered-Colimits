module Filtered-Colimits.DisplayedCategories.CocartesianFibrations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Morphism

open import Filtered-Colimits.General.Lemma
open import Filtered-Colimits.General.Poset
open import Filtered-Colimits.Category.Functors
open import Filtered-Colimits.Category.PosetCat
open import Filtered-Colimits.DisplayedCategories.DisplayedCategories
open import Filtered-Colimits.DisplayedCategories.IsoDispCat
open import Filtered-Colimits.DisplayedCategories.CocartesianMorphisms
open import Filtered-Colimits.DisplayedCategories.Functors
open import Filtered-Colimits.DisplayedCategories.DispPreorder

private
  variable
    ℓC ℓC' : Level

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
open PosetStr
open IsPoset
open eqFunct

module _ (C : Category ℓC ℓC')
         (ℓD ℓD' : Level) where
         
  private
    ℓ = ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

  cocartFibrUnivDispPreorderCat : Category (ℓ-suc ℓ) ℓ
  cocartFibrUnivDispPreorderCat .ob = Σ[ D ∈ dispPreorder C ℓD ℓD' ] isUnivalent-dC (disp-cat D) × isCocartesianFibration (disp-cat D)
  cocartFibrUnivDispPreorderCat .Hom[_,_] (D , _) (D' , _) = Σ ((dispPreorderCat C ℓD ℓD') [ D , D' ]) preservesCocartMor
  cocartFibrUnivDispPreorderCat .id {D , _} = id (dispPreorderCat C ℓD ℓD') {D} , preservesCocartMor-id (disp-cat D)
  cocartFibrUnivDispPreorderCat ._⋆_ {D , _} {D' , _} {D'' , _} (F , preservF) (G , preservG) =  (F ⋆ᵈᶠ G , preservesCocartMor-seq F G preservF preservG)
  cocartFibrUnivDispPreorderCat .⋆IdL {D , _} {D' , _} (F , _) = Σ≡Prop isProp-preservesCocartMor (⋆IdL (dispPreorderCat C ℓD ℓD') {x = D} {y = D'} F)
  cocartFibrUnivDispPreorderCat .⋆IdR {D , _} {D' , _} (F , _) = Σ≡Prop isProp-preservesCocartMor (⋆IdR (dispPreorderCat C ℓD ℓD') {x = D} {y = D'} F)
  cocartFibrUnivDispPreorderCat .⋆Assoc {D , _} {D' , _} {D'' , _} {D''' , _} (F , _) (G , _) (H , _) =
              Σ≡Prop isProp-preservesCocartMor (⋆Assoc (dispPreorderCat C ℓD ℓD') {x = D} {y = D'} {z = D''} {w = D'''} F G H)
  cocartFibrUnivDispPreorderCat .isSetHom {D , _} {D' , _} = isSetΣ (isSetHom (dispPreorderCat C ℓD ℓD') {x = D} {y = D'}) (λ F → isProp→isSet (isProp-preservesCocartMor F))


module _ {ℓD ℓD' : Level}
         {C : Category ℓC ℓC'} where

  dispCat→functToPOSET : Functor (cocartFibrUnivDispPreorderCat C ℓD ℓD') (FUNCTOR C (POSET ℓD ℓD'))
  dispCat→functToPOSET = F
    where
    toPoset : ob (cocartFibrUnivDispPreorderCat C ℓD ℓD') → ob C → Poset ℓD ℓD'
    toPoset (D , isUnivD , isCocartFibD) x = ((disp-cat D) ⦅ x ⦆) , posetStruct
      where
      posetStruct : PosetStr ℓD' (disp-cat D ⦅ x ⦆)
      posetStruct ._≤_ a b = (disp-cat D) [ id C , a , b ]ᴰ
      posetStruct .isPoset .is-set = isSetFiber (is-disp-preorder D) x
      posetStruct .isPoset .is-prop-valued = isPropMor (is-disp-preorder D) (id C)
      posetStruct .isPoset .is-refl a = dC-id (disp-cat D)
      posetStruct .isPoset .is-trans a b c a≤b b≤c = subst (λ f → (disp-cat D) [ f , a , c ]ᴰ) (⋆IdL C (id C)) (a≤b ⋆⟨ disp-cat D ⟩ᴰ b≤c)
      posetStruct .isPoset .is-antisym a b a≤b b≤a = equivFun (invEquiv (dC-univEquiv (disp-cat D) isUnivD a b)) a≃b
        where
        a≃b : dispCatIso (disp-cat D) idCatIso a b
        a≃b .dC-mor = a≤b
        a≃b .dC-inv = b≤a
        a≃b .dC-sec = isPropMor (is-disp-preorder D) (id C) _ _ _ _
        a≃b .dC-ret = isPropMor (is-disp-preorder D) (id C) _ _ _ _

    H : (D : ob (cocartFibrUnivDispPreorderCat C ℓD ℓD')) → {x y : ob C} → (f : C [ x , y ]) → Functor (PosetCategory (toPoset D x)) (PosetCategory (toPoset D y))
    H (D , isUnivD , isCocartFibD) f .F-ob a = isCocartesianFibration-getOb (disp-cat D) isCocartFibD f a
    H (D , isUnivD , isCocartFibD) {x} {y} f .F-hom {a} {a'} a≤a' =
      isCocartesian-getHom (disp-cat D) f (⋆IdR C f) a b b' u (subst (λ f → (disp-cat D) [ f , a , b' ]ᴰ) (⋆IdL C f) (a≤a' ⋆⟨ disp-cat D ⟩ᴰ u'))
                          (isCocartesianFibration-getIsCocart (disp-cat D) isCocartFibD f a)
      where
      b = isCocartesianFibration-getOb (disp-cat D) isCocartFibD f a
      b' = isCocartesianFibration-getOb (disp-cat D) isCocartFibD f a'
      u = isCocartesianFibration-getHom (disp-cat D) isCocartFibD f a 
      u' = isCocartesianFibration-getHom (disp-cat D) isCocartFibD f a'
    H (D , isUnivD , isCocartFibD) f .F-id = is-prop-valued (snd (toPoset (D , isUnivD , isCocartFibD) _)) _ _ _ _
    H (D , isUnivD , isCocartFibD) f .F-seq u v = is-prop-valued (snd (toPoset (D , isUnivD , isCocartFibD) _)) _ _ _ _
    G :  ob (cocartFibrUnivDispPreorderCat C ℓD ℓD') → Functor C (POSET ℓD ℓD')
    G (D , isUnivD , isCocartFibD) .F-ob = toPoset (D , isUnivD , isCocartFibD)
    G (D , isUnivD , isCocartFibD) .F-hom = H (D , isUnivD , isCocartFibD)
    G (D , isUnivD , isCocartFibD) .F-id {x} = eqFunct→≡ eq
      where
      eq : eqFunct (H (D , isUnivD , isCocartFibD) (id C)) 𝟙⟨ PosetCategory (toPoset (D , isUnivD , isCocartFibD) x) ⟩
      eq .eq-ob a = isCocartesianFibration-unicityOb (disp-cat D) isCocartFibD (id C) a a (dC-id (disp-cat D) , isCocartesian-id (disp-cat D) a)
      eq .eq-hom u = isPropMor (is-disp-preorder D) _ _ _ _ _
    G (D , isUnivD , isCocartFibD) .F-seq f g = eqFunct→≡ eq
      where
      eq : eqFunct (H (D , isUnivD , isCocartFibD) (f ⋆⟨ C ⟩ g)) (H (D , isUnivD , isCocartFibD) f ⋆ᶠ H (D , isUnivD , isCocartFibD) g)
      eq .eq-ob a = isCocartesianFibration-unicityOb (disp-cat D) isCocartFibD (f ⋆⟨ C ⟩ g) a c ((u ⋆⟨ disp-cat D ⟩ᴰ v) , isCocart-seq)
        where
        b = (H (D , isUnivD , isCocartFibD) f) ⟅ a ⟆
        u = isCocartesianFibration-getHom (disp-cat D) isCocartFibD f a
        isCocart-u = isCocartesianFibration-getIsCocart (disp-cat D) isCocartFibD f a
       
        c = (H (D , isUnivD , isCocartFibD) g) ⟅ b ⟆
        v = isCocartesianFibration-getHom (disp-cat D) isCocartFibD g b
        isCocart-v = isCocartesianFibration-getIsCocart (disp-cat D) isCocartFibD g b

        isCocart-seq : isCocartesian (disp-cat D) (f ⋆⟨ C ⟩ g) a c (u ⋆⟨ disp-cat D ⟩ᴰ v)
        isCocart-seq {g = g'} p {d} w = uniqueExists v'
                          (isPropMor (is-disp-preorder D) _ _ _ _ _) (λ _ → isProp→isSet (isPropMor (is-disp-preorder D) _ _ _) _ _) λ _ _ → isPropMor (is-disp-preorder D) _ _ _ _ _
          where
          u' = isCocartesian-getHom (disp-cat D) f (sym (⋆Assoc C _ _ _) ∙ p) a b d u w isCocart-u
          v' = isCocartesian-getHom (disp-cat D) g refl b c d v u' isCocart-v
        
      eq .eq-hom u  = isPropMor (is-disp-preorder D) _ _ _ _ _

    restrFunct : (D D' : ob (cocartFibrUnivDispPreorderCat C ℓD ℓD')) → (f : dispCat-Funct (disp-cat (fst D)) (disp-cat (fst D'))) → (x : ob C) → Functor (PosetCategory (toPoset D x)) (PosetCategory (toPoset D' x))
    restrFunct _ _ f x .F-ob a = f ⟅ a ⟆ᴰ
    restrFunct _ _ f x .F-hom u = f ⟪ u ⟫ᴰ
    restrFunct _ _ f x .F-id = dF-id f
    restrFunct _ (D' , _) f x .F-seq u v = isPropMor (is-disp-preorder D') _ _ _ _ _
  
    α : (D D' : ob (cocartFibrUnivDispPreorderCat C ℓD ℓD')) → (f : dispCat-Funct (disp-cat (fst D)) (disp-cat (fst D'))) → preservesCocartMor f → NatTrans (G D) (G D')
    α D D' f preservf .N-ob x = restrFunct D D' f x
    α (D , isUnivD , isCocartFibrD) (D' , isUnivD' , isCocartFibrD') f preservf .N-hom {x} {y} g = eqFunct→≡ eq
      where
      eq : eqFunct (H (D , isUnivD , isCocartFibrD) g ⋆ᶠ restrFunct  (D , isUnivD , isCocartFibrD) (D' , isUnivD' , isCocartFibrD') f y)
                   (restrFunct (D , isUnivD , isCocartFibrD) (D' , isUnivD' , isCocartFibrD') f x ⋆ᶠ H (D' , isUnivD' , isCocartFibrD') g)
      eq .eq-ob a = sym (isCocartesianFibration-unicityOb (disp-cat D') isCocartFibrD' g (f ⟅ a ⟆ᴰ) (f ⟅ a' ⟆ᴰ) (f ⟪ u ⟫ᴰ , preservf u isCocart-u))
        where
        a' = isCocartesianFibration-getOb (disp-cat D) isCocartFibrD g a
        u = isCocartesianFibration-getHom (disp-cat D) isCocartFibrD g a
        isCocart-u = isCocartesianFibration-getIsCocart (disp-cat D) isCocartFibrD g a
      eq .eq-hom u = isPropMor (is-disp-preorder D') _ _ _ _ _
    
    F : Functor (cocartFibrUnivDispPreorderCat C ℓD ℓD') (FUNCTOR C (POSET ℓD ℓD'))
    F .F-ob = G
    F .F-hom {D} {D'} (f , preservf) = α D D' f preservf
    F .F-id  {D , _ , _} = makeNatTransPath (funExt (λ x → eqFunct→≡ (record { eq-ob = λ a → refl ; eq-hom = λ u → isPropMor (is-disp-preorder D) _ _ _ _ _ })))
    F .F-seq {z = D'' , _ , _} f f' = makeNatTransPath (funExt (λ x → eqFunct→≡ (record { eq-ob = λ a → refl ; eq-hom = λ u → isPropMor (is-disp-preorder D'') _ _ _ _ _ })))

  functToPOSET→dispCat :  Functor (FUNCTOR C (POSET ℓD ℓD')) (cocartFibrUnivDispPreorderCat C ℓD ℓD')
  functToPOSET→dispCat = 𝑭
    where
    D : Functor C (POSET ℓD ℓD') → dispCat C ℓD ℓD'
    D G .dC-ob x = fst (G ⟅ x ⟆)
    D G .dC-hom {x} {y} f a b = G ⟪ f ⟫ ⟅ a ⟆ ≤[ G ⟅ y ⟆ ] b
    D G .dC-homSet {x} {y} f a b = isProp→isSet (is-prop-valued (snd (G ⟅ y ⟆)) _ _)
    D G .dC-id {x} {a} = ≡→≤ (G ⟅ x ⟆) (cong (λ G → G ⟅ a ⟆) (F-id G))
    D G .dC-⋆ {x} {y} {z} {a} {b} {c} {f} {g} p q =
     (G ⟪ f ⋆⟨ C ⟩ g ⟫) ⟅ a ⟆          ≤[ G ⟅ z ⟆ ]⟨ ≡→≤ (G ⟅ z ⟆) (cong (λ G → G ⟅ a ⟆) (F-seq G _ _)) ⟩
     (G ⟪ g ⟫) ⟅ (G ⟪ f ⟫) ⟅ a ⟆ ⟆    ≤[ G ⟅ z ⟆ ]⟨ G ⟪ g ⟫ ⟪ p ⟫ ⟩
     G ⟪ g ⟫ ⟅ b ⟆                     ≤[ G ⟅ z ⟆ ]⟨ q ⟩ 
     c                                  [ G ⟅ z ⟆ ]□
    D G .dC-⋆IdL p = is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _
    D G .dC-⋆IdR p = is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _
    D G .dC-⋆Assoc p q r = is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _

    isDispPreorderDG : (G : Functor C (POSET ℓD ℓD')) → isDispPreorder (D G)
    isDispPreorderDG G .isSetFiber x = is-set (snd (G ⟅ x ⟆))
    isDispPreorderDG G .isPropMor f a b = is-prop-valued (snd (G ⟅ _ ⟆)) _ _

    D-preorder : Functor C (POSET ℓD ℓD') → dispPreorder C ℓD ℓD'
    D-preorder G .disp-cat = D G
    D-preorder G .is-disp-preorder = isDispPreorderDG G

    isUnivDG : (G : Functor C (POSET ℓD ℓD')) → isUnivalent-dC (D G)
    isUnivDG G a b .equiv-proof p = (a≡b , makeDispCatIsoPath (D G) (dC-pathToIso (D G) a≡b) p (is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _)) ,
                                    λ {(a≡b' , _) → Σ≡Prop (λ a≡b → isSetDispCatIso (D G) idCatIso _ _ _ _) (is-set (snd (G ⟅ _ ⟆)) _ _ _ _)}
      where
      a≤b = a ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ H → H ⟅ a ⟆) (sym (F-id G))) ⟩ G ⟪ id C ⟫ ⟅ a ⟆ ≤[ G ⟅ _ ⟆ ]⟨ dC-mor p ⟩ b [ G ⟅ _ ⟆ ]□
      b≤a = b ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ H → H ⟅ b ⟆) (sym (F-id G))) ⟩ G ⟪ id C ⟫ ⟅ b ⟆ ≤[ G ⟅ _ ⟆ ]⟨ dC-inv p ⟩ a [ G ⟅ _ ⟆ ]□
      a≡b = is-antisym (snd (G ⟅ _ ⟆)) a b a≤b b≤a

    isCocartFibrDG : (G : Functor C (POSET ℓD ℓD')) → isCocartesianFibration (D G)
    isCocartFibrDG G {x} {y} f a = (b , b≤b , isCocartRefl) ,
                                   λ {(b' , ie , isCocart-ie) → Σ≡Prop (λ _ → isPropΣ (is-prop-valued (snd (G ⟅ _ ⟆)) _ _) λ _ → isProp-isCocartesian (D G) _)
                                   (unicity b' ie isCocart-ie) }
      where
      b = G ⟪ f ⟫ ⟅ a ⟆
      b≤b = is-refl (snd (G ⟅ _ ⟆)) b
      isCocartRefl : isCocartesian (D G) f a b b≤b
      isCocartRefl {g = g} {h} p {c} ie = uniqueExists ie' (is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _)
                                          (λ _ → isProp→isSet (is-prop-valued (snd (G ⟅ _ ⟆)) _ _) _ _) λ _ _ → is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _
        where
        ie' : G ⟪ g ⟫ ⟅ b ⟆ ≤[ G ⟅ _ ⟆ ] c
        ie' = 
          G ⟪ g ⟫ ⟅ G ⟪ f ⟫ ⟅ a ⟆ ⟆     ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ H → H ⟅ a ⟆) (sym (F-seq G _ _))) ⟩
          G ⟪ f ⋆⟨ C ⟩ g ⟫ ⟅ a ⟆         ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ f → G ⟪ f ⟫ ⟅ a ⟆) p) ⟩
          G ⟪ h ⟫ ⟅ a ⟆                 ≤[ G ⟅ _ ⟆ ]⟨ ie ⟩
          c                              [ G ⟅ _ ⟆ ]□
       
      unicity : (b' : fst (G ⟅ _ ⟆)) → (ie : (G ⟪ f ⟫) ⟅ a ⟆ ≤[ G ⟅ _ ⟆ ] b') → isCocartesian (D G) f a b' ie → b ≡ b'
      unicity b' ie isCocart-ie = is-antisym (snd (G ⟅ _ ⟆)) b b' b≤b' b'≤b
        where
        b→b' = isCocartesian-getHom (D G) f (⋆IdR C f) a b b' b≤b ie isCocartRefl
        b≤b' : b ≤[ G ⟅ _ ⟆ ] b'
        b≤b' = b ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ H → H ⟅ b ⟆) (sym (F-id G))) ⟩ G ⟪ id C ⟫ ⟅ b ⟆ ≤[ G ⟅ _ ⟆ ]⟨ b→b' ⟩ b' [ G ⟅ _ ⟆ ]□

        b'→b = isCocartesian-getHom (D G) f (⋆IdR C f) a b' b ie b≤b isCocart-ie
        b'≤b : b' ≤[ G ⟅ _ ⟆ ] b
        b'≤b = b' ≤[ G ⟅ _ ⟆ ]⟨ ≡→≤ (G ⟅ _ ⟆) (cong (λ H → H ⟅ b' ⟆) (sym (F-id G))) ⟩ G ⟪ id C ⟫ ⟅ b' ⟆ ≤[ G ⟅ _ ⟆ ]⟨ b'→b ⟩ b [ G ⟅ _ ⟆ ]□

    F : {G H : Functor C (POSET ℓD ℓD')} → NatTrans G H → dispCat-Funct (D G) (D H)
    F {G} {H} α .dF-ob {x} a = α ⟦ x ⟧ ⟅ a ⟆
    F {G} {H} α .dF-hom {x} {y} {f} {a} {b} ie = 
      (H ⟪ f ⟫) ⟅ (α ⟦ x ⟧) ⟅ a ⟆ ⟆         ≤[ H ⟅ _ ⟆ ]⟨ ≡→≤ (H ⟅ _ ⟆) (cong (λ G → G ⟅ a ⟆) (sym (N-hom α f))) ⟩
      α ⟦ y ⟧ ⟅ G ⟪ f ⟫ ⟅ a ⟆ ⟆             ≤[ H ⟅ _ ⟆ ]⟨ α ⟦ y ⟧ ⟪ ie ⟫ ⟩
      α ⟦ y ⟧ ⟅ b ⟆                          [ H ⟅ _ ⟆ ]□
    F {G} {H} α .dF-id = is-prop-valued (snd (H ⟅ _ ⟆)) _ _ _ _
    F {G} {H} α .dF-seq ie ie' = is-prop-valued (snd (H ⟅ _ ⟆)) _ _ _ _

    preservCocart : {G H : Functor C (POSET ℓD ℓD')} → (α : NatTrans G H) → preservesCocartMor (F α)
    preservCocart {G} {H} α {f = f} {a} {b} ie isCocart-ie {g = g} {h} p {c'} ie' = uniqueExists ie''
                                              (is-prop-valued (snd (H ⟅ _ ⟆)) _ _ _ _) (λ _ → isProp→isSet (is-prop-valued (snd (H ⟅ _ ⟆)) _ _) _ _) λ _ _ → is-prop-valued (snd (H ⟅ _ ⟆)) _ _ _ _
      where
      c = G ⟪ h ⟫ ⟅ a ⟆
      u = isCocartesianFibration-getHom (D G) (isCocartFibrDG G) h a
      isCocart-u = isCocartesianFibration-getIsCocart (D G) (isCocartFibrDG G) h a
      v = isCocartesian-getHom (D G) f p a b c ie u isCocart-ie
      
      ie'' : (H ⟪ g ⟫) ⟅ F α ⟅ b ⟆ᴰ ⟆ ≤[ H ⟅ _ ⟆ ] c'
      ie'' = 
        (H ⟪ g ⟫) ⟅ α ⟦ _ ⟧ ⟅ b ⟆ ⟆    ≤[ H ⟅ _ ⟆ ]⟨ ≡→≤ (H ⟅ _ ⟆) (cong (_⟅ b ⟆) (sym (N-hom α g))) ⟩
        α ⟦ _ ⟧ ⟅ (G ⟪ g ⟫) ⟅ b ⟆ ⟆    ≤[ H ⟅ _ ⟆ ]⟨ α ⟦ _ ⟧ ⟪ v ⟫ ⟩
        α ⟦ _ ⟧ ⟅ G ⟪ h ⟫ ⟅ a ⟆ ⟆      ≤[ H ⟅ _ ⟆ ]⟨  ≡→≤ (H ⟅ _ ⟆) (cong (_⟅ a ⟆) (N-hom α h)) ⟩
        (H ⟪ h ⟫) ⟅ α ⟦ _ ⟧ ⟅ a ⟆ ⟆    ≤[ H ⟅ _ ⟆ ]⟨ ie' ⟩
        c'                              [ H ⟅ _ ⟆ ]□
        
    𝑭 : Functor (FUNCTOR C (POSET ℓD ℓD')) (cocartFibrUnivDispPreorderCat C ℓD ℓD')
    𝑭 .F-ob G = D-preorder G , isUnivDG G , isCocartFibrDG G
    𝑭 .F-hom α = (F α) , (preservCocart α)
    𝑭 .F-id {G} = Σ≡Prop (λ F → isProp-preservesCocartMor F) (eq-dF→≡ eq)
     where
      eq : eq-dF (F (idTrans G)) dC-idFunct
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom ie = is-prop-valued (snd (G ⟅ _ ⟆)) _ _ _ _
    𝑭 .F-seq {G} {G'} {G''} α β = Σ≡Prop (λ F → isProp-preservesCocartMor F) (eq-dF→≡ eq)
      where
      eq : eq-dF (F (α ●ᵛ β)) ((F α) ⋆ᵈᶠ (F β))
      eq .eq-dF-ob a = refl
      eq .eq-dF-hom p = is-prop-valued (snd (G'' ⟅ _ ⟆)) _ _ _ _
