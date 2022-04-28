{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Foundations.GroupoidLaws

open import Lemma

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open CatIso
open Functor

module _ {C : Category ℓC ℓC'} where

  open Category
  open CatIso
  open Functor

  infix 30 _⟪_⟫ᵢ
  _⟪_⟫ᵢ : {D : Category ℓD ℓD'} → {x y : C .ob} → (F : Functor C D) → (f : CatIso C x y) → CatIso D (F ⟅ x ⟆) (F ⟅ y ⟆)
  _⟪_⟫ᵢ F f = preserveIsosF {F = F} f

  makeIso : {x y : C .ob} → (f : CatIso C x y) → (g : C [ x , y ]) → mor f ≡ g → isIso C g
  makeIso f g p = record { inv = inv f ; sec = cong (λ h → inv f ⋆⟨ C ⟩ h) (sym p) ∙ sec f ; ret = cong (λ h → h ⋆⟨ C ⟩ inv f) (sym p) ∙ ret f }

  invIso : {x y : C .ob} → CatIso C x y → CatIso C y x
  invIso f .mor = inv f
  invIso f .inv = mor f
  invIso f .sec = ret f
  invIso f .ret = sec f

  compIso : {x y z : C .ob} → CatIso C x y → CatIso C y z → CatIso C x z
  compIso f g .mor = mor f ⋆⟨ C ⟩ mor g
  compIso f g .inv = inv g ⋆⟨ C ⟩ inv f
  compIso {x} {y} {z} f g .sec =
    (inv g ⋆⟨ C ⟩ inv f) ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ mor g)
         ≡⟨ ⋆Assoc C (inv g) (inv f) (mor f ⋆⟨ C ⟩ mor g) ⟩
    inv g ⋆⟨ C ⟩ (inv f ⋆⟨ C ⟩ (mor f ⋆⟨ C ⟩ mor g))
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ f) (sym (⋆Assoc C (inv f) (mor f) (mor g))) ⟩
    inv g ⋆⟨ C ⟩ ((inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ mor g)
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ mor g)) (sec f) ⟩
    inv g ⋆⟨ C ⟩ (id C ⋆⟨ C ⟩ mor g)
        ≡⟨ cong (λ f → inv g ⋆⟨ C ⟩ f) (⋆IdL C (mor g)) ⟩
    inv g ⋆⟨ C ⟩ mor g
        ≡⟨ sec g ⟩
    id C ∎
    
  compIso {x} {y} {z} f g .ret = 
    (mor f ⋆⟨ C ⟩ mor g) ⋆⟨ C ⟩ (inv g ⋆⟨ C ⟩ inv f)
         ≡⟨ ⋆Assoc C (mor f) (mor g) (inv g ⋆⟨ C ⟩ inv f) ⟩
    mor f ⋆⟨ C ⟩ (mor g ⋆⟨ C ⟩ (inv g ⋆⟨ C ⟩ inv f))
        ≡⟨ cong (λ g →  mor f ⋆⟨ C ⟩ g) (sym (⋆Assoc C (mor g) (inv g) (inv f))) ⟩
    mor f ⋆⟨ C ⟩ ((mor g ⋆⟨ C ⟩ inv g) ⋆⟨ C ⟩ inv f)
        ≡⟨ cong (λ g → mor f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ inv f)) (ret g) ⟩
    mor f ⋆⟨ C ⟩ (id C ⋆⟨ C ⟩ inv f)
        ≡⟨ cong (λ g → mor f ⋆⟨ C ⟩ g) (⋆IdL C (inv f)) ⟩
    mor f ⋆⟨ C ⟩ inv f
        ≡⟨ ret f ⟩
    id C ∎

seqIso : (C : Category ℓC ℓC') → {x y z : C .ob} → CatIso C x y → CatIso C y z → CatIso C x z
seqIso C f g = compIso {C = C} f g

infixl 15 seqIso
syntax seqIso C f g = f ⋆ᵢ⟨ C ⟩ g

module _ {C : Category ℓC ℓC'} where
         
  makeIsoPath : {x y : C .ob} → (f g : CatIso C x y) → (mor f ≡ mor g) → f ≡ g
  makeIsoPath {x} {y} f g p = CatIso≡ f g p q
    where
    q : inv f ≡ inv g
    q = 
      inv f ≡⟨ sym (⋆IdR C (inv f)) ⟩
      inv f ⋆⟨ C ⟩ id C ≡⟨ cong (λ g → inv f ⋆⟨ C ⟩ g) (sym (ret g)) ⟩
      inv f ⋆⟨ C ⟩ (mor g ⋆⟨ C ⟩ inv g) ≡⟨ sym (⋆Assoc C (inv f) (mor g) (inv g)) ⟩
      (inv f ⋆⟨ C ⟩ mor g) ⋆⟨ C ⟩ inv g ≡⟨ cong (λ h →  (inv f ⋆⟨ C ⟩ h) ⋆⟨ C ⟩ inv g) (sym p) ⟩
      (inv f ⋆⟨ C ⟩ mor f) ⋆⟨ C ⟩ inv g ≡⟨ cong (λ f → f ⋆⟨ C ⟩ inv g) (sec f) ⟩
      (id C) ⋆⟨ C ⟩ inv g ≡⟨ ⋆IdL C (inv g) ⟩
      inv g ∎
      
  module _ {x y : C .ob}
           (f : CatIso C x y) where

    ⋆ᵢIdL : idCatIso ⋆ᵢ⟨ C ⟩ f ≡ f
    ⋆ᵢIdL = makeIsoPath (idCatIso ⋆ᵢ⟨ C ⟩ f) f (⋆IdL C (mor f))

    ⋆ᵢIdR : f ⋆ᵢ⟨ C ⟩ idCatIso ≡ f
    ⋆ᵢIdR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ idCatIso) f (⋆IdR C (mor f))

    ⋆ᵢInvL : invIso f ⋆ᵢ⟨ C ⟩ f ≡ idCatIso
    ⋆ᵢInvL = makeIsoPath (invIso f ⋆ᵢ⟨ C ⟩ f) idCatIso (sec f)

    ⋆ᵢInvR : f ⋆ᵢ⟨ C ⟩ invIso f ≡ idCatIso
    ⋆ᵢInvR = makeIsoPath (f ⋆ᵢ⟨ C ⟩ invIso f) idCatIso (ret f)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor C D) where

  iso-F-id : {x : C .ob} → F ⟪ idCatIso {x = x} ⟫ᵢ ≡ idCatIso
  iso-F-id {x} = makeIsoPath (F ⟪ idCatIso ⟫ᵢ) idCatIso (F-id F)

  iso-F-seq : {x y z : C .ob} → (f : CatIso C x y) → (g : CatIso C y z) → F ⟪ f ⋆ᵢ⟨ C ⟩ g ⟫ᵢ ≡ F ⟪ f ⟫ᵢ ⋆ᵢ⟨ D ⟩ F ⟪ g ⟫ᵢ
  iso-F-seq f g = makeIsoPath (F ⟪ f ⋆ᵢ⟨ C ⟩ g ⟫ᵢ) (F ⟪ f ⟫ᵢ ⋆ᵢ⟨ D ⟩ F ⟪ g ⟫ᵢ) (F-seq F (mor f) (mor g))

  iso-F-inv : {x y : C .ob} → (f : CatIso C x y) → F ⟪ invIso f ⟫ᵢ ≡ invIso (F ⟪ f ⟫ᵢ)
  iso-F-inv f = makeIsoPath (F ⟪ invIso f ⟫ᵢ) (invIso (F ⟪ f ⟫ᵢ)) refl

module _ (C : Category ℓC ℓC') where

  morP : {x y : ob C} → (p : x ≡ y) → C [ x , y ]
  morP {x} {y} p = mor (pathToIso {C = C} p)

  invP : {x y : ob C} → (p : x ≡ y) → C [ y , x ]
  invP {x} {y} p = inv (pathToIso {C = C} p)

  secMorP : {x y : ob C} → (p : x ≡ y) → invP p ⋆⟨ C ⟩ morP p ≡ id C
  secMorP {x} {y} p = sec (pathToIso {C = C} p)
  
  retMorP : {x y : ob C} → (p : x ≡ y) → morP p ⋆⟨ C ⟩ invP p ≡ id C
  retMorP {x} {y} p = ret (pathToIso {C = C} p)

  substHomL : {x x' y : ob C} → (p : x ≡ x') → (f : C [ x , y ]) → subst (λ x → C [ x , y ]) p f ≡ invP p ⋆⟨ C ⟩ f
  substHomL {x} {x'} {y} p f = J (λ x' p → subst (λ x → C [ x , y ]) p f ≡ invP p ⋆⟨ C ⟩ f) eqRefl p
    where
    eqRefl : subst (λ x → C [ x , y ]) refl f ≡ inv (subst (λ x → CatIso C x x) refl idCatIso) ⋆⟨ C ⟩ f
    eqRefl = 
      subst (λ x → C [ x , y ]) refl f ≡⟨ substRefl {B = λ x → C [ x , y ]} f ⟩
      f ≡⟨ sym (⋆IdL C f) ⟩
      id C ⋆⟨ C ⟩ f ≡⟨ cong (λ isom →  inv isom ⋆⟨ C ⟩ f) (sym (substRefl {B = λ x → CatIso C x x} idCatIso)) ⟩
      inv (subst (λ x → CatIso C x x) refl idCatIso) ⋆⟨ C ⟩ f ∎

  substHomR : {x y y' : ob C} → (p : y ≡ y') → (f : C [ x , y ]) → subst (λ y → C [ x , y ]) p f ≡ f ⋆⟨ C ⟩ morP p
  substHomR {x} {y} {y'} p f = J (λ y' p → subst (λ y → C [ x , y ]) p f ≡ f ⋆⟨ C ⟩ morP p) eqRefl p
    where
    eqRefl : subst (λ y → C [ x , y ]) refl f ≡ f ⋆⟨ C ⟩ mor (subst (λ y → CatIso C y y) refl idCatIso)
    eqRefl = 
     subst (λ y → C [ x , y ]) refl f ≡⟨ substRefl {B = λ y → C [ x , y ]} f ⟩
      f ≡⟨ sym (⋆IdR C f) ⟩
      f ⋆⟨ C ⟩ id C ≡⟨ cong (λ isom →  f ⋆⟨ C ⟩ mor isom) (sym (substRefl {B = λ y → CatIso C y y} idCatIso)) ⟩
      f ⋆⟨ C ⟩ mor (subst (λ y → CatIso C y y) refl idCatIso) ∎

  substHomLR : {x x' y y' : ob C} → (p : x ≡ x') → (q : y ≡ y') → (f : C [ x , y ]) → invP p ⋆⟨ C ⟩ f ⋆⟨ C ⟩ morP q ≡ subst2 (λ x' y' → C [ x' , y' ]) p q f
  substHomLR {x} {x'} {y} {y'} p q f = 
    invP p ⋆⟨ C ⟩ f ⋆⟨ C ⟩ morP q
        ≡⟨ sym (substHomR q (invP p ⋆⟨ C ⟩ f)) ⟩
    subst (λ y' → C [ x' , y' ]) q (invP p ⋆⟨ C ⟩ f)
        ≡⟨ cong (λ f → subst (λ y' → C [ x' , y' ]) q f) (sym (substHomL p f)) ⟩
    subst (λ y' → C [ x' , y' ]) q (subst (λ x' → C [ x' , y ]) p f)
        ≡⟨ subst-subst≡subst2 (λ x' y' → C [ x' , y' ]) p q f ⟩
    subst2 (λ x' y' → C [ x' , y' ]) p q f ∎  
      

  idPPathToIso : {x y : ob C} → (p : x ≡ y) → idP {C = C} ≡ morP p
  idPPathToIso {x} {y} p = (substHomR p (id C)) ∙ (⋆IdL C (morP p))

  reflMorP :  {x : ob C} → morP {x = x} refl ≡ id C
  reflMorP {x} = cong (λ (f : CatIso C x x) → mor f) pathToIso-refl
  
  reflInvP :  {x : ob C} → invP {x = x} refl ≡ id C
  reflInvP {x} = cong (λ (f : CatIso C x x) → inv f) pathToIso-refl
  
  symMorP : {x y : ob C} → (p : x ≡ y) → morP (sym p) ≡ invP p
  symMorP {x} {y} p = J (λ y p → morP (sym p) ≡ invP p) eqRefl p
    where
    eqRefl : morP refl ≡ invP refl
    eqRefl = 
      morP refl ≡⟨ reflMorP ⟩
      id C ≡⟨ sym reflInvP ⟩
      invP refl ∎

  symPathToIso : {x y : ob C} → (p : x ≡ y) → pathToIso {C = C} (sym p) ≡ invIso (pathToIso {C = C} p)
  symPathToIso {x} {y} p = makeIsoPath (pathToIso {C = C} (sym p)) (invIso (pathToIso {C = C} p)) (symMorP p)

  seqPathToIso : {x y z : ob C} → (p : x ≡ y) → (q : y ≡ z) → pathToIso (p ∙ q) ≡ pathToIso p ⋆ᵢ⟨ C ⟩ pathToIso q
  seqPathToIso {x} {y} {z} p q = J (λ z q → pathToIso (p ∙ q) ≡ pathToIso p ⋆ᵢ⟨ C ⟩ pathToIso q)  eqRefl q
    where
    eqRefl : pathToIso (p ∙ refl) ≡ pathToIso p ⋆ᵢ⟨ C ⟩ pathToIso refl
    eqRefl = 
      pathToIso (p ∙ refl) ≡⟨ cong (λ p → pathToIso p) (sym (rUnit p)) ⟩
      pathToIso p ≡⟨ sym (⋆ᵢIdR (pathToIso p)) ⟩
      pathToIso p ⋆ᵢ⟨ C ⟩ idCatIso ≡⟨ cong (λ isom → pathToIso p ⋆ᵢ⟨ C ⟩ isom) (sym pathToIso-refl) ⟩
      pathToIso p ⋆ᵢ⟨ C ⟩ pathToIso refl ∎
