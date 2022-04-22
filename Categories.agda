{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma

open import IsoCat
open import Lemma

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' : Level

open Precategory
open CatIso

module _ (C : Precategory ℓC ℓC')
         ⦃ isCatC : isCategory C ⦄ where

  isCat^op : isCategory (C ^op)
  isCat^op .isSetHom = isSetHom isCatC

-- Doesn't work because of eta equality for categories
--instance  
--  ⦃isCat^op⦄ : {C : Precategory ℓC ℓC'} → ⦃ isCatC : isCategory C ⦄ → isCategory (C ^op)
--  ⦃isCat^op⦄ {C = C} ⦃ isCatC ⦄ = isCat^op C

module _ (C : Precategory ℓC ℓC') where

  morP : {x y : ob C} → (p : x ≡ y) → C [ x , y ]
  morP {x} {y} p = mor (pathToIso {C = C} x y p)

  invP : {x y : ob C} → (p : x ≡ y) → C [ y , x ]
  invP {x} {y} p = inv (pathToIso {C = C} x y p)

  secMorP : {x y : ob C} → (p : x ≡ y) → invP p ⋆⟨ C ⟩ morP p ≡ id C y
  secMorP {x} {y} p = sec (pathToIso {C = C} x y p)
  
  retMorP : {x y : ob C} → (p : x ≡ y) → morP p ⋆⟨ C ⟩ invP p ≡ id C x
  retMorP {x} {y} p = ret (pathToIso {C = C} x y p)

  reflMorP :  {x : ob C} → morP refl ≡ id C x
  reflMorP {x} = cong mor (substRefl {B = λ x → CatIso {C = C} x x} (idIso x))

  substHomL : {x x' y : ob C} → (p : x ≡ x') → (f : C [ x , y ]) → subst (λ x → C [ x , y ]) p f ≡ invP p ⋆⟨ C ⟩ f
  substHomL {x} {x'} {y} p f = J (λ x' p → subst (λ x → C [ x , y ]) p f ≡ invP p ⋆⟨ C ⟩ f) eqRefl p
    where
    eqRefl : subst (λ x → C [ x , y ]) refl f ≡ inv (subst (λ x → CatIso {C = C} x x) refl (idIso x)) ⋆⟨ C ⟩ f
    eqRefl = 
      subst (λ x → C [ x , y ]) refl f ≡⟨ substRefl {B = λ x → C [ x , y ]} f ⟩
      f ≡⟨ sym (⋆IdL C f) ⟩
      id C x ⋆⟨ C ⟩ f ≡⟨ cong (λ isom →  inv isom ⋆⟨ C ⟩ f) (sym (substRefl {B = λ x → CatIso {C = C} x x} (idIso x))) ⟩
      inv (subst (λ x → CatIso {C = C} x x) refl (idIso x)) ⋆⟨ C ⟩ f ∎

  substHomR : {x y y' : ob C} → (p : y ≡ y') → (f : C [ x , y ]) → subst (λ y → C [ x , y ]) p f ≡ f ⋆⟨ C ⟩ morP p
  substHomR {x} {y} {y'} p f = J (λ y' p → subst (λ y → C [ x , y ]) p f ≡ f ⋆⟨ C ⟩ morP p) eqRefl p
    where
    eqRefl : subst (λ y → C [ x , y ]) refl f ≡ f ⋆⟨ C ⟩ mor (subst (λ y → CatIso {C = C} y y) refl (idIso y))
    eqRefl = 
      subst (λ y → C [ x , y ]) refl f ≡⟨ substRefl {B = λ y → C [ x , y ]} f ⟩
      f ≡⟨ sym (⋆IdR C f) ⟩
      f ⋆⟨ C ⟩ id C y ≡⟨ cong (λ isom →  f ⋆⟨ C ⟩ mor isom) (sym (substRefl {B = λ y → CatIso {C = C} y y} (idIso y))) ⟩
      f ⋆⟨ C ⟩ mor (subst (λ y → CatIso {C = C} y y) refl (idIso y)) ∎

  substHomLR : {x x' y y' : ob C} → (p : x ≡ x') → (q : y ≡ y') → (f : C [ x , y ]) → invP p ⋆⟨ C ⟩ f ⋆⟨ C ⟩ morP q ≡ subst2 (λ x' y' → C [ x' , y' ]) p q f
  substHomLR {x} {x'} {y} {y'} p q f = 
    invP p ⋆⟨ C ⟩ f ⋆⟨ C ⟩ morP q
        ≡⟨ sym (substHomR q (invP p ⋆⟨ C ⟩ f)) ⟩
    subst (λ y' → C [ x' , y' ]) q (invP p ⋆⟨ C ⟩ f)
        ≡⟨ cong (λ f → subst (λ y' → C [ x' , y' ]) q f) (sym (substHomL p f)) ⟩
    subst (λ y' → C [ x' , y' ]) q (subst (λ x' → C [ x' , y ]) p f)
        ≡⟨ subst-subst≡subst2 (λ x' y' → C [ x' , y' ]) p q f ⟩
    subst2 (λ x' y' → C [ x' , y' ]) p q f ∎  
      
  idPExp : {x y : ob C} → (p : x ≡ y) → C [ x , y ]
  idPExp p = idP {C = C} {p = p}

  idPPathToIso : {x y : ob C} → (p : x ≡ y) → idPExp p ≡ morP p
  idPPathToIso {x} {y} p = (substHomR p (id C x)) ∙ (⋆IdL C (morP p))
  
  module _ ⦃ isCatC : isCategory C ⦄ where
    reflPathToIso : {x : ob C} → pathToIso {C = C} x x refl ≡ idIso x
    reflPathToIso {x} = makeIsoPath (pathToIso x x refl) (idIso x) reflMorP

    reflInvP :  {x : ob C} → invP refl ≡ id C x
    reflInvP = cong inv reflPathToIso
  
    symMorP : {x y : ob C} → (p : x ≡ y) → morP (sym p) ≡ invP p
    symMorP {x} {y} p = J (λ y p → morP (sym p) ≡ invP p) eqRefl p
      where
      eqRefl : morP refl ≡ invP refl
      eqRefl = 
        morP refl ≡⟨ cong mor reflPathToIso ⟩
        id C x ≡⟨ cong inv (sym reflPathToIso) ⟩
        invP refl ∎
    
    symPathToIso : {x y : ob C} → (p : x ≡ y) → pathToIso {C = C} y x (sym p) ≡ invIso (pathToIso {C = C} x y p)
    symPathToIso {x} {y} p = makeIsoPath (pathToIso {C = C} y x (sym p)) (invIso (pathToIso {C = C} x y p)) (symMorP p)

    seqPathToIso : {x y z : ob C} → (p : x ≡ y) → (q : y ≡ z) → pathToIso x z (p ∙ q) ≡ pathToIso x y p ⋆ᵢ⟨ C ⟩ pathToIso y z q
    seqPathToIso {x} {y} {z} p q = J (λ z q → pathToIso x z (p ∙ q) ≡ pathToIso x y p ⋆ᵢ⟨ C ⟩ pathToIso y z q)  eqRefl q
      where
      eqRefl : pathToIso x y (p ∙ refl) ≡ pathToIso x y p ⋆ᵢ⟨ C ⟩ pathToIso y y refl
      eqRefl = 
        pathToIso x y (p ∙ refl) ≡⟨ cong (λ p → pathToIso x y p) (sym (rUnit p)) ⟩
        pathToIso x y p ≡⟨ sym (⋆ᵢIdR (pathToIso x y p)) ⟩
        pathToIso x y p ⋆ᵢ⟨ C ⟩ idIso y ≡⟨ cong (λ isom → pathToIso x y p ⋆ᵢ⟨ C ⟩ isom) (sym reflPathToIso) ⟩
        pathToIso x y p ⋆ᵢ⟨ C ⟩ pathToIso y y refl ∎


record Category ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  field
    cat : Precategory ℓ ℓ'
    instance ⦃ isCat ⦄ : isCategory cat

ProdCat : (C : Precategory ℓC ℓC') → (D : Precategory ℓD ℓD') → Precategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
ProdCat C D .ob = ob C × ob D
ProdCat C D .Hom[_,_] (x , y) (x' , y') = C [ x , x' ] × D [ y , y' ]
ProdCat C D .id (x , y) = (id C x) , (id D y)
ProdCat C D ._⋆_ (f , g) (f' , g') = (f ⋆⟨ C ⟩ f') , (g ⋆⟨ D ⟩ g')
ProdCat C D .⋆IdL (f , g) = ≡-× (⋆IdL C f) (⋆IdL D g)
ProdCat C D .⋆IdR (f , g) = ≡-× (⋆IdR C f) (⋆IdR D g)
ProdCat C D .⋆Assoc (f , g) (f' , g') (f'' , g'') = ≡-× (⋆Assoc C f f' f'') (⋆Assoc D g g' g'')
