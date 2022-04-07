{-# OPTIONS --cubical #-}


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Base

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

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄
         (F : Functor J (functorCat C D)) where

  creatFuncLim : ((G : Functor J D) → Limit G) → Limit F
  creatFuncLim lim = Lim      
   where
     L : (x : C .ob) → Limit ((eval C D x) ∘F F)
     L x = lim ((eval C D x) ∘F F)
      
     c : {x y : C .ob} → (f : C [ x , y ]) → Cone ((eval C D y) ∘F F) (head (L x))
     c {x} {y} f .N-ob j = proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫)
     c {x} {y} f .N-hom {j} {j'} g = 
       D .id (head (L x)) ⋆⟨ D ⟩ (proj (L x) j' ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫)
             ≡⟨ sym (⋆Assoc D (D .id (head (L x))) (proj (L x) j') (F ⟅ j' ⟆ ⟪ f ⟫)) ⟩
       D .id (head (L x)) ⋆⟨ D ⟩ proj (L x) j' ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫
             ≡⟨ cong (λ h → h ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫) (N-hom (cone (islim (lim ((eval C D x) ∘F F)))) g) ⟩
       proj (L x) j ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ x ⟧ ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫
             ≡⟨ ⋆Assoc D (proj (L x) j) (F ⟪ g ⟫ ⟦ x ⟧) (F ⟅ j' ⟆ ⟪ f ⟫) ⟩
       proj (L x) j ⋆⟨ D ⟩ (F ⟪ g ⟫ ⟦ x ⟧ ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫)
             ≡⟨ cong (λ h → proj (L x) j ⋆⟨ D ⟩ h) (sym (N-hom (F ⟪ g ⟫) f)) ⟩
       proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ y ⟧)
             ≡⟨ sym (⋆Assoc D (proj (L x) j) (F ⟅ j ⟆ ⟪ f ⟫) (F ⟪ g ⟫ ⟦ y ⟧))⟩
       (proj (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) ⋆⟨ D ⟩ F ⟪ g ⟫ ⟦ y ⟧ ∎

        
     idProj : {j : J .ob} → (x : C .ob) → id D (head (L x)) ⋆⟨ D ⟩  proj (L x) j ≡ proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆) ⟪ id C x ⟫
     idProj {j} x =
       id D (head (L x)) ⋆⟨ D ⟩ proj (L x) j
            ≡⟨ ⋆IdL D (proj (L x) j) ⟩
       proj (L x) j
            ≡⟨ sym (⋆IdR D (proj (L x) j)) ⟩
       proj (L x) j ⋆⟨ D ⟩ id D (F ⟅ j ⟆ ⟅ x ⟆)
            ≡⟨ cong (λ f → proj (L x) j ⋆⟨ D ⟩ f) (sym (F-id (F ⟅ j ⟆))) ⟩ 
       proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆) ⟪ id C x ⟫ ∎

     compProj : {j : J .ob} → {x y z : C .ob} → (f : C [ x , y ]) → (g : C [ y , z ]) →
                (canonicalFact (L y) (c f) ⋆⟨ D ⟩ canonicalFact (L z) (c g)) ⋆⟨ D ⟩ proj (L z) j ≡ proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆) ⟪ f ⋆⟨ C ⟩ g ⟫
     compProj {j} {x} {y} {z} f g = 
       (canonicalFact (L y) (c f) ⋆⟨ D ⟩ canonicalFact (L z) (c g)) ⋆⟨ D ⟩ proj (L z) j
            ≡⟨ ⋆Assoc D (canonicalFact (L y) (c f)) (canonicalFact (L z) (c g)) (proj (L z) j) ⟩
       canonicalFact (L y) (c f) ⋆⟨ D ⟩ (canonicalFact (L z) (c g) ⋆⟨ D ⟩ proj (L z) j)
            ≡⟨ cong (λ g → canonicalFact (L y) (c f) ⋆⟨ D ⟩ g) (defCanonicalFact (L z) (c g)) ⟩
       canonicalFact (L y) (c f) ⋆⟨ D ⟩ (proj (L y) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫)
            ≡⟨ sym (⋆Assoc D (canonicalFact (L y) (c f)) (proj (L y) j) ((F ⟅ j ⟆) ⟪ g ⟫)) ⟩
       (canonicalFact (L y) (c f) ⋆⟨ D ⟩ proj (L y) j) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫
            ≡⟨ cong (λ f → f ⋆⟨ D ⟩ (F ⟅ j ⟆) ⟪ g ⟫) (defCanonicalFact (L y) (c f)) ⟩
       (proj (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫
            ≡⟨ ⋆Assoc D (proj (L x) j) ((F ⟅ j ⟆) ⟪ f ⟫) (F ⟅ j ⟆ ⟪ g ⟫) ⟩
       proj (L x) j ⋆⟨ D ⟩ ((F ⟅ j ⟆) ⟪ f ⟫ ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ g ⟫)
            ≡⟨ cong (λ f → proj (L x) j ⋆⟨ D ⟩ f) (sym (F-seq (F ⟅ j ⟆) f g)) ⟩
       proj (L x) j ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⋆⟨ C ⟩ g ⟫ ∎

     G : Functor C D
     G .F-ob x = head (L x)
     G .F-hom {x} {y} f = canonicalFact (L y) (c f)
     G .F-id {x} = sym (carCanFact (L x) (c (id C x)) (id D (head (L x))) λ j → idProj x)
     G .F-seq {x} {y} {z} f g = sym (carCanFact (L z) (c (f ⋆⟨ C ⟩ g)) (canonicalFact (L y) (c f) ⋆⟨ D ⟩ canonicalFact (L z) (c g)) λ j → compProj f g)

     α : (j : J .ob) → NatTrans G (F ⟅ j ⟆)
     α j .N-ob x = proj (L x) j
     α j .N-hom {x} {y} f = defCanonicalFact (L y) (c f)

     comProjLim : {j j' : J .ob} → (f : J [ j , j' ]) → (x : C .ob) → (id D (head (L x))) ⋆⟨ D ⟩ proj (L x) j'  ≡ proj (L x) j ⋆⟨ D ⟩ F ⟪ f ⟫ ⟦ x ⟧
     comProjLim f x = N-hom (cone (islim (L x))) f

     isNatα : N-hom-Type (constF G) F α
     isNatα f = makeNatTransPath (funExt (comProjLim f))

     Lim : Limit F
     Lim .head = G
     Lim .islim .cone = natTrans α isNatα
     Lim .islim .up {H} β = (γ , αfactβ) , λ {(δ , αfactβ') → makeFactPath J (functorCat C D) ⦃ isCatFunct C D ⦄ { H } { G } { F } β (Lim .islim .cone) (γ , αfactβ) (δ , αfactβ') (γ≡δ αfactβ')}
       where
       cx : (x : C .ob) → Cone (eval C D x ∘F F) (H ⟅ x ⟆)
       cx x .N-ob j = β ⟦ j ⟧ ⟦ x ⟧
       cx x .N-hom {j} {j'} f = cong (λ ν → ν ⟦ x ⟧) (N-hom β f)

       γ : NatTrans H G
       γ .N-ob x = canonicalFact (L x) (cx x)
       γ .N-hom {x} {y} f = homToLimPath (L y) (H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx y)) (canonicalFact (L x) (cx x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f))) λ j → p
         where
         p : {j : J .ob} → H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx y) ⋆⟨ D ⟩ proj (L y) j ≡ canonicalFact (L x) (cx x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f))⋆⟨ D ⟩ proj (L y) j
         p {j} = 
           (H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx y)) ⋆⟨ D ⟩ proj (L y) j
                ≡⟨ ⋆Assoc D (H ⟪ f ⟫) (canonicalFact (L y) (cx y)) (proj (L y) j) ⟩
           H ⟪ f ⟫ ⋆⟨ D ⟩ (canonicalFact (L y) (cx y) ⋆⟨ D ⟩ proj (L y) j)
               ≡⟨ cong (λ g → H ⟪ f ⟫ ⋆⟨ D ⟩ g) (defCanonicalFact (L y) (cx y)) ⟩
           H ⟪ f ⟫ ⋆⟨ D ⟩ β ⟦ j ⟧ ⟦ y ⟧
               ≡⟨ N-hom (β ⟦ j ⟧) f ⟩
           β ⟦ j ⟧ ⟦ x ⟧ ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
               ≡⟨ cong (λ g → g ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) (sym (defCanonicalFact (L x) (cx x))) ⟩
           (canonicalFact (L x) (cx x) ⋆⟨ D ⟩ proj (L x) j) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
               ≡⟨ ⋆Assoc D (canonicalFact (L x) (cx x)) (proj (L x) j) (F ⟅ j ⟆ ⟪ f ⟫) ⟩
           canonicalFact (L x) (cx x) ⋆⟨ D ⟩ (proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫))
               ≡⟨ cong (λ g → canonicalFact (L x) (cx x) ⋆⟨ D ⟩ g) (sym (defCanonicalFact (L y) (c f))) ⟩
           canonicalFact (L x) (cx x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f) ⋆⟨ D ⟩ proj (L y) j)
               ≡⟨ sym (⋆Assoc D (canonicalFact (L x) (cx x)) (canonicalFact (L y) (c f)) (proj (L y) j)) ⟩
           canonicalFact (L x) (cx x) ⋆⟨ D ⟩ canonicalFact (L y) (c f) ⋆⟨ D ⟩ proj (L y) j ∎
           
       factβ : (j : J .ob) → (x : C .ob) → β ⟦ j ⟧ ⟦ x ⟧ ≡ γ ⟦ x ⟧ ⋆⟨ D ⟩ proj (L x) j
       factβ j x = sym (defCanonicalFact (L x) (cx x))

       αfactβ : β ≡ (γ ◼ natTrans α isNatα)
       αfactβ = makeNatTransPath ⦃ isCatFunct C D ⦄ (funExt λ j → makeNatTransPath (funExt (λ x → factβ j x)))


       γ≡δ : {δ :  NatTrans H G} → β ≡ (δ ◼ natTrans α isNatα) → γ ≡ δ
       γ≡δ {δ} αfactβ' = makeNatTransPath (funExt (λ x → sym (carCanFact (L x) (cx x) (δ ⟦ x ⟧) (λ j → (sym (cong (λ μ → μ ⟦ j ⟧ ⟦ x ⟧) αfactβ'))))))
       
module _ {J : Precategory ℓJ ℓJ'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄  where

  
  functLim : ((G : Functor J D) → Limit G) → Functor (functorCat J D) D
  functLim lim = L
    where
    c : {F G : Functor J D} → (α : NatTrans F G) → Cone G (head (lim F))
    c {F} {G} α .N-ob j = proj (lim F) j ⋆⟨ D ⟩ α ⟦ j ⟧
    c {F} {G} α .N-hom {j} {j'} f =
      id D (head (lim F)) ⋆⟨ D ⟩ (proj (lim F) j' ⋆⟨ D ⟩ α ⟦ j' ⟧)
         ≡⟨ ⋆IdL D (proj (lim F) j' ⋆⟨ D ⟩ α ⟦ j' ⟧) ⟩
      proj (lim F) j' ⋆⟨ D ⟩ α ⟦ j' ⟧
         ≡⟨ cong (λ g →  g ⋆⟨ D ⟩ α ⟦ j' ⟧) (sym (⋆IdL D (proj (lim F) j'))) ⟩
      (id D (head (lim F)) ⋆⟨ D ⟩ proj (lim F) j') ⋆⟨ D ⟩ α ⟦ j' ⟧
         ≡⟨  cong (λ g → g ⋆⟨ D ⟩ α ⟦ j' ⟧) (N-hom (cone (islim (lim F))) f) ⟩
      (proj (lim F) j ⋆⟨ D ⟩ F ⟪ f ⟫) ⋆⟨ D ⟩ α ⟦ j' ⟧
         ≡⟨ ⋆Assoc D (proj (lim F) j) (F ⟪ f ⟫) (α ⟦ j' ⟧) ⟩
      proj (lim F) j ⋆⟨ D ⟩ (F ⟪ f ⟫ ⋆⟨ D ⟩ α ⟦ j' ⟧)
         ≡⟨ cong (λ g → proj (lim F) j ⋆⟨ D ⟩ g) (N-hom α f) ⟩
      proj (lim F) j ⋆⟨ D ⟩ (α ⟦ j ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫)
         ≡⟨ sym (⋆Assoc D (proj (lim F) j) (α ⟦ j ⟧) (G ⟪ f ⟫)) ⟩
      (proj (lim F) j ⋆⟨ D ⟩ α ⟦ j ⟧) ⋆⟨ D ⟩ G ⟪ f ⟫ ∎

    L : Functor (functorCat J D) D
    L .F-ob F = head (lim F)
    L .F-hom {F} {G} α = canonicalFact (lim G) (c α)
    L .F-id {F} = sym (carCanFact (lim F) (c (id (functorCat J D) F)) (id D (head (lim F))) p)
      where
      p : (j : J .ob) → id D (head (lim F)) ⋆⟨ D ⟩ proj (lim F) j ≡ proj (lim F) j ⋆⟨ D ⟩ id D (F ⟅ j ⟆)
      p j = 
        id D (head (lim F)) ⋆⟨ D ⟩ proj (lim F) j
          ≡⟨ ⋆IdL D (proj (lim F) j) ⟩
        proj (lim F) j
          ≡⟨ sym (⋆IdR D (proj (lim F) j)) ⟩
        proj (lim F) j ⋆⟨ D ⟩ id D (F ⟅ j ⟆) ∎
    L .F-seq {F} {G} {H} α β = sym (carCanFact (lim H) (c (α ●ᵛ β)) (F-hom L α ⋆⟨ D ⟩ F-hom L β) q)
      where
      q : (j : J .ob) → (canonicalFact (lim G) (c α) ⋆⟨ D ⟩ canonicalFact (lim H) (c β)) ⋆⟨ D ⟩ proj (lim H) j ≡ proj (lim F) j ⋆⟨ D ⟩ (α ●ᵛ β) ⟦ j ⟧
      q j = 
        (canonicalFact (lim G) (c α) ⋆⟨ D ⟩ canonicalFact (lim H) (c β)) ⋆⟨ D ⟩ proj (lim H) j
            ≡⟨ ⋆Assoc D (canonicalFact (lim G) (c α)) (canonicalFact (lim H) (c β)) (proj (lim H) j) ⟩
        canonicalFact (lim G) (c α) ⋆⟨ D ⟩ (canonicalFact (lim H) (c β) ⋆⟨ D ⟩ proj (lim H) j)
            ≡⟨ cong (λ f → canonicalFact (lim G) (c α) ⋆⟨ D ⟩ f) (defCanonicalFact (lim H) (c β)) ⟩
        canonicalFact (lim G) (c α) ⋆⟨ D ⟩ (proj (lim G) j ⋆⟨ D ⟩ β ⟦ j ⟧)
            ≡⟨ sym (⋆Assoc D (canonicalFact (lim G) (c α)) (proj (lim G) j) (β ⟦ j ⟧)) ⟩
        (canonicalFact (lim G) (c α) ⋆⟨ D ⟩ proj (lim G) j) ⋆⟨ D ⟩ β ⟦ j ⟧
            ≡⟨ cong (λ f → f ⋆⟨ D ⟩ β ⟦ j ⟧) (defCanonicalFact (lim G) (c α)) ⟩
        (proj (lim F) j ⋆⟨ D ⟩ α ⟦ j ⟧) ⋆⟨ D ⟩ β ⟦ j ⟧
            ≡⟨ ⋆Assoc D (proj (lim F) j) (α ⟦ j ⟧) (β ⟦ j ⟧) ⟩
        proj (lim F) j ⋆⟨ D ⟩ (α ●ᵛ β) ⟦ j ⟧ ∎

functColim : {J : Precategory ℓJ ℓJ'} → {D : Precategory ℓD ℓD'} → ⦃ isCatD : isCategory D ⦄ → ((G : Functor J D) → Colimit G) → Functor (functorCat J D) D
functColim {J = J} {D = D} ⦃ isCatD ⦄ colim = Colim
  where
  c = functLim {J = J ^op} {D = D ^op} ⦃ isCatOp D isCatD ⦄ λ G → transport (cong Limit (^opF-invol G)) (colim (G ^opF))

  Colim : Functor (functorCat J D) D
  Colim .F-ob F = c .F-ob (F ^opF)
  Colim .F-hom {F} {G} α = c .F-hom (α ^opN)
  Colim .F-id {F} = cong (F-hom c) ^opN-id ∙ F-id c
  Colim .F-seq {F} {G} {H} α β = cong (F-hom c) (^opN-seq α β) ∙ F-seq c (β ^opN) (α ^opN)

