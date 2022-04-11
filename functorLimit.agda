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
open import functorCategories

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓD ℓD' : Level


open Precategory
open NatTrans
open Functor
open Limit
open isLimit
open CatIso

module _ {J : Precategory ℓJ ℓJ'}
         {C : Precategory ℓC ℓC'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄
         (lim : hasLimitShape J D)
         (F : Functor J (functorCat C D)) where

  L : (x : C .ob) → Limit ((eval C D x) ∘F F)
  L x = lim ((eval C D x) ∘F F)

  cx : {H : Functor C D} → (β : Cone F H) → (x : C .ob) → Cone (eval C D x ∘F F) (H ⟅ x ⟆)
  cx {H} β x .N-ob j = β ⟦ j ⟧ ⟦ x ⟧
  cx {H} β x .N-hom {j} {j'} f = cong (λ ν → ν ⟦ x ⟧) (N-hom β f)

  creatFuncLim : Limit F
  creatFuncLim = Lim      
   where
     c : {x y : C .ob} → (f : C [ x , y ]) → Cone ((eval C D y) ∘F F) (head (L x))
     c {x} {y} f .N-ob j = proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫)
     c {x} {y} f .N-hom {j} {j'} g = 
       D .id (head (L x)) ⋆⟨ D ⟩ (proj (L x) j' ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫)
             ≡⟨ sym (⋆Assoc D (D .id (head (L x))) (proj (L x) j') (F ⟅ j' ⟆ ⟪ f ⟫)) ⟩
       D .id (head (L x)) ⋆⟨ D ⟩ proj (L x) j' ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫
             ≡⟨ cong (λ h → h ⋆⟨ D ⟩ F ⟅ j' ⟆ ⟪ f ⟫) (N-hom (cone (islim (L x))) g) ⟩
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
       
       γ : NatTrans H G
       γ .N-ob x = canonicalFact (L x) (cx β x)
       γ .N-hom {x} {y} f = homToLimPath (L y) (H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx β y)) (canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f))) λ j → p
         where
         p : {j : J .ob} → H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx β y) ⋆⟨ D ⟩ proj (L y) j ≡ canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f))⋆⟨ D ⟩ proj (L y) j
         p {j} = 
           (H ⟪ f ⟫ ⋆⟨ D ⟩ canonicalFact (L y) (cx β y)) ⋆⟨ D ⟩ proj (L y) j
                ≡⟨ ⋆Assoc D (H ⟪ f ⟫) (canonicalFact (L y) (cx β y)) (proj (L y) j) ⟩
           H ⟪ f ⟫ ⋆⟨ D ⟩ (canonicalFact (L y) (cx β y) ⋆⟨ D ⟩ proj (L y) j)
               ≡⟨ cong (λ g → H ⟪ f ⟫ ⋆⟨ D ⟩ g) (defCanonicalFact (L y) (cx β y)) ⟩
           H ⟪ f ⟫ ⋆⟨ D ⟩ β ⟦ j ⟧ ⟦ y ⟧
               ≡⟨ N-hom (β ⟦ j ⟧) f ⟩
           β ⟦ j ⟧ ⟦ x ⟧ ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
               ≡⟨ cong (λ g → g ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫) (sym (defCanonicalFact (L x) (cx β x))) ⟩
           (canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ proj (L x) j) ⋆⟨ D ⟩ F ⟅ j ⟆ ⟪ f ⟫
               ≡⟨ ⋆Assoc D (canonicalFact (L x) (cx β x)) (proj (L x) j) (F ⟅ j ⟆ ⟪ f ⟫) ⟩
           canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ (proj (L x) j ⋆⟨ D ⟩ (F ⟅ j ⟆ ⟪ f ⟫))
               ≡⟨ cong (λ g → canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ g) (sym (defCanonicalFact (L y) (c f))) ⟩
           canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ (canonicalFact (L y) (c f) ⋆⟨ D ⟩ proj (L y) j)
               ≡⟨ sym (⋆Assoc D (canonicalFact (L x) (cx β x)) (canonicalFact (L y) (c f)) (proj (L y) j)) ⟩
           canonicalFact (L x) (cx β x) ⋆⟨ D ⟩ canonicalFact (L y) (c f) ⋆⟨ D ⟩ proj (L y) j ∎
           
       factβ : (j : J .ob) → (x : C .ob) → β ⟦ j ⟧ ⟦ x ⟧ ≡ γ ⟦ x ⟧ ⋆⟨ D ⟩ proj (L x) j
       factβ j x = sym (defCanonicalFact (L x) (cx β x))

       αfactβ : β ≡ (γ ◼ natTrans α isNatα)
       αfactβ = makeNatTransPath ⦃ isCatFunct C D ⦄ (funExt λ j → makeNatTransPath (funExt (λ x → factβ j x)))


       γ≡δ : {δ :  NatTrans H G} → β ≡ (δ ◼ natTrans α isNatα) → γ ≡ δ
       γ≡δ {δ} αfactβ' = makeNatTransPath (funExt (λ x → sym (carCanFact (L x) (cx β x) (δ ⟦ x ⟧) (λ j → (sym (cong (λ μ → μ ⟦ j ⟧ ⟦ x ⟧) αfactβ'))))))

  evalPreservLim : {x : C .ob} → (L' : Limit F) → (l : Limit ((eval C D x) ∘F F)) → preservLimit F (eval C D x) L' l
  evalPreservLim {x} L' l = makeIso isom (canonicalMapComp F (eval C D x) L' l) mor≡
    where
    isom : CatIso {C = D} (eval C D x ⟅ head L' ⟆) (head l)
    isom = eval C D x ⦅ unicityLim ⦃ isCatFunct C D ⦄ L' creatFuncLim ⦆ ⋆ᵢ⟨ D ⟩ unicityLim (L x) l

    p : (j : J .ob) → mor isom ⋆⟨ D ⟩ proj l j ≡ eval C D x ⟪ proj L' j ⟫
    p j = 
      mor isom ⋆⟨ D ⟩ proj l j
          ≡⟨ refl ⟩
      (canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ canonicalFact l (cone (islim (L x)))) ⋆⟨ D ⟩ proj l j
          ≡⟨ ⋆Assoc D (canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧) (canonicalFact l (cone (islim (L x)))) (proj l j) ⟩
      canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ (canonicalFact l (cone (islim (L x))) ⋆⟨ D ⟩ proj l j)
          ≡⟨ cong (λ f →  eval C D x ⟪ canonicalFact creatFuncLim (cone (islim L')) ⟫ ⋆⟨ D ⟩ f) (defCanonicalFact l (cone (islim (L x)))) ⟩
      canonicalFact creatFuncLim (cone (islim L')) ⟦ x ⟧ ⋆⟨ D ⟩ proj (L x) j
          ≡⟨ refl ⟩
      canonicalFact (L x) (cx (cone (islim L')) x) ⋆⟨ D ⟩ proj (L x) j
          ≡⟨ defCanonicalFact (L x) (cx (cone (islim L')) x) ⟩  
      proj L' j ⟦ x ⟧ ∎

    mor≡ : mor isom ≡ canonicalMapComp F (eval C D x) L' l
    mor≡ = carCanFact l (coneComp F (eval C D x) L' l) (mor isom) p
    
module _ {J : Precategory ℓJ ℓJ'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄
         (lim : hasLimitShape J D) where
         
  functLim : Functor (functorCat J D) D
  functLim = LimF
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

    LimF : Functor (functorCat J D) D
    LimF .F-ob F = head (lim F)
    LimF .F-hom {F} {G} α = canonicalFact (lim G) (c α)
    LimF .F-id {F} = sym (carCanFact (lim F) (c (id (functorCat J D) F)) (id D (head (lim F))) p)
      where
      p : (j : J .ob) → id D (head (lim F)) ⋆⟨ D ⟩ proj (lim F) j ≡ proj (lim F) j ⋆⟨ D ⟩ id D (F ⟅ j ⟆)
      p j = 
        id D (head (lim F)) ⋆⟨ D ⟩ proj (lim F) j
          ≡⟨ ⋆IdL D (proj (lim F) j) ⟩
        proj (lim F) j
          ≡⟨ sym (⋆IdR D (proj (lim F) j)) ⟩
        proj (lim F) j ⋆⟨ D ⟩ id D (F ⟅ j ⟆) ∎
    LimF .F-seq {F} {G} {H} α β = sym (carCanFact (lim H) (c (α ●ᵛ β)) (F-hom LimF α ⋆⟨ D ⟩ F-hom LimF β) q)
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

  isLimFunctLim : (F : Functor J D) → isLimit F (functLim ⟅ F ⟆)
  isLimFunctLim F = islim (lim F)

module _ {J : Precategory ℓJ ℓJ'}
         {D : Precategory ℓD ℓD'}
         ⦃ isCatD : isCategory D ⦄
         (colim : hasColimitShape J D) where

  functColim : Functor (functorCat J D) D
  functColim  = Colim
    where
    c : Functor (functorCat (J ^op) (D ^op) ⦃ isCatOp D isCatD ⦄ ) (D ^op)
    c = functLim ⦃ isCatOp D isCatD ⦄ λ G → elim-^opF G Limit (colim (G ^opF))

    Colim : Functor (functorCat J D) D
    Colim .F-ob F = c ⟅ F ^opF ⟆
    Colim .F-hom {F} {G} α = c ⟪ α ^opN ⟫
    Colim .F-id {F} = cong (F-hom c) ^opN-id ∙ F-id c
    Colim .F-seq {F} {G} {H} α β = cong (F-hom c) (^opN-seq α β) ∙ F-seq c (β ^opN) (α ^opN)

  isColimFunctColim : (F : Functor J D) → isColimit F (functColim ⟅ F ⟆)
  isColimFunctColim F = transport (cong (λ x → isLimit (F ^opF) x) ((cong (λ G → head (colim G)) (sym (^opF-invol F))) ∙ sym (transportRefl (head (colim (F ^opF ^opF)))))) (islim (colim F))

  module _ {C : Precategory ℓC ℓC'}
           (F : Functor J (functorCat C D)) where
 
    creatFuncColim : Colimit F
    creatFuncColim = Colim
      where
      op : (Functor J (functorCat C D)) →  Functor (J ^op) (functorCat (C ^op) (D ^op) ⦃ isCatOp D isCatD ⦄)
      op G .F-ob j = (G ⟅ j ⟆) ^opF
      op G .F-hom {j'} {j} f = G ⟪ f ⟫ ^opN 
      op G .F-id {j} = cong (λ α → α ^opN) (F-id G) ∙ ^opN-id
      op G .F-seq f g = cong (λ α → α ^opN) (F-seq G g f) ∙ ^opN-seq (G ⟪ g ⟫) (G ⟪ f ⟫)

      l : (G : Functor J (functorCat C D)) → Limit (op G)
      l G = creatFuncLim ⦃ isCatOp D isCatD ⦄ (λ H → elim-^opF H Limit (colim (H ^opF))) (op G)

      lF = l F

      Colim : Colimit F 
      Colim .head = head lF ^opF
      Colim .islim .cone .N-ob j = elim-^opF (F ⟅ j ⟆) (λ G → functorCat C D [ G , head lF ^opF ]) (proj lF j ^opN)
      Colim .islim .cone .N-hom {j'} {j} f = {!!}
        where
        p : elim-^opF (F ⟅ j ⟆) (λ G → functorCat C D [ G , head lF ^opF ]) (proj lF j ^opN) ●ᵛ idTrans (head lF ^opF) ≡ F ⟪ f ⟫ ●ᵛ elim-^opF (F ⟅ j' ⟆) (λ G → functorCat C D [ G , head lF ^opF ]) (proj lF j' ^opN)
        p =
          elim-^opF (F ⟅ j ⟆) (λ G → functorCat C D [ G , head lF ^opF ]) (proj lF j ^opN) ●ᵛ idTrans (head lF ^opF) ≡⟨ {!!} ⟩
          F ⟪ f ⟫ ●ᵛ elim-^opF (F ⟅ j' ⟆) (λ G → functorCat C D [ G , head lF ^opF ]) (proj lF j' ^opN) ∎
        
      Colim .islim .up = {!!}
