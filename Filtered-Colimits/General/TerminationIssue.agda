module Filtered-Colimits.General.TerminationIssue where

open import Cubical.Foundations.Prelude


module test1 {ℓB ℓX ℓY ℓZ : Level}
             {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ} {B : Type ℓB}
             {X→B : X → B} {Y→X : Y → X} {Z→Y : Z → Y} where
 
  data A : Type (ℓ-max ℓX (ℓ-max ℓY ℓZ)) where
    fromX : X → A
    fromY : Y → A
    fromZ : Z → A

  f : A → B
  f (fromX x) = X→B x
  f (fromY y) = f (fromX (Y→X y))
  f (fromZ z) = f (fromY (Z→Y z))

module test2 {ℓB ℓX ℓY : Level}
             {X : Type ℓX} {Y : Type ℓY} {B : Type ℓB}
             {X→B : X → B} {Y→X : Y → X} where
             
  data A' : Type (ℓ-max ℓX ℓY) where
    fromX : X → A'
    fromY : Y → A'
  
  f' : A' → B
  f' (fromX x) = X→B x
  f' (fromY y) = f' (fromX (Y→X y))

module test3 {ℓB ℓX : Level}
             {X : Type ℓX} {B : Type ℓB}
             {X→B : X → B} {B→B : B → B} where

  data A : Type ℓX where
    fromX : X → A
    s1 : A → A
    s2 : A → A

  f : A → B
  f (fromX x) = X→B x
  f (s1 a) = B→B (f a)
  f (s2 a) = f (s1 a)
  

module test4 {ℓB ℓC ℓX ℓY : Level}
             {X : Type ℓX} {Y : Type ℓY} {B : Type ℓB} {C : Type ℓC}
             {X→B : X → B} {Y→C : Y → C} {C→B : C → B} {B→C : B → C} where

  mutual 
    data A : Type (ℓ-max ℓX ℓY) where
      fromX : X → A
      s : A → A' → A
  
    data A' : Type (ℓ-max ℓX ℓY) where
      fromY : Y → A'
      s' : A' → A'
  --    s : A' → A'


  postulate A→A' : A → A'
  
  mutual
    f : A → B
    f' : A → A' → C

    f (fromX x) = X→B x
    f (s a a') = C→B (f' a (A→A' a))

    f' a (fromY y) = Y→C y
    f' a (s' a') with (A→A' a)
    ... | fromY y = {!!}
    ... | s' a' = {!!}
