module CancellativeAbelianMonoid where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Algebra
open import Algebra.Definitions
open import Algebra.Structures
open import Level
open import Relation.Binary

import Cancel

record IsCancellativeAbelianMonoid 
         {a l} {A : Set a} (≈ : Rel A l) (_∙_ : Op₂ A)
         (ε : A) : Set (a ⊔ l) where
  open Algebra.Definitions ≈
  open Cancel ≈
  field
    isCommutativeMonoid : IsCommutativeMonoid ≈ _∙_ ε
    cancel : Cancel _∙_

  open IsCommutativeMonoid isCommutativeMonoid public

record CancellativeAbelianMonoid c l : Set (suc (c ⊔ l)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier l
    _∙_     : Op₂ Carrier
    ε       : Carrier
    isCancellativeAbelianMonoid : IsCancellativeAbelianMonoid _≈_ _∙_ ε

  open IsCancellativeAbelianMonoid isCancellativeAbelianMonoid public

  commutativeMonoid : CommutativeMonoid c l
  commutativeMonoid 
    = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public 
    using (setoid; semigroup; rawMonoid; monoid)
