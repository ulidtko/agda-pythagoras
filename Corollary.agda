module Corollary where

open import Algebra
open import Function
open import Algebra.Definitions
open import Algebra.Structures
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq.≡-Reasoning

open import NatStar
open import NatStarProperties

import Cancel
open Cancel {_} {_} {NatStar} (_≡_)
open import CancellativeAbelianMonoid

isCancellativeAbelianMonoid : 
  IsCancellativeAbelianMonoid _≡_ _*_ one
isCancellativeAbelianMonoid
  = record {
      isCommutativeMonoid = *-isCommutativeMonoid
    ; cancel = cancel-*-left
    }

m : CancellativeAbelianMonoid Level.zero Level.zero
m = record {
      Carrier = NatStar
    ; _≈_ = _≡_
    ; _∙_ = _*_
    ; ε   = one
    ; isCancellativeAbelianMonoid = isCancellativeAbelianMonoid
    }

open import Noether
import Property
open Property Level.zero Level.zero m
import Theorem 
open Theorem Level.zero m

-- the original proof of 'two is prime' is written
-- by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

-- lemma1 : 2 isPrime
-- lemma1 = {!!}
postulate lemma1 : (succ one) isPrime

-- lemma2 : Noether Carrier (multiple 2)
-- lemma2 = {!!}
postulate lemma2 : Noether Carrier (multiple (succ one))

corollary : (succ one) isNotSquare
corollary = theorem (succ one) lemma1 lemma2

