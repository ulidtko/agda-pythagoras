open import Level
open import CancellativeAbelianMonoid

module Property
  (a l : Level)
  (m : CancellativeAbelianMonoid a l)
  where

open import Algebra
open import Algebra.Definitions
open import Algebra.Structures
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Unary

open import Cancel

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

Carrier : Set a
Carrier = CancellativeAbelianMonoid.Carrier m

infixl 7 _∙_
infix  4 _≈_

_≈_ : Carrier -> Carrier -> Set l
_≈_ = CancellativeAbelianMonoid._≈_ m

_∙_ : Carrier -> Carrier -> Carrier
_∙_ = CancellativeAbelianMonoid._∙_ m

ε : Carrier
ε = CancellativeAbelianMonoid.ε m

----
semigroup : Semigroup a l
semigroup = CancellativeAbelianMonoid.semigroup m

isSemigroup : IsSemigroup _≈_ _∙_
isSemigroup = Semigroup.isSemigroup semigroup
----

assoc : Associative _≈_ _∙_
assoc = IsSemigroup.assoc isSemigroup

∙-cong : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
∙-cong = IsSemigroup.∙-cong isSemigroup

----
≈-setoid : Setoid a l
≈-setoid = Semigroup.setoid semigroup

isPreorder : IsPreorder _≡_ _≈_
isPreorder = Setoid.isPreorder ≈-setoid
----

≈-refl : Reflexive _≈_
≈-refl = IsPreorder.refl isPreorder

≈-trans : Transitive _≈_
≈-trans = IsPreorder.trans isPreorder

----
isEquivalence : IsEquivalence _≈_
isEquivalence = Setoid.isEquivalence ≈-setoid
----

≈-sym : Symmetric _≈_
≈-sym = IsEquivalence.sym isEquivalence

----
commutativeMonoid : CommutativeMonoid a l
commutativeMonoid = CancellativeAbelianMonoid.commutativeMonoid m

isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε
isCommutativeMonoid 
  = CommutativeMonoid.isCommutativeMonoid commutativeMonoid
----

comm : Commutative _≈_ _∙_
comm = IsCommutativeMonoid.comm isCommutativeMonoid

cancel : Cancel _≈_ _∙_
cancel = IsCancellativeAbelianMonoid.cancel 
         (CancellativeAbelianMonoid.isCancellativeAbelianMonoid m)

square : (x : Carrier) -> Carrier
square x = x ∙ x

multiple : (p : Carrier) -> Rel Carrier l
multiple p = λ (x y : Carrier) -> (p ∙ x) ≈ y 

_divides_ : Rel Carrier (l ⊔ a)
x divides y = ∃ (λ z → (x ∙ z) ≈ y)

_isPrime : Pred Carrier (l ⊔ a)
p isPrime = (x y : Carrier) -> p divides (x ∙ y) ->
            (p divides x) ⊎ (p divides y)

Square : Rel Carrier (l ⊔ a)
Square = λ (p x : Carrier) → ∃ (λ y → p ∙ square x ≈ square y)

_isNotSquare : Pred Carrier (l ⊔ a)
p isNotSquare = (x y : Carrier) → ¬ ((p ∙ square x) ≈ square y)
