{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import two using (Two; I; O; _⊓_; _⊔_)
import join-semilattice-category

open join-semilattice-category using (Obj; TWO; products; terminal)
open import categories using (HasProducts; HasTerminal)

-- Objects: Bool^n, the n-fold product of TWO in the category of join semilattices.

private
  module P = HasProducts products
  module T = HasTerminal terminal

Bool^ : ℕ → Obj
Bool^ zero    = T.witness
Bool^ (suc n) = P.prod TWO (Bool^ n)

-- Standard basis vector: I at position i, O everywhere else.
open Obj

e : ∀ {n} → Fin n → Bool^ n .Carrier
e {suc n} zero = I , Bool^ n .⊥
e {suc n} (suc i) = O , e i

-- Morphisms: a join-semilattice morphism Bool^m → Bool^n.
-- Every such map is Bool-linear (determined by its values on basis vectors), so equivalent to an n×m Bool matrix.
-- The transpose (giving the backward/J^op component) will be derived.

-- Projection: extract the i-th component.
proj : ∀ {n} → Fin n → Bool^ n .Carrier → Two
proj zero    (b , _)  = b
proj (suc i) (_ , bs) = proj i bs

open import Data.Unit using (tt)

-- The Bool^n representation of a function.
tabulate : ∀ {n} → (Fin n → Two) → Bool^ n .Carrier
tabulate {zero} _ = tt
tabulate {suc n} f = f zero , tabulate {n} (λ i → f (suc i))

-- Dot product of two Bool^n, i.e. whether there exists a position where both are I.
_⋅_ : ∀ {n} → Bool^ n .Carrier → Bool^ n .Carrier → Two
_⋅_ {zero}  _ _ = O
_⋅_ {suc n} (a , as) (b , bs) = (a ⊓ b) ⊔ _⋅_ {n} as bs

-- Morphisms: a join-semilattice morphism Bool^m → Bool^n.
-- Every such map is Bool-linear (determined by its values on basis vectors), so equivalent to an n×m Bool matrix.
_⇒J_ : ℕ → ℕ → Set
m ⇒J n = Bool^ m ⇒ Bool^ n
  where open join-semilattice-category using (_⇒_)

-- Transpose f^T : Bool^n ⇒ Bool^m = f^T(v)[i] = f(e_i) ⋅ v, given f : Bool^m ⇒ Bool^n.
open join-semilattice-category using (_⇒_)
open join-semilattice-category._⇒_
import join-semilattice
open join-semilattice._=>_
open import preorder using (_=>_)
open preorder._=>_

transpose : ∀ {m n} → m ⇒J n → n ⇒J m
transpose {m} {n} f .*→* .func .fun v = tabulate {m} (λ i → _⋅_ {n} (f .fun (e i)) v)
transpose {m} {n} f .*→* .func .mono = {!!}
transpose {m} {n} f .*→* .∨-preserving = {!!}
transpose {m} {n} f .*→* .⊥-preserving = {!!}
