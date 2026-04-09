{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
import two
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
e {suc n} zero    = two.I , Bool^ n .⊥
e {suc n} (suc i) = two.O , e i

-- Morphisms: a join-semilattice morphism Bool^m → Bool^n.
-- Every such map is Bool-linear (determined by its values on basis vectors), so equivalent to an n×m Bool matrix.
-- The transpose (giving the backward/J^op component) will be derived.

_⇒J_ : ℕ → ℕ → Set
m ⇒J n = Bool^ m ⇒ Bool^ n
  where open join-semilattice-category using (_⇒_)
