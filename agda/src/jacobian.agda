{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
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
