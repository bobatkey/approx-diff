{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level
open import basics
open import lattice
open import meet-semilattice-2 renaming (_=>_ to _=>M_; id to idM; _∘_ to _∘M_; L to LM)
open import join-semilattice-2 renaming (_=>_ to _=>J_; id to idJ; _∘_ to _∘J_; L to LJ)

record FOApproxSet : Set (suc 0ℓ) where
  open Lattice

  field
    elem    : Set
    approx : elem → Lattice

  fapprox : (x : elem) → MeetSemilattice (approx x .A)
  fapprox x = approx x .meetSemilattice

  rapprox : (x : elem) → JoinSemilattice (approx x .A)
  rapprox x = joinSemilattice (approx x)

open FOApproxSet

module _ where
  infix 4 _⇔_

  _⇔_ : Set → Set → Set
  P ⇔ Q = (P → Q) × (Q → P)
