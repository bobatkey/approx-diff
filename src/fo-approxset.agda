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

record _⇒_ (X Y : FOApproxSet) : Set where
  open _=>M_
  open MeetSemilattice
  open Lattice

  field
    func : X .elem → Y .elem
    fwd : (x : X .elem) → fapprox X x =>M fapprox Y (func x)
    bwd : (x : X .elem) → rapprox Y (func x) =>J rapprox X x
    bwd⊣fwd : ∀ (x : X .elem) {x' y'} →
              Y .approx (func x) .A ._≤_ y' (fwd x ._=>M_.func x') ⇔ X .approx x .A ._≤_ (bwd x ._=>J_.func y') x'

open _⇒_
