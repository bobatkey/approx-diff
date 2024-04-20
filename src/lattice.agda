{-# OPTIONS --postfix-projections --safe --without-K #-}

module lattice where

open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Level
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import poset using (Poset)
open import meet-semilattice-2 renaming (L to LM)
open import join-semilattice-2 renaming (L to LJ)

record Lattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    A : Poset
    meetSemilattice : MeetSemilattice A
    joinSemilattice : JoinSemilattice A
    -- distributivity?

  open Poset public

-- Add a new bottom element to a finite lattice
module _ where
  open Lattice

  L : Lattice → Lattice
  L X .A = poset.L (X .A)
  L X .meetSemilattice = LM (X .meetSemilattice)
  L X .joinSemilattice = LJ (X .joinSemilattice)
