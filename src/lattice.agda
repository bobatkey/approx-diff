{-# OPTIONS --postfix-projections --safe --without-K #-}

module lattice where

open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Level
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import poset
open import meet-semilattice-2
open import join-semilattice-2

record Lattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    A : Poset
    meetSemilattice : MeetSemilattice A
    joinSemilattice : JoinSemilattice A
    -- distributivity?
