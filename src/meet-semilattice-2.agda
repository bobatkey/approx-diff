{-# OPTIONS --postfix-projections --safe --without-K #-}

module meet-semilattice-2 where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import poset using (Poset)

record MeetSemilattice : Set (suc 0ℓ) where
  no-eta-equality
  open Poset

  field
    X       : Poset
    _∧_     : X .Carrier → X .Carrier → X .Carrier
    ⊤       : X. Carrier
    ∧-isMeet  : IsMeet (X .≤-isPreorder) _∧_
    ⊤-isTop   : IsTop (X. ≤-isPreorder) ⊤

  open IsPreorder (X .≤-isPreorder) renaming (refl to ≤-refl; trans to ≤-trans) public
