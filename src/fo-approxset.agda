{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset where

open import Level
open import basics
open import lattice

record FOApproxSet : Set (suc 0ℓ) where
  field
    elem    : Set
    approx : elem → Lattice
