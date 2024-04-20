{-# OPTIONS --postfix-projections --safe --without-K #-}

module poset where

open import Level
open import basics

record Poset : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤-isPreorder : IsPreorder _≤_
