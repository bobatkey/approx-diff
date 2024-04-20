{-# OPTIONS --postfix-projections --safe --without-K #-}

module poset where

open import Level
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import basics

record Poset : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤-isPreorder : IsPreorder _≤_

module _ where
  open Poset

  -- Unit poset
  𝟙 : Poset
  𝟙 .Carrier = Unit
  𝟙 ._≤_ tt tt = Unit
  𝟙 .≤-isPreorder .IsPreorder.refl = tt
  𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt
