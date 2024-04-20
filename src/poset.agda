{-# OPTIONS --postfix-projections --safe --without-K #-}

module poset where

open import Level
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import basics

record Poset : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤-isPreorder : IsPreorder _≤_

  open IsPreorder ≤-isPreorder renaming (refl to ≤-refl; trans to ≤-trans) public

module _ where
  open Poset

  -- Unit poset
  𝟙 : Poset
  𝟙 .Carrier = Unit
  𝟙 ._≤_ tt tt = Unit
  𝟙 .≤-isPreorder .IsPreorder.refl = tt
  𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt

------------------------------------------------------------------------------
-- Lifting
module _ where
  open Poset

  data LCarrier (X : Set) : Set where
    bottom : LCarrier X
    <_>    : X → LCarrier X

  L : Poset → Poset
  L X .Carrier = LCarrier (X .Carrier)
  L X ._≤_ bottom bottom = Unit
  L X ._≤_ bottom < _ >  = Unit
  L X ._≤_ < _ >  bottom = 𝟘
  L X ._≤_ < x > < y >   = X ._≤_ x y
  L X .≤-isPreorder .IsPreorder.refl {bottom} = tt
  L X .≤-isPreorder .IsPreorder.refl {< x >} = ≤-refl X
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
    X .≤-isPreorder .IsPreorder.trans m₁ m₂
