{-# OPTIONS --postfix-projections --safe --without-K #-}

module poset where

open import Level
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_,_)
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

-- Products
module _ where
  open Poset

  _×_ : Poset → Poset → Poset
  (X × Y) .Carrier = Data.Product._×_ (X .Carrier) (Y .Carrier)
  (X × Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = Data.Product._×_ (X ._≤_ x₁ x₂) (Y ._≤_ y₁ y₂)
  (X × Y) .≤-isPreorder .IsPreorder.refl = (X .≤-refl) , (Y .≤-refl)
  (X × Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    (X .≤-trans x₁≤y₁ y₁≤z₁) , (Y .≤-trans x₂≤y₂ y₂≤z₂)
