{-# OPTIONS --postfix-projections --safe --without-K #-}

module preorder where

open import Level
import Data.Unit using (tt) renaming (⊤ to 𝟙)
open Data.Unit using (tt)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_,_)
open import basics

record Preorder : Set (suc 0ℓ) where
  no-eta-equality
  field

    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    ≤-isPreorder : IsPreorder _≤_

  open IsPreorder ≤-isPreorder renaming (refl to ≤-refl; trans to ≤-trans) public

module _ where
  open Preorder

  -- Unit preorder
  𝟙 : Preorder
  𝟙 .Carrier = Data.Unit.𝟙
  𝟙 ._≤_ tt tt = Data.Unit.𝟙
  𝟙 .≤-isPreorder .IsPreorder.refl = tt
  𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt

-- Lifting
module _ where
  open Preorder

  data LCarrier (X : Set) : Set where
    bottom : LCarrier X
    <_>    : X → LCarrier X

  L : Preorder → Preorder
  L X .Carrier = LCarrier (X .Carrier)
  L X ._≤_ bottom bottom = Data.Unit.𝟙
  L X ._≤_ bottom < _ >  = Data.Unit.𝟙
  L X ._≤_ < _ >  bottom = 𝟘
  L X ._≤_ < x > < y >   = X ._≤_ x y
  L X .≤-isPreorder .IsPreorder.refl {bottom} = tt
  L X .≤-isPreorder .IsPreorder.refl {< x >} = ≤-refl X
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
    X .≤-isPreorder .IsPreorder.trans m₁ m₂

-- Binary products
module _ where
  open Preorder

  _×_ : Preorder → Preorder → Preorder
  (X × Y) .Carrier = Data.Product._×_ (X .Carrier) (Y .Carrier)
  (X × Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = Data.Product._×_ (X ._≤_ x₁ x₂) (Y ._≤_ y₁ y₂)
  (X × Y) .≤-isPreorder .IsPreorder.refl = (X .≤-refl) , (Y .≤-refl)
  (X × Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    (X .≤-trans x₁≤y₁ y₁≤z₁) , (Y .≤-trans x₂≤y₂ y₂≤z₂)

-- Arbitrary products
module _ (I : Set) (A : I → Preorder) where
  open Preorder

  Π : Preorder
  Π .Carrier = ∀ i → A i .Carrier
  Π ._≤_ x₁ x₂ = ∀ i → A i ._≤_ (x₁ i) (x₂ i)
  Π .≤-isPreorder .IsPreorder.refl i = A i .≤-refl
  Π .≤-isPreorder .IsPreorder.trans x≤y y≤z i = A i .≤-trans (x≤y i) (y≤z i)
