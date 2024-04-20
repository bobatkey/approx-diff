{-# OPTIONS --postfix-projections --safe --without-K #-}

module join-semilattice-2 where

open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Level
open import basics
open import poset using (Poset; _×_)

record JoinSemilattice (A : Poset) : Set (suc 0ℓ) where
  no-eta-equality
  open Poset public

  field
    _∨_          : A .Carrier → A .Carrier → A .Carrier
    ⊥            : A .Carrier
    ∨-isJoin     : IsJoin (A .≤-isPreorder) _∨_
    ⊥-isBottom   : IsBottom (A .≤-isPreorder) ⊥

module _ {A B : Poset} where
  open Poset

  record _=>_ (X : JoinSemilattice A) (Y : JoinSemilattice B) : Set where
    open JoinSemilattice
    field
      func : A .Carrier → B .Carrier
      monotone : ∀ {x₁ x₂} → A ._≤_ x₁ x₂ → B ._≤_ (func x₁) (func x₂)
      ∨-preserving : ∀ {x x'} → B ._≤_ (func (X ._∨_ x x')) (Y ._∨_ (func x) (func x'))
      ⊥-preserving : B ._≤_ (func (X .⊥)) (Y .⊥)

  record _≃m_ {X : JoinSemilattice A} {Y : JoinSemilattice B} (f g : X => Y) : Set where
    open _=>_
    field
      eqfunc : ∀ x → _≃_ B (f .func x) (g .func x)

module _ where
  open JoinSemilattice
  open _=>_

  id : ∀ {A}{X : JoinSemilattice A} → X => X
  id .func x = x
  id .monotone x≤x' = x≤x'
  id {X} .∨-preserving = X .≤-refl
  id {X} .⊥-preserving = X .≤-refl

  _∘_ : ∀ {A B C}{X : JoinSemilattice A}{Y : JoinSemilattice B}{Z : JoinSemilattice C} → Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x≤x' = f .monotone (g .monotone x≤x')
  _∘_ {C = C} f g .∨-preserving = C .≤-trans (f .monotone (g .∨-preserving)) (f .∨-preserving)
  _∘_ {C = C} f g .⊥-preserving = C .≤-trans (f .monotone (g .⊥-preserving)) (f .⊥-preserving)

  -- constant (left zero) morphisms
  ⊥-map : ∀ {A}{B}{X : JoinSemilattice A}{Y : JoinSemilattice B} → X => Y
  ⊥-map {Y = Y} .func _ = Y .⊥
  ⊥-map {B = B} .monotone _ = B .≤-refl
  ⊥-map {Y = Y} .∨-preserving = IsJoin.idem (Y .∨-isJoin) .proj₂
  ⊥-map {X}{Y} .⊥-preserving = Y .≤-refl

------------------------------------------------------------------------------
-- One element semilattice, for use when there are no approximations
module _ where
  open JoinSemilattice

  𝟙 : JoinSemilattice poset.𝟙
  𝟙 ._∨_ tt tt = tt
  𝟙 .⊥ = tt
  𝟙 .∨-isJoin .IsJoin.inl = tt
  𝟙 .∨-isJoin .IsJoin.inr = tt
  𝟙 .∨-isJoin .IsJoin.[_,_] tt tt = tt
  𝟙 .⊥-isBottom .IsBottom.≤-bottom = tt

  -- this is a zero object (both initial and terminal)
  initial : ∀ {A}{X : JoinSemilattice A} → 𝟙 => X
  initial = ⊥-map

------------------------------------------------------------------------------
-- Lifting
module _ where
  open poset using (LCarrier; <_>; bottom)
  open JoinSemilattice

  L : ∀ {A} → JoinSemilattice A → JoinSemilattice (poset.L A)
  L X ._∨_ bottom bottom = bottom
  L X ._∨_ < x >  bottom = < x >
  L X ._∨_ bottom < y >  = < y >
  L X ._∨_ < x >  < y >  = < X ._∨_ x y >
  L X .⊥ = bottom
  L X .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
  L X .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
  L {A} X .∨-isJoin .IsJoin.inl {< x >}  {bottom} = A .≤-refl
  L X .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inl
  L X .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
  L {A} X .∨-isJoin .IsJoin.inr {bottom} {< x >}  = A. ≤-refl
  L X .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
  L X .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inr
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
  L X .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
  L X .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
  L X .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = X .∨-isJoin .IsJoin.[_,_] m₁ m₂
  L X .⊥-isBottom .IsBottom.≤-bottom {bottom} = tt
  L X .⊥-isBottom .IsBottom.≤-bottom {< x >} = tt
