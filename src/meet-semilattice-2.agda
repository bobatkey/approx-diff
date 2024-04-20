{-# OPTIONS --postfix-projections --safe --without-K #-}

module meet-semilattice-2 where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import poset using (Poset)

record MeetSemilattice (A : Poset) : Set (suc 0ℓ) where
  no-eta-equality
  open Poset

  field
    _∧_     : A .Carrier → A .Carrier → A .Carrier
    ⊤       : A. Carrier
    ∧-isMeet  : IsMeet (A .≤-isPreorder) _∧_
    ⊤-isTop   : IsTop (A. ≤-isPreorder) ⊤

  open IsPreorder (A .≤-isPreorder) renaming (refl to ≤-refl; trans to ≤-trans) public

module _ {A B : Poset} where
  open Poset

  record _=>_ (X : MeetSemilattice A) (Y : MeetSemilattice B) : Set where
    open MeetSemilattice
    field
      func : A .Carrier → B .Carrier
      monotone : ∀ {x₁ x₂} → A ._≤_ x₁ x₂ → B ._≤_ (func x₁) (func x₂)
      ∧-preserving : ∀ {x x'} → B ._≤_ (Y ._∧_ (func x) (func x')) (func (X ._∧_ x x'))
      ⊤-preserving : B ._≤_ (Y .⊤) (func (X .⊤))

  record _≃m_ {X : MeetSemilattice A} {Y : MeetSemilattice B} (f g : X => Y) : Set where
    open _=>_
    open IsPreorder (B .≤-isPreorder)
    field
      eqfunc : ∀ x → f .func x ≃ g .func x

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  id : ∀ {A}{X : MeetSemilattice A} → X => X
  id .func x = x
  id .monotone x₁≤x₂ = x₁≤x₂
  id {X = X} .∧-preserving = X .≤-refl
  id {X = X} .⊤-preserving = X .≤-refl

  _∘_ : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C} → Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x₁≤x₂ = f .monotone (g .monotone x₁≤x₂)
  _∘_ {Z = Z} f g .∧-preserving =
    Z .≤-trans (f .∧-preserving) (f .monotone (g .∧-preserving))
  _∘_ {Z = Z} f g .⊤-preserving =
    Z .≤-trans (f .⊤-preserving) (f .monotone (g .⊤-preserving))
