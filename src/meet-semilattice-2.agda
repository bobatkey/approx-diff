{-# OPTIONS --postfix-projections --safe --without-K #-}

module meet-semilattice-2 where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import poset using (Poset)

record MeetSemilattice (A : Poset) : Set (suc 0ℓ) where
  no-eta-equality
  open Poset public

  field
    _∧_     : A .Carrier → A .Carrier → A .Carrier
    ⊤       : A. Carrier
    ∧-isMeet  : IsMeet (A .≤-isPreorder) _∧_
    ⊤-isTop   : IsTop (A. ≤-isPreorder) ⊤

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
    field
      eqfunc : ∀ x → _≃_ B (f .func x) (g .func x)

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  id : ∀ {A}{X : MeetSemilattice A} → X => X
  id .func x = x
  id .monotone x₁≤x₂ = x₁≤x₂
  id {Α} .∧-preserving = Α .≤-refl
  id {Α} .⊤-preserving = Α .≤-refl

  _∘_ : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C} →
        Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x₁≤x₂ = f .monotone (g .monotone x₁≤x₂)
  _∘_ {C = C} f g .∧-preserving =
    C .≤-trans (f .∧-preserving) (f .monotone (g .∧-preserving))
  _∘_ {C = C} f g .⊤-preserving =
    C .≤-trans (f .⊤-preserving) (f .monotone (g .⊤-preserving))

-- Big Products would be expressed in terms of big product of posets

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  𝟙 : MeetSemilattice poset.𝟙
  𝟙 ._∧_ tt tt = tt
  𝟙 .⊤ = tt
  𝟙 .∧-isMeet .IsMeet.π₁ = tt
  𝟙 .∧-isMeet .IsMeet.π₂ = tt
  𝟙 .∧-isMeet .IsMeet.⟨_,_⟩ tt tt = tt
  𝟙 .⊤-isTop .IsTop.≤-top = tt

  terminal : ∀ {A}{X : MeetSemilattice A} → X => 𝟙
  terminal .func _ = tt
  terminal .monotone _ = tt
  terminal .∧-preserving = tt
  terminal .⊤-preserving = tt

------------------------------------------------------------------------------
-- Lifting
module _ where
  open poset using (LCarrier; <_>; bottom)
  open MeetSemilattice

  L : ∀ {A} → MeetSemilattice A → MeetSemilattice (poset.L A)
  L X ._∧_ bottom _ = bottom
  L X ._∧_ < x > bottom = bottom
  L X ._∧_ < x > < y > = < X ._∧_ x y >
  L X .⊤ = < X .⊤ >
  L X .∧-isMeet .IsMeet.π₁ {bottom} {y} = tt
  L X .∧-isMeet .IsMeet.π₁ {< x >} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₁ {< x >} {< x₁ >} = X .∧-isMeet .IsMeet.π₁
  L X .∧-isMeet .IsMeet.π₂ {bottom} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₂ {bottom} {< x >} = tt
  L X .∧-isMeet .IsMeet.π₂ {< x >} {bottom} = tt
  L X .∧-isMeet .IsMeet.π₂ {< x >} {< x₁ >} = X .∧-isMeet .IsMeet.π₂
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {bottom} {z} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {< y >}  {bottom} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {bottom} {< y >}  {< z >} x≤y x≤z = tt
  L X .∧-isMeet .IsMeet.⟨_,_⟩ {< x >}  {< y >}  {< z >} x≤y x≤z =
    X .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z
  L X .⊤-isTop .IsTop.≤-top {bottom} = tt
  L X .⊤-isTop .IsTop.≤-top {< x >} = X .⊤-isTop .IsTop.≤-top
