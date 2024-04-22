{-# OPTIONS --postfix-projections --safe --without-K #-}

module meet-semilattice-2 where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics
open import preorder using (Preorder; _×_)

record MeetSemilattice (A : Preorder) : Set (suc 0ℓ) where
  no-eta-equality
  open Preorder public

  field
    _∧_     : A .Carrier → A .Carrier → A .Carrier
    ⊤       : A. Carrier
    ∧-isMeet  : IsMeet (A .≤-isPreorder) _∧_
    ⊤-isTop   : IsTop (A. ≤-isPreorder) ⊤

module _ {A B : Preorder} where
  open Preorder

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

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  𝟙 : MeetSemilattice preorder.𝟙
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

-- Big Products
module _ (I : Set) (A : I → Preorder) (X : (i : I) → MeetSemilattice (A i)) where
  open MeetSemilattice
  open _=>_

  Π-preorder : Preorder
  Π-preorder .Carrier = ∀ i → A i .Carrier
  Π-preorder ._≤_ x₁ x₂ = ∀ i → A i ._≤_ (x₁ i) (x₂ i)
  Π-preorder .≤-isPreorder .IsPreorder.refl i = A i .≤-refl
  Π-preorder .≤-isPreorder .IsPreorder.trans x≤y y≤z i = A i .≤-trans (x≤y i) (y≤z i)

  Π : MeetSemilattice Π-preorder
  Π ._∧_ x₁ x₂ i = X i ._∧_ (x₁ i) (x₂ i)
  Π .⊤ i = X i .⊤
  Π .∧-isMeet .IsMeet.π₁ i = X i .∧-isMeet .IsMeet.π₁
  Π .∧-isMeet .IsMeet.π₂ i = X i .∧-isMeet .IsMeet.π₂
  Π .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z i = X i .∧-isMeet .IsMeet.⟨_,_⟩ (x≤y i) (x≤z i)
  Π .⊤-isTop .IsTop.≤-top i = X i .⊤-isTop .IsTop.≤-top

------------------------------------------------------------------------------
-- Lifting
module _ where
  open preorder using (LCarrier; <_>; bottom)
  open MeetSemilattice
  open _=>_

  L : ∀ {A} → MeetSemilattice A → MeetSemilattice (preorder.L A)
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

  L-unit : ∀ {A}{X : MeetSemilattice A} → X => L X
  L-unit .func x = < x >
  L-unit .monotone x₁≤x₂ = x₁≤x₂
  L-unit {A} .∧-preserving = A .≤-refl
  L-unit {A} .⊤-preserving = A .≤-refl

  L-join : ∀ {A}{X : MeetSemilattice A} → L (L X) => L X
  L-join .func bottom = bottom
  L-join .func < bottom > = bottom
  L-join .func < < x > > = < x >
  L-join .monotone {bottom}     {bottom}     x₁≤x₂ = tt
  L-join .monotone {bottom}     {< bottom >} x₁≤x₂ = tt
  L-join .monotone {bottom}     {< < x > >}  x₁≤x₂ = tt
  L-join .monotone {< bottom >} {< bottom >} x₁≤x₂ = tt
  L-join .monotone {< bottom >} {< < x > >}  x₁≤x₂ = tt
  L-join .monotone {< < x > >}  {< < y > >}  x₁≤x₂ = x₁≤x₂
  L-join .∧-preserving {bottom} {bottom} = tt
  L-join .∧-preserving {bottom} {< x >} = tt
  L-join .∧-preserving {< bottom >} {bottom} = tt
  L-join .∧-preserving {< < x > >} {bottom} = tt
  L-join .∧-preserving {< bottom >} {< x₁ >} = tt
  L-join .∧-preserving {< < x > >} {< bottom >} = tt
  L-join {A} .∧-preserving {< < x > >} {< < x₁ > >} = A .≤-refl
  L-join {A} .⊤-preserving = A .≤-refl

  L-func : ∀ {A B}{X : MeetSemilattice A}{Y : MeetSemilattice B} → X => Y → L X => L Y
  L-func f .func bottom = bottom
  L-func f .func < x > = < f .func x >
  L-func f .monotone {bottom} {bottom} x₁≤x₂ = tt
  L-func f .monotone {bottom} {< x₂ >} x₁≤x₂ = tt
  L-func f .monotone {< x₁ >} {< x₂ >} x₁≤x₂ = f .monotone x₁≤x₂
  L-func f .∧-preserving {bottom} {x'} = tt
  L-func f .∧-preserving {< x >} {bottom} = tt
  L-func f .∧-preserving {< x >} {< x₁ >} = f .∧-preserving
  L-func f .⊤-preserving = f .⊤-preserving

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open Preorder
  open MeetSemilattice
  open _=>_

  _⊕_ : ∀ {A B} → MeetSemilattice A → MeetSemilattice B → MeetSemilattice (A × B)
  (X ⊕ Y) ._∧_ (x₁ , y₁) (x₂ , y₂) = (X ._∧_ x₁ x₂) , (Y ._∧_ y₁ y₂)
  (X ⊕ Y) .⊤ = (X .⊤) , (Y .⊤)
  (X ⊕ Y) .∧-isMeet .IsMeet.π₁ = X .∧-isMeet .IsMeet.π₁ , Y .∧-isMeet .IsMeet.π₁
  (X ⊕ Y) .∧-isMeet .IsMeet.π₂ = X .∧-isMeet .IsMeet.π₂ , Y .∧-isMeet .IsMeet.π₂
  (X ⊕ Y) .∧-isMeet .IsMeet.⟨_,_⟩ (x₁≤y₁ , x₂≤y₂) (x₁≤z₁ , x₂≤z₂) =
    X .∧-isMeet .IsMeet.⟨_,_⟩ x₁≤y₁ x₁≤z₁ , Y .∧-isMeet .IsMeet.⟨_,_⟩ x₂≤y₂ x₂≤z₂
  (X ⊕ Y) .⊤-isTop .IsTop.≤-top = X .⊤-isTop .IsTop.≤-top , Y .⊤-isTop .IsTop.≤-top

  project₁ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → (X ⊕ Y) => X
  project₁ .func = proj₁
  project₁ .monotone = proj₁
  project₁ {A = A} .∧-preserving = A .≤-refl
  project₁ {A = A} .⊤-preserving = A .≤-refl

  project₂ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → (X ⊕ Y) => Y
  project₂ .func = proj₂
  project₂ .monotone = proj₂
  project₂ {B = B} .∧-preserving = B .≤-refl
  project₂ {B = B} .⊤-preserving = B .≤-refl

  ⟨_,_⟩ : ∀ {A B C} {W : MeetSemilattice A} {X : MeetSemilattice B} {Y : MeetSemilattice C} →
          W => X → W => Y → W => (X ⊕ Y)
  ⟨_,_⟩ f g .func w = f .func w , g .func w
  ⟨_,_⟩ f g .monotone w₁≤w₂ = (f .monotone w₁≤w₂) , (g .monotone w₁≤w₂)
  ⟨_,_⟩ f g .∧-preserving = (f .∧-preserving) , (g .∧-preserving)
  ⟨_,_⟩ f g .⊤-preserving = (f .⊤-preserving) , (g .⊤-preserving)

  inject₁ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → X => (X ⊕ Y)
  inject₁ {Y = Y} .func x = x , Y .⊤
  inject₁ {B = B} .monotone x₁≤x₂ = x₁≤x₂ , B .≤-refl
  inject₁ {A = A} .∧-preserving .proj₁ = A .≤-refl
  inject₁ {Y = Y} .∧-preserving .proj₂ = Y .⊤-isTop .IsTop.≤-top
  inject₁ {A = A}{B = B} .⊤-preserving = A .≤-refl , B .≤-refl

  inject₂ : ∀ {A B} {X : MeetSemilattice A} {Y : MeetSemilattice B} → Y => (X ⊕ Y)
  inject₂ {X = X} .func y = X .⊤ , y
  inject₂ {A = A} .monotone y₁≤y₂ = A .≤-refl , y₁≤y₂
  inject₂ {X = X} .∧-preserving .proj₁ = X .⊤-isTop .IsTop.≤-top
  inject₂ {B = B} .∧-preserving .proj₂ = B .≤-refl
  inject₂ {A = A}{B = B} .⊤-preserving = A .≤-refl , B .≤-refl

  [_,_] : ∀ {A B C}{X : MeetSemilattice A}{Y : MeetSemilattice B}{Z : MeetSemilattice C} → X => Z → Y => Z → (X ⊕ Y) => Z
  [_,_] {Z = Z} f g .func (x , y) = Z ._∧_ (f .func x) (g .func y)
  [_,_] {Z = Z} f g .monotone (x₁≤x₂ , y₁≤y₂) =
    mono (f .monotone x₁≤x₂) (g .monotone y₁≤y₂)
    where open IsMeet (Z .∧-isMeet)
  [_,_] {C = C}{Z = Z} f g .∧-preserving {x , y} {x' , y'} =
    C .≤-trans (interchange sym)
               (∧-mono (f .∧-preserving) (g .∧-preserving))
    where open IsMeet (Z .∧-isMeet) renaming (mono to ∧-mono)
          open IsMonoid (monoidOfMeet (C .≤-isPreorder) (Z .∧-isMeet) (Z .⊤-isTop))
  [_,_] {Z = Z} f g .⊤-preserving = ⟨ (f .⊤-preserving) , (g .⊤-preserving) ⟩Z
    where open IsMeet (Z .∧-isMeet) renaming (⟨_,_⟩ to ⟨_,_⟩Z)
