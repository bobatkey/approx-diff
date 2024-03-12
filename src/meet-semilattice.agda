{-# OPTIONS --postfix-projections --safe --without-K #-}

module meet-semilattice where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics

record MeetSemilattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    _∧_     : Carrier → Carrier → Carrier
    ⊤       : Carrier
    ≤-isPreorder : IsPreorder _≤_
    ∧-isMeet     : IsMeet ≤-isPreorder _∧_
    ⊤-isTop      : IsTop ≤-isPreorder ⊤

  open IsPreorder ≤-isPreorder renaming (refl to ≤-refl; trans to ≤-trans) public

record _=>_ (X Y : MeetSemilattice) : Set where
  open MeetSemilattice
  field
    func : X .Carrier → Y .Carrier
    monotone : ∀ {x₁ x₂} → X ._≤_ x₁ x₂ → Y ._≤_ (func x₁) (func x₂)
    ∧-preserving : ∀ {x x'} → Y ._≤_ (Y ._∧_ (func x) (func x')) (func (X ._∧_ x x'))
    ⊤-preserving : Y ._≤_ (Y .⊤) (func (X .⊤))

record _≃m_ {X Y : MeetSemilattice} (f g : X => Y) : Set where
  open _=>_
  open IsPreorder (Y .MeetSemilattice.≤-isPreorder)
  field
    eqfunc : ∀ x → f .func x ≃ g .func x

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice
  open _=>_

  id : ∀ {X} → X => X
  id {X} .func x = x
  id {X} .monotone x₁≤x₂ = x₁≤x₂
  id {X} .∧-preserving = X .≤-refl
  id {X} .⊤-preserving = X .≤-refl

  _∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
  (f ∘ g) .func x = f .func (g .func x)
  (f ∘ g) .monotone x₁≤x₂ = f .monotone (g .monotone x₁≤x₂)
  _∘_ {X}{Y}{Z} f g .∧-preserving =
    Z .≤-trans (f .∧-preserving) (f .monotone (g .∧-preserving))
  _∘_ {X}{Y}{Z} f g .⊤-preserving =
    Z .≤-trans (f .⊤-preserving) (f .monotone (g .⊤-preserving))

------------------------------------------------------------------------------
-- Big Products
module _ (I : Set)(X : I → MeetSemilattice) where

  open MeetSemilattice
  open _=>_

  Π : MeetSemilattice
  Π .Carrier = ∀ i → X i .Carrier
  Π ._≤_ x₁ x₂ = ∀ i → X i ._≤_ (x₁ i) (x₂ i)
  Π ._∧_ x₁ x₂ i = X i ._∧_ (x₁ i) (x₂ i)
  Π .⊤ i = X i .⊤
  Π .≤-isPreorder .IsPreorder.refl i = X i .≤-refl
  Π .≤-isPreorder .IsPreorder.trans x≤y y≤z i = X i .≤-trans (x≤y i) (y≤z i)
  Π .∧-isMeet .IsMeet.π₁ i = X i .∧-isMeet .IsMeet.π₁
  Π .∧-isMeet .IsMeet.π₂ i = X i .∧-isMeet .IsMeet.π₂
  Π .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z i = X i .∧-isMeet .IsMeet.⟨_,_⟩ (x≤y i) (x≤z i)
  Π .⊤-isTop .IsTop.≤-top i = X i .⊤-isTop .IsTop.≤-top

  proj-Π : (i : I) → Π => X i
  proj-Π i .func x = x i
  proj-Π i .monotone x₁≤x₂ = x₁≤x₂ i
  proj-Π i .∧-preserving = X i .≤-refl
  proj-Π i .⊤-preserving = X i .≤-refl

  lambda-Π : ∀ {W} → (W=>X : ∀ i → W => X i) → W => Π
  lambda-Π W=>X .func w i = W=>X i .func w
  lambda-Π W=>X .monotone w₁≤w₂ i = W=>X i .monotone w₁≤w₂
  lambda-Π W=>X .∧-preserving i = W=>X i .∧-preserving
  lambda-Π W=>X .⊤-preserving i = W=>X i .⊤-preserving

------------------------------------------------------------------------------
module _ where
  open MeetSemilattice

  𝟙 : MeetSemilattice
  𝟙 .Carrier = Unit
  𝟙 ._≤_ tt tt = Unit
  𝟙 ._∧_ tt tt = tt
  𝟙 .⊤ = tt
  𝟙 .≤-isPreorder .IsPreorder.refl = tt
  𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt
  𝟙 .∧-isMeet .IsMeet.π₁ = tt
  𝟙 .∧-isMeet .IsMeet.π₂ = tt
  𝟙 .∧-isMeet .IsMeet.⟨_,_⟩ tt tt = tt
  𝟙 .⊤-isTop .IsTop.≤-top = tt

------------------------------------------------------------------------------
-- Lifting
module _ where
  open MeetSemilattice
  open _=>_

  data LCarrier (X : Set) : Set where
    bottom : LCarrier X
    <_>    : X → LCarrier X

  L : MeetSemilattice → MeetSemilattice
  L X .Carrier = LCarrier (X .Carrier)
  L X ._≤_ bottom bottom = Unit
  L X ._≤_ bottom < _ >  = Unit
  L X ._≤_ < _ >  bottom = 𝟘
  L X ._≤_ < x > < y >   = X ._≤_ x y
  L X ._∧_ bottom _ = bottom
  L X ._∧_ < x > bottom = bottom
  L X ._∧_ < x > < y > = < X ._∧_ x y >
  L X .⊤ = < X .⊤ >
  L X .≤-isPreorder .IsPreorder.refl {bottom} = tt
  L X .≤-isPreorder .IsPreorder.refl {< x >} = ≤-refl X
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
  L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
    X .≤-isPreorder .IsPreorder.trans m₁ m₂
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

  L-unit : ∀ {X} → X => L X
  L-unit .func x = < x >
  L-unit .monotone x₁≤x₂ = x₁≤x₂
  L-unit {X} .∧-preserving = X .≤-refl
  L-unit {X} .⊤-preserving = X .≤-refl

  L-join : ∀ {X} → L (L X) => L X
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
  L-join {X} .∧-preserving {< < x > >} {< < x₁ > >} = X .≤-refl
  L-join {X} .⊤-preserving = X .≤-refl

------------------------------------------------------------------------------
-- Biproducts
module _ where
  open MeetSemilattice
  open _=>_

  _⊕_ : MeetSemilattice → MeetSemilattice → MeetSemilattice
  (X ⊕ Y) .Carrier = X .Carrier × Y .Carrier
  (X ⊕ Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = (X ._≤_ x₁ x₂) × (Y ._≤_ y₁ y₂)
  (X ⊕ Y) ._∧_ (x₁ , y₁) (x₂ , y₂) = (X ._∧_ x₁ x₂) , (Y ._∧_ y₁ y₂)
  (X ⊕ Y) .⊤ = (X .⊤) , (Y .⊤)
  (X ⊕ Y) .≤-isPreorder .IsPreorder.refl = (X .≤-refl) , (Y .≤-refl)
  (X ⊕ Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
    (X .≤-trans x₁≤y₁ y₁≤z₁) , (Y .≤-trans x₂≤y₂ y₂≤z₂)
  (X ⊕ Y) .∧-isMeet .IsMeet.π₁ = X .∧-isMeet .IsMeet.π₁ , Y .∧-isMeet .IsMeet.π₁
  (X ⊕ Y) .∧-isMeet .IsMeet.π₂ = X .∧-isMeet .IsMeet.π₂ , Y .∧-isMeet .IsMeet.π₂
  (X ⊕ Y) .∧-isMeet .IsMeet.⟨_,_⟩ (x₁≤y₁ , x₂≤y₂) (x₁≤z₁ , x₂≤z₂) =
    X .∧-isMeet .IsMeet.⟨_,_⟩ x₁≤y₁ x₁≤z₁ , Y .∧-isMeet .IsMeet.⟨_,_⟩ x₂≤y₂ x₂≤z₂
  (X ⊕ Y) .⊤-isTop .IsTop.≤-top = X .⊤-isTop .IsTop.≤-top , Y .⊤-isTop .IsTop.≤-top

  project₁ : ∀ {X Y} → (X ⊕ Y) => X
  project₁ .func = proj₁
  project₁ .monotone = proj₁
  project₁ {X}{Y} .∧-preserving = X .≤-refl
  project₁ {X}{Y} .⊤-preserving = X .≤-refl

  project₂ : ∀ {X Y} → (X ⊕ Y) => Y
  project₂ .func = proj₂
  project₂ .monotone = proj₂
  project₂ {X}{Y} .∧-preserving = Y .≤-refl
  project₂ {X}{Y} .⊤-preserving = Y .≤-refl

  ⟨_,_⟩ : ∀ {W X Y} → W => X → W => Y → W => (X ⊕ Y)
  ⟨_,_⟩ f g .func w = f .func w , g .func w
  ⟨_,_⟩ f g .monotone w₁≤w₂ = (f .monotone w₁≤w₂) , (g .monotone w₁≤w₂)
  ⟨_,_⟩ f g .∧-preserving = (f .∧-preserving) , (g .∧-preserving)
  ⟨_,_⟩ f g .⊤-preserving = (f .⊤-preserving) , (g .⊤-preserving)

  inject₁ : ∀ {X Y} → X => (X ⊕ Y)
  inject₁ {X} {Y} .func x = x , Y .⊤
  inject₁ {X} {Y} .monotone x₁≤x₂ = x₁≤x₂ , Y .≤-refl
  inject₁ {X} {Y} .∧-preserving .proj₁ = X .≤-refl
  inject₁ {X} {Y} .∧-preserving .proj₂ = Y .⊤-isTop .IsTop.≤-top
  inject₁ {X} {Y} .⊤-preserving = (X .≤-refl) , Y .≤-refl
