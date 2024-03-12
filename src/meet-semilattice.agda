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

  pair : ∀ {W X Y} → W => X → W => Y → W => (X ⊕ Y)
  pair f g .func w = f .func w , g .func w
  pair f g .monotone w₁≤w₂ = (f .monotone w₁≤w₂) , (g .monotone w₁≤w₂)
  pair f g .∧-preserving = (f .∧-preserving) , (g .∧-preserving)
  pair f g .⊤-preserving = (f .⊤-preserving) , (g .⊤-preserving)
