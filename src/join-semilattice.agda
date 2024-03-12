{-# OPTIONS --postfix-projections --safe --without-K #-}

module join-semilattice where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Relation.Binary using (IsEquivalence; Reflexive)
open import basics

record JoinSemilattice : Set (suc 0ℓ) where
  no-eta-equality
  field
    Carrier      : Set
    _≤_          : Carrier → Carrier → Set
    _∨_          : Carrier → Carrier → Carrier
    ⊥            : Carrier
    ≤-isPreorder : IsPreorder _≤_
    ∨-isJoin     : IsJoin ≤-isPreorder _∨_
    ⊥-isBottom   : IsBottom ≤-isPreorder ⊥

  ∨-⊥-isMonoid : IsMonoid ≤-isPreorder _∨_ ⊥
  ∨-⊥-isMonoid = monoidOfJoin _ ∨-isJoin ⊥-isBottom

  open IsPreorder ≤-isPreorder renaming (refl to ≤-refl; trans to ≤-trans) public
  open IsEquivalence (isEquivalenceOf (≤-isPreorder)) renaming (refl to ≃-refl; sym to ≃-sym) public

record _=>_ (X Y : JoinSemilattice) : Set where
  open JoinSemilattice
  open IsPreorder (X .JoinSemilattice.≤-isPreorder) renaming (_≃_ to _≃₁_)
  open IsPreorder (Y .JoinSemilattice.≤-isPreorder) renaming (_≃_ to _≃₂_)
  field
    func : X .Carrier → Y .Carrier
    join-preserving : ∀ {x x'} → Y ._∨_ (func x) (func x') ≃₂ func (X ._∨_ x x')
    -- TODO: bottom-preserving
    monotone : ∀ {x x'} → X ._≤_ x x' → Y ._≤_ (func x) (func x')

  cong : ∀ {x x'} → x ≃₁ x' → func x ≃₂ func x'
  cong (x≤x' , _) .proj₁ = monotone x≤x'
  cong (_ , x'≤x) .proj₂ = monotone x'≤x

open _=>_

record _≃m_ {X Y : JoinSemilattice} (f g : X => Y) : Set where
  open IsPreorder (Y .JoinSemilattice.≤-isPreorder)
  field
    eqfunc : ∀ x → f .func x ≃ g .func x

open JoinSemilattice

id : ∀ {X} → X => X
id .func x = x
id {X} .monotone x≤x' = x≤x'
id {X} .join-preserving = ≃-refl X

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .monotone x≤x' = f .monotone (g .monotone x≤x')
_∘_ {X}{Y}{Z} f g .join-preserving {x}{x'} =
  begin
    Z ._∨_ (f .func (g .func x)) (f .func (g .func x'))
  ≈⟨ f .join-preserving ⟩
    f .func (Y ._∨_ (g .func x) (g .func x'))
  ≈⟨ cong f (g .join-preserving) ⟩
    (f .func (g .func (X ._∨_ x x')))
  ∎
  where open import Relation.Binary.Reasoning.Setoid (setoidOf (Z .≤-isPreorder))

-- constant (left zero) morphism
⊥-map : ∀ {X Y} → X => Y
⊥-map {X}{Y} .func _ = Y .⊥
⊥-map {X}{Y} .monotone _ = ≤-refl Y
⊥-map {X}{Y} .join-preserving = IsJoin.idem (Y .∨-isJoin)

-- FIXME: ∨-map

------------------------------------------------------------------------------
-- One element semilattice, for use when there are no approximations
𝟙 : JoinSemilattice
𝟙 .Carrier = ⊤
𝟙 ._≤_ tt tt = ⊤
𝟙 ._∨_ tt tt = tt
𝟙 .⊥ = tt
𝟙 .≤-isPreorder .IsPreorder.refl = tt
𝟙 .≤-isPreorder .IsPreorder.trans tt tt = tt
𝟙 .∨-isJoin .IsJoin.inl = tt
𝟙 .∨-isJoin .IsJoin.inr = tt
𝟙 .∨-isJoin .IsJoin.[_,_] tt tt = tt
𝟙 .⊥-isBottom .IsBottom.≤-bottom = tt

-- this is a zero object (both initial and terminal)

------------------------------------------------------------------------------
-- Lifting

data LCarrier (X : Set) : Set where
  bottom : LCarrier X
  <_>    : X → LCarrier X

-- Add a new bottom element to a finite join semilattice
L : JoinSemilattice → JoinSemilattice
L X .Carrier = LCarrier (X .Carrier)
L X ._≤_ bottom bottom = ⊤
L X ._≤_ bottom < _ >  = ⊤
L X ._≤_ < _ >  bottom = 𝟘
L X ._≤_ < x > < y >   = X ._≤_ x y
L X ._∨_ bottom bottom = bottom
L X ._∨_ < x >  bottom = < x >
L X ._∨_ bottom < y >  = < y >
L X ._∨_ < x >  < y >  = < X ._∨_ x y >
L X .⊥ = bottom
L X .≤-isPreorder .IsPreorder.refl {bottom} = tt
L X .≤-isPreorder .IsPreorder.refl {< x >} = ≤-refl X
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
  X .≤-isPreorder .IsPreorder.trans m₁ m₂
L X .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
L X .∨-isJoin .IsJoin.inl {< x >}  {bottom} = ≤-refl X
L X .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inl
L X .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inr {bottom} {< x >}  = ≤-refl X
L X .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
L X .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inr
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
L X .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
L X .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = X .∨-isJoin .IsJoin.[_,_] m₁ m₂
L X .⊥-isBottom .IsBottom.≤-bottom {bottom} = tt
L X .⊥-isBottom .IsBottom.≤-bottom {< x >} = tt

L-func : ∀ {X Y} → X => Y → L X => L Y
L-func m .func bottom = bottom
L-func m .func < x > = < m .func x >
L-func {X} {Y} m .monotone {bottom} {bottom} _ = tt
L-func {X} {Y} m .monotone {bottom} {< _ >} _ = tt
L-func m .monotone {< _ >} {bottom} ()
L-func m .monotone {< _ >} {< _ >} x₁≤x₂ = m .monotone x₁≤x₂
L-func {Χ}{Υ} m .join-preserving {bottom} {bottom} = tt , tt
L-func {Χ}{Υ} m .join-preserving {bottom} {< _ >} = ≃-refl Υ
L-func {X}{Y} m .join-preserving {< _ >} {bottom} = ≃-refl Y
L-func m .join-preserving {< _ >} {< _ >} = m .join-preserving

-- Lifting is a monad:
L-unit : ∀ {X} → X => L X
L-unit .func x = < x >
L-unit .monotone x≤x' = x≤x'
L-unit {X} .join-preserving = ≃-refl X

L-join : ∀ {X} → L (L X) => L X
L-join .func bottom = bottom
L-join .func < bottom > = bottom
L-join .func < < x > > = < x >
L-join .monotone {bottom} {bottom} _ = tt
L-join .monotone {bottom} {< bottom >} _ = tt
L-join .monotone {bottom} {< < _ > >} _ = tt
L-join .monotone {< bottom >} {< bottom >} _ = tt
L-join .monotone {< bottom >} {< < _ > >} _ = tt
L-join .monotone {< < _ > >} {< < _ > >} x≤x' = x≤x'
L-join .join-preserving {bottom} {bottom} = tt , tt
L-join .join-preserving {bottom} {< bottom >} = tt , tt
L-join {X} .join-preserving {bottom} {< < _ > >} = ≃-refl X
L-join {X} .join-preserving {< bottom >} {bottom} = tt , tt
L-join .join-preserving {< bottom >} {< bottom >} = tt , tt
L-join {X} .join-preserving {< bottom >} {< < _ > >} = ≃-refl X
L-join {X} .join-preserving {< < _ > >} {bottom} = ≃-refl X
L-join {X} .join-preserving {< < _ > >} {< bottom >} = ≃-refl X
L-join {X} .join-preserving {< < _ > >} {< < _ > >} = ≃-refl X

-- TODO: monad laws for L-join/L-unit

-- Lifting is a comonad in preorders with a bottom:
L-counit : ∀ {X} → L X => X
L-counit {X} .func bottom = X .⊥
L-counit .func < x > = x
L-counit {X} .monotone {bottom} _ = X .⊥-isBottom .IsBottom.≤-bottom
L-counit {X} .monotone {< _ >} {< _ >} x≤x' = x≤x'
L-counit {X} .join-preserving {bottom} {bottom} = IsJoin.idem (X .∨-isJoin)
L-counit {X} .join-preserving {bottom} {< _ >} = IsMonoid.lunit (∨-⊥-isMonoid X)
L-counit {X} .join-preserving {< _ >} {bottom} = IsMonoid.runit (∨-⊥-isMonoid X)
L-counit {X} .join-preserving {< _ >} {< _ >} = ≃-refl X

L-dup : ∀ {X} → L X => L (L X)
L-dup .func bottom = bottom
L-dup .func < x > = < < x > >
L-dup .monotone {bottom} {bottom} _ = tt
L-dup .monotone {bottom} {< _ >} _ = tt
L-dup .monotone {< _ >} {< _ >} x≤x' = x≤x'
L-dup .join-preserving {bottom} {bottom} = tt , tt
L-dup {X} .join-preserving {bottom} {< _ >} = ≃-refl X
L-dup {X} .join-preserving {< x >} {bottom} = ≃-refl X
L-dup {X} .join-preserving {< _ >} {< _ >} = ≃-refl X

L-coassoc : ∀ {X} → (L-func L-dup ∘ L-dup) ≃m (L-dup ∘ L-dup {X})
L-coassoc ._≃m_.eqfunc bottom .proj₁ = tt
L-coassoc ._≃m_.eqfunc bottom .proj₂ = tt
L-coassoc {X} ._≃m_.eqfunc < x > = ≃-refl X

L-unit1 : ∀ {X} → (L-counit ∘ L-dup) ≃m id {L X}
L-unit1 ._≃m_.eqfunc bottom .proj₁ = tt
L-unit1 ._≃m_.eqfunc bottom .proj₂ = tt
L-unit1 {X} ._≃m_.eqfunc < x > = ≃-refl X

L-unit2 : ∀ {X} → (L-func L-counit ∘ L-dup) ≃m id {L X}
L-unit2 ._≃m_.eqfunc bottom .proj₁ = tt
L-unit2 ._≃m_.eqfunc bottom .proj₂ = tt
L-unit2 {X} ._≃m_.eqfunc < x > = ≃-refl X

------------------------------------------------------------------------------
-- Set-wide direct sums of JoinSemilattices
module _ (I : Set) (X : I → JoinSemilattice) where

  data FormalJoin : Set where
    bot  : FormalJoin
    el   : (i : I) → X i .Carrier → FormalJoin
    join : FormalJoin → FormalJoin → FormalJoin

  data UpperBound (i : I) : FormalJoin → X i .Carrier → Set where
    bot   : ∀ {x} → UpperBound i bot x
    el    : ∀ {x y} → X i ._≤_ x y → UpperBound i (el i x) y
    join  : ∀ {j₁ j₂ x} → UpperBound i j₁ x → UpperBound i j₂ x → UpperBound i (join j₁ j₂) x

  ⨁ : JoinSemilattice
  ⨁ .Carrier = FormalJoin
  ⨁ ._≤_ j₁ j₂ = ∀ i x → UpperBound i j₂ x → UpperBound i j₁ x
  ⨁ ._∨_ = join
  ⨁ .⊥ = bot
  ⨁ .≤-isPreorder .IsPreorder.refl i x u = u
  ⨁ .≤-isPreorder .IsPreorder.trans m₁ m₂ i x u = m₁ i x (m₂ i x u)
  ⨁ .∨-isJoin .IsJoin.inl i x (join u₁ u₂) = u₁
  ⨁ .∨-isJoin .IsJoin.inr i x (join u₁ u₂) = u₂
  ⨁ .∨-isJoin .IsJoin.[_,_] m₁ m₂ i x u = join (m₁ i x u) (m₂ i x u)
  ⨁ .⊥-isBottom .IsBottom.≤-bottom i x _ = bot

  inj-⨁ : (i : I) → X i => ⨁
  inj-⨁ i .func x = el i x
  inj-⨁ i .monotone x₁≤x₂ _ _ (el x₂≤x₃) = el (≤-trans (X i) x₁≤x₂ x₂≤x₃)
  inj-⨁ i .join-preserving = {!   !}

  module _ (Z : JoinSemilattice) (X=>Z : ∀ i → X i => Z) where
    module Z = JoinSemilattice Z

    elim-⨁-func : ⨁ .Carrier → Z .Carrier
    elim-⨁-func bot = Z.⊥
    elim-⨁-func (el i x) = X=>Z i .func x
    elim-⨁-func (join j₁ j₂) = elim-⨁-func j₁ Z.∨ elim-⨁-func j₂

    elim-⨁ : ⨁ => Z
    elim-⨁ .func = elim-⨁-func
    elim-⨁ .monotone = {!   !}
    elim-⨁ .join-preserving = {!   !}

------------------------------------------------------------------------------
-- Biproducts
_⊕_ : JoinSemilattice → JoinSemilattice → JoinSemilattice
(X ⊕ Y) .Carrier = X .Carrier × Y .Carrier
(X ⊕ Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = (X ._≤_ x₁ x₂) × (Y ._≤_ y₁ y₂)
(X ⊕ Y) ._∨_ (x₁ , y₁) (x₂ , y₂) = (X ._∨_ x₁ x₂) , (Y ._∨_ y₁ y₂)
(X ⊕ Y) .⊥ = X .⊥ , Y .⊥
(X ⊕ Y) .≤-isPreorder .IsPreorder.refl = ≤-refl X , ≤-refl Y
(X ⊕ Y) .≤-isPreorder .IsPreorder.trans (x₁≤y₁ , x₂≤y₂) (y₁≤z₁ , y₂≤z₂) =
  X .≤-isPreorder .IsPreorder.trans x₁≤y₁ y₁≤z₁ ,
  Y .≤-isPreorder .IsPreorder.trans x₂≤y₂ y₂≤z₂
(X ⊕ Y) .∨-isJoin .IsJoin.inl = X .∨-isJoin .IsJoin.inl , Y .∨-isJoin .IsJoin.inl
(X ⊕ Y) .∨-isJoin .IsJoin.inr = X .∨-isJoin .IsJoin.inr , Y .∨-isJoin .IsJoin.inr
(X ⊕ Y) .∨-isJoin .IsJoin.[_,_] (x₁≤z₁ , y₁≤z₂) (x₂≤z₁ , y₂≤z₂) =
  X .∨-isJoin .IsJoin.[_,_] x₁≤z₁ x₂≤z₁ ,
  Y .∨-isJoin .IsJoin.[_,_] y₁≤z₂ y₂≤z₂
(X ⊕ Y) .⊥-isBottom .IsBottom.≤-bottom =
  X .⊥-isBottom .IsBottom.≤-bottom , Y .⊥-isBottom .IsBottom.≤-bottom

-- need to prove that this gives a biproduct

-- Product bits:
project₁ : ∀ {X Y} → (X ⊕ Y) => X
project₁ .func = proj₁
project₁ .monotone = proj₁
project₁ {X} .join-preserving = ≃-refl X

project₂ : ∀ {X Y} → (X ⊕ Y) => Y
project₂ .func = proj₂
project₂ .monotone = proj₂
project₂ {X}{Y} .join-preserving = ≃-refl Y

⟨_,_⟩ : ∀ {X Y Z} → X => Y → X => Z → X => (Y ⊕ Z)
⟨ f , g ⟩ .func x = f .func x , g .func x
⟨ f , g ⟩ .monotone x≤x' = f .monotone x≤x' , g .monotone x≤x'
⟨ f , g ⟩ .join-preserving .proj₁ = f .join-preserving .proj₁ , g .join-preserving .proj₁
⟨ f , g ⟩ .join-preserving .proj₂ = f .join-preserving .proj₂ , g .join-preserving .proj₂

-- Coproduct bits:
inject₁ : ∀ {X Y} → X => (X ⊕ Y)
inject₁ {X}{Y} .func x = x , Y .⊥
inject₁ {X}{Y} .monotone x≤x' = x≤x' , ≤-refl Y
inject₁ {X}{Y} .join-preserving .proj₁ = ≤-refl X , IsJoin.idem (Y .∨-isJoin) .proj₁
inject₁ {X}{Y} .join-preserving .proj₂ = ≤-refl X , Y .⊥-isBottom .IsBottom.≤-bottom

inject₂ : ∀ {X Y} → Y => (X ⊕ Y)
inject₂ {X}{Y} .func y = X .⊥ , y
inject₂ {X}{Y} .monotone y≤y' = ≤-refl X , y≤y'
inject₂ {X}{Y} .join-preserving =
  (IsJoin.idem (X .∨-isJoin) .proj₁ , ≤-refl Y) , (X .⊥-isBottom .IsBottom.≤-bottom , ≤-refl Y)

[_,_] : ∀ {X Y Z} → X => Z → Y => Z → (X ⊕ Y) => Z
[_,_] {X}{Y}{Z} f g .func (x , y) = Z ._∨_ (f .func x) (g .func y)
[_,_] {X}{Y}{Z} f g .monotone (x₁≤x₁' , x₂≤x₂') =
  IsJoin.mono (Z .∨-isJoin) (f .monotone x₁≤x₁') (g .monotone x₂≤x₂')
[_,_] {X}{Y}{Z} f g .join-preserving {(x₁ , y₁)}{(x₂ , y₂)} =
  begin
    Z ._∨_ (Z ._∨_ (f .func x₁) (g .func y₁)) (Z ._∨_ (f .func x₂) (g .func y₂))
  ≈⟨ ∨-assoc ⟩
    Z ._∨_ (f .func x₁) (Z ._∨_ (g .func y₁) (Z ._∨_ (f .func x₂) (g .func y₂)))
  ≈⟨ ∨-cong (cong f (≃-refl X)) (≃-sym Z ∨-assoc) ⟩
    Z ._∨_ (f .func x₁) (Z ._∨_ (Z ._∨_ (g .func y₁) (f .func x₂)) (g .func y₂))
  ≈⟨ ∨-cong (cong f (≃-refl X)) (∨-cong ∨-comm (≃-refl Z)) ⟩
    Z ._∨_ (f .func x₁) (Z ._∨_ (Z ._∨_ (f .func x₂) (g .func y₁)) (g .func y₂))
  ≈⟨ ∨-cong (cong f (≃-refl X)) ∨-assoc ⟩
    Z ._∨_ (f .func x₁) (Z ._∨_ (f .func x₂) (Z ._∨_ (g .func y₁) (g .func y₂)))
  ≈⟨ ≃-sym Z ∨-assoc ⟩
    Z ._∨_ (Z ._∨_ (f .func x₁) (f .func x₂)) (Z ._∨_ (g .func y₁) (g .func y₂))
  ≈⟨ ∨-cong (f .join-preserving) (g .join-preserving) ⟩
    (Z ._∨_ (f .func (X ._∨_ x₁ x₂)) (g .func (Y ._∨_ y₁ y₂)))
  ∎
  where
  open import Relation.Binary.Reasoning.Setoid (setoidOf (Z .≤-isPreorder))
  open IsJoin (Z .∨-isJoin) renaming (cong to ∨-cong; assoc to ∨-assoc; comm to ∨-comm)
