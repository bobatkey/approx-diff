{-# OPTIONS --postfix-projections --safe --without-K #-}

module reverse where

open import Level
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import basics

------------------------------------------------------------------------------
--
-- Join Semilattices, and an implementation of reverse-mode automatic
-- approximation.
--
-- TODO:
--   1. Add join-preserving to the definition of JoinSemilattice morphism
--   2. Prove the expected categorical properties of JoinSemilattices
--   3. Prove the expected categorical properties of ApproxSets
--   4. Add in the forward approximation pass to ApproxSets
--   5. Show that a typed λ-calculus can be interpreted using ApproxSets
--   6. Show that the forwards and reverse-mode approximations form a Galois
--      connection at first order type.
--
--   7. Show that ApproxSets (with forward approximation) form a
--      Tangent Category
--
------------------------------------------------------------------------------

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
open JoinSemilattice

record _=>_ (X Y : JoinSemilattice) : Set where
  field
    func : X .Carrier → Y .Carrier
    -- join-preserving :
    -- bottom-preserving :
    -- monotone :
open _=>_

id : ∀ {X} → X => X
id .func x = x

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .func x = f .func (g .func x)

⊥-map : ∀ {X Y} → X => Y
⊥-map {X}{Y} .func x = Y .⊥


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
L X .≤-isPreorder .IsPreorder.refl {< x >} = X .≤-isPreorder .IsPreorder.refl
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {bottom} m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {bottom} {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {bottom} {< y >}  {< z >}  m₁ m₂ = tt
L X .≤-isPreorder .IsPreorder.trans {< x >}  {< y >}  {< z >}  m₁ m₂ =
  X .≤-isPreorder .IsPreorder.trans m₁ m₂
L X .∨-isJoin .IsJoin.inl {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inl {bottom} {< x >}  = tt
L X .∨-isJoin .IsJoin.inl {< x >}  {bottom} = X .≤-isPreorder .IsPreorder.refl
L X .∨-isJoin .IsJoin.inl {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inl
L X .∨-isJoin .IsJoin.inr {bottom} {bottom} = tt
L X .∨-isJoin .IsJoin.inr {bottom} {< x >}  = X .≤-isPreorder .IsPreorder.refl
L X .∨-isJoin .IsJoin.inr {< x >}  {bottom} = tt
L X .∨-isJoin .IsJoin.inr {< x >}  {< y >}  = X .∨-isJoin .IsJoin.inr
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{bottom} m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{bottom}{< z >}  m₁ m₂ = tt
L X .∨-isJoin .IsJoin.[_,_] {bottom}{< y >} {z}      m₁ m₂ = m₂
L X .∨-isJoin .IsJoin.[_,_] {< x >} {bottom}{z}      m₁ m₂ = m₁
L X .∨-isJoin .IsJoin.[_,_] {< x >} {< y >} {< z >}  m₁ m₂ = X .∨-isJoin .IsJoin.[_,_] m₁ m₂
L X .⊥-isBottom .IsBottom.≤-bottom {bottom} = tt
L X .⊥-isBottom .IsBottom.≤-bottom {< x >} = tt

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

  module _ (Z : JoinSemilattice) (X=>Z : ∀ i → X i => Z) where
    module Z = JoinSemilattice Z

    elim-⨁-func : ⨁ .Carrier → Z .Carrier
    elim-⨁-func bot = Z.⊥
    elim-⨁-func (el i x) = X=>Z i .func x
    elim-⨁-func (join j₁ j₂) = elim-⨁-func j₁ Z.∨ elim-⨁-func j₂

    elim-⨁ : ⨁ => Z
    elim-⨁ .func = elim-⨁-func

-- Biproducts
_⊕_ : JoinSemilattice → JoinSemilattice → JoinSemilattice
(X ⊕ Y) .Carrier = X .Carrier × Y .Carrier
(X ⊕ Y) ._≤_ (x₁ , y₁) (x₂ , y₂) = (X ._≤_ x₁ x₂) × (Y ._≤_ y₁ y₂)
(X ⊕ Y) ._∨_ (x₁ , y₁) (x₂ , y₂) = (X ._∨_ x₁ x₂) , (Y ._∨_ y₁ y₂)
(X ⊕ Y) .⊥ = X .⊥ , Y .⊥
(X ⊕ Y) .≤-isPreorder .IsPreorder.refl =
  X .≤-isPreorder .IsPreorder.refl , Y .≤-isPreorder .IsPreorder.refl
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

project₂ : ∀ {X Y} → (X ⊕ Y) => Y
project₂ .func = proj₂

⟨_,_⟩ : ∀ {X Y Z} → X => Y → X => Z → X => (Y ⊕ Z)
⟨ f , g ⟩ .func x = f .func x , g .func x

-- Coproduct bits:
inject₁ : ∀ {X Y} → X => (X ⊕ Y)
inject₁ {X}{Y} .func x = x , Y .⊥

inject₂ : ∀ {X Y} → Y => (X ⊕ Y)
inject₂ {X}{Y} .func y = X .⊥ , y

[_,_] : ∀ {X Y Z} → X => Z → Y => Z → (X ⊕ Y) => Z
[_,_] {X}{Y}{Z} f g .func (x , y) = Z ._∨_ (f .func x) (g .func y)

------------------------------------------------------------------------------
-- Sets-with-approximations
record ApproxSet : Set (suc 0ℓ) where
  field
    elem   : Set
    approx : elem → JoinSemilattice
    -- FIXME: do the forward approximation preorder at the same time
    -- is there a relationship between the two that always holds?
open ApproxSet

record _⇒_ (X Y : ApproxSet) : Set where
  field
    fwd : X .elem → Y .elem
    bwd : (x : X .elem) → Y .approx (fwd x) => X .approx x
open _⇒_

-- Have a bicartesian closed category... here's the definitions at least:

-- Products
_⊗_ : ApproxSet → ApproxSet → ApproxSet
(X ⊗ Y) .elem = X .elem × Y .elem
(X ⊗ Y) .approx (x , y) = X .approx x ⊕ Y .approx y

π₁ : ∀ {X Y} → (X ⊗ Y) ⇒ X
π₁ .fwd = proj₁
π₁ .bwd (x , y) = inject₁

π₂ : ∀ {X Y} → (X ⊗ Y) ⇒ Y
π₂ .fwd = proj₂
π₂ .bwd (x , y) = inject₂

pair : ∀ {X Y Z} → (X ⇒ Y) → (X ⇒ Z) → X ⇒ (Y ⊗ Z)
pair f g .fwd x = f .fwd x , g .fwd x
pair f g .bwd x = [ f .bwd x , g .bwd x ]

-- Sums
_+_ : ApproxSet → ApproxSet → ApproxSet
(X + Y) .elem = X .elem ⊎ Y .elem
(X + Y) .approx (inj₁ x) = X .approx x
(X + Y) .approx (inj₂ y) = Y .approx y

inl : ∀ {X Y} → X ⇒ (X + Y)
inl .fwd = inj₁
inl .bwd x = id

inr : ∀ {X Y} → Y ⇒ (X + Y)
inr .fwd = inj₂
inr .bwd y = id

case : ∀ {W X Y Z} → (W ⊗ X) ⇒ Z → (W ⊗ Y) ⇒ Z → (W ⊗ (X + Y)) ⇒ Z
case m₁ m₂ .fwd (w , inj₁ x) = m₁ .fwd (w , x)
case m₁ m₂ .fwd (w , inj₂ y) = m₂ .fwd (w , y)
case m₁ m₂ .bwd (w , inj₁ x) = m₁ .bwd (w , x)
case m₁ m₂ .bwd (w , inj₂ y) = m₂ .bwd (w , y)

-- Functions
_⊸_ : ApproxSet → ApproxSet → ApproxSet
(X ⊸ Y) .elem = X ⇒ Y
(X ⊸ Y) .approx f = ⨁ (X .elem) λ x → Y .approx (f .fwd x)

eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
eval .fwd (f , x) = f .fwd x
eval {X}{Y} .bwd (f , x) =
  ⟨ inj-⨁ (X .elem) (λ x → Y .approx (f .fwd x)) x , f .bwd x ⟩

lambda : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
lambda m .fwd x .fwd y = m .fwd (x , y)
lambda m .fwd x .bwd y = project₂ ∘ m .bwd (x , y)
lambda m .bwd x = elim-⨁ _ _ _ λ y → project₁ ∘ m .bwd (x , y)

-- Lifting
ℒ : ApproxSet → ApproxSet
ℒ X .elem = X .elem
ℒ X .approx x = L (X .approx x)

ℒ-unit : ∀ {X} → X ⇒ ℒ X
ℒ-unit .fwd x = x
ℒ-unit .bwd x = ⊥-map

-- is this right? the reverse pass gives the _least_ input that gets
-- the output, so I think this is right.
ℒ-join : ∀ {X} → ℒ (ℒ X) ⇒ ℒ X
ℒ-join .fwd x = x
ℒ-join .bwd x .func bottom = bottom -- or < bottom > ?
ℒ-join .bwd x .func < δx > = < < δx > >

-- Somehow, in JoinSemilattice, lifting is both a monad and a comonad?
