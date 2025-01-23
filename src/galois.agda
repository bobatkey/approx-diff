{-# OPTIONS --postfix-projections --prop #-}

module galois where

open import Level
open import prop
open import basics
open import prop-setoid
  using (IsEquivalence)
  renaming (_⇒_ to _⇒s_)
open import preorder
open import categories
open import meet-semilattice
  renaming (_=>_ to _=>M_; _≃m_ to _≃M_; id to idM; _∘_ to _∘M_;
            ≃m-isEquivalence to ≃M-isEquivalence)
open import join-semilattice
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; id to idJ; _∘_ to _∘J_;
            ≃m-isEquivalence to ≃J-isEquivalence)

-- The category of bounded lattices and Galois connections between
-- them.
--
-- We define the objects as being partially ordered sets that have a
-- meet structure and a join structure. The morphisms are pairs of
-- adjoint monotone functions.
--
-- The objects in this category form the first-order approximation
-- sets.

record Obj : Set (suc 0ℓ) where
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier
  open Preorder carrier public
open Obj

record _⇒g_ (X Y : Obj) : Set where
  private
    module X = Obj X
    module Y = Obj Y
  field
    fwd : X .meets =>M Y .meets
    bwd : Y .joins =>J X .joins
    bwd⊣fwd : ∀ {x y} → y Y.≤ (fwd ._=>M_.func x) ⇔ (bwd ._=>J_.func y) X.≤ x
open _⇒g_

record _≃g_ {X Y : Obj} (f g : X ⇒g Y) : Prop where
  field
    fwd-eq : f .fwd ≃M g .fwd
    bwd-eq : f .bwd ≃J g .bwd
open _≃g_

open IsEquivalence

≃g-isEquivalence : ∀ {X Y} → IsEquivalence (_≃g_ {X} {Y})
≃g-isEquivalence .refl .fwd-eq = ≃M-isEquivalence .refl
≃g-isEquivalence .refl .bwd-eq = ≃J-isEquivalence .refl
≃g-isEquivalence .sym e .fwd-eq = ≃M-isEquivalence .sym (e .fwd-eq)
≃g-isEquivalence .sym e .bwd-eq = ≃J-isEquivalence .sym (e .bwd-eq)
≃g-isEquivalence .trans e₁ e₂ .fwd-eq = ≃M-isEquivalence .trans (e₁ .fwd-eq) (e₂ .fwd-eq)
≃g-isEquivalence .trans e₁ e₂ .bwd-eq = ≃J-isEquivalence .trans (e₁ .bwd-eq) (e₂ .bwd-eq)

idg : (X : Obj) → X ⇒g X
idg X .fwd = idM
idg X .bwd = idJ
idg X .bwd⊣fwd = refl-⇔

_∘g_ : ∀ {X Y Z : Obj} → Y ⇒g Z → X ⇒g Y → X ⇒g Z
(f ∘g g) .fwd = f .fwd ∘M g .fwd
(f ∘g g) .bwd = g .bwd ∘J f .bwd
(f ∘g g) .bwd⊣fwd = trans-⇔ (f .bwd⊣fwd) (g .bwd⊣fwd)

-- TODO
--  3. category laws
--  4. products
--  5. lifting monad

module _ where

  open Category

  cat : Category (suc 0ℓ) 0ℓ 0ℓ
  cat .obj = Obj
  cat ._⇒_ = _⇒g_
  cat ._≈_ = _≃g_
  cat .isEquiv = ≃g-isEquivalence
  cat .id = idg
  cat ._∘_ = _∘g_
  cat .∘-cong = {!!}
  cat .id-left = {!!}
  cat .id-right = {!!}
  cat .assoc = {!!}

module _ where

  open HasProducts

  _⊗_ : Obj → Obj → Obj
  (X ⊗ Y) .carrier = X .carrier × Y .carrier
  (X ⊗ Y) .meets = {!!}
  (X ⊗ Y) .joins = {!!}

  products : HasProducts cat
  products .prod = _⊗_
  products .p₁ = {!!}
  products .p₂ = {!!}
  products .pair = {!!}
