{-# OPTIONS --postfix-projections --prop --safe #-}

module conjugate where

open import Level
open import prop hiding (_∨_; ⊥; _∧_)
open import prop-setoid using (IsEquivalence)
open import preorder
open import categories
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_)

-- Category of bounded lattices with "annihilator separation" (the annihilator map x ↦ { z | z # x } is
-- injective) and Tarski conjugates between them.

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier

  open Preorder carrier public
  open MeetSemilattice meets renaming (idem to ∧-idem; interchange to ∧-interchange) public
  open JoinSemilattice joins renaming (idem to ∨-idem; interchange to ∨-interchange) public

  _#_ : carrier .Preorder.Carrier -> carrier .Preorder.Carrier -> Prop
  x # y = (x ∧ y) ≤ ⊥

  -- annihilator map preserves ≤ automatically
  #-mono : ∀ {x y} → x ≤ y → ∀ z → y # z → x # z
  #-mono x≤y z = ≤-trans (∧-mono x≤y ≤-refl)

  field
    -- and reflects it as an additional assumption
    #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → y ≤ x

open Obj

record _⇒c_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
    module XJ = JoinSemilattice (X .joins)
    module YJ = JoinSemilattice (Y .joins)
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    conjugate : ∀ {x y} → y Y.# right .fun x ⇔ left .fun y X.# x

  -- Both preserve joins?
  -- No: I think we only have "subadditivity", i.e. sub-join preservation:
  --    f(x ∨ x') ≤ f(x) ∨ f(x')
  -- without enough additional structure for "separation by disjointness" to obtain:
  --    (∀z . z ∧ x = ⊥ ⇔ z ∧ y = ⊥) ⟹ x ≃ y.
  right-∨ : X .joins =>J Y .joins
  right-∨ .func = right
  right-∨ .∨-preserving = {!   !}
  right-∨ .⊥-preserving = {!   !}

  left-∨ : Y .joins =>J X .joins
  left-∨ .func = left
  left-∨ .∨-preserving = {!   !}
  left-∨ .⊥-preserving = {!   !}

open _⇒c_

record _≃c_ {X Y : Obj} (f g : X ⇒c Y) : Prop where
  open preorder._=>_
  open _=>J_

  field
    right-eq : f .right ≃m g .right
    left-eq : f .left ≃m g .left

open _≃c_

open IsEquivalence
open preorder using (≃m-isEquivalence)

≃c-isEquivalence : ∀ {X Y} → IsEquivalence (_≃c_ {X} {Y})
≃c-isEquivalence .refl .right-eq = ≃m-isEquivalence .refl
≃c-isEquivalence .refl .left-eq = ≃m-isEquivalence .refl
≃c-isEquivalence .sym e .right-eq = ≃m-isEquivalence .sym (e .right-eq)
≃c-isEquivalence .sym e .left-eq = ≃m-isEquivalence .sym (e .left-eq)
≃c-isEquivalence .trans e₁ e₂ .right-eq = ≃m-isEquivalence .trans (e₁ .right-eq) (e₂ .right-eq)
≃c-isEquivalence .trans e₁ e₂ .left-eq = ≃m-isEquivalence .trans (e₁ .left-eq) (e₂ .left-eq)

idc : (X : Obj) → X ⇒c X
idc X .right = id
idc X .left = id
idc X .conjugate = refl-⇔

_∘c_ : ∀ {X Y Z : Obj} → Y ⇒c Z → X ⇒c Y → X ⇒c Z
(f ∘c g) .right = f .right ∘ g .right
(f ∘c g) .left = g .left ∘ f .left
(f ∘c g) .conjugate = trans-⇔ (f .conjugate) (g .conjugate)

∘c-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒c Z}{g₁ g₂ : X ⇒c Y} → f₁ ≃c f₂ → g₁ ≃c g₂ → (f₁ ∘c g₁) ≃c (f₂ ∘c g₂)
∘c-cong f₁≈f₂ g₁≈g₂ .right-eq = ∘-cong (f₁≈f₂ .right-eq) (g₁≈g₂ .right-eq)
∘c-cong f₁≈f₂ g₁≈g₂ .left-eq = ∘-cong (g₁≈g₂ .left-eq) (f₁≈f₂ .left-eq)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒c_
cat .Category._≈_ = _≃c_
cat .Category.isEquiv = ≃c-isEquivalence
cat .Category.id = idc
cat .Category._∘_ = _∘c_
cat .Category.∘-cong = ∘c-cong
cat .Category.id-left .right-eq = id-left
cat .Category.id-left .left-eq = id-right
cat .Category.id-right .right-eq = id-right
cat .Category.id-right .left-eq = id-left
cat .Category.assoc f g h .right-eq = assoc (f .right) (g .right) (h .right)
cat .Category.assoc f g h .left-eq =
  ≃m-isEquivalence .sym (assoc (h .left) (g .left) (f .left))
