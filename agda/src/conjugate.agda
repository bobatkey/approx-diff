{-# OPTIONS --postfix-projections --prop --safe #-}

module conjugate where

open import Level
open import prop hiding (_∨_; ⊥; _∧_)
open import prop-setoid using (IsEquivalence)
open import preorder
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_)

-- Category of bounded lattices and Tarski conjugates between them.

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
  x # y = x ∧ y ≃ ⊥

  blib : ∀ x y → (∀ z → x # z ⇔ y # z) -> x ≃ y
  blib x y = {!   !}

open Obj

record _⇒c_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>M_
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    conjugate : ∀ {x y} → y Y.# right .fun x ⇔ left .fun y X.# x

open _⇒c_

-- sanity check: if conjugates exist they are unique
module _ {X Y} (f g : X ⇒c Y) (right≃right : f .right ≃m g .right) where
  open preorder._=>_
  open _≃m_

  module X = Obj X
  module Y = Obj Y

  blah : ∀ {x y} → y Y.# g .right .fun x ⇔ y Y.# f .right .fun x
  blah .proj₁ y#gx = Y .≃-trans (Y .≃-sym (∧-cong Y (Y .≃-refl) (Y .≃-sym (right≃right .eqfun _)))) y#gx
  blah .proj₂ y#fx = Y .≃-trans (∧-cong Y (Y .≃-refl) (Y .≃-sym (right≃right .eqfun _))) y#fx

  -- f .left and g .left exhibit the same disjointness behaviour
  lemma : ∀ {x y} → f .left .fun y X.# x ⇔ g .left .fun y X.# x
  lemma = trans-⇔ (sym-⇔ (trans-⇔ blah (f .conjugate))) (g .conjugate)

  uniqueness : f .left ≃m g .left
  uniqueness .eqfun y = blib X (f .left .fun y) (g .left .fun y) λ z → lemma {x = z} {y}
