{-# OPTIONS --postfix-projections --prop --safe #-}

module conjugate where

open import Level
open import prop hiding (_∨_; ⊥; _∧_)
open import preorder
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_)

-- Category of bounded lattices and conjugate maps between them.

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

open Obj

record _⇒c_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>M_
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
    module XM = MeetSemilattice (X .meets)
    module YM = MeetSemilattice (Y .meets)
    module XJ = JoinSemilattice (X .joins)
    module YJ = JoinSemilattice (Y .joins)
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    left⊣right : ∀ {x y} → (y Y.# (right .fun x)) ⇔ (left .fun y) X.# x
