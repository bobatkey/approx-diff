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

-- Category of Heyting algebras (residuated lattices) and Tarski conjugates between them.
-- FIXME: express using the standard definition of Heyting algebra (although I think this is equivalent).
-- To bounded lattices, Heyting algebras add distributivity and "disjointness separation" (the annihilator map
-- Ann(x) := { z | z # x } is injective). The latter corresponds to Ann(x) being a principal ideal ↓(¬x)
-- where ¬x is the unique pseudocomplement. This seems to be the minimum structure required for conjugates to
-- preserve joins; in particular we don't need double negation.

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

  #-sym : ∀ {x y} → x # y → y # x
  #-sym = ≤-trans ∧-comm

  ⊥-# : ∀ {x} → ⊥ # x
  ⊥-# = π₁

  -- annihilator map preserves ≤ automatically, and reflects ≤ as an additional assumption
  #-mono : ∀ {x y} → x ≤ y → ∀ z → y # z → x # z
  #-mono x≤y z = ≤-trans (∧-mono x≤y ≤-refl)

  field
    #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → y ≤ x
    ∧-∨-distrib : ∀ x y z → x ∧ (y ∨ z) ≤ (x ∧ y) ∨ (x ∧ z)
    ∨-∧-distrib : ∀ x y z → x ∨ (y ∧ z) ≤ (x ∨ y) ∧ (x ∨ z)

  #-distrib : ∀ {x y z} → x # y → x # z → x # (y ∨ z)
  #-distrib x#y x#z = ≤-trans (∧-∨-distrib _ _ _) (≤-trans (∨-mono x#y x#z) (∨-idem .proj₁))

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
    module YM = MeetSemilattice (Y .meets)
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    -- since disjointness determines the order, really just another way of saying that left is adjoint to
    -- (¬ ∘ right) or equivalently that right is adjoint to (¬ ∘ left)
    conjugate : ∀ {x y} → y Y.# right .fun x ⇔ left .fun y X.# x

  right-∨ : X .joins =>J Y .joins
  right-∨ .func = right
  right-∨ .∨-preserving {x} {x'} = Y .#-reflect suffices
    where
    suffices : ∀ y → right .fun (x XJ.∨ x') Y.# y → (right .fun x YJ.∨ right .fun x') Y.# y
    suffices y fx∨x'#y =
      Y.#-sym (Y.#-distrib
        (conjugate .proj₂ (X.#-sym (X.#-mono (inl X) (left .fun y) (X.#-sym gy#x∨x'))))
        (conjugate .proj₂ (X.#-sym (X.#-mono (inr X) (left .fun y) (X.#-sym gy#x∨x')))))
      where
      gy#x∨x' : left .fun y X.# (x XJ.∨ x')
      gy#x∨x' = conjugate .proj₁ (Y.#-sym fx∨x'#y)

  right-∨ .⊥-preserving = Y .#-reflect λ _ _ -> π₁ Y

  left-∨ : Y .joins =>J X .joins
  left-∨ .func = left
  left-∨ .∨-preserving {y} {y'} = X .#-reflect suffices
    where
    suffices : ∀ x → left .fun (y YJ.∨ y') X.# x → (left .fun y XJ.∨ left .fun y') X.# x
    suffices x gy∨y'#x =
      X.#-sym (X.#-distrib
        (X.#-sym (conjugate .proj₁ (Y.#-mono (inl Y) (right .fun x) fx#y∨y')))
        (X.#-sym (conjugate .proj₁ (Y.#-mono (inr Y) (right .fun x) fx#y∨y'))))
      where
      fx#y∨y' : (y YJ.∨ y') Y.# right .fun x
      fx#y∨y' = conjugate .proj₂ gy∨y'#x
  left-∨ .⊥-preserving = X .#-reflect λ _ _ -> π₁ X

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

-- CMon enrichment
module _ {X Y : Obj} where
  open _=>_
  open preorder._=>_
  open preorder._≃m_

  private
    module YJ = JoinSemilattice (Y .joins)
    module XJ = JoinSemilattice (X .joins)

  εm : X ⇒c Y
  εm .right = join-semilattice.εm {X = X .joins} {Y = Y .joins} ._=>J_.func
  εm .left = join-semilattice.εm {X = Y .joins} {Y = X .joins} ._=>J_.func
  εm .conjugate .proj₁ _ = π₁ X
  εm .conjugate .proj₂ _ = π₂ Y

  _+m_ : X ⇒c Y → X ⇒c Y → X ⇒c Y
  (f +m g) .right = join-semilattice._+m_ (right-∨ f) (right-∨ g) ._=>J_.func
  (f +m g) .left = join-semilattice._+m_ (left-∨ f) (left-∨ g) ._=>J_.func
  (f +m g) .conjugate {x} {y} .proj₁ = {!   !}
  (f +m g) .conjugate {x} {y} .proj₂ = {!   !}
