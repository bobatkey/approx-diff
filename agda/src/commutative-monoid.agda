{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-monoid where

open import Level
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import prop
open import prop-setoid
  using (Setoid; IsEquivalence; idS; _∘S_; ⊗-setoid; 𝟙; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≃s_; ≃m-isEquivalence to ≃s-isEquivalence)

------------------------------------------------------------------------------
-- Commutative Monoid structure on setoids
--
record CommutativeMonoid {o e} (A : Setoid o e) : Set (o ⊔ e) where
  open Setoid A
  field
    ε   : Carrier
    _+_ : Carrier → Carrier → Carrier

  infixl 21 _+_

  field
    +-cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ + y₁) ≈ (x₂ + y₂)
    +-lunit : ∀ {x} → (ε + x) ≈ x
    +-assoc : ∀ {x y z} → ((x + y) + z) ≈ (x + (y + z))
    +-comm  : ∀ {x y} → (x + y) ≈ (y + x)

------------------------------------------------------------------------------
-- Idempotent commutative monoids (semilattices)have an order.

record Idempotent {o e} {A : Setoid o e} (M : CommutativeMonoid A) : Set (o ⊔ e) where
  open Setoid A
  open CommutativeMonoid M

  field
    +-idem : ∀ {x} → (x + x) ≈ x

  _≤_ : Carrier → Carrier → Prop e
  x ≤ y = (x + y) ≈ y

  open import basics using (IsPreorder; IsJoin; IsBottom)

  ≤-isPreorder : IsPreorder _≤_
  ≤-isPreorder .IsPreorder.refl = +-idem
  ≤-isPreorder .IsPreorder.trans {x} {y} {z} x≤y y≤z =
    trans (+-cong refl (sym y≤z))
      (trans (sym +-assoc) (trans (+-cong x≤y refl) y≤z))

  +-isJoin : IsJoin ≤-isPreorder _+_
  +-isJoin .IsJoin.inl {x} {y} =
    trans (sym +-assoc) (+-cong +-idem refl)
  +-isJoin .IsJoin.inr {x} {y} =
    trans (+-cong refl +-comm) (trans (sym +-assoc) (trans (+-cong +-idem refl) +-comm))
  +-isJoin .IsJoin.[_,_] {x} {y} {z} x≤z y≤z =
    trans +-assoc (trans (+-cong refl y≤z) x≤z)

  ε-isBottom : IsBottom ≤-isPreorder ε
  ε-isBottom .IsBottom.≤-bottom = +-lunit

------------------------------------------------------------------------------

record _=[_]>_ {o e}{A B : Setoid o e}(X : CommutativeMonoid A)(f : A ⇒s B)(Y : CommutativeMonoid B) : Prop (o ⊔ e) where
  private
    module X = CommutativeMonoid X
    module Y = CommutativeMonoid Y
  open _⇒s_ f
  open Setoid B
  field
    preserve-ε : func X.ε ≈ Y.ε
    preserve-+ : ∀ {x₁ x₂} → func (x₁ X.+ x₂) ≈ (func x₁ Y.+ func x₂)
open _=[_]>_

module _ where

  open CommutativeMonoid

  𝟙cm : ∀ {o e} → CommutativeMonoid (𝟙 {o} {e})
  𝟙cm .ε = lift tt
  𝟙cm ._+_ _ _ = lift tt
  𝟙cm .+-cong _ _ = tt
  𝟙cm .+-lunit = tt
  𝟙cm .+-assoc = tt
  𝟙cm .+-comm = tt

  _⊗_ : ∀ {o e}{A B : Setoid o e} →
        CommutativeMonoid A →
        CommutativeMonoid B →
        CommutativeMonoid (⊗-setoid A B)
  (X ⊗ Y) .ε = X .ε , Y .ε
  (X ⊗ Y) ._+_ (x₁ , y₁) (x₂ , y₂) = X ._+_ x₁ x₂ , Y ._+_ y₁ y₂
  (X ⊗ Y) .+-cong (x₁≈x₂ , y₁≈y₂) (x'₁≈x'₂ , y'₁≈y'₂) =
     X .+-cong x₁≈x₂ x'₁≈x'₂ , Y .+-cong y₁≈y₂ y'₁≈y'₂
  (X ⊗ Y) .+-lunit = X .+-lunit , Y .+-lunit
  (X ⊗ Y) .+-assoc = X .+-assoc , Y .+-assoc
  (X ⊗ Y) .+-comm = X .+-comm , Y .+-comm
