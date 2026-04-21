{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-semiring where

open import Level using (_⊔_)
open import prop-setoid using (Setoid)
open import commutative-monoid using (CommutativeMonoid)

record CommutativeSemiring {o e} (A : Setoid o e) : Set (o ⊔ e) where
  open Setoid A public

  field
    additive : CommutativeMonoid A
    multiplicative : CommutativeMonoid A

  open CommutativeMonoid additive public
    renaming (ε to ε; _+_ to _+_)
  open CommutativeMonoid multiplicative public
    renaming (_+_ to _·_; +-cong to ·-cong; +-lunit to ·-lunit; +-assoc to ·-assoc; +-comm to ·-comm)
    hiding (ε)

  ι : Carrier
  ι = CommutativeMonoid.ε multiplicative

  field
    ·-+-distribₗ : ∀ {x y z} → x · (y + z) ≈ (x · y) + (x · z)
    ε-annihilₗ : ∀ {x} → ε · x ≈ ε

  ·-+-distribᵣ : ∀ {x y z} → (y + z) · x ≈ (y · x) + (z · x)
  ·-+-distribᵣ = trans ·-comm (trans ·-+-distribₗ (+-cong ·-comm ·-comm))

  ε-annihilᵣ : ∀ {x} → x · ε ≈ ε
  ε-annihilᵣ = trans ·-comm ε-annihilₗ
