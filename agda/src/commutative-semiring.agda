{-# OPTIONS --prop --postfix-projections --safe #-}

module commutative-semiring where

open import Level using (_⊔_)
open import prop-setoid using (Setoid)
open import commutative-monoid using (CommutativeMonoid)

record CommutativeSemiring {o e} (A : Setoid o e) : Set (o ⊔ e) where
  open Setoid A public

  field
    additive       : CommutativeMonoid A
    multiplicative : CommutativeMonoid A

  open CommutativeMonoid additive public
    renaming (ε to ε; _+_ to _+_)
  open CommutativeMonoid multiplicative public
    renaming (_+_ to _·_;
              +-cong to ·-cong; +-lunit to ·-lunit; +-assoc to ·-assoc; +-comm to ·-comm)
    hiding (ε)

  ι : Carrier
  ι = CommutativeMonoid.ε multiplicative

  field
    distrib-l : ∀ {x y z} → (x · (y + z)) ≈ ((x · y) + (x · z))
    annihil-l : ∀ {x} → (ε · x) ≈ ε

  distrib-r : ∀ {x y z} → ((y + z) · x) ≈ ((y · x) + (z · x))
  distrib-r = trans ·-comm (trans distrib-l (+-cong ·-comm ·-comm))

  annihil-r : ∀ {x} → (x · ε) ≈ ε
  annihil-r = trans ·-comm annihil-l
