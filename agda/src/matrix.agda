{-# OPTIONS --postfix-projections --prop --safe #-}

open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

module matrix {o ℓ} {A : Setoid o ℓ} (R : CommutativeSemiring A) where

open CommutativeSemiring R
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

-- Vectors: R^n.
Vec : ℕ → Set o
Vec n = Fin n → Carrier

-- Projection (just function application, but named for clarity).
proj : ∀ {n} → Fin n → Vec n → Carrier
proj i v = v i

-- Standard basis vector: ι at position i, ε elsewhere.
e : ∀ {n} → Fin n → Vec n
e zero    zero    = ι
e zero    (suc _) = ε
e (suc i) zero    = ε
e (suc i) (suc j) = e i j

-- Finite sum: Σᵢ f(i), using additive monoid.
Σ : ∀ {n} → (Fin n → Carrier) → Carrier
Σ {zero}  _ = ε
Σ {suc n} f = f zero + Σ {n} (λ i → f (suc i))

-- Dot product: u ⋅ v = Σᵢ uᵢ · vᵢ.
_⋅_ : ∀ {n} → Vec n → Vec n → Carrier
_⋅_ {n} u v = Σ {n} (λ i → u i · v i)
