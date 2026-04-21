{-# OPTIONS --postfix-projections --prop --safe #-}

open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

module matrix {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

open CommutativeSemiring S
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

-- Vectors S^n.
Vec : ℕ → Set o
Vec n = Fin n → Carrier

-- Projection (just function application, but named for clarity).
proj : ∀ {n} → Fin n → Vec n → Carrier
proj i v = v i

-- Standard basis vector: ι at position i, ε elsewhere.
e : ∀ {n} → Fin n → Vec n
e zero zero = ι
e zero (suc _) = ε
e (suc i) zero = ε
e (suc i) (suc j) = e i j

-- Finite sum: Σᵢ f(i), using addition of S.
Σ : ∀ {n} → (Fin n → Carrier) → Carrier
Σ {zero} _ = ε
Σ {suc n} f = f zero + Σ {n} (λ i → f (suc i))

-- Dot product (sum of multiplications).
_⋅_ : ∀ {n} → Vec n → Vec n → Carrier
_⋅_ {n} u v = Σ {n} (λ i → u i · v i)

Mat : ℕ → ℕ → Set o
Mat m n = Fin m → Fin n → Carrier

-- Identity matrix (Kronecker delta).
I : ∀ {n} → Mat n n
I = e

-- Matrix composition: (M ∘ N)ᵢₖ = Σⱼ Mᵢⱼ · Nⱼₖ.
_∘_ : ∀ {m n k} → Mat m n → Mat n k → Mat m k
(M ∘ N) i k = Σ (λ j → M i j · N j k)

_ᵀ : ∀ {m n} → Mat m n → Mat n m
(M ᵀ) i j = M j i
