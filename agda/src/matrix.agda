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

-- Pointwise equality of matrices.
_≈ₘ_ : ∀ {m n} → Mat m n → Mat m n → Prop ℓ
M ≈ₘ N = ∀ i j → M i j ≈ N i j

open import Level using (Level; _⊔_)
open import prop using (tt)
open import prop-setoid using (IsEquivalence)
open import categories using (Category)

≈ₘ-isEquiv : ∀ {m n} → IsEquivalence (_≈ₘ_ {m} {n})
≈ₘ-isEquiv .IsEquivalence.refl i j = refl
≈ₘ-isEquiv .IsEquivalence.sym p i j = sym (p i j)
≈ₘ-isEquiv .IsEquivalence.trans p q i j = trans (p i j) (q i j)

∘-cong : ∀ {m n k} {M₁ M₂ : Mat m n} {N₁ N₂ : Mat n k} →
  M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → (M₁ ∘ N₁) ≈ₘ (M₂ ∘ N₂)
∘-cong {m} {n} p q i k = Σ-cong {n} (λ j → ·-cong (p i j) (q j k))
  where
    Σ-cong : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ≈ g i) → Σ {n} f ≈ Σ {n} g
    Σ-cong {zero} _ = refl
    Σ-cong {suc n} h = +-cong (h zero) (Σ-cong {n} (λ i → h (suc i)))

id-left : ∀ {m n} {M : Mat m n} → (I ∘ M) ≈ₘ M
id-left {m} {n} i k = {!!}

id-right : ∀ {m n} {M : Mat m n} → (M ∘ I) ≈ₘ M
id-right {m} {n} i k = {!!}

assoc : ∀ {m n k l} (M : Mat m n) (N : Mat n k) (P : Mat k l) →
  ((M ∘ N) ∘ P) ≈ₘ (M ∘ (N ∘ P))
assoc M N P i l = {!!}

-- Σ respects pointwise ≈.
Σ-cong : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ≈ g i) → Σ {n} f ≈ Σ {n} g
Σ-cong {zero} _ = refl
Σ-cong {suc n} h = +-cong (h zero) (Σ-cong {n} (λ i → h (suc i)))

-- Picking out the i-th element: Σⱼ e(i,j) · f(j) ≈ f(i).
Σ-unit : ∀ {n} (i : Fin n) (f : Fin n → Carrier) → Σ {n} (λ j → e i j · f j) ≈ f i
Σ-unit = {!!}

-- Distributing · over Σ on the right: (Σⱼ fⱼ) · x ≈ Σⱼ (fⱼ · x).
Σ-·-distribᵣ : ∀ {n} (f : Fin n → Carrier) (x : Carrier) → Σ {n} f · x ≈ Σ {n} (λ j → f j · x)
Σ-·-distribᵣ = {!!}

-- Interchange (Fubini): Σᵢ Σⱼ f(i,j) ≈ Σⱼ Σᵢ f(i,j).
Σ-interchange : ∀ {m n} (f : Fin m → Fin n → Carrier) → Σ {m} (λ i → Σ {n} (f i)) ≈ Σ {n} (λ j → Σ {m} (λ i → f i j))
Σ-interchange = {!!}

cat : Category _ _ _
cat .Category.obj = ℕ
cat .Category._⇒_ m n = Mat n m
cat .Category._≈_ = _≈ₘ_
cat .Category.isEquiv = ≈ₘ-isEquiv
cat .Category.id n = I
cat .Category._∘_ = _∘_
cat .Category.∘-cong = ∘-cong
cat .Category.id-left = id-left
cat .Category.id-right = id-right
cat .Category.assoc = assoc
