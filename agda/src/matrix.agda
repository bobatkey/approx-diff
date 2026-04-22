{-# OPTIONS --postfix-projections --prop --safe #-}

open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

module matrix {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

open CommutativeSemiring S public
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

infixl 21 _∘_

_ᵀ : ∀ {m n} → Mat m n → Mat n m
(M ᵀ) i j = M j i

-- Pointwise equality of matrices.
_≈ₘ_ : ∀ {m n} → Mat m n → Mat m n → Prop ℓ
M ≈ₘ N = ∀ i j → M i j ≈ N i j

open import Level using (Level; _⊔_)
open import prop using (tt)
open import prop-setoid using (IsEquivalence)
open import categories using (Category)

-- Any reflexive relation preserved by + is preserved by Σ.
module +-to-Σ
  {p} (_~_ : Carrier → Carrier → Prop p)
  (~-refl : ∀ {x} → x ~ x)
  (+-preserves : ∀ {x₁ x₂ y₁ y₂} → x₁ ~ x₂ → y₁ ~ y₂ → (x₁ + y₁) ~ (x₂ + y₂))
  where

  Σ-preserves : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ~ g i) → Σ {n} f ~ Σ {n} g
  Σ-preserves {zero} _ = ~-refl
  Σ-preserves {suc n} h = +-preserves (h zero) (Σ-preserves {n} (λ i → h (suc i)))

Σ-cong : ∀ {n} {f g : Fin n → Carrier} → (∀ i → f i ≈ g i) → Σ {n} f ≈ Σ {n} g
Σ-cong = +-to-Σ.Σ-preserves _≈_ refl +-cong

-- Kronecker delta is symmetric.
e-sym : ∀ {n} (i j : Fin n) → e i j ≈ e j i
e-sym zero zero = refl
e-sym zero (suc _) = refl
e-sym (suc _) zero = refl
e-sym (suc i) (suc j) = e-sym i j

-- Σ of zeros is zero.
Σ-ε : ∀ {n} → Σ {n} (λ _ → ε) ≈ ε
Σ-ε {zero} = refl
Σ-ε {suc n} = trans +-lunit (Σ-ε {n})

-- Picking out the i-th element: Σⱼ e(i,j) · f(j) ≈ f(i).
Σ-unit : ∀ {n} (i : Fin n) (f : Fin n → Carrier) → Σ {n} (λ j → e i j · f j) ≈ f i
Σ-unit {suc n} zero f =
  trans (+-cong ·-lunit (trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})))
        (trans +-comm +-lunit)
Σ-unit {suc n} (suc i) f =
  trans (+-cong ε-annihilₗ refl)
        (trans +-lunit (Σ-unit i (λ j → f (suc j))))

-- Distributing · over Σ on the right: (Σⱼ fⱼ) · x ≈ Σⱼ (fⱼ · x).
Σ-·-distribᵣ : ∀ {n} (f : Fin n → Carrier) (x : Carrier) → Σ {n} f · x ≈ Σ {n} (λ j → f j · x)
Σ-·-distribᵣ {zero} f x = ε-annihilₗ
Σ-·-distribᵣ {suc n} f x =
  trans ·-+-distribᵣ (+-cong refl (Σ-·-distribᵣ {n} (λ j → f (suc j)) x))

-- Distributing · over Σ on the left: x · (Σⱼ fⱼ) ≈ Σⱼ (x · fⱼ).
Σ-·-distribₗ : ∀ {n} (x : Carrier) (f : Fin n → Carrier) → x · Σ {n} f ≈ Σ {n} (λ j → x · f j)
Σ-·-distribₗ {n} x f =
  trans ·-comm (trans (Σ-·-distribᵣ f x) (Σ-cong {n} (λ j → ·-comm)))

+-interchange : ∀ {a b c d} → (a + b) + (c + d) ≈ (a + c) + (b + d)
+-interchange =
  trans +-assoc (trans (+-cong refl (trans (sym +-assoc) (trans (+-cong +-comm refl) +-assoc))) (sym +-assoc))

-- Σ distributes over +: Σ g + Σ h ≈ Σ (λ j → g j + h j).
Σ-+ : ∀ {n} (g h : Fin n → Carrier) → Σ {n} g + Σ {n} h ≈ Σ {n} (λ j → g j + h j)
Σ-+ {zero} g h = +-lunit
Σ-+ {suc n} g h =
  trans +-interchange (+-cong refl (Σ-+ {n} (λ j → g (suc j)) (λ j → h (suc j))))

-- Swapping two finite sums.
Σ-interchange : ∀ {m n} (f : Fin m → Fin n → Carrier) → Σ {m} (λ i → Σ {n} (f i)) ≈ Σ {n} (λ j → Σ {m} (λ i → f i j))
Σ-interchange {zero} {n} f = sym (Σ-ε {n})
Σ-interchange {suc m} {n} f =
  trans (+-cong refl (Σ-interchange {m} {n} (λ i → f (suc i))))
        (Σ-+ {n} (f zero) (λ j → Σ {m} (λ i → f (suc i) j)))


≈ₘ-isEquiv : ∀ {m n} → IsEquivalence (_≈ₘ_ {m} {n})
≈ₘ-isEquiv .IsEquivalence.refl i j = refl
≈ₘ-isEquiv .IsEquivalence.sym p i j = sym (p i j)
≈ₘ-isEquiv .IsEquivalence.trans p q i j = trans (p i j) (q i j)

∘-cong : ∀ {m n k} {M₁ M₂ : Mat m n} {N₁ N₂ : Mat n k} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → M₁ ∘ N₁ ≈ₘ M₂ ∘ N₂
∘-cong {m} {n} p q i k = Σ-cong {n} (λ j → ·-cong (p i j) (q j k))

id-left : ∀ {m n} {M : Mat m n} → I ∘ M ≈ₘ M
id-left {M = M} i k = Σ-unit i (λ j → M j k)

id-right : ∀ {m n} {M : Mat m n} → M ∘ I ≈ₘ M
id-right {n = n} {M = M} i k =
  trans (Σ-cong {n} (λ j → ·-cong refl (e-sym j k)))
        (trans (Σ-cong {n} (λ j → ·-comm)) (Σ-unit k (M i)))

assoc : ∀ {m n k l} (M : Mat m n) (N : Mat n k) (P : Mat k l) → (M ∘ N) ∘ P ≈ₘ M ∘ (N ∘ P)
assoc {n = n} {k} M N P i l =
  trans (Σ-cong {k} (λ j → Σ-·-distribᵣ (λ r → M i r · N r j) (P j l)))
    (trans (Σ-cong {k} (λ j → Σ-cong {n} (λ r → ·-assoc)))
      (trans (Σ-interchange {k} {n} (λ j r → M i r · (N r j · P j l)))
        (Σ-cong {n} (λ r → sym (Σ-·-distribₗ (M i r) (λ j → N r j · P j l))))))

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

open import categories using (HasTerminal; IsTerminal; HasInitial; IsInitial)

-- 0 is a zero object (both terminal and initial).
terminal : HasTerminal cat
terminal .HasTerminal.witness = 0
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal ()
terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f ()

initial : HasInitial cat
initial .HasInitial.witness = 0
initial .HasInitial.is-initial .IsInitial.from-initial _ ()
initial .HasInitial.is-initial .IsInitial.from-initial-ext f _ ()

open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import Data.Nat using () renaming (_+_ to _+ℕ_)

-- Pointwise addition of matrices.
_+ₘ_ : ∀ {m n} → Mat m n → Mat m n → Mat m n
(M +ₘ N) i j = M i j + N i j

infixl 21 _+ₘ_

-- Zero matrix.
εₘ : ∀ {m n} → Mat m n
εₘ _ _ = ε

-- Σ over zero function is zero.
Σ-+ₘ : ∀ {n} {f : Fin n → Carrier} → Σ {n} (λ i → f i + ε) ≈ Σ {n} f
Σ-+ₘ {n} = Σ-cong {n} (λ i → trans +-comm +-lunit)

-- Σ distributes over pointwise addition.
Σ-distribₗ : ∀ {n} (f g : Fin n → Carrier) → Σ {n} (λ i → f i + g i) ≈ Σ {n} f + Σ {n} g
Σ-distribₗ {n} f g = sym (Σ-+ {n} f g)

comp-bilinear₁ : ∀ {m n k} (M₁ M₂ : Mat m n) (N : Mat n k) → (M₁ +ₘ M₂) ∘ N ≈ₘ (M₁ ∘ N) +ₘ (M₂ ∘ N)
comp-bilinear₁ {n = n} M₁ M₂ N i k =
  trans (Σ-cong {n} (λ j → ·-+-distribᵣ))
        (sym (Σ-+ {n} (λ j → M₁ i j · N j k) (λ j → M₂ i j · N j k)))

comp-bilinear₂ : ∀ {m n k} (M : Mat m n) (N₁ N₂ : Mat n k) → M ∘ (N₁ +ₘ N₂) ≈ₘ (M ∘ N₁) +ₘ (M ∘ N₂)
comp-bilinear₂ {n = n} M N₁ N₂ i k =
  trans (Σ-cong {n} (λ j → ·-+-distribₗ))
        (sym (Σ-+ {n} (λ j → M i j · N₁ j k) (λ j → M i j · N₂ j k)))

comp-bilinear-ε₁ : ∀ {m n k} (N : Mat n k) → εₘ ∘ N ≈ₘ εₘ {m} {k}
comp-bilinear-ε₁ {n = n} N i k =
  trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

comp-bilinear-ε₂ : ∀ {m n k} (M : Mat m n) → M ∘ εₘ ≈ₘ εₘ {m} {k}
comp-bilinear-ε₂ {n = n} M i k =
  trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

private
  hom-setoid : ℕ → ℕ → Setoid _ _
  hom-setoid m n .Setoid.Carrier = Mat n m
  hom-setoid m n .Setoid._≈_ = _≈ₘ_
  hom-setoid m n .Setoid.isEquivalence = ≈ₘ-isEquiv

cmon : CMonEnriched cat
cmon .CMonEnriched.homCM m n .CommutativeMonoid.ε = εₘ
cmon .CMonEnriched.homCM m n .CommutativeMonoid._+_ = _+ₘ_
cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-cong p q i j = +-cong (p i j) (q i j)
cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-lunit i j = +-lunit
cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-assoc i j = +-assoc
cmon .CMonEnriched.homCM m n .CommutativeMonoid.+-comm i j = +-comm
cmon .CMonEnriched.comp-bilinear₁ = comp-bilinear₁
cmon .CMonEnriched.comp-bilinear₂ = comp-bilinear₂
cmon .CMonEnriched.comp-bilinear-ε₁ = comp-bilinear-ε₁
cmon .CMonEnriched.comp-bilinear-ε₂ = comp-bilinear-ε₂

-- Biproduct: m ⊕ n = m +ℕ n.

p₁ : ∀ {m n} → Mat m (m +ℕ n)
p₁ {suc m} zero zero = ι
p₁ {suc m} zero (suc _) = ε
p₁ {suc m} (suc i) zero = ε
p₁ {suc m} (suc i) (suc j) = p₁ {m} i j

p₂ : ∀ {m n} → Mat n (m +ℕ n)
p₂ {zero}  i j = e i j
p₂ {suc m} i zero = ε
p₂ {suc m} i (suc j) = p₂ {m} i j

in₁ : ∀ {m n} → Mat (m +ℕ n) m
in₁ {suc m} zero zero = ι
in₁ {suc m} zero (suc _) = ε
in₁ {suc m} (suc i) zero = ε
in₁ {suc m} (suc i) (suc j) = in₁ {m} i j

in₂ : ∀ {m n} → Mat (m +ℕ n) n
in₂ {zero}  i j = e i j
in₂ {suc m} zero _ = ε
in₂ {suc m} (suc i) j = in₂ {m} i j

private
  Σ-ε· : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → ε · f j) ≈ ε
  Σ-ε· {n} f = trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

  ·ε-Σ : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → f j · ε) ≈ ε
  ·ε-Σ {n} f = trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

id-1 : ∀ m n → p₁ {m} {n} ∘ in₁ {m} {n} ≈ₘ I
id-1 (suc m) n zero zero =
  trans (+-cong ·-lunit (Σ-ε· {m +ℕ n} _)) (trans +-comm +-lunit)
id-1 (suc m) n zero (suc k) =
  trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
id-1 (suc m) n (suc i) zero =
  trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
id-1 (suc m) n (suc i) (suc k) =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-1 m n i k))

id-2 : ∀ m n → p₂ {m} {n} ∘ in₂ {m} {n} ≈ₘ I
id-2 zero n i j = Σ-unit i (λ k → e k j)
id-2 (suc m) n i j =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-2 m n i j))

zero-1 : ∀ m n → p₁ {m} {n} ∘ in₂ {m} {n} ≈ₘ εₘ
zero-1 zero n ()
zero-1 (suc m) n zero j =
  trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
zero-1 (suc m) n (suc i) j =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-1 m n i j))

zero-2 : ∀ m n → p₂ {m} {n} ∘ in₁ {m} {n} ≈ₘ εₘ
zero-2 zero n _ ()
zero-2 (suc m) n i zero =
  trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
zero-2 (suc m) n i (suc j) =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-2 m n i j))

id-+ : ∀ m n → (in₁ {m} {n} ∘ p₁ {m} {n}) +ₘ (in₂ {m} {n} ∘ p₂ {m} {n}) ≈ₘ I {m +ℕ n}
id-+ zero n i j =
  trans +-lunit (Σ-unit i (λ k → e k j))
id-+ (suc m) n zero zero =
  trans (+-cong (+-cong ·-lunit (Σ-ε· {m} _)) (Σ-ε· {n} _))
        (trans (+-cong (trans +-comm +-lunit) refl) (trans +-comm +-lunit))
id-+ (suc m) n zero (suc j) =
  trans (+-cong (+-cong ε-annihilᵣ (Σ-ε· {m} _)) (Σ-ε· {n} _))
        (trans (+-cong +-lunit refl) +-lunit)
id-+ (suc m) n (suc i) zero =
  trans (+-cong (+-cong ε-annihilₗ (·ε-Σ {m} _)) (·ε-Σ {n} _))
        (trans (+-cong +-lunit refl) +-lunit)
id-+ (suc m) n (suc i) (suc j) =
  trans (+-cong (+-cong ε-annihilₗ refl) refl) (trans (+-cong +-lunit refl) (id-+ m n i j))

biproduct : ∀ m n → Biproduct cmon m n
biproduct m n .Biproduct.prod = m +ℕ n
biproduct m n .Biproduct.p₁ = p₁ {m} {n}
biproduct m n .Biproduct.p₂ = p₂ {m} {n}
biproduct m n .Biproduct.in₁ = in₁ {m} {n}
biproduct m n .Biproduct.in₂ = in₂ {m} {n}
biproduct m n .Biproduct.id-1 = id-1 m n
biproduct m n .Biproduct.id-2 = id-2 m n
biproduct m n .Biproduct.zero-1 = zero-1 m n
biproduct m n .Biproduct.zero-2 = zero-2 m n
biproduct m n .Biproduct.id-+ = id-+ m n

-- Vector concatenation, a monoid homomorphism preserving pointwise additive structure.
concat : ∀ {x y} → Vec x → Vec y → Vec (x +ℕ y)
concat {zero} u v = v
concat {suc x} u v zero = u zero
concat {suc x} u v (suc i) = concat {x} (λ j → u (suc j)) v i

concat-preserves : ∀ {x y p} (_~_ : Carrier → Carrier → Prop p) {u₁ u₂ : Vec x} {v₁ v₂ : Vec y} →
                   (∀ i → u₁ i ~ u₂ i) → (∀ i → v₁ i ~ v₂ i) → ∀ i → concat u₁ v₁ i ~ concat u₂ v₂ i
concat-preserves {zero} _ p q i = q i
concat-preserves {suc x} _ p q zero = p zero
concat-preserves {suc x} _~_ p q (suc i) = concat-preserves {x} _~_ (λ j → p (suc j)) q i

concat-+ : ∀ {x y} (u₁ u₂ : Vec x) (v₁ v₂ : Vec y) →
           ∀ i → concat (λ j → u₁ j + u₂ j) (λ j → v₁ j + v₂ j) i ≈ concat u₁ v₁ i + concat u₂ v₂ i
concat-+ {zero} u₁ u₂ v₁ v₂ i = refl
concat-+ {suc x} u₁ u₂ v₁ v₂ zero = refl
concat-+ {suc x} u₁ u₂ v₁ v₂ (suc i) = concat-+ {x} (λ j → u₁ (suc j)) (λ j → u₂ (suc j)) v₁ v₂ i

concat-ε : ∀ {x y} → ∀ i → concat {x} {y} (λ _ → ε) (λ _ → ε) i ≈ ε
concat-ε {zero} i = refl
concat-ε {suc x} zero = refl
concat-ε {suc x} (suc i) = concat-ε {x} i

-- Vector splitting (inverse of concat).
split₁ : ∀ {x y} → Vec (x +ℕ y) → Vec x
split₁ {suc x} w zero = w zero
split₁ {suc x} w (suc i) = split₁ {x} (λ j → w (suc j)) i

split₂ : ∀ {x y} → Vec (x +ℕ y) → Vec y
split₂ {zero} w = w
split₂ {suc x} w = split₂ {x} (λ j → w (suc j))

-- Round-trips: concat and split are inverse.
split₁-concat : ∀ {x y} (u : Vec x) (v : Vec y) (i : Fin x) → split₁ {x} (concat u v) i ≈ u i
split₁-concat {suc x} u v zero = refl
split₁-concat {suc x} u v (suc i) = split₁-concat {x} (λ j → u (suc j)) v i

split₂-concat : ∀ {x y} (u : Vec x) (v : Vec y) (i : Fin y) → split₂ {x} (concat u v) i ≈ v i
split₂-concat {zero} u v i = refl
split₂-concat {suc x} u v i = split₂-concat {x} (λ j → u (suc j)) v i

concat-split : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin (x +ℕ y)) → concat (split₁ {x} w) (split₂ {x} w) i ≈ w i
concat-split {zero} w i = refl
concat-split {suc x} w zero = refl
concat-split {suc x} w (suc i) = concat-split {x} (λ j → w (suc j)) i

-- Matrix multiplication by p₁/p₂ computes split₁/split₂.
Σ-p₁ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin x) → Σ {x +ℕ y} (λ j → p₁ {x} {y} i j · w j) ≈ split₁ {x} w i
Σ-p₁ {suc x} w zero =
  trans (+-cong ·-lunit (trans (Σ-cong {x +ℕ _} (λ j → ε-annihilₗ)) (Σ-ε {x +ℕ _})))
        (trans +-comm +-lunit)
Σ-p₁ {suc x} w (suc i) =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (Σ-p₁ {x} (λ j → w (suc j)) i))

Σ-p₂ : ∀ {x y} (w : Vec (x +ℕ y)) (i : Fin y) → Σ {x +ℕ y} (λ j → p₂ {x} {y} i j · w j) ≈ split₂ {x} w i
Σ-p₂ {zero} w i = Σ-unit i w
Σ-p₂ {suc x} w i =
  trans (+-cong ε-annihilₗ refl) (trans +-lunit (Σ-p₂ {x} (λ j → w (suc j)) i))

------------------------------------------------------------------------------
-- If + is idempotent then (S, +) is a join-semilattice with ⊥ = ε.
module Join (+-idem : ∀ {x} → (x + x) ≈ x) where

  infix 4 _≤_
  _≤_ : Carrier → Carrier → Prop _
  x ≤ y = (x + y) ≈ y

  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl = +-idem

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} xy yz = trans (sym (+-cong refl yz)) (trans (sym +-assoc) (trans (+-cong xy refl) yz))

  +-inl : ∀ {x y} → x ≤ (x + y)
  +-inl {x} {y} = trans (sym +-assoc) (+-cong +-idem refl)

  +-inr : ∀ {x y} → y ≤ (x + y)
  +-inr {x} {y} = trans (+-cong refl +-comm) (trans (sym +-assoc) (trans (+-cong +-idem refl) +-comm))

  +-lub : ∀ {x y z} → x ≤ z → y ≤ z → (x + y) ≤ z
  +-lub xz yz = trans +-assoc (trans (+-cong refl yz) xz)

  ε-bot : ∀ {x} → ε ≤ x
  ε-bot = +-lunit

  ----------------------------------------------------------------------------
  -- Tier 2.5: absorption. Makes · the meet in the induced order; combined with
  -- idempotence and the semiring's distributivity, S becomes a bounded
  -- distributive lattice with ⊥ = ε, ⊤ = ι, ∨ = +, ∧ = ·.
  module Lattice (absorb : ∀ {x y} → (x + (x · y)) ≈ x) where

    -- · is below both operands.
    ·-≤₁ : ∀ {x y} → (x · y) ≤ x
    ·-≤₁ = trans +-comm absorb

    ·-≤₂ : ∀ {x y} → (x · y) ≤ y
    ·-≤₂ = ≤-trans (≡→≤ ·-comm) ·-≤₁
      where ≡→≤ : ∀ {x y} → x ≈ y → x ≤ y
            ≡→≤ eq = trans (+-cong eq refl) +-idem

    -- Disjointness at the carrier level.
    infix 4 _#_
    _#_ : Carrier → Carrier → Prop _
    x # y = (x · y) ≈ ε

    --------------------------------------------------------------------------
    -- Tier 3: Heyting-like structure via #-reflect. Enough to construct
    -- conjugate pairs on X^n / X^m from matrices M : Mat n m.
    module Heyting (#-reflect : ∀ {x y} → (∀ z → y # z → x # z) → x ≤ y) where
      -- TODO: disjointness on vectors, to-conj construction.
