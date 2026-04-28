{-# OPTIONS --postfix-projections --prop --safe #-}

module matrix where

open import Level using (0ℓ)
open import prop-setoid using (Setoid)
open import commutative-semiring using (CommutativeSemiring)

-- Matrices over a commutative semiring S. (Commutativity means the dot product is commutative, which means
-- transpose preserves composition, i.e. AB^T = B^T A^T.)
module Mat {o ℓ} {A : Setoid o ℓ} (S : CommutativeSemiring A) where

  open CommutativeSemiring S public
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin using (Fin; zero; suc)

  -- Vectors S^n.
  Vec : ℕ → Set o
  Vec n = Fin n → Carrier

  -- Standard basis vector: ι at position i, ε elsewhere.
  e : ∀ {n} → Fin n → Vec n
  e zero zero = ι
  e zero (suc _) = ε
  e (suc i) zero = ε
  e (suc i) (suc j) = e i j

  -- i-th projection out of S^n (just function application, named for clarity).
  proj : ∀ {n} → Fin n → Vec n → Carrier
  proj i v = v i

  -- i-th injection into S^n: z at index i, ε elsewhere.
  inj : ∀ {n} → Fin n → Carrier → Vec n
  inj i z j = e i j · z

  -- Finite sum: Σᵢ f(i), using addition of S.
  Σ : ∀ {n} → (Fin n → Carrier) → Carrier
  Σ {zero} _ = ε
  Σ {suc n} f = f zero + Σ {n} (λ i → f (suc i))

  -- Dot product (sum of multiplications).
  _⋅_ : ∀ {n} → Vec n → Vec n → Carrier
  _⋅_ {n} u v = Σ {n} λ i → u i · v i

  Matrix : ℕ → ℕ → Set o
  Matrix m n = Fin m → Fin n → Carrier

  -- Identity matrix (Kronecker delta).
  I : ∀ {n} → Matrix n n
  I = e

  -- Matrix composition: (M ∘ N)ᵢₖ = Σⱼ Mᵢⱼ · Nⱼₖ.
  _∘_ : ∀ {m n k} → Matrix m n → Matrix n k → Matrix m k
  (M ∘ N) i k = Σ (λ j → M i j · N j k)

  infixl 21 _∘_

  _ᵀ : ∀ {m n} → Matrix m n → Matrix n m
  (M ᵀ) i j = M j i

  -- Pointwise equality of matrices.
  _≈ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Prop ℓ
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

  -- Scalar × vector, pointwise.
  scale : ∀ {n} → Carrier → Vec n → Vec n
  scale a v j = a · v j

  scale-ε : ∀ {n} (v : Vec n) → ∀ j → scale ε v j ≈ ε
  scale-ε v j = ε-annihilₗ

  scale-ι : ∀ {n} (v : Vec n) → ∀ j → scale ι v j ≈ v j
  scale-ι v j = ·-lunit

  -- Iterated vector join: pointwise Σ.
  Σ^ : ∀ {m n} → (Fin m → Vec n) → Vec n
  Σ^ g j = Σ (λ i → g i j)

  -- Basis decomposition of a vector v : ∀ j → v j ≈ Σ_i (v i · e i j).
  -- Using e-symmetry to massage Σ-unit into the shape v = Σ^ (scale (v _) (e _)).
  Σ^-basis : ∀ {m} (v : Vec m) (j : Fin m) → v j ≈ Σ^ (λ i → scale (v i) (e i)) j
  Σ^-basis v j =
    trans (sym (Σ-unit j v))
          (Σ-cong (λ i → trans (·-cong (e-sym j i) refl) ·-comm))

  -- Pointwise Σ^-congruence.
  Σ^-cong : ∀ {m n} {g g' : Fin m → Vec n} → (∀ i j → g i j ≈ g' i j) → ∀ j → Σ^ g j ≈ Σ^ g' j
  Σ^-cong h j = Σ-cong (λ i → h i j)

  -- Dot product isolates the ith coordinate: v ⋅ inj i z ≈ v i · z.
  -- A weighted form of Σ-unit with a constant factor pulled outside the sum.
  ⋅-inj : ∀ {n} (v : Vec n) (i : Fin n) (z : Carrier) → (v ⋅ inj i z) ≈ (v i · z)
  ⋅-inj {n} v i z =
    trans (Σ-cong {n} (λ j → trans (sym ·-assoc) (·-cong ·-comm refl)))
    (trans (sym (Σ-·-distribᵣ (λ j → e i j · v j) z))
           (·-cong (Σ-unit i v) refl))

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

  ∘-cong : ∀ {m n k} {M₁ M₂ : Matrix m n} {N₁ N₂ : Matrix n k} → M₁ ≈ₘ M₂ → N₁ ≈ₘ N₂ → M₁ ∘ N₁ ≈ₘ M₂ ∘ N₂
  ∘-cong {m} {n} p q i k = Σ-cong {n} (λ j → ·-cong (p i j) (q j k))

  id-left : ∀ {m n} {M : Matrix m n} → I ∘ M ≈ₘ M
  id-left {M = M} i k = Σ-unit i (λ j → M j k)

  id-right : ∀ {m n} {M : Matrix m n} → M ∘ I ≈ₘ M
  id-right {n = n} {M = M} i k =
    trans (Σ-cong {n} (λ j → ·-cong refl (e-sym j k)))
          (trans (Σ-cong {n} (λ j → ·-comm)) (Σ-unit k (M i)))

  assoc : ∀ {m n k l} (M : Matrix m n) (N : Matrix n k) (P : Matrix k l) → (M ∘ N) ∘ P ≈ₘ M ∘ (N ∘ P)
  assoc {n = n} {k} M N P i l =
    trans (Σ-cong {k} (λ j → Σ-·-distribᵣ (λ r → M i r · N r j) (P j l)))
      (trans (Σ-cong {k} (λ j → Σ-cong {n} (λ r → ·-assoc)))
        (trans (Σ-interchange {k} {n} (λ j r → M i r · (N r j · P j l)))
          (Σ-cong {n} (λ r → sym (Σ-·-distribₗ (M i r) (λ j → N r j · P j l))))))

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ m n = Matrix n m
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
  _+ₘ_ : ∀ {m n} → Matrix m n → Matrix m n → Matrix m n
  (M +ₘ N) i j = M i j + N i j

  infixl 21 _+ₘ_

  -- Zero matrix.
  εₘ : ∀ {m n} → Matrix m n
  εₘ _ _ = ε

  -- Σ over zero function is zero.
  Σ-+ₘ : ∀ {n} {f : Fin n → Carrier} → Σ {n} (λ i → f i + ε) ≈ Σ {n} f
  Σ-+ₘ {n} = Σ-cong {n} (λ i → trans +-comm +-lunit)

  -- Σ distributes over pointwise addition.
  Σ-distribₗ : ∀ {n} (f g : Fin n → Carrier) → Σ {n} (λ i → f i + g i) ≈ Σ {n} f + Σ {n} g
  Σ-distribₗ {n} f g = sym (Σ-+ {n} f g)

  comp-bilinear₁ : ∀ {m n k} (M₁ M₂ : Matrix m n) (N : Matrix n k) → (M₁ +ₘ M₂) ∘ N ≈ₘ (M₁ ∘ N) +ₘ (M₂ ∘ N)
  comp-bilinear₁ {n = n} M₁ M₂ N i k =
    trans (Σ-cong {n} (λ j → ·-+-distribᵣ))
          (sym (Σ-+ {n} (λ j → M₁ i j · N j k) (λ j → M₂ i j · N j k)))

  comp-bilinear₂ : ∀ {m n k} (M : Matrix m n) (N₁ N₂ : Matrix n k) → M ∘ (N₁ +ₘ N₂) ≈ₘ (M ∘ N₁) +ₘ (M ∘ N₂)
  comp-bilinear₂ {n = n} M N₁ N₂ i k =
    trans (Σ-cong {n} (λ j → ·-+-distribₗ))
          (sym (Σ-+ {n} (λ j → M i j · N₁ j k) (λ j → M i j · N₂ j k)))

  comp-bilinear-ε₁ : ∀ {m n k} (N : Matrix n k) → εₘ ∘ N ≈ₘ εₘ {m} {k}
  comp-bilinear-ε₁ {n = n} N i k =
    trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

  comp-bilinear-ε₂ : ∀ {m n k} (M : Matrix m n) → M ∘ εₘ ≈ₘ εₘ {m} {k}
  comp-bilinear-ε₂ {n = n} M i k =
    trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

  private
    hom-setoid : ℕ → ℕ → Setoid _ _
    hom-setoid m n .Setoid.Carrier = Matrix n m
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

  -- Biproducts.
  p₁ : ∀ {m n} → Matrix m (m +ℕ n)
  p₁ {suc m} zero zero = ι
  p₁ {suc m} zero (suc _) = ε
  p₁ {suc m} (suc i) zero = ε
  p₁ {suc m} (suc i) (suc j) = p₁ {m} i j

  p₂ : ∀ {m n} → Matrix n (m +ℕ n)
  p₂ {zero} i j = e i j
  p₂ {suc m} i zero = ε
  p₂ {suc m} i (suc j) = p₂ {m} i j

  in₁ : ∀ {m n} → Matrix (m +ℕ n) m
  in₁ {suc m} zero zero = ι
  in₁ {suc m} zero (suc _) = ε
  in₁ {suc m} (suc i) zero = ε
  in₁ {suc m} (suc i) (suc j) = in₁ {m} i j

  in₂ : ∀ {m n} → Matrix (m +ℕ n) n
  in₂ {zero}  i j = e i j
  in₂ {suc m} zero _ = ε
  in₂ {suc m} (suc i) j = in₂ {m} i j

  private
    Σ-ε· : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → ε · f j) ≈ ε
    Σ-ε· {n} f = trans (Σ-cong {n} (λ j → ε-annihilₗ)) (Σ-ε {n})

    ·ε-Σ : ∀ {n} (f : Fin n → Carrier) → Σ {n} (λ j → f j · ε) ≈ ε
    ·ε-Σ {n} f = trans (Σ-cong {n} (λ j → ε-annihilᵣ)) (Σ-ε {n})

  id-1 : ∀ m n → p₁ {m} {n} ∘ in₁ {m} {n} ≈ₘ I
  id-1 (suc m) n zero zero = trans (+-cong ·-lunit (Σ-ε· {m +ℕ n} _)) (trans +-comm +-lunit)
  id-1 (suc m) n zero (suc k) = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  id-1 (suc m) n (suc i) (suc k) = trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-1 m n i k))

  id-2 : ∀ m n → p₂ {m} {n} ∘ in₂ {m} {n} ≈ₘ I
  id-2 zero n i j = Σ-unit i (λ k → e k j)
  id-2 (suc m) n i j = trans (+-cong ε-annihilₗ refl) (trans +-lunit (id-2 m n i j))

  zero-1 : ∀ m n → p₁ {m} {n} ∘ in₂ {m} {n} ≈ₘ εₘ
  zero-1 zero n ()
  zero-1 (suc m) n zero j = trans (+-cong ε-annihilᵣ (Σ-ε· {m +ℕ n} _)) +-lunit
  zero-1 (suc m) n (suc i) j = trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-1 m n i j))

  zero-2 : ∀ m n → p₂ {m} {n} ∘ in₁ {m} {n} ≈ₘ εₘ
  zero-2 zero n _ ()
  zero-2 (suc m) n i zero = trans (+-cong ε-annihilₗ (·ε-Σ {m +ℕ n} _)) +-lunit
  zero-2 (suc m) n i (suc j) = trans (+-cong ε-annihilₗ refl) (trans +-lunit (zero-2 m n i j))

  id-+ : ∀ m n → (in₁ {m} {n} ∘ p₁ {m} {n}) +ₘ (in₂ {m} {n} ∘ p₂ {m} {n}) ≈ₘ I {m +ℕ n}
  id-+ zero n i j = trans +-lunit (Σ-unit i (λ k → e k j))
  id-+ (suc m) n zero zero =
    trans (+-cong (+-cong ·-lunit (Σ-ε· {m} _)) (Σ-ε· {n} _))
          (trans (+-cong (trans +-comm +-lunit) refl) (trans +-comm +-lunit))
  id-+ (suc m) n zero (suc j) =
    trans (+-cong (+-cong ε-annihilᵣ (Σ-ε· {m} _)) (Σ-ε· {n} _)) (trans (+-cong +-lunit refl) +-lunit)
  id-+ (suc m) n (suc i) zero =
    trans (+-cong (+-cong ε-annihilₗ (·ε-Σ {m} _)) (·ε-Σ {n} _)) (trans (+-cong +-lunit refl) +-lunit)
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
                     (∀ i → u₁ i ~ u₂ i) → (∀ j → v₁ j ~ v₂ j) →
                     ∀ i → concat u₁ v₁ i ~ concat u₂ v₂ i
  concat-preserves {zero} _ _ v-eq i = v-eq i
  concat-preserves {suc x} _ u-eq _ zero = u-eq zero
  concat-preserves {suc x} _~_ u-eq v-eq (suc i) = concat-preserves {x} _~_ (λ j → u-eq (suc j)) v-eq i

  concat-+ : ∀ {x y} (u₁ u₂ : Vec x) (v₁ v₂ : Vec y) i →
             concat (λ k → u₁ k + u₂ k) (λ k → v₁ k + v₂ k) i ≈ (concat u₁ v₁ i + concat u₂ v₂ i)
  concat-+ {zero} u₁ u₂ v₁ v₂ i = refl
  concat-+ {suc x} u₁ u₂ v₁ v₂ zero = refl
  concat-+ {suc x} u₁ u₂ v₁ v₂ (suc i) = concat-+ {x} _ _ _ _ i

  concat-ε : ∀ {x y} i → concat {x} {y} (λ _ → ε) (λ _ → ε) i ≈ ε
  concat-ε {zero} i = refl
  concat-ε {suc x} zero = refl
  concat-ε {suc x} (suc i) = concat-ε {x} i

  split₁ : ∀ {x y} → Vec (x +ℕ y) → Vec x
  split₁ {zero} w ()
  split₁ {suc x} w zero = w zero
  split₁ {suc x} w (suc i) = split₁ {x} (λ j → w (suc j)) i

  split₂ : ∀ {x y} → Vec (x +ℕ y) → Vec y
  split₂ {zero} w = w
  split₂ {suc x} w i = split₂ {x} (λ j → w (suc j)) i

  split₁-concat : ∀ {x y} (u : Vec x) (v : Vec y) i → split₁ {x} {y} (concat u v) i ≈ u i
  split₁-concat {suc x} u v zero = refl
  split₁-concat {suc x} u v (suc i) = split₁-concat {x} (λ j → u (suc j)) v i

  split₂-concat : ∀ {x y} (u : Vec x) (v : Vec y) i → split₂ {x} {y} (concat u v) i ≈ v i
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

-- Additional (ordered) structures that might be present on S.
module _ {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A) where
  open import basics using (IsPreorder; IsJoin; IsBottom; IsMeet; IsTop; module Disjoint)
  open import preorder using (Preorder)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Fin using (Fin; zero; suc)
  open import join-semilattice using (JoinSemilattice)
  open import meet-semilattice using (MeetSemilattice)

  -- Pointwise lifts to Vec n.
  module vec (P : Preorder) (n : ℕ) where
    open Preorder
    open JoinSemilattice
    open MeetSemilattice

    preorder : Preorder
    preorder .Carrier = Fin n → P .Carrier
    preorder ._≤_ u v = ∀ i → P ._≤_ (u i) (v i)
    preorder .≤-isPreorder .IsPreorder.refl i = IsPreorder.refl (P .≤-isPreorder)
    preorder .≤-isPreorder .IsPreorder.trans u≤v v≤w i = IsPreorder.trans (P .≤-isPreorder) (u≤v i) (v≤w i)

    join : JoinSemilattice P → JoinSemilattice preorder
    join J ._∨_ u v i = J ._∨_ (u i) (v i)
    join J .⊥ _ = J .⊥
    join J .∨-isJoin .IsJoin.inl i = IsJoin.inl (J .∨-isJoin)
    join J .∨-isJoin .IsJoin.inr i = IsJoin.inr (J .∨-isJoin)
    join J .∨-isJoin .IsJoin.[_,_] u≤w v≤w i = IsJoin.[_,_] (J .∨-isJoin) (u≤w i) (v≤w i)
    join J .⊥-isBottom .IsBottom.≤-bottom i = IsBottom.≤-bottom (J .⊥-isBottom)

    meet : MeetSemilattice P → MeetSemilattice preorder
    meet M ._∧_ u v i = M ._∧_ (u i) (v i)
    meet M .⊤ _ = M .⊤
    meet M .∧-isMeet .IsMeet.π₁ i = IsMeet.π₁ (M .∧-isMeet)
    meet M .∧-isMeet .IsMeet.π₂ i = IsMeet.π₂ (M .∧-isMeet)
    meet M .∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z i = IsMeet.⟨_,_⟩ (M .∧-isMeet) (x≤y i) (x≤z i)
    meet M .⊤-isTop .IsTop.≤-top i = IsTop.≤-top (M .⊤-isTop)

  open Mat S public
    renaming (
      _·_ to _∧_;
      _+_ to _∨_;
      ε to ⊥;
      ι to ⊤;
      ·-cong to ∧-cong;
      ·-assoc to ∧-assoc;
      ·-comm to ∧-comm;
      ·-lunit to ∧-lunit;
      +-cong to ∨-cong;
      +-assoc to ∨-assoc;
      +-comm to ∨-comm;
      +-lunit to ∨-lunit;
      ·-+-distribₗ to ∧-∨-distribₗ;
      ·-+-distribᵣ to ∧-∨-distribᵣ;
      ε-annihilₗ to ⊥-annihilₗ;
      ε-annihilᵣ to ⊥-annihilᵣ
    )

  module Join
    (_≤_          : Carrier → Carrier → Prop _)
    (≤-isPreorder : IsPreorder _≤_)
    (∨-isJoin     : IsJoin ≤-isPreorder _∨_)
    (⊥-isBottom   : IsBottom ≤-isPreorder ⊥)
    (≈→≤          : ∀ {x y} → x ≈ y → x ≤ y)
    where

    open IsPreorder ≤-isPreorder public using (_≃_) renaming (refl to ≤-refl; trans to ≤-trans)
    open import prop public using (proj₁; proj₂)

    preorder : Preorder
    preorder .Preorder.Carrier = Carrier
    preorder .Preorder._≤_ = _≤_
    preorder .Preorder.≤-isPreorder = ≤-isPreorder

    joins : JoinSemilattice preorder
    joins .JoinSemilattice._∨_ = _∨_
    joins .JoinSemilattice.⊥ = ⊥
    joins .JoinSemilattice.∨-isJoin = ∨-isJoin
    joins .JoinSemilattice.⊥-isBottom = ⊥-isBottom

    -- Iterated-∨ laws (Σ as iterated +). Σ-ub mirrors inl/inr, Σ-lub mirrors [_,_].
    Σ-ub : ∀ {n} (f : Fin n → Carrier) (i : Fin n) → f i ≤ Σ f
    Σ-ub f zero = IsJoin.inl ∨-isJoin
    Σ-ub f (suc i) = ≤-trans (Σ-ub (λ j → f (suc j)) i) (IsJoin.inr ∨-isJoin)

    Σ-lub : ∀ {n} {z} (f : Fin n → Carrier) → (∀ j → f j ≤ z) → Σ f ≤ z
    Σ-lub {zero} _ _ = IsBottom.≤-bottom ⊥-isBottom
    Σ-lub {suc n} f h = IsJoin.[_,_] ∨-isJoin (h zero) (Σ-lub (λ j → f (suc j)) (λ j → h (suc j)))

    Σ-mono : ∀ {n} {f g : Fin n → Carrier} → (∀ j → f j ≤ g j) → Σ f ≤ Σ g
    Σ-mono = +-to-Σ.Σ-preserves _≤_ ≤-refl (IsJoin.mono ∨-isJoin)

    -- Pointwise lift of _≤_ and _≃_ to Vec, from vec.preorder.
    module _ {n : ℕ} where
      open Preorder (vec.preorder preorder n) using () renaming (_≤_ to _≤^_; _≃_ to _≃^_) public

    -- Iterated-∨ at Vec level.
    Σ^-ub : ∀ {m n} (g : Fin m → Vec n) (i : Fin m) → g i ≤^ Σ^ g
    Σ^-ub g i j = Σ-ub (λ k → g k j) i

    Σ^-lub : ∀ {m n} {z : Vec n} (g : Fin m → Vec n) → (∀ i → g i ≤^ z) → Σ^ g ≤^ z
    Σ^-lub g h j = Σ-lub (λ k → g k j) (λ i → h i j)

    Σ^-mono : ∀ {m n} {g g' : Fin m → Vec n} → (∀ i → g i ≤^ g' i) → Σ^ g ≤^ Σ^ g'
    Σ^-mono h j = Σ-mono (λ i → h i j)

    -- Basis decomposition of a join-preserving, scale-linear map. Scale-linearity is an explicit hypothesis
    -- because f's interaction with scalar · isn't otherwise constrained (like it is in Two). Currently unused,
    -- but nice because it shows that because every such f is determined by its action on basis vectors, we
    -- can think of it as a "join of atomic slices".
    module _ {m n}
      (f       : Vec m → Vec n)
      (f-mono  : ∀ {u v} → u ≤^ v → f u ≤^ f v)
      (f-⊥     : ∀ j → f (λ _ → ⊥) j ≤ ⊥)
      (f-∨     : ∀ u v j → f (λ k → u k ∨ v k) j ≤ (f u j ∨ f v j))
      (f-scale : ∀ a v j → f (scale a v) j ≃ scale a (f v) j)
      where

      -- f preserves and reflects Σ^.
      f-Σ^ : ∀ {k} (g : Fin k → Vec m) → f (Σ^ g) ≃^ Σ^ (λ i → f (g i))
      f-Σ^ {zero} g .proj₁ j = f-⊥ j
      f-Σ^ {suc k} g .proj₁ j =
        ≤-trans (f-∨ (g zero) (Σ^ (λ i → g (suc i))) j)
                (IsJoin.mono ∨-isJoin ≤-refl (f-Σ^ (λ i → g (suc i)) .proj₁ j))
      f-Σ^ g .proj₂ = Σ^-lub _ (λ i → f-mono (Σ^-ub g i))

      basis-decomp : ∀ (v : Vec m) j → f v j ≃ Σ^ (λ i → scale (v i) (f (e i))) j
      basis-decomp v j .proj₁ =
        ≤-trans (f-mono (λ k → ≈→≤ (Σ^-basis v k)) j)
          (≤-trans (f-Σ^ (λ i → scale (v i) (e i)) .proj₁ j)
                   (Σ-mono (λ i → f-scale (v i) (e i) j .proj₁)))
      basis-decomp v j .proj₂ =
        ≤-trans (Σ-mono (λ i → f-scale (v i) (e i) j .proj₂))
          (≤-trans (f-Σ^ (λ i → scale (v i) (e i)) .proj₂ j)
                   (f-mono (λ k → ≈→≤ (sym (Σ^-basis v k))) j))

  module DistributiveLattice
    (_≤_          : Carrier → Carrier → Prop _)
    (≤-isPreorder : IsPreorder _≤_)
    (∧-isMeet     : IsMeet ≤-isPreorder _∧_)
    (⊤-isTop      : IsTop  ≤-isPreorder ⊤)
    (∨-isJoin     : IsJoin ≤-isPreorder _∨_)
    (⊥-isBottom   : IsBottom ≤-isPreorder ⊥)
    (∧-∨-distrib  : ∀ {x y z} → (x ∧ (y ∨ z)) ≤ ((x ∧ y) ∨ (x ∧ z)))
    (≈→≤          : ∀ {x y} → x ≈ y → x ≤ y) -- S setoid equivalence compatible with the preorder
    where

    open Join _≤_ ≤-isPreorder ∨-isJoin ⊥-isBottom ≈→≤ public

    meets : MeetSemilattice preorder
    meets .MeetSemilattice._∧_ = _∧_
    meets .MeetSemilattice.⊤ = ⊤
    meets .MeetSemilattice.∧-isMeet = ∧-isMeet
    meets .MeetSemilattice.⊤-isTop = ⊤-isTop

    open Disjoint ≤-isPreorder ∧-isMeet ⊥-isBottom public

    -- Dot-product form of disjointness, for vectors.
    infix 4 _#^_
    _#^_ : ∀ {n} → Vec n → Vec n → Prop _
    u #^ v = (u ⋅ v) ≤ ⊥

    open import prop using (_⇔_)

    module BooleanAlgebra
      (¬ : Carrier → Carrier)
      (complement-∨ : ∀ {x} → ⊤ ≤ x ∨ ¬ x)
      (complement-∧ : ∀ {x} → x ∧ ¬ x ≤ ⊥)
      where

      open IsMeet ∧-isMeet using (π₁; π₂; ⟨_,_⟩) renaming (mono to ∧-mono)
      open IsJoin ∨-isJoin using (inl; inr; [_,_]) renaming (mono to ∨-mono)
      open IsTop ⊤-isTop
      open IsBottom ⊥-isBottom

      #-↔-≤¬ : ∀ {x y} → (x # y) ⇔ (x ≤ ¬ y)
      #-↔-≤¬ {x} {y} .proj₁ x#y =
        ≤-trans ⟨ ≤-refl , ≤-top ⟩
                (≤-trans (∧-mono ≤-refl complement-∨)
                         (≤-trans ∧-∨-distrib [ ≤-trans x#y ≤-bottom , π₂ ]))
      #-↔-≤¬ .proj₂ x≤¬y =
        ≤-trans (∧-mono x≤¬y ≤-refl) (≤-trans (IsMeet.comm ∧-isMeet) complement-∧)

      ¬-antitone : ∀ {x y} → x ≤ y → ¬ y ≤ ¬ x
      ¬-antitone x≤y =
        #-↔-≤¬ .proj₁ (#-sym (#-mono x≤y _ (#-sym (#-↔-≤¬ {¬ _} .proj₂ ≤-refl))))

      ¬-involutive : ∀ {x} → x ≃ ¬ (¬ x)
      ¬-involutive {x} .proj₁ = #-↔-≤¬ .proj₁ (#-sym (#-↔-≤¬ {¬ x} {x} .proj₂ ≤-refl))
      ¬-involutive {x} .proj₂ =
        ≤-trans ⟨ ≤-refl , ≤-top ⟩
                (≤-trans (∧-mono ≤-refl complement-∨)
                         (≤-trans ∧-∨-distrib
                                  [ π₂ , ≤-trans (≤-trans (IsMeet.comm ∧-isMeet) complement-∧) ≤-bottom ]))

      #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → x ≤ y
      #-reflect {x} {y} h =
        ≤-trans (#-↔-≤¬ .proj₁ (h (¬ y) (#-sym (#-↔-≤¬ {¬ y} {y} .proj₂ ≤-refl)))) (¬-involutive .proj₂)

      ¬^ : ∀ {n} → Vec n → Vec n
      ¬^ u i = ¬ (u i)

      ¬^-antitone : ∀ {n} {u v : Vec n} → u ≤^ v → ¬^ v ≤^ ¬^ u
      ¬^-antitone u≤v i = ¬-antitone (u≤v i)

      #^-reflect : ∀ {n} {u v : Vec n} → (∀ w → v #^ w → u #^ w) → u ≤^ v
      #^-reflect {n} {u} {v} h i =
        #-reflect λ z vi#z →
          ≤-trans (≈→≤ (sym (⋅-inj u i z)))
            (h (inj i z) (≤-trans (≈→≤ (⋅-inj v i z)) vi#z))

      open import conjugate using (Obj; _⇒c_; BooleanAlgebra; boolean-⇒c)
      open _⇒c_ using (conjugate)
      open preorder._=>_ using (fun; mono)

      BoolAlg : ℕ → Obj
      BoolAlg n .Obj.carrier = vec.preorder preorder n
      BoolAlg n .Obj.meets = vec.meet preorder n meets
      BoolAlg n .Obj.joins = vec.join preorder n joins
      BoolAlg n .Obj.∧-∨-distrib _ _ _ _ = ∧-∨-distrib

      BoolAlg-boolean : ∀ n → BooleanAlgebra (BoolAlg n)
      BoolAlg-boolean n .BooleanAlgebra.¬ = ¬^
      BoolAlg-boolean n .BooleanAlgebra.complement-∨ _ = complement-∨
      BoolAlg-boolean n .BooleanAlgebra.complement-∧ _ = complement-∧

      -- Push y inside, interchange, pull x out.
      swap : ∀ {m n} (M : Matrix n m) {x : Vec m} {y : Vec n} →
             (y ⋅ (λ i → M i ⋅ x)) ≈ ((λ j → (M ᵀ) j ⋅ y) ⋅ x)
      swap {m} {n} M {x} {y} =
        trans (Σ-cong {n} (λ i → Σ-·-distribₗ (y i) (λ j → M i j ∧ x j)))
              (trans (Σ-interchange {n} {m} (λ i j → y i ∧ (M i j ∧ x j)))
                     (Σ-cong {m} (λ j →
                       trans (Σ-cong {n} (λ i → trans (sym ∧-assoc) (∧-cong ∧-comm refl)))
                             (sym (Σ-·-distribᵣ (λ i → M i j ∧ y i) (x j))))))

      -- Target arrow has direction of Mᵀ for consistency with to-gal.
      to-conj : ∀ {m n} → Matrix n m → BoolAlg n ⇒c BoolAlg m
      to-conj {m} {n} M =
        boolean-⇒c (BoolAlg-boolean n) (BoolAlg-boolean m) right left conj
        where
          right : preorder._=>_ (vec.preorder preorder n) (vec.preorder preorder m)
          right .fun x j = (M ᵀ) j ⋅ x
          right .mono x≤x' j = Σ-mono (λ i → ∧-mono ≤-refl (x≤x' i))
          left : preorder._=>_ (vec.preorder preorder m) (vec.preorder preorder n)
          left .fun y i = M i ⋅ y
          left .mono y≤y' i = Σ-mono (λ j → ∧-mono ≤-refl (y≤y' j))
          conj : ∀ {x y} → Obj._#_ (BoolAlg m) y (right .fun x) ⇔ Obj._#_ (BoolAlg n) (left .fun y) x
          conj {x} {y} .proj₁ h i =
            ≤-trans (Σ-ub _ i) (≤-trans (≈→≤ (sym (swap (M ᵀ) {x} {y}))) (Σ-lub _ h))
          conj {x} {y} .proj₂ k j =
            ≤-trans (Σ-ub _ j) (≤-trans (≈→≤ (swap (M ᵀ) {x} {y})) (Σ-lub _ k))

      -- De Morgan dual of the transpose. Meet-preserving; right adjoint of M · _.
      adjoint : ∀ {m n} → Matrix n m → Vec n → Vec m
      adjoint M x j = ¬ ((M ᵀ) j ⋅ ¬^ x)

      open import galois using () renaming (Obj to Obj-g; _⇒g_ to _=>g_)
      open _=>g_

      BoundedLattice : ℕ → Obj-g
      BoundedLattice n .Obj-g.carrier = vec.preorder preorder n
      BoundedLattice n .Obj-g.meets = vec.meet preorder n meets
      BoundedLattice n .Obj-g.joins = vec.join preorder n joins

      to-gal : ∀ {m n} → Matrix n m → BoundedLattice n =>g BoundedLattice m
      to-gal M .right .fun = adjoint M
      to-gal M .right .mono x≤x' j = ¬-antitone (Σ-mono (λ i → ∧-mono ≤-refl (¬-antitone (x≤x' i))))
      to-gal M .left .fun y i = M i ⋅ y
      to-gal M .left .mono y≤y' i = Σ-mono (λ j → ∧-mono ≤-refl (y≤y' j))
      to-gal M .left⊣right {x} {y} .proj₁ h i =
        ≤-trans (#-↔-≤¬ .proj₁ (to-conj M .conjugate {¬^ x} {y} .proj₁ (λ j → #-↔-≤¬ .proj₂ (h j)) i))
                (¬-involutive .proj₂)
      to-gal M .left⊣right {x} {y} .proj₂ k j =
        #-↔-≤¬ .proj₁
          (to-conj M .conjugate {¬^ x} {y} .proj₂ (λ i → #-mono (k i) _ (#-sym (#-↔-≤¬ .proj₂ ≤-refl))) j)

      -- FIXME: functor properties of the two embeddings.

  -- A commutative semiring is exactly a (bounded) distributive lattice when both ∨ (= +) and ∧ (= ·) are
  -- idempotent and ⊤ (= 1) is the additive top. The induced order is x ≤ y iff x ∨ y ≈ y; ∨ becomes the
  -- join, ∧ the meet, ⊥ (= 0) the bottom, ⊤ the top. Will eventually replace DistributiveLattice.
  module DistributiveLattice2
    (∨-idem    : ∀ {x} → x ∨ x ≈ x)
    (∧-idem    : ∀ {x} → x ∧ x ≈ x)
    (⊤-add-top : ∀ {x} → ⊤ ∨ x ≈ ⊤)
    where

    open import prop using (proj₁; proj₂)

    _≤_ : Carrier → Carrier → Prop _
    x ≤ y = x ∨ y ≈ y

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder .IsPreorder.refl = ∨-idem
    ≤-isPreorder .IsPreorder.trans {x} {y} {z} x≤y y≤z =
      trans (∨-cong refl (sym y≤z)) (trans (sym ∨-assoc) (trans (∨-cong x≤y refl) y≤z))

    ≈→≤ : ∀ {x y} → x ≈ y → x ≤ y
    ≈→≤ x≈y = trans (∨-cong x≈y refl) ∨-idem

    ∨-isJoin : IsJoin ≤-isPreorder _∨_
    ∨-isJoin .IsJoin.inl = trans (sym ∨-assoc) (∨-cong ∨-idem refl)
    ∨-isJoin .IsJoin.inr =
      trans (∨-cong refl ∨-comm) (trans (sym ∨-assoc) (trans (∨-cong ∨-idem refl) ∨-comm))
    ∨-isJoin .IsJoin.[_,_] x≤z y≤z = trans ∨-assoc (trans (∨-cong refl y≤z) x≤z)

    ⊥-isBottom : IsBottom ≤-isPreorder ⊥
    ⊥-isBottom .IsBottom.≤-bottom = ∨-lunit

    ⊤-isTop : IsTop ≤-isPreorder ⊤
    ⊤-isTop .IsTop.≤-top = trans ∨-comm ⊤-add-top

    ∨-∧-absorption : ∀ {a b} → a ∨ (a ∧ b) ≈ a
    ∨-∧-absorption {a} {b} =
      trans (∨-cong (trans (sym ∧-lunit) ∧-comm) refl)
            (trans (sym ∧-∨-distribₗ) (trans (∧-cong refl ⊤-add-top) (trans ∧-comm ∧-lunit)))

    ∧-monoʳ : ∀ {a b c} → a ≤ b → c ∧ a ≤ c ∧ b
    ∧-monoʳ a≤b = trans (sym ∧-∨-distribₗ) (∧-cong refl a≤b)

    ∧-monoˡ : ∀ {a b c} → a ≤ b → a ∧ c ≤ b ∧ c
    ∧-monoˡ a≤b = trans (sym ∧-∨-distribᵣ) (∧-cong a≤b refl)

    ∧-isMeet : IsMeet ≤-isPreorder _∧_
    ∧-isMeet .IsMeet.π₁ = trans ∨-comm ∨-∧-absorption
    ∧-isMeet .IsMeet.π₂ = trans (∨-cong ∧-comm refl) (trans ∨-comm ∨-∧-absorption)
    ∧-isMeet .IsMeet.⟨_,_⟩ {x} {y} {z} x≤y x≤z =
      ≤-isPreorder .IsPreorder.trans
        (trans (∨-cong (sym ∧-idem) refl) (∧-monoʳ x≤z)) (∧-monoˡ x≤y)

    ∧-∨-distrib : ∀ {x y z} → x ∧ (y ∨ z) ≤ (x ∧ y) ∨ (x ∧ z)
    ∧-∨-distrib = ≈→≤ ∧-∨-distribₗ

    ∨-∧-distribₗ : ∀ {a b c} → (a ∨ b) ∧ (a ∨ c) ≈ a ∨ (b ∧ c)
    ∨-∧-distribₗ {a} {b} {c} =
      trans ∧-∨-distribᵣ
            (trans (∨-cong ∧-∨-distribₗ ∧-∨-distribₗ)
                  (trans (∨-cong (∨-cong ∧-idem refl) (∨-cong ∧-comm refl))
                          (trans (∨-cong ∨-∧-absorption refl)
                                (trans (sym ∨-assoc) (∨-cong ∨-∧-absorption refl)))))

    preorder : Preorder
    preorder .Preorder.Carrier = Carrier
    preorder .Preorder._≤_ = _≤_
    preorder .Preorder.≤-isPreorder = ≤-isPreorder

    meets : MeetSemilattice preorder
    meets .MeetSemilattice._∧_ = _∧_
    meets .MeetSemilattice.⊤ = ⊤
    meets .MeetSemilattice.∧-isMeet = ∧-isMeet
    meets .MeetSemilattice.⊤-isTop = ⊤-isTop

    joins : JoinSemilattice preorder
    joins .JoinSemilattice._∨_ = _∨_
    joins .JoinSemilattice.⊥ = ⊥
    joins .JoinSemilattice.∨-isJoin = ∨-isJoin
    joins .JoinSemilattice.⊥-isBottom = ⊥-isBottom

    open import conjugate using (Obj; _⇒c_)
    open _⇒c_

    DistribLattice : ℕ → Obj
    DistribLattice n .Obj.carrier = vec.preorder preorder n
    DistribLattice n .Obj.meets = vec.meet preorder n meets
    DistribLattice n .Obj.joins = vec.join preorder n joins
    DistribLattice n .Obj.∧-∨-distrib _ _ _ _ = ∧-∨-distrib

    open Join _≤_ ≤-isPreorder ∨-isJoin ⊥-isBottom ≈→≤ using (Σ-mono; Σ-ub; Σ-lub)
    open IsPreorder ≤-isPreorder using () renaming (refl to ≤-refl; trans to ≤-trans)
    open IsMeet ∧-isMeet using () renaming (mono to ∧-mono)

    open import join-semilattice using () renaming (_=>_ to _=>J_)
    open _=>J_
    open preorder._=>_ using (fun; mono)

    -- Push y inside, interchange, pull x out.
    swap : ∀ {m n} (M : Matrix n m) {x : Vec m} {y : Vec n} →
           (y ⋅ (λ i → M i ⋅ x)) ≈ ((λ j → (M ᵀ) j ⋅ y) ⋅ x)
    swap {m} {n} M {x} {y} =
      trans (Σ-cong {n} (λ i → Σ-·-distribₗ (y i) (λ j → M i j ∧ x j)))
            (trans (Σ-interchange {n} {m} (λ i j → y i ∧ (M i j ∧ x j)))
                   (Σ-cong {m} (λ j →
                     trans (Σ-cong {n} (λ i → trans (sym ∧-assoc) (∧-cong ∧-comm refl)))
                           (sym (Σ-·-distribᵣ (λ i → M i j ∧ y i) (x j))))))

    to-conj : ∀ {m n} → Matrix n m → DistribLattice n ⇒c DistribLattice m
    to-conj {m} {n} M .right .func .fun x j = (M ᵀ) j ⋅ x
    to-conj {m} {n} M .right .func .mono x≤x' j = Σ-mono (λ i → ∧-mono ≤-refl (x≤x' i))
    to-conj {m} {n} M .right .∨-preserving {x} {x'} j =
      ≈→≤ (trans (Σ-cong {n} (λ i → ∧-∨-distribₗ)) (sym (Σ-+ {n} _ _)))
    to-conj {m} {n} M .right .⊥-preserving j =
      ≈→≤ (trans (Σ-cong {n} (λ i → ⊥-annihilᵣ)) (Σ-ε {n}))
    to-conj {m} {n} M .left .func .fun y i = M i ⋅ y
    to-conj {m} {n} M .left .func .mono y≤y' i = Σ-mono (λ j → ∧-mono ≤-refl (y≤y' j))
    to-conj {m} {n} M .left .∨-preserving {y} {y'} i =
      ≈→≤ (trans (Σ-cong {m} (λ j → ∧-∨-distribₗ)) (sym (Σ-+ {m} _ _)))
    to-conj {m} {n} M .left .⊥-preserving i =
      ≈→≤ (trans (Σ-cong {m} (λ j → ⊥-annihilᵣ)) (Σ-ε {m}))
    to-conj {m} {n} M .conjugate {x} {y} .proj₁ h i =
      ≤-trans (Σ-ub _ i) (≤-trans (≈→≤ (sym (swap (M ᵀ) {x} {y}))) (Σ-lub _ h))
    to-conj {m} {n} M .conjugate {x} {y} .proj₂ k j =
      ≤-trans (Σ-ub _ j) (≤-trans (≈→≤ (swap (M ᵀ) {x} {y})) (Σ-lub _ k))

    -- The opposite semiring, with + and · swapped.
    opposite : CommutativeSemiring A
    opposite .CommutativeSemiring.additive = multiplicative
    opposite .CommutativeSemiring.multiplicative = additive
    opposite .CommutativeSemiring.·-+-distribₗ = sym ∨-∧-distribₗ
    opposite .CommutativeSemiring.ε-annihilₗ = ⊤-add-top

module _
  {A : Setoid 0ℓ 0ℓ} (S : CommutativeSemiring A)
  (let open CommutativeSemiring S hiding (_≈_); _≈_ = Setoid._≈_ A)
  (∨-idem    : ∀ {x} → x + x ≈ x)
  (∧-idem    : ∀ {x} → x · x ≈ x)
  (⊤-add-top : ∀ {x} → ι + x ≈ ι)
  where
  module L = DistributiveLattice2 S ∨-idem ∧-idem ⊤-add-top
  module L-op = DistributiveLattice2 L.opposite ∧-idem ∨-idem ε-annihilₗ
