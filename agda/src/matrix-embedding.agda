{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)
open import functor using (Functor)

-- CMon-enriched equivalence Mat(S) ≃ matrix-rep.cat (𝒞, X), given an iso between the semiring S and
-- End(X). The representation of S inside End(X) is faithful on both sides: scalar is a homomorphism
-- with an inverse scalar-inv that is also a homomorphism (automatically, given scalar is bijective).
module matrix-embedding
  {o m e o' ℓ} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  {A : Setoid o' ℓ} (S : CommutativeSemiring A)
  (let open Category 𝒞)
  (let open CMonEnriched CM)
  (let open CommutativeSemiring S using (Carrier) renaming (ε to S-ε; ι to S-ι; _+_ to _+ₛ_; _·_ to _·ₛ_; _≈_ to _≈ₛ_; ·-comm to ·ₛ-comm; trans to ≈ₛ-trans))
  (scalar : Carrier → X ⇒ X)
  (scalar-cong : ∀ {a b} → a ≈ₛ b → scalar a ≈ scalar b)
  (scalar-ε : scalar S-ε ≈ εm)
  (scalar-ι : scalar S-ι ≈ id X)
  (scalar-+ : ∀ {a b} → scalar (a +ₛ b) ≈ scalar a +m scalar b)
  (scalar-· : ∀ {a b} → scalar (a ·ₛ b) ≈ scalar a ∘ scalar b)
  (scalar-inv : X ⇒ X → Carrier)
  (scalar-inv-cong : ∀ {f g : X ⇒ X} → f ≈ g → scalar-inv f ≈ₛ scalar-inv g)
  (scalar-inv-scalar : ∀ a → scalar-inv (scalar a) ≈ₛ a)
  (scalar-scalar-inv : ∀ (f : X ⇒ X) → scalar (scalar-inv f) ≈ f)
  where

  open CommutativeMonoid
  open Biproduct

  -- Composition in End(X) is commutative, derived from S commutativity via the iso.
  scalar-comm : ∀ (f g : X ⇒ X) → (f ∘ g) ≈ (g ∘ f)
  scalar-comm f g =
    begin
      f ∘ g
    ≈˘⟨ ∘-cong (scalar-scalar-inv f) (scalar-scalar-inv g) ⟩
      scalar (scalar-inv f) ∘ scalar (scalar-inv g)
    ≈˘⟨ scalar-· ⟩
      scalar (scalar-inv f ·ₛ scalar-inv g)
    ≈⟨ scalar-cong ·ₛ-comm ⟩
      scalar (scalar-inv g ·ₛ scalar-inv f)
    ≈⟨ scalar-· ⟩
      scalar (scalar-inv g) ∘ scalar (scalar-inv f)
    ≈⟨ ∘-cong (scalar-scalar-inv g) (scalar-scalar-inv f) ⟩
      g ∘ f
    ∎ where open ≈-Reasoning isEquiv

  import matrix-rep
  open matrix-rep CM BP 𝟘 𝟘-initial 𝟘-terminal X scalar-comm public

  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  import matrix
  private
    module Mat = matrix S
    open matrix S using (Mat) public

  open Functor

  -- scalar preserves dot products.
  scalar-Σ : ∀ {n} (f g : Fin n → Carrier) →
    scalar (Mat.Σ (λ k → f k ·ₛ g k)) ≈ (cotuple {n} (λ k → scalar (f k)) ∘ tuple {n} (λ k → scalar (g k)))
  scalar-Σ {zero} f g =
    begin
      scalar S-ε
    ≈⟨ scalar-ε ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₁ to-terminal ⟩
      εm ∘ to-terminal
    ≈˘⟨ ∘-cong (from-initial-ext εm) ≈-refl ⟩
      from-initial ∘ to-terminal
    ∎ where open ≈-Reasoning isEquiv
  scalar-Σ {suc n} f g =
    begin
      scalar ((f zero ·ₛ g zero) +ₛ Mat.Σ (λ k → f (suc k) ·ₛ g (suc k)))
    ≈⟨ scalar-+ ⟩
      scalar (f zero ·ₛ g zero) +m scalar (Mat.Σ (λ k → f (suc k) ·ₛ g (suc k)))
    ≈⟨ homCM _ _ .+-cong scalar-· (scalar-Σ (λ k → f (suc k)) (λ k → g (suc k))) ⟩
      (scalar (f zero) ∘ scalar (g zero))
      +m
      (cotuple {n} (λ k → scalar (f (suc k))) ∘ tuple {n} (λ k → scalar (g (suc k))))
    ≈˘⟨ homCM _ _ .+-cong
          (∘-cong ≈-refl (pair-p₁ (BP X (X^ n)) _ _))
          (∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) _ _)) ⟩
      (scalar (f zero) ∘ (p₁ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar (g zero)) (tuple (λ k → scalar (g (suc k))))))
      +m
      (cotuple {n} (λ k → scalar (f (suc k))) ∘ (p₂ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar (g zero)) (tuple (λ k → scalar (g (suc k))))))
    ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((scalar (f zero) ∘ p₁ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (scalar (g zero)) (tuple (λ k → scalar (g (suc k)))))
      +m
      ((cotuple {n} (λ k → scalar (f (suc k))) ∘ p₂ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (scalar (g zero)) (tuple (λ k → scalar (g (suc k)))))
    ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
      copair (BP X (X^ n)) (scalar (f zero)) (cotuple {n} (λ k → scalar (f (suc k))))
      ∘ pair (BP X (X^ n)) (scalar (g zero)) (tuple {n} (λ k → scalar (g (suc k))))
    ∎ where open ≈-Reasoning isEquiv

  -- scalar applied to the Kronecker delta e matches projection-injection.
  scalar-e : ∀ {n} (i j : Fin n) → scalar (Mat.e i j) ≈ (π {n} i ∘ ι {n} j)
  scalar-e {suc n} zero zero =
    begin
      scalar S-ι ≈⟨ scalar-ι ⟩ id X
    ≈˘⟨ id-1 (BP X (X^ n)) ⟩
      p₁ (BP X (X^ n)) ∘ in₁ (BP X (X^ n))
    ∎ where open ≈-Reasoning isEquiv
  scalar-e {suc n} zero (suc j) =
    begin
      scalar S-ε
    ≈⟨ scalar-ε ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₁ _ ⟩
      εm ∘ ι j
    ≈˘⟨ ∘-cong (zero-1 (BP X (X^ n))) ≈-refl ⟩
      (p₁ (BP X (X^ n)) ∘ in₂ (BP X (X^ n))) ∘ ι j
    ≈⟨ assoc _ _ _ ⟩
      p₁ (BP X (X^ n)) ∘ (in₂ (BP X (X^ n)) ∘ ι j)
    ∎ where open ≈-Reasoning isEquiv
  scalar-e {suc n} (suc i) zero =
    begin
      scalar S-ε
    ≈⟨ scalar-ε ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₂ _ ⟩
      π i ∘ εm
    ≈˘⟨ ∘-cong ≈-refl (zero-2 (BP X (X^ n))) ⟩
      π i ∘ (p₂ (BP X (X^ n)) ∘ in₁ (BP X (X^ n)))
    ≈˘⟨ assoc _ _ _ ⟩
      (π i ∘ p₂ (BP X (X^ n))) ∘ in₁ (BP X (X^ n))
    ∎ where open ≈-Reasoning isEquiv
  scalar-e {suc n} (suc i) (suc j) =
    begin
      scalar (Mat.e i j)
    ≈⟨ scalar-e i j ⟩
      π i ∘ ι j
    ≈˘⟨ ∘-cong ≈-refl id-left ⟩
      π i ∘ (id _ ∘ ι j)
    ≈˘⟨ ∘-cong ≈-refl (∘-cong (id-2 (BP X (X^ n))) ≈-refl) ⟩
      π i ∘ ((p₂ (BP X (X^ n)) ∘ in₂ (BP X (X^ n))) ∘ ι j)
    ≈⟨ ∘-cong ≈-refl (assoc _ _ _) ⟩
      π i ∘ (p₂ (BP X (X^ n)) ∘ (in₂ (BP X (X^ n)) ∘ ι j))
    ≈˘⟨ assoc _ _ _ ⟩
      (π i ∘ p₂ (BP X (X^ n))) ∘ (in₂ (BP X (X^ n)) ∘ ι j)
    ∎ where open ≈-Reasoning isEquiv

  -- F : Mat(S) → matrix-rep.cat, the "assemble matrix from entries" direction.
  F : Functor Mat.cat cat
  F .fobj n = n
  F .fmor {m} {n} M = tuple {n} (λ i → cotuple {m} (λ j → scalar (M i j)))
  F .fmor-cong p = tuple-cong _ _ (λ i → cotuple-cong _ _ (λ j → scalar-cong (p i j)))
  F .fmor-id {n} = entry-ext (λ i j →
    begin
      π {n} i ∘ (tuple {n} (λ i' → cotuple {n} (λ j' → scalar (Mat.I i' j'))) ∘ ι {n} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {n} i ∘ tuple {n} (λ i' → cotuple {n} (λ j' → scalar (Mat.I i' j')))) ∘ ι {n} j
    ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
      cotuple {n} (λ j' → scalar (Mat.I i j')) ∘ ι {n} j
    ≈⟨ cotuple-ι {n} _ j ⟩
      scalar (Mat.I i j)
    ≈⟨ scalar-e i j ⟩
      π {n} i ∘ ι {n} j
    ≈˘⟨ ∘-cong ≈-refl id-left ⟩
      π {n} i ∘ (id (X^ n) ∘ ι {n} j)
    ∎) where open ≈-Reasoning isEquiv
  F .fmor-comp {x} {y} {z} M N = entry-ext (λ i j →
    begin
      entry (F .fmor (M Mat.∘ N)) i j
    ≈⟨ entry-F (M Mat.∘ N) i j ⟩
      scalar (Mat.Σ (λ k → M i k ·ₛ N k j))
    ≈⟨ scalar-Σ (λ k → M i k) (λ k → N k j) ⟩
      cotuple {y} (λ k → scalar (M i k)) ∘ tuple {y} (λ k → scalar (N k j))
    ≈˘⟨ ∘-cong (cotuple-cong {y} _ _ (λ k → entry-F M i k))
               (tuple-cong {y} _ _ (λ k → entry-F N k j)) ⟩
      cotuple {y} (λ k → entry (F .fmor M) i k) ∘ tuple {y} (λ k → entry (F .fmor N) k j)
    ≈˘⟨ entry-comp {x} {y} {z} (F .fmor N) (F .fmor M) i j ⟩
      π {z} i ∘ ((F .fmor M ∘ F .fmor N) ∘ ι {x} j)
    ∎) where
      open ≈-Reasoning isEquiv
      entry-F : ∀ {m n} (M : Mat n m) (i : Fin n) (j : Fin m) → entry (F .fmor M) i j ≈ scalar (M i j)
      entry-F {m} {n} M i j =
        begin
          π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j'))) ∘ ι {m} j)
        ≈˘⟨ assoc _ _ _ ⟩
          (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j')))) ∘ ι {m} j
        ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
          cotuple {m} (λ j' → scalar (M i j')) ∘ ι {m} j
        ≈⟨ cotuple-ι {m} _ j ⟩
          scalar (M i j)
        ∎

  -- Entry-wise characterization of F, re-stated at module level for use below.
  entry-F : ∀ {m n} (M : Mat n m) (i : Fin n) (j : Fin m) → entry (F .fmor M) i j ≈ scalar (M i j)
  entry-F {m} {n} M i j =
    begin
      π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j'))) ∘ ι {m} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j')))) ∘ ι {m} j
    ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
      cotuple {m} (λ j' → scalar (M i j')) ∘ ι {m} j
    ≈⟨ cotuple-ι {m} _ j ⟩
      scalar (M i j)
    ∎ where open ≈-Reasoning isEquiv

  -- F⁻¹ : matrix-rep.cat → Mat(S), the "extract matrix of entries" direction.
  F⁻¹ : Functor cat Mat.cat
  F⁻¹ .fobj n = n
  F⁻¹ .fmor {m} {n} f i j = scalar-inv (entry {m} {n} f i j)
  F⁻¹ .fmor-cong p i j = scalar-inv-cong (∘-cong ≈-refl (∘-cong p ≈-refl))
  F⁻¹ .fmor-id {n} i j =
    begin
      scalar-inv (entry {n} {n} (id (X^ n)) i j)
    ≈⟨ scalar-inv-cong (∘-cong ≈-refl id-left) ⟩
      scalar-inv (π {n} i ∘ ι {n} j)
    ≈˘⟨ scalar-inv-cong (scalar-e i j) ⟩
      scalar-inv (scalar (Mat.e i j))
    ≈⟨ scalar-inv-scalar (Mat.e i j) ⟩
      Mat.e i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)
  F⁻¹ .fmor-comp {x} {y} {z} g f i j =
    begin
      scalar-inv (entry {x} {z} (g ∘ f) i j)
    ≈⟨ scalar-inv-cong (entry-comp {x} {y} {z} f g i j) ⟩
      scalar-inv (cotuple {y} (λ k → entry {y} {z} g i k) ∘ tuple {y} (λ k → entry {x} {y} f k j))
    ≈˘⟨ scalar-inv-cong (∘-cong (cotuple-cong {y} _ _ (λ k → scalar-scalar-inv _))
                                 (tuple-cong {y} _ _ (λ k → scalar-scalar-inv _))) ⟩
      scalar-inv (cotuple {y} (λ k → scalar (scalar-inv (entry {y} {z} g i k)))
                  ∘ tuple {y} (λ k → scalar (scalar-inv (entry {x} {y} f k j))))
    ≈˘⟨ scalar-inv-cong (scalar-Σ {y} (λ k → scalar-inv (entry {y} {z} g i k)) (λ k → scalar-inv (entry {x} {y} f k j))) ⟩
      scalar-inv (scalar (Mat.Σ {y} (λ k → scalar-inv (entry {y} {z} g i k) ·ₛ scalar-inv (entry {x} {y} f k j))))
    ≈⟨ scalar-inv-scalar _ ⟩
      Mat.Σ {y} (λ k → scalar-inv (entry {y} {z} g i k) ·ₛ scalar-inv (entry {x} {y} f k j))
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  -- Round trip: F⁻¹ is a left inverse of F up to pointwise semiring equality.
  F⁻¹∘F : ∀ {m n} (M : Mat n m) → (F⁻¹ .fmor (F .fmor M)) Mat.≈ₘ M
  F⁻¹∘F {m} {n} M i j =
    begin
      scalar-inv (entry {m} {n} (F .fmor {m} {n} M) i j)
    ≈⟨ scalar-inv-cong (entry-F {m} {n} M i j) ⟩
      scalar-inv (scalar (M i j))
    ≈⟨ scalar-inv-scalar (M i j) ⟩
      M i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  -- Round trip: F is a left inverse of F⁻¹ up to hom equality.
  F∘F⁻¹ : ∀ {m n} (f : X^ m ⇒ X^ n) → F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f) ≈ f
  F∘F⁻¹ {m} {n} f = entry-ext {m} {n} (λ i j →
    begin
      entry {m} {n} (F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f)) i j
    ≈⟨ entry-F {m} {n} (F⁻¹ .fmor {m} {n} f) i j ⟩
      scalar (scalar-inv (entry {m} {n} f i j))
    ≈⟨ scalar-scalar-inv _ ⟩
      entry {m} {n} f i j
    ∎) where open ≈-Reasoning isEquiv

  -- TODO: CMon preservation — restore next.
  -- F-εₘ : ∀ {m n} → F .fmor (Mat.εₘ {m} {n}) ≈ εm {X^ n} {X^ m}
  -- F-+ₘ : ∀ {m n} (M N : Mat n m) → F .fmor (M Mat.+ₘ N) ≈ (F .fmor M +m F .fmor N)
