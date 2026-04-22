{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal; HasInitial; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)
open import commutative-semiring using (CommutativeSemiring)

-- Embedding of Mat(S) into a CMon-enriched category 𝒞 with binary biproducts and zero object, via a chosen
-- scalar object X whose endomorphism semiring is (isomorphic to) S, witnessed by a semiring homomorphism
-- scalar : Carrier S → (X ⇒ X). The representation functor builds the morphism for a matrix M by taking
-- the n-ary pair of n-ary copairs of the scalar-embedded matrix entries.
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
  (let open CommutativeSemiring S using (Carrier) renaming (ε to S-ε; ι to S-ι; _+_ to _+ₛ_; _·_ to _·ₛ_; _≈_ to _≈ₛ_))
  (scalar : Carrier → X ⇒ X)
  (scalar-cong : ∀ {a b} → a ≈ₛ b → scalar a ≈ scalar b)
  (scalar-ε : scalar S-ε ≈ εm)
  (scalar-ι : scalar S-ι ≈ id X)
  (scalar-+ : ∀ {a b} → scalar (a +ₛ b) ≈ scalar a +m scalar b)
  (scalar-· : ∀ {a b} → scalar (a ·ₛ b) ≈ scalar a ∘ scalar b)
  where

  open CommutativeMonoid
  open Biproduct
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  _⊕_ : obj → obj → obj
  x ⊕ y = prod (BP x y)

  -- n-ary biproduct.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = X ⊕ X^ n

  -- i-th injection.
  ι : ∀ {n} → Fin n → X ⇒ X^ n
  ι {suc n} zero = in₁ (BP X (X^ n))
  ι {suc n} (suc i) = in₂ (BP X (X^ n)) ∘ ι i

  -- i-th projection.
  π : ∀ {n} → Fin n → X^ n ⇒ X
  π {suc n} zero = p₁ (BP X (X^ n))
  π {suc n} (suc i) = π i ∘ p₂ (BP X (X^ n))

  tuple : ∀ {n Z} → (Fin n → Z ⇒ X) → Z ⇒ X^ n
  tuple {zero} f = to-terminal
  tuple {suc n} f = pair (BP X (X^ n)) (f zero) (tuple (λ i → f (suc i)))

  cotuple : ∀ {n Z} → (Fin n → X ⇒ Z) → X^ n ⇒ Z
  cotuple {zero} f = from-initial
  cotuple {suc n} f = copair (BP X (X^ n)) (f zero) (cotuple (λ i → f (suc i)))

  tuple-π : ∀ {n Z} (f : Fin n → Z ⇒ X) (i : Fin n) → (π i ∘ tuple f) ≈ f i
  tuple-π {suc n} f zero = pair-p₁ (BP X (X^ n)) (f zero) (tuple (λ i → f (suc i)))
  tuple-π {suc n} f (suc i) =
    begin
      (π i ∘ p₂ (BP X (X^ n))) ∘ tuple f
    ≈⟨ assoc _ _ _ ⟩
      π i ∘ (p₂ (BP X (X^ n)) ∘ tuple f)
    ≈⟨ ∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) (f zero) (tuple (λ i → f (suc i)))) ⟩
      π i ∘ tuple (λ i → f (suc i))
    ≈⟨ tuple-π (λ i → f (suc i)) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  cotuple-ι : ∀ {n Z} (f : Fin n → X ⇒ Z) (i : Fin n) → (cotuple f ∘ ι i) ≈ f i
  cotuple-ι {suc n} f zero = copair-in₁ (BP X (X^ n)) (f zero) (cotuple (λ i → f (suc i)))
  cotuple-ι {suc n} f (suc i) =
    begin
      cotuple f ∘ (in₂ (BP X (X^ n)) ∘ ι i)
    ≈˘⟨ assoc _ _ _ ⟩
      (cotuple f ∘ in₂ (BP X (X^ n))) ∘ ι i
    ≈⟨ ∘-cong (copair-in₂ (BP X (X^ n)) (f zero) (cotuple (λ i → f (suc i)))) ≈-refl ⟩
      cotuple (λ i → f (suc i)) ∘ ι i
    ≈⟨ cotuple-ι (λ i → f (suc i)) i ⟩
      f (suc i)
    ∎ where open ≈-Reasoning isEquiv

  tuple-cong : ∀ {n Z} (f g : Fin n → Z ⇒ X) → (∀ i → f i ≈ g i) → tuple f ≈ tuple g
  tuple-cong {zero}  f g h = ≈-refl
  tuple-cong {suc n} f g h =
    pair-cong (BP X (X^ n)) (h zero) (tuple-cong (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

  cotuple-cong : ∀ {n Z} (f g : Fin n → X ⇒ Z) → (∀ i → f i ≈ g i) → cotuple f ≈ cotuple g
  cotuple-cong {zero}  f g h = ≈-refl
  cotuple-cong {suc n} f g h =
    copair-cong (BP X (X^ n)) (h zero) (cotuple-cong (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

  tuple-ext : ∀ {n Z} (f : Z ⇒ X^ n) → tuple {n} (λ i → π {n} i ∘ f) ≈ f
  tuple-ext {zero}  f = to-terminal-ext f
  tuple-ext {suc n} f =
    begin
      pair (BP X (X^ n)) (p₁ (BP X (X^ n)) ∘ f) (tuple {n} (λ i → (π {n} i ∘ p₂ (BP X (X^ n))) ∘ f))
    ≈⟨ pair-cong (BP X (X^ n)) ≈-refl (tuple-cong {n} _ _ (λ i → assoc (π {n} i) (p₂ (BP X (X^ n))) f)) ⟩
      pair (BP X (X^ n)) (p₁ (BP X (X^ n)) ∘ f) (tuple {n} (λ i → π {n} i ∘ (p₂ (BP X (X^ n)) ∘ f)))
    ≈⟨ pair-cong (BP X (X^ n)) ≈-refl (tuple-ext {n} (p₂ (BP X (X^ n)) ∘ f)) ⟩
      pair (BP X (X^ n)) (p₁ (BP X (X^ n)) ∘ f) (p₂ (BP X (X^ n)) ∘ f)
    ≈⟨ pair-ext (BP X (X^ n)) f ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

  cotuple-ext : ∀ {n Z} (f : X^ n ⇒ Z) → cotuple {n} (λ i → f ∘ ι {n} i) ≈ f
  cotuple-ext {zero}  f = from-initial-ext f
  cotuple-ext {suc n} f =
    begin
      copair (BP X (X^ n)) (f ∘ in₁ (BP X (X^ n))) (cotuple {n} (λ i → f ∘ (in₂ (BP X (X^ n)) ∘ ι {n} i)))
    ≈⟨ copair-cong (BP X (X^ n)) ≈-refl (cotuple-cong {n} _ _ (λ i → ≈-sym (assoc f (in₂ (BP X (X^ n))) (ι {n} i)))) ⟩
      copair (BP X (X^ n)) (f ∘ in₁ (BP X (X^ n))) (cotuple {n} (λ i → (f ∘ in₂ (BP X (X^ n))) ∘ ι {n} i))
    ≈⟨ copair-cong (BP X (X^ n)) ≈-refl (cotuple-ext {n} (f ∘ in₂ (BP X (X^ n)))) ⟩
      copair (BP X (X^ n)) (f ∘ in₁ (BP X (X^ n))) (f ∘ in₂ (BP X (X^ n)))
    ≈⟨ copair-ext (BP X (X^ n)) f ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

  tuple-natural : ∀ {n Y Z} (f : Fin n → Y ⇒ X) (g : Z ⇒ Y) → (tuple f ∘ g) ≈ tuple {n} (λ i → f i ∘ g)
  tuple-natural {zero}  f g = ≈-sym (to-terminal-ext (to-terminal ∘ g))
  tuple-natural {suc n} f g =
    begin
      pair (BP X (X^ n)) (f zero) (tuple (λ i → f (suc i))) ∘ g
    ≈⟨ comp-bilinear₁ _ _ g ⟩
      ((in₁ (BP X (X^ n)) ∘ f zero) ∘ g) +m ((in₂ (BP X (X^ n)) ∘ tuple (λ i → f (suc i))) ∘ g)
    ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      (in₁ (BP X (X^ n)) ∘ (f zero ∘ g)) +m (in₂ (BP X (X^ n)) ∘ (tuple (λ i → f (suc i)) ∘ g))
    ≈⟨ pair-cong (BP X (X^ n)) ≈-refl (tuple-natural (λ i → f (suc i)) g) ⟩
      pair (BP X (X^ n)) (f zero ∘ g) (tuple {n} (λ i → f (suc i) ∘ g))
    ∎ where open ≈-Reasoning isEquiv

  cotuple-natural : ∀ {n Y Z} (g : Y ⇒ Z) (f : Fin n → X ⇒ Y) → (g ∘ cotuple f) ≈ cotuple {n} (λ i → g ∘ f i)
  cotuple-natural {zero}  g f = ≈-sym (from-initial-ext (g ∘ from-initial))
  cotuple-natural {suc n} g f =
    begin
      g ∘ copair (BP X (X^ n)) (f zero) (cotuple (λ i → f (suc i)))
    ≈⟨ comp-bilinear₂ g _ _ ⟩
      (g ∘ (f zero ∘ p₁ (BP X (X^ n)))) +m (g ∘ (cotuple (λ i → f (suc i)) ∘ p₂ (BP X (X^ n))))
    ≈⟨ homCM _ _ .+-cong (≈-sym (assoc _ _ _)) (≈-sym (assoc _ _ _)) ⟩
      ((g ∘ f zero) ∘ p₁ (BP X (X^ n))) +m ((g ∘ cotuple (λ i → f (suc i))) ∘ p₂ (BP X (X^ n)))
    ≈⟨ copair-cong (BP X (X^ n)) ≈-refl (cotuple-natural g (λ i → f (suc i))) ⟩
      copair (BP X (X^ n)) (g ∘ f zero) (cotuple {n} (λ i → g ∘ f (suc i)))
    ∎ where open ≈-Reasoning isEquiv

  -- Matrix entry: the (i, j)-entry of a morphism f : X^m → X^n.
  entry : ∀ {m n} → X^ m ⇒ X^ n → Fin n → Fin m → X ⇒ X
  entry f i j = π i ∘ (f ∘ ι j)

  -- The (i,j)-entry of a composition is a dot product of entries (matrix multiplication).
  entry-comp : ∀ {m n k} (f : X^ m ⇒ X^ n) (g : X^ n ⇒ X^ k) (i : Fin k) (j : Fin m) →
               entry (g ∘ f) i j ≈ (cotuple {n} (λ l → entry g i l) ∘ tuple {n} (λ l → entry f l j))
  entry-comp {m} {n} {k} f g i j =
    begin
      π {k} i ∘ ((g ∘ f) ∘ ι {m} j)
    ≈⟨ ∘-cong ≈-refl (assoc g f (ι j)) ⟩
      π {k} i ∘ (g ∘ (f ∘ ι {m} j))
    ≈˘⟨ assoc (π {k} i) g (f ∘ ι {m} j) ⟩
      (π {k} i ∘ g) ∘ (f ∘ ι {m} j)
    ≈˘⟨ ∘-cong (cotuple-ext {n} (π {k} i ∘ g)) ≈-refl ⟩
      cotuple {n} (λ l → (π {k} i ∘ g) ∘ ι {n} l) ∘ (f ∘ ι {m} j)
    ≈⟨ ∘-cong (cotuple-cong {n} _ _ (λ l → assoc (π {k} i) g (ι {n} l))) ≈-refl ⟩
      cotuple {n} (λ l → entry g i l) ∘ (f ∘ ι {m} j)
    ≈˘⟨ ∘-cong ≈-refl (tuple-ext {n} (f ∘ ι {m} j)) ⟩
      cotuple {n} (λ l → entry g i l) ∘ tuple {n} (λ l → entry f l j)
    ∎ where open ≈-Reasoning isEquiv

  -- Morphisms with equal entries are equal.
  entry-ext : ∀ {m n} {f g : X^ m ⇒ X^ n} → (∀ (i : Fin n) (j : Fin m) → entry f i j ≈ entry g i j) → f ≈ g
  entry-ext {m} {n} {f} {g} h =
    begin
      f
    ≈˘⟨ tuple-ext {n} f ⟩
      tuple {n} (λ i → π {n} i ∘ f)
    ≈˘⟨ tuple-cong {n} _ _ (λ i → cotuple-ext {m} (π {n} i ∘ f)) ⟩
      tuple {n} (λ i → cotuple {m} (λ j → (π {n} i ∘ f) ∘ ι {m} j))
    ≈⟨ tuple-cong {n} _ _ (λ i → cotuple-cong {m} _ _ (λ j → entry-step i j)) ⟩
      tuple {n} (λ i → cotuple {m} (λ j → (π {n} i ∘ g) ∘ ι {m} j))
    ≈⟨ tuple-cong {n} _ _ (λ i → cotuple-ext {m} (π {n} i ∘ g)) ⟩
      tuple {n} (λ i → π {n} i ∘ g)
    ≈⟨ tuple-ext {n} g ⟩
      g
    ∎ where
      entry-step : ∀ (i : Fin n) (j : Fin m) → ((π {n} i ∘ f) ∘ ι {m} j) ≈ ((π {n} i ∘ g) ∘ ι {m} j)
      entry-step i j =
        begin
          (π {n} i ∘ f) ∘ ι {m} j
        ≈⟨ assoc (π {n} i) f (ι {m} j) ⟩
          entry f i j
        ≈⟨ h i j ⟩
          entry g i j
        ≈˘⟨ assoc (π {n} i) g (ι {m} j) ⟩
          (π {n} i ∘ g) ∘ ι {m} j
        ∎ where open ≈-Reasoning isEquiv
      open ≈-Reasoning isEquiv

  open import functor using (Functor)
  open Functor
  import matrix
  private
    module Mat = matrix S
    open matrix S using (Mat)

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

  -- The representation functor: maps a matrix M to its "build from entries" morphism in 𝒞.
  𝓕 : Functor Mat.cat 𝒞
  𝓕 .fobj = X^
  𝓕 .fmor M = tuple (λ i → cotuple (λ j → scalar (M i j)))
  𝓕 .fmor-cong p = tuple-cong _ _ (λ i → cotuple-cong _ _ (λ j → scalar-cong (p i j)))
  𝓕 .fmor-id {n} = entry-ext (λ i j →
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
  𝓕 .fmor-comp {x} {y} {z} M N = entry-ext (λ i j →
    begin
      entry (𝓕 .fmor (M Mat.∘ N)) i j
    ≈⟨ entry-𝓕 (M Mat.∘ N) i j ⟩
      scalar (Mat.Σ (λ k → M i k ·ₛ N k j))
    ≈⟨ scalar-Σ (λ k → M i k) (λ k → N k j) ⟩
      cotuple {y} (λ k → scalar (M i k)) ∘ tuple {y} (λ k → scalar (N k j))
    ≈˘⟨ ∘-cong (cotuple-cong {y} _ _ (λ k → entry-𝓕 M i k))
               (tuple-cong {y} _ _ (λ k → entry-𝓕 N k j)) ⟩
      cotuple {y} (λ k → entry (𝓕 .fmor M) i k) ∘ tuple {y} (λ k → entry (𝓕 .fmor N) k j)
    ≈˘⟨ entry-comp {x} {y} {z} (𝓕 .fmor N) (𝓕 .fmor M) i j ⟩
      π {z} i ∘ ((𝓕 .fmor M ∘ 𝓕 .fmor N) ∘ ι {x} j)
    ∎) where
      open ≈-Reasoning isEquiv
      entry-𝓕 : ∀ {m n} (M : Mat n m) (i : Fin n) (j : Fin m) → entry (𝓕 .fmor M) i j ≈ scalar (M i j)
      entry-𝓕 {m} {n} M i j =
        begin
          π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j'))) ∘ ι {m} j)
        ≈˘⟨ assoc _ _ _ ⟩
          (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j')))) ∘ ι {m} j
        ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
          cotuple {m} (λ j' → scalar (M i j')) ∘ ι {m} j
        ≈⟨ cotuple-ι {m} _ j ⟩
          scalar (M i j)
        ∎

  -- Entry-wise characterization of 𝓕.fmor.
  entry-𝓕 : ∀ {m n} (M : Mat n m) (i : Fin n) (j : Fin m) → entry (𝓕 .fmor M) i j ≈ scalar (M i j)
  entry-𝓕 {m} {n} M i j =
    begin
      π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j'))) ∘ ι {m} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar (M i' j')))) ∘ ι {m} j
    ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
      cotuple {m} (λ j' → scalar (M i j')) ∘ ι {m} j
    ≈⟨ cotuple-ι {m} _ j ⟩
      scalar (M i j)
    ∎ where open ≈-Reasoning isEquiv

  open import finite-product-functor
    using (preserve-chosen-terminal; preserve-chosen-products)
  open import cmon-enriched using (biproducts→products)

  -- Chosen terminals: matrix's 0, and 𝟘 in 𝒞.
  Mat-terminal : HasTerminal Mat.cat
  Mat-terminal = Mat.terminal

  𝒞-terminal : HasTerminal 𝒞
  𝒞-terminal .HasTerminal.witness = 𝟘
  𝒞-terminal .HasTerminal.is-terminal = 𝟘-terminal

  𝓕-preserve-terminal : preserve-chosen-terminal 𝓕 Mat-terminal 𝒞-terminal
  𝓕-preserve-terminal .Category.IsIso.inverse = id 𝟘
  𝓕-preserve-terminal .Category.IsIso.f∘inverse≈id =
    ≈-trans id-right (to-terminal-ext (id 𝟘))
  𝓕-preserve-terminal .Category.IsIso.inverse∘f≈id =
    ≈-trans id-left (to-terminal-ext (id 𝟘))

  -- 𝓕 preserves the zero morphism.
  𝓕-εₘ : ∀ {m n} → 𝓕 .fmor (Mat.εₘ {m} {n}) ≈ εm {X^ n} {X^ m}
  𝓕-εₘ {m} {n} = entry-ext {n} {m} (λ i j →
    begin
      entry {n} {m} (𝓕 .fmor (Mat.εₘ {m} {n})) i j
    ≈⟨ entry-𝓕 {n} {m} (Mat.εₘ {m} {n}) i j ⟩
      scalar S-ε
    ≈⟨ scalar-ε ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₂ (π {m} i) ⟩
      π {m} i ∘ εm
    ≈˘⟨ ∘-cong ≈-refl (comp-bilinear-ε₁ (ι {n} j)) ⟩
      π {m} i ∘ (εm ∘ ι {n} j)
    ∎) where open ≈-Reasoning isEquiv

  -- 𝓕 preserves addition of matrices.
  𝓕-+ₘ : ∀ {m n} (M N : Mat n m) → 𝓕 .fmor (M Mat.+ₘ N) ≈ (𝓕 .fmor M +m 𝓕 .fmor N)
  𝓕-+ₘ {m} {n} M N = entry-ext {m} {n} (λ i j →
    begin
      entry {m} {n} (𝓕 .fmor (M Mat.+ₘ N)) i j
    ≈⟨ entry-𝓕 {m} {n} (M Mat.+ₘ N) i j ⟩
      scalar (M i j +ₛ N i j)
    ≈⟨ scalar-+ ⟩
      scalar (M i j) +m scalar (N i j)
    ≈˘⟨ homCM _ _ .+-cong (entry-𝓕 {m} {n} M i j) (entry-𝓕 {m} {n} N i j) ⟩
      (π {n} i ∘ (𝓕 .fmor M ∘ ι {m} j)) +m (π {n} i ∘ (𝓕 .fmor N ∘ ι {m} j))
    ≈˘⟨ comp-bilinear₂ _ _ _ ⟩
      π {n} i ∘ ((𝓕 .fmor M ∘ ι {m} j) +m (𝓕 .fmor N ∘ ι {m} j))
    ≈˘⟨ ∘-cong ≈-refl (comp-bilinear₁ _ _ _) ⟩
      π {n} i ∘ ((𝓕 .fmor M +m 𝓕 .fmor N) ∘ ι {m} j)
    ∎) where open ≈-Reasoning isEquiv

  Mat-products : HasProducts Mat.cat
  Mat-products = biproducts→products Mat.cmon Mat.biproduct

  𝒞-products : HasProducts 𝒞
  𝒞-products = biproducts→products CM BP

  𝓕-preserve-products : preserve-chosen-products 𝓕 Mat-products 𝒞-products
  𝓕-preserve-products {m} {n} = iso
    where
      module BP' = Biproduct (BP (X^ m) (X^ n))

      𝓕p₁ = 𝓕 .fmor (Mat.p₁ {m} {n})
      𝓕p₂ = 𝓕 .fmor (Mat.p₂ {m} {n})
      𝓕in₁ = 𝓕 .fmor (Mat.in₁ {m} {n})
      𝓕in₂ = 𝓕 .fmor (Mat.in₂ {m} {n})

      forward = BP'.pair 𝓕p₁ 𝓕p₂
      backward = BP'.copair 𝓕in₁ 𝓕in₂

      -- 𝓕 preserves the biproduct equations from Mat.
      𝓕-id-1 : (𝓕p₁ ∘ 𝓕in₁) ≈ id (X^ m)
      𝓕-id-1 = ≈-trans (≈-sym (𝓕 .fmor-comp (Mat.p₁ {m} {n}) (Mat.in₁ {m} {n})))
                        (≈-trans (𝓕 .fmor-cong (Mat.id-1 m n)) (𝓕 .fmor-id {m}))

      𝓕-id-2 : (𝓕p₂ ∘ 𝓕in₂) ≈ id (X^ n)
      𝓕-id-2 = ≈-trans (≈-sym (𝓕 .fmor-comp (Mat.p₂ {m} {n}) (Mat.in₂ {m} {n})))
                        (≈-trans (𝓕 .fmor-cong (Mat.id-2 m n)) (𝓕 .fmor-id {n}))

      𝓕-zero-1 : (𝓕p₁ ∘ 𝓕in₂) ≈ εm {X^ n} {X^ m}
      𝓕-zero-1 = ≈-trans (≈-sym (𝓕 .fmor-comp (Mat.p₁ {m} {n}) (Mat.in₂ {m} {n})))
                          (≈-trans (𝓕 .fmor-cong (Mat.zero-1 m n)) (𝓕-εₘ {m} {n}))

      𝓕-zero-2 : (𝓕p₂ ∘ 𝓕in₁) ≈ εm {X^ m} {X^ n}
      𝓕-zero-2 = ≈-trans (≈-sym (𝓕 .fmor-comp (Mat.p₂ {m} {n}) (Mat.in₁ {m} {n})))
                          (≈-trans (𝓕 .fmor-cong (Mat.zero-2 m n)) (𝓕-εₘ {n} {m}))

      in₁-p₁ : Mat (m Data.Nat.+ n) (m Data.Nat.+ n)
      in₁-p₁ = Mat.in₁ {m} {n} Mat.∘ Mat.p₁ {m} {n}

      in₂-p₂ : Mat (m Data.Nat.+ n) (m Data.Nat.+ n)
      in₂-p₂ = Mat.in₂ {m} {n} Mat.∘ Mat.p₂ {m} {n}

      𝓕-id-+ : ((𝓕in₁ ∘ 𝓕p₁) +m (𝓕in₂ ∘ 𝓕p₂)) ≈ id (X^ (m Data.Nat.+ n))
      𝓕-id-+ =
        begin
          (𝓕in₁ ∘ 𝓕p₁) +m (𝓕in₂ ∘ 𝓕p₂)
        ≈˘⟨ homCM _ _ .+-cong (𝓕 .fmor-comp (Mat.in₁ {m} {n}) (Mat.p₁ {m} {n}))
                              (𝓕 .fmor-comp (Mat.in₂ {m} {n}) (Mat.p₂ {m} {n})) ⟩
          𝓕 .fmor in₁-p₁ +m 𝓕 .fmor in₂-p₂
        ≈˘⟨ 𝓕-+ₘ in₁-p₁ in₂-p₂ ⟩
          𝓕 .fmor (in₁-p₁ Mat.+ₘ in₂-p₂)
        ≈⟨ 𝓕 .fmor-cong (Mat.id-+ m n) ⟩
          𝓕 .fmor (Mat.I {m Data.Nat.+ n})
        ≈⟨ 𝓕 .fmor-id {m Data.Nat.+ n} ⟩
          id _
        ∎ where open ≈-Reasoning isEquiv

      𝓕p₁-backward : (𝓕p₁ ∘ backward) ≈ BP'.p₁
      𝓕p₁-backward =
        begin
          𝓕p₁ ∘ ((𝓕in₁ ∘ BP'.p₁) +m (𝓕in₂ ∘ BP'.p₂))
        ≈⟨ comp-bilinear₂ _ _ _ ⟩
          (𝓕p₁ ∘ (𝓕in₁ ∘ BP'.p₁)) +m (𝓕p₁ ∘ (𝓕in₂ ∘ BP'.p₂))
        ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
          ((𝓕p₁ ∘ 𝓕in₁) ∘ BP'.p₁) +m ((𝓕p₁ ∘ 𝓕in₂) ∘ BP'.p₂)
        ≈⟨ homCM _ _ .+-cong (∘-cong 𝓕-id-1 ≈-refl) (∘-cong 𝓕-zero-1 ≈-refl) ⟩
          (id _ ∘ BP'.p₁) +m (εm ∘ BP'.p₂)
        ≈⟨ homCM _ _ .+-cong id-left (comp-bilinear-ε₁ _) ⟩
          BP'.p₁ +m εm
        ≈⟨ +m-runit ⟩
          BP'.p₁
        ∎ where open ≈-Reasoning isEquiv

      𝓕p₂-backward : (𝓕p₂ ∘ backward) ≈ BP'.p₂
      𝓕p₂-backward =
        begin
          𝓕p₂ ∘ ((𝓕in₁ ∘ BP'.p₁) +m (𝓕in₂ ∘ BP'.p₂))
        ≈⟨ comp-bilinear₂ _ _ _ ⟩
          (𝓕p₂ ∘ (𝓕in₁ ∘ BP'.p₁)) +m (𝓕p₂ ∘ (𝓕in₂ ∘ BP'.p₂))
        ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
          ((𝓕p₂ ∘ 𝓕in₁) ∘ BP'.p₁) +m ((𝓕p₂ ∘ 𝓕in₂) ∘ BP'.p₂)
        ≈⟨ homCM _ _ .+-cong (∘-cong 𝓕-zero-2 ≈-refl) (∘-cong 𝓕-id-2 ≈-refl) ⟩
          (εm ∘ BP'.p₁) +m (id _ ∘ BP'.p₂)
        ≈⟨ homCM _ _ .+-cong (comp-bilinear-ε₁ _) id-left ⟩
          εm +m BP'.p₂
        ≈⟨ homCM _ _ .+-lunit ⟩
          BP'.p₂
        ∎ where open ≈-Reasoning isEquiv

      forward∘backward : (forward ∘ backward) ≈ id BP'.prod
      forward∘backward =
        begin
          forward ∘ backward
        ≈⟨ BP'.pair-natural _ _ _ ⟩
          BP'.pair (𝓕p₁ ∘ backward) (𝓕p₂ ∘ backward)
        ≈⟨ BP'.pair-cong 𝓕p₁-backward 𝓕p₂-backward ⟩
          BP'.pair BP'.p₁ BP'.p₂
        ≈⟨ BP'.pair-ext0 ⟩
          id BP'.prod
        ∎ where open ≈-Reasoning isEquiv

      -- Rearrange (a ∘ p) ∘ (i ∘ b) to a ∘ ((p ∘ i) ∘ b).
      collapse : ∀ {A B C D E} (a : D ⇒ E) (p : C ⇒ D) (i : B ⇒ C) (b : A ⇒ B) →
                 ((a ∘ p) ∘ (i ∘ b)) ≈ (a ∘ ((p ∘ i) ∘ b))
      collapse a p i b =
        ≈-trans (assoc _ _ _) (∘-cong ≈-refl (≈-sym (assoc _ _ _)))

      cross-id : ∀ {A B C} (a : B ⇒ C) (b : A ⇒ B) → (a ∘ (id B ∘ b)) ≈ (a ∘ b)
      cross-id a b = ∘-cong ≈-refl id-left

      cross-εm : ∀ {A B C D} (a : C ⇒ D) (b : A ⇒ B) → (a ∘ (εm {B} {C} ∘ b)) ≈ εm
      cross-εm a b =
        ≈-trans (∘-cong ≈-refl (comp-bilinear-ε₁ _)) (comp-bilinear-ε₂ _)

      -- backward ∘ forward ≈ id via 4-term expansion; cross-terms vanish.
      backward∘forward : (backward ∘ forward) ≈ id (X^ (m Data.Nat.+ n))
      backward∘forward =
        begin
          ((𝓕in₁ ∘ BP'.p₁) +m (𝓕in₂ ∘ BP'.p₂)) ∘ ((BP'.in₁ ∘ 𝓕p₁) +m (BP'.in₂ ∘ 𝓕p₂))
        ≈⟨ comp-bilinear₁ _ _ _ ⟩
          ((𝓕in₁ ∘ BP'.p₁) ∘ ((BP'.in₁ ∘ 𝓕p₁) +m (BP'.in₂ ∘ 𝓕p₂))) +m
          ((𝓕in₂ ∘ BP'.p₂) ∘ ((BP'.in₁ ∘ 𝓕p₁) +m (BP'.in₂ ∘ 𝓕p₂)))
        ≈⟨ homCM _ _ .+-cong (comp-bilinear₂ _ _ _) (comp-bilinear₂ _ _ _) ⟩
          (((𝓕in₁ ∘ BP'.p₁) ∘ (BP'.in₁ ∘ 𝓕p₁)) +m ((𝓕in₁ ∘ BP'.p₁) ∘ (BP'.in₂ ∘ 𝓕p₂))) +m
          (((𝓕in₂ ∘ BP'.p₂) ∘ (BP'.in₁ ∘ 𝓕p₁)) +m ((𝓕in₂ ∘ BP'.p₂) ∘ (BP'.in₂ ∘ 𝓕p₂)))
        ≈⟨ homCM _ _ .+-cong
             (homCM _ _ .+-cong (collapse 𝓕in₁ BP'.p₁ BP'.in₁ 𝓕p₁) (collapse 𝓕in₁ BP'.p₁ BP'.in₂ 𝓕p₂))
             (homCM _ _ .+-cong (collapse 𝓕in₂ BP'.p₂ BP'.in₁ 𝓕p₁) (collapse 𝓕in₂ BP'.p₂ BP'.in₂ 𝓕p₂)) ⟩
          ((𝓕in₁ ∘ ((BP'.p₁ ∘ BP'.in₁) ∘ 𝓕p₁)) +m (𝓕in₁ ∘ ((BP'.p₁ ∘ BP'.in₂) ∘ 𝓕p₂))) +m
          ((𝓕in₂ ∘ ((BP'.p₂ ∘ BP'.in₁) ∘ 𝓕p₁)) +m (𝓕in₂ ∘ ((BP'.p₂ ∘ BP'.in₂) ∘ 𝓕p₂)))
        ≈⟨ homCM _ _ .+-cong
             (homCM _ _ .+-cong
                (∘-cong ≈-refl (∘-cong BP'.id-1 ≈-refl))
                (∘-cong ≈-refl (∘-cong BP'.zero-1 ≈-refl)))
             (homCM _ _ .+-cong
                (∘-cong ≈-refl (∘-cong BP'.zero-2 ≈-refl))
                (∘-cong ≈-refl (∘-cong BP'.id-2 ≈-refl))) ⟩
          ((𝓕in₁ ∘ (id _ ∘ 𝓕p₁)) +m (𝓕in₁ ∘ (εm ∘ 𝓕p₂))) +m
          ((𝓕in₂ ∘ (εm ∘ 𝓕p₁)) +m (𝓕in₂ ∘ (id _ ∘ 𝓕p₂)))
        ≈⟨ homCM _ _ .+-cong
             (homCM _ _ .+-cong (cross-id 𝓕in₁ 𝓕p₁) (cross-εm 𝓕in₁ 𝓕p₂))
             (homCM _ _ .+-cong (cross-εm 𝓕in₂ 𝓕p₁) (cross-id 𝓕in₂ 𝓕p₂)) ⟩
          ((𝓕in₁ ∘ 𝓕p₁) +m εm) +m (εm +m (𝓕in₂ ∘ 𝓕p₂))
        ≈⟨ homCM _ _ .+-cong +m-runit (homCM _ _ .+-lunit) ⟩
          (𝓕in₁ ∘ 𝓕p₁) +m (𝓕in₂ ∘ 𝓕p₂)
        ≈⟨ 𝓕-id-+ ⟩
          id _
        ∎ where open ≈-Reasoning isEquiv

      iso : Category.IsIso 𝒞 forward
      iso = record
        { inverse = backward
        ; f∘inverse≈id = forward∘backward
        ; inverse∘f≈id = backward∘forward
        }
