{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal; HasInitial; HasTerminal)
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
  (let open CommutativeSemiring S using (Carrier; ε; _+_; _·_) renaming (ι to 𝟙))
  (scalar : Carrier → X ⇒ X)
  (scalar-ε : scalar ε ≈ εm)
  (scalar-𝟙 : scalar 𝟙 ≈ id X)
  (scalar-+ : ∀ {a b} → scalar (a + b) ≈ scalar a +m scalar b)
  (scalar-· : ∀ {a b} → scalar (a · b) ≈ scalar a ∘ scalar b)
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

  open import functor using (Functor)
  open Functor
  import matrix
  private
    module Mat = matrix S
    open matrix S using (Mat)

  -- The representation functor: maps a matrix M to its "build from entries" morphism in 𝒞.
  𝓕 : Functor Mat.cat 𝒞
  𝓕 .fobj = X^
  𝓕 .fmor M = tuple (λ i → cotuple (λ j → scalar (M i j)))
  𝓕 .fmor-cong = {!!}
  𝓕 .fmor-id = {!!}
  𝓕 .fmor-comp = {!!}

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
