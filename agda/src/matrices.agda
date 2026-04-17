{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal; HasInitial; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

-- Matrix representation via iterated biproducts in a (necessarily CMon-enriched) category with binary
-- biproducts and zero object, and base object X. Instantiating X to Two in SemiLat recovers the "Boolean
-- Jacobian" setting FDVect_2. The endomorphisms of X act as the "scalars", and form a semiring, with
-- composition as multiplication and addition via the CMon enrichment. We need the multiplication to be
-- commutative for the dot product to be commutative, in turn required for transpose to preserve composition
-- (i.e. for the usual AB^T = B^T A^T to hold).
module matrices
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  (open Category 𝒞)
  (scalar-comm : ∀ (f g : X ⇒ X) → (f ∘ g) ≈ (g ∘ f))
  where

  open CMonEnriched CM
  open CommutativeMonoid
  open Biproduct
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  -- n-ary biproduct.
  X^ : ℕ → obj
  X^ zero = 𝟘
  X^ (suc n) = prod (BP X (X^ n))

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
  tuple-cong {suc n} f g h = pair-cong (BP X (X^ n)) (h zero) (tuple-cong (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

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

  cotuple-cong : ∀ {n Z} (f g : Fin n → X ⇒ Z) → (∀ i → f i ≈ g i) → cotuple f ≈ cotuple g
  cotuple-cong {zero}  f g h = ≈-refl
  cotuple-cong {suc n} f g h = copair-cong (BP X (X^ n)) (h zero) (cotuple-cong (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

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

  -- Requires commutativity of scalar multiplication (composition in X ⇒ X).
  dot-comm : ∀ {n} (h k : Fin n → X ⇒ X) → (cotuple {n} h ∘ tuple {n} k) ≈ (cotuple {n} k ∘ tuple {n} h)
  dot-comm {zero}  h k = ≈-refl
  dot-comm {suc n} h k =
    begin
      copair (BP X (X^ n)) (h zero) (cotuple (λ i → h (suc i))) ∘ pair (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i)))
    ≈⟨ comp-bilinear₁ _ _ _ ⟩
      ((h zero ∘ p₁ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i))))
      +m
      ((cotuple (λ i → h (suc i)) ∘ p₂ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i))))
    ≈⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      (h zero ∘ (p₁ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i)))))
      +m
      (cotuple (λ i → h (suc i)) ∘ (p₂ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i)))))
    ≈⟨ homCM _ _ .+-cong
         (∘-cong ≈-refl (pair-p₁ (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i)))))
         (∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) (k zero) (tuple (λ i → k (suc i))))) ⟩
      (h zero ∘ k zero) +m (cotuple {n} (λ i → h (suc i)) ∘ tuple {n} (λ i → k (suc i)))
    ≈⟨ homCM _ _ .+-cong (scalar-comm (h zero) (k zero)) (dot-comm (λ i → h (suc i)) (λ i → k (suc i))) ⟩
      (k zero ∘ h zero) +m (cotuple {n} (λ i → k (suc i)) ∘ tuple {n} (λ i → h (suc i)))
    ≈˘⟨ homCM _ _ .+-cong
          (∘-cong ≈-refl (pair-p₁ (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i)))))
          (∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i))))) ⟩
      (k zero ∘ (p₁ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i)))))
      +m
      (cotuple (λ i → k (suc i)) ∘ (p₂ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i)))))
    ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((k zero ∘ p₁ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i))))
      +m
      ((cotuple (λ i → k (suc i)) ∘ p₂ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i))))
    ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
      copair (BP X (X^ n)) (k zero) (cotuple (λ i → k (suc i))) ∘ pair (BP X (X^ n)) (h zero) (tuple (λ i → h (suc i)))
    ∎ where open ≈-Reasoning isEquiv

  -- Dagger structure.
  transpose : ∀ {m n} → X^ m ⇒ X^ n → X^ n ⇒ X^ m
  transpose {m} {n} f = tuple {m} (λ j → cotuple {n} (λ i → entry f i j))

  -- Sanity check that transpose does what we expect.
  transpose-entry : ∀ {m n} (f : X^ m ⇒ X^ n) (i : Fin m) (j : Fin n) →
                    entry (transpose {m} {n} f) i j ≈ entry f j i
  transpose-entry {m} {n} f i j =
    begin
      π {m} i ∘ (transpose {m} {n} f ∘ ι {n} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {m} i ∘ transpose {m} {n} f) ∘ ι {n} j
    ≈⟨ ∘-cong (tuple-π {m} (λ k → cotuple {n} (λ l → entry f l k)) i) ≈-refl ⟩
      cotuple {n} (λ l → entry f l i) ∘ ι {n} j
    ≈⟨ cotuple-ι {n} (λ l → entry f l i) j ⟩
      π {n} j ∘ (f ∘ ι {m} i)
    ∎ where open ≈-Reasoning isEquiv

  transpose-involutive : ∀ {m n} (f : X^ m ⇒ X^ n) → transpose {n} {m} (transpose {m} {n} f) ≈ f
  transpose-involutive {m} {n} f =
    begin
      tuple {n} (λ j → cotuple {m} (λ i → entry (transpose {m} {n} f) i j))
    ≈⟨ tuple-cong {n} _ _ (λ j → cotuple-cong {m} _ _ (λ i → transpose-entry f i j)) ⟩
      tuple {n} (λ j → cotuple {m} (λ i → entry f j i))
    ≡⟨⟩
      tuple {n} (λ j → cotuple {m} (λ i → π {n} j ∘ (f ∘ ι {m} i)))
    ≈⟨ tuple-cong {n} _ _ (λ j → ≈-sym (cotuple-natural (π {n} j) (λ i → f ∘ ι {m} i))) ⟩
      tuple {n} (λ j → π {n} j ∘ cotuple {m} (λ i → f ∘ ι {m} i))
    ≈⟨ tuple-cong {n} _ _ (λ j → ∘-cong ≈-refl (cotuple-ext {m} f)) ⟩
      tuple {n} (λ j → π {n} j ∘ f)
    ≈⟨ tuple-ext {n} f ⟩
      f
    ∎ where open ≈-Reasoning isEquiv

  -- We have π i ∘ ι j is id when i = j and the zero morphism εm when i ≠ j; this is a trivial consequence.
  kronecker-sym : ∀ {n} (i j : Fin n) → (π {n} i ∘ ι {n} j) ≈ (π {n} j ∘ ι {n} i)
  kronecker-sym {suc n} zero zero = ≈-refl
  kronecker-sym {suc n} zero (suc j) =
    begin
      p₁ (BP X (X^ n)) ∘ (in₂ (BP X (X^ n)) ∘ ι j)
    ≈˘⟨ assoc _ _ _ ⟩
      (p₁ (BP X (X^ n)) ∘ in₂ (BP X (X^ n))) ∘ ι j
    ≈⟨ ∘-cong (zero-1 (BP X (X^ n))) ≈-refl ⟩
      εm ∘ ι j
    ≈⟨ comp-bilinear-ε₁ _ ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₂ _ ⟩
      π j ∘ εm
    ≈˘⟨ ∘-cong ≈-refl (zero-2 (BP X (X^ n))) ⟩
      π j ∘ (p₂ (BP X (X^ n)) ∘ in₁ (BP X (X^ n)))
    ≈˘⟨ assoc _ _ _ ⟩
      (π j ∘ p₂ (BP X (X^ n))) ∘ in₁ (BP X (X^ n))
    ∎ where open ≈-Reasoning isEquiv
  kronecker-sym {suc n} (suc i) zero = ≈-sym (kronecker-sym zero (suc i))
  kronecker-sym {suc n} (suc i) (suc j) =
    begin
      π (suc i) ∘ ι (suc j)
    ≈⟨ kronecker-suc i j ⟩
      (π i ∘ ι j)
    ≈⟨ kronecker-sym i j ⟩
      (π j ∘ ι i)
    ≈˘⟨ kronecker-suc j i ⟩
       π (suc j) ∘ ι (suc i)
    ∎ where
    open ≈-Reasoning isEquiv

    kronecker-suc : ∀ {n} (i j : Fin n) → (π {suc n} (suc i) ∘ ι {suc n} (suc j)) ≈ (π {n} i ∘ ι {n} j)
    kronecker-suc {n} i j =
      begin
        (π i ∘ p₂ (BP X (X^ n))) ∘ (in₂ (BP X (X^ n)) ∘ ι j)
      ≈⟨ assoc _ _ _ ⟩
        π i ∘ (p₂ (BP X (X^ n)) ∘ (in₂ (BP X (X^ n)) ∘ ι j))
      ≈⟨ ∘-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
        π i ∘ ((p₂ (BP X (X^ n)) ∘ in₂ (BP X (X^ n))) ∘ ι j)
      ≈⟨ ∘-cong ≈-refl (∘-cong (id-2 (BP X (X^ n))) ≈-refl) ⟩
        π i ∘ (id _ ∘ ι j)
      ≈⟨ ∘-cong ≈-refl id-left ⟩
        π i ∘ ι j
      ∎

  transpose-comp : ∀ {m n k} (f : X^ m ⇒ X^ n) (g : X^ n ⇒ X^ k) →
                   transpose {m} {k} (g ∘ f) ≈ (transpose {m} {n} f ∘ transpose {n} {k} g)
  private
    -- The entry of a composition is a dot product of entries (matrix multiplication).
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

  transpose-comp {m} {n} {k} f g =
    entry-ext (λ i j → let open ≈-Reasoning isEquiv in
      begin
        entry (transpose {m} {k} (g ∘ f)) i j
      ≈⟨ transpose-entry {m} {k} (g ∘ f) i j ⟩
        entry (g ∘ f) j i
      ≈⟨ entry-comp {m} {n} {k} f g j i ⟩
        cotuple {n} (λ l → entry g j l) ∘ tuple {n} (λ l → entry f l i)
      ≈⟨ dot-comm {n} (λ l → entry g j l) (λ l → entry f l i) ⟩
        cotuple {n} (λ l → entry f l i) ∘ tuple {n} (λ l → entry g j l)
      ≈˘⟨ ∘-cong (cotuple-cong {n} _ _ (λ l → transpose-entry {m} {n} f i l))
                  (tuple-cong {n} _ _ (λ l → transpose-entry {n} {k} g l j)) ⟩
        cotuple {n} (λ l → entry (transpose {m} {n} f) i l) ∘ tuple {n} (λ l → entry (transpose {n} {k} g) l j)
      ≈˘⟨ entry-comp {k} {n} {m} (transpose {n} {k} g) (transpose {m} {n} f) i j ⟩
        entry (transpose {m} {n} f ∘ transpose {n} {k} g) i j
      ∎)

  transpose-id : ∀ {n} → transpose {n} {n} (id (X^ n)) ≈ id (X^ n)
  transpose-id {n} =
    begin
      tuple {n} (λ j → cotuple {n} (λ i → π {n} i ∘ (id (X^ n) ∘ ι {n} j)))
    ≈⟨ tuple-cong {n} _ _ (λ j → cotuple-cong {n} _ _ (λ i → ∘-cong ≈-refl id-left)) ⟩
      tuple {n} (λ j → cotuple {n} (λ i → π {n} i ∘ ι {n} j))
    ≈⟨ tuple-cong {n} _ _ (λ j → cotuple-cong {n} _ _ (λ i → kronecker-sym i j)) ⟩
      tuple {n} (λ j → cotuple {n} (λ i → π {n} j ∘ ι {n} i))
    ≈⟨ tuple-cong {n} _ _ (λ j → cotuple-ext {n} (π {n} j)) ⟩
      tuple {n} (λ j → π {n} j)
    ≈⟨ ≈-sym (tuple-cong {n} _ _ (λ j → id-right)) ⟩
      tuple {n} (λ j → π {n} j ∘ id (X^ n))
    ≈⟨ tuple-ext {n} (id (X^ n)) ⟩
      id (X^ n)
    ∎ where open ≈-Reasoning isEquiv

  -- Category Mat where objects are ℕ, morphisms m → n are X^m ⇒ X^n.
  open import prop-setoid using (IsEquivalence)

  cat : Category _ _ _
  cat .Category.obj = ℕ
  cat .Category._⇒_ m n = X^ m ⇒ X^ n
  cat .Category._≈_ f g = f ≈ g
  cat .Category.isEquiv = isEquiv
  cat .Category.id n = id (X^ n)
  cat .Category._∘_ f g = f ∘ g
  cat .Category.∘-cong = ∘-cong
  cat .Category.id-left = id-left
  cat .Category.id-right = id-right
  cat .Category.assoc f g h = assoc f g h

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = 0
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal = to-terminal
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext = to-terminal-ext

  initial : HasInitial cat
  initial .HasInitial.witness = 0
  initial .HasInitial.is-initial .IsInitial.from-initial = from-initial
  initial .HasInitial.is-initial .IsInitial.from-initial-ext = from-initial-ext

  private
    split-π : ∀ {m n} → Fin m ⊎ Fin n → X^ (m +ℕ n) ⇒ X
    split-π {m} {n} (inj₁ i) = π {m +ℕ n} (i ↑ˡ n)
    split-π {m} {n} (inj₂ j) = π {m +ℕ n} (m ↑ʳ j)

    split-pair : ∀ {k m n} → X^ k ⇒ X^ m → X^ k ⇒ X^ n → Fin m ⊎ Fin n → X^ k ⇒ X
    split-pair {_} {m} f g (inj₁ i) = π {m} i ∘ f
    split-pair {_} {_} {n} f g (inj₂ j) = π {n} j ∘ g

    split-pair-≡ : ∀ {k m n} (f : X^ k ⇒ X^ m) (g : X^ k ⇒ X^ n)
                   {s₁ s₂ : Fin m ⊎ Fin n} → s₁ ≡ s₂ → split-pair {k} f g s₁ ≈ split-pair {k} f g s₂
    split-pair-≡ _ _ refl = ≈-refl

    split-pair-cong : ∀ {k m n} {f₁ f₂ : X^ k ⇒ X^ m} {g₁ g₂ : X^ k ⇒ X^ n}
                      → f₁ ≈ f₂ → g₁ ≈ g₂ → ∀ s → split-pair {k} {m} {n} f₁ g₁ s ≈ split-pair {k} {m} {n} f₂ g₂ s
    split-pair-cong f≈ g≈ (inj₁ i) = ∘-cong ≈-refl f≈
    split-pair-cong f≈ g≈ (inj₂ j) = ∘-cong ≈-refl g≈

  products : HasProducts cat
  products .HasProducts.prod m n = m +ℕ n
  products .HasProducts.p₁ {m} {n} = tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n))
  products .HasProducts.p₂ {m} {n} = tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j))
  products .HasProducts.pair {k} {m} {n} f g = tuple {m +ℕ n} (λ i → split-pair {k} {m} {n} f g (splitAt m i))
  products .HasProducts.pair-cong {_} {m} {n} f≈ g≈ =
    tuple-cong {m +ℕ n} _ _ (λ i → split-pair-cong f≈ g≈ (splitAt m i))
  products .HasProducts.pair-p₁ {k} {m} {n} f g =
    begin
      tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) ∘ tuple {m +ℕ n} col
    ≈⟨ tuple-natural {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) (tuple {m +ℕ n} col) ⟩
      tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n) ∘ tuple {m +ℕ n} col)
    ≈⟨ tuple-cong {m}
        (λ i → π {m +ℕ n} (i ↑ˡ n) ∘ tuple {m +ℕ n} col)
        (λ i → π {m} i ∘ f)
        (λ i → ≈-trans (tuple-π {m +ℕ n} col (i ↑ˡ n)) (split-pair-≡ {k} f g (splitAt-↑ˡ m i n))) ⟩
      tuple {m} (λ i → π {m} i ∘ f)
    ≈⟨ tuple-ext {m} f ⟩
      f
    ∎ where
        open ≈-Reasoning isEquiv
        col = λ i → split-pair {k} {m} {n} f g (splitAt m i)
  products .HasProducts.pair-p₂ {k} {m} {n} f g =
    begin
      tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j)) ∘ tuple {m +ℕ n} col
    ≈⟨ tuple-natural {n} (λ j → π {m +ℕ n} (m ↑ʳ j)) (tuple {m +ℕ n} col) ⟩
      tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j) ∘ tuple {m +ℕ n} col)
    ≈⟨ tuple-cong {n}
        (λ j → π {m +ℕ n} (m ↑ʳ j) ∘ tuple {m +ℕ n} col)
        (λ j → π {n} j ∘ g)
        (λ j → ≈-trans (tuple-π {m +ℕ n} col (m ↑ʳ j)) (split-pair-≡ {k} f g (splitAt-↑ʳ m n j))) ⟩
      tuple {n} (λ j → π {n} j ∘ g)
    ≈⟨ tuple-ext {n} g ⟩
      g
    ∎ where
        open ≈-Reasoning isEquiv
        col = λ i → split-pair {k} {m} {n} f g (splitAt m i)
  products .HasProducts.pair-ext = {!!}
