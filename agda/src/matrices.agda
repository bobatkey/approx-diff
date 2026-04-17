{-# OPTIONS --postfix-projections --prop --safe #-}

-- Matrix representation via iterated biproducts in a (necessarily CMon-enriched) category with binary
-- biproducts and zero object, and base object X. Instantiating X to Two in SemiLat recovers the "Boolean
-- Jacobian" setting FDVect_2.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

module matrices
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  where

  open Category 𝒞
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
