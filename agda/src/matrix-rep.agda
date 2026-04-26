{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin using (join)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; IsInitial; IsTerminal; HasInitial; HasTerminal; HasProducts)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid)

-- Suppose 𝒞 a biproduct category with a chosen object X whose endomorphism hom 𝒞(X, X) is a commutative
-- semiring (with composition as multiplication and addition of morphisms as addition). Then MatRep(𝒞, X) is
-- the full subcategory of 𝒞 whose objects are iterated biproducts X^n, and is equivalent to Mat(S), with
-- 𝒞(X, X) representing the scalars. Instantiating X to TWO in SemiLat recovers the "Boolean Jacobian"
-- setting Mat(Bool).
module matrix-rep
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

  tuple-ext0 : ∀ {n} → tuple {n} (λ i → π {n} i) ≈ id (X^ n)
  tuple-ext0 {n} = ≈-trans (≈-sym (tuple-cong {n} _ _ (λ i → id-right))) (tuple-ext {n} (id (X^ n)))

  bp-pair-ext0 : ∀ {x y} (bp : Biproduct CM x y) → pair bp (p₁ bp) (p₂ bp) ≈ id (prod bp)
  bp-pair-ext0 bp = ≈-trans (≈-sym (pair-cong bp id-right id-right)) (pair-ext bp (id _))

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


  -- MatRep(𝒞, X) as an Agda Category: objects are ℕ, morphisms m → n are X^m ⇒ X^n.
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
        (λ i → ≈-trans (tuple-π {m +ℕ n} col (i ↑ˡ n)) (≡-to-≈ (cong (split-pair {k} {m} {n} f g) (splitAt-↑ˡ m i n)))) ⟩
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
        (λ j → ≈-trans (tuple-π {m +ℕ n} col (m ↑ʳ j)) (≡-to-≈ (cong (split-pair {k} {m} {n} f g) (splitAt-↑ʳ m n j)))) ⟩
      tuple {n} (λ j → π {n} j ∘ g)
    ≈⟨ tuple-ext {n} g ⟩
      g
    ∎ where
        open ≈-Reasoning isEquiv
        col = λ i → split-pair {k} {m} {n} f g (splitAt m i)
  products .HasProducts.pair-ext {k} {m} {n} f =
    begin
      tuple {m +ℕ n} col
    ≈⟨ tuple-cong {m +ℕ n} col (λ i → π {m +ℕ n} i ∘ f)
        (λ i → ≈-trans (col-ext (splitAt m i)) (≡-to-≈ (cong (λ j → π {m +ℕ n} j ∘ f) (join-splitAt m n i)))) ⟩
      tuple {m +ℕ n} (λ i → π {m +ℕ n} i ∘ f)
    ≈⟨ tuple-ext {m +ℕ n} f ⟩
      f
    ∎ where
        p₁' = tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n))
        p₂' = tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j))
        col = λ i → split-pair {k} {m} {n} (p₁' ∘ f) (p₂' ∘ f) (splitAt m i)

        col-ext : ∀ (s : Fin m ⊎ Fin n) → split-pair {k} {m} {n} (p₁' ∘ f) (p₂' ∘ f) s ≈ (π {m +ℕ n} (join m n s) ∘ f)
        col-ext (inj₁ j) =
          begin
            π {m} j ∘ (p₁' ∘ f)
          ≈˘⟨ assoc (π {m} j) p₁' f ⟩
            (π {m} j ∘ p₁') ∘ f
          ≈⟨ ∘-cong (tuple-π {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) j) ≈-refl ⟩
            π {m +ℕ n} (j ↑ˡ n) ∘ f
          ∎ where open ≈-Reasoning isEquiv
        col-ext (inj₂ j) =
          begin
            π {n} j ∘ (p₂' ∘ f)
          ≈˘⟨ assoc (π {n} j) p₂' f ⟩
            (π {n} j ∘ p₂') ∘ f
          ≈⟨ ∘-cong (tuple-π {n} (λ i → π {m +ℕ n} (m ↑ʳ i)) j) ≈-refl ⟩
            π {m +ℕ n} (m ↑ʳ j) ∘ f
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv

  module _ (m n : ℕ) where
    private
      bwd-col : Fin m ⊎ Fin n → (X^ m ⊕ X^ n) ⇒ X
      bwd-col (inj₁ j) = π {m} j ∘ p₁ (BP (X^ m) (X^ n))
      bwd-col (inj₂ j) = π {n} j ∘ p₂ (BP (X^ m) (X^ n))

      split-fwd : X^ (m +ℕ n) ⇒ (X^ m ⊕ X^ n)
      split-fwd = pair (BP (X^ m) (X^ n))
        (tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n)))
        (tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j)))

    X^-split : Iso (X^ (m +ℕ n)) (X^ m ⊕ X^ n)
    X^-split .Iso.fwd = split-fwd
    X^-split .Iso.bwd = tuple {m +ℕ n} (λ i → bwd-col (splitAt m i))
    X^-split .Iso.fwd∘bwd≈id =
      ≈-trans (≈-sym (pair-ext (BP (X^ m) (X^ n)) (split-fwd ∘ bwd)))
      (≈-trans (pair-cong (BP (X^ m) (X^ n)) p₁-preserved p₂-preserved)
      (bp-pair-ext0 (BP (X^ m) (X^ n))))
      where
        bwd = tuple {m +ℕ n} (λ i → bwd-col (splitAt m i))

        p₁-preserved : (p₁ (BP (X^ m) (X^ n)) ∘ (split-fwd ∘ bwd)) ≈ p₁ (BP (X^ m) (X^ n))
        p₁-preserved =
          begin
            p₁ (BP (X^ m) (X^ n)) ∘ (split-fwd ∘ bwd)
          ≈˘⟨ assoc (p₁ (BP (X^ m) (X^ n))) split-fwd bwd ⟩
            (p₁ (BP (X^ m) (X^ n)) ∘ split-fwd) ∘ bwd
          ≈⟨ ∘-cong (pair-p₁ (BP (X^ m) (X^ n)) _ _) ≈-refl ⟩
            tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) ∘ bwd
          ≈⟨ tuple-natural {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) bwd ⟩
            tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n) ∘ bwd)
          ≈⟨ tuple-cong {m} _ _ (λ i → tuple-π {m +ℕ n} (λ j → bwd-col (splitAt m j)) (i ↑ˡ n)) ⟩
            tuple {m} (λ i → bwd-col (splitAt m (i ↑ˡ n)))
          ≈⟨ tuple-cong {m} _ _ (λ i → ≡-to-≈ (cong bwd-col (splitAt-↑ˡ m i n))) ⟩
            tuple {m} (λ i → π {m} i ∘ p₁ (BP (X^ m) (X^ n)))
          ≈⟨ tuple-ext {m} (p₁ (BP (X^ m) (X^ n))) ⟩
            p₁ (BP (X^ m) (X^ n))
          ∎ where open ≈-Reasoning isEquiv

        p₂-preserved : (p₂ (BP (X^ m) (X^ n)) ∘ (split-fwd ∘ bwd)) ≈ p₂ (BP (X^ m) (X^ n))
        p₂-preserved =
          begin
            p₂ (BP (X^ m) (X^ n)) ∘ (split-fwd ∘ bwd)
          ≈˘⟨ assoc (p₂ (BP (X^ m) (X^ n))) split-fwd bwd ⟩
            (p₂ (BP (X^ m) (X^ n)) ∘ split-fwd) ∘ bwd
          ≈⟨ ∘-cong (pair-p₂ (BP (X^ m) (X^ n)) _ _) ≈-refl ⟩
            tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j)) ∘ bwd
          ≈⟨ tuple-natural {n} (λ j → π {m +ℕ n} (m ↑ʳ j)) bwd ⟩
            tuple {n} (λ j → π {m +ℕ n} (m ↑ʳ j) ∘ bwd)
          ≈⟨ tuple-cong {n} _ _ (λ j → tuple-π {m +ℕ n} (λ i → bwd-col (splitAt m i)) (m ↑ʳ j)) ⟩
            tuple {n} (λ j → bwd-col (splitAt m (m ↑ʳ j)))
          ≈⟨ tuple-cong {n} _ _ (λ j → ≡-to-≈ (cong bwd-col (splitAt-↑ʳ m n j))) ⟩
            tuple {n} (λ j → π {n} j ∘ p₂ (BP (X^ m) (X^ n)))
          ≈⟨ tuple-ext {n} (p₂ (BP (X^ m) (X^ n))) ⟩
            p₂ (BP (X^ m) (X^ n))
          ∎ where open ≈-Reasoning isEquiv
    X^-split .Iso.bwd∘fwd≈id =
      begin
        tuple {m +ℕ n} col ∘ split-fwd
      ≈⟨ tuple-natural {m +ℕ n} col split-fwd ⟩
        tuple {m +ℕ n} (λ i → col i ∘ split-fwd)
      ≈⟨ tuple-cong {m +ℕ n} _ _ (λ i → col-id (splitAt m i)) ⟩
        tuple {m +ℕ n} (λ i → π {m +ℕ n} (join m n (splitAt m i)))
      ≈⟨ tuple-cong {m +ℕ n} _ _ (λ i → ≡-to-≈ (cong (π {m +ℕ n}) (join-splitAt m n i))) ⟩
        tuple {m +ℕ n} (λ i → π {m +ℕ n} i)
      ≈⟨ tuple-ext0 {m +ℕ n} ⟩
        id (X^ (m +ℕ n))
      ∎
      where
        col = λ i → bwd-col (splitAt m i)

        col-id : ∀ (s : Fin m ⊎ Fin n) → (bwd-col s ∘ split-fwd) ≈ π {m +ℕ n} (join m n s)
        col-id (inj₁ j) =
          begin
            (π {m} j ∘ p₁ (BP (X^ m) (X^ n))) ∘ split-fwd
          ≈⟨ assoc (π {m} j) (p₁ (BP (X^ m) (X^ n))) split-fwd ⟩
            π {m} j ∘ (p₁ (BP (X^ m) (X^ n)) ∘ split-fwd)
          ≈⟨ ∘-cong ≈-refl (pair-p₁ (BP (X^ m) (X^ n)) _ _) ⟩
            π {m} j ∘ tuple {m} (λ i → π {m +ℕ n} (i ↑ˡ n))
          ≈⟨ tuple-π {m} (λ i → π {m +ℕ n} (i ↑ˡ n)) j ⟩
            π {m +ℕ n} (j ↑ˡ n)
          ∎ where open ≈-Reasoning isEquiv
        col-id (inj₂ j) =
          begin
            (π {n} j ∘ p₂ (BP (X^ m) (X^ n))) ∘ split-fwd
          ≈⟨ assoc (π {n} j) (p₂ (BP (X^ m) (X^ n))) split-fwd ⟩
            π {n} j ∘ (p₂ (BP (X^ m) (X^ n)) ∘ split-fwd)
          ≈⟨ ∘-cong ≈-refl (pair-p₂ (BP (X^ m) (X^ n)) _ _) ⟩
            π {n} j ∘ tuple {n} (λ i → π {m +ℕ n} (m ↑ʳ i))
          ≈⟨ tuple-π {n} (λ i → π {m +ℕ n} (m ↑ʳ i)) j ⟩
            π {m +ℕ n} (m ↑ʳ j)
          ∎ where open ≈-Reasoning isEquiv
        open ≈-Reasoning isEquiv


