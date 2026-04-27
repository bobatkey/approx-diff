{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; module ≈-Reasoning) renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category; IsInitial; IsTerminal; HasProducts)
open import setoid-cat using (SetoidCat)
open import cmon-enriched using (CMonEnriched; Biproduct; biproducts→products)
open import commutative-monoid using (CommutativeMonoid; _=[_]>_)
open import commutative-semiring using (CommutativeSemiring)
open import functor using (Functor)

-- Suppose 𝒞 a biproduct category with a chosen object X whose endomorphism hom 𝒞(X, X) is a commutative
-- semiring (with composition as multiplication and addition of morphisms as addition), semiring-isomorphic
-- to a given commutative semiring S. Then MatRep(𝒞, X) is the full subcategory of 𝒞 whose objects are
-- iterated biproducts X^n, and is equivalent to Mat(S), with 𝒞(X, X) representing the scalars.
module matrix-embedding
  {o m e} {𝒞 : Category o m e}
  (CM : CMonEnriched 𝒞)
  (BP : ∀ x y → Biproduct CM x y)
  (𝟘 : Category.obj 𝒞)
  (𝟘-initial : IsInitial 𝒞 𝟘)
  (𝟘-terminal : IsTerminal 𝒞 𝟘)
  (X : Category.obj 𝒞)
  (A : Setoid m e) (S : CommutativeSemiring A)
  (let open Category 𝒞)
  (let open CMonEnriched CM)
  (let module CS = CommutativeSemiring S)
  (let open CS using () renaming (_+_ to _+ₛ_; _·_ to _·ₛ_))
  (scalar-iso : Category.Iso (SetoidCat m e) A (hom-setoid X X))
  (let open _⇒s_)
  (let open Category.Iso)
  (let scalar = scalar-iso .fwd)
  (scalar-cmon : CS.additive =[ scalar-iso .fwd ]> homCM X X)
  (scalar-ι : scalar .func CS.ι ≈ id X)
  (scalar-· : ∀ {a b} → scalar .func (a ·ₛ b) ≈ scalar .func a ∘ scalar .func b)
  where

  open _⇒s_
  open _≈s_
  open _=[_]>_
  open Category.Iso

  open CommutativeMonoid
  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  scalar⁻¹ = scalar-iso .bwd
  scalar∘scalar⁻¹≈id = scalar-iso .fwd∘bwd≈id
  scalar⁻¹∘scalar≈id = scalar-iso .bwd∘fwd≈id

  import matrix
  module Mat = matrix.Mat S
  open Mat using (Matrix) public

  module _ where
    open Biproduct

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

    -- scalar preserves dot products.
    scalar-Σ : ∀ {n} (f g : Fin n → CS.Carrier) →
              scalar .func (Mat.Σ (λ k → f k ·ₛ g k)) ≈ (cotuple {n} (λ k → scalar .func (f k)) ∘ tuple {n} (λ k → scalar .func (g k)))
    scalar-Σ {zero} f g =
      begin
        scalar .func CS.ε
      ≈⟨ scalar-cmon .preserve-ε ⟩
        εm
      ≈˘⟨ comp-bilinear-ε₁ to-terminal ⟩
        εm ∘ to-terminal
      ≈˘⟨ ∘-cong (from-initial-ext εm) ≈-refl ⟩
        from-initial ∘ to-terminal
      ∎ where open ≈-Reasoning isEquiv
    scalar-Σ {suc n} f g =
      begin
        scalar .func ((f zero ·ₛ g zero) +ₛ Mat.Σ (λ k → f (suc k) ·ₛ g (suc k)))
      ≈⟨ scalar-cmon .preserve-+ ⟩
        scalar .func (f zero ·ₛ g zero) +m scalar .func (Mat.Σ (λ k → f (suc k) ·ₛ g (suc k)))
      ≈⟨ homCM _ _ .+-cong scalar-· (scalar-Σ (λ k → f (suc k)) (λ k → g (suc k))) ⟩
        (scalar .func (f zero) ∘ scalar .func (g zero))
        +m
        (cotuple {n} (λ k → scalar .func (f (suc k))) ∘ tuple {n} (λ k → scalar .func (g (suc k))))
      ≈˘⟨ homCM _ _ .+-cong
            (∘-cong ≈-refl (pair-p₁ (BP X (X^ n)) _ _))
            (∘-cong ≈-refl (pair-p₂ (BP X (X^ n)) _ _)) ⟩
        (scalar .func (f zero) ∘
         (p₁ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k))))))
        +m
        (cotuple {n} (λ k → scalar .func (f (suc k))) ∘
         (p₂ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k))))))
      ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
        ((scalar .func (f zero) ∘ p₁ (BP X (X^ n))) ∘
         pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k)))))
        +m
        ((cotuple {n} (λ k → scalar .func (f (suc k))) ∘ p₂ (BP X (X^ n))) ∘
         pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k)))))
      ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
        copair (BP X (X^ n)) (scalar .func (f zero)) (cotuple {n} (λ k → scalar .func (f (suc k)))) ∘
        pair (BP X (X^ n)) (scalar .func (g zero)) (tuple {n} (λ k → scalar .func (g (suc k))))
      ∎ where open ≈-Reasoning isEquiv

    -- scalar applied to the Kronecker delta e matches projection-injection.
    scalar-e : ∀ {n} (i j : Fin n) → scalar .func (Mat.e i j) ≈ (π {n} i ∘ ι {n} j)
    scalar-e {suc n} zero zero =
      begin
        scalar .func CS.ι ≈⟨ scalar-ι ⟩ id X
      ≈˘⟨ id-1 (BP X (X^ n)) ⟩
        p₁ (BP X (X^ n)) ∘ in₁ (BP X (X^ n))
      ∎ where open ≈-Reasoning isEquiv
    scalar-e {suc n} zero (suc j) =
      begin
        scalar .func CS.ε
      ≈⟨ scalar-cmon .preserve-ε ⟩
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
        scalar .func CS.ε
      ≈⟨ scalar-cmon .preserve-ε ⟩
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
        scalar .func (Mat.e i j)
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

  -- Category MatRep(𝒞, X).
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

  open Functor

  F-fmor : ∀ {m n} → Matrix n m → X^ m ⇒ X^ n
  F-fmor {m} {n} M = tuple {n} (λ i → cotuple {m} (λ j → scalar .func (M i j)))

  -- Entry-wise characterisation of F's action on morphisms.
  entry-F : ∀ {m n} (M : Matrix n m) (i : Fin n) (j : Fin m) → entry (F-fmor M) i j ≈ scalar .func (M i j)
  entry-F {m} {n} M i j =
    begin
      π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar .func (M i' j'))) ∘ ι {m} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar .func (M i' j')))) ∘ ι {m} j
    ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
      cotuple {m} (λ j' → scalar .func (M i j')) ∘ ι {m} j
    ≈⟨ cotuple-ι {m} _ j ⟩
      scalar .func (M i j)
    ∎ where open ≈-Reasoning isEquiv

  -- F : Mat(S) → MatRep(𝒞, X), the "assemble matrix from entries" direction.
  F : Functor Mat.cat cat
  F .fobj n = n
  F .fmor = F-fmor
  F .fmor-cong p = tuple-cong _ _ (λ i → cotuple-cong _ _ (λ j → scalar-iso .fwd .func-resp-≈ (p i j)))
  F .fmor-id {n} = entry-ext (λ i j →
    begin
      π {n} i ∘ (tuple {n} (λ i' → cotuple {n} (λ j' → scalar .func (Mat.I i' j'))) ∘ ι {n} j)
    ≈˘⟨ assoc _ _ _ ⟩
      (π {n} i ∘ tuple {n} (λ i' → cotuple {n} (λ j' → scalar .func (Mat.I i' j')))) ∘ ι {n} j
    ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
      cotuple {n} (λ j' → scalar .func (Mat.I i j')) ∘ ι {n} j
    ≈⟨ cotuple-ι {n} _ j ⟩
      scalar .func (Mat.I i j)
    ≈⟨ scalar-e i j ⟩
      π {n} i ∘ ι {n} j
    ≈˘⟨ ∘-cong ≈-refl id-left ⟩
      π {n} i ∘ (id (X^ n) ∘ ι {n} j)
    ∎) where open ≈-Reasoning isEquiv
  F .fmor-comp {m} {n} {k} M N = entry-ext (λ i j →
    begin
      entry (F .fmor (M Mat.∘ N)) i j
    ≈⟨ entry-F (M Mat.∘ N) i j ⟩
      scalar .func (Mat.Σ (λ l → M i l ·ₛ N l j))
    ≈⟨ scalar-Σ (λ l → M i l) (λ l → N l j) ⟩
      cotuple {n} (λ l → scalar .func (M i l)) ∘ tuple {n} (λ l → scalar .func (N l j))
    ≈˘⟨ ∘-cong (cotuple-cong {n} _ _ (λ l → entry-F M i l)) (tuple-cong {n} _ _ (λ l → entry-F N l j)) ⟩
      cotuple {n} (λ l → entry (F .fmor M) i l) ∘ tuple {n} (λ l → entry (F .fmor N) l j)
    ≈˘⟨ entry-comp {m} {n} {k} (F .fmor N) (F .fmor M) i j ⟩
      π {k} i ∘ ((F .fmor M ∘ F .fmor N) ∘ ι {m} j)
    ∎) where open ≈-Reasoning isEquiv

  -- F⁻¹ : MatRep(𝒞, X) → Mat(S), the "extract matrix of entries" direction.
  F⁻¹ : Functor cat Mat.cat
  F⁻¹ .fobj n = n
  F⁻¹ .fmor {m} {n} f i j = scalar⁻¹ .func (entry {m} {n} f i j)
  F⁻¹ .fmor-cong p i j = scalar⁻¹ .func-resp-≈ (∘-cong ≈-refl (∘-cong p ≈-refl))
  F⁻¹ .fmor-id {n} i j =
    begin
      scalar⁻¹ .func (entry {n} {n} (id (X^ n)) i j)
    ≈⟨ scalar⁻¹ .func-resp-≈ (∘-cong ≈-refl id-left) ⟩
      scalar⁻¹ .func (π {n} i ∘ ι {n} j)
    ≈˘⟨ scalar⁻¹ .func-resp-≈ (scalar-e i j) ⟩
      scalar⁻¹ .func (scalar .func (Mat.e i j))
    ≈⟨ scalar⁻¹∘scalar≈id .func-eq (Setoid.refl A) ⟩
      Mat.e i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)
  F⁻¹ .fmor-comp {m} {n} {k} g f i j =
    begin
      scalar⁻¹ .func (entry {m} {k} (g ∘ f) i j)
    ≈⟨ scalar⁻¹ .func-resp-≈ (entry-comp {m} {n} {k} f g i j) ⟩
      scalar⁻¹ .func (cotuple {n} (λ l → entry {n} {k} g i l) ∘ tuple {n} (λ l → entry {m} {n} f l j))
    ≈˘⟨ scalar⁻¹ .func-resp-≈ (∘-cong (cotuple-cong {n} _ _ (λ l → scalar∘scalar⁻¹≈id .func-eq ≈-refl))
                                 (tuple-cong {n} _ _ (λ l → scalar∘scalar⁻¹≈id .func-eq ≈-refl))) ⟩
      scalar⁻¹ .func (cotuple {n} (λ l → scalar .func (scalar⁻¹ .func (entry {n} {k} g i l)))
                  ∘ tuple {n} (λ l → scalar .func (scalar⁻¹ .func (entry {m} {n} f l j))))
    ≈˘⟨ scalar⁻¹ .func-resp-≈
          (scalar-Σ {n} (λ l → scalar⁻¹ .func (entry {n} {k} g i l)) (λ l → scalar⁻¹ .func (entry {m} {n} f l j))) ⟩
      scalar⁻¹ .func
        (scalar .func (Mat.Σ {n} (λ l → scalar⁻¹ .func (entry {n} {k} g i l) ·ₛ scalar⁻¹ .func (entry {m} {n} f l j))))
    ≈⟨ scalar⁻¹∘scalar≈id .func-eq (Setoid.refl A) ⟩
      Mat.Σ {n} (λ l → scalar⁻¹ .func (entry {n} {k} g i l) ·ₛ scalar⁻¹ .func (entry {m} {n} f l j))
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  F⁻¹∘F : ∀ {m n} (M : Matrix n m) → (F⁻¹ .fmor (F .fmor M)) Mat.≈ₘ M
  F⁻¹∘F {m} {n} M i j =
    begin
      scalar⁻¹ .func (entry {m} {n} (F .fmor {m} {n} M) i j)
    ≈⟨ scalar⁻¹ .func-resp-≈ (entry-F {m} {n} M i j) ⟩
      scalar⁻¹ .func (scalar .func (M i j))
    ≈⟨ scalar⁻¹∘scalar≈id .func-eq (Setoid.refl A) ⟩
      M i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  F∘F⁻¹ : ∀ {m n} (f : X^ m ⇒ X^ n) → F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f) ≈ f
  F∘F⁻¹ {m} {n} f = entry-ext {m} {n} (λ i j →
    begin
      entry {m} {n} (F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f)) i j
    ≈⟨ entry-F {m} {n} (F⁻¹ .fmor {m} {n} f) i j ⟩
      scalar .func (scalar⁻¹ .func (entry {m} {n} f i j))
    ≈⟨ scalar∘scalar⁻¹≈id .func-eq ≈-refl ⟩
      entry {m} {n} f i j
    ∎) where open ≈-Reasoning isEquiv

  F-εₘ : ∀ {m n} → F .fmor (Mat.εₘ {m} {n}) ≈ εm {X^ n} {X^ m}
  F-εₘ {m} {n} = entry-ext {n} {m} (λ i j →
    begin
      entry {n} {m} (F .fmor {n} {m} (Mat.εₘ {m} {n})) i j
    ≈⟨ entry-F {n} {m} (Mat.εₘ {m} {n}) i j ⟩
      scalar .func CS.ε
    ≈⟨ scalar-cmon .preserve-ε ⟩
      εm
    ≈˘⟨ comp-bilinear-ε₂ (π {m} i) ⟩
      π {m} i ∘ εm
    ≈˘⟨ ∘-cong ≈-refl (comp-bilinear-ε₁ (ι {n} j)) ⟩
      π {m} i ∘ (εm ∘ ι {n} j)
    ∎) where open ≈-Reasoning isEquiv

  F-+ₘ : ∀ {m n} (M N : Matrix n m) → F .fmor {m} {n} (M Mat.+ₘ N) ≈ (F .fmor {m} {n} M +m F .fmor {m} {n} N)
  F-+ₘ {m} {n} M N = entry-ext {m} {n} (λ i j →
    begin
      entry {m} {n} (F .fmor {m} {n} (M Mat.+ₘ N)) i j
    ≈⟨ entry-F {m} {n} (M Mat.+ₘ N) i j ⟩
      scalar .func (M i j +ₛ N i j)
    ≈⟨ scalar-cmon .preserve-+ ⟩
      scalar .func (M i j) +m scalar .func (N i j)
    ≈˘⟨ homCM _ _ .+-cong (entry-F {m} {n} M i j) (entry-F {m} {n} N i j) ⟩
      (π {n} i ∘ (F .fmor {m} {n} M ∘ ι {m} j)) +m (π {n} i ∘ (F .fmor {m} {n} N ∘ ι {m} j))
    ≈˘⟨ comp-bilinear₂ _ _ _ ⟩
      π {n} i ∘ ((F .fmor {m} {n} M ∘ ι {m} j) +m (F .fmor {m} {n} N ∘ ι {m} j))
    ≈˘⟨ ∘-cong ≈-refl (comp-bilinear₁ _ _ _) ⟩
      π {n} i ∘ ((F .fmor {m} {n} M +m F .fmor {m} {n} N) ∘ ι {m} j)
    ∎) where open ≈-Reasoning isEquiv

  -- Morphisms in Mat(S) are determined by their F-images.
  F-faithful : ∀ {m n} {M N : Matrix n m} → F .fmor {m} {n} M ≈ F .fmor {m} {n} N → M Mat.≈ₘ N
  F-faithful {m} {n} {M} {N} eq i j =
    begin
      M i j
    ≈˘⟨ F⁻¹∘F {m} {n} M i j ⟩
      scalar⁻¹ .func (entry {m} {n} (F .fmor {m} {n} M) i j)
    ≈⟨ scalar⁻¹ .func-resp-≈ (∘-cong ≈-refl (∘-cong eq ≈-refl)) ⟩
      scalar⁻¹ .func (entry {m} {n} (F .fmor {m} {n} N) i j)
    ≈⟨ F⁻¹∘F {m} {n} N i j ⟩
      N i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  F⁻¹-εₘ : ∀ {m n} → (F⁻¹ .fmor {m} {n} (εm {X^ m} {X^ n})) Mat.≈ₘ (Mat.εₘ {n} {m})
  F⁻¹-εₘ {m} {n} = F-faithful {m} {n}
    {F⁻¹ .fmor {m} {n} (εm {X^ m} {X^ n})}
    {Mat.εₘ {n} {m}}
    (begin
      F .fmor {m} {n} (F⁻¹ .fmor {m} {n} (εm {X^ m} {X^ n}))
    ≈⟨ F∘F⁻¹ {m} {n} (εm {X^ m} {X^ n}) ⟩
      εm
    ≈˘⟨ F-εₘ {n} {m} ⟩
      F .fmor {m} {n} (Mat.εₘ {n} {m})
    ∎) where open ≈-Reasoning isEquiv

  F⁻¹-+ₘ : ∀ {m n} (f g : X^ m ⇒ X^ n) →
           F⁻¹ .fmor {m} {n} (f +m g) Mat.≈ₘ (F⁻¹ .fmor {m} {n} f Mat.+ₘ F⁻¹ .fmor {m} {n} g)
  F⁻¹-+ₘ {m} {n} f g = F-faithful {m} {n}
    {F⁻¹ .fmor {m} {n} (f +m g)}
    {F⁻¹ .fmor {m} {n} f Mat.+ₘ F⁻¹ .fmor {m} {n} g}
    (begin
      F .fmor {m} {n} (F⁻¹ .fmor {m} {n} (f +m g))
    ≈⟨ F∘F⁻¹ {m} {n} (f +m g) ⟩
      f +m g
    ≈˘⟨ homCM _ _ .+-cong (F∘F⁻¹ {m} {n} f) (F∘F⁻¹ {m} {n} g) ⟩
      F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f) +m F .fmor {m} {n} (F⁻¹ .fmor {m} {n} g)
    ≈˘⟨ F-+ₘ (F⁻¹ .fmor {m} {n} f) (F⁻¹ .fmor {m} {n} g) ⟩
      F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f Mat.+ₘ F⁻¹ .fmor {m} {n} g)
    ∎) where open ≈-Reasoning isEquiv

  -- FIXME: derive biproducts instead and have clients use biproducts→products.
  open import Data.Nat using () renaming (_+_ to _+ℕ_)

  module _ where
    private
      module MP = HasProducts (biproducts→products Mat.cmon Mat.biproduct)

    prod : ℕ → ℕ → ℕ
    prod m n = m +ℕ n

    p₁ : ∀ {m n} → X^ (m +ℕ n) ⇒ X^ m
    p₁ {m} {n} = F .fmor (MP.p₁ {m} {n})

    p₂ : ∀ {m n} → X^ (m +ℕ n) ⇒ X^ n
    p₂ {m} {n} = F .fmor (MP.p₂ {m} {n})

    pair : ∀ {k m n} → X^ k ⇒ X^ m → X^ k ⇒ X^ n → X^ k ⇒ X^ (m +ℕ n)
    pair {k} {m} {n} f g = F .fmor (MP.pair {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g))

    pair-cong : ∀ {k m n} {f₁ f₂ : X^ k ⇒ X^ m} {g₁ g₂ : X^ k ⇒ X^ n} →
                f₁ ≈ f₂ → g₁ ≈ g₂ → pair {k} {m} {n} f₁ g₁ ≈ pair {k} {m} {n} f₂ g₂
    pair-cong {k} {m} {n} f≈ g≈ =
      F .fmor-cong (MP.pair-cong {k} {m} {n} (F⁻¹ .fmor-cong f≈) (F⁻¹ .fmor-cong g≈))

    pair-p₁ : ∀ {k m n} (f : X^ k ⇒ X^ m) (g : X^ k ⇒ X^ n) → (p₁ {m} {n} ∘ pair {k} {m} {n} f g) ≈ f
    pair-p₁ {k} {m} {n} f g =
      begin
        p₁ {m} {n} ∘ pair {k} {m} {n} f g
      ≈˘⟨ F .fmor-comp {k} {m +ℕ n} {m} (MP.p₁ {m} {n}) (MP.pair {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g)) ⟩
        F .fmor {k} {m} (MP.p₁ {m} {n} Mat.∘ MP.pair {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g))
      ≈⟨ F .fmor-cong {k} {m} (MP.pair-p₁ {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g)) ⟩
        F .fmor {k} {m} (F⁻¹ .fmor f)
      ≈⟨ F∘F⁻¹ {k} {m} f ⟩
        f
      ∎ where open ≈-Reasoning isEquiv

    pair-p₂ : ∀ {k m n} (f : X^ k ⇒ X^ m) (g : X^ k ⇒ X^ n) → (p₂ {m} {n} ∘ pair {k} {m} {n} f g) ≈ g
    pair-p₂ {k} {m} {n} f g =
      begin
        p₂ {m} {n} ∘ pair {k} {m} {n} f g
      ≈˘⟨ F .fmor-comp {k} {m +ℕ n} {n} (MP.p₂ {m} {n}) (MP.pair {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g)) ⟩
        F .fmor {k} {n} (MP.p₂ {m} {n} Mat.∘ MP.pair {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g))
      ≈⟨ F .fmor-cong {k} {n} (MP.pair-p₂ {k} {m} {n} (F⁻¹ .fmor f) (F⁻¹ .fmor g)) ⟩
        F .fmor {k} {n} (F⁻¹ .fmor g)
      ≈⟨ F∘F⁻¹ {k} {n} g ⟩
        g
      ∎ where open ≈-Reasoning isEquiv

    pair-ext : ∀ {k m n} (f : X^ k ⇒ X^ (m +ℕ n)) → pair {k} {m} {n} (p₁ {m} {n} ∘ f) (p₂ {m} {n} ∘ f) ≈ f
    pair-ext {k} {m} {n} f =
      begin
        pair {k} {m} {n} (p₁ {m} {n} ∘ f) (p₂ {m} {n} ∘ f)
      ≈⟨ F .fmor-cong {k} {m +ℕ n} mat-eq ⟩
        F .fmor {k} {m +ℕ n} (F⁻¹ .fmor f)
      ≈⟨ F∘F⁻¹ {k} {m +ℕ n} f ⟩
        f
      ∎ where
        mat-eq : MP.pair {k} {m} {n} (F⁻¹ .fmor (p₁ {m} {n} ∘ f)) (F⁻¹ .fmor (p₂ {m} {n} ∘ f)) Mat.≈ₘ F⁻¹ .fmor f
        mat-eq =
          begin
            MP.pair {k} {m} {n} (F⁻¹ .fmor (p₁ {m} {n} ∘ f)) (F⁻¹ .fmor (p₂ {m} {n} ∘ f))
          ≈⟨ MP.pair-cong {k} {m} {n}
               (F⁻¹ .fmor-comp {k} {m +ℕ n} {m} (F .fmor (MP.p₁ {m} {n})) f)
               (F⁻¹ .fmor-comp {k} {m +ℕ n} {n} (F .fmor (MP.p₂ {m} {n})) f) ⟩
            MP.pair {k} {m} {n}
              (Mat._∘_ {m} {m +ℕ n} {k} (F⁻¹ .fmor (F .fmor (MP.p₁ {m} {n}))) (F⁻¹ .fmor f))
              (Mat._∘_ {n} {m +ℕ n} {k} (F⁻¹ .fmor (F .fmor (MP.p₂ {m} {n}))) (F⁻¹ .fmor f))
          ≈⟨ MP.pair-cong {k} {m} {n}
               (Mat.∘-cong {m} {m +ℕ n} {k} (F⁻¹∘F (MP.p₁ {m} {n})) (λ i j → Mat.refl {F⁻¹ .fmor f i j}))
               (Mat.∘-cong {n} {m +ℕ n} {k} (F⁻¹∘F (MP.p₂ {m} {n})) (λ i j → Mat.refl {F⁻¹ .fmor f i j})) ⟩
            MP.pair {k} {m} {n} (MP.p₁ {m} {n} Mat.∘ F⁻¹ .fmor f) (MP.p₂ {m} {n} Mat.∘ F⁻¹ .fmor f)
          ≈⟨ MP.pair-ext {k} {m} {n} (F⁻¹ .fmor f) ⟩
            F⁻¹ .fmor f
          ∎ where open ≈-Reasoning Mat.≈ₘ-isEquiv
        open ≈-Reasoning isEquiv

    products : HasProducts cat
    products .HasProducts.prod = prod
    products .HasProducts.p₁ {x} {y} = p₁ {x} {y}
    products .HasProducts.p₂ {x} {y} = p₂ {x} {y}
    products .HasProducts.pair {x} {y} {z} = pair {x} {y} {z}
    products .HasProducts.pair-cong {x} {y} {z} = pair-cong {x} {y} {z}
    products .HasProducts.pair-p₁ {x} {y} {z} = pair-p₁ {x} {y} {z}
    products .HasProducts.pair-p₂ {x} {y} {z} = pair-p₂ {x} {y} {z}
    products .HasProducts.pair-ext {x} {y} {z} = pair-ext {x} {y} {z}

  -- Inclusion of MatRep(𝒞, X) into 𝒞: identity on morphisms, sending object n to X^n.
  𝓕 : Functor cat 𝒞
  𝓕 .fobj = X^
  𝓕 .fmor f = f
  𝓕 .fmor-cong f≈ = f≈
  𝓕 .fmor-id = ≈-refl
  𝓕 .fmor-comp _ _ = ≈-refl
