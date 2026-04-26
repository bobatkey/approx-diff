{-# OPTIONS --postfix-projections --prop --safe #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import prop-setoid using (Setoid; module ≈-Reasoning) renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category; IsInitial; IsTerminal)
open import setoid-cat using (SetoidCat)
open import cmon-enriched using (CMonEnriched; Biproduct)
open import commutative-monoid using (CommutativeMonoid; _=[_]>_)
open import commutative-semiring using (CommutativeSemiring)
open import functor using (Functor)

-- CMon-enriched equivalence Mat(S) ≃ MatRep(𝒞, X), given an iso between the semiring S and End(X).
-- The representation of S inside End(X) is faithful on both sides: scalar is a homomorphism with an
-- inverse that is also a homomorphism (automatically, given scalar is bijective).
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
  (let open CommutativeSemiring S using (Carrier; additive) renaming (ε to S-ε; ι to S-ι; _+_ to _+ₛ_; _·_ to _·ₛ_; _≈_ to _≈ₛ_; ·-comm to ·ₛ-comm; trans to ≈ₛ-trans))
  (scalar-iso : Category.Iso (SetoidCat m e) A (hom-setoid X X))
  (let open _⇒s_)
  (let open Category.Iso)
  (let scalar = scalar-iso .fwd)
  (let scalar⁻¹ = scalar-iso .bwd)
  (scalar-cmon : additive =[ scalar-iso .fwd ]> homCM X X)
  (scalar-ι : scalar .func S-ι ≈ id X)
  (scalar-· : ∀ {a b} → scalar .func (a ·ₛ b) ≈ scalar .func a ∘ scalar .func b)
  where

  open _⇒s_
  open _≈s_
  open _=[_]>_
  open Category.Iso

  open CommutativeMonoid
  open Biproduct

  -- Composition in End(X) is commutative, derived from S commutativity via the iso.
  scalar-comm : ∀ (f g : X ⇒ X) → (f ∘ g) ≈ (g ∘ f)
  scalar-comm f g =
    begin
      f ∘ g
    ≈˘⟨ ∘-cong (scalar-iso .fwd∘bwd≈id .func-eq ≈-refl) (scalar-iso .fwd∘bwd≈id .func-eq ≈-refl) ⟩
      scalar .func (scalar-iso .bwd .func f) ∘ scalar .func (scalar-iso .bwd .func g)
    ≈˘⟨ scalar-· ⟩
      scalar .func (scalar-iso .bwd .func f ·ₛ scalar-iso .bwd .func g)
    ≈⟨ scalar-iso .fwd .func-resp-≈ ·ₛ-comm ⟩
      scalar .func (scalar-iso .bwd .func g ·ₛ scalar-iso .bwd .func f)
    ≈⟨ scalar-· ⟩
      scalar .func (scalar-iso .bwd .func g) ∘ scalar .func (scalar-iso .bwd .func f)
    ≈⟨ ∘-cong (scalar-iso .fwd∘bwd≈id .func-eq ≈-refl) (scalar-iso .fwd∘bwd≈id .func-eq ≈-refl) ⟩
      g ∘ f
    ∎ where open ≈-Reasoning isEquiv

  import matrix-rep
  module MatRep = matrix-rep CM BP 𝟘 𝟘-initial 𝟘-terminal X scalar-comm
  open MatRep hiding (cat) public

  open IsInitial 𝟘-initial
  open IsTerminal 𝟘-terminal

  import matrix
  private
    module Mat = matrix.Mat S
    open matrix.Mat S using (Matrix) public

  open Functor

  -- scalar preserves dot products.
  scalar-Σ : ∀ {n} (f g : Fin n → Carrier) →
    scalar .func (Mat.Σ (λ k → f k ·ₛ g k)) ≈ (cotuple {n} (λ k → scalar .func (f k)) ∘ tuple {n} (λ k → scalar .func (g k)))
  scalar-Σ {zero} f g =
    begin
      scalar .func S-ε
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
      (scalar .func (f zero) ∘ (p₁ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k))))))
      +m
      (cotuple {n} (λ k → scalar .func (f (suc k))) ∘ (p₂ (BP X (X^ n)) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k))))))
    ≈˘⟨ homCM _ _ .+-cong (assoc _ _ _) (assoc _ _ _) ⟩
      ((scalar .func (f zero) ∘ p₁ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k)))))
      +m
      ((cotuple {n} (λ k → scalar .func (f (suc k))) ∘ p₂ (BP X (X^ n))) ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple (λ k → scalar .func (g (suc k)))))
    ≈˘⟨ comp-bilinear₁ _ _ _ ⟩
      copair (BP X (X^ n)) (scalar .func (f zero)) (cotuple {n} (λ k → scalar .func (f (suc k))))
      ∘ pair (BP X (X^ n)) (scalar .func (g zero)) (tuple {n} (λ k → scalar .func (g (suc k))))
    ∎ where open ≈-Reasoning isEquiv

  -- scalar applied to the Kronecker delta e matches projection-injection.
  scalar-e : ∀ {n} (i j : Fin n) → scalar .func (Mat.e i j) ≈ (π {n} i ∘ ι {n} j)
  scalar-e {suc n} zero zero =
    begin
      scalar .func S-ι ≈⟨ scalar-ι ⟩ id X
    ≈˘⟨ id-1 (BP X (X^ n)) ⟩
      p₁ (BP X (X^ n)) ∘ in₁ (BP X (X^ n))
    ∎ where open ≈-Reasoning isEquiv
  scalar-e {suc n} zero (suc j) =
    begin
      scalar .func S-ε
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
      scalar .func S-ε
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

  -- F : Mat(S) → MatRep(𝒞, X), the "assemble matrix from entries" direction.
  F : Functor Mat.cat MatRep.cat
  F .fobj n = n
  F .fmor {m} {n} M = tuple {n} (λ i → cotuple {m} (λ j → scalar .func (M i j)))
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
  F .fmor-comp {x} {y} {z} M N = entry-ext (λ i j →
    begin
      entry (F .fmor (M Mat.∘ N)) i j
    ≈⟨ entry-F (M Mat.∘ N) i j ⟩
      scalar .func (Mat.Σ (λ k → M i k ·ₛ N k j))
    ≈⟨ scalar-Σ (λ k → M i k) (λ k → N k j) ⟩
      cotuple {y} (λ k → scalar .func (M i k)) ∘ tuple {y} (λ k → scalar .func (N k j))
    ≈˘⟨ ∘-cong (cotuple-cong {y} _ _ (λ k → entry-F M i k))
               (tuple-cong {y} _ _ (λ k → entry-F N k j)) ⟩
      cotuple {y} (λ k → entry (F .fmor M) i k) ∘ tuple {y} (λ k → entry (F .fmor N) k j)
    ≈˘⟨ entry-comp {x} {y} {z} (F .fmor N) (F .fmor M) i j ⟩
      π {z} i ∘ ((F .fmor M ∘ F .fmor N) ∘ ι {x} j)
    ∎) where
      open ≈-Reasoning isEquiv
      entry-F : ∀ {m n} (M : Matrix n m) (i : Fin n) (j : Fin m) → entry (F .fmor M) i j ≈ scalar .func (M i j)
      entry-F {m} {n} M i j =
        begin
          π {n} i ∘ (tuple {n} (λ i' → cotuple {m} (λ j' → scalar .func (M i' j'))) ∘ ι {m} j)
        ≈˘⟨ assoc _ _ _ ⟩
          (π {n} i ∘ tuple {n} (λ i' → cotuple {m} (λ j' → scalar .func (M i' j')))) ∘ ι {m} j
        ≈⟨ ∘-cong (tuple-π {n} _ i) ≈-refl ⟩
          cotuple {m} (λ j' → scalar .func (M i j')) ∘ ι {m} j
        ≈⟨ cotuple-ι {m} _ j ⟩
          scalar .func (M i j)
        ∎

  -- Entry-wise characterization of F, re-stated at module level for use below.
  entry-F : ∀ {m n} (M : Matrix n m) (i : Fin n) (j : Fin m) → entry (F .fmor M) i j ≈ scalar .func (M i j)
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

  -- F⁻¹ : MatRep(𝒞, X) → Mat(S), the "extract matrix of entries" direction.
  F⁻¹ : Functor MatRep.cat Mat.cat
  F⁻¹ .fobj n = n
  F⁻¹ .fmor {m} {n} f i j = scalar-iso .bwd .func (entry {m} {n} f i j)
  F⁻¹ .fmor-cong p i j = scalar-iso .bwd .func-resp-≈ (∘-cong ≈-refl (∘-cong p ≈-refl))
  F⁻¹ .fmor-id {n} i j =
    begin
      scalar-iso .bwd .func (entry {n} {n} (id (X^ n)) i j)
    ≈⟨ scalar-iso .bwd .func-resp-≈ (∘-cong ≈-refl id-left) ⟩
      scalar-iso .bwd .func (π {n} i ∘ ι {n} j)
    ≈˘⟨ scalar-iso .bwd .func-resp-≈ (scalar-e i j) ⟩
      scalar-iso .bwd .func (scalar .func (Mat.e i j))
    ≈⟨ scalar-iso .bwd∘fwd≈id .func-eq (Setoid.refl A) ⟩
      Mat.e i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)
  F⁻¹ .fmor-comp {x} {y} {z} g f i j =
    begin
      scalar-iso .bwd .func (entry {x} {z} (g ∘ f) i j)
    ≈⟨ scalar-iso .bwd .func-resp-≈ (entry-comp {x} {y} {z} f g i j) ⟩
      scalar-iso .bwd .func (cotuple {y} (λ k → entry {y} {z} g i k) ∘ tuple {y} (λ k → entry {x} {y} f k j))
    ≈˘⟨ scalar-iso .bwd .func-resp-≈ (∘-cong (cotuple-cong {y} _ _ (λ k → scalar-iso .fwd∘bwd≈id .func-eq ≈-refl))
                                 (tuple-cong {y} _ _ (λ k → scalar-iso .fwd∘bwd≈id .func-eq ≈-refl))) ⟩
      scalar-iso .bwd .func (cotuple {y} (λ k → scalar .func (scalar-iso .bwd .func (entry {y} {z} g i k)))
                  ∘ tuple {y} (λ k → scalar .func (scalar-iso .bwd .func (entry {x} {y} f k j))))
    ≈˘⟨ scalar-iso .bwd .func-resp-≈ (scalar-Σ {y} (λ k → scalar-iso .bwd .func (entry {y} {z} g i k)) (λ k → scalar-iso .bwd .func (entry {x} {y} f k j))) ⟩
      scalar-iso .bwd .func (scalar .func (Mat.Σ {y} (λ k → scalar-iso .bwd .func (entry {y} {z} g i k) ·ₛ scalar-iso .bwd .func (entry {x} {y} f k j))))
    ≈⟨ scalar-iso .bwd∘fwd≈id .func-eq (Setoid.refl A) ⟩
      Mat.Σ {y} (λ k → scalar-iso .bwd .func (entry {y} {z} g i k) ·ₛ scalar-iso .bwd .func (entry {x} {y} f k j))
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  F⁻¹∘F : ∀ {m n} (M : Matrix n m) → (F⁻¹ .fmor (F .fmor M)) Mat.≈ₘ M
  F⁻¹∘F {m} {n} M i j =
    begin
      scalar-iso .bwd .func (entry {m} {n} (F .fmor {m} {n} M) i j)
    ≈⟨ scalar-iso .bwd .func-resp-≈ (entry-F {m} {n} M i j) ⟩
      scalar-iso .bwd .func (scalar .func (M i j))
    ≈⟨ scalar-iso .bwd∘fwd≈id .func-eq (Setoid.refl A) ⟩
      M i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  F∘F⁻¹ : ∀ {m n} (f : X^ m ⇒ X^ n) → F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f) ≈ f
  F∘F⁻¹ {m} {n} f = entry-ext {m} {n} (λ i j →
    begin
      entry {m} {n} (F .fmor {m} {n} (F⁻¹ .fmor {m} {n} f)) i j
    ≈⟨ entry-F {m} {n} (F⁻¹ .fmor {m} {n} f) i j ⟩
      scalar .func (scalar-iso .bwd .func (entry {m} {n} f i j))
    ≈⟨ scalar-iso .fwd∘bwd≈id .func-eq ≈-refl ⟩
      entry {m} {n} f i j
    ∎) where open ≈-Reasoning isEquiv

  F-εₘ : ∀ {m n} → F .fmor (Mat.εₘ {m} {n}) ≈ εm {X^ n} {X^ m}
  F-εₘ {m} {n} = entry-ext {n} {m} (λ i j →
    begin
      entry {n} {m} (F .fmor {n} {m} (Mat.εₘ {m} {n})) i j
    ≈⟨ entry-F {n} {m} (Mat.εₘ {m} {n}) i j ⟩
      scalar .func S-ε
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

  -- F is faithful: morphisms in Mat(S) are determined by their F-images.
  F-faithful : ∀ {m n} {M N : Matrix n m} → F .fmor {m} {n} M ≈ F .fmor {m} {n} N → M Mat.≈ₘ N
  F-faithful {m} {n} {M} {N} eq i j =
    begin
      M i j
    ≈˘⟨ F⁻¹∘F {m} {n} M i j ⟩
      scalar-iso .bwd .func (entry {m} {n} (F .fmor {m} {n} M) i j)
    ≈⟨ scalar-iso .bwd .func-resp-≈ (∘-cong ≈-refl (∘-cong eq ≈-refl)) ⟩
      scalar-iso .bwd .func (entry {m} {n} (F .fmor {m} {n} N) i j)
    ≈⟨ F⁻¹∘F {m} {n} N i j ⟩
      N i j
    ∎ where open ≈-Reasoning (CommutativeSemiring.isEquivalence S)

  -- F⁻¹ preserves the zero morphism (derived via F's preservation + faithfulness).
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

  -- F⁻¹ preserves addition (derived via F's preservation + faithfulness).
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
