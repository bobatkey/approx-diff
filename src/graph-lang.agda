{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (0ℓ)
open import prop using (LiftS; liftS)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category; HasTerminal; HasProducts)
open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (CMonEnriched)

module graph-lang (Base : Set) where

-- The free biproduct category on some objects with no extra
-- morphisms. I think this also expressible as formal sums of
-- morphisms in the free product category.

data Sort : Set where
  [_]  : Base → Sort
  𝟙    : Sort
  _×_  : Sort → Sort → Sort

data Term (σ : Sort) : Sort → Set where
  x     : Term σ σ
  !     : Term σ 𝟙
  π₁    : ∀ {τ₁ τ₂} → Term σ (τ₁ × τ₂) → Term σ τ₁
  π₂    : ∀ {τ₁ τ₂} → Term σ (τ₁ × τ₂) → Term σ τ₂
  _,_   : ∀ {τ₁ τ₂} → Term σ τ₁ → Term σ τ₂ → Term σ (τ₁ × τ₂)
  _+_   : ∀ {τ} → Term σ τ → Term σ τ → Term σ τ
  ∅     : ∀ {τ} → Term σ τ

data _≃_ : ∀ {σ τ} → Term σ τ → Term σ τ → Set where
  ≃-sym   : ∀ {σ τ} {f g : Term σ τ} → f ≃ g → g ≃ f
  ≃-trans : ∀ {σ τ} {f g h : Term σ τ} → f ≃ g → g ≃ h → f ≃ h

  x≃x : ∀ {σ} → _≃_ {σ} {σ} x x
  ∅≃∅ : ∀ {σ τ} → _≃_ {σ} {τ} ∅ ∅
  π₁-cong : ∀ {σ τ₁ τ₂} {f g : Term σ (τ₁ × τ₂)} → f ≃ g → π₁ f ≃ π₁ g
  π₂-cong : ∀ {σ τ₁ τ₂} {f g : Term σ (τ₁ × τ₂)} → f ≃ g → π₂ f ≃ π₂ g
  ,-cong  : ∀ {σ τ₁ τ₂} {f₁ g₁ : Term σ τ₁} {f₂ g₂ : Term σ τ₂} → f₁ ≃ g₁ → f₂ ≃ g₂ → (f₁ , f₂) ≃ (g₁ , g₂)
  +-cong  : ∀ {σ τ} {f₁ g₁ f₂ g₂ : Term σ τ} → f₁ ≃ g₁ → f₂ ≃ g₂ → (f₁ + f₂) ≃ (g₁ + g₂)

  -- Terminal
  !≃f : ∀ {σ} {f : Term σ 𝟙} → ! ≃ f

  -- Product
  pair-p₁  : ∀ {σ τ₁ τ₂} {f : Term σ τ₁} {g : Term σ τ₂} → π₁ (f , g) ≃ f
  pair-p₂  : ∀ {σ τ₁ τ₂} {f : Term σ τ₁} {g : Term σ τ₂} → π₂ (f , g) ≃ g
  pair-ext : ∀ {σ τ₁ τ₂} {f : Term σ (τ₁ × τ₂)} → (π₁ f , π₂ f) ≃ f

  -- Addition
  +-assoc : ∀ {σ τ} {f₁ f₂ f₃ : Term σ τ} → ((f₁ + f₂) + f₃) ≃ (f₁ + (f₂ + f₃))
  +-comm  : ∀ {σ τ} {f₁ f₂ : Term σ τ} → (f₁ + f₂) ≃ (f₂ + f₁)
  +-lunit : ∀ {σ τ} {f : Term σ τ} → (∅ + f) ≃ f

  -- Bilinearity
  π₁-∅   : ∀ {σ τ₁ τ₂} → π₁ (∅ {σ} {τ₁ × τ₂}) ≃ ∅
  π₂-∅   : ∀ {σ τ₁ τ₂} → π₂ (∅ {σ} {τ₁ × τ₂}) ≃ ∅
  pair-∅ : ∀ {σ τ₁ τ₂} → (∅ {σ} {τ₁} , ∅ {σ} {τ₂}) ≃ ∅
  π₁-+   : ∀ {σ τ₁ τ₂} {f₁ f₂ : Term σ (τ₁ × τ₂)} → π₁ (f₁ + f₂) ≃ (π₁ f₁ + π₁ f₂)
  π₂-+   : ∀ {σ τ₁ τ₂} {f₁ f₂ : Term σ (τ₁ × τ₂)} → π₂ (f₁ + f₂) ≃ (π₂ f₁ + π₂ f₂)
  pair-+ : ∀ {σ τ₁ τ₂} {f₁ f₂ : Term σ τ₁} {g₁ g₂ : Term σ τ₂} → ((f₁ + f₂) , (g₁ + g₂)) ≃ ((f₁ , g₁) + (f₂ , g₂))

≃-refl : ∀ {σ τ} {f : Term σ τ} → f ≃ f
≃-refl {f = x} = x≃x
≃-refl {f = !} = !≃f
≃-refl {f = π₁ f} = π₁-cong ≃-refl
≃-refl {f = π₂ f} = π₂-cong ≃-refl
≃-refl {f = f , f₁} = ,-cong ≃-refl ≃-refl
≃-refl {f = f + f₁} = +-cong ≃-refl ≃-refl
≃-refl {f = ∅} = ∅≃∅

_≃ₚ_ : ∀ {σ τ} → Term σ τ → Term σ τ → Prop
f ≃ₚ g = LiftS 0ℓ (f ≃ g)

≃-isEquivalence : ∀ {σ τ} → IsEquivalence (λ f g → LiftS 0ℓ (_≃_ {σ} {τ} f g))
≃-isEquivalence .IsEquivalence.refl = liftS ≃-refl
≃-isEquivalence .IsEquivalence.sym (liftS p) = liftS (≃-sym p)
≃-isEquivalence .IsEquivalence.trans (liftS p) (liftS q) = liftS (≃-trans p q)

id : ∀ σ → Term σ σ
id _ = x

_∘_ : ∀ {σ τ υ} → Term τ υ → Term σ τ → Term σ υ
x ∘ g = g
! ∘ g = !
π₁ f ∘ g = π₁ (f ∘ g)
π₂ f ∘ g = π₂ (f ∘ g)
(f₁ , f₂) ∘ g = (f₁ ∘ g) , (f₂ ∘ g)
(f₁ + f₂) ∘ g = (f₁ ∘ g) + (f₂ ∘ g)
∅ ∘ g = ∅

∘-cong-snd : ∀ {σ τ υ} (f : Term τ υ) {g₁ g₂ : Term σ τ} → g₁ ≃ g₂ → (f ∘ g₁) ≃ (f ∘ g₂)
∘-cong-snd x q = q
∘-cong-snd ! q = !≃f
∘-cong-snd (π₁ f) q = π₁-cong (∘-cong-snd f q)
∘-cong-snd (π₂ f) q = π₂-cong (∘-cong-snd f q)
∘-cong-snd (f , f₁) q = ,-cong (∘-cong-snd f q) (∘-cong-snd f₁ q)
∘-cong-snd (f + f₁) q = +-cong (∘-cong-snd f q) (∘-cong-snd f₁ q)
∘-cong-snd ∅ q = ∅≃∅

∘-cong : ∀ {σ τ υ} {f₁ f₂ : Term τ υ} {g₁ g₂ : Term σ τ} → f₁ ≃ f₂ → g₁ ≃ g₂ → (f₁ ∘ g₁) ≃ (f₂ ∘ g₂)
∘-cong (≃-sym p) q = ≃-sym (∘-cong p (≃-sym q))
∘-cong (≃-trans p p₁) q = ≃-trans (∘-cong p q) (∘-cong p₁ (≃-trans (≃-sym q) q))
∘-cong x≃x q = q
∘-cong ∅≃∅ q = ∅≃∅
∘-cong (π₁-cong p) q = π₁-cong (∘-cong p q)
∘-cong (π₂-cong p) q = π₂-cong (∘-cong p q)
∘-cong (,-cong p p₁) q = ,-cong (∘-cong p q) (∘-cong p₁ q)
∘-cong (+-cong p p₁) q = +-cong (∘-cong p q) (∘-cong p₁ q)
∘-cong !≃f q = !≃f
∘-cong pair-p₁ q = ≃-trans pair-p₁ (∘-cong-snd _ q)
∘-cong pair-p₂ q = ≃-trans pair-p₂ (∘-cong-snd _ q)
∘-cong pair-ext q = ≃-trans pair-ext (∘-cong-snd _ q)
∘-cong +-assoc q = ≃-trans +-assoc (+-cong (∘-cong-snd _ q) (+-cong (∘-cong-snd _ q) (∘-cong-snd _ q)))
∘-cong +-comm q = ≃-trans +-comm (+-cong (∘-cong-snd _ q) (∘-cong-snd _ q))
∘-cong +-lunit q = ≃-trans +-lunit (∘-cong-snd _ q)
∘-cong π₁-∅ q = π₁-∅
∘-cong π₂-∅ q = π₂-∅
∘-cong pair-∅ q = pair-∅
∘-cong π₁-+ q = ≃-trans π₁-+ (+-cong (π₁-cong (∘-cong-snd _ q)) (π₁-cong (∘-cong-snd _ q)))
∘-cong π₂-+ q = ≃-trans π₂-+ (+-cong (π₂-cong (∘-cong-snd _ q)) (π₂-cong (∘-cong-snd _ q)))
∘-cong pair-+ q = ≃-trans pair-+ (+-cong (,-cong (∘-cong-snd _ q) (∘-cong-snd _ q)) (,-cong (∘-cong-snd _ q) (∘-cong-snd _ q)))

id-left : ∀ {σ τ} {f : Term σ τ} → (id τ ∘ f) ≃ f
id-left {f = f} = ≃-refl

id-right : ∀ {σ τ} {f : Term σ τ} → (f ∘ id σ) ≃ f
id-right {f = x} = x≃x
id-right {f = !} = !≃f
id-right {f = π₁ f} = π₁-cong id-right
id-right {f = π₂ f} = π₂-cong id-right
id-right {f = f₁ , f₂} = ,-cong id-right id-right
id-right {f = f₁ + f₂} = +-cong id-right id-right
id-right {f = ∅} = ∅≃∅

assoc : ∀ {σ τ υ ϕ} (f : Term υ ϕ) (g : Term τ υ) (h : Term σ τ) →
        ((f ∘ g) ∘ h) ≃ (f ∘ (g ∘ h))
assoc x g h = ≃-refl
assoc ! g h = !≃f
assoc (π₁ f) g h = π₁-cong (assoc f g h)
assoc (π₂ f) g h = π₂-cong (assoc f g h)
assoc (f₁ , f₂) g h = ,-cong (assoc f₁ g h) (assoc f₂ g h)
assoc (f₁ + f₂) g h = +-cong (assoc f₁ g h) (assoc f₂ g h)
assoc ∅ g h = ∅≃∅

cat : Category 0ℓ 0ℓ 0ℓ
cat .Category.obj = Sort
cat .Category._⇒_ = Term
cat .Category._≈_ = _≃ₚ_
cat .Category.isEquiv = ≃-isEquivalence
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong (liftS p) (liftS q) = liftS (∘-cong p q)
cat .Category.id-left = liftS id-left
cat .Category.id-right = liftS id-right
cat .Category.assoc f g h = liftS (assoc f g h)

-- This category has all finite products
hasTerminal : HasTerminal cat
hasTerminal .HasTerminal.witness = 𝟙
hasTerminal .HasTerminal.terminal-mor _ = !
hasTerminal .HasTerminal.terminal-unique _ f g = liftS (≃-trans (≃-sym !≃f) !≃f)

hasProducts : HasProducts cat
hasProducts .HasProducts.prod = _×_
hasProducts .HasProducts.p₁ = π₁ x
hasProducts .HasProducts.p₂ = π₂ x
hasProducts .HasProducts.pair = _,_
hasProducts .HasProducts.pair-cong (liftS p) (liftS q) = liftS (,-cong p q)
hasProducts .HasProducts.pair-p₁ f g = liftS pair-p₁
hasProducts .HasProducts.pair-p₂ f g = liftS pair-p₂
hasProducts .HasProducts.pair-ext f = liftS pair-ext

-- Commutative Monoid Enrichment
comp-bilinear₂ : ∀ {σ τ υ} → (f : Term τ υ) (g₁ g₂ : Term σ τ) →
                (f ∘ (g₁ + g₂)) ≃ ((f ∘ g₁) + (f ∘ g₂))
comp-bilinear₂ x g₁ g₂ = ≃-refl
comp-bilinear₂ ! g₁ g₂ = !≃f
comp-bilinear₂ (π₁ f) g₁ g₂ = ≃-trans (π₁-cong (comp-bilinear₂ f g₁ g₂)) π₁-+
comp-bilinear₂ (π₂ f) g₁ g₂ = ≃-trans (π₂-cong (comp-bilinear₂ f g₁ g₂)) π₂-+
comp-bilinear₂ (f₁ , f₂) g₁ g₂ =
  ≃-trans (,-cong (comp-bilinear₂ f₁ g₁ g₂) (comp-bilinear₂ f₂ g₁ g₂))
          pair-+
comp-bilinear₂ (f₁ + f₂) g₁ g₂ =
  ≃-trans (+-cong (comp-bilinear₂ f₁ g₁ g₂) (comp-bilinear₂ f₂ g₁ g₂))
           -- FIXME: this is an instance of interchange
          (≃-trans +-assoc (≃-trans (+-cong ≃-refl (≃-sym +-assoc)) (≃-trans (+-cong ≃-refl (+-cong +-comm ≃-refl)) (≃-trans (+-cong ≃-refl +-assoc) (≃-sym +-assoc)))))
comp-bilinear₂ ∅ g₁ g₂ = ≃-sym +-lunit

comp-bilinear-ε₂ : ∀ {σ τ υ} (f : Term τ υ) → (f ∘ ∅) ≃ ∅ {σ} {υ}
comp-bilinear-ε₂ x = ∅≃∅
comp-bilinear-ε₂ ! = !≃f
comp-bilinear-ε₂ (π₁ f) = ≃-trans (π₁-cong (comp-bilinear-ε₂ f)) π₁-∅
comp-bilinear-ε₂ (π₂ f) = ≃-trans (π₂-cong (comp-bilinear-ε₂ f)) π₂-∅
comp-bilinear-ε₂ (f₁ , f₂) = ≃-trans (,-cong (comp-bilinear-ε₂ f₁) (comp-bilinear-ε₂ f₂)) pair-∅
comp-bilinear-ε₂ (f₁ + f₂) = ≃-trans (+-cong (comp-bilinear-ε₂ f₁) (comp-bilinear-ε₂ f₂))
                              +-lunit
comp-bilinear-ε₂ ∅ = ∅≃∅

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid.ε = ∅
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid._+_ = _+_
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid.+-cong (liftS p) (liftS q) = liftS (+-cong p q)
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid.+-lunit = liftS +-lunit
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid.+-assoc = liftS +-assoc
cmon-enriched .CMonEnriched.homCM σ τ .CommutativeMonoid.+-comm = liftS +-comm
cmon-enriched .CMonEnriched.comp-bilinear₁ _ _ _ = liftS ≃-refl
cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ = liftS (comp-bilinear₂ f g₁ g₂)
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f = liftS ≃-refl
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f = liftS (comp-bilinear-ε₂ f)
