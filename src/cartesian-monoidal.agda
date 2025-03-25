{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (module ≈-Reasoning)
open import categories using (Category; HasTerminal; HasProducts)
open import monoidal-product using (MonoidalProduct; SymmetricMonoidal)

-- Construction of monoidal products from cartesian products.

module cartesian-monoidal
  {o m e} (𝒞 : Category o m e)
  (terminal : HasTerminal 𝒞)
  (products : HasProducts 𝒞)
  where

open Category 𝒞

open HasTerminal terminal renaming (witness to 𝟙)

open HasProducts products

_×_ : obj → obj → obj
x × y = prod x y

_×m_ : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ x₂ → y₁ ⇒ y₂ → (x₁ × y₁) ⇒ (x₂ × y₂)
_×m_ = prod-m

×m-cong : ∀ {x₁ x₂ y₁ y₂} {f₁ f₂ : x₁ ⇒ x₂} {g₁ g₂ : y₁ ⇒ y₂} → f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ×m g₁) ≈ (f₂ ×m g₂)
×m-cong = prod-m-cong

×m-id : ∀ {x y} → (id x ×m id y) ≈ id (x × y)
×m-id = prod-m-id

×m-comp : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
          (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
          ((f₁ ∘ g₁) ×m (f₂ ∘ g₂)) ≈ ((f₁ ×m f₂) ∘ (g₁ ×m g₂))
×m-comp = pair-functorial

-- Associativity
×-assoc : ∀ {x y z} → ((x × y) × z) ⇒ (x × (y × z))
×-assoc = pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)

×-assoc-natural : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f : x₁ ⇒ x₂) (g : y₁ ⇒ y₂) (h : z₁ ⇒ z₂) →
  ((f ×m (g ×m h)) ∘ ×-assoc) ≈ (×-assoc ∘ ((f ×m g) ×m h))
×-assoc-natural f g h = begin
    (f ×m (g ×m h)) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-compose _ _ _ _ ⟩
    pair (f ∘ (p₁ ∘ p₁)) ((g ×m h) ∘ pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-cong ≈-refl (pair-compose _ _ _ _) ⟩
    pair (f ∘ (p₁ ∘ p₁)) (pair (g ∘ (p₂ ∘ p₁)) (h ∘ p₂))
  ≈˘⟨ pair-cong (assoc _ _ _) (pair-cong (assoc _ _ _) ≈-refl) ⟩
    pair ((f ∘ p₁) ∘ p₁) (pair ((g ∘ p₂) ∘ p₁) (h ∘ p₂))
  ≈˘⟨ pair-cong ≈-refl (pair-cong (∘-cong (pair-p₂ _ _) ≈-refl) ≈-refl) ⟩
    pair ((f ∘ p₁) ∘ p₁) (pair ((p₂ ∘ (f ×m g)) ∘ p₁) (h ∘ p₂))
  ≈˘⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (pair-cong (≈-sym (assoc _ _ _)) ≈-refl) ⟩
    pair ((p₁ ∘ (f ×m g)) ∘ p₁) (pair (p₂ ∘ ((f ×m g) ∘ p₁)) (h ∘ p₂))
  ≈⟨ pair-cong (assoc _ _ _) (pair-cong (∘-cong ≈-refl (≈-sym (pair-p₁ _ _))) ≈-refl) ⟩
    pair (p₁ ∘ ((f ×m g) ∘ p₁)) (pair (p₂ ∘ (p₁ ∘ ((f ×m g) ×m h))) (h ∘ p₂))
  ≈˘⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-p₂ _ _)) ⟩
    pair (p₁ ∘ (p₁ ∘ ((f ×m g) ×m h))) (pair ((p₂ ∘ p₁) ∘ ((f ×m g) ×m h)) (p₂ ∘ ((f ×m g) ×m h)))
  ≈˘⟨ pair-cong (assoc _ _ _) (pair-natural _ _ _) ⟩
    pair ((p₁ ∘ p₁) ∘ ((f ×m g) ×m h)) (pair (p₂ ∘ p₁) p₂ ∘ ((f ×m g) ×m h))
  ≈˘⟨ pair-natural _ _ _ ⟩
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ ((f ×m g) ×m h)
  ∎
  where open ≈-Reasoning isEquiv

×-assoc⁻¹ : ∀ {x y z} → (x × (y × z)) ⇒ ((x × y) × z)
×-assoc⁻¹ = pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂)

×-assoc-iso1 : ∀ {x y z} → (×-assoc ∘ ×-assoc⁻¹) ≈ id (x × (y × z))
×-assoc-iso1 =
  begin
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂)
  ≈⟨ pair-natural _ _ _ ⟩
    pair ((p₁ ∘ p₁) ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂)) (pair (p₂ ∘ p₁) p₂ ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂))
  ≈⟨ pair-cong (assoc _ _ _) (pair-natural _ _ _) ⟩
    pair (p₁ ∘ (p₁ ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂))) (pair ((p₂ ∘ p₁) ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂)) (p₂ ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂)))
  ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-p₂ _ _)) ⟩
    pair (p₁ ∘ pair p₁ (p₁ ∘ p₂)) (pair (p₂ ∘ (p₁ ∘ pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂))) (p₂ ∘ p₂))
  ≈⟨ pair-cong (pair-p₁ _ _) (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl) ⟩
    pair p₁ (pair (p₂ ∘ pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂))
  ≈⟨ pair-cong ≈-refl (pair-cong (pair-p₂ _ _) ≈-refl) ⟩
    pair p₁ (pair (p₁ ∘ p₂) (p₂ ∘ p₂))
  ≈˘⟨ pair-cong ≈-refl (pair-natural _ _ _) ⟩
    pair p₁ (pair p₁ p₂ ∘ p₂)
  ≈⟨ pair-cong ≈-refl (∘-cong pair-ext0 ≈-refl) ⟩
    pair p₁ (id _ ∘ p₂)
  ≈⟨ pair-cong ≈-refl id-left ⟩
    pair p₁ p₂
  ≈⟨ pair-ext0 ⟩
    id _
  ∎
  where open ≈-Reasoning isEquiv

×-assoc-iso2 : ∀ {x y z} → (×-assoc⁻¹ ∘ ×-assoc) ≈ id ((x × y) × z)
×-assoc-iso2 = begin
    pair (pair p₁ (p₁ ∘ p₂)) (p₂ ∘ p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-natural _ _ _ ⟩
    pair (pair p₁ (p₁ ∘ p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ((p₂ ∘ p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))
  ≈⟨ pair-cong (pair-natural _ _ _) (assoc _ _ _) ⟩
    pair (pair (p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ((p₁ ∘ p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))) (p₂ ∘ (p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)))
  ≈⟨ pair-cong (pair-cong (pair-p₁ _ _) (assoc _ _ _)) (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
    pair (pair (p₁ ∘ p₁) (p₁ ∘ (p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)))) (p₂ ∘ pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-cong (pair-cong ≈-refl (∘-cong ≈-refl (pair-p₂ _ _))) (pair-p₂ _ _) ⟩
    pair (pair (p₁ ∘ p₁) (p₁ ∘ pair (p₂ ∘ p₁) p₂)) p₂
  ≈⟨ pair-cong (pair-cong ≈-refl (pair-p₁ _ _)) ≈-refl ⟩
    pair (pair (p₁ ∘ p₁) (p₂ ∘ p₁)) p₂
  ≈⟨ pair-cong (pair-ext p₁) ≈-refl ⟩
    pair p₁ p₂
  ≈⟨ pair-ext0 ⟩
    id _
  ∎
  where open ≈-Reasoning isEquiv

-- Right unit
×-runit : ∀ {x} → (x × 𝟙) ⇒ x
×-runit = p₁

×-runit⁻¹ : ∀ {x} → x ⇒ (x × 𝟙)
×-runit⁻¹ = pair (id _) (terminal-mor _)

×-runit-natural : ∀ {x₁ x₂} (f : x₁ ⇒ x₂) → (f ∘ ×-runit) ≈ (×-runit ∘ (f ×m id _))
×-runit-natural f = begin
    f ∘ p₁
  ≈˘⟨ pair-p₁ _ _ ⟩
    p₁ ∘ (f ×m id _)
  ∎
  where open ≈-Reasoning isEquiv

×-runit-iso1 : ∀ {x} → (×-runit ∘ ×-runit⁻¹) ≈ id x
×-runit-iso1 = pair-p₁ _ _

×-runit-iso2 : ∀ {x} → (×-runit⁻¹ ∘ ×-runit) ≈ id (x × 𝟙)
×-runit-iso2 = begin
    pair (id _) (terminal-mor _) ∘ p₁
  ≈⟨ pair-natural _ _ _ ⟩
    pair (id _ ∘ p₁) (terminal-mor _ ∘ p₁)
  ≈⟨ pair-cong id-left (terminal-unique _ _ _) ⟩
    pair p₁ p₂
  ≈⟨ pair-ext0 ⟩
    id _
  ∎
  where open ≈-Reasoning isEquiv

-- Left unit
×-lunit : ∀ {x} → (𝟙 × x) ⇒ x
×-lunit = p₂

×-lunit⁻¹ : ∀ {x} → x ⇒ (𝟙 × x)
×-lunit⁻¹ = pair (terminal-mor _) (id _)

×-lunit-natural : ∀ {x₁ x₂} (f : x₁ ⇒ x₂) → (f ∘ ×-lunit) ≈ (×-lunit ∘ (id _ ×m f))
×-lunit-natural f = begin
    f ∘ p₂
  ≈˘⟨ pair-p₂ _ _ ⟩
    p₂ ∘ (id _ ×m f)
  ∎
  where open ≈-Reasoning isEquiv

×-lunit-iso1 : ∀ {x} → (×-lunit ∘ ×-lunit⁻¹) ≈ id x
×-lunit-iso1 = pair-p₂ _ _

×-lunit-iso2 : ∀ {x} → (×-lunit⁻¹ ∘ ×-lunit) ≈ id (𝟙 × x)
×-lunit-iso2 = begin
    pair (terminal-mor _) (id _) ∘ p₂
  ≈⟨ pair-natural _ _ _ ⟩
    pair (terminal-mor _ ∘ p₂) (id _ ∘ p₂)
  ≈⟨ pair-cong (terminal-unique _ _ _) id-left ⟩
    pair p₁ p₂
  ≈⟨ pair-ext0 ⟩
    id _
  ∎
  where open ≈-Reasoning isEquiv

-- FIXME: there ought to be a decision procedure for this...
pentagon : ∀ {w x y z} →
           (×-assoc ∘ ×-assoc {w × x} {y} {z}) ≈ (((id w ×m ×-assoc) ∘ ×-assoc) ∘ (×-assoc ×m id z))
pentagon = begin
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-natural _ _ _ ⟩
    pair ((p₁ ∘ p₁) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) (pair (p₂ ∘ p₁) p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))
  ≈⟨ pair-cong (assoc _ _ _) (pair-natural _ _ _) ⟩
    pair (p₁ ∘ (p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))) (pair ((p₂ ∘ p₁) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) (p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)))
  ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-p₂ _ _)) ⟩
    pair (p₁ ∘ (p₁ ∘ p₁)) (pair (p₂ ∘ (p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))) (pair (p₂ ∘ p₁) p₂))
  ≈⟨ pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl) ⟩
    pair (p₁ ∘ (p₁ ∘ p₁)) (pair (p₂ ∘ (p₁ ∘ p₁)) (pair (p₂ ∘ p₁) p₂))

  ≈˘⟨ pair-cong (assoc _ _ _) (pair-cong (assoc _ _ _) ≈-refl) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair ((p₂ ∘ p₁) ∘ p₁) (pair (p₂ ∘ p₁) p₂))
  ≈˘⟨ pair-cong ≈-refl (pair-cong ≈-refl (pair-cong (∘-cong (pair-p₂ _ _) ≈-refl) ≈-refl)) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair ((p₂ ∘ p₁) ∘ p₁) (pair ((p₂ ∘ pair (p₂ ∘ p₁) p₂) ∘ p₁) p₂))
  ≈⟨ pair-cong ≈-refl (pair-cong (∘-cong (≈-sym (pair-p₁ _ _)) ≈-refl) (pair-cong (assoc _ _ _) ≈-refl)) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair ((p₁ ∘ pair (p₂ ∘ p₁) p₂) ∘ p₁) (pair (p₂ ∘ (pair (p₂ ∘ p₁) p₂ ∘ p₁)) p₂))
  ≈⟨ pair-cong ≈-refl (pair-cong (assoc _ _ _) (pair-cong (∘-cong ≈-refl (∘-cong (≈-sym (pair-p₂ _ _)) ≈-refl)) ≈-refl)) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair (p₁ ∘ (pair (p₂ ∘ p₁) p₂ ∘ p₁)) (pair (p₂ ∘ ((p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ p₁)) p₂))
  ≈˘⟨ pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl)) (pair-cong (∘-cong ≈-refl (≈-sym (assoc _ _ _))) ≈-refl)) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair (p₁ ∘ ((p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ p₁)) (pair (p₂ ∘ (p₂ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ p₁))) p₂))
  ≈⟨ pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (assoc _ _ _)) (pair-cong (∘-cong ≈-refl (∘-cong ≈-refl (≈-sym (pair-p₁ _ _)))) ≈-refl)) ⟩
    pair ((p₁ ∘ p₁) ∘ p₁) (pair (p₁ ∘ (p₂ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ p₁))) (pair (p₂ ∘ (p₂ ∘ (p₁ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)))) p₂))
  ≈˘⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (pair-cong (∘-cong ≈-refl (∘-cong ≈-refl (pair-p₁ _ _))) (pair-cong (∘-cong ≈-refl (assoc _ _ _)) id-left)) ⟩
    pair ((p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ p₁) (pair (p₁ ∘ (p₂ ∘ (p₁ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)))) (pair (p₂ ∘ ((p₂ ∘ p₁) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _))) (id _ ∘ p₂)))
  ≈⟨ pair-cong (assoc _ _ _) (pair-cong (∘-cong ≈-refl (≈-sym (assoc _ _ _))) (pair-cong (≈-sym (assoc _ _ _)) (≈-sym (pair-p₂ _ _)))) ⟩
    pair (p₁ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ p₁)) (pair (p₁ ∘ ((p₂ ∘ p₁) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _))) (pair ((p₂ ∘ (p₂ ∘ p₁)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)) (p₂ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _))))
  ≈˘⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-natural _ _ _)) ⟩
    pair (p₁ ∘ (p₁ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _))) (pair ((p₁ ∘ (p₂ ∘ p₁)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)) (pair (p₂ ∘ (p₂ ∘ p₁)) p₂ ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)))
  ≈˘⟨ pair-cong (assoc _ _ _) (pair-natural _ _ _) ⟩
    pair ((p₁ ∘ p₁) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)) (pair (p₁ ∘ (p₂ ∘ p₁)) (pair (p₂ ∘ (p₂ ∘ p₁)) p₂) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _))
  ≈˘⟨ pair-natural _ _ _ ⟩
    pair (p₁ ∘ p₁) (pair (p₁ ∘ (p₂ ∘ p₁)) (pair (p₂ ∘ (p₂ ∘ p₁)) p₂)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ≈˘⟨ ∘-cong (pair-cong ≈-refl (pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl))) ≈-refl ⟩
    pair (p₁ ∘ p₁) (pair (p₁ ∘ (p₂ ∘ p₁)) (pair (p₂ ∘ (p₁ ∘ pair (p₂ ∘ p₁) p₂)) p₂)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ≈˘⟨ ∘-cong (pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-p₂ _ _)))) ≈-refl ⟩
    pair (p₁ ∘ p₁) (pair (p₁ ∘ (p₁ ∘ pair (p₂ ∘ p₁) p₂)) (pair ((p₂ ∘ p₁) ∘ pair (p₂ ∘ p₁) p₂) (p₂ ∘ pair (p₂ ∘ p₁) p₂))) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ≈˘⟨ ∘-cong (pair-cong ≈-refl (pair-cong (assoc _ _ _) (pair-natural _ _ _))) ≈-refl ⟩
    pair (p₁ ∘ p₁) (pair ((p₁ ∘ p₁) ∘ pair (p₂ ∘ p₁) p₂) (pair (p₂ ∘ p₁) p₂ ∘ pair (p₂ ∘ p₁) p₂)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ≈˘⟨ ∘-cong (pair-cong id-left (pair-natural _ _ _)) ≈-refl ⟩
    pair (id _ ∘ (p₁ ∘ p₁)) (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ pair (p₂ ∘ p₁) p₂) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ≈˘⟨ ∘-cong (pair-compose _ _ _ _) ≈-refl ⟩
    ((id _ ×m pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ×m id _)
  ∎
  where open ≈-Reasoning isEquiv

triangle : ∀ {x y} → ((id x ×m ×-lunit) ∘ ×-assoc) ≈ (×-runit ×m id y)
triangle {x} {y} = begin
    (id x ×m p₂) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-compose _ _ _ _ ⟩
    pair (id x ∘ (p₁ ∘ p₁)) (p₂ ∘ pair (p₂ ∘ p₁) p₂)
  ≈⟨ pair-cong id-left (pair-p₂ _ _) ⟩
    pair (p₁ ∘ p₁) p₂
  ≈˘⟨ pair-cong ≈-refl id-left ⟩
    pair (p₁ ∘ p₁) (id y ∘ p₂)
  ∎
  where open ≈-Reasoning isEquiv

×-monoidal : MonoidalProduct 𝒞
×-monoidal .MonoidalProduct.I⊗ = 𝟙
×-monoidal .MonoidalProduct._⊗_ = _×_
×-monoidal .MonoidalProduct._⊗m_ = _×m_
×-monoidal .MonoidalProduct.⊗m-cong = ×m-cong
×-monoidal .MonoidalProduct.⊗m-id = ×m-id
×-monoidal .MonoidalProduct.⊗m-comp = ×m-comp
×-monoidal .MonoidalProduct.⊗-assoc = ×-assoc
×-monoidal .MonoidalProduct.⊗-assoc-natural = ×-assoc-natural
×-monoidal .MonoidalProduct.⊗-assoc⁻¹ = ×-assoc⁻¹
×-monoidal .MonoidalProduct.⊗-assoc-iso1 = ×-assoc-iso1
×-monoidal .MonoidalProduct.⊗-assoc-iso2 = ×-assoc-iso2
×-monoidal .MonoidalProduct.⊗-lunit = ×-lunit
×-monoidal .MonoidalProduct.⊗-lunit⁻¹ = ×-lunit⁻¹
×-monoidal .MonoidalProduct.⊗-lunit-natural = ×-lunit-natural
×-monoidal .MonoidalProduct.⊗-lunit-iso1 = ×-lunit-iso1
×-monoidal .MonoidalProduct.⊗-lunit-iso2 = ×-lunit-iso2
×-monoidal .MonoidalProduct.⊗-runit = ×-runit
×-monoidal .MonoidalProduct.⊗-runit⁻¹ = ×-runit⁻¹
×-monoidal .MonoidalProduct.⊗-runit-natural = ×-runit-natural
×-monoidal .MonoidalProduct.⊗-runit-iso1 = ×-runit-iso1
×-monoidal .MonoidalProduct.⊗-runit-iso2 = ×-runit-iso2
×-monoidal .MonoidalProduct.pentagon = pentagon
×-monoidal .MonoidalProduct.triangle = triangle

------------------------------------------------------------------------------
-- Symmetry
×-symmetry : ∀ {x y} → (x × y) ⇒ (y × x)
×-symmetry = pair p₂ p₁

symmetry-natural : ∀ {x₁ x₂ y₁ y₂} (f : x₁ ⇒ x₂) (g : y₁ ⇒ y₂) →
        ((g ×m f) ∘ ×-symmetry) ≈ (×-symmetry ∘ (f ×m g))
symmetry-natural f g = begin
    (g ×m f) ∘ pair p₂ p₁                 ≈⟨ pair-compose _ _ _ _ ⟩
    pair (g ∘ p₂) (f ∘ p₁)                ≈˘⟨ pair-cong (pair-p₂ _ _) (pair-p₁ _ _) ⟩
    pair (p₂ ∘ (f ×m g)) (p₁ ∘ (f ×m g))  ≈˘⟨ pair-natural _ _ _ ⟩
    pair p₂ p₁ ∘ (f ×m g)                 ∎
  where open ≈-Reasoning isEquiv

symmetry-iso : ∀ {x y} → (×-symmetry ∘ ×-symmetry) ≈ id (x × y)
symmetry-iso = begin
    pair p₂ p₁ ∘ pair p₂ p₁                 ≈⟨ pair-natural _ _ _ ⟩
    pair (p₂ ∘ pair p₂ p₁) (p₁ ∘ pair p₂ p₁) ≈⟨ pair-cong (pair-p₂ _ _) (pair-p₁ _ _) ⟩
    pair p₁ p₂                              ≈⟨ pair-ext0  ⟩
    id _                                    ∎
  where open ≈-Reasoning isEquiv

symmetry-triangle : ∀ {x} → (×-runit ∘ ×-symmetry {𝟙} {x}) ≈ ×-lunit
symmetry-triangle = pair-p₁ _ _

symmetry-hexagon : ∀ {x y z} →
  (((id y ×m ×-symmetry) ∘ ×-assoc {y} {x} {z}) ∘ (×-symmetry ×m id z))
  ≈ ((×-assoc {y} {z} {x} ∘ ×-symmetry) ∘ ×-assoc {x} {y} {z})
symmetry-hexagon = begin
    ((id _ ×m pair p₂ p₁) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) ∘ (pair p₂ p₁ ×m id _)
  ≈⟨ ∘-cong (pair-compose _ _ _ _) ≈-refl ⟩
    pair (id _ ∘ (p₁ ∘ p₁)) (pair p₂ p₁ ∘ pair (p₂ ∘ p₁) p₂) ∘ (pair p₂ p₁ ×m id _)
  ≈⟨ ∘-cong (pair-cong id-left ≈-refl) ≈-refl ⟩
    pair (p₁ ∘ p₁) (pair p₂ p₁ ∘ pair (p₂ ∘ p₁) p₂) ∘ (pair p₂ p₁ ×m id _)
  ≈⟨ pair-natural _ _ _ ⟩
    pair ((p₁ ∘ p₁) ∘ (pair p₂ p₁ ×m id _)) ((pair p₂ p₁ ∘ pair (p₂ ∘ p₁) p₂) ∘ (pair p₂ p₁ ×m id _))
  ≈⟨ pair-cong (assoc _ _ _) (∘-cong (pair-natural _ _ _) ≈-refl) ⟩
    pair (p₁ ∘ (p₁ ∘ (pair p₂ p₁ ×m id _))) ((pair (p₂ ∘ pair (p₂ ∘ p₁) p₂) (p₁ ∘ pair (p₂ ∘ p₁) p₂)) ∘ (pair p₂ p₁ ×m id _))
  ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong (pair-cong (pair-p₂ _ _) (pair-p₁ _ _)) ≈-refl) ⟩
    pair (p₁ ∘ (pair p₂ p₁ ∘ p₁)) (pair p₂ (p₂ ∘ p₁) ∘ (pair p₂ p₁ ×m id _))
  ≈⟨ pair-cong (≈-sym (assoc _ _ _)) (pair-natural _ _ _) ⟩
    pair ((p₁ ∘ pair p₂ p₁) ∘ p₁) (pair (p₂ ∘ (pair p₂ p₁ ×m id _)) ((p₂ ∘ p₁) ∘ (pair p₂ p₁ ×m id _)))
  ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (pair-cong (pair-p₂ _ _) (assoc _ _ _)) ⟩
    pair (p₂ ∘ p₁) (pair (id _ ∘ p₂) (p₂ ∘ (p₁ ∘ (pair p₂ p₁ ×m id _))))
  ≈⟨ pair-cong ≈-refl (pair-cong id-left (∘-cong ≈-refl (pair-p₁ _ _))) ⟩
    pair (p₂ ∘ p₁) (pair p₂ (p₂ ∘ (pair p₂ p₁ ∘ p₁)))
  ≈˘⟨ pair-cong ≈-refl (pair-cong ≈-refl (assoc _ _ _)) ⟩
    pair (p₂ ∘ p₁) (pair p₂ ((p₂ ∘ pair p₂ p₁) ∘ p₁))
  ≈⟨ pair-cong ≈-refl (pair-cong ≈-refl (∘-cong (pair-p₂ _ _) ≈-refl)) ⟩
    pair (p₂ ∘ p₁) (pair p₂ (p₁ ∘ p₁))
  ≈˘⟨ pair-cong ≈-refl (pair-cong (pair-p₂ _ _) ≈-refl) ⟩
    pair (p₂ ∘ p₁) (pair (p₂ ∘ pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁))
  ≈˘⟨ pair-cong (pair-p₁ _ _) (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) ≈-refl) ⟩
    pair (p₁ ∘ pair (p₂ ∘ p₁) p₂) (pair (p₂ ∘ (p₁ ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁))) (p₁ ∘ p₁))
  ≈˘⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (pair-cong (assoc _ _ _) (pair-p₂ _ _)) ⟩
    pair (p₁ ∘ (p₁ ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁))) (pair ((p₂ ∘ p₁) ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁)) (p₂ ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁)))
  ≈˘⟨ pair-cong (assoc _ _ _) (pair-natural _ _ _) ⟩
    pair ((p₁ ∘ p₁) ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁)) (pair (p₂ ∘ p₁) p₂ ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁))
  ≈˘⟨ pair-natural _ _ _ ⟩
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ pair (pair (p₂ ∘ p₁) p₂) (p₁ ∘ p₁)
  ≈˘⟨ ∘-cong ≈-refl (pair-cong (pair-p₂ _ _) (pair-p₁ _ _)) ⟩
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ (pair (p₂ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)) (p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)))
  ≈˘⟨ ∘-cong ≈-refl (pair-natural _ _ _) ⟩
    pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ (pair p₂ p₁ ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂))
  ≈˘⟨ assoc _ _ _ ⟩
    (pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂) ∘ pair p₂ p₁) ∘ pair (p₁ ∘ p₁) (pair (p₂ ∘ p₁) p₂)
  ∎
  where open ≈-Reasoning isEquiv

×-symmetric-monoidal : SymmetricMonoidal 𝒞
×-symmetric-monoidal .SymmetricMonoidal.monoidal = ×-monoidal
×-symmetric-monoidal .SymmetricMonoidal.⊗-symmetry = ×-symmetry
×-symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-natural = symmetry-natural
×-symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-iso = symmetry-iso
×-symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-triangle = symmetry-triangle
×-symmetric-monoidal .SymmetricMonoidal.⊗-symmetry-hexagon = symmetry-hexagon
