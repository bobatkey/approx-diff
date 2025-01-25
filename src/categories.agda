{-# OPTIONS --prop --postfix-projections --safe #-}

module categories where

open import Level
open import prop
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)

-- Definition of category, and some basic structure one might want to
-- have.

record Category o m e : Set (suc (o ⊔ m ⊔ e)) where
  field
    obj  : Set o
    _⇒_ : obj → obj → Set m
    _≈_  : ∀ {x y} → x ⇒ y → x ⇒ y → Prop e

    isEquiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})

    id  : ∀ x → x ⇒ x
    _∘_ : ∀ {x y z} → y ⇒ z → x ⇒ y → x ⇒ z

    ∘-cong : ∀ {x y z} {f₁ f₂ : y ⇒ z} {g₁ g₂ : x ⇒ y} →
      f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ∘ g₁) ≈ (f₂ ∘ g₂)

    id-left  : ∀ {x y} {f : x ⇒ y} → (id y ∘ f) ≈ f
    id-right : ∀ {x y} {f : x ⇒ y} → (f ∘ id x) ≈ f
    assoc    : ∀ {w x y z} (f : y ⇒ z) (g : x ⇒ y) (h : w ⇒ x) →
      ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

  open Setoid renaming (_≈_ to _≃_)

  hom-setoid : obj → obj → Setoid m e
  hom-setoid x y .Carrier = x ⇒ y
  hom-setoid x y ._≃_ = _≈_
  hom-setoid x y .isEquivalence = isEquiv

record HasTerminal {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    witness         : obj
    terminal-mor    : (x : obj) → x ⇒ witness
    terminal-unique : (x : obj) → (f g : x ⇒ witness) → f ≈ g

record HasCoproducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {x y z} → x ⇒ z → y ⇒ z → coprod x y ⇒ z
    -- FIXME: equations

record HasProducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    prod : obj → obj → obj
    p₁   : ∀ {x y} → prod x y ⇒ x
    p₂   : ∀ {x y} → prod x y ⇒ y
    pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ prod y z

    pair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ y} {g₁ g₂ : x ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-p₁ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₁ ∘ pair f g) ≈ f
    pair-p₂ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₂ ∘ pair f g) ≈ g
    pair-ext : ∀ {x y z} (f : x ⇒ prod y z) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

  pair-natural : ∀ {w x y z} (h : w ⇒ x) (f : x ⇒ y) (g : x ⇒ z) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
  pair-natural h f g =
    begin
      pair f g ∘ h
    ≈⟨ isEquiv .sym (pair-ext _) ⟩
      pair (p₁ ∘ (pair f g ∘ h)) (p₂ ∘ (pair f g ∘ h))
    ≈⟨ isEquiv .sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((p₁ ∘ pair f g) ∘ h) ((p₂ ∘ pair f g) ∘ h)
    ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) (isEquiv .refl)) (∘-cong (pair-p₂ _ _) (isEquiv .refl)) ⟩
      pair (f ∘ h) (g ∘ h)
    ∎
    where open ≈-Reasoning isEquiv
          open IsEquivalence

  pair-compose : ∀ {x y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x ⇒ y₁) (g₂ : x ⇒ y₂) →
    (pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair g₁ g₂) ≈ pair (f₁ ∘ g₁) (f₂ ∘ g₂)
  pair-compose f₁ f₂ g₁ g₂ =
    begin
      pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair g₁ g₂
    ≈⟨ pair-natural _ _ _ ⟩
      pair ((f₁ ∘ p₁) ∘ pair g₁ g₂) ((f₂ ∘ p₂) ∘ pair g₁ g₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (p₁ ∘ pair g₁ g₂)) (f₂ ∘ (p₂ ∘ pair g₁ g₂))
    ≈⟨ pair-cong (∘-cong (isEquiv .refl) (pair-p₁ _ _)) (∘-cong (isEquiv .refl) (pair-p₂ _ _)) ⟩
      pair (f₁ ∘ g₁) (f₂ ∘ g₂)
    ∎ where open ≈-Reasoning isEquiv
            open IsEquivalence

  pair-functorial : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
    pair ((f₁ ∘ g₁) ∘ p₁) ((f₂ ∘ g₂) ∘ p₂) ≈ (pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))
  pair-functorial f₁ f₂ g₁ g₂ =
    begin
      pair ((f₁ ∘ g₁) ∘ p₁) ((f₂ ∘ g₂) ∘ p₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (g₁ ∘ p₁)) (f₂ ∘ (g₂ ∘ p₂))
    ≈⟨ isEquiv .sym (pair-cong (∘-cong (isEquiv .refl) (pair-p₁ _ _)) (∘-cong (isEquiv .refl) (pair-p₂ _ _))) ⟩
      pair (f₁ ∘ (p₁ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))) (f₂ ∘ (p₂ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)))
    ≈⟨ isEquiv .sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((f₁ ∘ p₁) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)) ((f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))
    ≈⟨ isEquiv .sym (pair-natural _ _ _) ⟩
      pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)
    ∎
    where open ≈-Reasoning isEquiv
          open IsEquivalence

  pair-ext0 : ∀ {x y} → pair p₁ p₂ ≈ id (prod x y)
  pair-ext0 = begin pair p₁ p₂
                      ≈⟨ isEquiv .sym (pair-cong id-right id-right) ⟩
                    pair (p₁ ∘ id _) (p₂ ∘ id _)
                      ≈⟨ pair-ext (id _) ⟩
                    id _ ∎
    where open ≈-Reasoning isEquiv
          open IsEquivalence

record HasStrongCoproducts {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {w x y z} → prod w x ⇒ z → prod w y ⇒ z → prod w (coprod x y) ⇒ z
    -- FIXME: equations

record HasBiproducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    prod   : obj → obj → obj
    p₁   : ∀ {x y} → prod x y ⇒ x
    p₂   : ∀ {x y} → prod x y ⇒ y
    pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ prod y z

    pair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ y} {g₁ g₂ : x ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-p₁ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₁ ∘ pair f g) ≈ f
    pair-p₂ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₂ ∘ pair f g) ≈ g
    pair-ext : ∀ {x y z} (f : x ⇒ prod y z) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

    in₁    : ∀ {x y} → x ⇒ prod x y
    in₂    : ∀ {x y} → y ⇒ prod x y
    copair : ∀ {x y z} → x ⇒ z → y ⇒ z → prod x y ⇒ z
    -- FIXME: equations

  hasProducts : HasProducts 𝒞
  hasProducts .HasProducts.prod = prod
  hasProducts .HasProducts.p₁ = p₁
  hasProducts .HasProducts.p₂ = p₂
  hasProducts .HasProducts.pair = pair
  hasProducts .HasProducts.pair-cong = pair-cong
  hasProducts .HasProducts.pair-p₁ = pair-p₁
  hasProducts .HasProducts.pair-p₂ = pair-p₂
  hasProducts .HasProducts.pair-ext = pair-ext

record HasExponentials {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    exp    : obj → obj → obj
    eval   : ∀ {x y} → prod x (exp x y) ⇒ y
    lambda : ∀ {x y z} → prod x y ⇒ z → x ⇒ exp y z
  -- FIXME: equations

-- FIXME: separate out 'endofunctor' and 'natural transformation'
record Monad {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    M    : obj → obj
    map  : ∀ {x y} → x ⇒ y → M x ⇒ M y
    unit : ∀ {x} → x ⇒ M x
    join : ∀ {x} → M (M x) ⇒ M x
    map-cong : ∀ {x y}{f g : x ⇒ y} → f ≈ g → map f ≈ map g
    map-id   : ∀ {x} → map (id x) ≈ id (M x)
    map-comp : ∀ {x y z} (f : y ⇒ z) (g : x ⇒ y) → map (f ∘ g) ≈ (map f ∘ map g)
    unit-natural : ∀ {x y} (f : x ⇒ y) → (unit ∘ f) ≈ (map f ∘ unit)
    join-natural : ∀ {x y} (f : x ⇒ y) → (join ∘ map (map f)) ≈ (map f ∘ join)
    -- FIXME: actual monad equations




record StrongMonad {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    M      : obj → obj
    unit   : ∀ {x} → x ⇒ M x
    extend : ∀ {x y z} → prod x y ⇒ M z → prod x (M y) ⇒ M z
  -- FIXME: equations
