{-# OPTIONS --postfix-projections --safe --without-K #-}

-- Setoid gunk that may overlap somewhat with stdlib
module setoid where

open import Level
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid
open import Relation.Binary.PropositionalEquality
   using (_≡_)
   renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open Setoid
open IsEquivalence

module ≃-Reasoning = Relation.Binary.Reasoning.Setoid

≡-to-≈ : ∀ {a b} (X : Setoid a b) {x y : X .Carrier} → x ≡ y → X ._≈_ x y
≡-to-≈ X {x} {.x} ≡-refl = X .isEquivalence .refl

record _⇒_ {a b} (X Y : Setoid a b) : Set (a ⊔ b) where
  field
    func : X .Carrier → Y .Carrier
    func-resp-≈ : ∀ {x y} → X ._≈_ x y → Y ._≈_ (func x) (func y)

ofSet : ∀ {a} → Set a → Setoid a a
ofSet X .Carrier = X
ofSet X ._≈_ = _≡_
ofSet X .isEquivalence .refl = ≡-refl
ofSet X .isEquivalence .sym = ≡-sym
ofSet X .isEquivalence .trans = ≡-trans

⊤-setoid : ∀ {a b} → Setoid a b
⊤-setoid .Carrier = Lift _ ⊤
⊤-setoid ._≈_ _ _ = Lift _ ⊤
⊤-setoid .isEquivalence .refl = lift tt
⊤-setoid .isEquivalence .sym _ = lift tt
⊤-setoid .isEquivalence .trans _ _ = lift tt

⊗-setoid : ∀ {a b c d} → Setoid a b → Setoid c d → Setoid (a ⊔ c) (b ⊔ d)
⊗-setoid X Y .Carrier = X .Carrier × Y .Carrier
⊗-setoid X Y ._≈_ (x₁ , y₁) (x₂ , y₂) = X ._≈_ x₁ x₂ × Y ._≈_ y₁ y₂
⊗-setoid X Y .isEquivalence .refl .proj₁ = X .isEquivalence .refl
⊗-setoid X Y .isEquivalence .refl .proj₂ = Y .isEquivalence .refl
⊗-setoid X Y .isEquivalence .sym (x₁≈y₁ , _) .proj₁ = X .isEquivalence .sym x₁≈y₁
⊗-setoid X Y .isEquivalence .sym (_ , x₂≈y₂) .proj₂ = Y .isEquivalence .sym x₂≈y₂
⊗-setoid X Y .isEquivalence .trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = X .isEquivalence .trans x₁≈y₁ y₁≈z₁
⊗-setoid X Y .isEquivalence .trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = Y .isEquivalence .trans x₂≈y₂ y₂≈z₂

+-setoid : ∀ {a b c d} (X : Setoid a b) (Y : Setoid c d) → Setoid (a ⊔ c) (b ⊔ d)
+-setoid X Y .Carrier = X .Carrier ⊎ Y .Carrier
+-setoid {a} {b} {c} {d} X Y ._≈_ (inj₁ x) (inj₁ y) = Lift (b ⊔ d) (X ._≈_ x y)
+-setoid {a} {b} {c} {d} X Y ._≈_ (inj₂ x) (inj₂ y) = Lift (b ⊔ d) (Y ._≈_ x y)
+-setoid X Y ._≈_ (inj₁ x) (inj₂ y) = Lift _ 𝟘
+-setoid X Y ._≈_ (inj₂ x) (inj₁ y) = Lift _ 𝟘
+-setoid X Y .isEquivalence .refl {inj₁ x} .lower = X .isEquivalence .refl
+-setoid X Y .isEquivalence .refl {inj₂ x} .lower = Y .isEquivalence .refl
+-setoid X Y .isEquivalence .sym {inj₁ x} {inj₁ y} x≈y .lower = X .isEquivalence .sym (x≈y .lower)
+-setoid X Y .isEquivalence .sym {inj₂ x} {inj₂ y} x≈y .lower = Y .isEquivalence .sym (x≈y .lower)
+-setoid X Y .isEquivalence .trans {inj₁ x} {inj₁ y} {inj₁ z} x≈y y≈z .lower =
  X .isEquivalence .trans (x≈y .lower) (y≈z .lower)
+-setoid X Y .isEquivalence .trans {inj₂ x} {inj₂ y} {inj₂ z} x≈y y≈z .lower =
  Y .isEquivalence .trans (x≈y .lower) (y≈z .lower)
