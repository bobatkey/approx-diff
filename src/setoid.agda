{-# OPTIONS --postfix-projections --safe --without-K #-}

-- Setoid gunk that may overlap somewhat with stdlib
module setoid where

open import Level
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open Setoid
open IsEquivalence

module ≃-Reasoning = Relation.Binary.Reasoning.Setoid

≡-to-≈ : ∀ {a b} (X : Setoid a b) {x y : X .Carrier} → x ≡ y → X ._≈_ x y
≡-to-≈ X {x} {.x} ≡-refl = X .isEquivalence .refl

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

{-
record _⇒_ {a b} (X Y : Setoid a b) : Set (a ⊔ b) where
  field
    func : X .Carrier → Y .Carrier
    func-resp-≈ : ∀ {x y} → X ._≈_ x y → Y ._≈_ (func x) (func y)

open _⇒_

record _≃m_ {a b} {X Y : Setoid a b} (f g : X ⇒ Y) : Set (suc (a ⊔ b)) where
  field
    eqfunc : ∀ x → Y ._≈_ (f .func x) (g .func x)

open _≃m_

id : ∀ {a b} {X : Setoid a b} → X ⇒ X
id .func x = x
id .func-resp-≈ x = x

_∘_ : ∀ {a b} {X Y Z : Setoid a b} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .func-resp-≈ x = f .func-resp-≈ (g .func-resp-≈ x)

record Iso {a b} (X Y : Setoid a b) : Set (suc (a ⊔ b)) where
  field
    right : X ⇒ Y
    left : Y ⇒ X
    isoᵣ : (right ∘ left) ≃m id
    isoₗ : (left ∘ right) ≃m id

open Iso

-- For a setoid-indexed family of setoids, each proof p : i = j gives rise to an extensional
-- "reindexing" bijection φ p : X i → X j.
record Resp-≈ {a b} (I : Setoid a b) (X : I .Carrier → Setoid a b) : Set (suc (a ⊔ b)) where
  field
    eq : ∀ {i j} → I ._≈_ i j → Iso (X i) (X j)
    -- proof irrelevance:
    eq-refl : ∀ {i} → (eq (I .isEquivalence .refl {i}) .right) ≃m id
    eq-trans : ∀ {i j k} → (p : I ._≈_ i j) (q : I ._≈_ j k) (r : I ._≈_ i k) →
                (eq q .right ∘ eq p .right) ≃m eq r .right

open Resp-≈

-- Coproduct of setoid-indexed family of setoids
∐-setoid : ∀ {a b} (I : Setoid a b) (X : I .Carrier → Setoid a b) → Resp-≈ I X → Setoid a b
∐-setoid I X resp-≈ .Carrier = Σ (I .Carrier) λ i → X i .Carrier
∐-setoid I X resp-≈ ._≈_ (i , x) (j , y) =
  Σ (I ._≈_ i j) λ p → X j ._≈_ (resp-≈ .eq p .Iso.right .func x) y
∐-setoid I X resp-≈ .isEquivalence .refl .proj₁ = I .isEquivalence .refl
∐-setoid I X resp-≈ .isEquivalence .refl {i , x} .proj₂ = resp-≈ .eq-refl {i} .eqfunc x
∐-setoid I X resp-≈ .isEquivalence .sym (i≈j , x≈y) .proj₁ = I .isEquivalence .sym i≈j
∐-setoid I X resp-≈ .isEquivalence .sym {i , x} {j , y} (i≈j , x≈y) .proj₂ =
  begin
    resp-≈ .eq (I .isEquivalence .sym i≈j) .right .func y
  ≈⟨ resp-≈ .eq (I .isEquivalence .sym i≈j) .right .func-resp-≈ (X j .isEquivalence .sym x≈y) ⟩
    resp-≈ .eq (I .isEquivalence .sym i≈j) .right .func (resp-≈ .eq i≈j .right .func x)
  ≈⟨ resp-≈ .eq-trans i≈j (I .isEquivalence .sym i≈j) (I .isEquivalence .refl {i}) .eqfunc x ⟩
    resp-≈ .eq (I .isEquivalence .refl) .right .func x
  ≈⟨ resp-≈ .eq-refl {i} .eqfunc x ⟩
    x
  ∎
  where open ≃-Reasoning (X i)
∐-setoid I X resp-≈ .isEquivalence .trans (i≈j , x≈y) (j≈k , y≈z) .proj₁ =
  I .isEquivalence .trans i≈j j≈k
∐-setoid I X resp-≈ .isEquivalence .trans {i , x} {j , y} {k , z} (i≈j , x≈y) (j≈k , y≈z) .proj₂ =
  X k .isEquivalence .trans
    (X k .isEquivalence .sym (resp-≈ .eq-trans i≈j j≈k (I .isEquivalence .trans i≈j j≈k) .eqfunc x))
    (X k .isEquivalence .trans (resp-≈ .eq j≈k .right .func-resp-≈ x≈y) y≈z)
-}
