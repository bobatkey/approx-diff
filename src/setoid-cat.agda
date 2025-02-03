{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import Data.Unit using (⊤; tt)
open import categories
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import fam

module setoid-cat where

open _⇒s_
open _≈s_

module _ o e where

  open Category

  SetoidCat : Category (suc o ⊔ suc e) (o ⊔ e) (o ⊔ e)
  SetoidCat .obj = Setoid o e
  SetoidCat ._⇒_ = _⇒s_
  SetoidCat ._≈_ = _≈s_
  SetoidCat .isEquiv = prop-setoid.≃m-isEquivalence
  SetoidCat .id = prop-setoid.idS
  SetoidCat ._∘_ = prop-setoid._∘S_
  SetoidCat .∘-cong = prop-setoid.∘S-cong
  SetoidCat .id-left = prop-setoid.id-left
  SetoidCat .id-right = prop-setoid.id-right
  SetoidCat .assoc = prop-setoid.assoc

  open HasTerminal

  Setoid-terminal : HasTerminal SetoidCat
  Setoid-terminal .witness = 𝟙
  Setoid-terminal .terminal-mor _ ._⇒s_.func _ = lift tt
  Setoid-terminal .terminal-mor _ ._⇒s_.func-resp-≈ _ = tt
  Setoid-terminal .terminal-unique X f g .prop-setoid._≃m_.func-eq _ = tt

  open HasProducts

  Setoid-products : HasProducts SetoidCat
  Setoid-products .prod = ⊗-setoid
  Setoid-products .p₁ = prop-setoid.project₁
  Setoid-products .p₂ = prop-setoid.project₂
  Setoid-products .pair = prop-setoid.pair
  Setoid-products .pair-cong = prop-setoid.pair-cong
  Setoid-products .pair-p₁ f g .func-eq = f .func-resp-≈
  Setoid-products .pair-p₂ f g .func-eq = g .func-resp-≈
  Setoid-products .pair-ext f .func-eq = f .func-resp-≈

  open HasCoproducts

  Setoid-coproducts : HasCoproducts SetoidCat
  Setoid-coproducts .coprod = +-setoid
  Setoid-coproducts .in₁ = prop-setoid.inject₁
  Setoid-coproducts .in₂ = prop-setoid.inject₂
  Setoid-coproducts .copair = prop-setoid.copair
  Setoid-coproducts .copair-cong = prop-setoid.copair-cong
  Setoid-coproducts .copair-in₁ = prop-setoid.copair-in₁
  Setoid-coproducts .copair-in₂ = prop-setoid.copair-in₂
  Setoid-coproducts .copair-ext = prop-setoid.copair-ext

-- FIXME: Setoid-exponentials

module _ {o e} where
  open Setoid
  open IsEquivalence
  open Fam
  open _⇒f_
  open _≃f_

  record ΠS-Carrier (A : Setoid o e) (F : Fam A (SetoidCat (o ⊔ e) (o ⊔ e))) : Set (o ⊔ e) where
    field
      Π-func : (a : A .Carrier) → F .fm a .Carrier
      Π-eq   : ∀ {a₁ a₂} (e : A ._≈_ a₁ a₂) → F .fm a₂ ._≈_ (F .subst e .func (Π-func a₁)) (Π-func a₂)
  open ΠS-Carrier

  ΠS : (A : Setoid o e) (F : Fam A (SetoidCat (o ⊔ e) (o ⊔ e))) → Setoid (o ⊔ e) (o ⊔ e)
  ΠS A F .Carrier = ΠS-Carrier A F
  ΠS A F ._≈_ f₁ f₂ = ∀ a → F .fm a ._≈_ (f₁ .Π-func a) (f₂ .Π-func a)
  ΠS A F .isEquivalence .refl {f} a = F .fm a .refl
  ΠS A F .isEquivalence .sym {f₁} {f₂} f₁≈f₂ a = F .fm a .sym (f₁≈f₂ a)
  ΠS A F .isEquivalence .trans f₁≈f₂ f₂≈f₃ a = F .fm a .trans (f₁≈f₂ a) (f₂≈f₃ a)

  Setoid-BigProducts : HasSetoidProducts o e (SetoidCat (o ⊔ e) (o ⊔ e))
  Setoid-BigProducts .HasSetoidProducts.Π = ΠS
  Setoid-BigProducts .HasSetoidProducts.lambdaΠ {A} Γ F f .func γ .Π-func a = f .transf a .func γ
  Setoid-BigProducts .HasSetoidProducts.lambdaΠ {A} Γ F f .func γ .Π-eq {a₁} {a₂} a₁≈a₂ =
    F .fm a₂ .sym (f .natural a₁≈a₂ .func-eq (Γ .refl))
  Setoid-BigProducts .HasSetoidProducts.lambdaΠ {A} Γ F f .func-resp-≈ γ₁≈γ₂ a = f .transf a .func-resp-≈ γ₁≈γ₂
  Setoid-BigProducts .HasSetoidProducts.lambdaΠ-cong f₁≈f₂ .func-eq x₁≈x₂ a = f₁≈f₂ .transf-eq .func-eq x₁≈x₂
  Setoid-BigProducts .HasSetoidProducts.evalΠ P a .func f = f .Π-func a
  Setoid-BigProducts .HasSetoidProducts.evalΠ P a .func-resp-≈ f₁≈f₂ = f₁≈f₂ a
  Setoid-BigProducts .HasSetoidProducts.evalΠ-cong {A} {P} {a₁} {a₂} a₁≈a₂ .func-eq {f₁} {f₂} f₁≈f₂ =
    P .fm a₂ .trans (f₁ .Π-eq a₁≈a₂) (f₁≈f₂ a₂)
  Setoid-BigProducts .HasSetoidProducts.lambda-eval {f = f} a .func-eq = f .transf a .func-resp-≈
  Setoid-BigProducts .HasSetoidProducts.lambda-ext {f = f} .func-eq = f .func-resp-≈

open import functor using (HasLimits; Functor; NatTrans; ≃-NatTrans)

-- Setoid categories have all "smaller" limits
module _ {o m e} os (𝒟 : Category o m e) where

  ℓ : Level
  ℓ = os ⊔ o ⊔ m ⊔ e

  private
    module 𝒟 = Category 𝒟
  open Functor
  open NatTrans
  open ≃-NatTrans
  open Setoid
  open IsEquivalence

  record Π-Carrier (F : Functor 𝒟 (SetoidCat ℓ ℓ)) : Set ℓ where
    field
      Π-func : (x : 𝒟.obj) → F .fobj x .Carrier
      Π-eq   : ∀ {x₁ x₂} (f : x₁ 𝒟.⇒ x₂) → F .fobj x₂ ._≈_ (F .fmor f .func (Π-func x₁)) (Π-func x₂)
  open Π-Carrier

  Π : Functor 𝒟 (SetoidCat ℓ ℓ) → Setoid ℓ ℓ
  Π F .Carrier = Π-Carrier F
  Π F ._≈_ f₁ f₂ = ∀ x → F .fobj x ._≈_ (f₁ .Π-func x) (f₂ .Π-func x)
  Π F .isEquivalence .refl {f} a = F .fobj a .refl
  Π F .isEquivalence .sym {f₁} {f₂} f₁≈f₂ a = F .fobj a .sym (f₁≈f₂ a)
  Π F .isEquivalence .trans f₁≈f₂ f₂≈f₃ a = F .fobj a .trans (f₁≈f₂ a) (f₂≈f₃ a)

  Setoid-Limit : HasLimits 𝒟 (SetoidCat ℓ ℓ)
  Setoid-Limit .HasLimits.Π = Π
  Setoid-Limit .HasLimits.lambdaΠ A F α .func a .Π-func x = α .transf x .func a
  Setoid-Limit .HasLimits.lambdaΠ A F α .func a .Π-eq {x₁} {x₂} f =
    begin
      F .fmor f .func (α .transf x₁ .func a)
    ≈⟨ α .natural f .func-eq (A .refl) ⟩
      α .transf x₂ .func a
    ∎ where open ≈-Reasoning (F .fobj x₂ .isEquivalence)
  Setoid-Limit .HasLimits.lambdaΠ A F α .func-resp-≈ a₁≈a₂ x =
    α .transf x .func-resp-≈ a₁≈a₂
  Setoid-Limit .HasLimits.evalΠ F .transf x .func f = f .Π-func x
  Setoid-Limit .HasLimits.evalΠ F .transf x .func-resp-≈ f₁≈f₂ = f₁≈f₂ x
  Setoid-Limit .HasLimits.evalΠ F .natural {x} {y} g .func-eq {f₁} {f₂} f₁≈f₂ =
    F .fobj y .trans (f₁ .Π-eq g) (f₁≈f₂ y)
  Setoid-Limit .HasLimits.lambda-cong α≃β .func-eq x₁≈x₂ x = α≃β .transf-eq x .func-eq x₁≈x₂
  Setoid-Limit .HasLimits.lambda-eval α .transf-eq x .func-eq = α .transf x .func-resp-≈
  Setoid-Limit .HasLimits.lambda-ext f .func-eq = f .func-resp-≈

-- FIXME: Setoid-CoLimits
