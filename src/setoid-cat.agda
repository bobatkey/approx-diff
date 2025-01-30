{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import Data.Unit using (⊤; tt)
open import categories
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_)
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

-- FIXME: Setoid-BigSums
