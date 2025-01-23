{-# OPTIONS --prop --postfix-projections #-}

open import Level
open import Data.Unit using (⊤; tt)
open import categories
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)

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
