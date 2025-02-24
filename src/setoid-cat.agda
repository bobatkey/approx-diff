{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import Data.Unit using (⊤; tt)
open import categories
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning;
         rel→Setoid; EquivOf-intro; rel-preserving-func)
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

open import functor using (HasLimits; Functor; NatTrans; ≃-NatTrans; Colimit; IsColimit)

-- Setoid categories have all "smaller" limits
module _ {o m e} os (𝒟 : Category o m e) where

  private
    ℓ : Level
    ℓ = o ⊔ m ⊔ os

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

-- Colimits
module _ {o m e} os (𝒮 : Category o m e) where

  private
    ℓ : Level
    ℓ = o ⊔ m ⊔ os

  private
    module 𝒮 = Category 𝒮
  open Functor
  open NatTrans
  open ≃-NatTrans
  open Setoid
  open IsEquivalence
  open import Data.Product using (Σ-syntax; proj₁; proj₂; _,_)

  open Colimit
  open IsColimit

  ∐ : (D : Functor 𝒮 (SetoidCat ℓ ℓ)) → Setoid ℓ ℓ
  ∐ D = prop-setoid.rel→Setoid
          (Σ[ x ∈ 𝒮.obj ] D .fobj x .Carrier)
          (λ { (x₁ , dx₁) (x₂ , dx₂) →
             ∃ (x₁ 𝒮.⇒ x₂) λ f → D .fobj x₂ ._≈_ (D .fmor f .func dx₁) dx₂  })

  Setoid-Colimit : (D : Functor 𝒮 (SetoidCat ℓ ℓ)) → Colimit D
  Setoid-Colimit D .apex = ∐ D
  Setoid-Colimit D .cocone .transf x .func dx = x , dx
  Setoid-Colimit D .cocone .transf x .func-resp-≈ dx₁≈dx₂ =
    EquivOf-intro (𝒮.id x , D .fmor-id .func-eq dx₁≈dx₂)
  Setoid-Colimit D .cocone .natural f .func-eq dx₁≈dx₂ =
    EquivOf-intro (f , D .fmor f .func-resp-≈ dx₁≈dx₂)
  Setoid-Colimit D .isColimit .colambda X α =
    rel-preserving-func X (λ { (x , dx) → α .transf x .func dx })
      λ { {x₁ , dx₁} {x₂ , dx₂} (f , eq) →
          X .trans (α .natural f .func-eq (D .fobj x₁ .refl))
                   (α .transf x₂ .func-resp-≈ eq) }
  Setoid-Colimit D .isColimit .colambda-cong {X} {α} {β} α≈β .func-eq {x₁ , dx₁} {x₂ , dx₂} (liftS eq) =
    X .trans (α≈β .transf-eq x₁ .func-eq (D .fobj x₁ .refl))
             (prop-setoid.elim-EquivOfS X
                (λ xdx → β .transf (xdx .proj₁) .func (xdx .proj₂))
                (λ { {x₁ , dx₁} {x₂ , dx₂} (f , eq) →
                  X .trans (β .natural f .func-eq (D .fobj x₁ .refl))
                           (β .transf x₂ .func-resp-≈ eq) })
                eq)
  Setoid-Colimit D .isColimit .colambda-coeval X α .transf-eq x .func-eq =
    α .transf x .func-resp-≈
  Setoid-Colimit D .isColimit .colambda-ext X f .func-eq = f .func-resp-≈
