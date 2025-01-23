{-# OPTIONS --prop --postfix-projections --safe #-}

module prop-setoid where

open import Level
open import prop
open import Data.Unit using (tt) renaming (⊤ to 𝟙S)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using () renaming (⊥ to 𝟘)
open import Data.Product using (_×_; proj₁; proj₂; _,_)

record IsEquivalence {o e} {A : Set o} (_≈_ : A → A → Prop e) : Set (o ⊔ e) where
  field
    refl : ∀ {x} → x ≈ x
    sym  : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
open IsEquivalence

module ≈-Reasoning {o e} {A : Set o} {_≈_ : A → A → Prop e} (equiv : IsEquivalence _≈_) where

  infix  1 begin_
  infixr 2 _≈⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≈ y
      -----
    → x ≈ y
  begin x≈y  =  x≈y

  _≈⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≈ y
    → y ≈ z
      -----
    → x ≈ z
  x ≈⟨ x≈y ⟩ y≈z  =  equiv .trans x≈y y≈z

  _∎ : ∀ (x : A)
      -----
    → x ≈ x
  x ∎  =  equiv .refl

record Setoid o e : Set (suc (o ⊔ e)) where
  no-eta-equality
  field
    Carrier : Set o
    _≈_     : Carrier → Carrier → Prop e
    isEquivalence : IsEquivalence _≈_
  open IsEquivalence isEquivalence public
open Setoid

-- liftSetoid : ∀ {o e} o' e' → Setoid o e → Setoid (o ⊔ o') (e ⊔ e')
-- liftSetoid o' e' x .Carrier = {!!}
-- liftSetoid o' e' x ._≈_ = {!!}
-- liftSetoid o' e' x .isEquivalence = {!!}

record _⇒_ {o₁ e₁ o₂ e₂} (X : Setoid o₁ e₁) (Y : Setoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where
  no-eta-equality
  private
    module X = Setoid X
    module Y = Setoid Y
  field
    func : X.Carrier → Y.Carrier
    func-resp-≈ : ∀ {x₁ x₂} → x₁ X.≈ x₂ → func x₁ Y.≈ func x₂
open _⇒_

module _ {o e} where

  record _≃m_ {X Y : Setoid o e} (f g : X ⇒ Y) : Prop (o ⊔ e) where
    private
      module X = Setoid X
      module Y = Setoid Y
    field
      func-eq : ∀ {x₁ x₂} → x₁ X.≈ x₂ → f .func x₁ Y.≈ g .func x₂
  open _≃m_

  ≃m-isEquivalence : ∀ {X Y : Setoid o e} → IsEquivalence (_≃m_ {X} {Y})
  ≃m-isEquivalence {X} {Y} .refl {f} .func-eq = f .func-resp-≈
  ≃m-isEquivalence {X} {Y} .sym {f} {g} f≈g .func-eq x₁≈x₂ = Y .sym (f≈g .func-eq (X .sym x₁≈x₂))
  ≃m-isEquivalence {X} {Y} .trans {f} {g} {h} f≈g g≈h .func-eq x₁≈x₂ = Y .trans (f≈g .func-eq x₁≈x₂) (g≈h .func-eq (X .refl))

  idS : ∀ (X : Setoid o e) → X ⇒ X
  idS X .func x = x
  idS X .func-resp-≈ e = e

  _∘S_ : ∀ {X Y Z : Setoid o e} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  (f ∘S g) .func x = f .func (g .func x)
  (f ∘S g) .func-resp-≈ e = f .func-resp-≈ (g .func-resp-≈ e)

  ∘S-cong : ∀ {X Y Z : Setoid o e} {f₁ f₂ : Y ⇒ Z} {g₁ g₂ : X ⇒ Y} →
    f₁ ≃m f₂  → g₁ ≃m g₂ → (f₁ ∘S g₁) ≃m (f₂ ∘S g₂)
  ∘S-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ =
    f₁≈f₂ .func-eq (g₁≈g₂ .func-eq x₁≈x₂)

  id-left : ∀ {X Y : Setoid o e} {f : X ⇒ Y} → (idS Y ∘S f) ≃m f
  id-left {X} {Y} {f} .func-eq = f .func-resp-≈

  id-right : ∀ {X Y : Setoid o e} {f : X ⇒ Y} → (f ∘S idS X) ≃m f
  id-right {X} {Y} {f} .func-eq = f .func-resp-≈

  assoc : ∀ {W X Y Z : Setoid o e} (f : Y ⇒ Z) (g : X ⇒ Y) (h : W ⇒ X) →
      ((f ∘S g) ∘S h) ≃m (f ∘S (g ∘S h))
  assoc f g h .func-eq w₁≈w₂ = f .func-resp-≈ (g .func-resp-≈ (h .func-resp-≈ w₁≈w₂))

module _ {o e} where

  𝟙 : Setoid o e
  𝟙 .Carrier = Lift _ 𝟙S
  𝟙 ._≈_ _ _ = ⊤
  𝟙 .isEquivalence .refl = tt
  𝟙 .isEquivalence .sym _ = tt
  𝟙 .isEquivalence .trans _ _ = tt

  to-𝟙 : ∀ {X : Setoid o e} → X ⇒ 𝟙
  to-𝟙 .func _ = lift tt
  to-𝟙 .func-resp-≈ _ = tt

  to-𝟙-unique : ∀ {X : Setoid o e} (f g : X ⇒ 𝟙) → f ≃m g
  to-𝟙-unique f g ._≃m_.func-eq _ = tt

  const : (X : Setoid o e) → X .Carrier → 𝟙 ⇒ X
  const X x .func _ = x
  const X x .func-resp-≈ tt = X .refl

+-setoid : ∀ {a b c d} (X : Setoid a b) (Y : Setoid c d) → Setoid (a ⊔ c) (b ⊔ d)
+-setoid X Y .Carrier = X .Carrier ⊎ Y .Carrier
+-setoid {a} {b} {c} {d} X Y ._≈_ (inj₁ x) (inj₁ y) = LiftP (b ⊔ d) (X ._≈_ x y)
+-setoid {a} {b} {c} {d} X Y ._≈_ (inj₂ x) (inj₂ y) = LiftP (b ⊔ d) (Y ._≈_ x y)
+-setoid X Y ._≈_ (inj₁ x) (inj₂ y) = ⊥
+-setoid X Y ._≈_ (inj₂ x) (inj₁ y) = ⊥
+-setoid X Y .isEquivalence .refl {inj₁ x} .lower = X .isEquivalence .refl
+-setoid X Y .isEquivalence .refl {inj₂ x} .lower = Y .isEquivalence .refl
+-setoid X Y .isEquivalence .sym {inj₁ x} {inj₁ y} x≈y .lower = X .isEquivalence .sym (x≈y .lower)
+-setoid X Y .isEquivalence .sym {inj₂ x} {inj₂ y} x≈y .lower = Y .isEquivalence .sym (x≈y .lower)
+-setoid X Y .isEquivalence .trans {inj₁ x} {inj₁ y} {inj₁ z} x≈y y≈z .lower =
    X .isEquivalence .trans (x≈y .lower) (y≈z .lower)
+-setoid X Y .isEquivalence .trans {inj₂ x} {inj₂ y} {inj₂ z} x≈y y≈z .lower =
    Y .isEquivalence .trans (x≈y .lower) (y≈z .lower)

inject₁ : ∀ {o e} {X Y : Setoid o e} → X ⇒ +-setoid X Y
inject₁ .func = inj₁
inject₁ .func-resp-≈ = lift

inject₂ : ∀ {o e} {X Y : Setoid o e} → Y ⇒ +-setoid X Y
inject₂ .func = inj₂
inject₂ .func-resp-≈ = lift

copair : ∀ {o e} {X Y Z : Setoid o e} → X ⇒ Z → Y ⇒ Z → +-setoid X Y ⇒ Z
copair f g .func (inj₁ x) = f .func x
copair f g .func (inj₂ y) = g .func y
copair f g .func-resp-≈ {inj₁ x} {inj₁ x₁} (lift e) = f .func-resp-≈ e
copair f g .func-resp-≈ {inj₂ y} {inj₂ y₁} (lift e) = g .func-resp-≈ e

⊗-setoid : ∀ {a b c d} → Setoid a b → Setoid c d → Setoid (a ⊔ c) (b ⊔ d)
⊗-setoid X Y .Carrier = X .Carrier × Y .Carrier
⊗-setoid X Y ._≈_ (x₁ , y₁) (x₂ , y₂) = X ._≈_ x₁ x₂ ∧ Y ._≈_ y₁ y₂
⊗-setoid X Y .isEquivalence .refl .proj₁ = X .isEquivalence .refl
⊗-setoid X Y .isEquivalence .refl .proj₂ = Y .isEquivalence .refl
⊗-setoid X Y .isEquivalence .sym (x₁≈y₁ , _) .proj₁ = X .isEquivalence .sym x₁≈y₁
⊗-setoid X Y .isEquivalence .sym (_ , x₂≈y₂) .proj₂ = Y .isEquivalence .sym x₂≈y₂
⊗-setoid X Y .isEquivalence .trans (x₁≈y₁ , _) (y₁≈z₁ , _) .proj₁ = X .isEquivalence .trans x₁≈y₁ y₁≈z₁
⊗-setoid X Y .isEquivalence .trans (_ , x₂≈y₂) (_ , y₂≈z₂) .proj₂ = Y .isEquivalence .trans x₂≈y₂ y₂≈z₂

project₁ : ∀ {o e} {X Y : Setoid o e} → ⊗-setoid X Y ⇒ X
project₁ .func = proj₁
project₁ .func-resp-≈ = proj₁

project₂ : ∀ {o e} {X Y : Setoid o e} → ⊗-setoid X Y ⇒ Y
project₂ .func = proj₂
project₂ .func-resp-≈ = proj₂

pair : ∀ {o e} {X Y Z : Setoid o e} → X ⇒ Y → X ⇒ Z → X ⇒ ⊗-setoid Y Z
pair f g .func x = f .func x , g .func x
pair f g .func-resp-≈ e = f .func-resp-≈ e , g .func-resp-≈ e

open _≃m_

pair-cong : ∀ {o e} {X Y Z : Setoid o e} {f₁ f₂ : X ⇒ Y} {g₁ g₂ : X ⇒ Z} →
  f₁ ≃m f₂ → g₁ ≃m g₂ → pair f₁ g₁ ≃m pair f₂ g₂
pair-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ .proj₁ = f₁≈f₂ .func-eq x₁≈x₂
pair-cong f₁≈f₂ g₁≈g₂ .func-eq x₁≈x₂ .proj₂ = g₁≈g₂ .func-eq x₁≈x₂

-- Strong coproducts
case : ∀ {o e} {W X Y Z : Setoid o e} →
          (⊗-setoid W X) ⇒ Z →
          (⊗-setoid W Y) ⇒ Z →
          (⊗-setoid W (+-setoid X Y)) ⇒ Z
case f g .func (w , inj₁ x) = f .func (w , x)
case f g .func (w , inj₂ y) = g .func (w , y)
case f g .func-resp-≈ {w₁ , inj₁ x₁} {w₂ , inj₁ x₂} (w₁≈w₂ , lift x₁≈x₂) = f .func-resp-≈ (w₁≈w₂ , x₁≈x₂)
case f g .func-resp-≈ {w₁ , inj₂ y₁} {w₂ , inj₂ y₂} (w₁≈w₂ , lift y₁≈y₂) = g .func-resp-≈ (w₁≈w₂ , y₁≈y₂)
