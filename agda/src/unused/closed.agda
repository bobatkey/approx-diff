{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using () renaming (_⊔_ to _⊔ℓ_)
open import prop using (proj₁; proj₂)
open import basics
  using (IsPreorder; IsMonoid; IsResidual; IsClosureOp; module ≤-Reasoning;
         IsMeet; IsJoin; IsBigMeet; IsBigJoin; IsExponential)

module closed {aℓ bℓ}
  {A : Set aℓ}
  {_≤_ : A → A → Prop bℓ} (≤-isPreorder : IsPreorder _≤_)
  {𝐂 : A → A} (𝐂-isClosure : IsClosureOp ≤-isPreorder 𝐂)
  where

open IsPreorder ≤-isPreorder
open IsClosureOp 𝐂-isClosure
  renaming ( mono to 𝐂-mono
           ; unit to 𝐂-unit
           ; closed to 𝐂-join )

------------------------------------------------------------------------------
record Elt : Set (aℓ ⊔ℓ bℓ) where
  no-eta-equality
  field
    elt    : A
    closed : 𝐂 elt ≤ elt
open Elt

record _⊑_ (X Y : Elt) : Prop bℓ where
  no-eta-equality
  field
    *≤* : X .elt ≤ Y .elt
open _⊑_

⊑-isPreorder : IsPreorder _⊑_
⊑-isPreorder .IsPreorder.refl .*≤* = refl
⊑-isPreorder .IsPreorder.trans x≤y y≤z .*≤* = trans (x≤y .*≤*) (y≤z .*≤*)

------------------------------------------------------------------------------
-- Meets and Joins
-- FIXME: do ⊤ and ⊥
module meets {_∧_} (∧-isMeet : IsMeet ≤-isPreorder _∧_) where
  open IsMeet ∧-isMeet using (π₁; π₂; ⟨_,_⟩)

  _⊓_ : Elt → Elt → Elt
  (x ⊓ y) .elt = x .elt ∧ y .elt
  (x ⊓ y) .closed = ⟨ trans (𝐂-mono π₁) (x .closed) ,
                      trans (𝐂-mono π₂) (y .closed) ⟩

  ⊓-isMeet : IsMeet ⊑-isPreorder _⊓_
  ⊓-isMeet .IsMeet.π₁ .*≤* = π₁
  ⊓-isMeet .IsMeet.π₂ .*≤* = π₂
  ⊓-isMeet .IsMeet.⟨_,_⟩ x⊑y x⊑z .*≤* = ⟨ x⊑y .*≤* , x⊑z .*≤* ⟩

module bigmeets {ℓ ⋀} (⋀-isBigMeet : IsBigMeet ≤-isPreorder ℓ ⋀) where
  open IsBigMeet ⋀-isBigMeet

  ⋂ : (I : Set ℓ) → (I → Elt) → Elt
  ⋂ I e .elt = ⋀ I λ i → e i .elt
  ⋂ I e .closed = greatest _ _ _ λ i → trans (𝐂-mono (lower _ _ i)) (e i .closed)

  ⋂-isBigMeet : IsBigMeet ⊑-isPreorder ℓ ⋂
  ⋂-isBigMeet .IsBigMeet.lower I x i .*≤* = lower _ _ i
  ⋂-isBigMeet .IsBigMeet.greatest I x z z⊑x .*≤* = greatest _ _ _ (λ i → z⊑x i .*≤*)


module joins {_∨_} (∨-isJoin : IsJoin ≤-isPreorder _∨_) where
  open IsJoin ∨-isJoin using (inl; inr; [_,_])

  _⊔_ : Elt → Elt → Elt
  (x ⊔ y) .elt = 𝐂 (x .elt ∨ y .elt)
  (x ⊔ y) .closed = 𝐂-join

  ⊔-isJoin : IsJoin ⊑-isPreorder _⊔_
  ⊔-isJoin .IsJoin.inl .*≤* = trans inl 𝐂-unit
  ⊔-isJoin .IsJoin.inr .*≤* = trans inr 𝐂-unit
  ⊔-isJoin .IsJoin.[_,_] {x} {y} {z} x⊑z y⊑z .*≤* =
    trans (𝐂-mono [ x⊑z .*≤* , y⊑z .*≤* ]) (z .closed)

  -- When are joins preserved? What makes it possible to preserve
  -- joins from the original preorder in the case that 'A' is a
  -- downset lattice?

module bigjoins {ℓ ⋁} (⋁-isBigJoin : IsBigJoin ≤-isPreorder ℓ ⋁) where
  open IsBigJoin ⋁-isBigJoin

  ⋃ : (I : Set ℓ) → (I → Elt) → Elt
  ⋃ I e .elt = 𝐂 (⋁ I (λ i → e i .elt))
  ⋃ I e .closed = 𝐂-join

  ⋃-isBigJoin : IsBigJoin ⊑-isPreorder ℓ ⋃
  ⋃-isBigJoin .IsBigJoin.upper I e i .*≤* = trans (upper _ _ i) 𝐂-unit
  ⋃-isBigJoin .IsBigJoin.least I e z x⊑z .*≤* = trans (𝐂-mono (least _ _ _ λ i → x⊑z i .*≤*)) (z .closed)

------------------------------------------------------------------------------
-- FIXME: Distributivity
--   - meet and join only distribute if 𝐂 preserves meets
--   - .. and a residual for ∧ is likewise only preserved in that case
--   - If join and a monoid commuted before, then they still do now
--   - And duoidal relationships...

------------------------------------------------------------------------------
-- Monoids
--
-- FIXME: probably another version for when 𝐂 x ∙ 𝐂 y ≃ 𝐂 (x ∙ y)
module monoid
    {_∙_ ε} (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε)
    (comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
    (𝐂-strong : ∀ {x y} → (x ∙ 𝐂 y) ≤ 𝐂 (x ∙ y))
  where

  open IsMonoid ∙-isMonoid

  𝐂-strong' : ∀ {X Y} → (𝐂 X ∙ Y) ≤ 𝐂 (X ∙ Y)
  𝐂-strong' {X} {Y} = begin
      𝐂 X ∙ Y    ≤⟨ comm ⟩
      Y ∙ 𝐂 X    ≤⟨ 𝐂-strong ⟩
      𝐂 (Y ∙ X)  ≤⟨ 𝐂-mono comm ⟩
      𝐂 (X ∙ Y)  ∎
    where open ≤-Reasoning ≤-isPreorder

  𝐂-monoidal : ∀ {X Y} → (𝐂 X ∙ 𝐂 Y) ≤ 𝐂 (X ∙ Y)
  𝐂-monoidal {X} {Y} = begin
      𝐂 X ∙ 𝐂 Y        ≤⟨ 𝐂-strong ⟩
      𝐂 (𝐂 X ∙ Y)      ≤⟨ 𝐂-mono 𝐂-strong' ⟩
      𝐂 (𝐂 (X ∙ Y))    ≤⟨ 𝐂-join ⟩
      𝐂 (X ∙ Y)         ∎
    where open ≤-Reasoning ≤-isPreorder

  _⊗_ : Elt → Elt → Elt
  (x ⊗ y) .elt = 𝐂 (x .elt ∙ y .elt)
  (x ⊗ y) .closed = 𝐂-join

  I : Elt
  I .elt = 𝐂 ε
  I .closed = 𝐂-join

  ⊗-isMonoid : IsMonoid ⊑-isPreorder _⊗_ I
  ⊗-isMonoid .IsMonoid.mono x₁⊑x₂ y₁⊑y₂ .*≤* = 𝐂-mono (mono (x₁⊑x₂ .*≤*) (y₁⊑y₂ .*≤*))
  ⊗-isMonoid .IsMonoid.assoc {x} {y} {z} .proj₁ .*≤* = begin
      𝐂 (𝐂 (x .elt ∙ y .elt) ∙ z .elt)    ≤⟨ 𝐂-mono 𝐂-strong' ⟩
      𝐂 (𝐂 ((x .elt ∙ y .elt) ∙ z .elt))  ≤⟨ 𝐂-mono (𝐂-mono (assoc .proj₁)) ⟩
      𝐂 (𝐂 (x .elt ∙ (y .elt ∙ z .elt)))  ≤⟨ 𝐂-join ⟩
      𝐂 (x .elt ∙ (y .elt ∙ z .elt))       ≤⟨ 𝐂-mono (mono refl 𝐂-unit) ⟩
      𝐂 (x .elt ∙ 𝐂 (y .elt ∙ z .elt))    ∎
    where open ≤-Reasoning ≤-isPreorder
  ⊗-isMonoid .IsMonoid.assoc {x} {y} {z} .proj₂ .*≤* = begin
      𝐂 (x .elt ∙ 𝐂 (y .elt ∙ z .elt))    ≤⟨ 𝐂-mono 𝐂-strong ⟩
      𝐂 (𝐂 (x .elt ∙ (y .elt ∙ z .elt)))  ≤⟨ 𝐂-mono (𝐂-mono (assoc .proj₂)) ⟩
      𝐂 (𝐂 ((x .elt ∙ y .elt) ∙ z .elt))  ≤⟨ 𝐂-join ⟩
      𝐂 ((x .elt ∙ y .elt) ∙ z .elt)       ≤⟨ 𝐂-mono (mono 𝐂-unit refl) ⟩
      𝐂 (𝐂 (x .elt ∙ y .elt) ∙ z .elt)    ∎
    where open ≤-Reasoning ≤-isPreorder
  ⊗-isMonoid .IsMonoid.lunit {x} .proj₁ .*≤* = begin
      𝐂 (𝐂 ε ∙ x .elt)   ≤⟨ 𝐂-mono 𝐂-strong' ⟩
      𝐂 (𝐂 (ε ∙ x .elt)) ≤⟨ 𝐂-mono (𝐂-mono (lunit .proj₁)) ⟩
      𝐂 (𝐂 (x .elt))     ≤⟨ 𝐂-join ⟩
      𝐂 (x .elt)          ≤⟨ x .closed ⟩
      x .elt
    ∎
    where open ≤-Reasoning ≤-isPreorder
  ⊗-isMonoid .IsMonoid.lunit {x} .proj₂ .*≤* = begin
      x .elt             ≤⟨ 𝐂-unit ⟩
      𝐂 (x .elt)        ≤⟨ 𝐂-mono (lunit .proj₂) ⟩
      𝐂 (ε ∙ x .elt)    ≤⟨ 𝐂-mono (mono 𝐂-unit refl) ⟩
      𝐂 (𝐂 ε ∙ x .elt) ∎
    where open ≤-Reasoning ≤-isPreorder
  ⊗-isMonoid .IsMonoid.runit {x} .proj₁ .*≤* = begin
      𝐂 (x .elt ∙ 𝐂 ε)   ≤⟨ 𝐂-mono 𝐂-strong ⟩
      𝐂 (𝐂 (x .elt ∙ ε)) ≤⟨ 𝐂-mono (𝐂-mono (runit .proj₁)) ⟩
      𝐂 (𝐂 (x .elt))     ≤⟨ 𝐂-join ⟩
      𝐂 (x .elt)          ≤⟨ x .closed ⟩
      x .elt
    ∎
    where open ≤-Reasoning ≤-isPreorder
  ⊗-isMonoid .IsMonoid.runit {x} .proj₂ .*≤* = begin
      x .elt             ≤⟨ 𝐂-unit ⟩
      𝐂 (x .elt)        ≤⟨ 𝐂-mono (runit .proj₂) ⟩
      𝐂 (x .elt ∙ ε)    ≤⟨ 𝐂-mono (mono refl 𝐂-unit) ⟩
      𝐂 (x .elt ∙ 𝐂 ε) ∎
    where open ≤-Reasoning ≤-isPreorder

  ⊗-comm : ∀ {x y} → (x ⊗ y) ⊑ (y ⊗ x)
  ⊗-comm .*≤* = 𝐂-mono comm

  module residual {_-∙_} (-∙-isResidual : IsResidual ≤-isPreorder ∙-isMonoid _-∙_) where

    open IsResidual -∙-isResidual

    _⊸_ : Elt → Elt → Elt
    (x ⊸ y) .elt = x .elt -∙ y .elt
    (x ⊸ y) .closed = lambda (begin
        𝐂 (x .elt -∙ y .elt) ∙ x .elt    ≤⟨ 𝐂-strong' ⟩
        𝐂 ((x .elt -∙ y .elt) ∙ x .elt)  ≤⟨ 𝐂-mono eval ⟩
        𝐂 (y .elt)                       ≤⟨ y .closed ⟩
        y .elt                           ∎)
      where open ≤-Reasoning ≤-isPreorder

    ⊸-isResidual : IsResidual ⊑-isPreorder ⊗-isMonoid _⊸_
    ⊸-isResidual .IsResidual.lambda {x} {y} {z} f .*≤* = lambda (begin
        x .elt ∙ y .elt       ≤⟨ 𝐂-unit ⟩
        𝐂 (x .elt ∙ y .elt)  ≤⟨ f .*≤* ⟩
        z .elt               ∎)
      where open ≤-Reasoning ≤-isPreorder
    ⊸-isResidual .IsResidual.eval {x} {y} .*≤* = begin
        𝐂 ((x .elt -∙  y .elt) ∙ x .elt) ≤⟨ 𝐂-mono eval ⟩
        𝐂 (y .elt)                      ≤⟨ y .closed ⟩
        y .elt                           ∎
      where open ≤-Reasoning ≤-isPreorder

  module exponentials { !! } (!!-isExponential : IsExponential ≤-isPreorder ∙-isMonoid !!) where

    open IsExponential !!-isExponential
      renaming (mono to !!-mono)

    ！ : Elt → Elt
    ！ x .elt = 𝐂 (!! (x .elt))
    ！ x .closed = 𝐂-join

    ！-isExponential : IsExponential ⊑-isPreorder ⊗-isMonoid ！
    ！-isExponential .IsExponential.mono x₁⊑x₂ .*≤* = 𝐂-mono (!!-mono (x₁⊑x₂ .*≤*))
    ！-isExponential .IsExponential.monoidal-unit .*≤* = trans (𝐂-mono monoidal-unit) (𝐂-mono (!!-mono 𝐂-unit))
    ！-isExponential .IsExponential.monoidal-prod .*≤* =
      trans (𝐂-mono 𝐂-monoidal) (trans 𝐂-join (trans (𝐂-mono monoidal-prod) (𝐂-mono (!!-mono 𝐂-unit))))
    ！-isExponential .IsExponential.discard .*≤* = 𝐂-mono discard
    ！-isExponential .IsExponential.duplicate .*≤* = trans (𝐂-mono duplicate) (𝐂-mono (mono 𝐂-unit 𝐂-unit))
    ！-isExponential .IsExponential.derelict {x} .*≤* = trans (𝐂-mono derelict) (x .closed)
    ！-isExponential .IsExponential.dig {x} .*≤* = trans (𝐂-mono dig) (𝐂-mono (!!-mono 𝐂-unit))
