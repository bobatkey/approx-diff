{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using () renaming (_⊔_ to _⊔ℓ_)
open import prop using (proj₁; proj₂)
open import basics
  using (IsPreorder; IsMonoid; IsResidual; IsClosureOp;
         module ≤-Reasoning;
         IsMeet; IsJoin; IsExponential; IsStarAuto)

module double-negation {aℓ bℓ}
  {A : Set aℓ} {_≤_ : A → A → Prop bℓ} (≤-isPreorder : IsPreorder _≤_)
  {_∙_ ε} (∙-isMonoid : IsMonoid ≤-isPreorder _∙_ ε) (comm : ∀ {x y} → (x ∙ y) ≤ (y ∙ x))
  {_-∙_}  (-∙-isResidual : IsResidual ≤-isPreorder ∙-isMonoid _-∙_)
  (¶ : A)
  where

open IsPreorder ≤-isPreorder
open IsMonoid ∙-isMonoid
open IsResidual -∙-isResidual

¬ : A → A
¬ x = x -∙ ¶

¬-mono : ∀ {x₁ x₂} → x₁ ≤ x₂ → ¬ x₂ ≤ ¬ x₁
¬-mono x₁≤x₂ = lambda (trans (mono refl x₁≤x₂) eval)

-- Double negation always gives a closure operator on a residuated
-- commutative monoid.

𝐂 : A → A
𝐂 x = ¬ (¬ x)

¶-closed : 𝐂 ¶ ≤ ¶
¶-closed = begin
    (¶ -∙ ¶) -∙ ¶              ≤⟨ runit .proj₂ ⟩
    ((¶ -∙ ¶) -∙ ¶) ∙ ε        ≤⟨ mono refl (lambda (lunit .proj₁)) ⟩
    ((¶ -∙ ¶) -∙ ¶) ∙ (¶ -∙ ¶)  ≤⟨ eval ⟩
    ¶                         ∎
  where open ≤-Reasoning ≤-isPreorder

𝐂-mono : ∀ {x₁ x₂} → x₁ ≤ x₂ → 𝐂 x₁ ≤ 𝐂 x₂
𝐂-mono x₁≤x₂ = ¬-mono (¬-mono x₁≤x₂)

𝐂-unit : ∀ {x} → x ≤ 𝐂 x
𝐂-unit = lambda (trans comm eval)

𝐂-join : ∀ {x} → 𝐂 (𝐂 x) ≤ 𝐂 x
𝐂-join = lambda (trans (mono refl 𝐂-unit) eval)

𝐂-isClosure : IsClosureOp ≤-isPreorder 𝐂
𝐂-isClosure .IsClosureOp.mono = 𝐂-mono
𝐂-isClosure .IsClosureOp.unit = 𝐂-unit
𝐂-isClosure .IsClosureOp.closed = 𝐂-join

𝐂-strong : ∀ {X Y} → (X ∙ 𝐂 Y) ≤ 𝐂 (X ∙ Y)
𝐂-strong {X} {Y} = lambda (begin
    (X ∙ ((Y -∙ ¶) -∙ ¶)) ∙ ((X ∙ Y) -∙ ¶)     ≤⟨ comm ⟩
    ((X ∙ Y) -∙ ¶) ∙ (X ∙ ((Y -∙ ¶) -∙ ¶))     ≤⟨ assoc .proj₂ ⟩
    (((X ∙ Y) -∙ ¶) ∙ X) ∙ ((Y -∙ ¶) -∙ ¶)     ≤⟨ mono (mono curry refl) refl ⟩
    ((X -∙ (Y -∙ ¶)) ∙ X) ∙ ((Y -∙ ¶) -∙ ¶)    ≤⟨ mono eval refl ⟩
    (Y -∙ ¶) ∙ ((Y -∙ ¶) -∙ ¶)                ≤⟨ comm ⟩
    ((Y -∙ ¶) -∙ ¶) ∙ (Y -∙ ¶)                ≤⟨ eval ⟩
    ¶                                       ∎)
  where open ≤-Reasoning ≤-isPreorder

------------------------------------------------------------------------------
-- The closed elements form a *-autonomous poset

open import closed ≤-isPreorder 𝐂-isClosure
open monoid ∙-isMonoid comm 𝐂-strong

open Elt
open _⊑_

negate : Elt → Elt
negate X .elt = ¬ (X .elt)
negate X .closed = lambda (trans (mono refl 𝐂-unit) eval)

isStarAut : IsStarAuto ⊑-isPreorder ⊗-isMonoid ⊗-comm negate
isStarAut .IsStarAuto.¬-mono x⊑y .*≤* = ¬-mono (x⊑y .*≤*)
isStarAut .IsStarAuto.involution {x} .proj₁ .*≤* = 𝐂-unit
isStarAut .IsStarAuto.involution {x} .proj₂ .*≤* = x .closed
isStarAut .IsStarAuto.*-aut {x} {y} {z} f .*≤* = lambda (begin
    x .elt ∙ (((y .elt ∙ z .elt) -∙ ¶) -∙ ¶)    ≤⟨ 𝐂-strong ⟩
    ((x .elt ∙ (y .elt ∙ z .elt)) -∙ ¶) -∙ ¶    ≤⟨ -∙-mono (-∙-mono (assoc .proj₂) refl) refl ⟩
    (((x .elt ∙ y .elt) ∙ z .elt) -∙ ¶) -∙ ¶    ≤⟨ -∙-mono (-∙-mono (mono (trans 𝐂-unit (f .*≤*)) refl) refl) refl ⟩
    (((z .elt -∙ ¶) ∙ z .elt) -∙ ¶) -∙ ¶        ≤⟨ -∙-mono (-∙-mono eval refl) refl ⟩
    (¶ -∙ ¶) -∙ ¶                              ≤⟨ ¶-closed ⟩
    ¶                                         ∎)
  where open ≤-Reasoning ≤-isPreorder
isStarAut .IsStarAuto.*-aut⁻¹ {x} {y} {z} f .*≤* = lambda (begin
    (((x .elt ∙ y .elt) -∙ ¶) -∙ ¶) ∙ z .elt                        ≤⟨ 𝐂-strong' ⟩
    (((x .elt ∙ y .elt) ∙ z .elt) -∙ ¶) -∙ ¶                        ≤⟨ -∙-mono (-∙-mono (assoc .proj₁) refl) refl ⟩
    ((x .elt ∙ (y .elt ∙ z .elt)) -∙ ¶) -∙ ¶                        ≤⟨ -∙-mono (-∙-mono (mono (f .*≤*) 𝐂-unit) refl) refl ⟩
    (((𝐂 (y .elt ∙ z .elt) -∙ ¶) ∙ 𝐂 (y .elt ∙ z .elt)) -∙ ¶) -∙ ¶  ≤⟨ -∙-mono (-∙-mono eval refl) refl ⟩
    (¶ -∙ ¶) -∙ ¶                                                  ≤⟨ ¶-closed ⟩
    ¶                                                             ∎)
  where open ≤-Reasoning ≤-isPreorder

-- TODO:
--   1. Meets and Joins
--   2. Exponentials
--   3. Preservation properties of the embedding
