{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
  using (suc)
open import prop
  using (_∧_; _∨_; ⊤; ⊥; proj₁; proj₂; _,_; tt; inj₁; inj₂; ∃)
open import basics
  using ( IsPreorder; IsMeet; IsJoin; IsTop; IsBottom
        ; IsMonoid; monoidOfMeet; monoidOfJoin
        ; IsResidual
        ; IsBigMeet; IsBigJoin
        )

module prop-preorder aℓ where

------------------------------------------------------------------------------
-- Preorder
Elt : Set (suc aℓ)
Elt = Prop aℓ

_≤_ : Prop aℓ → Prop aℓ → Prop aℓ
p ≤ q = p → q

≤-isPreorder : IsPreorder _≤_
≤-isPreorder .IsPreorder.refl = λ z → z
≤-isPreorder .IsPreorder.trans p≤q q≤r p = q≤r (p≤q p)

------------------------------------------------------------------------------
-- Meets
∧-isMeet : IsMeet ≤-isPreorder _∧_
∧-isMeet .IsMeet.π₁ = proj₁
∧-isMeet .IsMeet.π₂ = proj₂
∧-isMeet .IsMeet.⟨_,_⟩ x≤y x≤z x = x≤y x , x≤z x

⊤-isTop : IsTop ≤-isPreorder ⊤
⊤-isTop .IsTop.≤-top _ = tt

∧-isMonoid : IsMonoid ≤-isPreorder _∧_ ⊤
∧-isMonoid = monoidOfMeet ≤-isPreorder ∧-isMeet ⊤-isTop
-- FIXME: commutativity

⋂ : (I : Set aℓ) (a : I → Prop aℓ) → Prop aℓ
⋂ I a = ∀ i → a i

⋂-isBigMeet : IsBigMeet ≤-isPreorder aℓ ⋂
⋂-isBigMeet .IsBigMeet.lower I a i ⋂a = ⋂a i
⋂-isBigMeet .IsBigMeet.greatest I a z z≤⋂a π i = z≤⋂a i π

------------------------------------------------------------------------------
-- Implication
_⇒_ : Prop aℓ → Prop aℓ → Prop aℓ
p ⇒ q = p → q

residual : IsResidual ≤-isPreorder ∧-isMonoid _⇒_
residual .IsResidual.lambda xy≤z x y = xy≤z (x , y)
residual .IsResidual.eval (x⇒y , x) = x⇒y x

------------------------------------------------------------------------------
-- Joins
∨-isJoin : IsJoin ≤-isPreorder _∨_
∨-isJoin .IsJoin.inl = inj₁
∨-isJoin .IsJoin.inr = inj₂
∨-isJoin .IsJoin.[_,_] x≤z y≤z (inj₁ x) = x≤z x
∨-isJoin .IsJoin.[_,_] x≤z y≤z (inj₂ y) = y≤z y

⊥-isBottom : IsBottom ≤-isPreorder ⊥
⊥-isBottom .IsBottom.≤-bottom ()

∨-isMonoid : IsMonoid ≤-isPreorder _∨_ ⊥
∨-isMonoid = monoidOfJoin ≤-isPreorder ∨-isJoin ⊥-isBottom
-- FIXME: commutativity

⋃ : (I : Set aℓ) (a : I → Prop aℓ) → Prop aℓ
⋃ I a = ∃ I a

⋃-isBigJoin : IsBigJoin ≤-isPreorder aℓ ⋃
⋃-isBigJoin .IsBigJoin.upper I a i π = i , π
⋃-isBigJoin .IsBigJoin.least I a z a≤z (i , π) = a≤z i π

------------------------------------------------------------------------------
-- FIXME: distributivity properties

------------------------------------------------------------------------------
-- FIXME: the identity function is an exponential comonad
