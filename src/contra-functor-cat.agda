{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level
open import prop-setoid using (IsEquivalence; Setoid; module ≈-Reasoning)
open import categories
open import fam

-- FIXME: this is mostly in functor.agda now

module contra-functor-cat {o m e o' m'} -- e'}
        (𝒞 : Category o m e)
        (𝒟 : Category o' m' m')
  where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟

record Obj : Set (o ⊔ o' ⊔ m ⊔ m' ⊔ e{- ⊔ e'-}) where
  field
    fobj : 𝒞.obj → 𝒟.obj
    fmap : ∀ {x y} → x 𝒞.⇒ y → fobj y 𝒟.⇒ fobj x
    fmap-cong : ∀ {x y} {f g : x 𝒞.⇒ y} → f 𝒞.≈ g → fmap f 𝒟.≈ fmap g
    fmap-id   : ∀ x → fmap (𝒞.id x) 𝒟.≈ 𝒟.id (fobj x)
    fmap-∘    : ∀ {x y z} (f : y 𝒞.⇒ z) (g : x 𝒞.⇒ y) → fmap (f 𝒞.∘ g) 𝒟.≈ (fmap g 𝒟.∘ fmap f)
open Obj

record _⇒p_ (F G : Obj) : Set (o ⊔ m ⊔ m'{- ⊔ e'-}) where
  private
    module F = Obj F
    module G = Obj G
  field
    transf  : ∀ x → F.fobj x 𝒟.⇒ G.fobj x
    natural : ∀ {x y} (f : x 𝒞.⇒ y) → (G.fmap f 𝒟.∘ transf y) 𝒟.≈ (transf x 𝒟.∘ F.fmap f)
open _⇒p_

record _≈p_ {F G : Obj} (α β : F ⇒p G) : Prop (o ⊔ m ⊔ m') {-e')-} where
  field
    transf-eq : ∀ x → α .transf x 𝒟.≈ β .transf x
open _≈p_

open IsEquivalence

≈p-isEquivalence : ∀ {F G} → IsEquivalence (_≈p_ {F} {G})
≈p-isEquivalence .refl .transf-eq x = 𝒟.isEquiv .refl
≈p-isEquivalence .sym α≈β .transf-eq x = 𝒟.isEquiv .sym (α≈β .transf-eq x)
≈p-isEquivalence .trans α≈β β≈γ .transf-eq x =
  𝒟.isEquiv .trans (α≈β .transf-eq x) (β≈γ .transf-eq x)

idp : (F : Obj) → F ⇒p F
idp F .transf x = 𝒟.id _
idp F .natural f =
  begin
    F .fmap f 𝒟.∘ 𝒟.id _ ≈⟨ 𝒟.≈-sym 𝒟.id-swap ⟩
    𝒟.id _ 𝒟.∘ F .fmap f
  ∎ where open ≈-Reasoning 𝒟.isEquiv

_∘p_ : {F G H : Obj} (f : G ⇒p H) (g : F ⇒p G) → F ⇒p H
(α ∘p β) .transf x = (α .transf x) 𝒟.∘ (β .transf x)
_∘p_ {F}{G}{H} α β .natural {x} {y} f =
  begin
    fmap H f 𝒟.∘ (α .transf y 𝒟.∘ β .transf y)
  ≈⟨ 𝒟.≈-sym (𝒟.assoc _ _ _) ⟩
    (fmap H f 𝒟.∘ α .transf y) 𝒟.∘ β .transf y
  ≈⟨ 𝒟.∘-cong (α .natural f) 𝒟.≈-refl ⟩
    (α .transf x 𝒟.∘ fmap G f) 𝒟.∘ β .transf y
  ≈⟨ 𝒟.assoc _ _ _ ⟩
    α .transf x 𝒟.∘ (fmap G f 𝒟.∘ β .transf y)
  ≈⟨ 𝒟.∘-cong (𝒟.isEquiv .refl) (β .natural f) ⟩
    α .transf x 𝒟.∘ (β .transf x 𝒟.∘ F .fmap f)
  ≈⟨ 𝒟.isEquiv .sym (𝒟.assoc _ _ _) ⟩
    (α .transf x 𝒟.∘ β .transf x) 𝒟.∘ F .fmap f
  ∎ where open ≈-Reasoning 𝒟.isEquiv

∘p-cong : ∀ {F G H} {f₁ f₂ : G ⇒p H} {g₁ g₂ : F ⇒p G} →
  f₁ ≈p f₂ → g₁ ≈p g₂ → (f₁ ∘p g₁) ≈p (f₂ ∘p g₂)
∘p-cong f₁≈f₂ g₁≈g₂ .transf-eq x = 𝒟.∘-cong (f₁≈f₂ .transf-eq x) (g₁≈g₂ .transf-eq x)

cat : Category _ _ _
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒p_
cat .Category._≈_ = _≈p_
cat .Category.isEquiv = ≈p-isEquivalence
cat .Category.id = idp
cat .Category._∘_ = _∘p_
cat .Category.∘-cong = ∘p-cong
cat .Category.id-left .transf-eq x = 𝒟.id-left
cat .Category.id-right .transf-eq x = 𝒟.id-right
cat .Category.assoc f g h .transf-eq x = 𝒟.assoc _ _ _

------------------------------------------------------------------------------
-- If 𝒟 has finite products, then so does this category
--
-- FIXME: this is true for all limits...

module finite-products (T : HasTerminal 𝒟) (P : HasProducts 𝒟) where

  private
    module P = HasProducts P
    module T = HasTerminal T

  open HasTerminal

  terminal : HasTerminal cat
  terminal .witness .fobj x = T.witness
  terminal .witness .fmap f = 𝒟.id _
  terminal .witness .fmap-cong x = 𝒟.≈-refl
  terminal .witness .fmap-id x = 𝒟.≈-refl
  terminal .witness .fmap-∘ f g = 𝒟.≈-sym 𝒟.id-left
  terminal .terminal-mor F .transf x = T.terminal-mor _
  terminal .terminal-mor F .natural f = T.terminal-unique _ _ _
  terminal .terminal-unique F α β .transf-eq x = T.terminal-unique _ _ _

  _×_ : Obj → Obj → Obj
  (F × G) .fobj x = P.prod (F .fobj x) (G .fobj x)
  (F × G) .fmap f = P.prod-m (F .fmap f) (G .fmap f)
  (F × G) .fmap-cong f≈g =
    P.prod-m-cong (F .fmap-cong f≈g) (G .fmap-cong f≈g)
  (F × G) .fmap-id x =
    begin
      P.prod-m (F .fmap (Category.id 𝒞 x)) (G .fmap (Category.id 𝒞 x))
    ≈⟨ P.prod-m-cong (F .fmap-id x) (G .fmap-id x) ⟩
      P.prod-m (𝒟.id _) (𝒟.id _)
    ≈⟨ P.prod-m-id ⟩
      𝒟.id _
    ∎ where open ≈-Reasoning 𝒟.isEquiv
  (F × G) .fmap-∘ f g =
    begin
      P.prod-m (F .fmap (f 𝒞.∘ g)) (G .fmap (f 𝒞.∘ g))
    ≈⟨ P.prod-m-cong (F .fmap-∘ _ _) (G .fmap-∘ _ _) ⟩
      P.prod-m (F .fmap g 𝒟.∘ F .fmap f) (G .fmap g 𝒟.∘ G .fmap f)
    ≈⟨ P.pair-functorial _ _ _ _ ⟩
      P.prod-m (F .fmap g) (G .fmap g) 𝒟.∘ P.prod-m (F .fmap f) (G .fmap f)
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  open HasProducts

  products : HasProducts cat
  products .prod = _×_
  products .p₁ .transf x = P.p₁
  products .p₁ .natural f = 𝒟.≈-sym (P.pair-p₁ _ _)
  products .p₂ .transf x = P.p₂
  products .p₂ .natural f = 𝒟.≈-sym (P.pair-p₂ _ _)
  products .pair α β .transf x = P.pair (α .transf x) (β .transf x)
  products .pair {F} {G} {H} α β .natural {x} {y} f =
    begin
      P.prod-m (G .fmap f) (H .fmap f) 𝒟.∘ P.pair (α .transf y) (β .transf y)
    ≈⟨ P.pair-compose _ _ _ _ ⟩
      P.pair (G .fmap f 𝒟.∘ α .transf y) (H .fmap f 𝒟.∘ β .transf y)
    ≈⟨ P.pair-cong (α .natural f) (β .natural f) ⟩
      P.pair (α .transf x 𝒟.∘ F .fmap f) (β .transf x 𝒟.∘ F .fmap f)
    ≈⟨ 𝒟.≈-sym (P.pair-natural _ _ _) ⟩
      P.pair (α .transf x) (β .transf x) 𝒟.∘ F .fmap f
    ∎ where open ≈-Reasoning 𝒟.isEquiv
  products .pair-cong e₁ e₂ .transf-eq x = P.pair-cong (e₁ .transf-eq x) (e₂ .transf-eq x)
  products .pair-p₁ f g .transf-eq x = P.pair-p₁ _ _
  products .pair-p₂ f g .transf-eq x = P.pair-p₂ _ _
  products .pair-ext f .transf-eq x = P.pair-ext _
