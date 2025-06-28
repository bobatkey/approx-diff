{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_; Level; lift; lower)
open import Data.Product using (_,_)
open import prop using (lift; lower; _,_)
open import prop-setoid
  using (Setoid; IsEquivalence; module ≈-Reasoning; _∘S_; idS)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category; HasProducts; IsProduct; HasExponentials)
open import functor using ([_⇒_]; Functor; NatTrans; ≃-NatTrans;
  HasLimits';
  preserve-limits-of-shape; IsLimit; constF; constF-F; constFmor;
  _∘F_; id; _∘H_; _∘_; ≃-isEquivalence)
open import setoid-cat using (SetoidCat; Setoid-terminal; Setoid-products; Setoid-Limit'; Setoid-coproducts)

-- extra 'os' level is to raise the level of the codomain if needed
module yoneda {o m e} os (𝒞 : Category o m e) where

private
  ℓ : Level
  ℓ = o ⊔ m ⊔ e ⊔ os

  module 𝒞 = Category 𝒞

PSh : Category (suc ℓ) ℓ ℓ
PSh = [ 𝒞.opposite ⇒ SetoidCat ℓ ℓ ]

open Setoid
open _⇒s_
open _≈s_
open IsEquivalence
open Functor
open NatTrans
open ≃-NatTrans

よ₀ : 𝒞.obj → PSh .Category.obj
よ₀ x .fobj y = Category.hom-setoid-l 𝒞 ℓ ℓ y x
よ₀ x .fmor f .func (lift g) = lift (g 𝒞.∘ f)
よ₀ x .fmor f .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ 𝒞.≈-refl)
よ₀ x .fmor-cong {y} {z} {f₁} {f₂} f₁≈f₂ .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ f₁≈f₂)
よ₀ x .fmor-id {y} .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.isEquiv .trans 𝒞.id-right g₁≈g₂)
よ₀ x .fmor-comp {y} {z} {w} f g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin
    h₁ 𝒞.∘ (g 𝒞.∘ f)  ≈⟨ 𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl ⟩
    h₂ 𝒞.∘ (g 𝒞.∘ f)  ≈˘⟨ 𝒞.assoc _ _ _ ⟩
    (h₂ 𝒞.∘ g) 𝒞.∘ f  ∎
  where open ≈-Reasoning 𝒞.isEquiv

よ : Functor 𝒞 PSh
よ .fobj = よ₀
よ .fmor f .transf y .func (lift g) = lift (f 𝒞.∘ g)
よ .fmor f .transf y .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong 𝒞.≈-refl g₁≈g₂)
よ .fmor f .natural g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  begin ((f 𝒞.∘ h₁) 𝒞.∘ g)   ≈⟨ 𝒞.∘-cong (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) 𝒞.≈-refl ⟩
         ((f 𝒞.∘ h₂) 𝒞.∘ g)  ≈⟨ 𝒞.assoc _ _ _ ⟩
         (f 𝒞.∘ (h₂ 𝒞.∘ g))  ∎
  where open ≈-Reasoning 𝒞.isEquiv
よ .fmor-cong {x} {y} {f₁} {f₂} f₁≈f₂ .transf-eq z .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) = lift (𝒞.∘-cong f₁≈f₂ g₁≈g₂)
よ .fmor-id .transf-eq x .func-eq {lift g₁} {lift g₂} (lift g₁≈g₂) .lower = 𝒞.isEquiv .trans 𝒞.id-left g₁≈g₂
よ .fmor-comp f g .transf-eq x .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) .lower =
  𝒞.isEquiv .trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.assoc _ _ _)

------------------------------------------------------------------------------
-- Yoneda lemma

lemma : ∀ F x → F .fobj x ⇒s Category.hom-setoid PSh (よ₀ x) F
lemma F x .func Fx .transf y .func (lift f) = F .fmor f .func Fx
lemma F x .func Fx .transf y .func-resp-≈ {lift f₁} {lift f₂} (lift f₁≈f₂) =
  F .fmor-cong f₁≈f₂ .func-eq (F .fobj x .refl)
lemma F x .func Fx .natural {y} {z} g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) =
  begin
    F .fmor g .func (F .fmor h₁ .func Fx)
  ≈⟨ F .fmor g .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl)) ⟩
    F .fmor g .func (F .fmor h₂ .func Fx)
  ≈˘⟨ F .fmor-comp _ _ .func-eq (F .fobj x .refl) ⟩
    F .fmor (h₂ 𝒞.∘ g) .func Fx
  ∎ where open ≈-Reasoning (F .fobj z .isEquivalence)
lemma F x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f₁} {lift f₂} (lift f₁≈f₂) =
  F .fmor-cong f₁≈f₂ .func-eq Fx₁≈Fx₂

lemma⁻¹ : ∀ F x → Category.hom-setoid PSh (よ₀ x) F ⇒s F .fobj x
lemma⁻¹ F x .func α = α .transf x .func (lift (𝒞.id _))
lemma⁻¹ F x .func-resp-≈ {α₁}{α₂} α₁≈α₂ = α₁≈α₂ .transf-eq x .func-eq (lift 𝒞.≈-refl)

よ⁻¹ : ∀ {x y} → NatTrans (よ₀ x) (よ₀ y) → x 𝒞.⇒ y
よ⁻¹ {x} {y} α = lemma⁻¹ (よ₀ y) x .func α .lower

lemma∘lemma⁻¹ : ∀ F x → (lemma F x ∘S lemma⁻¹ F x) ≈s idS (Category.hom-setoid PSh (よ₀ x) F)
lemma∘lemma⁻¹ F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f} {lift g} (lift f≈g) =
  F .fobj y .trans
      (Fx₁ .natural f .func-eq (lift 𝒞.≈-refl))
      (Fx₁≈Fx₂ .transf-eq y .func-eq (lift (𝒞.≈-trans 𝒞.id-left f≈g)))

lemma⁻¹∘lemma : ∀ F x → (lemma⁻¹ F x ∘S lemma F x) ≈s idS (F .fobj x)
lemma⁻¹∘lemma F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ = F .fmor-id .func-eq Fx₁≈Fx₂

-- lemma-natural-x : ∀ {F x y} (f : x 𝒞.⇒ y) →
--                 (lemma F x ∘S F .fmor f) ≈s ({!!} ∘S lemma F y)
-- lemma-natural-x f = {!!}

------------------------------------------------------------------------------
-- Completeness

import functor-cat-limits

limits : (𝒮 : Category o m e) → HasLimits' 𝒮 PSh
limits 𝒮 = functor-cat-limits.limits _ _ _ (Setoid-Limit' ℓ 𝒮)

-- products as a special case, using a nicer intensional representation.
open import functor-cat-products
       𝒞.opposite
       (SetoidCat ℓ ℓ)
       (Setoid-terminal _ _)
       (Setoid-products _ _)
  public

------------------------------------------------------------------------------
-- FIXME: cocompleteness

open import functor-cat-coproducts
       𝒞.opposite
       (SetoidCat ℓ ℓ)
       (Setoid-coproducts _ _)
  public

------------------------------------------------------------------------------
-- Exponentials
module _ where

  open HasProducts products

  _⟶_ : PSh .Category.obj → PSh .Category.obj → PSh .Category.obj
  (F ⟶ G) .fobj x = Category.hom-setoid PSh (F × (よ .fobj x)) G
  (F ⟶ G) .fmor f .func x .transf y .func (a , lift b) = x .transf y .func (a , (lift (f 𝒞.∘ b)))
  (F ⟶ G) .fmor f .func x .transf y .func-resp-≈ (x₁≈x₂ , lift e) =
    x .transf y .func-resp-≈ (x₁≈x₂ , (lift (𝒞.∘-cong (𝒞.≈-refl) e)))
  (F ⟶ G) .fmor f .func h .natural {y}{z} g .func-eq (a₁≈a₂ , lift e) =
    G .fobj z .trans
      (h .natural g .func-eq (a₁≈a₂ , lift (𝒞.∘-cong 𝒞.≈-refl e)))
      (h .transf z .func-resp-≈ (F .fobj z .Setoid.refl , lift (𝒞.assoc _ _ _)))
  (F ⟶ G) .fmor f .func-resp-≈ {h₁}{h₂} h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , (lift (𝒞.∘-cong 𝒞.≈-refl e)))
  (F ⟶ G) .fmor-cong f≈g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (𝒞.∘-cong f≈g e))
  (F ⟶ G) .fmor-id .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (𝒞.≈-trans 𝒞.id-left e))
  (F ⟶ G) .fmor-comp f g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq
      (a₁≈a₂ ,
       lift (𝒞.≈-trans (𝒞.assoc _ _ _)
                        (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong 𝒞.≈-refl e))))

  eval : ∀ {F G} → NatTrans ((F ⟶ G) × F) G
  eval .transf x .func (g , a) = g .transf x .func (a , lift (𝒞.id x))
  eval .transf x .func-resp-≈ (e , a₁≈a₂) = e .transf-eq x .func-eq (a₁≈a₂ , lift 𝒞.≈-refl)
  eval {F} {G} .natural {x} {y} f .func-eq {h₁ , a₁} {h₂ , a₂} (h₁≈h₂ , a₁≈a₂) =
    G .fobj y .trans
      (h₁ .natural f .func-eq (a₁≈a₂ , lift 𝒞.≈-refl))
      (h₁≈h₂ .transf-eq y .func-eq (F .fobj y .refl , lift 𝒞.id-swap))

  lambda⟶ : ∀ {F G H} → NatTrans (F × G) H → NatTrans F (G ⟶ H)
  lambda⟶ {F} f .transf x .func Fx .transf y .func (Gy , lift g) =
    f .transf y .func (F .fmor g .func Fx , Gy)
  lambda⟶ {F} f .transf x .func Fx .transf y .func-resp-≈ {Gy₁ , lift g₁} {Gy₂ , lift g₂} (Gy₁≈Gy₂ , lift g₁≈g₂) =
    f .transf y .func-resp-≈ (F .fmor-cong g₁≈g₂ .func-eq (F .fobj x .refl) , Gy₁≈Gy₂)
  lambda⟶ {F}{G}{H} f .transf x .func Fx .natural {y} {z} g .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    H .fobj z .trans
      (f .natural g .func-eq (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl) , Gy₁≈Gy₂))
      (f .transf z .func-resp-≈ ((F .fobj z .sym (F .fmor-comp _ _ .func-eq (F .fobj x .refl))) , G .fobj z .refl))
  lambda⟶ {F} f .transf x .func-resp-≈ {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    f .transf y .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq Fx₁≈Fx₂ , Gy₁≈Gy₂)
  lambda⟶ {F} f .natural {x} {y} g .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq z .func-eq {Gz₁ , lift h₁} {Gz₂ , lift h₂} (Gz₁≈Gz₂ , lift h₁≈h₂) =
    f .transf z .func-resp-≈
      (F .fobj z .trans (F .fmor-comp h₁ g .func-eq Fx₁≈Fx₂)
                        (F .fmor-cong h₁≈h₂ .func-eq (F .fobj y .refl)) ,
       Gz₁≈Gz₂)

  exponentials : HasExponentials PSh products
  exponentials .HasExponentials.exp = _⟶_
  exponentials .HasExponentials.eval = eval
  exponentials .HasExponentials.lambda = lambda⟶
  exponentials .HasExponentials.lambda-cong {F} {G} {H} f₁≈f₂ .transf-eq x .func-eq Fx₁≈Fx₂ .transf-eq y .func-eq (Gy₁≈Gy₂ , lift h₁≈h₂) =
    f₁≈f₂ .transf-eq y .func-eq (F .fmor-cong h₁≈h₂ .func-eq Fx₁≈Fx₂ , Gy₁≈Gy₂)
  exponentials .HasExponentials.eval-lambda {F} {G} {H} f .transf-eq x .func-eq (Fx₁≈Fx₂ , Gx₁≈Gx₂) =
    f .transf x .func-resp-≈ (F .fmor-id .func-eq Fx₁≈Fx₂ , Gx₁≈Gx₂)
  exponentials .HasExponentials.lambda-ext {F} {G} {H} f .transf-eq x .func-eq Fx₁≈Fx₂ .transf-eq y .func-eq {Gy₁ , lift h₁} {Gy₂ , lift h₂} (Gy₁≈Gy₂ , lift h₁≈h₂) =
    H .fobj y .trans
      (H .fobj y .sym (f .natural h₁ .func-eq (F .fobj x .sym Fx₁≈Fx₂) .transf-eq y .func-eq (G .fobj y .refl , lift 𝒞.≈-refl)))
      (f .transf x .func _ .transf y .func-resp-≈ (Gy₁≈Gy₂ , lift (𝒞.≈-trans 𝒞.id-right h₁≈h₂)))

------------------------------------------------------------------------------
{-
-- よ preserves products. FIXME: extend this to all limits by copying
-- the proofs from cmon-category.

open IsProduct

preserve-products : ∀ (x y p : 𝒞.obj) (p₁ : p 𝒞.⇒ x) (p₂ : p 𝒞.⇒ y) →
                    IsProduct 𝒞 x y p p₁ p₂ →
                    IsProduct PSh (よ₀ x) (よ₀ y) (よ₀ p) (よ .fmor p₁) (よ .fmor p₂)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func Zz .lower =
  p-isproduct .pair (f .transf z .func Zz .lower) (g .transf z .func Zz .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .transf z .func-resp-≈ {Zz₁} {Zz₂} Zz₁≈Zz₂ .lower =
  p-isproduct .pair-cong (f .transf z .func-resp-≈ Zz₁≈Zz₂ .lower) (g .transf z .func-resp-≈ Zz₁≈Zz₂ .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair {Z} f g .natural {x₁} {y₁} h .func-eq {Zz₁} {Zz₂} e .lower =
  begin
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower) (g .transf x₁ .func Zz₁ .lower) 𝒞.∘ h
  ≈⟨ pair-natural p-isproduct _ _ _ ⟩
    p-isproduct .pair (f .transf x₁ .func Zz₁ .lower 𝒞.∘ h) (g .transf x₁ .func Zz₁ .lower 𝒞.∘ h)
  ≈⟨ p-isproduct .pair-cong (f .natural h .func-eq e .lower) (g .natural h .func-eq e .lower) ⟩
    p-isproduct .pair (f .transf y₁ .func (Z .fmor h .func Zz₂) .lower) (g .transf y₁ .func (Z .fmor h .func Zz₂) .lower)
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-cong {Z} f₁≈f₂ g₁≈g₂ .transf-eq w .func-eq e .lower =
  p-isproduct .pair-cong (f₁≈f₂ .transf-eq w .func-eq e .lower) (g₁≈g₂ .transf-eq w .func-eq e .lower)
preserve-products x y p p₁ p₂ p-isproduct .pair-p₁ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₁ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₁ _ _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-p₂ {Z} f g .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p₂ 𝒞.∘ p-isproduct .pair (f .transf w .func Zw₁ .lower) (g .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-p₂ _ _ ⟩
    g .transf w .func Zw₁ .lower
  ≈⟨ g .transf w .func-resp-≈ e .lower ⟩
    g .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
preserve-products x y p p₁ p₂ p-isproduct .pair-ext {Z} f .transf-eq w .func-eq {Zw₁} {Zw₂} e .lower =
  begin
    p-isproduct .pair (p₁ 𝒞.∘ f .transf w .func Zw₁ .lower) (p₂ 𝒞.∘ f .transf w .func Zw₁ .lower)
  ≈⟨ p-isproduct .pair-ext _ ⟩
    f .transf w .func Zw₁ .lower
  ≈⟨ f .transf w .func-resp-≈ e .lower ⟩
    f .transf w .func Zw₂ .lower
  ∎ where open ≈-Reasoning 𝒞.isEquiv
-}

------------------------------------------------------------------------------
-- Yoneda embedding preserves all limits
preserve-limits : ∀ {o₁ m₁ e₁} (𝒮 : Category o₁ m₁ e₁) → preserve-limits-of-shape 𝒮 よ
preserve-limits 𝒮 D apex cone isLimit = lim
  where
  open IsLimit

  conv-transf : ∀ {X x} → NatTrans (constF 𝒮 X) (よ ∘F D) → X .fobj x .Carrier → NatTrans (constF 𝒮 x) D
  conv-transf {X} {x} α Xx .transf s = α .transf s .transf x .func Xx .lower
  conv-transf {X} {x} α Xx .natural f = 𝒞.≈-trans (α .natural f .transf-eq x .func-eq (X .fobj x .refl) .lower) (𝒞.≈-sym 𝒞.id-right)

  conv-transf-≈ : ∀ {X x α₁ α₂ Xx₁ Xx₂} →
                    ≃-NatTrans α₁ α₂ →
                    X .fobj x ._≈_ Xx₁ Xx₂ →
                    ≃-NatTrans (conv-transf {X} {x} α₁ Xx₁) (conv-transf {X} {x} α₂ Xx₂)
  conv-transf-≈ {X} {x} α₁≈α₂ Xx₁≈Xx₂ .transf-eq s = α₁≈α₂ .transf-eq s .transf-eq x .func-eq Xx₁≈Xx₂ .lower

  lim : IsLimit (よ ∘F D) (よ .fobj apex) ((id _ ∘H cone) ∘ constF-F よ apex)
  lim .lambda X α .transf x .func Xx .lower =
    isLimit .lambda x (conv-transf α Xx)
  lim .lambda X α .transf x .func-resp-≈ Xx₁≈Xx₂ .lower =
    isLimit .lambda-cong (conv-transf-≈ (≃-isEquivalence .IsEquivalence.refl) Xx₁≈Xx₂)
  lim .lambda X α .natural {x} {y} f .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
    begin
      isLimit .lambda x (conv-transf α Xx₁) 𝒞.∘ f
    ≈⟨ lambda-natural isLimit (conv-transf α Xx₁) f ⟩
      isLimit .lambda y (conv-transf α Xx₁ ∘ constFmor f)
    ≈⟨ isLimit .lambda-cong (record { transf-eq = λ s → α .transf s .natural f .func-eq Xx₁≈Xx₂ .lower }) ⟩
      isLimit .lambda y (conv-transf α (X .fmor f .func Xx₂))
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
  lim .lambda-cong α≈β .transf-eq x .func-eq Xx₁≈Xx₂ .lower =
    isLimit .lambda-cong (conv-transf-≈ α≈β Xx₁≈Xx₂)
  lim .lambda-eval {X} α .transf-eq s .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
    𝒞.≈-trans (isLimit .lambda-eval (conv-transf α Xx₁) .transf-eq s)
               (α .transf s .transf x .func-resp-≈ Xx₁≈Xx₂ .lower)
  lim .lambda-ext {X} f .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower = begin
      isLimit .lambda x (conv-transf (((id よ ∘H cone) ∘ constF-F よ apex) ∘ constFmor f) Xx₁)
    ≈⟨ isLimit .lambda-cong (record { transf-eq = λ s → 𝒞.≈-refl }) ⟩
      isLimit .lambda x (cone ∘ constFmor (f .transf x .func Xx₁ .lower))
    ≈⟨ isLimit .lambda-ext _ ⟩
      f .transf x .func Xx₁ .lower
    ≈⟨ f .transf x .func-resp-≈ Xx₁≈Xx₂ .lower ⟩
      f .transf x .func Xx₂ .lower
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

-- FIXME: Yoneda embedding also preserves exponentials. Slick proof given here:
--
--   https://math.stackexchange.com/questions/3511252/show-that-the-yoneda-embedding-preserves-exponential-objects?rq=1
