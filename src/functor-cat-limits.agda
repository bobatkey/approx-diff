{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories
open import functor

module functor-cat-limits
         {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂)
         (𝒮 : Category o₃ m₃ e₃)
         (𝒟-limits : HasLimits 𝒮 𝒟)
  where

private
  module 𝒮 = Category 𝒮
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module DL = HasLimits 𝒟-limits

-- NOTE:
--   If 𝒟 has colimits, then opposite 𝒟 has limits
--   then [ 𝒞 ⇒ opposite 𝒟 ] has limits
--   which is equivalent to opposite [ 𝒞 ⇒ 𝒟 ], which will have limits
--   hence [ 𝒞 ⇒ 𝒟 ] has colimits.
-- Can this reasoning be formalised?

open IsEquivalence
open Functor
open NatTrans
open ≃-NatTrans

-- FIXME: this should probably be next to the definition of functor category
evalAt : Functor 𝒞 [ [ 𝒞 ⇒ 𝒟 ] ⇒ 𝒟 ]
evalAt .fobj x .fobj F = F .fobj x
evalAt .fobj x .fmor α = α .transf x
evalAt .fobj x .fmor-cong F₁≃F₂ = F₁≃F₂ .transf-eq x
evalAt .fobj x .fmor-id = 𝒟.≈-refl
evalAt .fobj x .fmor-comp f g = 𝒟.≈-refl
evalAt .fmor f .transf F = F .fmor f
evalAt .fmor f .natural α = 𝒟.≈-sym (α .natural f)
evalAt .fmor-cong f₁≈f₂ .transf-eq F = F .fmor-cong f₁≈f₂
evalAt .fmor-id .transf-eq F = F .fmor-id
evalAt .fmor-comp f g .transf-eq F = F .fmor-comp f g

Π : Functor 𝒮 [ 𝒞 ⇒ 𝒟 ] → Functor 𝒞 𝒟
Π F .fobj x = DL.Π (evalAt .fobj x ∘F F)
Π F .fmor f = DL.Π-map (evalAt .fmor f ∘H id F)
Π F .fmor-cong f₁≈f₂ =
  DL.Π-map-cong (∘H-cong (evalAt .fmor-cong f₁≈f₂) (≃-isEquivalence .refl {id F}))
Π F .fmor-id {x} =
  begin
    DL.Π-map (evalAt .fmor (𝒞 .Category.id x) ∘H id F)
  ≈⟨ DL.Π-map-cong (∘H-cong (evalAt .fmor-id) (≃-isEquivalence .refl {id F})) ⟩
    DL.Π-map (id (evalAt .fobj x) ∘H id F)
  ≈⟨ DL.Π-map-cong (record { transf-eq = λ _ → 𝒟.id-left }) ⟩ -- FIXME: work out id-left for vertical composition
    DL.Π-map (id _)
  ≈⟨ DL.Π-map-id ⟩
    𝒟.id (DL.Π (evalAt .fobj x ∘F F))
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
Π F .fmor-comp {x} {y} {z} f g =
  begin
    DL.Π-map (evalAt .fmor (f 𝒞.∘ g) ∘H id F)
  ≈⟨ DL.Π-map-cong (∘H-cong (evalAt .fmor-comp f g) (≃-isEquivalence .sym NT-id-left)) ⟩
    DL.Π-map ((evalAt .fmor f ∘ evalAt .fmor g) ∘H (id F ∘ id F))
  ≈⟨ DL.Π-map-cong (interchange _ _ _ _) ⟩
    DL.Π-map ((evalAt .fmor f ∘H id F) ∘ (evalAt .fmor g ∘H id F))
  ≈⟨ DL.Π-map-comp _ _ ⟩
    DL.Π-map (evalAt .fmor f ∘H id F) 𝒟.∘ DL.Π-map (evalAt .fmor g ∘H id F)
  ∎
  where open ≈-Reasoning 𝒟.isEquiv

evalAt-const : ∀ (X : Functor 𝒞 𝒟) x →
               NatTrans (constF 𝒮 (X .fobj x)) (evalAt .fobj x ∘F constF 𝒮 X)
evalAt-const X x .transf s = 𝒟.id _
evalAt-const X x .natural f = 𝒟.≈-refl

lambdaΠ : ∀ (X : Functor 𝒞 𝒟) (F : Functor 𝒮 [ 𝒞 ⇒ 𝒟 ]) →
            NatTrans (constF 𝒮 {[ 𝒞 ⇒ 𝒟 ]} X) F →
            NatTrans X (Π F)
lambdaΠ X F α .transf x =
  DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)
lambdaΠ X F α .natural {x} {y} f =
  begin
    DL.Π-map (evalAt .fmor f ∘H id F) 𝒟.∘ DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)
  ≈⟨ DL.lambdaΠ-natural _ _ ⟩
    DL.lambdaΠ _ _ (((evalAt .fmor f ∘H id F) ∘ DL.evalΠ _) ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)))
  ≈⟨ DL.lambda-cong (𝒮𝒟.assoc (evalAt .fmor f ∘H id F) (DL.evalΠ _) (constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)))) ⟩
    DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ (DL.evalΠ _ ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x))))
  ≈⟨ DL.lambda-cong (𝒮𝒟.∘-cong (𝒮𝒟.≈-refl {f = evalAt .fmor f ∘H id F}) (DL.lambda-eval ((id _ ∘H α) ∘ evalAt-const X x))) ⟩
    DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ ((id _ ∘H α) ∘ evalAt-const X x))
  ≈⟨ DL.lambda-cong {!!} ⟩ -- FIXME: vertical / horizontal interchange and naturality of evalAt-const
    DL.lambdaΠ _ _ ((((id _ ∘H α) ∘ evalAt-const X y)) ∘ constFmor (X .fmor f))
  ≈⟨ 𝒟.≈-sym (DL.lambdaΠ-natural _ _) ⟩
    DL.lambdaΠ _ _ ((id _ ∘H α) ∘ evalAt-const X y) 𝒟.∘ X .fmor f
  ∎ where open ≈-Reasoning 𝒟.isEquiv
          module 𝒮𝒟 = Category [ 𝒮 ⇒ 𝒟 ]

evalΠ : (F : Functor 𝒮 [ 𝒞 ⇒ 𝒟 ]) → NatTrans (constF 𝒮 (Π F)) F
evalΠ F .transf s .transf x = DL.evalΠ _ .transf s
evalΠ F .transf s .natural {x} {y} f =
  begin
    F .fobj s .fmor f 𝒟.∘ DL.evalΠ (evalAt .fobj x ∘F F) .transf s
  ≈⟨ 𝒟.∘-cong (𝒟.≈-sym 𝒟.id-right) 𝒟.≈-refl ⟩
    (F .fobj s .fmor f 𝒟.∘ 𝒟.id _) 𝒟.∘ DL.evalΠ (evalAt .fobj x ∘F F) .transf s
  ≈⟨ 𝒟.≈-sym (DL.lambda-eval ((evalAt .fmor f ∘H id F) ∘ DL.evalΠ _) .transf-eq s) ⟩
    DL.evalΠ (evalAt .fobj y ∘F F) .transf s 𝒟.∘ DL.Π-map (evalAt .fmor f ∘H id F)
  ∎
  where open ≈-Reasoning 𝒟.isEquiv
evalΠ F .natural f .transf-eq x = DL.evalΠ _ .natural f

limits : HasLimits 𝒮 [ 𝒞 ⇒ 𝒟 ]
limits .HasLimits.Π = Π
limits .HasLimits.lambdaΠ = lambdaΠ
limits .HasLimits.evalΠ = evalΠ
limits .HasLimits.lambda-cong α≃β .transf-eq x =
  DL.lambda-cong (∘NT-cong (∘H-cong (≃-isEquivalence .refl) α≃β) (≃-isEquivalence .refl))
limits .HasLimits.lambda-eval {X} {F} α .transf-eq s .transf-eq x =
  𝒟.isEquiv .trans
     (DL.lambda-eval _ .transf-eq s)
     (𝒟.isEquiv .trans (𝒟.∘-cong 𝒟.id-left 𝒟.≈-refl) 𝒟.id-right)
limits .HasLimits.lambda-ext {X} {F} α .transf-eq x =
  𝒟.isEquiv .trans
    (DL.lambda-cong (record { transf-eq = λ s → 𝒟.isEquiv .trans 𝒟.id-right 𝒟.id-left }))
    (DL.lambda-ext (α .transf x))
