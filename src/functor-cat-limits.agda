{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import categories using (Category)
open import functor
  using (Functor; NatTrans; ≃-NatTrans; [_⇒_];
         _∘F_; Id; _∘H_; id; ∘H-cong; interchange; left-unit; left-unit⁻¹; F-assoc⁻¹; F-assoc;
         ≃-isEquivalence; NT-id-left; NT-assoc; _∘_; ∘NT-cong;
         constF; constF-F; constFmor; const; HasLimits';
         Limit; IsLimit; module LimitFunctor)

-- If 𝒟 has all limits of shape 𝒮, then so does [ 𝒞 ⇒ 𝒟 ].

module functor-cat-limits
         {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂)
         (𝒮 : Category o₃ m₃ e₃)
         (𝒟-limits : HasLimits' 𝒮 𝒟)
  where

private
  module 𝒮 = Category 𝒮
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module DL = HasLimits' 𝒟-limits

-- NOTE:
--   If 𝒟 has colimits, then opposite 𝒟 has limits
--   then [ opposite 𝒞 ⇒ opposite 𝒟 ] has limits
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

-- FIXME: remove the "by hand" equivalences of natural transformations
-- below and replace them with axiomatised versions.

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
  ≈⟨ DL.Π-map-cong (record { transf-eq = λ _ → 𝒟.id-left }) ⟩
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

-- FIXME: replace uses of evalAt-const with its definition below
evalAt-const : ∀ (X : Functor 𝒞 𝒟) x →
               NatTrans (constF 𝒮 (X .fobj x)) (evalAt .fobj x ∘F constF 𝒮 X)
evalAt-const X x = constF-F (evalAt .fobj x) X

lambdaΠ : ∀ (X : Functor 𝒞 𝒟) (F : Functor 𝒮 [ 𝒞 ⇒ 𝒟 ]) →
            NatTrans (constF 𝒮 {[ 𝒞 ⇒ 𝒟 ]} X) F →
            NatTrans X (Π F)
lambdaΠ X F α .transf x = DL.lambdaΠ _ _ ((id _ ∘H α) ∘ evalAt-const X x)
lambdaΠ X F α .natural {x} {y} f =
  begin
    DL.Π-map (evalAt .fmor f ∘H id F) 𝒟.∘ DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)
  ≈⟨ DL.lambdaΠ-natural _ _ ⟩
    DL.lambdaΠ _ _ (((evalAt .fmor f ∘H id F) ∘ DL.evalΠ _) ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)))
  ≈⟨ DL.lambda-cong (𝒮𝒟.assoc (evalAt .fmor f ∘H id F) (DL.evalΠ _) (constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x)))) ⟩
    DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ (DL.evalΠ _ ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x ∘F F) ((id _ ∘H α) ∘ evalAt-const X x))))
  ≈⟨ DL.lambda-cong (𝒮𝒟.∘-cong (𝒮𝒟.≈-refl {f = evalAt .fmor f ∘H id F}) (DL.lambda-eval ((id _ ∘H α) ∘ evalAt-const X x))) ⟩
    DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ ((id _ ∘H α) ∘ evalAt-const X x))
  ≈˘⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
    DL.lambdaΠ _ _ (((evalAt .fmor f ∘H id F) ∘ (id _ ∘H α)) ∘ evalAt-const X x)
  ≈˘⟨ DL.lambda-cong (∘NT-cong (interchange _ _ _ _) 𝒮𝒟.≈-refl) ⟩
    DL.lambdaΠ _ _ (((evalAt .fmor f ∘ id _) ∘H (id F ∘ α)) ∘ evalAt-const X x)
  ≈⟨ DL.lambda-cong (∘NT-cong (∘H-cong (𝒞𝒟.≈-sym 𝒞𝒟.id-swap) 𝒮𝒞𝒟.id-swap) 𝒮𝒟.≈-refl) ⟩
    DL.lambdaΠ _ _ (((id _ ∘ evalAt .fmor f) ∘H (α ∘ id _)) ∘ evalAt-const X x)
  ≈⟨ DL.lambda-cong (∘NT-cong (interchange _ _ _ _) 𝒮𝒟.≈-refl) ⟩
    DL.lambdaΠ _ _ (((id _ ∘H α) ∘ (evalAt .fmor f ∘H id _)) ∘ evalAt-const X x)
  ≈⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
    DL.lambdaΠ _ _ ((id _ ∘H α) ∘ ((evalAt .fmor f ∘H id _) ∘ evalAt-const X x))
  ≈⟨ DL.lambda-cong (∘NT-cong 𝒮𝒟.≈-refl (record { transf-eq = λ s → 𝒟.isEquiv .trans 𝒟.id-right (𝒟.≈-sym 𝒟.id-swap) })) ⟩
    DL.lambdaΠ _ _ ((id _ ∘H α) ∘ (evalAt-const X y ∘ constFmor (X .fmor f)))
  ≈˘⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
    DL.lambdaΠ _ _ (((id _ ∘H α) ∘ evalAt-const X y) ∘ constFmor (X .fmor f))
  ≈⟨ 𝒟.≈-sym (DL.lambdaΠ-natural _ _) ⟩
    DL.lambdaΠ _ _ ((id _ ∘H α) ∘ evalAt-const X y) 𝒟.∘ X .fmor f
  ∎ where open ≈-Reasoning 𝒟.isEquiv
          module 𝒮𝒟 = Category [ 𝒮 ⇒ 𝒟 ]
          module 𝒞𝒟 = Category [ [ 𝒞 ⇒ 𝒟 ] ⇒ 𝒟 ]
          module 𝒮𝒞𝒟 = Category [ 𝒮 ⇒ [ 𝒞 ⇒ 𝒟 ] ]

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

limits : HasLimits' 𝒮 [ 𝒞 ⇒ 𝒟 ]
limits .HasLimits'.Π = Π
limits .HasLimits'.lambdaΠ = lambdaΠ
limits .HasLimits'.evalΠ = evalΠ
limits .HasLimits'.lambda-cong α≃β .transf-eq x =
  DL.lambda-cong (∘NT-cong (∘H-cong (≃-isEquivalence .refl) α≃β) (≃-isEquivalence .refl))
limits .HasLimits'.lambda-eval {X} {F} α .transf-eq s .transf-eq x =
  𝒟.isEquiv .trans
     (DL.lambda-eval _ .transf-eq s)
     (𝒟.isEquiv .trans (𝒟.∘-cong 𝒟.id-left 𝒟.≈-refl) 𝒟.id-right)
limits .HasLimits'.lambda-ext {X} {F} α .transf-eq x =
  𝒟.isEquiv .trans
    (DL.lambda-cong (record { transf-eq = λ s → 𝒟.isEquiv .trans 𝒟.id-right 𝒟.id-left }))
    (DL.lambda-ext (α .transf x))

{-
-- A “higher-level” approach, which requires more equational reasoning
-- at the bicategory of categories level.

swapArgs : Functor [ 𝒮 ⇒ [ 𝒞 ⇒ 𝒟 ] ] [ 𝒞 ⇒ [ 𝒮 ⇒ 𝒟 ] ]
swapArgs .fobj F .fobj x .fobj s = F .fobj s .fobj x
swapArgs .fobj F .fobj x .fmor f = F .fmor f .transf x
swapArgs .fobj F .fobj x .fmor-cong f₁≈f₂ = F .fmor-cong f₁≈f₂ .transf-eq x
swapArgs .fobj F .fobj x .fmor-id = F .fmor-id .transf-eq x
swapArgs .fobj F .fobj x .fmor-comp f g = F .fmor-comp f g .transf-eq x
swapArgs .fobj F .fmor g .transf s = F .fobj s .fmor g
swapArgs .fobj F .fmor g .natural f = 𝒟.≈-sym (F .fmor f .natural g)
swapArgs .fobj F .fmor-cong g₁≈g₂ .transf-eq x = F .fobj x .fmor-cong g₁≈g₂
swapArgs .fobj F .fmor-id .transf-eq s = F .fobj s .fmor-id
swapArgs .fobj F .fmor-comp f g .transf-eq s = F .fobj s .fmor-comp f g
swapArgs .fmor α .transf x .transf s = α .transf s .transf x
swapArgs .fmor α .transf x .natural f = α .natural f .transf-eq x
swapArgs .fmor α .natural f .transf-eq s = α .transf s .natural f
swapArgs .fmor-cong α≈β .transf-eq x .transf-eq s = α≈β .transf-eq s .transf-eq x
swapArgs .fmor-id .transf-eq x .transf-eq s = 𝒟.≈-refl
swapArgs .fmor-comp f g .transf-eq x .transf-eq s = 𝒟.≈-refl

swapArgs⁻¹ : ∀ {F G} → NatTrans (swapArgs .fobj F) (swapArgs .fobj G) → NatTrans F G
swapArgs⁻¹ α .transf s .transf x = α .transf x .transf s
swapArgs⁻¹ α .transf s .natural f = α .natural f .transf-eq s
swapArgs⁻¹ α .natural f .transf-eq x = α .transf x .natural f

swap-const : ∀ (F : Functor 𝒞 𝒟) → NatTrans (const ∘F F) (swapArgs .fobj (constF 𝒮 F))
swap-const F .transf x .transf s = 𝒟.id _
swap-const F .transf x .natural f = 𝒟.≈-refl
swap-const F .natural f .transf-eq s = 𝒟.id-swap'

swap-const⁻¹ : ∀ (F : Functor 𝒞 𝒟) → NatTrans (swapArgs .fobj (constF 𝒮 F)) (const ∘F F)
swap-const⁻¹ F .transf x .transf s = 𝒟.id _
swap-const⁻¹ F .transf x .natural f = 𝒟.≈-refl
swap-const⁻¹ F .natural f .transf-eq s = 𝒟.id-swap'

open Limit
open IsLimit

open LimitFunctor 𝒟-limits

limits : (D : Functor 𝒮 [ 𝒞 ⇒ 𝒟 ]) → Limit D
limits D .apex = Π ∘F swapArgs .fobj D
limits D .cone =
  swapArgs⁻¹ (left-unit _ ∘ ((counitΠ ∘H id _) ∘ (F-assoc⁻¹ ∘ swap-const⁻¹ _)))
limits D .isLimit .lambda F α =
  (id _ ∘H (swapArgs .fmor α ∘ swap-const F)) ∘ (F-assoc ∘ ((unitΠ ∘H id _) ∘ left-unit⁻¹ F))
limits D .isLimit .lambda-cong α≃β =
  ∘NT-cong (∘H-cong (≃-isEquivalence .refl) (∘NT-cong (swapArgs .fmor-cong α≃β) (≃-isEquivalence .refl))) (≃-isEquivalence .refl)
limits D .isLimit .lambda-eval {F} α = {!!}
limits D .isLimit .lambda-ext {F} α = {!!}
-}
