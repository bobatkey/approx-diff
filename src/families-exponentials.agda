{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (_⊔_)
open import Data.Product using (_,_)
open import prop using (_,_)
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories
  using (Category; HasExponentials; HasProducts; HasCoproducts)
open import fam
  using (HasSetoidProducts; Fam;
         _⇒f_; _≃f_; ≃f-isEquivalence;
         idf; _∘f_; ∘f-cong; ≃f-assoc; ≃f-id-right; ≃f-id-left;
         _[_]; reindex-≈; reindex-≈-refl; reindex-≈-trans; reindex-comp-≈;
         reindex-comp; constantFam; constF; reindex-f; reindex-f-cong; reindex-f-id; reindex-sq; reindex-f-comp)
open import cmon-enriched
  using (CMonEnriched; Biproduct; biproducts→products; biproducts→coproducts; copair-prod; in₁-natural; in₂-natural)
open import grothendieck using (module CategoryOfFamilies)

-- If 𝒞 has binary biproducts and Setoid-indexed products, then Fam(𝒞)
-- has exponentials.
--
-- More precisely, if 𝒞 has binary coproducts and Setoid-indexed
-- products, then the category of families has symmetric monoidal
-- structure (with the monoidal product generated by the
-- coproduct). If the coproducts are in fact biproducts, then Fam(𝒞)
-- is cartesian closed.

module families-exponentials {o m e} os es
   (𝒞 : Category o m e)
   (CM𝒞 : CMonEnriched 𝒞)
   (BP : ∀ x y → Biproduct CM𝒞 x y)
   (SP : HasSetoidProducts (m ⊔ e ⊔ os ⊔ es) (os ⊔ es ⊔ m ⊔ e) 𝒞)
       where

module Fam𝒞 = CategoryOfFamilies (m ⊔ e ⊔ os ⊔ es) (os ⊔ es ⊔ m ⊔ e) 𝒞

open Fam𝒞

open Obj
open Fam
open Mor
open _≃_

open Category 𝒞 renaming (_≈_ to _≈C_)
open IsEquivalence
open HasExponentials
open HasSetoidProducts
open HasProducts
open HasCoproducts

private
  P  = biproducts→products _ BP
  CP = biproducts→coproducts _ BP
open products P

open Setoid
open _⇒s_
open _⇒f_
open _≈s_
open _≃f_

_⟶_ : Obj → Obj → Obj
(X ⟶ Y) .idx = Category.hom-setoid cat X Y
(X ⟶ Y) .fam .fm f = SP .Π (X .idx) (Y .fam [ f .idxf ])
(X ⟶ Y) .fam .subst {f} {g} e =
  Π-map SP (reindex-≈ (f .idxf) (g .idxf) (e .idxf-eq))
(X ⟶ Y) .fam .refl* {f} =
  isEquiv .trans (Π-map-cong SP (reindex-≈-refl (f .idxf))) (Π-map-id SP)
(X ⟶ Y) .fam .trans* {f} {g} {h} g≈h f≈g =
  isEquiv .trans (Π-map-cong SP (reindex-≈-trans _ _)) (Π-map-comp SP _ _)

eval⟶ : ∀ {X Y : Obj} → Mor ((X ⟶ Y) ⊗ X) Y
eval⟶ .idxf .func (f , x) = f .idxf .func x
eval⟶ .idxf .func-resp-≈ (f₁≈f₂ , x₁≈x₂) = f₁≈f₂ .idxf-eq .func-eq x₁≈x₂
eval⟶ .famf .transf (f , x) =
  CP .copair (SP .evalΠ _ x) (f .famf .transf x)
eval⟶ {X} {Y} .famf .natural {f₁ , x₁} {f₂ , x₂} (f₁≈f₂ , x₁≈x₂) =
  begin
    CP .copair (SP .evalΠ (Y .fam [ f₂ .idxf ]) x₂) (f₂ .famf .transf x₂) ∘ prod-m P ((X ⟶ Y) .fam .subst f₁≈f₂) (X .fam .subst x₁≈x₂)
  ≈⟨ copair-prod _ BP ⟩
    CP .copair (SP .evalΠ (Y .fam [ f₂ .idxf ]) x₂ ∘ (X ⟶ Y) .fam .subst f₁≈f₂) (f₂ .famf .transf x₂ ∘ X .fam .subst x₁≈x₂)
  ≈⟨ CP .copair-cong (SP .lambda-eval x₂) (f₂ .famf .natural x₁≈x₂) ⟩
    CP .copair (Y .fam .subst _ ∘ SP .evalΠ (Y .fam [ f₁ .idxf ]) x₂) (Y .fam .subst _ ∘ f₂ .famf .transf x₁)
  ≈˘⟨ CP .copair-cong (∘-cong ≈-refl (SP .evalΠ-cong x₁≈x₂)) (∘-cong ≈-refl (f₁≈f₂ .famf-eq .transf-eq)) ⟩
    CP .copair (Y .fam .subst _ ∘ (Y .fam .subst _ ∘ SP .evalΠ (Y .fam [ f₁ .idxf ]) x₁)) (Y .fam .subst _ ∘ (Y .fam .subst _ ∘ f₁ .famf .transf x₁))
  ≈˘⟨ CP .copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
    CP .copair ((Y .fam .subst _ ∘ Y .fam .subst _) ∘ SP .evalΠ (Y .fam [ f₁ .idxf ]) x₁) ((Y .fam .subst _ ∘ Y .fam .subst _) ∘ f₁ .famf .transf x₁)
  ≈˘⟨ CP .copair-cong (∘-cong (Y .fam .trans* _ _) ≈-refl) (∘-cong (Y .fam .trans* _ _) ≈-refl) ⟩
    CP .copair (Y .fam .subst _ ∘ SP .evalΠ (Y .fam [ f₁ .idxf ]) x₁) (Y .fam .subst _ ∘ f₁ .famf .transf x₁)
  ≈˘⟨ copair-natural CP _ _ _ ⟩
    Y .fam .subst _ ∘ CP .copair (SP .evalΠ (Y .fam [ f₁ .idxf ]) x₁) (f₁ .famf .transf x₁)
  ∎
  where open ≈-Reasoning isEquiv

nudge : ∀ {X Y : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es)} → X .Carrier → Y ⇒s ⊗-setoid X Y
nudge x .func y = x , y
nudge {X} x .func-resp-≈ e = X .refl , e

nudge-≈ : ∀ {X Y : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es)} {x₁ x₂} → X ._≈_ x₁ x₂ → nudge {X = X} {Y = Y} x₁ ≈s nudge x₂
nudge-≈ x₁≈x₂ .func-eq y₁≈y₂ = x₁≈x₂ , y₁≈y₂

nudge-in₁ : ∀ {X Y : Obj} (x : X .idx .Carrier) →
           constantFam _ _ (X .fam .fm x) ⇒f ((X ⊗ Y) .fam [ nudge x ])
nudge-in₁ {X} {Y} x .transf y = CP .in₁
nudge-in₁ {X} {Y} x .natural e =
  begin
    CP .in₁ ∘ id _
  ≈˘⟨ ∘-cong ≈-refl (X .fam .refl*) ⟩
    CP .in₁ ∘ X .fam .subst _
  ≈˘⟨ in₁-natural _ BP ⟩
    (X ⊗ Y) .fam .subst _ ∘ CP .in₁
  ∎
  where open ≈-Reasoning isEquiv

nudge-in₂ : ∀ {X Y : Obj} (x : X .idx .Carrier) →
            Y .fam ⇒f ((X ⊗ Y) .fam [ nudge x ])
nudge-in₂ {X} {Y} x .transf y = CP .in₂
nudge-in₂ {X} {Y} x .natural e = ≈-sym (in₂-natural _ BP)

nudge-in₂-≈ : ∀ {X Y : Obj} {x₁ x₂ : X .idx .Carrier}
              (x₁≈x₂ : X .idx ._≈_ x₁ x₂) →
              (reindex-≈ (nudge x₁) (nudge x₂) (nudge-≈ x₁≈x₂) ∘f nudge-in₂ x₁) ≃f nudge-in₂ {X = X} {Y = Y} x₂
nudge-in₂-≈ {X} {Y} x₁≈x₂ .transf-eq =
  begin
    (X ⊗ Y) .fam .subst _ ∘ CP .in₂
  ≈⟨ in₂-natural _ BP ⟩
    CP .in₂ ∘ Y .fam .subst _
  ≈⟨ ∘-cong ≈-refl (Y .fam .refl*) ⟩
    CP .in₂ ∘ id _
  ≈⟨ id-right ⟩
    CP .in₂
  ∎
  where open ≈-Reasoning isEquiv

nudge-in₁-≈ : ∀ {X Y : Obj} {x₁ x₂ : X .idx .Carrier}
              (x₁≈x₂ : X .idx ._≈_ x₁ x₂) →
              (nudge-in₁ {X = X} {Y = Y} x₂ ∘f constF (X .fam .subst x₁≈x₂)) ≃f (reindex-≈ (nudge x₁) (nudge x₂) (nudge-≈ x₁≈x₂) ∘f nudge-in₁ x₁)
nudge-in₁-≈ {X} {Y} x₁≈x₂ .transf-eq = ≈-sym (in₁-natural _ BP)

lambda⟶ : ∀ {X Y Z} → Mor (X ⊗ Y) Z → Mor X (Y ⟶ Z)
lambda⟶ f .idxf .func x .idxf = f .idxf ∘S nudge x
lambda⟶ f .idxf .func x .famf = reindex-comp ∘f ((reindex-f (nudge x) (f .famf)) ∘f nudge-in₂ x)
lambda⟶ f .idxf .func-resp-≈ x₁≈x₂ .idxf-eq .func-eq y₁≈y₂ = f .idxf .func-resp-≈ (x₁≈x₂ , y₁≈y₂)
lambda⟶ {X} {Y} {Z} f .idxf .func-resp-≈ {x₁} {x₂} x₁≈x₂ .famf-eq =
  begin
    reindex-≈ (f .idxf ∘S nudge x₁) (f .idxf ∘S nudge x₂) _ ∘f (reindex-comp ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁))
  ≈˘⟨ ≃f-assoc _ _ _ ⟩
    (reindex-≈ (f .idxf ∘S nudge x₁) (f .idxf ∘S nudge x₂) _ ∘f reindex-comp) ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁)
  ≈⟨ ∘f-cong (reindex-comp-≈ _ _ (nudge-≈ x₁≈x₂)) ≃f-refl ⟩
    (reindex-comp ∘f (reindex-≈ (nudge x₁) (nudge x₂) _ ∘f reindex-f (nudge x₁) (reindex-≈ _ _ _))) ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁)
  ≈⟨ ∘f-cong (∘f-cong ≃f-refl (∘f-cong ≃f-refl (reindex-f-cong (reindex-≈-refl _)))) ≃f-refl ⟩
    (reindex-comp ∘f (reindex-≈ (nudge x₁) (nudge x₂) _ ∘f reindex-f (nudge x₁) (idf _))) ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁)
  ≈⟨ ∘f-cong (∘f-cong ≃f-refl (∘f-cong ≃f-refl (reindex-f-id _ _))) ≃f-refl ⟩
    (reindex-comp ∘f (reindex-≈ (nudge x₁) (nudge x₂) _ ∘f idf _)) ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁)
  ≈⟨ ∘f-cong (∘f-cong ≃f-refl ≃f-id-right) ≃f-refl ⟩
    (reindex-comp ∘f reindex-≈ (nudge x₁) (nudge x₂) _) ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁)
  ≈⟨ ≃f-assoc _ _ _ ⟩
    reindex-comp ∘f (reindex-≈ (nudge x₁) (nudge x₂) _ ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₂ x₁))
  ≈˘⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
    reindex-comp ∘f ((reindex-≈ (nudge x₁) (nudge x₂) _ ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₂ x₁)
  ≈˘⟨ ∘f-cong ≃f-refl (∘f-cong (reindex-sq _ _) ≃f-refl) ⟩
    reindex-comp ∘f ((reindex-f (nudge x₂) (f .famf) ∘f reindex-≈ (nudge x₁) (nudge x₂) _) ∘f nudge-in₂ x₁)
  ≈⟨ ∘f-cong ≃f-refl (≃f-assoc _ _ _) ⟩
    reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f (reindex-≈ (nudge x₁) (nudge x₂) _ ∘f nudge-in₂ x₁))
  ≈⟨ ∘f-cong ≃f-refl (∘f-cong ≃f-refl (nudge-in₂-≈ x₁≈x₂)) ⟩
    reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f nudge-in₂ x₂)
  ∎
  where open ≈-Reasoning ≃f-isEquivalence
lambda⟶ {X} {Y} {Z} f .famf .transf x =
  SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x) (f .famf) ∘f nudge-in₁ x))
lambda⟶ {X} {Y} {Z} f .famf .natural {x₁} {x₂} x₁≈x₂ =
  begin
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f nudge-in₁ x₂)) ∘ X .fam .subst x₁≈x₂
  ≈⟨ lambdaΠ-natural SP _ _ ⟩
    SP .lambdaΠ _ _ ((reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f nudge-in₁ x₂)) ∘f constF (X .fam .subst x₁≈x₂))
  ≈⟨ SP .lambdaΠ-cong (≃f-assoc _ _ _) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f ((reindex-f (nudge x₂) (f .famf) ∘f nudge-in₁ x₂) ∘f constF (X .fam .subst x₁≈x₂)))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (≃f-assoc _ _ _)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f (nudge-in₁ x₂ ∘f constF (X .fam .subst x₁≈x₂))))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (∘f-cong ≃f-refl (nudge-in₁-≈ x₁≈x₂))) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x₂) (f .famf) ∘f (reindex-≈ _ _ _ ∘f nudge-in₁ x₁)))
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (≃f-assoc _ _ _)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f ((reindex-f (nudge x₂) (f .famf) ∘f reindex-≈ _ _ _) ∘f nudge-in₁ x₁))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (∘f-cong (reindex-sq _ _) ≃f-refl)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f ((reindex-≈ _ _ _ ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁))
  ≈˘⟨ SP .lambdaΠ-cong (≃f-assoc _ _ _) ⟩
    SP .lambdaΠ _ _ ((reindex-comp ∘f (reindex-≈ _ _ _ ∘f reindex-f (nudge x₁) (f .famf))) ∘f nudge-in₁ x₁)
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong (≃f-assoc _ _ _) ≃f-refl) ⟩
    SP .lambdaΠ _ _ (((reindex-comp ∘f reindex-≈ _ _ _) ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁)
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong (∘f-cong ≃f-refl ≃f-id-right) ≃f-refl) ≃f-refl) ⟩
    SP .lambdaΠ _ _ (((reindex-comp ∘f (reindex-≈ _ _ _ ∘f idf _)) ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁)
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong (∘f-cong ≃f-refl (∘f-cong ≃f-refl (reindex-f-id _ (nudge x₁)))) ≃f-refl) ≃f-refl) ⟩
    SP .lambdaΠ _ _ (((reindex-comp ∘f (reindex-≈ _ _ _ ∘f reindex-f _ (idf _))) ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁)
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong (∘f-cong ≃f-refl (∘f-cong ≃f-refl (reindex-f-cong (reindex-≈-refl _)))) ≃f-refl) ≃f-refl) ⟩
    SP .lambdaΠ _ _ (((reindex-comp ∘f (reindex-≈ _ _ _ ∘f reindex-f _ (reindex-≈ _ _ _))) ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁)
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong (reindex-comp-≈ _ _ _) ≃f-refl) ≃f-refl) ⟩
    SP .lambdaΠ _ _ (((reindex-≈ _ _ _ ∘f reindex-comp) ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁)
  ≈⟨ SP .lambdaΠ-cong (∘f-cong (≃f-assoc _ _ _) ≃f-refl) ⟩
    SP .lambdaΠ _ _ ((reindex-≈ _ _ _ ∘f (reindex-comp ∘f reindex-f (nudge x₁) (f .famf))) ∘f nudge-in₁ x₁)
  ≈⟨ SP .lambdaΠ-cong (≃f-assoc _ _ _) ⟩
    SP .lambdaΠ _ _ (reindex-≈ _ _ _ ∘f ((reindex-comp ∘f reindex-f (nudge x₁) (f .famf)) ∘f nudge-in₁ x₁))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (≃f-assoc _ _ _)) ⟩
    SP .lambdaΠ _ _ (reindex-≈ _ _ _ ∘f (reindex-comp ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₁ x₁)))
  ≈⟨ lambda-compose SP _ _ ⟩
    Π-map SP (reindex-≈ _ _ _) ∘ SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x₁) (f .famf) ∘f nudge-in₁ x₁))
  ∎
  where open ≈-Reasoning isEquiv

private
  module PP = HasProducts products

lambda⟶-cong : ∀ {X Y Z} {f₁ f₂ : Mor (X ⊗ Y) Z} → f₁ ≃ f₂ → lambda⟶ f₁ ≃ lambda⟶ f₂
lambda⟶-cong f₁≃f₂ .idxf-eq .func-eq x₁≈x₂ .idxf-eq .func-eq y₁≈y₂ = f₁≃f₂ .idxf-eq .func-eq (x₁≈x₂ , y₁≈y₂)
lambda⟶-cong {X} {Y} {Z} {f₁} {f₂} f₁≃f₂ .idxf-eq .func-eq {x₁} {x₂} x₁≈x₂ .famf-eq .transf-eq {y} = begin
    Z .fam .subst _ ∘ (id _ ∘ (f₁ .famf .transf (x₁ , y) ∘ CP .in₂))
  ≈⟨ ∘-cong ≈-refl id-left ⟩
    Z .fam .subst _ ∘ (f₁ .famf .transf (x₁ , y) ∘ CP .in₂)
  ≈˘⟨ assoc _ _ _ ⟩
    (Z .fam .subst _ ∘ f₁ .famf .transf (x₁ , y)) ∘ CP .in₂
  ≈⟨ ∘-cong (∘-cong (Z .fam .trans* (f₁≃f₂ .idxf-eq .func-eq (X .idx .refl , Y .idx .refl) ) (f₁ .idxf .func-resp-≈ (x₁≈x₂ , (Y .idx .refl)))) ≈-refl) ≈-refl ⟩
    ((Z .fam .subst _ ∘ Z .fam .subst _) ∘ f₁ .famf .transf (x₁ , y)) ∘ CP .in₂
  ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    (Z .fam .subst _ ∘ (Z .fam .subst _ ∘ f₁ .famf .transf (x₁ , y))) ∘ CP .in₂
  ≈⟨ ∘-cong (∘-cong ≈-refl (≈-sym (f₁ .famf .natural (x₁≈x₂ , Y .idx .refl)))) ≈-refl ⟩
    (Z .fam .subst _ ∘ (f₁ .famf .transf (x₂ , y) ∘ (X ⊗ Y) .fam .subst _)) ∘ CP .in₂
  ≈˘⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
    ((Z .fam .subst _ ∘ f₁ .famf .transf (x₂ , y)) ∘ (X ⊗ Y) .fam .subst _) ∘ CP .in₂
  ≈⟨ assoc _ _ _ ⟩
    (Z .fam .subst _ ∘ f₁ .famf .transf (x₂ , y)) ∘ ((X ⊗ Y) .fam .subst _ ∘ CP .in₂)
  ≈⟨ ∘-cong (f₁≃f₂ .famf-eq .transf-eq) (in₂-natural _ BP) ⟩
    f₂ .famf .transf (x₂ , y) ∘ (CP .in₂ ∘ Y .fam .subst _)
  ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (Y .fam .refl*)) ⟩
    f₂ .famf .transf (x₂ , y) ∘ (CP .in₂ ∘ id _)
  ≈⟨ ∘-cong ≈-refl id-right ⟩
    f₂ .famf .transf (x₂ , y) ∘ CP .in₂
  ≈˘⟨ id-left ⟩
    id _ ∘ (f₂ .CategoryOfFamilies.Mor.famf .transf (x₂ , y) ∘ CP .in₂)
  ∎
  where open ≈-Reasoning isEquiv
lambda⟶-cong {X}{Y}{Z}{f₁}{f₂} f₁≃f₂ .famf-eq .transf-eq {x} = begin
    Π-map SP (reindex-≈ (f₁ .idxf ∘S nudge x) (f₂ .idxf ∘S nudge x) _) ∘ SP .lambdaΠ (X .fam .fm x) (Z .fam [ f₁ .idxf ∘S nudge x ]) (reindex-comp ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x))
  ≈˘⟨ lambda-compose SP _ _ ⟩
    SP .lambdaΠ _ _ (reindex-≈ (f₁ .idxf ∘S nudge x) (f₂ .idxf ∘S nudge x) _ ∘f (reindex-comp ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x)))
  ≈˘⟨ SP .lambdaΠ-cong (≃f-assoc _ _ _) ⟩
    SP .lambdaΠ _ _ ((reindex-≈ (f₁ .idxf ∘S nudge x) (f₂ .idxf ∘S nudge x) _ ∘f reindex-comp) ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong (reindex-comp-≈ _ _ _) ≃f-refl) ⟩
    SP .lambdaΠ _ _ ((reindex-comp ∘f (reindex-≈ (nudge x) (nudge x) _ ∘f reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq)))) ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong ≃f-refl (∘f-cong (reindex-≈-refl _) ≃f-refl)) ≃f-refl) ⟩
    SP .lambdaΠ _ _ ((reindex-comp ∘f (idf _ ∘f reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq)))) ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong (∘f-cong ≃f-refl ≃f-id-left) ≃f-refl) ⟩
    SP .lambdaΠ _ _ ((reindex-comp ∘f reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq))) ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (≃f-assoc _ _ _) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq)) ∘f (reindex-f (nudge x) (f₁ .famf) ∘f nudge-in₁ x)))
  ≈˘⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (≃f-assoc _ _ _)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f ((reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq)) ∘f reindex-f (nudge x) (f₁ .famf)) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (∘f-cong (reindex-f-comp _ _) ≃f-refl)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x) (reindex-≈ (f₁ .idxf) (f₂ .idxf) (f₁≃f₂ .idxf-eq) ∘f f₁ .famf) ∘f nudge-in₁ x))
  ≈⟨ SP .lambdaΠ-cong (∘f-cong ≃f-refl (∘f-cong (reindex-f-cong (f₁≃f₂ .famf-eq)) ≃f-refl)) ⟩
    SP .lambdaΠ _ _ (reindex-comp ∘f (reindex-f (nudge x) (f₂ .famf) ∘f nudge-in₁ x))
  ∎
  where open ≈-Reasoning isEquiv

β-rule : ∀ {X Y Z} (f : Mor (X ⊗ Y) Z) →
         Mor-∘ eval⟶ (PP.prod-m (lambda⟶ f) (Mor-id _)) ≃ f
β-rule f .idxf-eq .func-eq = f .idxf .func-resp-≈
β-rule {X} {Y} {Z} f .famf-eq .transf-eq {x , y} =
  begin
    Z .fam .subst _ ∘ (id _ ∘ (CP .copair (SP .evalΠ _ y) (id _ ∘ (f .famf .transf (x , y) ∘ CP .in₂)) ∘ P .pair (id _ ∘ (lambda⟶ f .famf .transf x ∘ P .p₁)) (id _ ∘ (id _ ∘ P .p₂))))
  ≈⟨ ∘-cong (Z .fam .refl*) (∘-cong ≈-refl (∘-cong (CP .copair-cong ≈-refl id-left) (P .pair-cong id-left id-left))) ⟩
    id _ ∘ (id _ ∘ (CP .copair (SP .evalΠ _ y) (f .famf .transf (x , y) ∘ CP .in₂) ∘ P .pair (lambda⟶ f .famf .transf x ∘ P .p₁) (id _ ∘ P .p₂)))
  ≈⟨ id-left ⟩
    id _ ∘ (CP .copair (SP .evalΠ _ y) (f .famf .transf (x , y) ∘ CP .in₂) ∘ P .pair (lambda⟶ f .famf .transf x ∘ P .p₁) (id _ ∘ P .p₂))
  ≈⟨ id-left ⟩
    CP .copair (SP .evalΠ _ y) (f .famf .transf (x , y) ∘ CP .in₂) ∘ P .pair (lambda⟶ f .famf .transf x ∘ P .p₁) (id _ ∘ P .p₂)
  ≈⟨ copair-prod _ BP ⟩
    CP .copair (SP .evalΠ _ y ∘ lambda⟶ f .famf .transf x) ((f .famf .transf (x , y) ∘ CP .in₂) ∘ id _)
  ≈⟨ CP .copair-cong (SP .lambda-eval y) id-right ⟩
    CP .copair (id _ ∘ (f .famf .transf (x , y) ∘ CP .in₁)) (f .famf .transf (x , y) ∘ CP .in₂)
  ≈⟨ CP .copair-cong id-left ≈-refl ⟩
    CP .copair (f .famf .transf (x , y) ∘ CP .in₁) (f .famf .transf (x , y) ∘ CP .in₂)
  ≈⟨ CP .copair-ext _ ⟩
    f .famf .transf (x , y)
  ∎
  where open ≈-Reasoning isEquiv

open import Data.Product using (proj₁; proj₂)

lambda-ext' : ∀ {X Y Z} (f : Mor X (Y ⟶ Z)) →
             lambda⟶ (Mor-∘ eval⟶ (PP.prod-m f (Mor-id _))) ≃ f
lambda-ext' f .idxf-eq .func-eq x₁≈x₂ .idxf-eq .func-eq y₁≈y₂ =
  f .idxf .func-resp-≈ x₁≈x₂ .idxf-eq .func-eq y₁≈y₂
lambda-ext' {X} {Y} {Z} f .idxf-eq .func-eq {x₁} {x₂} x₁≈x₂ .famf-eq .transf-eq {y} =
  let q : f .idxf .func x₁ ≃ f .idxf .func x₂
      q = {!   !} in
  begin
    Z .fam .subst _ ∘ (id (Z .fam .fm (Mor-∘ eval⟶ (PP.prod-m f (Mor-id Y)) .idxf .func (x₁ , y))) ∘
                       (Mor-∘ eval⟶ (PP.prod-m f (Mor-id Y)) .famf .transf (x₁ , y) ∘ CP .in₂))
  ≈⟨ ∘-cong ≈-refl id-left ⟩
    Z .fam .subst _ ∘ (Mor-∘ eval⟶ (PP.prod-m f (Mor-id Y)) .famf .transf (x₁ , y) ∘ CP .in₂)
  ≈⟨ ∘-cong ≈-refl (∘-cong id-left ≈-refl) ⟩
    Z .fam .subst _ ∘ ((CP .copair (SP .evalΠ (Z .fam [ f .idxf .func x₁ .idxf ]) y) (f .idxf .func x₁ .famf .transf y) ∘
                        PP.prod-m f (Mor-id Y) .famf .transf (x₁ , y)) ∘ CP .in₂)
  ≈⟨ ∘-cong ≈-refl (∘-cong (∘-cong ≈-refl (P .pair-cong id-left id-left)) ≈-refl) ⟩
    Z .fam .subst _ ∘ ((CP .copair (SP .evalΠ (Z .fam [ f .idxf .func x₁ .idxf ]) y) (f .idxf .func x₁ .famf .transf y) ∘
                        prod-m P (f .famf .transf x₁) (id (Y .fam .fm y))) ∘ CP .in₂)
  ≈⟨ ∘-cong ≈-refl (∘-cong (copair-prod _ BP) ≈-refl) ⟩
    Z .fam .subst _ ∘ (CP .copair (SP .evalΠ (Z .fam [ f .idxf .func x₁ .idxf ]) y ∘ f .famf .transf x₁)
                                  (f .idxf .func x₁ .famf .transf y ∘ id (Y .fam .fm y)) ∘ CP .in₂)
  ≈⟨ ∘-cong ≈-refl (CP .copair-in₂ _ _) ⟩
    Z .fam .subst _ ∘ (f .idxf .func x₁ .famf .transf y ∘ id (Y .fam .fm y))
  ≈⟨ ∘-cong ≈-refl id-right ⟩
    Z .fam .subst _ ∘ f .idxf .func x₁ .famf .transf y
  ≈⟨ q .famf-eq .transf-eq ⟩
    f .idxf .func x₂ .famf .transf y
  ∎ where open ≈-Reasoning isEquiv
lambda-ext' f .famf-eq = {!   !}

exponentials : HasExponentials cat products
exponentials .exp = _⟶_
exponentials .eval = eval⟶
exponentials .lambda = lambda⟶
exponentials .lambda-cong = lambda⟶-cong
exponentials .eval-lambda f = β-rule f
exponentials .lambda-ext f = lambda-ext' f
