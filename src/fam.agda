{-# OPTIONS --prop --postfix-projections --safe #-}

module fam where

open import Level
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories

-- Families of objects over a setoid
module _ {o m e} os es (𝒞 : Category o m e) (A : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es)) where

  open Setoid A
  open Category 𝒞 renaming (_≈_ to _≈C_)

  -- A family of elements indexed over a setoid (really a functor from
  -- the setoid-as-category)
  record Fam : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
    field
      fm     : Carrier → obj
      subst  : ∀ {x y} → x ≈ y → fm x ⇒ fm y
      refl*  : ∀ {x} → subst (refl {x}) ≈C id (fm x)
      trans* : ∀ {x y z} (e₁ : y ≈ z) (e₂ : x ≈ y) →
        subst (trans e₂ e₁) ≈C (subst e₁ ∘ subst e₂)

  open Fam

  constantFam : obj → Fam
  constantFam x .fm _ = x
  constantFam x .subst _ = id x
  constantFam x .refl* = isEquiv .IsEquivalence.refl
  constantFam x .trans* _ _ = isEquiv .IsEquivalence.sym id-left

module _ {o m e} {os es} {𝒞 : Category o m e} {A : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es)} where
  open Setoid A using (_≈_)
  open Category 𝒞 renaming (_≈_ to _≈C_)
  open IsEquivalence
  open Fam

  record _⇒f_ (P Q : Fam os es 𝒞 A) : Set (m ⊔ e ⊔ os ⊔ es) where
    no-eta-equality
    field
      transf  : ∀ x → P .fm x ⇒ Q .fm x
      natural : ∀ {x₁ x₂} (e : x₁ ≈ x₂) → (transf x₂ ∘ P .subst e) ≈C (Q .subst e ∘ transf x₁)

  open _⇒f_

  idf : ∀ P → P ⇒f P
  idf P .transf x = id (P .fm x)
  idf P .natural x₁≈x₂ =
    begin
      id _ ∘ P .subst _
    ≈⟨ id-left ⟩
      P .subst _
    ≈⟨ isEquiv .sym id-right ⟩
      P .subst _ ∘ id _
    ∎ where open ≈-Reasoning isEquiv

  _∘f_ : ∀ {P Q R} (f : Q ⇒f R) (g : P ⇒f Q) → P ⇒f R
  (f ∘f g) .transf x = (f .transf x) ∘ (g .transf x)
  _∘f_ {P} {Q} {R} f g .natural {x₁} {x₂} x₁≈x₂ =
    begin
      (f .transf x₂ ∘ g .transf x₂) ∘ P .subst _
         ≈⟨ assoc _ _ _ ⟩
      f .transf x₂ ∘ (g .transf x₂ ∘ P .subst _)
         ≈⟨ ∘-cong (isEquiv .refl) (g .natural _) ⟩
      f .transf x₂ ∘ (Q .subst _ ∘ g .transf x₁)
         ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
      (f .transf x₂ ∘ Q .subst _) ∘ g .transf x₁
         ≈⟨ ∘-cong (f .natural _) (isEquiv .refl) ⟩
      (R .subst _ ∘ f .transf x₁) ∘ g .transf x₁
         ≈⟨ assoc _ _ _ ⟩
      R .subst _ ∘ (f .transf x₁ ∘ g .transf x₁)
     ∎
    where open ≈-Reasoning isEquiv

  record _≃f_ {P Q : Fam os es 𝒞 A} (f g : P ⇒f Q) : Prop (m ⊔ e ⊔ os ⊔ es) where
    no-eta-equality
    field
      transf-eq : ∀ {x} → f .transf x ≈C g .transf x

  open _≃f_

  ≃f-isEquivalence : ∀ {P Q} → IsEquivalence (_≃f_ {P} {Q})
  ≃f-isEquivalence .refl .transf-eq = isEquiv .refl
  ≃f-isEquivalence .sym {f} {g} f≈g .transf-eq = isEquiv .sym (f≈g .transf-eq)
  ≃f-isEquivalence .trans {f} {g} {h} f≈g g≈h .transf-eq = isEquiv .trans (f≈g .transf-eq) (g≈h .transf-eq)

  ∘f-cong : ∀ {P Q R} {f₁ f₂ : Q ⇒f R} {g₁ g₂ : P ⇒f Q} →
      f₁ ≃f f₂ → g₁ ≃f g₂ → (f₁ ∘f g₁) ≃f (f₂ ∘f g₂)
  ∘f-cong f₁≈f₂ g₁≈g₂ .transf-eq = ∘-cong (f₁≈f₂ .transf-eq) (g₁≈g₂ .transf-eq)

  ≃f-id-left : ∀ {P Q} {f : P ⇒f Q} → (idf Q ∘f f) ≃f f
  ≃f-id-left .transf-eq = id-left

  ≃f-id-right : ∀ {P Q} {f : P ⇒f Q} → (f ∘f idf P) ≃f f
  ≃f-id-right .transf-eq = id-right

  ≃f-assoc : ∀ {P Q R S} (f : R ⇒f S) (g : Q ⇒f R) (h : P ⇒f Q) →
      ((f ∘f g) ∘f h) ≃f (f ∘f (g ∘f h))
  ≃f-assoc f g h .transf-eq = assoc _ _ _

  constF : ∀ {x y} → x ⇒ y → constantFam os es 𝒞 A x ⇒f constantFam os es 𝒞 A y
  constF f .transf _ = f
  constF f .natural _ = isEquiv .trans id-right (isEquiv .sym id-left)


-- FIXME: families over a fixed setoid form a category

------------------------------------------------------------------------------
-- Change of indexed category
open import functor

module _ {o m e} os es {𝒞 𝒟 : Category o m e}
         (A : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es))
         (F : Functor 𝒞 𝒟) where

  open Fam
  open Functor
  open Category
  open IsEquivalence
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  -- FIXME: might need this to be more flexible about universe levels
  changeCat : Fam os es 𝒞 A → Fam os es 𝒟 A
  changeCat P .fm a = F .fobj (P .fm a)
  changeCat P .subst a₁≈a₂ = F .fmor (P .subst a₁≈a₂)
  changeCat P .refl* =
    𝒟 .isEquiv .trans (F .fmor-cong (P .refl*)) (F .fmor-id)
  changeCat P .trans* e₁ e₂ =
    𝒟 .isEquiv .trans (F .fmor-cong (P .trans* e₁ e₂)) (F .fmor-comp _ _)

  open _⇒f_
  open _≃f_

  changeCatF : ∀ {P Q : Fam os es 𝒞 A} → P ⇒f Q → changeCat P ⇒f changeCat Q
  changeCatF f .transf x = F .fmor (f .transf x)
  changeCatF {P} {Q} f .natural {x₁} {x₂} x₁≈x₂ =
    begin
      F .fmor (f .transf x₂) 𝒟.∘ F .fmor (P .subst _)
    ≈⟨ 𝒟.isEquiv .sym (F .fmor-comp _ _) ⟩
      F .fmor (f .transf x₂ 𝒞.∘ P .subst _)
    ≈⟨ F .fmor-cong (f .natural _) ⟩
      F .fmor (Q .subst x₁≈x₂ 𝒞.∘ f .transf x₁)
    ≈⟨ F .fmor-comp _ _ ⟩
      F .fmor (Q .subst x₁≈x₂) 𝒟.∘ F .fmor (f .transf x₁)
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  changeCatF-cong : ∀ {P Q : Fam os es 𝒞 A} {f₁ f₂ : P ⇒f Q} → f₁ ≃f f₂ → changeCatF f₁ ≃f changeCatF f₂
  changeCatF-cong f₁≈f₂ .transf-eq = F .fmor-cong (f₁≈f₂ .transf-eq)

  preserveConst : ∀ x → changeCat (constantFam os es 𝒞 A x) ⇒f constantFam os es 𝒟 A (F .fobj x)
  preserveConst x .transf a = 𝒟.id _
  preserveConst x .natural a₁≈a₂ =
    begin
      𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (𝒟.isEquiv .refl) (F .fmor-id) ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  preserveConst⁻¹ : ∀ x → constantFam os es 𝒟 A (F .fobj x) ⇒f changeCat (constantFam os es 𝒞 A x)
  preserveConst⁻¹ x .transf a = 𝒟.id _
  preserveConst⁻¹ x .natural a₁≈a₂ = 𝒟.∘-cong (𝒟.isEquiv .sym (F .fmor-id)) (𝒟.isEquiv .refl)

  -- FIXME: preserves id and composition, and preserveConst is a natural isomorphism

------------------------------------------------------------------------------
-- reindexing of families (so that Fam is an indexed category)
-- FIXME: Codify what an indexed category is
module _ {o m e os es} {𝒞 : Category o m e} where

  open _⇒s_
  open Fam

  -- NOTE: This requires that all proofs of setoid equalities are
  -- equal for the iobj-id and iobj-trans to typecheck. This is why I
  -- am using Prop.
  _[_] : ∀ {X Y} → Fam os es 𝒞 X → (Y ⇒s X) → Fam os es 𝒞 Y
  _[_] P f .fm w    = P .fm (f .func w)
  _[_] P f .subst e = P .subst (f .func-resp-≈ e)
  _[_] P f .refl*   = P .refl*
  _[_] P f .trans* e₁ e₂ = P .trans* (f .func-resp-≈ e₁) (f .func-resp-≈ e₂)

  open _⇒f_
  open _≈s_
  open Category 𝒞
  open IsEquivalence

  reindex-f : ∀ {X Y} {P Q : Fam os es 𝒞 X} (f : Y ⇒s X) → P ⇒f Q → (P [ f ]) ⇒f (Q [ f ])
  reindex-f f g .transf y = g .transf _
  reindex-f f g .natural x₁≈x₂ = g .natural (f .func-resp-≈ x₁≈x₂)

  reindex-≈ : ∀ {X Y} {P : Fam os es 𝒞 X} (f g : Y ⇒s X) → f ≈s g → (P [ f ]) ⇒f (P [ g ])
  reindex-≈ {Y = Y} {P = P} f g f≈g .transf x = P .subst (f≈g .func-eq (Y .Setoid.refl))
  reindex-≈ {Y = Y} {P = P} f g f≈g .natural y₁≈y₂ =
    isEquiv .trans (isEquiv .sym (P .trans* _ _)) (P .trans* _ _)

  open _≃f_

  reindex-f-cong : ∀ {X Y} {P Q : Fam os es 𝒞 X} {f : Y ⇒s X} {g₁ g₂ : P ⇒f Q} → g₁ ≃f g₂ → reindex-f f g₁ ≃f reindex-f f g₂
  reindex-f-cong g₁≃g₂ .transf-eq = g₁≃g₂ .transf-eq

  reindex-f-comp : ∀ {X Y} {P Q R : Fam os es 𝒞 X} {f : Y ⇒s X} (g₁ : Q ⇒f R) (g₂ : P ⇒f Q) →
    (reindex-f f g₁ ∘f reindex-f f g₂) ≃f reindex-f f (g₁ ∘f g₂)
  reindex-f-comp g₁ g₂ .transf-eq = isEquiv .refl

  reindex-f-id : ∀ {X Y} (P : Fam os es 𝒞 X) (f : Y ⇒s X) →
    reindex-f f (idf P) ≃f idf (P [ f ])
  reindex-f-id P f .transf-eq = isEquiv .refl

  reindex-sq :
    ∀ {X Y} {P Q : Fam os es 𝒞 X} {f₁ f₂ : Y ⇒s X} (g : P ⇒f Q) (e : f₁ ≈s f₂) →
    (reindex-f f₂ g ∘f reindex-≈ {P = P} f₁ f₂ e) ≃f (reindex-≈ {P = Q} f₁ f₂ e ∘f reindex-f f₁ g)
  reindex-sq {Y = Y} g e .transf-eq = g .natural (e .func-eq (Y .Setoid.refl))

  reindex-≈-refl : ∀ {X Y} {P : Fam os es 𝒞 X} (f : Y ⇒s X) →
    reindex-≈ {P = P} f f (≈s-isEquivalence .refl {f}) ≃f idf (P [ f ])
  reindex-≈-refl {P = P} f .transf-eq = P .refl*

  reindex-≈-trans : ∀ {X Y} {P : Fam os es 𝒞 X} {f g h : Y ⇒s X} →
    (e₁ : f ≈s g) (e₂ : g ≈s h) →
    reindex-≈ {P = P} f h (≈s-isEquivalence .trans e₁ e₂) ≃f (reindex-≈ {P = P} g h e₂ ∘f reindex-≈ {P = P} f g e₁)
  reindex-≈-trans {P = P} e₁ e₂ .transf-eq = P .trans* _ _

  reindex-≈-comp-1 : ∀ {X Y Z} (P : Fam os es 𝒞 Z)
    (f₁ f₂ : Y ⇒s Z) (g : X ⇒s Y) (e : f₁ ≈s f₂) →
    reindex-≈ {P = P} (f₁ ∘S g) (f₂ ∘S g) (prop-setoid.∘S-cong e (≈s-isEquivalence .refl))
      ≃f reindex-f g (reindex-≈ {P = P} f₁ f₂ e)
  reindex-≈-comp-1 P f₁ f₂ g e .transf-eq = isEquiv .refl

  reindex-≈-comp-2 : ∀ {X Y Z} (P : Fam os es 𝒞 Z)
    (f : Y ⇒s Z) (g₁ g₂ : X ⇒s Y) (e : g₁ ≈s g₂) →
    reindex-≈ {P = P} (f ∘S g₁) (f ∘S g₂) (prop-setoid.∘S-cong (≈s-isEquivalence .refl {f}) e)
      ≃f reindex-≈ {P = P [ f ]} g₁ g₂ e
  reindex-≈-comp-2 P f g₁ g₂ e .transf-eq = isEquiv .refl

{-
-- We can now say what it means for a category to have setoid-indexed
-- products. This definition works in any indexed category with
-- products.
record HasSetoidProducts {o m e} os es (𝒞 : Category o m e) : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
  field
    Π : (X Y : Setoid _ _) → Fam os es 𝒞 (⊗-setoid X Y) → Fam os es 𝒞 X
    lambdaΠ : ∀ {X Y} {P : Fam os es 𝒞 X} (Q : Fam os es 𝒞 (⊗-setoid X Y)) →
                (P [ prop-setoid.project₁ {X = X} {Y = Y} ]) ⇒f Q →
                P ⇒f (Π X Y Q)
    evalΠ : ∀ {X Y} Q → (Π X Y Q [ prop-setoid.project₁ {X = X} {Y = Y} ]) ⇒f Q
-}

--
record HasSetoidProducts {o m e} os es (𝒞 : Category o m e) : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
  open Category 𝒞
  field
    Π : (A : Setoid _ _) → Fam os es 𝒞 A → obj
    lambdaΠ : ∀ {A} (x : obj) (P : Fam os es 𝒞 A) → (constantFam os es 𝒞 A x ⇒f P) → (x ⇒ Π A P)
    lambdaΠ-cong : ∀ {A x P} {f₁ f₂ : constantFam os es 𝒞 A x ⇒f P} → f₁ ≃f f₂ → lambdaΠ x P f₁ ≈ lambdaΠ x P f₂
    evalΠ : ∀ {A} P (a : A .Setoid.Carrier) → Π A P ⇒ P .Fam.fm a
    evalΠ-cong : ∀ {A} {P : Fam os es 𝒞 A} {a₁ a₂ : A .Setoid.Carrier} →
      (e : A .Setoid._≈_ a₁ a₂) → (P .Fam.subst e ∘ evalΠ P a₁) ≈ evalΠ P a₂

  open IsEquivalence

  evalΠf : ∀ {A} P → constantFam os es 𝒞 A (Π A P) ⇒f P
  evalΠf P = record { transf = evalΠ P
                    ; natural = λ x₁≈x₂ →
                       isEquiv .trans id-right (isEquiv .sym (evalΠ-cong x₁≈x₂)) }

  field
    lambda-eval : ∀ {A} {P : Fam os es 𝒞 A} {x} {f} a →
      (evalΠ P a ∘ lambdaΠ x P f) ≈ f ._⇒f_.transf a
    lambda-ext : ∀ {A} {P : Fam os es 𝒞 A} {x} {f} → lambdaΠ x P (evalΠf P ∘f constF f) ≈ f
