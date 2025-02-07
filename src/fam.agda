{-# OPTIONS --prop --postfix-projections --safe #-}

module fam where

open import Level
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; ∘S-cong; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories

-- Families of objects over a setoid
--
-- FIXME: restate this as "Functor (setoid→category A) 𝒞"
--
-- FIXME: restate this as a displayed category
module _ {o m e os es} (A : Setoid os es) (𝒞 : Category o m e) where

  open Setoid A
  open Category 𝒞 renaming (_≈_ to _≈C_)

  -- A family of elements indexed over a setoid (really a functor from
  -- the setoid-as-category)
  record Fam : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
    no-eta-equality
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

module _ {o m e} {os es} {𝒞 : Category o m e} {A : Setoid os es} where
  open Setoid A using (_≈_)
  open Category 𝒞 renaming (_≈_ to _≈C_)
  open IsEquivalence
  open Fam

  record _⇒f_ (P Q : Fam A 𝒞) : Set (m ⊔ e ⊔ os ⊔ es) where
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
    ≈⟨ ≈-sym id-right ⟩
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
         ≈⟨ ≈-sym (assoc _ _ _) ⟩
      (f .transf x₂ ∘ Q .subst _) ∘ g .transf x₁
         ≈⟨ ∘-cong (f .natural _) (isEquiv .refl) ⟩
      (R .subst _ ∘ f .transf x₁) ∘ g .transf x₁
         ≈⟨ assoc _ _ _ ⟩
      R .subst _ ∘ (f .transf x₁ ∘ g .transf x₁)
     ∎
    where open ≈-Reasoning isEquiv

  record _≃f_ {P Q : Fam A 𝒞} (f g : P ⇒f Q) : Prop (m ⊔ e ⊔ os ⊔ es) where
    no-eta-equality
    field
      transf-eq : ∀ {x} → f .transf x ≈C g .transf x

  open _≃f_

  ≃f-isEquivalence : ∀ {P Q} → IsEquivalence (_≃f_ {P} {Q})
  ≃f-isEquivalence .refl .transf-eq = isEquiv .refl
  ≃f-isEquivalence .sym {f} {g} f≈g .transf-eq = ≈-sym (f≈g .transf-eq)
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

  constF : ∀ {x y} → x ⇒ y → constantFam A 𝒞 x ⇒f constantFam A 𝒞 y
  constF f .transf _ = f
  constF f .natural _ = isEquiv .trans id-right (≈-sym id-left)

  constF-id : ∀ {x} → constF (id x) ≃f idf _
  constF-id .transf-eq = ≈-refl

  constF-comp : ∀ {x y z} (f : y ⇒ z) (g : x ⇒ y) →
                constF (f ∘ g) ≃f (constF f ∘f constF g)
  constF-comp f g .transf-eq = ≈-refl

-- FIXME: families over a fixed setoid form a category

------------------------------------------------------------------------------
-- Change of indexed category (post composition)
open import functor hiding (id; _∘_; constF)

module _ {o m e o' m' e' os es}
         {𝒞 : Category o m e}
         {𝒟 : Category o' m' e'}
         {A : Setoid os es}
         (F : Functor 𝒞 𝒟) where

  open Fam
  open Functor
  open Category
  open IsEquivalence
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟

  changeCat : Fam A 𝒞 → Fam A 𝒟
  changeCat P .fm a = F .fobj (P .fm a)
  changeCat P .subst a₁≈a₂ = F .fmor (P .subst a₁≈a₂)
  changeCat P .refl* =
    𝒟 .isEquiv .trans (F .fmor-cong (P .refl*)) (F .fmor-id)
  changeCat P .trans* e₁ e₂ =
    𝒟 .isEquiv .trans (F .fmor-cong (P .trans* e₁ e₂)) (F .fmor-comp _ _)

  open _⇒f_
  open _≃f_

  changeCatF : ∀ {P Q : Fam A 𝒞} → P ⇒f Q → changeCat P ⇒f changeCat Q
  changeCatF f .transf x = F .fmor (f .transf x)
  changeCatF {P} {Q} f .natural {x₁} {x₂} x₁≈x₂ =
    begin
      F .fmor (f .transf x₂) 𝒟.∘ F .fmor (P .subst _)
    ≈⟨ 𝒟.≈-sym (F .fmor-comp _ _) ⟩
      F .fmor (f .transf x₂ 𝒞.∘ P .subst _)
    ≈⟨ F .fmor-cong (f .natural _) ⟩
      F .fmor (Q .subst x₁≈x₂ 𝒞.∘ f .transf x₁)
    ≈⟨ F .fmor-comp _ _ ⟩
      F .fmor (Q .subst x₁≈x₂) 𝒟.∘ F .fmor (f .transf x₁)
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  changeCatF-cong : ∀ {P Q : Fam A 𝒞} {f₁ f₂ : P ⇒f Q} → f₁ ≃f f₂ → changeCatF f₁ ≃f changeCatF f₂
  changeCatF-cong f₁≈f₂ .transf-eq = F .fmor-cong (f₁≈f₂ .transf-eq)

  preserveConst : ∀ x → changeCat (constantFam A 𝒞 x) ⇒f constantFam A 𝒟 (F .fobj x)
  preserveConst x .transf a = 𝒟.id _
  preserveConst x .natural a₁≈a₂ =
    begin
      𝒟.id _ 𝒟.∘ F .fmor (𝒞.id _)
    ≈⟨ 𝒟.∘-cong (𝒟.isEquiv .refl) (F .fmor-id) ⟩
      𝒟.id _ 𝒟.∘ 𝒟.id _
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  preserveConst⁻¹ : ∀ x → constantFam A 𝒟 (F .fobj x) ⇒f changeCat (constantFam A 𝒞 x)
  preserveConst⁻¹ x .transf a = 𝒟.id _
  preserveConst⁻¹ x .natural a₁≈a₂ = 𝒟.∘-cong (𝒟.≈-sym (F .fmor-id)) (𝒟.isEquiv .refl)

  -- FIXME: preserves id and composition, and preserveConst is a natural isomorphism

module _ {o m e o' m' e'} os es
         {𝒞 : Category o m e}
         {𝒟 : Category o' m' e'}
         (A : Setoid os es)
         {F G : Functor 𝒞 𝒟}
         (α : NatTrans F G)
  where

------------------------------------------------------------------------------
-- reindexing of families (so that Fam is an indexed category)
-- FIXME: Codify what an indexed category is
module _ {o m e os es} {𝒞 : Category o m e} where

  open _⇒s_
  open Fam

  -- NOTE: This requires that all proofs of setoid equalities are
  -- equal for the iobj-id and iobj-trans to typecheck. This is why I
  -- am using Prop.
  _[_] : ∀ {X Y : Setoid os es} → Fam X 𝒞 → (Y ⇒s X) → Fam Y 𝒞
  _[_] P f .fm w    = P .fm (f .func w)
  _[_] P f .subst e = P .subst (f .func-resp-≈ e)
  _[_] P f .refl*   = P .refl*
  _[_] P f .trans* e₁ e₂ = P .trans* (f .func-resp-≈ e₁) (f .func-resp-≈ e₂)

  open _⇒f_
  open _≈s_
  open Category 𝒞
  open IsEquivalence

  reindex-id : ∀ {X} {P : Fam X 𝒞} → P ⇒f (P [ idS _ ])
  reindex-id .transf x = id _
  reindex-id .natural x₁≈x₂ = id-swap

  reindex-comp : ∀ {X Y Z} {f : Y ⇒s Z} {g : X ⇒s Y} {P : Fam Z 𝒞} →
                 ((P [ f ]) [ g ]) ⇒f (P [ f ∘S g ])
  reindex-comp .transf x = id _
  reindex-comp .natural _ = id-swap

  reindex-f : ∀ {X Y} {P Q : Fam X 𝒞} (f : Y ⇒s X) → P ⇒f Q → (P [ f ]) ⇒f (Q [ f ])
  reindex-f f g .transf y = g .transf _
  reindex-f f g .natural x₁≈x₂ = g .natural (f .func-resp-≈ x₁≈x₂)

  reindex-≈ : ∀ {X Y} {P : Fam X 𝒞} (f g : Y ⇒s X) → f ≈s g → (P [ f ]) ⇒f (P [ g ])
  reindex-≈ {Y = Y} {P = P} f g f≈g .transf x = P .subst (f≈g .func-eq (Y .Setoid.refl))
  reindex-≈ {Y = Y} {P = P} f g f≈g .natural y₁≈y₂ =
    isEquiv .trans (≈-sym (P .trans* _ _)) (P .trans* _ _)

  open _≃f_

  reindex-f-cong : ∀ {X Y} {P Q : Fam X 𝒞} {f : Y ⇒s X} {g₁ g₂ : P ⇒f Q} → g₁ ≃f g₂ → reindex-f f g₁ ≃f reindex-f f g₂
  reindex-f-cong g₁≃g₂ .transf-eq = g₁≃g₂ .transf-eq

  reindex-f-comp : ∀ {X Y} {P Q R : Fam X 𝒞} {f : Y ⇒s X} (g₁ : Q ⇒f R) (g₂ : P ⇒f Q) →
    (reindex-f f g₁ ∘f reindex-f f g₂) ≃f reindex-f f (g₁ ∘f g₂)
  reindex-f-comp g₁ g₂ .transf-eq = isEquiv .refl

  reindex-f-id : ∀ {X Y} (P : Fam X 𝒞) (f : Y ⇒s X) →
    reindex-f f (idf P) ≃f idf (P [ f ])
  reindex-f-id P f .transf-eq = isEquiv .refl

  reindex-sq :
    ∀ {X Y} {P Q : Fam X 𝒞} {f₁ f₂ : Y ⇒s X} (g : P ⇒f Q) (e : f₁ ≈s f₂) →
    (reindex-f f₂ g ∘f reindex-≈ {P = P} f₁ f₂ e) ≃f (reindex-≈ {P = Q} f₁ f₂ e ∘f reindex-f f₁ g)
  reindex-sq {Y = Y} g e .transf-eq = g .natural (e .func-eq (Y .Setoid.refl))

  reindex-≈-refl : ∀ {X Y} {P : Fam X 𝒞} (f : Y ⇒s X) →
    reindex-≈ {P = P} f f (≈s-isEquivalence .refl {f}) ≃f idf (P [ f ])
  reindex-≈-refl {P = P} f .transf-eq = P .refl*

  reindex-≈-trans : ∀ {X Y} {P : Fam X 𝒞} {f g h : Y ⇒s X} →
    (e₁ : f ≈s g) (e₂ : g ≈s h) →
    reindex-≈ {P = P} f h (≈s-isEquivalence .trans e₁ e₂) ≃f (reindex-≈ {P = P} g h e₂ ∘f reindex-≈ {P = P} f g e₁)
  reindex-≈-trans {P = P} e₁ e₂ .transf-eq = P .trans* _ _

  reindex-comp-≈ : ∀ {X Y Z} (P : Fam Z 𝒞)
    {f₁ f₂ : Y ⇒s Z} {g₁ g₂ : X ⇒s Y}
    (f₁≈f₂ : f₁ ≈s f₂) (g₁≈g₂ : g₁ ≈s g₂) →
       (reindex-≈ (f₁ ∘S g₁) (f₂ ∘S g₂) (∘S-cong f₁≈f₂ g₁≈g₂) ∘f reindex-comp {P = P})
    ≃f (reindex-comp ∘f (reindex-≈ g₁ g₂ g₁≈g₂ ∘f reindex-f g₁ (reindex-≈ f₁ f₂ f₁≈f₂)))
    -- FIXME: better as horizontal composition? then we are using the
    -- interchange law.
  reindex-comp-≈ P f₁≈f₂ g₁≈g₂ .transf-eq {x} =
    begin
      P .subst _ ∘ id _               ≈⟨ id-right ⟩
      P .subst _                      ≈⟨ P .trans* _ _ ⟩
      P .subst _ ∘ P .subst _         ≈˘⟨ id-left ⟩
      id _ ∘ (P .subst _ ∘ P .subst _) ∎
    where open ≈-Reasoning isEquiv

-- FIXME: this is a special case of limits, defined in functor.agda
record HasSetoidProducts {o m e} os es (𝒞 : Category o m e) : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
  open Category 𝒞
  field
    Π : (A : Setoid os es) → Fam A 𝒞 → obj
    lambdaΠ : ∀ {A} (x : obj) (P : Fam A 𝒞) → (constantFam A 𝒞 x ⇒f P) → (x ⇒ Π A P)
    lambdaΠ-cong : ∀ {A x P} {f₁ f₂ : constantFam A 𝒞 x ⇒f P} → f₁ ≃f f₂ → lambdaΠ x P f₁ ≈ lambdaΠ x P f₂
    evalΠ : ∀ {A} P (a : A .Setoid.Carrier) → Π A P ⇒ P .Fam.fm a
    evalΠ-cong : ∀ {A} {P : Fam A 𝒞} {a₁ a₂ : A .Setoid.Carrier} →
      (e : A .Setoid._≈_ a₁ a₂) → (P .Fam.subst e ∘ evalΠ P a₁) ≈ evalΠ P a₂

  open IsEquivalence

  evalΠf : ∀ {A} P → constantFam _ _ (Π A P) ⇒f P
  evalΠf P = record { transf = evalΠ P
                    ; natural = λ x₁≈x₂ →
                       isEquiv .trans id-right (≈-sym (evalΠ-cong x₁≈x₂)) }

  field
    lambda-eval : ∀ {A} {P : Fam A 𝒞} {x} {f} a →
      (evalΠ P a ∘ lambdaΠ x P f) ≈ f ._⇒f_.transf a
    lambda-ext : ∀ {A} {P : Fam A 𝒞} {x} {f} → lambdaΠ x P (evalΠf P ∘f constF f) ≈ f

  lambda-evalf : ∀ {A} {P : Fam A 𝒞} {x} f → (evalΠf P ∘f constF (lambdaΠ x P f)) ≃f f
  lambda-evalf f ._≃f_.transf-eq {a} = lambda-eval a

  Π-map : ∀ {A} {P Q : Fam A 𝒞} → P ⇒f Q → Π A P ⇒ Π A Q
  Π-map {A} {P} {Q} f = lambdaΠ (Π A P) Q (f ∘f evalΠf P)

  Π-map-cong : ∀ {A} {P Q : Fam A 𝒞}
               {f₁ f₂ : P ⇒f Q} → f₁ ≃f f₂ → Π-map f₁ ≈ Π-map f₂
  Π-map-cong f₁≃f₂ = lambdaΠ-cong (∘f-cong f₁≃f₂ (≃f-isEquivalence .refl))

  Π-map-id : ∀ {A} {P : Fam A 𝒞} → Π-map (idf _) ≈ id (Π A P)
  Π-map-id {A} {P} =
    begin
      lambdaΠ (Π A P) P (idf _ ∘f evalΠf P)
    ≈⟨ lambdaΠ-cong ≃f-id-left ⟩
      lambdaΠ (Π A P) P (evalΠf P)
    ≈⟨ ≈-sym (lambdaΠ-cong ≃f-id-right) ⟩
      lambdaΠ (Π A P) P (evalΠf P ∘f idf _)
    ≈⟨ ≈-sym (lambdaΠ-cong (∘f-cong (≃f-isEquivalence .refl) constF-id)) ⟩
      lambdaΠ (Π A P) P (evalΠf P ∘f constF (id (Π A P)))
    ≈⟨ lambda-ext ⟩
      id (Π A P)
    ∎
    where open ≈-Reasoning isEquiv

  lambdaΠ-natural : ∀ {A} {P : Fam A 𝒞} {x y} →
                    (f : constantFam A 𝒞 y ⇒f P) →
                    (h : x ⇒ y) →
                    (lambdaΠ y P f ∘ h) ≈ lambdaΠ x P (f ∘f constF h)
  lambdaΠ-natural {A} {P} {x} {y} f h =
    begin
      lambdaΠ y P f ∘ h
    ≈⟨ ≈-sym lambda-ext ⟩
      lambdaΠ x P (evalΠf P ∘f constF (lambdaΠ y P f ∘ h))
    ≈⟨ lambdaΠ-cong (∘f-cong (≃f-isEquivalence .refl) (constF-comp _ _)) ⟩
      lambdaΠ x P (evalΠf P ∘f (constF (lambdaΠ y P f) ∘f constF h))
    ≈⟨ ≈-sym (lambdaΠ-cong (≃f-assoc _ _ _)) ⟩
      lambdaΠ x P ((evalΠf P ∘f constF (lambdaΠ y P f)) ∘f constF h)
    ≈⟨ lambdaΠ-cong (∘f-cong (lambda-evalf _) (≃f-isEquivalence .refl)) ⟩
      lambdaΠ x P (f ∘f constF h)
    ∎
    where open ≈-Reasoning isEquiv

  Π-map-comp : ∀ {A} {P Q R : Fam A 𝒞} (f : Q ⇒f R) (g : P ⇒f Q) →
               Π-map (f ∘f g) ≈ (Π-map f ∘ Π-map g)
  Π-map-comp {A} {P} {Q} {R} f g =
    begin
      lambdaΠ (Π A P) R ((f ∘f g) ∘f evalΠf P)
    ≈⟨ lambdaΠ-cong (≃f-assoc _ _ _) ⟩
      lambdaΠ (Π A P) R (f ∘f (g ∘f evalΠf P))
    ≈⟨ ≈-sym (lambdaΠ-cong (∘f-cong (≃f-isEquivalence .refl) (lambda-evalf _))) ⟩
      lambdaΠ (Π A P) R (f ∘f (evalΠf Q ∘f constF (lambdaΠ (Π A P) Q (g ∘f evalΠf P))))
    ≈⟨ ≈-sym (lambdaΠ-cong (≃f-assoc _ _ _)) ⟩
      lambdaΠ (Π A P) R ((f ∘f evalΠf Q) ∘f constF (lambdaΠ (Π A P) Q (g ∘f evalΠf P)))
    ≈⟨ ≈-sym (lambdaΠ-natural _ _) ⟩
      lambdaΠ (Π A Q) R (f ∘f evalΠf Q) ∘ lambdaΠ (Π A P) Q (g ∘f evalΠf P)
    ∎
    where open ≈-Reasoning isEquiv

  lambda-compose : ∀ {A} {Q R : Fam A 𝒞} {x}
    (f : Q ⇒f R) (g : constantFam A 𝒞 x ⇒f Q) →
    lambdaΠ _ _ (f ∘f g) ≈ (Π-map f ∘ lambdaΠ _ _ g)
  lambda-compose {A} {Q} {R} {x} f g =
    begin
      lambdaΠ x R (f ∘f g)
    ≈˘⟨ lambdaΠ-cong (∘f-cong (≃f-isEquivalence .refl) (lambda-evalf _)) ⟩
      lambdaΠ _ _ (f ∘f (evalΠf _ ∘f constF (lambdaΠ _ _ g)))
    ≈˘⟨ lambdaΠ-cong (≃f-assoc _ _ _) ⟩
      lambdaΠ _ _ ((f ∘f evalΠf _) ∘f constF (lambdaΠ _ _ g))
    ≈˘⟨ lambdaΠ-natural _ _ ⟩
      lambdaΠ _ _ (f ∘f evalΠf _) ∘ lambdaΠ _ _ g
    ∎
    where open ≈-Reasoning isEquiv
