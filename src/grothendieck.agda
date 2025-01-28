{-# OPTIONS --prop --postfix-projections #-}

module grothendieck where

open import Level
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; ⊗-setoid; idS; _∘S_; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import categories
open import setoid-cat
open import fam

-- Categories of Families, a special case of the Grothendieck
-- construction
module CategoryOfFamilies {o m e} {os es} (𝒞 : Category o m e) where

  open Fam

  record Obj : Set (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
    field
      idx : Setoid (m ⊔ e ⊔ os ⊔ es) (m ⊔ e ⊔ os ⊔ es)
      fam : Fam os es 𝒞 idx
  open Obj

  record Mor (X Y : Obj) : Set (os ⊔ es ⊔ m ⊔ e) where
    field
      idxf : X .idx ⇒s Y .idx
      famf : X .fam ⇒f (Y .fam [ idxf ])
  open Mor

  record _≃_ {X Y : Obj} (f g : Mor X Y) : Prop (os ⊔ es ⊔ m ⊔ e) where
    field
      idxf-eq : f .idxf ≈s g .idxf
      famf-eq : (reindex-≈ {P = Y .fam} (f .idxf) (g .idxf) idxf-eq ∘f f .famf) ≃f g .famf
  open _≃_

  module _ where
    open IsEquivalence

    ≃-isEquivalence : ∀ {X Y} → IsEquivalence (_≃_ {X} {Y})
    ≃-isEquivalence .refl .idxf-eq = ≈s-isEquivalence .refl
    ≃-isEquivalence {X} {Y} .refl {f} .famf-eq =
      begin
        reindex-≈ {P = Y .fam} (f .idxf) (f .idxf) (≈s-isEquivalence .refl) ∘f f .famf
      ≈⟨ ∘f-cong (reindex-≈-refl {P = Y .fam} (f .idxf)) (≃f-isEquivalence .refl {f .famf}) ⟩
        idf (Y .fam [ f .idxf ]) ∘f f .famf
      ≈⟨ ≃f-id-left ⟩
        f .famf
      ∎ where open ≈-Reasoning ≃f-isEquivalence
    ≃-isEquivalence .sym f≈g .idxf-eq = ≈s-isEquivalence .sym (f≈g .idxf-eq)
    ≃-isEquivalence {X} {Y} .sym {f}{g} f≈g .famf-eq =
      begin
        reindex-≈ {P = Y .fam} (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f g .famf
      ≈⟨ ∘f-cong (≃f-isEquivalence .refl {reindex-≈ {P = Y .fam} (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq))}) (≃f-isEquivalence .sym (f≈g .famf-eq)) ⟩
        reindex-≈ {P = Y .fam} (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f (reindex-≈ {P = Y .fam} (f .idxf) (g .idxf) (f≈g .idxf-eq) ∘f f .famf)
      ≈⟨ ≃f-isEquivalence .sym (≃f-assoc _ _ _) ⟩
        (reindex-≈ {P = Y .fam} (g .idxf) (f .idxf) (≈s-isEquivalence .sym (f≈g .idxf-eq)) ∘f reindex-≈ {P = Y .fam} (f .idxf) (g .idxf) (f≈g .idxf-eq)) ∘f f .famf
      ≈⟨ ∘f-cong (≃f-isEquivalence .sym (reindex-≈-trans _ _)) (≃f-isEquivalence .refl) ⟩
        reindex-≈ {P = Y .fam} (f .idxf) _ (≈s-isEquivalence .refl {f .idxf}) ∘f f .famf
      ≈⟨ ∘f-cong (reindex-≈-refl {P = Y .fam} (f .idxf)) (≃f-isEquivalence .refl {f .famf}) ⟩
        idf (Y .fam [ f .idxf ]) ∘f f .famf
      ≈⟨ ≃f-id-left ⟩
        f .famf
      ∎ where open ≈-Reasoning ≃f-isEquivalence
    ≃-isEquivalence .trans f≈g g≈h .idxf-eq = ≈s-isEquivalence .trans (f≈g .idxf-eq) (g≈h .idxf-eq)
    ≃-isEquivalence {X} {Y} .trans {f}{g}{h} f≈g g≈h .famf-eq =
      begin
        reindex-≈ {P = Y .fam} (f .idxf) (h .idxf) _ ∘f f .famf
      ≈⟨ ∘f-cong (reindex-≈-trans (f≈g .idxf-eq) (g≈h .idxf-eq)) (≃f-isEquivalence .refl) ⟩
        (reindex-≈ {P = Y .fam} _ _ (g≈h .idxf-eq) ∘f reindex-≈ {P = Y .fam} (f .idxf) (g .idxf) (f≈g .idxf-eq)) ∘f f .famf
      ≈⟨ ≃f-assoc _ _ _ ⟩
        reindex-≈ {P = Y .fam} _ _ (g≈h .idxf-eq) ∘f (reindex-≈ {P = Y .fam} _ _ (f≈g .idxf-eq) ∘f f .famf)
      ≈⟨ ∘f-cong (≃f-isEquivalence .refl) (f≈g .famf-eq) ⟩
        reindex-≈ {P = Y .fam} _ _ (g≈h .idxf-eq) ∘f g .famf
      ≈⟨ g≈h .famf-eq ⟩
        h .famf
      ∎ where open ≈-Reasoning ≃f-isEquivalence

  module _ where

    open Category 𝒞
    open IsEquivalence

    Mor-id : ∀ X → Mor X X
    Mor-id X .idxf = idS _
    Mor-id X .famf = idf _
     -- FIXME: to generalise to all indexed categories, this ought to
     -- be an explicit witness of X -> X[id]. Likewise for
     -- composition. The definition of reindexing currently satisfies
     -- reindexing by identity and composition laws definitionally.

    Mor-∘ : ∀ {X Y Z} → Mor Y Z → Mor X Y → Mor X Z
    Mor-∘ f g .idxf = f .idxf ∘S g .idxf
    Mor-∘ f g .famf = reindex-f (g .idxf) (f .famf) ∘f (g .famf)

    open _≃_

    Mor-∘-cong : ∀ {X Y Z}{f₁ f₂ : Mor Y Z}{g₁ g₂ : Mor X Y} → f₁ ≃ f₂ → g₁ ≃ g₂ → Mor-∘ f₁ g₁ ≃ Mor-∘ f₂ g₂
    Mor-∘-cong f₁≃f₂ g₁≃g₂ .idxf-eq = prop-setoid.∘S-cong (f₁≃f₂ .idxf-eq) (g₁≃g₂ .idxf-eq)
    Mor-∘-cong {X}{Y}{Z} {f₁}{f₂}{g₁}{g₂} f₁≃f₂ g₁≃g₂ .famf-eq =
      begin
        reindex-≈ {P = Z .fam} (f₁ .idxf ∘S g₁ .idxf) (f₂ .idxf ∘S g₂ .idxf) eq₁ ∘f (reindex-f (g₁ .idxf) (f₁ .famf) ∘f g₁ .famf)
      ≈⟨ ≃f-isEquivalence .sym (≃f-assoc _ _ _) ⟩
        (reindex-≈ {P = Z .fam} _ _ eq₁ ∘f reindex-f (g₁ .idxf) (f₁ .famf)) ∘f g₁ .famf
      ≈⟨ ∘f-cong (∘f-cong (reindex-≈-trans eq₂ eq₃) (≃f-isEquivalence .refl)) (≃f-isEquivalence .refl) ⟩
        ((reindex-≈ {P = Z .fam} _ _ eq₃ ∘f reindex-≈ {P = Z .fam} _ _ eq₂) ∘f reindex-f (g₁ .idxf) (f₁ .famf)) ∘f g₁ .famf
      ≈⟨ ∘f-cong
          (∘f-cong (∘f-cong (reindex-≈-comp-1 (Z .fam) _ _ (g₂ .idxf) (f₁≃f₂ .idxf-eq))
                           (reindex-≈-comp-2 (Z .fam) (f₁ .idxf) _ _ (g₁≃g₂ .idxf-eq)))
                   (≃f-isEquivalence .refl))
          (≃f-isEquivalence .refl) ⟩
        ((reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) ∘f reindex-≈ {P = Z .fam [ f₁ .idxf ]} _ _ (g₁≃g₂ .idxf-eq)) ∘f reindex-f (g₁ .idxf) (f₁ .famf)) ∘f g₁ .famf
      ≈⟨ ∘f-cong (≃f-assoc _ _ _) (≃f-isEquivalence .refl) ⟩
        (reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) ∘f (reindex-≈ {P = Z .fam [ f₁ .idxf ]} _ _ (g₁≃g₂ .idxf-eq) ∘f reindex-f (g₁ .idxf) (f₁ .famf))) ∘f g₁ .famf
      ≈⟨ ∘f-cong (∘f-cong (≃f-isEquivalence .refl) square) (≃f-isEquivalence .refl) ⟩
        (reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) ∘f (reindex-f (g₂ .idxf) (f₁ .famf) ∘f reindex-≈ {P = Y .fam} _ _ (g₁≃g₂ .idxf-eq))) ∘f g₁ .famf
      ≈⟨ ∘f-cong (≃f-isEquivalence .sym (≃f-assoc _ _ _)) (≃f-isEquivalence .refl) ⟩
        ((reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) ∘f reindex-f (g₂ .idxf) (f₁ .famf)) ∘f reindex-≈ {P = Y .fam} _ _ (g₁≃g₂ .idxf-eq)) ∘f g₁ .famf
      ≈⟨ ≃f-assoc _ _ _ ⟩
        (reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) ∘f reindex-f (g₂ .idxf) (f₁ .famf)) ∘f (reindex-≈ {P = Y .fam} _ _ (g₁≃g₂ .idxf-eq) ∘f g₁ .famf)
      ≈⟨ ∘f-cong (reindex-f-comp (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq)) (f₁ .famf)) (≃f-isEquivalence .refl) ⟩
        reindex-f (g₂ .idxf) (reindex-≈ {P = Z .fam} _ _ (f₁≃f₂ .idxf-eq) ∘f f₁ .famf) ∘f (reindex-≈ {P = Y .fam} _ _ (g₁≃g₂ .idxf-eq) ∘f g₁ .famf)
      ≈⟨ ∘f-cong (reindex-f-cong (f₁≃f₂ .famf-eq)) (g₁≃g₂ .famf-eq) ⟩
        reindex-f (g₂ .idxf) (f₂ .famf) ∘f g₂ .famf
      ∎
      where open ≈-Reasoning ≃f-isEquivalence
            eq₁ = prop-setoid.∘S-cong (f₁≃f₂ .idxf-eq) (g₁≃g₂ .idxf-eq)
            eq₂ = prop-setoid.∘S-cong (≈s-isEquivalence .refl {f₁ .idxf}) (g₁≃g₂ .idxf-eq)
            eq₃ = prop-setoid.∘S-cong (f₁≃f₂ .idxf-eq) (≈s-isEquivalence .refl {g₂ .idxf})

            square : (reindex-≈ {P = Z .fam [ f₁ .idxf ]} _ _ (g₁≃g₂ .idxf-eq) ∘f reindex-f (g₁ .idxf) (f₁ .famf))
                     ≃f (reindex-f (g₂ .idxf) (f₁ .famf) ∘f reindex-≈ {P = Y .fam} _ _ (g₁≃g₂ .idxf-eq))
            square = ≃f-isEquivalence .sym (reindex-sq (f₁ .famf) (g₁≃g₂ .idxf-eq))

  module _ where
    open Category
    open IsEquivalence
    private module 𝒞 = Category 𝒞

    cat : Category (o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) (os ⊔ es ⊔ m ⊔ e) (e ⊔ m ⊔ os ⊔ es)
    cat .obj = Obj
    cat ._⇒_ = Mor
    cat ._≈_ = _≃_
    cat .isEquiv = ≃-isEquivalence
    cat .id = Mor-id
    cat ._∘_ = Mor-∘
    cat .∘-cong = Mor-∘-cong
    cat .id-left .idxf-eq = prop-setoid.id-left
    cat .id-left {X} {Y} {f} .famf-eq ._≃f_.transf-eq {x} =
      begin
        Y .fam .subst _ 𝒞.∘ (𝒞.id _ 𝒞.∘ f .famf ._⇒f_.transf x)
      ≈⟨ 𝒞.∘-cong (Y .fam .refl*) 𝒞.id-left ⟩
        𝒞.id _ 𝒞.∘ f .famf ._⇒f_.transf x
      ≈⟨ 𝒞.id-left ⟩
        f .famf ._⇒f_.transf x
      ∎ where open ≈-Reasoning 𝒞.isEquiv
    cat .id-right .idxf-eq = prop-setoid.id-right
    cat .id-right {X}{Y}{f} .famf-eq ._≃f_.transf-eq {x} =
      begin
        Y .fam .subst _ 𝒞.∘ (f .famf ._⇒f_.transf x 𝒞.∘ 𝒞.id _)
      ≈⟨ 𝒞.∘-cong (Y .fam .refl*) 𝒞.id-right ⟩
        𝒞.id _ 𝒞.∘ f .famf ._⇒f_.transf x
      ≈⟨ 𝒞.id-left ⟩
        f .famf ._⇒f_.transf x
      ∎ where open ≈-Reasoning 𝒞.isEquiv
    cat .assoc f g h .idxf-eq = prop-setoid.assoc (f .idxf) (g .idxf) (h .idxf)
    cat .assoc {W}{X}{Y}{Z} f g h .famf-eq ._≃f_.transf-eq {x} =
      begin
        Z .fam .subst _ 𝒞.∘ ((f .famf .transf (g .idxf .func (h .idxf .func x)) 𝒞.∘ g .famf .transf (h .idxf .func x)) 𝒞.∘ h .famf .transf x)
      ≈⟨ 𝒞.∘-cong (Z .fam .refl*) (𝒞.assoc _ _ _) ⟩
        𝒞.id _ 𝒞.∘ (f .famf .transf (g .idxf .func (h .idxf .func x)) 𝒞.∘ (g .famf .transf (h .idxf .func x) 𝒞.∘ h .famf .transf x))
      ≈⟨ 𝒞.id-left ⟩
        f .famf .transf (g .idxf .func (h .idxf .func x)) 𝒞.∘ (g .famf .transf (h .idxf .func x) 𝒞.∘ h .famf .transf x)
      ∎ where open ≈-Reasoning 𝒞.isEquiv
              open _⇒f_
              open _⇒s_

  -- If 𝒞 has a terminal object, then so does the category of families
  module _ (T : HasTerminal 𝒞) where
    open HasTerminal
    open IsEquivalence

    -- FIXME: try to do this without breaking the abstraction of
    -- Fam(X). Need to know that every fibre of the indexed category
    -- has a terminal object, and that reindexing preserves them.
    terminal : HasTerminal cat
    terminal .witness .idx = 𝟙
    terminal .witness .fam = constantFam _ _ 𝒞 𝟙 (T .witness)
    terminal .terminal-mor x .idxf = prop-setoid.to-𝟙
    terminal .terminal-mor x .famf ._⇒f_.transf _ = T .terminal-mor _
    terminal .terminal-mor x .famf ._⇒f_.natural _ = T .terminal-unique _ _ _
    terminal .terminal-unique x f g .idxf-eq = prop-setoid.to-𝟙-unique _ _
    terminal .terminal-unique x f g .famf-eq ._≃f_.transf-eq = T .terminal-unique _ _ _

  -- This category always has coproducts, because it is the free
  -- co-product completion.
  module _ where

    open Category 𝒞
    open HasCoproducts
    open IsEquivalence
    open _⇒f_

    coproducts : HasCoproducts cat
    coproducts .coprod X Y .idx = +-setoid (X .idx) (Y .idx)
    coproducts .coprod X Y .fam .fm (inj₁ x) = X .fam .fm x
    coproducts .coprod X Y .fam .fm (inj₂ y) = Y .fam .fm y
    coproducts .coprod X Y .fam .subst {inj₁ x} {inj₁ x₁} (lift e) = X .fam .subst e
    coproducts .coprod X Y .fam .subst {inj₂ y} {inj₂ y₁} (lift e) = Y .fam .subst e
    coproducts .coprod X Y .fam .refl* {inj₁ x} = X .fam .refl*
    coproducts .coprod X Y .fam .refl* {inj₂ y} = Y .fam .refl*
    coproducts .coprod X Y .fam .trans* {inj₁ x} {inj₁ x₁} {inj₁ x₂} (lift e₁) (lift e₂) = X .fam .trans* e₁ e₂
    coproducts .coprod X Y .fam .trans* {inj₂ y} {inj₂ y₁} {inj₂ y₂} (lift e₁) (lift e₂) = Y .fam .trans* e₁ e₂
    coproducts .in₁ .idxf = prop-setoid.inject₁
    coproducts .in₁ .famf .transf x = id _
    coproducts .in₁ .famf .natural e = isEquiv .trans id-left (isEquiv .sym id-right)
    coproducts .in₂ .idxf = prop-setoid.inject₂
    coproducts .in₂ .famf .transf x = id _
    coproducts .in₂ .famf .natural e = isEquiv .trans id-left (isEquiv .sym id-right)
    coproducts .copair f g .idxf = prop-setoid.copair (f .idxf) (g .idxf)
    coproducts .copair f g .famf .transf (inj₁ x) = f .famf .transf x
    coproducts .copair f g .famf .transf (inj₂ y) = g .famf .transf y
    coproducts .copair f g .famf .natural {inj₁ x} {inj₁ x₁} (lift e) = f .famf .natural e
    coproducts .copair f g .famf .natural {inj₂ y} {inj₂ y₁} (lift e) = g .famf .natural e

  -- If 𝒞 has products, then so does the category of families. FIXME:
  -- redo the core of this to just get monoidal products from monoidal
  -- products.
  module products (P : HasProducts 𝒞) where

    open Category 𝒞
    open HasProducts
    open IsEquivalence
    open _⇒f_

    _⊗_ : Obj → Obj → Obj
    (X ⊗ Y) .idx = ⊗-setoid (X .idx) (Y .idx)
    (X ⊗ Y) .fam .fm (x , y) = P .prod (X .fam .fm x) (Y .fam .fm y)
    (X ⊗ Y) .fam .subst (e₁ , e₂) =
      prod-m P (X .fam .subst e₁) (Y .fam .subst e₂)
    (X ⊗ Y) .fam .refl* =
      begin
        prod-m P (X .fam .subst _) (Y .fam .subst _)
      ≈⟨ prod-m-cong P (X .fam .refl*) (Y .fam .refl*) ⟩
        prod-m P (id _) (id _)
      ≈⟨ prod-m-id P ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    (X ⊗ Y) .fam .trans* {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} (x₂≈x₃ , y₂≈y₃) (x₁≈x₂ , y₁≈y₂) =
      begin
        prod-m P (X .fam .subst _) (Y .fam .subst _)
      ≈⟨ prod-m-cong P (X .fam .trans* _ _) (Y .fam .trans* _ _) ⟩
        prod-m P (X .fam .subst _ ∘ X .fam .subst _) (Y .fam .subst _ ∘ Y .fam .subst _)
      ≈⟨ pair-functorial P _ _ _ _ ⟩
        prod-m P (X .fam .subst _) (Y .fam .subst _) ∘ prod-m P (X .fam .subst _) (Y .fam .subst _)
      ∎ where open ≈-Reasoning isEquiv

    products : HasProducts cat
    products .prod = _⊗_
    products .p₁ .idxf = prop-setoid.project₁
    products .p₁ .famf .transf (x , y) = P .p₁
    products .p₁ {X} {Y} .famf .natural (e₁ , e₂) =
      begin
        P .p₁ ∘ P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-p₁ _ _ ⟩
        X .fam .subst _ ∘ P .p₁
      ∎ where open ≈-Reasoning isEquiv
    products .p₂ .idxf = prop-setoid.project₂
    products .p₂ .famf .transf (x , y) = P .p₂
    products .p₂ {X} {Y} .famf .natural (e₁ , e₂) =
      begin
        P .p₂ ∘ P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-p₂ _ _ ⟩
        Y .fam .subst _ ∘ P .p₂
      ∎ where open ≈-Reasoning isEquiv
    products .pair f g .idxf = prop-setoid.pair (f .idxf) (g .idxf)
    products .pair f g .famf .transf x = P .pair (f .famf .transf x) (g .famf .transf x)
    products .pair {X} {Y} {Z} f g .famf .natural {x₁} {x₂} x₁≈x₂ =
      begin
        P .pair (f .famf .transf x₂) (g .famf .transf x₂) ∘ X .fam .subst _
      ≈⟨ pair-natural P _ _ _ ⟩
        P .pair (f .famf .transf x₂ ∘ X .fam .subst _) (g .famf .transf x₂ ∘ X .fam .subst _)
      ≈⟨ P .pair-cong (f .famf .natural x₁≈x₂) (g .famf .natural x₁≈x₂) ⟩
        P .pair (Y .fam .subst _ ∘ f .famf .transf x₁) (Z .fam .subst _ ∘ g .famf .transf x₁)
      ≈⟨ isEquiv .sym (P .pair-cong (∘-cong ≈-refl (P .pair-p₁ _ _)) (∘-cong ≈-refl (P .pair-p₂ _ _))) ⟩
        P .pair (Y .fam .subst _ ∘ (P .p₁ ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁))) (Z .fam .subst _ ∘ (P .p₂ ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)))
      ≈⟨ isEquiv .sym (P .pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
        P .pair ((Y .fam .subst _ ∘ P .p₁) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)) ((Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁))
      ≈⟨ isEquiv .sym (pair-natural P _ _ _) ⟩
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f .famf .transf x₁) (g .famf .transf x₁)
      ∎ where open ≈-Reasoning isEquiv
    products .pair-cong f₁≈f₂ g₁≈g₂ .idxf-eq = prop-setoid.pair-cong (f₁≈f₂ .idxf-eq) (g₁≈g₂ .idxf-eq)
    products .pair-cong {X}{Y}{Z} {f₁}{f₂}{g₁}{g₂} f₁≈f₂ g₁≈g₂ .famf-eq ._≃f_.transf-eq {x} =
      begin
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (f₁ .famf .transf x) (g₁ .famf .transf x)
      ≈⟨ pair-compose P _ _ _ _ ⟩
        P .pair (Y .fam .subst _ ∘ f₁ .famf .transf x) (Z .fam .subst _ ∘ g₁ .famf .transf x)
      ≈⟨ P .pair-cong (f₁≈f₂ .famf-eq ._≃f_.transf-eq) (g₁≈g₂ .famf-eq ._≃f_.transf-eq) ⟩
        P .pair (f₂ .famf .transf x) (g₂ .famf .transf x)
      ∎ where open ≈-Reasoning isEquiv
    products .pair-p₁ {X} {Y} {Z} f g .idxf-eq = Setoid-products _ _ .pair-p₁ _ _
    products .pair-p₁ {X} {Y} {Z} f g .famf-eq ._≃f_.transf-eq {x} =
      begin
        Y .fam .subst _ ∘ (P .p₁ ∘ P .pair (f .famf .transf x) (g .famf .transf x))
      ≈⟨ ∘-cong (Y .fam .refl*) (P .pair-p₁ _ _) ⟩
        id _ ∘ f .famf .transf x
      ≈⟨ id-left ⟩
        f .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    products .pair-p₂ {X} {Y} {Z} f g .idxf-eq = Setoid-products _ _ .pair-p₂ _ _
    products .pair-p₂ {X} {Y} {Z} f g .famf-eq ._≃f_.transf-eq {x} =
      begin
        Z .fam .subst _ ∘ (P .p₂ ∘ P .pair (f .famf .transf x) (g .famf .transf x))
      ≈⟨ ∘-cong (Z .fam .refl*) (P .pair-p₂ _ _) ⟩
        id _ ∘ g .famf .transf x
      ≈⟨ id-left ⟩
        g .famf .transf x
      ∎ where open ≈-Reasoning isEquiv
    products .pair-ext f .idxf-eq = Setoid-products _ _ .pair-ext _
    products .pair-ext {X}{Y}{Z} f .famf-eq ._≃f_.transf-eq {x} =
      begin
        P .pair (Y .fam .subst _ ∘ P .p₁) (Z .fam .subst _ ∘ P .p₂) ∘ P .pair (P .p₁ ∘ f .famf .transf x) (P .p₂ ∘ f .famf .transf x)
      ≈⟨ pair-compose P _ _ _ _ ⟩
        P .pair (Y .fam .subst _ ∘ (P .p₁ ∘ f .famf .transf x)) (Z .fam .subst _ ∘ (P .p₂ ∘ f .famf .transf x))
      ≈⟨ P .pair-cong (∘-cong (Y .fam .refl*) ≈-refl) (∘-cong (Z .fam .refl*) ≈-refl) ⟩
        P .pair (id _ ∘ (P .p₁ ∘ f .famf .transf x)) (id _ ∘ (P .p₂ ∘ f .famf .transf x))
      ≈⟨ P .pair-cong id-left id-left ⟩
        P .pair (P .p₁ ∘ f .famf .transf x) (P .p₂ ∘ f .famf .transf x)
      ≈⟨ P .pair-ext _ ⟩
        f .famf .transf x
      ∎ where open ≈-Reasoning isEquiv

    open HasStrongCoproducts

    strongCoproducts : HasStrongCoproducts cat products
    strongCoproducts .coprod = coproducts .HasCoproducts.coprod
    strongCoproducts .in₁ = coproducts .HasCoproducts.in₁
    strongCoproducts .in₂ = coproducts .HasCoproducts.in₂
    strongCoproducts .copair f g .idxf = prop-setoid.case (f .idxf) (g .idxf)
    strongCoproducts .copair f g .famf .transf (w , inj₁ x) = f .famf .transf (w , x)
    strongCoproducts .copair f g .famf .transf (w , inj₂ y) = g .famf .transf (w , y)
    strongCoproducts .copair {W}{X}{Y}{Z} f g .famf .natural {w₁ , inj₁ x₁} {w₂ , inj₁ x₂} (w₁≈w₂ , lift e) =
      f .famf .natural (w₁≈w₂ , e)
    strongCoproducts .copair f g .famf .natural {w₁ , inj₂ y} {w₂ , inj₂ y₁} (w₁≈w₂ , lift e) =
      g .famf .natural (w₁≈w₂ , e)

  module monad (Mon : Monad 𝒞) where

    open Category 𝒞
    open IsEquivalence
    open Monad
    open _⇒f_
    open _≃f_

    monad : Monad cat
    monad .M X .idx = X .idx
    monad .M X .fam .fm x = Mon .M (X .fam .fm x)
    monad .M X .fam .subst x≈y = Mon .map (X .fam .subst x≈y)
    monad .M X .fam .refl* =
      begin
        Mon .map (X .fam .subst _)
      ≈⟨ Mon .map-cong (X .fam .refl*) ⟩
        Mon .map (id _)
      ≈⟨ Mon .map-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    monad .M X .fam .trans* y≈z x≈y =
      begin
        Mon .map (X .fam .subst _)
      ≈⟨ Mon .map-cong (X .fam .trans* _ _) ⟩
        Mon .map (X .fam .subst _ ∘ X .fam .subst _)
      ≈⟨ Mon .map-comp _ _ ⟩
        Mon .map (X .fam .subst _) ∘ Mon .map (X .fam .subst _)
      ∎ where open ≈-Reasoning isEquiv
    monad .map f .idxf = f .idxf
    monad .map f .famf .transf x = Mon .map (f .famf .transf x)
    monad .map {X} {Y} f .famf .natural x₁≈x₂ =
      begin
        Mon .map (f .famf .transf _) ∘ Mon .map (X .fam .subst _)
      ≈⟨ isEquiv .sym (Mon .map-comp _ _) ⟩
        Mon .map (f .famf .transf _ ∘ X .fam .subst _)
      ≈⟨ Mon .map-cong (f .famf .natural _) ⟩
        Mon .map (Y .fam .subst _ ∘ f .famf .transf _)
      ≈⟨ Mon .map-comp _ _ ⟩
        Mon .map (Y .fam .subst _) ∘ Mon .map (f .famf .transf _)
      ∎ where open ≈-Reasoning isEquiv
    monad .unit .idxf = idS _
    monad .unit .famf .transf x = Mon .unit
    monad .unit .famf .natural e = Mon .unit-natural _
    monad .join .idxf = idS _
    monad .join .famf .transf x = Mon .join
    monad .join .famf .natural e = Mon .join-natural _
    monad .map-cong eq .idxf-eq = eq .idxf-eq
    monad .map-cong eq .famf-eq .transf-eq {x} =
      isEquiv .trans (isEquiv .sym (Mon .map-comp _ _))
                     (Mon .map-cong (eq .famf-eq .transf-eq))
    monad .map-id .idxf-eq = ≈s-isEquivalence .refl
    monad .map-id {X} .famf-eq .transf-eq {x} =
      begin
        Mon .map (X .fam .subst _) ∘ Mon .map (id _)
      ≈⟨ ∘-cong (Mon .map-cong (X .fam .refl*)) ≈-refl ⟩
        Mon .map (id _) ∘ Mon .map (id _)
      ≈⟨ ∘-cong (Mon .map-id) (Mon .map-id) ⟩
        id _ ∘ id _
      ≈⟨ id-left ⟩
        id _
      ∎
      where open ≈-Reasoning isEquiv
    monad .map-comp f g .idxf-eq = ≈s-isEquivalence .refl
    monad .map-comp {X} {Y} {Z} f g .famf-eq .transf-eq {x} =
      begin
        Mon .map (Z .fam .subst _) ∘ Mon .map (f .famf .transf _ ∘ g .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-cong (Z .fam .refl*)) ≈-refl ⟩
        Mon .map (id _) ∘ Mon .map (f .famf .transf _ ∘ g .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-id) (Mon .map-comp _ _) ⟩
        id _ ∘ (Mon .map (f .famf .transf _) ∘ Mon .map (g .famf .transf x))
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf _) ∘ Mon .map (g .famf .transf x)
      ∎
      where open ≈-Reasoning isEquiv
    monad .unit-natural f .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-left (≈s-isEquivalence .sym prop-setoid.id-right)
    monad .unit-natural {X}{Y} f .famf-eq .transf-eq {x} =
      begin
        Mon .map (Y .fam .subst _) ∘ (Mon .unit ∘ f .famf .transf x)
      ≈⟨ ∘-cong (Mon .map-cong (Y .fam .refl*)) (Mon .unit-natural (f .famf .transf x)) ⟩
        Mon .map (id _) ∘ (Mon .map (f .famf .transf x) ∘ Mon .unit)
      ≈⟨ ∘-cong (Mon .map-id) ≈-refl ⟩
        id _ ∘ (Mon .map (f .famf .transf x) ∘ Mon .unit)
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf x) ∘ Mon .unit
      ∎
      where open ≈-Reasoning isEquiv
    monad .join-natural f .idxf-eq =
      ≈s-isEquivalence .trans prop-setoid.id-left (≈s-isEquivalence .sym prop-setoid.id-right)
    monad .join-natural {X} {Y} f .famf-eq .transf-eq {x} =
      begin
        Mon .map (Y .fam .subst _) ∘ (Mon .join ∘ Mon .map (Mon .map (f .famf .transf x)))
      ≈⟨ ∘-cong (Mon .map-cong (Y .fam .refl*)) (Mon .join-natural _) ⟩
        Mon .map (id _) ∘ (Mon .map (f .famf .transf x) ∘ Mon .join)
      ≈⟨ ∘-cong (Mon .map-id) ≈-refl ⟩
        id _ ∘ (Mon .map (f .famf .transf x) ∘ Mon .join)
      ≈⟨ id-left ⟩
        Mon .map (f .famf .transf x) ∘ Mon .join
      ∎
      where open ≈-Reasoning isEquiv

  module _ (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

    open import Data.List using ([]; _∷_)
    open Category 𝒞
    open IsEquivalence
    open HasTerminal
    open HasProducts P

    ListFam : (X : Obj) → Fam os es 𝒞 (prop-setoid.ListS (X .idx))
    ListFam X .fm [] = T .witness
    ListFam X .fm (x ∷ xs) = prod (X .fam .fm x) (ListFam X .fm xs)
    ListFam X .subst {[]} {[]} tt = id _
    ListFam X .subst {x ∷ xs} {y ∷ ys} (x≈y , xs≈ys) = prod-m (X .fam .subst x≈y) (ListFam X .subst xs≈ys)
    ListFam X .refl* {[]} = isEquiv .refl
    ListFam X .refl* {x ∷ xs} =
      begin
        prod-m (X .fam .subst (X .idx .Setoid.refl {x})) (ListFam X .subst (prop-setoid.List-≈-refl (X .idx) {xs}))
      ≈⟨ prod-m-cong (X .fam .refl*) (ListFam X .refl* {xs}) ⟩
        prod-m (id _) (id _)
      ≈⟨ prod-m-id ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    ListFam X .trans* {[]} {[]} {[]} e₁ e₂ = isEquiv .sym id-left
    ListFam X .trans* {x ∷ xs} {y ∷ ys} {z ∷ zs} (x≈y , xs≈ys) (y≈z , ys≈zs) =
      begin
        prod-m (X .fam .subst (X .idx .Setoid.trans y≈z x≈y)) (ListFam X .subst (prop-setoid.List-≈-trans (X .idx) ys≈zs xs≈ys))
      ≈⟨ prod-m-cong (X .fam .trans* x≈y y≈z) (ListFam X .trans* xs≈ys ys≈zs) ⟩
        prod-m (X .fam .subst x≈y ∘ X .fam .subst y≈z) (ListFam X .subst xs≈ys ∘ ListFam X .subst ys≈zs)
      ≈⟨ pair-functorial _ _ _ _ ⟩
       prod-m (X .fam .subst x≈y) (ListFam X .subst xs≈ys) ∘ prod-m (X .fam .subst y≈z) (ListFam X .subst ys≈zs)
      ∎
      where open ≈-Reasoning isEquiv

    ListF : Obj → Obj
    ListF X .idx = prop-setoid.ListS (X .idx)
    ListF X .fam = ListFam X

    module FT = HasTerminal (terminal T)
    open products P
    open _⇒f_
    open _≃f_

    nil : ∀ {X} → Mor FT.witness (ListF X)
    nil .idxf = prop-setoid.nil
    nil .famf .transf (lift tt) = id _
    nil .famf .natural x₁≈x₂ = isEquiv .refl

    cons : ∀ {X} → Mor (X ⊗ (ListF X)) (ListF X)
    cons .idxf = prop-setoid.cons
    cons .famf .transf x = id _
    cons .famf .natural x₁≈x₂ =
      isEquiv .trans id-left (isEquiv .sym id-right)

    private
      _⊛_ = prod
      _⊛f_ = prod-m

      -- FIXME: if we had a DSL of finite products the naturality
      -- would be easier
      shuffle : ∀ {X Y Z} → (X ⊛ (Y ⊛ Z)) ⇒ (X ⊛ (Y ⊛ (X ⊛ Z)))
      shuffle = pair p₁ (pair (p₁ ∘ p₂) (id _ ⊛f p₂))

      shuffle-natural : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f : X₁ ⇒ X₂) (g : Y₁ ⇒ Y₂) (h : Z₁ ⇒ Z₂) →
          (shuffle ∘ (f ⊛f (g ⊛f h))) ≈ ((f ⊛f (g ⊛f (f ⊛f h))) ∘ shuffle)
      shuffle-natural f g h =
        begin
          shuffle ∘ (f ⊛f (g ⊛f h))
        ≈⟨ pair-natural _ _ _ ⟩
          pair (p₁ ∘ (f ⊛f (g ⊛f h))) (pair (p₁ ∘ p₂) (id _ ⊛f p₂) ∘ (f ⊛f (g ⊛f h)))
        ≈⟨ pair-cong (pair-p₁ _ _) (pair-natural _ _ _) ⟩
          pair (f ∘ p₁) (pair ((p₁ ∘ p₂) ∘ (f ⊛f (g ⊛f h))) ((id _ ⊛f p₂) ∘ (f ⊛f (g ⊛f h))))
        ≈⟨ pair-cong ≈-refl (pair-cong (assoc _ _ _) (isEquiv .sym (pair-functorial _ _ _ _))) ⟩
          pair (f ∘ p₁) (pair (p₁ ∘ (p₂ ∘ (f ⊛f (g ⊛f h)))) ((id _ ∘ f) ⊛f (p₂ ∘ (g ⊛f h))))
        ≈⟨ pair-cong ≈-refl (pair-cong (∘-cong ≈-refl (pair-p₂ _ _)) (prod-m-cong id-swap (pair-p₂ _ _))) ⟩
           pair (f ∘ p₁) (pair (p₁ ∘ ((g ⊛f h) ∘ p₂)) ((f ∘ id _) ⊛f (h ∘ p₂)))
        ≈⟨ pair-cong ≈-refl (pair-cong (isEquiv .sym (assoc _ _ _)) ≈-refl) ⟩
           pair (f ∘ p₁) (pair ((p₁ ∘ (g ⊛f h)) ∘ p₂) ((f ∘ id _) ⊛f (h ∘ p₂)))
        ≈⟨ pair-cong ≈-refl (pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) ≈-refl) ⟩
           pair (f ∘ p₁) (pair ((g ∘ p₁) ∘ p₂) ((f ∘ id _) ⊛f (h ∘ p₂)))
        ≈⟨ pair-cong ≈-refl (pair-cong (assoc _ _ _) (pair-functorial _ _ _ _)) ⟩
          pair (f ∘ p₁) (pair (g ∘ (p₁ ∘ p₂)) ((f ⊛f h) ∘ (id _ ⊛f p₂)))
        ≈⟨ pair-cong ≈-refl (isEquiv .sym (pair-compose _ _ _ _)) ⟩
          pair (f ∘ p₁) ((g ⊛f (f ⊛f h)) ∘ pair (p₁ ∘ p₂) (id _ ⊛f p₂))
        ≈⟨ isEquiv .sym (pair-compose _ _ _ _) ⟩
          (f ⊛f (g ⊛f (f ⊛f h))) ∘ shuffle
        ∎
        where open ≈-Reasoning isEquiv

    foldr : ∀ {X Y Z} → Mor X Z → Mor (X ⊗ (Y ⊗ Z)) Z → Mor (X ⊗ ListF Y) Z
    foldr nilCase consCase .idxf = prop-setoid.foldrP (nilCase .idxf) (consCase .idxf)
    foldr nilCase consCase .famf .transf (x , []) = nilCase .famf .transf x ∘ p₁
    foldr nilCase consCase .famf .transf (x , y ∷ ys) =
      (consCase .famf .transf (x , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x , ys)))) ∘ shuffle
    foldr {X} {Y} {Z} nilCase consCase .famf .natural {x₁ , []} {x₂ , []} (x₁≈x₂ , tt) =
      begin
        (nilCase .famf .transf x₂ ∘ p₁) ∘ prod-m (X .fam .subst _) (id _)
      ≈⟨ assoc _ _ _ ⟩
        nilCase .famf .transf x₂ ∘ (p₁ ∘ prod-m (X .fam .subst _) (id _))
      ≈⟨ ∘-cong ≈-refl (pair-p₁ _ _) ⟩
        nilCase .famf .transf x₂ ∘ (X .fam .subst _ ∘ p₁)
      ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
        (nilCase .famf .transf x₂ ∘ X .fam .subst _) ∘ p₁
      ≈⟨ ∘-cong (nilCase .famf .natural _) ≈-refl ⟩
        (Z .fam .subst _ ∘ nilCase .famf .transf x₁) ∘ p₁
      ≈⟨ assoc _ _ _ ⟩
        Z .fam .subst _ ∘ (nilCase .famf .transf x₁ ∘ p₁)
      ∎ where open ≈-Reasoning isEquiv
    foldr {X} {Y} {Z} nilCase consCase .famf .natural {x₁ , y₁ ∷ ys₁} {x₂ , y₂ ∷ ys₂} (x₁≈x₂ , y₁≈y₂ , ys₁≈ys₂) =
      begin
        ((consCase .famf .transf (x₂ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)))) ∘ shuffle) ∘ (sX ⊛f (sY ⊛f sYS))
      ≈⟨ assoc _ _ _ ⟩
        (consCase .famf .transf (x₂ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)))) ∘ (shuffle ∘ (sX ⊛f (sY ⊛f sYS)))
      ≈⟨ ∘-cong ≈-refl (shuffle-natural _ _ _) ⟩
        (consCase .famf .transf (x₂ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)))) ∘ ((sX ⊛f (sY ⊛f (sX ⊛f sYS))) ∘ shuffle)
      ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
        ((consCase .famf .transf (x₂ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)))) ∘ (sX ⊛f (sY ⊛f (sX ⊛f sYS)))) ∘ shuffle
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂))) ∘ (sX ⊛f (sY ⊛f (sX ⊛f sYS))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (isEquiv .sym (pair-functorial _ _ _ _))) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m (id _ ∘ sX) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₂ , ys₂)) ∘ (sY ⊛f (sX ⊛f sYS))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (prod-m-cong ≈-refl (isEquiv .sym (pair-functorial _ _ _ _)))) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m (id _ ∘ sX) (prod-m (id _ ∘ sY) (foldr nilCase consCase .famf .transf (x₂ , ys₂) ∘ (sX ⊛f sYS))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (prod-m-cong id-swap (prod-m-cong id-swap (foldr nilCase consCase .famf .natural (x₁≈x₂ , ys₁≈ys₂))))) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m (sX ∘ id _) (prod-m (sY ∘ id _) (Z .fam .subst _ ∘ foldr nilCase consCase .famf .transf (x₁ , ys₁))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (prod-m-cong ≈-refl (pair-functorial _ _ _ _))) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m (sX ∘ id _) (prod-m sY (Z .fam .subst _) ∘ prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong ≈-refl (pair-functorial _ _ _ _)) ≈-refl ⟩
        (consCase .famf .transf (x₂ , _) ∘ (prod-m sX (prod-m sY (Z .fam .subst _)) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))))) ∘ shuffle
      ≈⟨ ∘-cong (isEquiv .sym (assoc _ _ _)) ≈-refl ⟩
        ((consCase .famf .transf (x₂ , _) ∘ prod-m sX (prod-m sY (Z .fam .subst _))) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁)))) ∘ shuffle
      ≈⟨ ∘-cong (∘-cong (consCase .famf .natural (x₁≈x₂ , y₁≈y₂ , eq)) ≈-refl) ≈-refl ⟩
        ((Z .fam .subst _ ∘ consCase .famf .transf (x₁ , _)) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁)))) ∘ shuffle
      ≈⟨ ∘-cong (assoc _ _ _) ≈-refl ⟩
        (Z .fam .subst _ ∘ (consCase .famf .transf (x₁ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁))))) ∘ shuffle
      ≈⟨ assoc _ _ _ ⟩
        Z .fam .subst _ ∘ ((consCase .famf .transf (x₁ , _) ∘ prod-m (id _) (prod-m (id _) (foldr nilCase consCase .famf .transf (x₁ , ys₁)))) ∘ shuffle)
      ∎
      where open ≈-Reasoning isEquiv
            sX = X .fam .subst x₁≈x₂
            sY = Y .fam .subst y₁≈y₂
            sYS = ListF Y .fam .subst ys₁≈ys₂
            eq = prop-setoid.foldrP (nilCase .idxf) (consCase .idxf) ._⇒s_.func-resp-≈ (x₁≈x₂ , ys₁≈ys₂)

  -- If 𝒞 has binary biproducts and Setoid-indexed products, then this
  -- category has exponentials.
  --
  -- More precisely, if 𝒞 has binary coproducts and Setoid-indexed
  -- products, then the category of families has symmetric monoidal
  -- structure (with the monoidal product generated by the
  -- coproduct). If the coproducts are in fact biproducts, then Fam(𝒞)
  -- is cartesian closed.
  module _ (P : HasBiproducts 𝒞) (SP : HasSetoidProducts os es 𝒞) where

    open Category 𝒞
    open HasBiproducts hiding (hasProducts)
    open IsEquivalence
    open HasExponentials
    open HasSetoidProducts

    open products (HasBiproducts.hasProducts P)

    open _⇒s_
    open _⇒f_
    open _≈s_
    open _≃f_

    _⟶_ : Obj → Obj → Obj
    (X ⟶ Y) .idx = Category.hom-setoid cat X Y
    (X ⟶ Y) .fam .fm f = SP .Π (X .idx) (Y .fam [ f .idxf ])
    (X ⟶ Y) .fam .subst {f} {g} e =
        -- FIXME: this is a general 'map' on Π, do the definitions in HasSetoidProducts
        SP .lambdaΠ
           (SP .Π (X .idx) (Y .fam [ f .idxf ]))
           (Y .fam [ g .idxf ])
           (record { transf = λ x → Y .fam .subst (e .idxf-eq .func-eq (X .idx .Setoid.refl)) ∘ SP .evalΠ _ x
                   ; natural = λ {x₁} {x₂} x₁≈x₂ → {!!} })
    (X ⟶ Y) .fam .refl* =
      {!!}
    (X ⟶ Y) .fam .trans* =
      {!!}


    eval⟶ : ∀ {X Y : Obj} → Mor (X ⊗ (X ⟶ Y)) Y
    eval⟶ .idxf .func (x , f) = f .idxf .func x
    eval⟶ .idxf .func-resp-≈ (x₁≈x₂ , f₁≈f₂) = f₁≈f₂ .idxf-eq .func-eq x₁≈x₂
    eval⟶ .famf .transf (x , f) =
      P .copair (f .famf .transf x) (SP .evalΠ _ x)
    eval⟶ {X} {Y} .famf .natural {x₁ , f₁} {x₂ , f₂} (x₁≈x₂ , f₁≈f₂) =
      begin
        P .copair (f₂ .famf .transf x₂) (SP .evalΠ (Y .fam [ f₂ .idxf ]) x₂) ∘ prod-m P (X .fam .subst x₁≈x₂) ((X ⟶ Y) .fam .subst f₁≈f₂)
      ≈⟨ {!!} ⟩
        Y .fam .subst _ ∘ P .copair (f₁ .famf .transf x₁) (SP .evalΠ (Y .fam [ f₁ .idxf ]) x₁)
      ∎
      where open ≈-Reasoning isEquiv

    lambda⟶ : ∀ {X Y Z} → Mor (X ⊗ Y) Z → Mor X (Y ⟶ Z)
    lambda⟶ f .idxf .func x .idxf .func y = f .idxf .func (x , y)
    lambda⟶ {X} f .idxf .func x .idxf .func-resp-≈ y₁≈y₂ = f .idxf .func-resp-≈ ((X .idx .Setoid.refl) , y₁≈y₂)
    lambda⟶ f .idxf .func x .famf .transf y = f .famf .transf (x , y) ∘ P .in₂
    lambda⟶ {X} {Y} {Z} f .idxf .func x .famf .natural {y₁} {y₂} y₁≈y₂ =
      begin
        (f .famf .transf (x , y₂) ∘ P .in₂) ∘ Y .fam .subst _
      ≈⟨ {!!} ⟩ -- FIXME: need naturality of in₂
        Z .fam .subst _ ∘ (f .famf .transf (x , y₁) ∘ P .in₂)
      ∎
      where open ≈-Reasoning isEquiv
    lambda⟶ f .idxf .func-resp-≈ x₁≈x₂ .idxf-eq .func-eq y₁≈y₂ = f .idxf .func-resp-≈ (x₁≈x₂ , y₁≈y₂)
    lambda⟶ {X} {Y} {Z} f .idxf .func-resp-≈ {x₁} {x₂} x₁≈x₂ .famf-eq .transf-eq {y} =
      begin
        Z .fam .subst _ ∘ (f .famf .transf (x₁ , y) ∘ P .in₂)
      ≈⟨ isEquiv .sym (assoc _ _ _) ⟩
        (Z .fam .subst _ ∘ f .famf .transf (x₁ , y)) ∘ P .in₂
      ≈⟨ isEquiv .sym (∘-cong (f .famf .natural (x₁≈x₂ , Y .idx .Setoid.refl)) ≈-refl) ⟩
        (f .famf .transf (x₂ , y) ∘ (X ⊗ Y) .fam .subst _) ∘ P .in₂
      ≈⟨ assoc _ _ _ ⟩
        f .famf .transf (x₂ , y) ∘ ((X ⊗ Y) .fam .subst _ ∘ P .in₂)
      ≈⟨ ∘-cong ≈-refl {!!} ⟩ -- FIXME: need naturality of in₂
        f .famf .transf (x₂ , y) ∘ (P .in₂ ∘ Y .fam .subst _)
      ≈⟨ ∘-cong ≈-refl (∘-cong ≈-refl (Y .fam .refl*)) ⟩
        f .famf .transf (x₂ , y) ∘ (P .in₂ ∘ id _)
      ≈⟨ ∘-cong ≈-refl id-right ⟩
        f .famf .transf (x₂ , y) ∘ P .in₂
      ∎
      where open ≈-Reasoning isEquiv
    lambda⟶ {X} {Y} {Z} f .famf .transf x =
      SP .lambdaΠ
        (X .fam .fm x)
        (Z .fam [ lambda⟶ {X} {Y} {Z} f .idxf .func x .idxf ])
        (record { transf = λ y →  f .famf .transf (x , y) ∘ P .in₁
                ; natural = λ {y₁} {y₂} y₁≈y₂ → {!!} -- FIXME: need naturality of in₁
                })
    lambda⟶ f .famf .natural x₁≈₂ = {!!}

    exponentials : HasExponentials cat products
    exponentials .exp = _⟶_
    exponentials .eval = eval⟶
    exponentials .lambda = lambda⟶
