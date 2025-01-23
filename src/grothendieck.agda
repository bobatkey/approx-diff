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

  -- If 𝒞 has products, then so does the category of families
  module products (P : HasProducts 𝒞) where

    open Category 𝒞
    open HasProducts
    open IsEquivalence
    open _⇒f_

    _⊗_ : Obj → Obj → Obj
    (X ⊗ Y) .idx = ⊗-setoid (X .idx) (Y .idx)
    (X ⊗ Y) .fam .fm (x , y) = P .prod (X .fam .fm x) (Y .fam .fm y)
    (X ⊗ Y) .fam .subst (e₁ , e₂) =
      P .pair (X .fam .subst e₁ ∘ P .p₁) (Y .fam .subst e₂ ∘ P .p₂)
    (X ⊗ Y) .fam .refl* =
      begin
        P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-cong (∘-cong (X .fam .refl*) (isEquiv .refl)) (∘-cong (Y .fam .refl*) (isEquiv .refl)) ⟩
        P .pair (id _ ∘ P .p₁) (id _ ∘ P .p₂)
      ≈⟨ P .pair-cong id-left id-left ⟩
        P .pair (P .p₁) (P .p₂)
      ≈⟨ pair-ext0 P ⟩
        id _
      ∎ where open ≈-Reasoning isEquiv
    (X ⊗ Y) .fam .trans* {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} (x₂≈x₃ , y₂≈y₃) (x₁≈x₂ , y₁≈y₂) =
      begin
        P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ≈⟨ P .pair-cong (∘-cong (X .fam .trans* _ _) (isEquiv .refl)) (∘-cong (Y .fam .trans* _ _) (isEquiv .refl)) ⟩
        P .pair ((X .fam .subst _ ∘ X .fam .subst _) ∘ P .p₁) ((Y .fam .subst _ ∘ Y .fam .subst _) ∘ P .p₂)
      ≈⟨ pair-functorial P _ _ _ _ ⟩
        P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂) ∘ P .pair (X .fam .subst _ ∘ P .p₁) (Y .fam .subst _ ∘ P .p₂)
      ∎
      where open ≈-Reasoning isEquiv

    products : HasProducts cat
    products .prod = _⊗_
    products .p₁ .idxf = prop-setoid.project₁
    products .p₁ .famf .transf (x , y) = P .p₁
    products .p₁ .famf .natural (e₁ , e₂) = {!!}
    products .p₂ .idxf = prop-setoid.project₂
    products .p₂ .famf .transf (x , y) = P .p₂
    products .p₂ .famf .natural (e₁ , e₂) = {!!}
    products .pair f g .idxf = prop-setoid.pair (f .idxf) (g .idxf)
    products .pair f g .famf .transf x = P .pair (f .famf .transf x) (g .famf .transf x)
    products .pair f g .famf .natural {x₁} {x₂} x₁≈x₂ = {!!}
    products .pair-cong = {!!}
    products .pair-p₁ = {!!}
    products .pair-p₂ = {!!}
    products .pair-ext = {!!}

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

  -- If 𝒞 has binary biproducts and Setoid-indexed products, then this
  -- category has exponentials
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
    (X ⟶ Y) .fam .fm f =
      SP .Π 𝟙 (X .idx) (Y .fam [ f .idxf ∘S prop-setoid.project₂ ]) .fm (lift tt)
    (X ⟶ Y) .fam .subst {f} {g} e =
      SP .lambdaΠ {X = 𝟙} {Y = X .idx}
           {P = SP .Π 𝟙 (X .idx) (Y .fam [ f .idxf ∘S prop-setoid.project₂ ])}
           (Y .fam [ g .idxf ∘S prop-setoid.project₂ ])
           (reindex-≈ {P = Y .fam}
                      (f .idxf ∘S prop-setoid.project₂)
                      (g .idxf ∘S prop-setoid.project₂)
                      (prop-setoid.∘S-cong (e .idxf-eq)
                         (≈s-isEquivalence .refl {prop-setoid.project₂})) ∘f SP .evalΠ _)
           .transf (lift tt)
    (X ⟶ Y) .fam .refl* = {!!}
    (X ⟶ Y) .fam .trans* = {!!}

    eval⟶ : ∀ {X Y : Obj} → Mor (X ⊗ (X ⟶ Y)) Y
    eval⟶ .idxf .func (x , f) = f .idxf .func x
    eval⟶ .idxf .func-resp-≈ (x₁≈x₂ , f₁≈f₂) = f₁≈f₂ .idxf-eq .func-eq x₁≈x₂
    eval⟶ .famf .transf (x , f) = SP .evalΠ _ .transf (lift tt , x)  ∘ P .p₂
    eval⟶ .famf .natural = {!!}

    exponentials : HasExponentials cat products
    exponentials .exp = _⟶_
    exponentials .eval = eval⟶
    exponentials .lambda {X} {Y} {Z} f .idxf .func x .idxf .func y = f .idxf .func (x , y)
    exponentials .lambda {X} {Y} {Z} f .idxf .func x .idxf .func-resp-≈ y₁≈y₂ = f .idxf .func-resp-≈ (X .idx .Setoid.refl , y₁≈y₂)
    exponentials .lambda {X} {Y} {Z} f .idxf .func x .famf .transf y = f .famf .transf (x , y) ∘ P .in₂
    exponentials .lambda {X} {Y} {Z} f .idxf .func x .famf .natural x₁≈x₂ = {!!}
    exponentials .lambda {X} {Y} {Z} f .idxf .func-resp-≈ x₁≈x₂ .idxf-eq .func-eq y₁≈y₂ = f .idxf .func-resp-≈ (x₁≈x₂ , y₁≈y₂)
    exponentials .lambda {X} {Y} {Z} f .idxf .func-resp-≈ x₁≈x₂ .famf-eq .transf-eq = {!!}
    exponentials .lambda {X} {Y} {Z} f .famf .transf x =
      SP .lambdaΠ {X = 𝟙} {Y = Y .idx}
                  {P = X .fam [ prop-setoid.const (X .idx) x ]}
                  (Z .fam [ record { func = λ y → f .idxf .func (x , y)
                                   ; func-resp-≈ = λ y₁≈y₂ → f .idxf .func-resp-≈ (X .idx .Setoid.refl , y₁≈y₂) }
                            ∘S prop-setoid.project₂ {X = 𝟙} {Y = Y .idx} ])
                  (record { transf = λ (_ , y) → f .famf .transf (x , y) ∘ P .in₁
                          ; natural = λ (_ , y₁≈y₂) → {!!}
                          })
         .transf (lift tt)
    exponentials .lambda {X} {Y} {Z} f .famf .natural x₁≈x₂ = {!!}

{-
  -- If 𝒞 has a strong monad, then so does this category
  module _ (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (Mon : StrongMonad 𝒞 P) where

    open Category 𝒞
    open StrongMonad
    private
      module P = HasProducts P
      module Mon = StrongMonad Mon

    strongMonad : StrongMonad cat (products P)
    strongMonad .M X .idx = X .idx
    strongMonad .M X .iobj x = Mon.M (X .iobj x)
    strongMonad .M X .iobj-transport = {!!}
    strongMonad .M X .iobj-id = {!!}
    strongMonad .M X .iobj-trans = {!!}
    strongMonad .unit .idxf = idS _
    strongMonad .unit .ifunc = {!!}
    strongMonad .unit .ifunc-≈ = {!!}
    strongMonad .extend f .idxf = f .idxf
    strongMonad .extend f .ifunc = {!!}
    strongMonad .extend f .ifunc-≈ = {!!}
-}
