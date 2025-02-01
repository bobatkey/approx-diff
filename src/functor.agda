{-# OPTIONS --prop --postfix-projections --safe #-}

module functor where

open import Level
open import categories
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)

open IsEquivalence

record Functor {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : Category o₁ m₁ e₁)
         (𝒟 : Category o₂ m₂ e₂) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
  no-eta-equality
  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  field
    fobj : 𝒞.obj → 𝒟.obj
    fmor : ∀ {x y} → x 𝒞.⇒ y → fobj x 𝒟.⇒ fobj y
    fmor-cong : ∀ {x y}{f₁ f₂ : x 𝒞.⇒ y} → f₁ 𝒞.≈ f₂ → fmor f₁ 𝒟.≈ fmor f₂
    fmor-id : ∀ {x} → fmor (𝒞.id x) 𝒟.≈ 𝒟.id _
    fmor-comp : ∀ {x y z} (f : y 𝒞.⇒ z) (g : x 𝒞.⇒ y) →
                fmor (f 𝒞.∘ g) 𝒟.≈ (fmor f 𝒟.∘ fmor g)

module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         {ℰ : Category o₃ m₃ e₃}
    where

  private
    module ℰ = Category ℰ

  open Functor

  _∘F_ : Functor 𝒟 ℰ → Functor 𝒞 𝒟 → Functor 𝒞 ℰ
  (F ∘F G) .fobj x = F .fobj (G .fobj x)
  (F ∘F G) .fmor f = F .fmor (G .fmor f)
  (F ∘F G) .fmor-cong f₁≈f₂ = F .fmor-cong (G .fmor-cong f₁≈f₂)
  (F ∘F G) .fmor-id = ℰ.isEquiv .trans (F .fmor-cong (G .fmor-id)) (F .fmor-id)
  (F ∘F G) .fmor-comp f g =
    ℰ.isEquiv .trans (F .fmor-cong (G .fmor-comp _ _)) (F .fmor-comp _ _)

module _ {o₁ m₁ e₁ o₂ m₂ e₂} where

  constF : ∀ (𝒞 : Category o₁ m₁ e₁)
             {𝒟 : Category o₂ m₂ e₂}
             (x  : 𝒟 .Category.obj) →
             Functor 𝒞 𝒟
  constF 𝒞 {𝒟} x .Functor.fobj _ = x
  constF 𝒞 {𝒟} x .Functor.fmor _ = 𝒟 .Category.id x
  constF 𝒞 {𝒟} x .Functor.fmor-cong _ = 𝒟 .Category.isEquiv .refl
  constF 𝒞 {𝒟} x .Functor.fmor-id = 𝒟 .Category.isEquiv .refl
  constF 𝒞 {𝒟} x .Functor.fmor-comp _ _ = 𝒟 .Category.isEquiv .sym (𝒟 .Category.id-left)

-- FIXME: composition of functors, and the identity and constant functors

-- Functors form a category
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor

  record NatTrans (F G : Functor 𝒞 𝒟) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
    no-eta-equality
    field
      transf : ∀ x → F .fobj x 𝒟.⇒ G .fobj x
      natural : ∀ {x y} (f : x 𝒞.⇒ y) →
        (G .fmor f 𝒟.∘ transf x) 𝒟.≈ (transf y 𝒟.∘ F .fmor f)

  open NatTrans

  record ≃-NatTrans {F G : Functor 𝒞 𝒟} (α β : NatTrans F G) : Prop (o₁ ⊔ e₂) where
    field
      transf-eq : ∀ x → α .transf x 𝒟.≈ β .transf x
  open ≃-NatTrans

  ≃-isEquivalence : ∀ {F G} → IsEquivalence (≃-NatTrans {F} {G})
  ≃-isEquivalence .refl .transf-eq x = 𝒟.≈-refl
  ≃-isEquivalence .sym e .transf-eq x = 𝒟.≈-sym (e .transf-eq x)
  ≃-isEquivalence .trans e₁ e₂ .transf-eq x = 𝒟.isEquiv .trans (e₁ .transf-eq x) (e₂ .transf-eq x)

  id : ∀ F → NatTrans F F
  id F .transf x = 𝒟.id _
  id F .natural f = 𝒟.≈-sym 𝒟.id-swap

  _∘_ : ∀ {F G H} → NatTrans G H → NatTrans F G → NatTrans F H
  (α ∘ β) .transf x = α .transf x 𝒟.∘ β .transf x
  _∘_ {F} {G} {H} α β .natural {x} {y} f =
    begin
      H .fmor f 𝒟.∘ (α .transf x 𝒟.∘ β .transf x)
    ≈⟨ 𝒟.≈-sym (𝒟.assoc _ _ _) ⟩
      (H .fmor f 𝒟.∘ α .transf x) 𝒟.∘ β .transf x
    ≈⟨ 𝒟.∘-cong (α .natural f) 𝒟.≈-refl ⟩
      (α .transf y 𝒟.∘ G .fmor f) 𝒟.∘ β .transf x
    ≈⟨ 𝒟.assoc _ _ _ ⟩
      α .transf y 𝒟.∘ (G .fmor f 𝒟.∘ β .transf x)
    ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (β .natural f) ⟩
      α .transf y 𝒟.∘ (β .transf y 𝒟.∘ F .fmor f)
    ≈⟨ 𝒟.≈-sym (𝒟.assoc _ _ _) ⟩
      (α .transf y 𝒟.∘ β .transf y) 𝒟.∘ F .fmor f
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  ∘NT-cong : ∀ {F G H}{α₁ α₂ : NatTrans G H}{β₁ β₂ : NatTrans F G} →
            ≃-NatTrans α₁ α₂ → ≃-NatTrans β₁ β₂ → ≃-NatTrans (α₁ ∘ β₁) (α₂ ∘ β₂)
  ∘NT-cong α₁≃α₂ β₁≃β₂ .transf-eq x = 𝒟.∘-cong (α₁≃α₂ .transf-eq x) (β₁≃β₂ .transf-eq x)

  NT-assoc : ∀ {F G H I}(α : NatTrans H I)(β : NatTrans G H)(γ : NatTrans F G) →
             ≃-NatTrans ((α ∘ β) ∘ γ) (α ∘ (β ∘ γ))
  NT-assoc α β γ .transf-eq x = 𝒟.assoc _ _ _

  NT-id-left : ∀ {F G}{α : NatTrans F G} → ≃-NatTrans (id _ ∘ α) α
  NT-id-left .transf-eq x = 𝒟.id-left

  constFmor : ∀ {x} {y} → (x 𝒟.⇒ y) → NatTrans (constF 𝒞 x) (constF 𝒞 y)
  constFmor f .transf _ = f
  constFmor f .natural _ = 𝒟.id-swap

  -- Horizontal composition of natural transformations
module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         {ℰ : Category o₃ m₃ e₃}
         {F₁ : Functor 𝒟 ℰ} {F₂ : Functor 𝒞 𝒟}
         {G₁ : Functor 𝒟 ℰ} {G₂ : Functor 𝒞 𝒟}
         where

  open Functor
  open NatTrans
  open ≃-NatTrans

  private
    module 𝒟 = Category 𝒟
    module ℰ = Category ℰ

  _∘H_ : NatTrans F₁ G₁ → NatTrans F₂ G₂ → NatTrans (F₁ ∘F F₂) (G₁ ∘F G₂)
  (α ∘H β) .transf x = α .transf _ ℰ.∘ F₁ .fmor (β .transf x)
  (α ∘H β) .natural f =
    begin
      G₁ .fmor (G₂ .fmor f) ℰ.∘ (α .transf _ ℰ.∘ F₁ .fmor (β .transf _))
    ≈⟨ ℰ.≈-sym (ℰ.assoc _ _ _) ⟩
      (G₁ .fmor (G₂ .fmor f) ℰ.∘ α .transf _) ℰ.∘ F₁ .fmor (β .transf _)
    ≈⟨ ℰ.∘-cong (α .natural _) ℰ.≈-refl ⟩
      (α .transf _ ℰ.∘ F₁ .fmor (G₂ .fmor f)) ℰ.∘ F₁ .fmor (β .transf _)
    ≈⟨ ℰ.assoc _ _ _ ⟩
      α .transf _ ℰ.∘ (F₁ .fmor (G₂ .fmor f) ℰ.∘ F₁ .fmor (β .transf _))
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (ℰ.≈-sym (F₁ .fmor-comp _ _)) ⟩
      α .transf _ ℰ.∘ F₁ .fmor (G₂ .fmor f 𝒟.∘ β .transf _)
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (F₁ .fmor-cong (β .natural _)) ⟩
      α .transf _ ℰ.∘ F₁ .fmor (β .transf _ 𝒟.∘ F₂ .fmor f)
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (F₁ .fmor-comp _ _) ⟩
      α .transf _ ℰ.∘ (F₁ .fmor (β .transf _) ℰ.∘ F₁ .fmor (F₂ .fmor f))
    ≈⟨ ℰ.≈-sym (ℰ.assoc _ _ _) ⟩
      (α .transf _ ℰ.∘ F₁ .fmor (β .transf _)) ℰ.∘ F₁ .fmor (F₂ .fmor f)
    ∎ where open ≈-Reasoning ℰ.isEquiv

  ∘H-cong : ∀ {α₁ α₂ : NatTrans F₁ G₁} {β₁ β₂ : NatTrans F₂ G₂}
              (α₁≈α₂ : ≃-NatTrans α₁ α₂) (β₁≈β₂ : ≃-NatTrans β₁ β₂) →
              ≃-NatTrans (α₁ ∘H β₁) (α₂ ∘H β₂)
  ∘H-cong α₁≈α₂ β₁≈β₂ .transf-eq x = ℰ.∘-cong (α₁≈α₂ .transf-eq _) (F₁ .fmor-cong (β₁≈β₂ .transf-eq x))

module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         {ℰ : Category o₃ m₃ e₃}
         where

  open Functor
  open NatTrans
  open ≃-NatTrans

  private
    module 𝒟 = Category 𝒟
    module ℰ = Category ℰ

  interchange : ∀ {F₁ G₁ H₁ : Functor 𝒟 ℰ}
                  {F₂ G₂ H₂ : Functor 𝒞 𝒟}
                (α₁ : NatTrans G₁ H₁) (β₁ : NatTrans F₁ G₁)
                (α₂ : NatTrans G₂ H₂) (β₂ : NatTrans F₂ G₂) →
         ≃-NatTrans ((α₁ ∘ β₁) ∘H (α₂ ∘ β₂)) ((α₁ ∘H α₂) ∘ (β₁ ∘H β₂))
  interchange {F₁}{G₁}{H₁}{F₂}{G₂}{H₂} α₁ α₂ β₁ β₂ .transf-eq x =
    begin
      (α₁ .transf _ ℰ.∘ α₂ .transf _) ℰ.∘ F₁ .fmor (β₁ .transf x 𝒟.∘ β₂ .transf x)
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (F₁ .fmor-comp _ _) ⟩
      (α₁ .transf _ ℰ.∘ α₂ .transf _) ℰ.∘ (F₁ .fmor (β₁ .transf x) ℰ.∘ F₁ .fmor (β₂ .transf x))
    ≈⟨ ℰ.assoc _ _ _ ⟩
      α₁ .transf _ ℰ.∘ (α₂ .transf _ ℰ.∘ (F₁ .fmor (β₁ .transf x) ℰ.∘ F₁ .fmor (β₂ .transf x)))
    ≈⟨ ℰ.≈-sym (ℰ.∘-cong ℰ.≈-refl (ℰ.assoc _ _ _)) ⟩
      α₁ .transf _ ℰ.∘ ((α₂ .transf _ ℰ.∘ F₁ .fmor (β₁ .transf x)) ℰ.∘ F₁ .fmor (β₂ .transf x))
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (ℰ.∘-cong (ℰ.≈-sym (α₂ .natural _)) ℰ.≈-refl) ⟩
      α₁ .transf _ ℰ.∘ ((G₁ .fmor (β₁ .transf x) ℰ.∘ α₂ .transf _) ℰ.∘ F₁ .fmor (β₂ .transf x))
    ≈⟨ ℰ.∘-cong ℰ.≈-refl (ℰ.assoc _ _ _) ⟩
      α₁ .transf _ ℰ.∘ (G₁ .fmor (β₁ .transf x) ℰ.∘ (α₂ .transf _ ℰ.∘ F₁ .fmor (β₂ .transf x)))
    ≈⟨ ℰ.≈-sym (ℰ.assoc _ _ _) ⟩
      (α₁ .transf _ ℰ.∘ G₁ .fmor (β₁ .transf x)) ℰ.∘ (α₂ .transf _ ℰ.∘ F₁ .fmor (β₂ .transf x))
    ∎
    where open ≈-Reasoning ℰ.isEquiv


  -- FIXME: draw a diagram!

  -- V-id-left : (α : NatTrans F₂ G₂) → ≃-NatTrans (id F ∘V α) ?
  -- V-id-left α = ?

open ≃-NatTrans

-- Category of functors
[_⇒_] : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} →
         Category o₁ m₁ e₁ →
         Category o₂ m₂ e₂ →
         Category (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ e₂)
[ 𝒞 ⇒ 𝒟 ] .Category.obj = Functor 𝒞 𝒟
[ 𝒞 ⇒ 𝒟 ] .Category._⇒_ = NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category._≈_ = ≃-NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category.isEquiv = ≃-isEquivalence
[ 𝒞 ⇒ 𝒟 ] .Category.id = id
[ 𝒞 ⇒ 𝒟 ] .Category._∘_ = _∘_
[ 𝒞 ⇒ 𝒟 ] .Category.∘-cong = ∘NT-cong
[ 𝒞 ⇒ 𝒟 ] .Category.id-left = NT-id-left
[ 𝒞 ⇒ 𝒟 ] .Category.id-right .transf-eq x = 𝒟 .Category.id-right
[ 𝒞 ⇒ 𝒟 ] .Category.assoc = NT-assoc

const : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} →
          {𝒞 : Category o₁ m₁ e₁} →
          {𝒟 : Category o₂ m₂ e₂} →
          Functor 𝒟 [ 𝒞 ⇒ 𝒟 ]
const .Functor.fobj x = constF _ x
const .Functor.fmor f = constFmor f
const .Functor.fmor-cong eq .transf-eq x = eq
const {𝒟 = 𝒟} .Functor.fmor-id .transf-eq x = Category.≈-refl 𝒟
const {𝒟 = 𝒟} .Functor.fmor-comp f g .transf-eq x = Category.≈-refl 𝒟

record HasLimits {o₁ m₁ e₁ o₂ m₂ e₂} (𝒟 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂)
             : Set (o₁ ⊔ e₁ ⊔ e₂ ⊔ m₁ ⊔ m₂ ⊔ o₂) where
  private
    module 𝒞 = Category 𝒞
  field
    Π : Functor 𝒟 𝒞 → 𝒞.obj
    lambdaΠ : ∀ (x : 𝒞.obj) F → NatTrans (constF 𝒟 {𝒞} x) F → (x 𝒞.⇒ Π F)
    evalΠ   : ∀ F → NatTrans (constF 𝒟 (Π F)) F

    lambda-cong : ∀ {x} {F : Functor 𝒟 𝒞} {α β : NatTrans (constF 𝒟 x) F} →
                  ≃-NatTrans α β → lambdaΠ x F α 𝒞.≈ lambdaΠ x F β
    lambda-eval : ∀ {x} {F} α → ≃-NatTrans (evalΠ F ∘ constFmor (lambdaΠ x F α)) α
    lambda-ext  : ∀ {x} {F} f → lambdaΠ x F (evalΠ F ∘ constFmor f) 𝒞.≈ f

  Π-map : ∀ {P Q : Functor 𝒟 𝒞} → NatTrans P Q → Π P 𝒞.⇒ Π Q
  Π-map {P} {Q} f = lambdaΠ (Π P) Q (f ∘ evalΠ P)

  lambdaΠ-natural : ∀ {P : Functor 𝒟 𝒞} {x y} →
                      (α : NatTrans (constF 𝒟 {𝒞} y) P) →
                      (h : x 𝒞.⇒ y) →
                      (lambdaΠ y P α 𝒞.∘ h) 𝒞.≈ lambdaΠ x P (α ∘ constFmor h)
  lambdaΠ-natural {P} {x} {y} α h =
    begin
      lambdaΠ y P α 𝒞.∘ h
    ≈⟨ 𝒞.≈-sym (lambda-ext _) ⟩
      lambdaΠ x P (evalΠ P ∘ constFmor (lambdaΠ y P α 𝒞.∘ h))
    ≈⟨ lambda-cong (∘NT-cong (≃-isEquivalence .refl {evalΠ P}) (const .Functor.fmor-comp _ _)) ⟩
      lambdaΠ x P (evalΠ P ∘ (constFmor (lambdaΠ y P α) ∘ constFmor h))
    ≈⟨ 𝒞.≈-sym (lambda-cong ([ 𝒟 ⇒ 𝒞 ] .Category.assoc (evalΠ P) (constFmor (lambdaΠ y P α)) (constFmor h))) ⟩
      lambdaΠ x P ((evalΠ P ∘ constFmor (lambdaΠ y P α)) ∘ constFmor h)
    ≈⟨ lambda-cong (∘NT-cong (lambda-eval α) (≃-isEquivalence .refl {constFmor h})) ⟩
      lambdaΠ x P (α ∘ constFmor h)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  Π-map-cong : ∀ {P Q : Functor 𝒟 𝒞}
                 {α₁ α₂ : NatTrans P Q} → ≃-NatTrans α₁ α₂ → Π-map α₁ 𝒞.≈ Π-map α₂
  Π-map-cong {P} α₁≃α₂ =
    lambda-cong (∘NT-cong α₁≃α₂ (≃-isEquivalence .refl {evalΠ P}))

  Π-map-id : ∀ {P : Functor 𝒟 𝒞} → Π-map (id P) 𝒞.≈ 𝒞.id (Π P)
  Π-map-id {P} =
    begin
      lambdaΠ (Π P) P (id P ∘ evalΠ P)
    ≈⟨ lambda-cong (𝒟𝒞.id-swap {f = evalΠ P}) ⟩
      lambdaΠ (Π P) P (evalΠ P ∘ id _)
    ≈⟨ lambda-cong (∘NT-cong (𝒟𝒞.≈-refl {f = evalΠ P})
                             (≃-isEquivalence .sym (const .Functor.fmor-id))) ⟩
      lambdaΠ (Π P) P (evalΠ P ∘ constFmor (𝒞.id _))
    ≈⟨ lambda-ext _ ⟩
      𝒞.id (Π P)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
          module 𝒟𝒞 = Category [ 𝒟 ⇒ 𝒞 ]

  Π-map-comp : ∀ {P Q R : Functor 𝒟 𝒞} (α : NatTrans Q R) (β : NatTrans P Q) →
               Π-map (α ∘ β) 𝒞.≈ (Π-map α 𝒞.∘ Π-map β)
  Π-map-comp {P} {Q} {R} α β =
    begin
      lambdaΠ (Π P) R ((α ∘ β) ∘ evalΠ P)
    ≈⟨ lambda-cong (NT-assoc _ _ _) ⟩
      lambdaΠ (Π P) R (α ∘ (β ∘ evalΠ P))
    ≈⟨ 𝒞.≈-sym (lambda-cong (∘NT-cong (≃-isEquivalence .refl) (lambda-eval _))) ⟩
      lambdaΠ (Π P) R (α ∘ (evalΠ Q ∘ constFmor (lambdaΠ _ _ (β ∘ evalΠ P))))
    ≈⟨ 𝒞.≈-sym (lambda-cong (NT-assoc _ _ _)) ⟩
      lambdaΠ (Π P) R ((α ∘ evalΠ Q) ∘ constFmor (lambdaΠ _ _ (β ∘ evalΠ P)))
    ≈⟨ 𝒞.≈-sym (lambdaΠ-natural _ _) ⟩
      lambdaΠ _ _ (α ∘ evalΠ Q) 𝒞.∘ lambdaΠ _ _ (β ∘ evalΠ P)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
