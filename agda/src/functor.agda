{-# OPTIONS --prop --postfix-projections --safe #-}

module functor where

open import Level using (_⊔_)
open import prop using (tt; ⟪_⟫) -- only needed for setoid-functor
open import categories using (Category; setoid→category)
open import prop-setoid using (Setoid; IsEquivalence; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_)

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

module _ {o₁ e₁ o₂ e₂} {X : Setoid o₁ e₁} {Y : Setoid o₂ e₂} where

  setoid-functor : X ⇒s Y → Functor (setoid→category X) (setoid→category Y)
  setoid-functor f .Functor.fobj = f ._⇒s_.func
  setoid-functor f .Functor.fmor ⟪ prf ⟫ = ⟪ f ._⇒s_.func-resp-≈ prf ⟫
  setoid-functor f .Functor.fmor-cong _ = tt
  setoid-functor f .Functor.fmor-id = tt
  setoid-functor f .Functor.fmor-comp _ _ = tt

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor
  open 𝒞.Iso

  functor-preserve-iso : (F : Functor 𝒞 𝒟) → ∀ {x y} → 𝒞.Iso x y → 𝒟.Iso (F .fobj x) (F .fobj y)
  functor-preserve-iso F iso .Category.Iso.fwd = F .fmor (iso .fwd)
  functor-preserve-iso F iso .Category.Iso.bwd = F .fmor (iso .bwd)
  functor-preserve-iso F iso .Category.Iso.fwd∘bwd≈id = begin
      F .fmor (iso .fwd) 𝒟.∘ F .fmor (iso .bwd)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (iso .fwd 𝒞.∘ iso .bwd)
    ≈⟨ F .fmor-cong (iso .fwd∘bwd≈id) ⟩
      F .fmor (𝒞.id _)
    ≈⟨ F .fmor-id ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  functor-preserve-iso F iso .Category.Iso.bwd∘fwd≈id = begin
      F .fmor (iso .bwd) 𝒟.∘ F .fmor (iso .fwd)
    ≈˘⟨ F .fmor-comp _ _ ⟩
      F .fmor (iso .bwd 𝒞.∘ iso .fwd)
    ≈⟨ F .fmor-cong (iso .bwd∘fwd≈id) ⟩
      F .fmor (𝒞.id _)
    ≈⟨ F .fmor-id ⟩
      𝒟.id _
    ∎
    where open ≈-Reasoning 𝒟.isEquiv

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

  module _ {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

    private
      module 𝒞 = Category 𝒞
      module 𝒟 = Category 𝒟

    open Functor

    opF : Functor 𝒞 𝒟 → Functor 𝒞.opposite 𝒟.opposite
    opF F .fobj = F .fobj
    opF F .fmor = F .fmor
    opF F .fmor-cong = F .fmor-cong
    opF F .fmor-id = F .fmor-id
    opF F .fmor-comp f g = F .fmor-comp g f

    opF' : Functor 𝒞 𝒟.opposite → Functor 𝒞.opposite 𝒟
    opF' F .fobj = F .fobj
    opF' F .fmor = F .fmor
    opF' F .fmor-cong = F .fmor-cong
    opF' F .fmor-id = F .fmor-id
    opF' F .fmor-comp f g = F .fmor-comp g f

-- Functors form a category
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : Category o₁ m₁ e₁} {𝒟 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
  open Functor

  record NatTrans (F G : Functor 𝒞 𝒟) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      transf : ∀ x → F .fobj x 𝒟.⇒ G .fobj x
      natural : ∀ {x y} (f : x 𝒞.⇒ y) →
        (G .fmor f 𝒟.∘ transf x) 𝒟.≈ (transf y 𝒟.∘ F .fmor f)

  record NatIso (F G : Functor 𝒞 𝒟) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    open NatTrans
    open Category.IsIso
    field
      transform  : NatTrans F G
      transf-iso : ∀ x → Category.IsIso 𝒟 (transform .transf x)

    transform⁻¹ : NatTrans G F
    transform⁻¹ .transf x = transf-iso x .inverse
    transform⁻¹ .natural {x} {y} f = begin
        F .fmor f 𝒟.∘ transf-iso x .inverse
      ≈˘⟨ 𝒟.∘-cong 𝒟.id-left 𝒟.≈-refl ⟩
        (𝒟.id _ 𝒟.∘ F .fmor f) 𝒟.∘ transf-iso x .inverse
      ≈˘⟨ 𝒟.∘-cong (𝒟.∘-cong (transf-iso y .inverse∘f≈id) 𝒟.≈-refl) 𝒟.≈-refl ⟩
        ((transf-iso y .inverse 𝒟.∘ transform .transf y) 𝒟.∘ F .fmor f) 𝒟.∘ transf-iso x .inverse
      ≈⟨ 𝒟.∘-cong (𝒟.assoc _ _ _) 𝒟.≈-refl ⟩
        (transf-iso y .inverse 𝒟.∘ (transform .transf y 𝒟.∘ F .fmor f)) 𝒟.∘ transf-iso x .inverse
      ≈⟨ 𝒟.assoc _ _ _ ⟩
        transf-iso y .inverse 𝒟.∘ ((transform .transf y 𝒟.∘ F .fmor f) 𝒟.∘ transf-iso x .inverse)
      ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong (transform .natural f) 𝒟.≈-refl) ⟩
        transf-iso y .inverse 𝒟.∘ ((G .fmor f 𝒟.∘ transform .transf x) 𝒟.∘ transf-iso x .inverse)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.assoc _ _ _) ⟩
        transf-iso y .inverse 𝒟.∘ (G .fmor f 𝒟.∘ (transform .transf x 𝒟.∘ transf-iso x .inverse))
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl (𝒟.∘-cong 𝒟.≈-refl (transf-iso x .f∘inverse≈id)) ⟩
        transf-iso y .inverse 𝒟.∘ (G .fmor f 𝒟.∘ 𝒟.id _)
      ≈⟨ 𝒟.∘-cong 𝒟.≈-refl 𝒟.id-right ⟩
        transf-iso y .inverse 𝒟.∘ G .fmor f
      ∎
      where open ≈-Reasoning 𝒟.isEquiv

  open NatTrans

  record ≃-NatTrans {F G : Functor 𝒞 𝒟} (α β : NatTrans F G) : Prop (o₁ ⊔ e₂) where
    no-eta-equality
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

  NT-id-right : ∀ {F G}{α : NatTrans F G} → ≃-NatTrans (α ∘ id _) α
  NT-id-right .transf-eq x = 𝒟.id-right

  constFmor : ∀ {x} {y} → (x 𝒟.⇒ y) → NatTrans (constF 𝒞 x) (constF 𝒞 y)
  constFmor f .transf _ = f
  constFmor f .natural _ = 𝒟.id-swap

-- Category of functors
[_⇒_] : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} →
         Category o₁ m₁ e₁ →
         Category o₂ m₂ e₂ →
         Category (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) (o₁ ⊔ e₂)
[ 𝒞 ⇒ 𝒟 ] .Category.obj = Functor 𝒞 𝒟
[ 𝒞 ⇒ 𝒟 ] .Category._⇒_ = NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category._≈_ = ≃-NatTrans
[ 𝒞 ⇒ 𝒟 ] .Category.isEquiv = ≃-isEquivalence
[ 𝒞 ⇒ 𝒟 ] .Category.id = id
[ 𝒞 ⇒ 𝒟 ] .Category._∘_ = _∘_
[ 𝒞 ⇒ 𝒟 ] .Category.∘-cong = ∘NT-cong
[ 𝒞 ⇒ 𝒟 ] .Category.id-left = NT-id-left
[ 𝒞 ⇒ 𝒟 ] .Category.id-right = NT-id-right
[ 𝒞 ⇒ 𝒟 ] .Category.assoc = NT-assoc

------------------------------------------------------------------------------
module _ {o₁ m₁ e₁}
         {𝒞 : Category o₁ m₁ e₁}
    where

  private
    module 𝒞 = Category 𝒞

  open Functor

  Id : Functor 𝒞 𝒞
  Id .fobj x = x
  Id .fmor f = f
  Id .fmor-cong eq = eq
  Id .fmor-id = 𝒞.≈-refl
  Id .fmor-comp f g = 𝒞.≈-refl

module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         {ℰ : Category o₃ m₃ e₃}
    where

  private
    module ℰ = Category ℰ

  open Functor
  open NatTrans

  _∘F_ : Functor 𝒟 ℰ → Functor 𝒞 𝒟 → Functor 𝒞 ℰ
  (F ∘F G) .fobj x = F .fobj (G .fobj x)
  (F ∘F G) .fmor f = F .fmor (G .fmor f)
  (F ∘F G) .fmor-cong f₁≈f₂ = F .fmor-cong (G .fmor-cong f₁≈f₂)
  (F ∘F G) .fmor-id = ℰ.isEquiv .trans (F .fmor-cong (G .fmor-id)) (F .fmor-id)
  (F ∘F G) .fmor-comp f g =
    ℰ.isEquiv .trans (F .fmor-cong (G .fmor-comp _ _)) (F .fmor-comp _ _)

  -- FIXME: this is an isomorphism
  constF-F : ∀ (F : Functor 𝒟 ℰ) x →
             NatTrans (constF 𝒞 (F .fobj x)) (F ∘F constF 𝒞 x)
  constF-F F x .transf _ = ℰ.id _
  constF-F F x .natural f = ℰ.∘-cong (F .fmor-id) ℰ.≈-refl

-- FIXME: associativity and unit for functor composition
module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ o₄ m₄ e₄}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
         {ℰ : Category o₃ m₃ e₃}
         {ℱ : Category o₄ m₄ e₄}
         where

  open Functor
  open NatTrans

  private
    module ℱ = Category ℱ

  F-assoc : ∀ {F : Functor ℰ ℱ} {G : Functor 𝒟 ℰ} {H : Functor 𝒞 𝒟} →
            NatTrans ((F ∘F G) ∘F H) (F ∘F (G ∘F H))
  F-assoc .transf x = ℱ.id _
  F-assoc .natural f = ℱ.id-swap'

  F-assoc⁻¹ : ∀ {F : Functor ℰ ℱ} {G : Functor 𝒟 ℰ} {H : Functor 𝒞 𝒟} →
              NatTrans (F ∘F (G ∘F H)) ((F ∘F G) ∘F H)
  F-assoc⁻¹ .transf x = ℱ.id _
  F-assoc⁻¹ .natural f = ℱ.id-swap'


  -- and back again... and it is natural, and some coherence bits

-- Unitors
module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
  where

  open Functor
  open NatTrans

  private
    module 𝒟 = Category 𝒟

  right-unit⁻¹ : ∀ (F : Functor 𝒞 𝒟) → NatTrans F (F ∘F Id)
  right-unit⁻¹ F .transf x = 𝒟.id _
  right-unit⁻¹ F .natural f = 𝒟.id-swap'

  right-unit : ∀ (F : Functor 𝒞 𝒟) → NatTrans (F ∘F Id) F
  right-unit F .transf x = 𝒟.id _
  right-unit F .natural f = 𝒟.id-swap'

  left-unit⁻¹ : ∀ (F : Functor 𝒞 𝒟) → NatTrans F (Id ∘F F)
  left-unit⁻¹ F .transf x = 𝒟.id _
  left-unit⁻¹ F .natural f = 𝒟.id-swap'

  left-unit : ∀ (F : Functor 𝒞 𝒟) → NatTrans (Id ∘F F) F
  left-unit F .transf x = 𝒟.id _
  left-unit F .natural f = 𝒟.id-swap'

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

open ≃-NatTrans

const : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} →
          {𝒞 : Category o₁ m₁ e₁} →
          {𝒟 : Category o₂ m₂ e₂} →
          Functor 𝒟 [ 𝒞 ⇒ 𝒟 ]
const .Functor.fobj x = constF _ x
const .Functor.fmor f = constFmor f
const .Functor.fmor-cong eq .transf-eq x = eq
const {𝒟 = 𝒟} .Functor.fmor-id .transf-eq x = Category.≈-refl 𝒟
const {𝒟 = 𝒟} .Functor.fmor-comp f g .transf-eq x = Category.≈-refl 𝒟

------------------------------------------------------------------------------
-- Definition of Colimits and Limits
module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒮 : Category o₁ m₁ e₁} {𝒞 : Category o₂ m₂ e₂} where

  private
    module 𝒞 = Category 𝒞

  record IsColimit (D : Functor 𝒮 𝒞)
                   (apex : 𝒞.obj) (cocone : NatTrans D (constF 𝒮 apex))
           : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      colambda        : ∀ x → NatTrans D (constF _ x) → apex 𝒞.⇒ x
      colambda-cong   : ∀ {x α β} → ≃-NatTrans α β → colambda x α 𝒞.≈ colambda x β
      colambda-coeval : ∀ x α → ≃-NatTrans (constFmor (colambda x α) ∘ cocone) α
      colambda-ext    : ∀ x f → colambda x (constFmor f ∘ cocone) 𝒞.≈ f

  record Colimit (D : Functor 𝒮 𝒞) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      apex      : 𝒞.obj
      cocone    : NatTrans D (constF 𝒮 apex)
      isColimit : IsColimit D apex cocone
    open IsColimit isColimit public

  record IsLimit (D : Functor 𝒮 𝒞)
                 (apex : 𝒞.obj) (cone : NatTrans (constF 𝒮 apex) D)
           : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      lambda      : ∀ (x : 𝒞.obj) → NatTrans (constF _ x) D → x 𝒞.⇒ apex
      lambda-cong : ∀ {x α β} → ≃-NatTrans α β → lambda x α 𝒞.≈ lambda x β
      lambda-eval : ∀ {x} α → ≃-NatTrans (cone ∘ constFmor (lambda x α)) α
      lambda-ext  : ∀ {x} f → lambda x (cone ∘ constFmor f) 𝒞.≈ f

    lambda-natural : ∀ {x y} →
                       (α : NatTrans (constF 𝒮 {𝒞} y) D) →
                       (h : x 𝒞.⇒ y) →
                       (lambda y α 𝒞.∘ h) 𝒞.≈ lambda x (α ∘ constFmor h)
    lambda-natural {x} {y} α h =
      begin
        lambda y α 𝒞.∘ h
      ≈⟨ 𝒞.≈-sym (lambda-ext _) ⟩
        lambda x (cone ∘ constFmor (lambda y α 𝒞.∘ h))
      ≈⟨ lambda-cong (∘NT-cong (≃-isEquivalence .refl {cone}) (const .Functor.fmor-comp _ _)) ⟩
        lambda x (cone ∘ (constFmor (lambda y α) ∘ constFmor h))
      ≈⟨ 𝒞.≈-sym (lambda-cong ([ 𝒮 ⇒ 𝒞 ] .Category.assoc cone (constFmor (lambda y α)) (constFmor h))) ⟩
        lambda x ((cone ∘ constFmor (lambda y α)) ∘ constFmor h)
      ≈⟨ lambda-cong (∘NT-cong (lambda-eval α) (≃-isEquivalence .refl {constFmor h})) ⟩
        lambda x (α ∘ constFmor h)
      ∎ where open ≈-Reasoning 𝒞.isEquiv

  record Limit (D : Functor 𝒮 𝒞) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
    no-eta-equality
    field
      apex    : 𝒞.obj
      cone    : NatTrans (constF 𝒮 apex) D
      isLimit : IsLimit D apex cone
    open IsLimit isLimit public

-- Has all colimits of shape 𝒮
HasColimits : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒮 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
HasColimits 𝒮 𝒞 = (D : Functor 𝒮 𝒞) → Colimit D

-- Has all limits of shape 𝒮
HasLimits : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒮 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
HasLimits 𝒮 𝒞 = (D : Functor 𝒮 𝒞) → Limit D

------------------------------------------------------------------------------
-- If a category has all limits of shape 𝒮, then these can be
-- organised into a functor

module LimitFunctor {o₁ m₁ e₁ o₂ m₂ e₂}
                    {𝒮 : Category o₁ m₁ e₁}
                    {𝒞 : Category o₂ m₂ e₂}
                    (limits : HasLimits 𝒮 𝒞)
                    where

  private
    module 𝒞 = Category 𝒞

  open Functor
  open Limit
  open IsLimit

  Π : Functor [ 𝒮 ⇒ 𝒞 ] 𝒞
  Π .fobj D = limits D .apex
  Π .fmor {D} {E} α = EL.lambda DL.apex (α ∘ DL.cone)
    where module EL = Limit (limits E)
          module DL = Limit (limits D)
  Π .fmor-cong {D} {E} {α₁} {α₂} α₁≈α₂ =
    EL.lambda-cong (∘NT-cong α₁≈α₂ (≃-isEquivalence .refl))
    where module EL = Limit (limits E)
          module DL = Limit (limits D)
  Π .fmor-id {D} =
    begin
      DL.lambda DL.apex (id D ∘ DL.cone)
    ≈⟨ DL.lambda-cong (𝒮𝒞.id-swap {f = DL.cone}) ⟩
      DL.lambda DL.apex (DL.cone ∘ id _)
    ≈⟨ DL.lambda-cong (∘NT-cong (𝒮𝒞.≈-refl {f = DL.cone})
                               (≃-isEquivalence .sym (const .Functor.fmor-id))) ⟩
      DL.lambda DL.apex (DL.cone ∘ constFmor (𝒞.id _))
    ≈⟨ DL.lambda-ext _ ⟩
      𝒞.id DL.apex
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
          module 𝒮𝒞 = Category [ 𝒮 ⇒ 𝒞 ]
          module DL = Limit (limits D)
  Π .fmor-comp {D} {E} {F} α β =
    begin
      FL.lambda DL.apex ((α ∘ β) ∘ DL.cone)
    ≈⟨ FL.lambda-cong (NT-assoc _ _ _) ⟩
      FL.lambda DL.apex (α ∘ (β ∘ DL.cone))
    ≈˘⟨ FL.lambda-cong (∘NT-cong (≃-isEquivalence .refl) (EL.lambda-eval _)) ⟩
      FL.lambda DL.apex (α ∘ (EL.cone ∘ constFmor (EL.lambda _ (β ∘ DL.cone))))
    ≈˘⟨ FL.lambda-cong (NT-assoc _ _ _) ⟩
      FL.lambda DL.apex ((α ∘ EL.cone) ∘ constFmor (EL.lambda _ (β ∘ DL.cone)))
    ≈˘⟨ FL.lambda-natural _ _ ⟩
      FL.lambda _ (α ∘ EL.cone) 𝒞.∘ EL.lambda _ (β ∘ DL.cone)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
          module DL = Limit (limits D)
          module EL = Limit (limits E)
          module FL = Limit (limits F)

  -- This functor forms an adjunction with const

  open NatTrans

  unitΠ : NatTrans Id (Π ∘F const)
  unitΠ .transf x = limits (constF 𝒮 x) .isLimit .lambda x (id _)
  unitΠ .natural {x} {y} f =
    begin
      Ly.lambda _ (constFmor f ∘ Lx.cone) 𝒞.∘ Lx.lambda _ (id _)
    ≈⟨ Ly.lambda-natural _ _ ⟩
      Ly.lambda _ ((constFmor f ∘ Lx.cone) ∘ constFmor (Lx.lambda _ (id _)))
    ≈⟨ Ly.lambda-cong (NT-assoc _ _ _) ⟩
      Ly.lambda _ (constFmor f ∘ (Lx.cone ∘ constFmor (Lx.lambda _ (id _))))
    ≈⟨ Ly.lambda-cong (∘NT-cong (≃-isEquivalence .refl) (Lx.lambda-eval (id _))) ⟩
      Ly.lambda _ (constFmor f ∘ id _)
    ≈⟨ Ly.lambda-cong 𝒮𝒞.id-swap' ⟩
      Ly.lambda _ (id _ ∘ constFmor f)
    ≈˘⟨ Ly.lambda-natural (id _) f ⟩
      Ly.lambda _ (id _) 𝒞.∘ f
    ∎
    where module Ly = Limit (limits (constF 𝒮 y))
          module Lx = Limit (limits (constF 𝒮 x))
          module 𝒮𝒞 = Category [ 𝒮 ⇒ 𝒞 ]
          open ≈-Reasoning 𝒞.isEquiv

  counitΠ : NatTrans (const ∘F Π) Id
  counitΠ .transf D = limits D .cone
  counitΠ .natural {D} {E} α .transf-eq s =
    𝒞.≈-sym (limits E .lambda-eval (α ∘ limits D .cone) .transf-eq s)
{-
  triangle1 : ≃-NatTrans
                (left-unit _ ∘ ((counitΠ ∘H id const) ∘ (F-assoc⁻¹ ∘ ((id const ∘H unitΠ) ∘ right-unit⁻¹ _))))
                (id const)
  triangle1 .transf-eq x .transf-eq s = {!!}
-}
--   triangle2 : ≃-NatTrans

record HasLimits' {o₁ m₁ e₁ o₂ m₂ e₂} (𝒮 : Category o₁ m₁ e₁) (𝒞 : Category o₂ m₂ e₂)
             : Set (o₁ ⊔ e₁ ⊔ e₂ ⊔ m₁ ⊔ m₂ ⊔ o₂) where
  private
    module 𝒞 = Category 𝒞
  field
    Π : Functor 𝒮 𝒞 → 𝒞.obj
    lambdaΠ : ∀ (x : 𝒞.obj) F → NatTrans (constF _ x) F → (x 𝒞.⇒ Π F)
    evalΠ   : ∀ F → NatTrans (constF 𝒮 (Π F)) F

    lambda-cong : ∀ {x} {F : Functor 𝒮 𝒞} {α β : NatTrans (constF 𝒮 x) F} →
                  ≃-NatTrans α β → lambdaΠ x F α 𝒞.≈ lambdaΠ x F β
    lambda-eval : ∀ {x} {F} α → ≃-NatTrans (evalΠ F ∘ constFmor (lambdaΠ x F α)) α
    lambda-ext  : ∀ {x} {F} f → lambdaΠ x F (evalΠ F ∘ constFmor f) 𝒞.≈ f

  -- If 𝒞 has all limits of shape 𝒮, then there is a functor
  --    Π : Functor [ 𝒮 ⇒ 𝒞 ] 𝒞

  Π-map : ∀ {P Q : Functor 𝒮 𝒞} → NatTrans P Q → Π P 𝒞.⇒ Π Q
  Π-map {P} {Q} f = lambdaΠ (Π P) Q (f ∘ evalΠ P)

  lambdaΠ-natural : ∀ {P : Functor 𝒮 𝒞} {x y} →
                      (α : NatTrans (constF 𝒮 {𝒞} y) P) →
                      (h : x 𝒞.⇒ y) →
                      (lambdaΠ y P α 𝒞.∘ h) 𝒞.≈ lambdaΠ x P (α ∘ constFmor h)
  lambdaΠ-natural {P} {x} {y} α h =
    begin
      lambdaΠ y P α 𝒞.∘ h
    ≈⟨ 𝒞.≈-sym (lambda-ext _) ⟩
      lambdaΠ x P (evalΠ P ∘ constFmor (lambdaΠ y P α 𝒞.∘ h))
    ≈⟨ lambda-cong (∘NT-cong (≃-isEquivalence .refl {evalΠ P}) (const .Functor.fmor-comp _ _)) ⟩
      lambdaΠ x P (evalΠ P ∘ (constFmor (lambdaΠ y P α) ∘ constFmor h))
    ≈⟨ 𝒞.≈-sym (lambda-cong ([ 𝒮 ⇒ 𝒞 ] .Category.assoc (evalΠ P) (constFmor (lambdaΠ y P α)) (constFmor h))) ⟩
      lambdaΠ x P ((evalΠ P ∘ constFmor (lambdaΠ y P α)) ∘ constFmor h)
    ≈⟨ lambda-cong (∘NT-cong (lambda-eval α) (≃-isEquivalence .refl {constFmor h})) ⟩
      lambdaΠ x P (α ∘ constFmor h)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv

  Π-map-cong : ∀ {P Q : Functor 𝒮 𝒞}
                 {α₁ α₂ : NatTrans P Q} → ≃-NatTrans α₁ α₂ → Π-map α₁ 𝒞.≈ Π-map α₂
  Π-map-cong {P} α₁≃α₂ =
    lambda-cong (∘NT-cong α₁≃α₂ (≃-isEquivalence .refl {evalΠ P}))

  Π-map-id : ∀ {P : Functor 𝒮 𝒞} → Π-map (id P) 𝒞.≈ 𝒞.id (Π P)
  Π-map-id {P} =
    begin
      lambdaΠ (Π P) P (id P ∘ evalΠ P)
    ≈⟨ lambda-cong (𝒮𝒞.id-swap {f = evalΠ P}) ⟩
      lambdaΠ (Π P) P (evalΠ P ∘ id _)
    ≈⟨ lambda-cong (∘NT-cong (𝒮𝒞.≈-refl {f = evalΠ P})
                             (≃-isEquivalence .sym (const .Functor.fmor-id))) ⟩
      lambdaΠ (Π P) P (evalΠ P ∘ constFmor (𝒞.id _))
    ≈⟨ lambda-ext _ ⟩
      𝒞.id (Π P)
    ∎
    where open ≈-Reasoning 𝒞.isEquiv
          module 𝒮𝒞 = Category [ 𝒮 ⇒ 𝒞 ]

  Π-map-comp : ∀ {P Q R : Functor 𝒮 𝒞} (α : NatTrans Q R) (β : NatTrans P Q) →
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

limits→limits' : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒮 : Category o₁ m₁ e₁} {𝒞 : Category o₂ m₂ e₂} →
                   HasLimits 𝒮 𝒞 →
                   HasLimits' 𝒮 𝒞
limits→limits' hasLimits .HasLimits'.Π D = hasLimits D .Limit.apex
limits→limits' hasLimits .HasLimits'.lambdaΠ x D α = hasLimits D .Limit.isLimit .IsLimit.lambda x α
limits→limits' hasLimits .HasLimits'.evalΠ D = hasLimits D .Limit.cone
limits→limits' hasLimits .HasLimits'.lambda-cong {x} {D} = hasLimits D .Limit.isLimit .IsLimit.lambda-cong
limits→limits' hasLimits .HasLimits'.lambda-eval {x} {D} = hasLimits D .Limit.isLimit .IsLimit.lambda-eval
limits→limits' hasLimits .HasLimits'.lambda-ext {x} {D} = hasLimits D .Limit.isLimit .IsLimit.lambda-ext

limits'→limits : ∀ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒮 : Category o₁ m₁ e₁} {𝒞 : Category o₂ m₂ e₂} →
                   HasLimits' 𝒮 𝒞 →
                   HasLimits 𝒮 𝒞
limits'→limits hasLimits' D .Limit.apex = hasLimits' .HasLimits'.Π D
limits'→limits hasLimits' D .Limit.cone = hasLimits' .HasLimits'.evalΠ D
limits'→limits hasLimits' D .Limit.isLimit .IsLimit.lambda x = hasLimits' .HasLimits'.lambdaΠ x D
limits'→limits hasLimits' D .Limit.isLimit .IsLimit.lambda-cong = hasLimits' .HasLimits'.lambda-cong
limits'→limits hasLimits' D .Limit.isLimit .IsLimit.lambda-eval = hasLimits' .HasLimits'.lambda-eval
limits'→limits hasLimits' D .Limit.isLimit .IsLimit.lambda-ext f = hasLimits' .HasLimits'.lambda-ext f

------------------------------------------------------------------------------
-- Colimits are limits in the opposite category

module _ {o₁ m₁ e₁ o₂ m₂ e₂}
         {𝒮 : Category o₁ m₁ e₁}
         {𝒞 : Category o₂ m₂ e₂}
  where

  open NatTrans
  open ≃-NatTrans

  private
    module 𝒮 = Category 𝒮
    module 𝒞 = Category 𝒞

    switch : ∀ (D : Functor 𝒮 𝒞.opposite) {x} → NatTrans (opF' D) (constF 𝒮.opposite x) → NatTrans (constF 𝒮 x) D
    switch D α .transf = α .transf
    switch D α .natural f = 𝒞.≈-sym (α .natural f)

    switch⁻¹ : ∀ (D : Functor 𝒮 𝒞.opposite) {x} → NatTrans (constF 𝒮 x) D → NatTrans (opF' D) (constF 𝒮.opposite x)
    switch⁻¹ D α .transf = α .transf
    switch⁻¹ D α .natural f = 𝒞.≈-sym (α .natural f)

    switch⁻¹-cong : ∀ (D : Functor 𝒮 𝒞.opposite) {x} {α β} → ≃-NatTrans α β → ≃-NatTrans (switch⁻¹ D {x} α) (switch⁻¹ D {x} β)
    switch⁻¹-cong D α≃β .transf-eq = α≃β .transf-eq

    switch⁻¹-comp : ∀ D {x y α} {f : y 𝒞.⇒ x} → ≃-NatTrans (switch⁻¹ D {x} (α ∘ constFmor f)) (constFmor f ∘ switch⁻¹ D α)
    switch⁻¹-comp D .transf-eq s = 𝒞.≈-refl

    switch⁻¹-switch : ∀ D {x α} → ≃-NatTrans (switch⁻¹ D {x} (switch D α)) α
    switch⁻¹-switch D .transf-eq s = 𝒞.≈-refl

  op-colimit : (D : Functor 𝒮 𝒞.opposite) → Colimit (opF' D) → Limit D
  op-colimit D colimitOpD .Limit.apex = colimitOpD .Colimit.apex
  op-colimit D colimitOpD .Limit.cone = switch D (colimitOpD .Colimit.cocone)
  op-colimit D colimitOpD .Limit.isLimit .IsLimit.lambda x α =
    colimitOpD .Colimit.colambda x (switch⁻¹ D α)
  op-colimit D colimitOpD .Limit.isLimit .IsLimit.lambda-cong α≃β =
    colimitOpD .Colimit.colambda-cong (switch⁻¹-cong D α≃β)
  op-colimit D colimitOpD .Limit.isLimit .IsLimit.lambda-eval {x} α .transf-eq s =
    colimitOpD .Colimit.colambda-coeval x _ .transf-eq s
  op-colimit D colimitOpD .Limit.isLimit .IsLimit.lambda-ext {x} f = begin
      colimitOpD .Colimit.colambda x (switch⁻¹ D (switch D (colimitOpD .Colimit.cocone) ∘ constFmor f))
    ≈⟨ colimitOpD .Colimit.colambda-cong (switch⁻¹-comp D) ⟩
      colimitOpD .Colimit.colambda x (constFmor f ∘ switch⁻¹ D (switch D (colimitOpD .Colimit.cocone)))
    ≈⟨ colimitOpD .Colimit.colambda-cong (∘NT-cong (≃-isEquivalence .refl) (switch⁻¹-switch D)) ⟩
      colimitOpD .Colimit.colambda x (constFmor f ∘ colimitOpD .Colimit.cocone)
    ≈⟨ colimitOpD .Colimit.colambda-ext x f ⟩
      f
    ∎
    where open ≈-Reasoning 𝒞.isEquiv


------------------------------------------------------------------------------
-- Definition of limit preservation

module _ {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃}
         {𝒞 : Category o₁ m₁ e₁}
         {𝒟 : Category o₂ m₂ e₂}
  where

  private
    module 𝒞 = Category 𝒞
  open Functor

  preserve-limits-of-shape : (𝒮 : Category o₃ m₃ e₃) →
                             Functor 𝒞 𝒟 →
                             Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ o₃ ⊔ m₃ ⊔ e₃)
  preserve-limits-of-shape 𝒮 F =
    ∀ (D : Functor 𝒮 𝒞)
      (apex : 𝒞.obj)
      (cone : NatTrans (constF 𝒮 apex) D) →
    IsLimit D apex cone →
    IsLimit (F ∘F D) (F .fobj apex) ((id F ∘H cone) ∘ (constF-F F apex))
