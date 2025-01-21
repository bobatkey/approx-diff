{-# OPTIONS --postfix-projections #-}

module grothendieck where

open import Level
open import Relation.Binary using (Setoid; IsEquivalence)
open import setoid
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,_)

record Category o m e : Set (suc (o ⊔ m ⊔ e)) where
  field
    obj  : Set o
    _⇒_ : obj → obj → Set m
    _≈_  : ∀ {x y} → x ⇒ y → x ⇒ y → Set e

    isEquiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})

    id  : ∀ {x} → x ⇒ x
    _∘_ : ∀ {x y z} → y ⇒ z → x ⇒ y → x ⇒ z

    ∘-cong : ∀ {x y z} (f₁ f₂ : y ⇒ z) (g₁ g₂ : x ⇒ y) →
      f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ∘ g₁) ≈ (f₂ ∘ g₂)

    id-left  : ∀ {x y} {f : x ⇒ y} → (id ∘ f) ≈ f
    id-right : ∀ {x y} {f : x ⇒ y} → (f ∘ id) ≈ f
    assoc    : ∀ {w x y z} (f : y ⇒ z) (g : x ⇒ y) (h : w ⇒ x) →
      ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

  open Setoid renaming (_≈_ to _≃_)

  hom-setoid : obj → obj → Setoid m e
  hom-setoid x y .Carrier = x ⇒ y
  hom-setoid x y ._≃_ = _≈_
  hom-setoid x y .isEquivalence = isEquiv

record HasTerminal {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    witness         : obj
    terminal-mor    : (x : obj) → x ⇒ witness
    terminal-unique : (x : obj) → (f g : x ⇒ witness) → f ≈ g

-- FIXME: will want distributive coproducts too
record HasCoproducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {x y z} → x ⇒ z → y ⇒ z → coprod x y ⇒ z
    -- FIXME: equations

record HasProducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    prod : obj → obj → obj
    p₁   : ∀ {x y} → prod x y ⇒ x
    p₂   : ∀ {x y} → prod x y ⇒ y
    pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ prod y z
    -- FIXME: equations

record HasExponentials {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    products : HasProducts 𝒞
  open HasProducts products
  field
    exp    : obj → obj → obj
    eval   : ∀ {x y} → prod x (exp x y) ⇒ y
    lambda : ∀ {x y z} → prod x y ⇒ z → x ⇒ exp y z
  -- FIXME: equations

module Fam {o m e} {os es} (𝒞 : Category o m e) where

  record Obj : Set (o ⊔ m ⊔ e ⊔ suc os ⊔ suc es) where
    open Setoid
    open Category 𝒞 renaming (_≈_ to _≈C_)
    field
      idx : Setoid os es
      iobj : idx .Carrier → obj
      iobj-transport : ∀ {x y} → idx ._≈_ x y → iobj x ⇒ iobj y
      iobj-id : ∀ {x} → iobj-transport (idx .refl {x}) ≈C id {iobj x}
      iobj-trans : ∀ {x y z} (e₁ : idx ._≈_ y z) (e₂ : idx ._≈_ x y) →
        iobj-transport (idx .trans e₂ e₁) ≈C (iobj-transport e₁ ∘ iobj-transport e₂)
  open Obj

  record Mor (X Y : Obj) : Set (os ⊔ es ⊔ m ⊔ e) where
    open Setoid
    open Category 𝒞 renaming (_≈_ to _≈C_)
    field
      func    : X .idx .Carrier → Y .idx .Carrier
      func-≈  : ∀ {x₁ x₂} → X .idx ._≈_ x₁ x₂ → Y .idx ._≈_ (func x₁) (func x₂)
      ifunc   : (x : X .idx .Carrier) → X .iobj x ⇒ Y .iobj (func x)
      ifunc-≈ : ∀ {x₁ x₂} (e : X .idx ._≈_ x₁ x₂) →
        (ifunc x₂ ∘ X .iobj-transport e) ≈C (Y .iobj-transport (func-≈ e) ∘ ifunc x₁)
  open Mor

  module _ where

    Mor-id : ∀ {X} → Mor X X
    Mor-id .func x = x
    Mor-id .func-≈ e = e
    Mor-id .ifunc x = 𝒞 .Category.id
    Mor-id .ifunc-≈ e =
      -- FIXME: tidy
      𝒞 .Category.isEquiv .IsEquivalence.trans
        (𝒞 .Category.id-left) (𝒞 .Category.isEquiv .IsEquivalence.sym (𝒞 .Category.id-right))

  record _≃Mor_ {X Y : Obj} (f g : Mor X Y) : Set (os ⊔ es ⊔ e) where
    private
      module Xidx = Setoid (X .idx)
      module Yidx = Setoid (Y .idx)
    open Category 𝒞 renaming (_≈_ to _≈C_)
    field
      func-eq : ∀ {x₁ x₂} → x₁ Xidx.≈ x₂ → (f .func x₁) Yidx.≈ (g .func x₂)
      ifunc-eq : ∀ {x₁ x₂} (e : x₁ Xidx.≈ x₂) →
        (Y .iobj-transport (func-eq e) ∘ f .ifunc x₁) ≈C (g .ifunc x₂ ∘ X .iobj-transport e)
  open _≃Mor_

  module _ where
    open Category

    cat : Category (o ⊔ m ⊔ e ⊔ suc os ⊔ suc es) (os ⊔ es ⊔ m ⊔ e) (e ⊔ os ⊔ es)
    cat .obj = Obj
    cat ._⇒_ = Mor
    cat ._≈_ = _≃Mor_
    cat .isEquiv = {!!}
    cat .id = Mor-id
    cat ._∘_ = {!!}
    cat .∘-cong = {!!}
    cat .id-left = {!!}
    cat .id-right = {!!}
    cat .assoc = {!!}

  -- If 𝒞 has a terminal object, then so does the category of families
  module _ (T : HasTerminal 𝒞) where

    module T = HasTerminal T
    open Category 𝒞
    open HasTerminal
    open IsEquivalence

    hasTerminal : HasTerminal cat
    hasTerminal .witness .idx = ⊤-setoid
    hasTerminal .witness .iobj _ = T.witness
    hasTerminal .witness .iobj-transport _ = id
    hasTerminal .witness .iobj-id = isEquiv .refl
    hasTerminal .witness .iobj-trans _ _ =
      isEquiv .sym id-left
    hasTerminal .terminal-mor x .func _ = lift tt
    hasTerminal .terminal-mor x .func-≈ _ = lift tt
    hasTerminal .terminal-mor x .ifunc X = T .terminal-mor _
    hasTerminal .terminal-mor x .ifunc-≈ e = T .terminal-unique _ _ _ --
    hasTerminal .terminal-unique X f g .func-eq e = lift tt
    hasTerminal .terminal-unique X f g .ifunc-eq e =
      T .terminal-unique _ _ _

  -- This category always has coproducts
  module _ where

    open Category 𝒞
    open HasCoproducts
    open IsEquivalence

    hasCoproducts : HasCoproducts cat
    hasCoproducts .coprod X Y .idx = +-setoid (X .idx) (Y .idx)
    hasCoproducts .coprod X Y .iobj (inj₁ x) = X .iobj x
    hasCoproducts .coprod X Y .iobj (inj₂ y) = Y .iobj y
    hasCoproducts .coprod X Y .iobj-transport {inj₁ x} {inj₁ x₁} (lift e) = X .iobj-transport e
    hasCoproducts .coprod X Y .iobj-transport {inj₂ y₁} {inj₂ y} (lift e) = Y .iobj-transport e
    hasCoproducts .coprod X Y .iobj-id {inj₁ x} = X .iobj-id
    hasCoproducts .coprod X Y .iobj-id {inj₂ y} = Y .iobj-id
    hasCoproducts .coprod X Y .iobj-trans {inj₁ x} {inj₁ x₁} {inj₁ x₂} (lift e₁) (lift e₂) = X .iobj-trans e₁ e₂
    hasCoproducts .coprod X Y .iobj-trans {inj₂ y} {inj₂ y₁} {inj₂ y₂} (lift e₁) (lift e₂) = Y .iobj-trans e₁ e₂
    hasCoproducts .in₁ .func = inj₁
    hasCoproducts .in₁ .func-≈ = lift
    hasCoproducts .in₁ .ifunc x = id
    hasCoproducts .in₁ .ifunc-≈ e = isEquiv .trans id-left (isEquiv .sym id-right)
    hasCoproducts .in₂ .func = inj₂
    hasCoproducts .in₂ .func-≈ = lift
    hasCoproducts .in₂ .ifunc x = id
    hasCoproducts .in₂ .ifunc-≈ e = isEquiv .trans id-left (isEquiv .sym id-right)
    hasCoproducts .copair f g .func (inj₁ x) = f .func x
    hasCoproducts .copair f g .func (inj₂ y) = g .func y
    hasCoproducts .copair f g .func-≈ {inj₁ x} {inj₁ x₁} (lift e) = f .func-≈ e
    hasCoproducts .copair f g .func-≈ {inj₂ y} {inj₂ y₁} (lift e) = g .func-≈ e
    hasCoproducts .copair f g .ifunc (inj₁ x) = f .ifunc x
    hasCoproducts .copair f g .ifunc (inj₂ y) = g .ifunc y
    hasCoproducts .copair f g .ifunc-≈ {inj₁ x} {inj₁ x₁} (lift e) = f .ifunc-≈ e
    hasCoproducts .copair f g .ifunc-≈ {inj₂ y} {inj₂ y₁} (lift e) = g .ifunc-≈ e

  -- If 𝒞 has products, then so does this category
  module _ (P : HasProducts 𝒞) where

    open Category 𝒞
    open HasProducts
    open IsEquivalence
    private
      module P = HasProducts P

    products : HasProducts cat
    products .prod X Y .idx = ⊗-setoid (X .idx) (Y .idx)
    products .prod X Y .iobj (x , y) = P.prod (X .iobj x) (Y .iobj y)
    products .prod X Y .iobj-transport (e₁ , e₂) = P.pair (X .iobj-transport e₁ ∘ P.p₁) (Y .iobj-transport e₂ ∘ P.p₂)
    products .prod X Y .iobj-id = {!!}
    products .prod X Y .iobj-trans e₁ e₂ = {!!}
    products .p₁ .func = proj₁
    products .p₁ .func-≈ = proj₁
    products .p₁ .ifunc = {!!}
    products .p₁ .ifunc-≈ = {!!}
    products .p₂ = {!!}
    products .pair = {!!}

  -- If 𝒞 has Setoid-indexed products, then this category has exponentials
  module _ (P : HasProducts 𝒞) where

    open Category 𝒞
    open HasProducts
    open IsEquivalence
    open HasExponentials renaming (products to products')

    exponentials : HasExponentials cat
    exponentials .products' = products P
    exponentials .exp X Y .idx = {!hom-setoid X Y!}
    exponentials .exp X Y .iobj = {!!}
    exponentials .exp X Y .iobj-transport = {!!}
    exponentials .exp X Y .iobj-id = {!!}
    exponentials .exp X Y .iobj-trans = {!!}
    exponentials .eval = {!!}
    exponentials .lambda = {!!}


  -- If 𝒞 has a monad, then so does this category
