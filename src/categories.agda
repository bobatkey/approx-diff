{-# OPTIONS --prop --postfix-projections --safe #-}

module categories where

open import Level
open import Data.Product using (_,_)
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; module ≈-Reasoning; ⊗-setoid)
  renaming (_⇒_ to _⇒s_)
open IsEquivalence

-- Definition of category, and some basic structure one might want to
-- have.

record Category o m e : Set (suc (o ⊔ m ⊔ e)) where
  no-eta-equality
  field
    obj  : Set o
    _⇒_ : obj → obj → Set m
    _≈_  : ∀ {x y} → x ⇒ y → x ⇒ y → Prop e

    isEquiv : ∀ {x y} → IsEquivalence (_≈_ {x} {y})

    id  : ∀ x → x ⇒ x
    _∘_ : ∀ {x y z} → y ⇒ z → x ⇒ y → x ⇒ z

    ∘-cong : ∀ {x y z} {f₁ f₂ : y ⇒ z} {g₁ g₂ : x ⇒ y} →
      f₁ ≈ f₂ → g₁ ≈ g₂ → (f₁ ∘ g₁) ≈ (f₂ ∘ g₂)

    id-left  : ∀ {x y} {f : x ⇒ y} → (id y ∘ f) ≈ f
    id-right : ∀ {x y} {f : x ⇒ y} → (f ∘ id x) ≈ f
    assoc    : ∀ {w x y z} (f : y ⇒ z) (g : x ⇒ y) (h : w ⇒ x) →
      ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))

  ≈-refl : ∀ {x y} {f : x ⇒ y} → f ≈ f
  ≈-refl = isEquiv .refl

  ≈-sym : ∀ {x y} {f g : x ⇒ y} → f ≈ g → g ≈ f
  ≈-sym = isEquiv .sym

  id-swap : ∀ {x y}{f : x ⇒ y} → (id y ∘ f) ≈ (f ∘ id x)
  id-swap = isEquiv .trans id-left (≈-sym id-right)

  id-swap' : ∀ {x y}{f : x ⇒ y} → (f ∘ id x) ≈ (id y ∘ f)
  id-swap' = isEquiv .trans id-right (≈-sym id-left)

  open Setoid renaming (_≈_ to _≃_)

  hom-setoid : obj → obj → Setoid m e
  hom-setoid x y .Carrier = x ⇒ y
  hom-setoid x y ._≃_ = _≈_
  hom-setoid x y .isEquivalence = isEquiv

  hom-setoid-l : ∀ ℓ₁ ℓ₂ → obj → obj → Setoid (ℓ₁ ⊔ m) (ℓ₂ ⊔ e)
  hom-setoid-l ℓ₁ _ x y .Carrier = Lift ℓ₁ (x ⇒ y)
  hom-setoid-l _ ℓ₂ x y ._≃_ (lift f) (lift g) = LiftP ℓ₂ (f ≈ g)
  hom-setoid-l _ _ x y .isEquivalence .refl = lift (isEquiv .refl)
  hom-setoid-l _ _ x y .isEquivalence .sym (lift e) = lift (isEquiv .sym e)
  hom-setoid-l _ _ x y .isEquivalence .trans (lift p) (lift q) = lift (isEquiv .trans p q)

  -- comp : ∀ {x y z} → ⊗-setoid (hom-setoid y z) (hom-setoid x y) ⇒s hom-setoid x z
  -- comp ._⇒s_.func (f , g) = f ∘ g
  -- comp ._⇒s_.func-resp-≈ (f₁≈f₂ , g₁≈g₂) = ∘-cong f₁≈f₂ g₁≈g₂

module _ {o m e} (𝒞 : Category o m e) where

  open Category 𝒞

  record Iso (x y : obj) : Set (m ⊔ e) where
    field
      fwd : x ⇒ y
      bwd : y ⇒ x
      fwd∘bwd≈id : (fwd ∘ bwd) ≈ id y
      bwd∘fwd≈id : (bwd ∘ fwd) ≈ id x

  opposite : Category o m e
  opposite .Category.obj = obj
  opposite .Category._⇒_ x y = y ⇒ x
  opposite .Category._≈_ = _≈_
  opposite .Category.isEquiv = isEquiv
  opposite .Category.id = id
  opposite .Category._∘_ f g = g ∘ f
  opposite .Category.∘-cong e₁ e₂ = ∘-cong e₂ e₁
  opposite .Category.id-left = id-right
  opposite .Category.id-right = id-left
  opposite .Category.assoc f g h = ≈-sym (assoc h g f)

------------------------------------------------------------------------------
setoid→category : ∀ {o e} → Setoid o e → Category o e e
setoid→category A .Category.obj = A .Setoid.Carrier
setoid→category A .Category._⇒_ x y = Prf (A .Setoid._≈_ x y)
setoid→category A .Category._≈_ _ _ = ⊤
setoid→category A .Category.isEquiv = prop-setoid.⊤-isEquivalence
setoid→category A .Category.id x = ⟪ A .Setoid.refl ⟫
setoid→category A .Category._∘_ ⟪ f ⟫ ⟪ g ⟫ = ⟪ A .Setoid.trans g f ⟫
setoid→category A .Category.∘-cong _ _ = tt
setoid→category A .Category.id-left = tt
setoid→category A .Category.id-right = tt
setoid→category A .Category.assoc _ _ _ = tt


------------------------------------------------------------------------------
-- Terminal objects
record IsTerminal {o m e} (𝒞 : Category o m e) (t : Category.obj 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    to-terminal     : ∀ {x} → x ⇒ t
    to-terminal-ext : ∀ {x} (f : x ⇒ t) → to-terminal ≈ f

record HasTerminal {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    witness         : obj
    terminal-mor    : (x : obj) → x ⇒ witness
    terminal-unique : (x : obj) → (f g : x ⇒ witness) → f ≈ g

  isTerminal : IsTerminal 𝒞 witness
  isTerminal .IsTerminal.to-terminal = terminal-mor _
  isTerminal .IsTerminal.to-terminal-ext f = terminal-unique _ _ f

------------------------------------------------------------------------------
-- Coproducts
record HasCoproducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {x y z} → x ⇒ z → y ⇒ z → coprod x y ⇒ z

    copair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ z} {g₁ g₂ : y ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → copair f₁ g₁ ≈ copair f₂ g₂
    copair-in₁ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₁) ≈ f
    copair-in₂ : ∀ {x y z} (f : x ⇒ z) (g : y ⇒ z) → (copair f g ∘ in₂) ≈ g
    copair-ext : ∀ {x y z} (f : coprod x y ⇒ z) → copair (f ∘ in₁) (f ∘ in₂) ≈ f

  copair-natural : ∀ {w x y z} (h : z ⇒ w) (f : x ⇒ z) (g : y ⇒ z) → (h ∘ copair f g) ≈ copair (h ∘ f) (h ∘ g)
  copair-natural h f g =
    begin
      h ∘ copair f g
    ≈˘⟨ copair-ext _ ⟩
      copair ((h ∘ copair f g) ∘ in₁) ((h ∘ copair f g) ∘ in₂)
    ≈⟨ copair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      copair (h ∘ (copair f g ∘ in₁)) (h ∘ (copair f g ∘ in₂))
    ≈⟨ copair-cong (∘-cong ≈-refl (copair-in₁ f g)) (∘-cong ≈-refl (copair-in₂ f g)) ⟩
      copair (h ∘ f) (h ∘ g)
    ∎
    where open ≈-Reasoning isEquiv

module _ {o m e} (𝒞 : Category o m e) where

  open Category 𝒞

  record IsProduct (x : obj) (y : obj) (p : obj) (p₁ : p ⇒ x) (p₂ : p ⇒ y) : Set (o ⊔ m ⊔ e) where
    field
      pair : ∀ {z} → z ⇒ x → z ⇒ y → z ⇒ p
      pair-cong : ∀ {z} {f₁ f₂ : z ⇒ x} {g₁ g₂ : z ⇒ y} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
      pair-p₁ : ∀ {z} (f : z ⇒ x) (g : z ⇒ y) → (p₁ ∘ pair f g) ≈ f
      pair-p₂ : ∀ {z} (f : z ⇒ x) (g : z ⇒ y) → (p₂ ∘ pair f g) ≈ g
      pair-ext : ∀ {z} (f : z ⇒ p) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

    pair-natural : ∀ {w z} (h : w ⇒ z) (f : z ⇒ x) (g : z ⇒ y) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
    pair-natural h f g =
      begin
       pair f g ∘ h
      ≈⟨ ≈-sym (pair-ext _) ⟩
        pair (p₁ ∘ (pair f g ∘ h)) (p₂ ∘ (pair f g ∘ h))
      ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
        pair ((p₁ ∘ pair f g) ∘ h) ((p₂ ∘ pair f g) ∘ h)
      ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
        pair (f ∘ h) (g ∘ h)
      ∎
      where open ≈-Reasoning isEquiv

    pair-ext0 : pair p₁ p₂ ≈ id p
    pair-ext0 = begin pair p₁ p₂
                        ≈⟨ ≈-sym (pair-cong id-right id-right) ⟩
                      pair (p₁ ∘ id _) (p₂ ∘ id _)
                        ≈⟨ pair-ext (id _) ⟩
                      id _ ∎
      where open ≈-Reasoning isEquiv

  record Product (x : obj) (y : obj) : Set (o ⊔ m ⊔ e) where
    field
      prod : obj
      p₁   : prod ⇒ x
      p₂   : prod ⇒ y
      isProduct : IsProduct x y prod p₁ p₂
    open IsProduct isProduct public

  -- FIXME: extend this to all limits and colimits, and include the (co)cones.
  product-iso : ∀ {x y} (P₁ P₂ : Product x y) → Iso 𝒞 (Product.prod P₁) (Product.prod P₂)
  product-iso P₁ P₂ .Iso.fwd = Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)
  product-iso P₁ P₂ .Iso.bwd = Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)
  product-iso P₁ P₂ .Iso.fwd∘bwd≈id =
    begin
      Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁) ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)
    ≈⟨ Product.pair-natural P₂ _ _ _ ⟩
      Product.pair P₂ (Product.p₁ P₁ ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂)) (Product.p₂ P₁ ∘ Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂))
    ≈⟨ Product.pair-cong P₂ (Product.pair-p₁ P₁ _ _) (Product.pair-p₂ P₁ _ _) ⟩
      Product.pair P₂ (Product.p₁ P₂) (Product.p₂ P₂)
    ≈⟨ Product.pair-ext0 P₂ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv
  product-iso P₁ P₂ .Iso.bwd∘fwd≈id =
    begin
      Product.pair P₁ (Product.p₁ P₂) (Product.p₂ P₂) ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)
    ≈⟨ Product.pair-natural P₁ _ _ _ ⟩
      Product.pair P₁ (Product.p₁ P₂ ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁)) (Product.p₂ P₂ ∘ Product.pair P₂ (Product.p₁ P₁) (Product.p₂ P₁))
    ≈⟨ Product.pair-cong P₁ (Product.pair-p₁ P₂ _ _) (Product.pair-p₂ P₂ _ _) ⟩
      Product.pair P₁ (Product.p₁ P₁) (Product.p₂ P₁)
    ≈⟨ Product.pair-ext0 P₁ ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

record HasProducts {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    prod : obj → obj → obj
    p₁   : ∀ {x y} → prod x y ⇒ x
    p₂   : ∀ {x y} → prod x y ⇒ y
    pair : ∀ {x y z} → x ⇒ y → x ⇒ z → x ⇒ prod y z

    pair-cong : ∀ {x y z} {f₁ f₂ : x ⇒ y} {g₁ g₂ : x ⇒ z} → f₁ ≈ f₂ → g₁ ≈ g₂ → pair f₁ g₁ ≈ pair f₂ g₂
    pair-p₁ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₁ ∘ pair f g) ≈ f
    pair-p₂ : ∀ {x y z} (f : x ⇒ y) (g : x ⇒ z) → (p₂ ∘ pair f g) ≈ g
    pair-ext : ∀ {x y z} (f : x ⇒ prod y z) → pair (p₁ ∘ f) (p₂ ∘ f) ≈ f

  pair-natural : ∀ {w x y z} (h : w ⇒ x) (f : x ⇒ y) (g : x ⇒ z) → (pair f g ∘ h) ≈ pair (f ∘ h) (g ∘ h)
  pair-natural h f g =
    begin
      pair f g ∘ h
    ≈⟨ ≈-sym (pair-ext _) ⟩
      pair (p₁ ∘ (pair f g ∘ h)) (p₂ ∘ (pair f g ∘ h))
    ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((p₁ ∘ pair f g) ∘ h) ((p₂ ∘ pair f g) ∘ h)
    ≈⟨ pair-cong (∘-cong (pair-p₁ _ _) ≈-refl) (∘-cong (pair-p₂ _ _) ≈-refl) ⟩
      pair (f ∘ h) (g ∘ h)
    ∎
    where open ≈-Reasoning isEquiv

  pair-compose : ∀ {x y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x ⇒ y₁) (g₂ : x ⇒ y₂) →
    (pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair g₁ g₂) ≈ pair (f₁ ∘ g₁) (f₂ ∘ g₂)
  pair-compose f₁ f₂ g₁ g₂ =
    begin
      pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair g₁ g₂
    ≈⟨ pair-natural _ _ _ ⟩
      pair ((f₁ ∘ p₁) ∘ pair g₁ g₂) ((f₂ ∘ p₂) ∘ pair g₁ g₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (p₁ ∘ pair g₁ g₂)) (f₂ ∘ (p₂ ∘ pair g₁ g₂))
    ≈⟨ pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong ≈-refl (pair-p₂ _ _)) ⟩
      pair (f₁ ∘ g₁) (f₂ ∘ g₂)
    ∎ where open ≈-Reasoning isEquiv

  prod-m : ∀ {x₁ x₂ y₁ y₂} → x₁ ⇒ y₁ → x₂ ⇒ y₂ → prod x₁ x₂ ⇒ prod y₁ y₂
  prod-m f₁ f₂ = pair (f₁ ∘ p₁) (f₂ ∘ p₂)

  pair-functorial : ∀ {x₁ x₂ y₁ y₂ z₁ z₂} (f₁ : y₁ ⇒ z₁) (f₂ : y₂ ⇒ z₂) (g₁ : x₁ ⇒ y₁) (g₂ : x₂ ⇒ y₂) →
    prod-m (f₁ ∘ g₁) (f₂ ∘ g₂) ≈ (prod-m f₁ f₂ ∘ prod-m g₁ g₂)
  pair-functorial f₁ f₂ g₁ g₂ =
    begin
      pair ((f₁ ∘ g₁) ∘ p₁) ((f₂ ∘ g₂) ∘ p₂)
    ≈⟨ pair-cong (assoc _ _ _) (assoc _ _ _) ⟩
      pair (f₁ ∘ (g₁ ∘ p₁)) (f₂ ∘ (g₂ ∘ p₂))
    ≈⟨ ≈-sym (pair-cong (∘-cong ≈-refl (pair-p₁ _ _)) (∘-cong ≈-refl (pair-p₂ _ _))) ⟩
      pair (f₁ ∘ (p₁ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))) (f₂ ∘ (p₂ ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)))
    ≈⟨ ≈-sym (pair-cong (assoc _ _ _) (assoc _ _ _)) ⟩
      pair ((f₁ ∘ p₁) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)) ((f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂))
    ≈⟨ ≈-sym (pair-natural _ _ _) ⟩
      pair (f₁ ∘ p₁) (f₂ ∘ p₂) ∘ pair (g₁ ∘ p₁) (g₂ ∘ p₂)
    ∎
    where open ≈-Reasoning isEquiv

  prod-m-cong : ∀ {x₁ x₂ y₁ y₂} {f₁ f₂ : x₁ ⇒ y₁} {g₁ g₂ : x₂ ⇒ y₂} →
                f₁ ≈ f₂ → g₁ ≈ g₂ → prod-m f₁ g₁ ≈ prod-m f₂ g₂
  prod-m-cong f₁≈f₂ g₁≈g₂ =
    pair-cong (∘-cong f₁≈f₂ ≈-refl) (∘-cong g₁≈g₂ ≈-refl)

  pair-ext0 : ∀ {x y} → pair p₁ p₂ ≈ id (prod x y)
  pair-ext0 = begin pair p₁ p₂
                      ≈⟨ ≈-sym (pair-cong id-right id-right) ⟩
                    pair (p₁ ∘ id _) (p₂ ∘ id _)
                      ≈⟨ pair-ext (id _) ⟩
                    id _ ∎
    where open ≈-Reasoning isEquiv

  prod-m-id : ∀ {x y} → prod-m (id x) (id y) ≈ id (prod x y)
  prod-m-id =
    begin
      pair (id _ ∘ p₁) (id _ ∘ p₂)
    ≈⟨ pair-cong id-left id-left ⟩
      pair p₁ p₂
    ≈⟨ pair-ext0 ⟩
      id _
    ∎
    where open ≈-Reasoning isEquiv

  getProduct : ∀ (x y : obj) → Product 𝒞 x y
  getProduct x y .Product.prod = prod x y
  getProduct x y .Product.p₁ = p₁
  getProduct x y .Product.p₂ = p₂
  getProduct x y .Product.isProduct .IsProduct.pair = pair
  getProduct x y .Product.isProduct .IsProduct.pair-cong = pair-cong
  getProduct x y .Product.isProduct .IsProduct.pair-p₁ = pair-p₁
  getProduct x y .Product.isProduct .IsProduct.pair-p₂ = pair-p₂
  getProduct x y .Product.isProduct .IsProduct.pair-ext = pair-ext

record HasStrongCoproducts {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    coprod : obj → obj → obj
    in₁    : ∀ {x y} → x ⇒ coprod x y
    in₂    : ∀ {x y} → y ⇒ coprod x y
    copair : ∀ {w x y z} → prod w x ⇒ z → prod w y ⇒ z → prod w (coprod x y) ⇒ z
    -- FIXME: equations

record HasExponentials {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    exp    : obj → obj → obj
    eval   : ∀ {x y} → prod (exp x y) x ⇒ y
    lambda : ∀ {x y z} → prod x y ⇒ z → x ⇒ exp y z
  -- FIXME: equations

-- FIXME: separate out 'endofunctor' and 'natural transformation'
record Monad {o m e} (𝒞 : Category o m e) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  field
    M    : obj → obj
    map  : ∀ {x y} → x ⇒ y → M x ⇒ M y
    unit : ∀ {x} → x ⇒ M x
    join : ∀ {x} → M (M x) ⇒ M x
    map-cong : ∀ {x y}{f g : x ⇒ y} → f ≈ g → map f ≈ map g
    map-id   : ∀ {x} → map (id x) ≈ id (M x)
    map-comp : ∀ {x y z} (f : y ⇒ z) (g : x ⇒ y) → map (f ∘ g) ≈ (map f ∘ map g)
    unit-natural : ∀ {x y} (f : x ⇒ y) → (unit ∘ f) ≈ (map f ∘ unit)
    join-natural : ∀ {x y} (f : x ⇒ y) → (join ∘ map (map f)) ≈ (map f ∘ join)
    -- FIXME: actual monad equations




record StrongMonad {o m e} (𝒞 : Category o m e) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasProducts P
  field
    M      : obj → obj
    unit   : ∀ {x} → x ⇒ M x
    extend : ∀ {x y z} → prod x y ⇒ M z → prod x (M y) ⇒ M z
  -- FIXME: equations

record HasBooleans {o m e} (𝒞 : Category o m e) (T : HasTerminal 𝒞) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  field
    Bool : obj
    True False : terminal ⇒ Bool
    cond : ∀ {x y} → x ⇒ y → x ⇒ y → prod x Bool ⇒ y
  -- FIXME: equations

-- strong coproducts to booleans
module _ {o m e} {𝒞 : Category o m e} (T : HasTerminal 𝒞) {P : HasProducts 𝒞} (C : HasStrongCoproducts 𝒞 P) where

  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  open HasStrongCoproducts C
  open HasBooleans

  coproducts→booleans : HasBooleans 𝒞 T P
  coproducts→booleans .Bool = coprod terminal terminal
  coproducts→booleans .True = in₁
  coproducts→booleans .False = in₂
  coproducts→booleans .cond f g = copair (f ∘ p₁) (g ∘ p₁)

------------------------------------------------------------------------------
-- For every object, there is a list object
record HasLists {o m e} (𝒞 : Category o m e) (T : HasTerminal 𝒞) (P : HasProducts 𝒞) : Set (o ⊔ m ⊔ e) where
  open Category 𝒞
  open HasTerminal T renaming (witness to terminal)
  open HasProducts P
  field
    list : obj → obj
    nil  : ∀ {x} → terminal ⇒ list x
    cons : ∀ {x} → prod x (list x) ⇒ list x
    fold : ∀ {x y z} →
           x ⇒ z →
           prod (prod x y) z ⇒ z →
           prod x (list y) ⇒ z
  -- FIXME: equations
