{-# OPTIONS --prop --postfix-projections #-}

open import Level
open import Data.Product using (_,_; proj₁; proj₂)
open import categories
open import prop
open import prop-setoid
  using (IsEquivalence; Setoid; 𝟙; +-setoid; idS; _∘S_; module ≈-Reasoning; ∘S-cong)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_; ≃m-isEquivalence to ≈s-isEquivalence)
open import setoid-cat

module presheaves {o m e} os es (𝒞 : Category o m e) where

record PreSheaf : Set (suc o ⊔ suc m ⊔ suc e ⊔ suc os ⊔ suc es) where
  open Category 𝒞
  field
    fobj      : obj → Setoid (o ⊔ m ⊔ e ⊔ os ⊔ es) (o ⊔ m ⊔ e ⊔ es ⊔ os)
    fmap      : ∀ {x y} → x ⇒ y → fobj y ⇒s fobj x
    fmap-cong : ∀ {x y} {f g : x ⇒ y} → f ≈ g → fmap f ≈s fmap g
    fmap-id   : ∀ x → fmap (id x) ≈s idS (fobj x)
    fmap-∘    : ∀ {x y z} (f : y ⇒ z) (g : x ⇒ y) → fmap (f ∘ g) ≈s (fmap g ∘S fmap f)

    -- glueing for finite sums:
    --
    -- sum         : ∀ {x y} → ⊗-setoid (fobj x) (fobj y) ⇒s fobj (coprod x y)
    -- sum-natural : ...
    -- sum-glue    : pair (fmap in₁) (fmap in₂) ∘ sum ≈ id

    -- zero : 𝟙 ⇒s fobj 𝟘

record _⇒p_ (F G : PreSheaf) : Set (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  open Category 𝒞
  private
    module F = PreSheaf F
    module G = PreSheaf G
  field
    transf  : ∀ x → F.fobj x ⇒s G.fobj x
    natural : ∀ {x y} (f : x ⇒ y) → (G.fmap f ∘S transf y) ≈s (transf x ∘S F.fmap f)

record _≈p_ {F G : PreSheaf} (α β : F ⇒p G) : Prop (o ⊔ m ⊔ e ⊔ os ⊔ es) where
  open _⇒p_
  field
    transf-eq : ∀ x → α .transf x ≈s β .transf x

open PreSheaf
open _⇒p_
open _≈p_
open IsEquivalence

≈p-isEquivalence : ∀ {F G} → IsEquivalence (_≈p_ {F} {G})
≈p-isEquivalence .refl .transf-eq x = ≈s-isEquivalence .refl
≈p-isEquivalence .sym α≈β .transf-eq x = ≈s-isEquivalence .sym (α≈β .transf-eq x)
≈p-isEquivalence .trans α≈β β≈γ .transf-eq x =
  ≈s-isEquivalence .trans (α≈β .transf-eq x) (β≈γ .transf-eq x)

idp : (F : PreSheaf) → F ⇒p F
idp F .transf x = idS _
idp F .natural f =
  begin
    F .fmap f ∘S idS _
  ≈⟨ prop-setoid.id-right ⟩
    F .fmap f
  ≈⟨ ≈s-isEquivalence .sym prop-setoid.id-left ⟩
    idS _ ∘S F .fmap f
  ∎ where open ≈-Reasoning ≈s-isEquivalence

_∘p_ : {F G H : PreSheaf} (f : G ⇒p H) (g : F ⇒p G) → F ⇒p H
(α ∘p β) .transf x = (α .transf x) ∘S (β .transf x)
_∘p_ {F}{G}{H} α β .natural {x} {y} f =
  begin
    fmap H f ∘S (α .transf y ∘S β .transf y)
  ≈⟨ ≈s-isEquivalence .sym (prop-setoid.assoc _ _ _) ⟩
    (fmap H f ∘S α .transf y) ∘S β .transf y
  ≈⟨ ∘S-cong (α .natural f) (≈s-isEquivalence .refl {β .transf y}) ⟩
    (α .transf x ∘S fmap G f) ∘S β .transf y
  ≈⟨ prop-setoid.assoc _ _ _ ⟩
    α .transf x ∘S (fmap G f ∘S β .transf y)
  ≈⟨ ∘S-cong (≈s-isEquivalence .refl) (β .natural f) ⟩
    α .transf x ∘S (β .transf x ∘S F .fmap f)
  ≈⟨ ≈s-isEquivalence .sym (prop-setoid.assoc _ _ _) ⟩
    (α .transf x ∘S β .transf x) ∘S F .fmap f
  ∎ where open ≈-Reasoning ≈s-isEquivalence

∘p-cong : ∀ {F G H} {f₁ f₂ : G ⇒p H} {g₁ g₂ : F ⇒p G} →
  f₁ ≈p f₂ → g₁ ≈p g₂ → (f₁ ∘p g₁) ≈p (f₂ ∘p g₂)
∘p-cong f₁≈f₂ g₁≈g₂ .transf-eq x = ∘S-cong (f₁≈f₂ .transf-eq x) (g₁≈g₂ .transf-eq x)

module _ where

  open Category

  cat : Category _ _ _
  cat .obj = PreSheaf
  cat ._⇒_ = _⇒p_
  cat ._≈_ = _≈p_
  cat .isEquiv = ≈p-isEquivalence
  cat .id = idp
  cat ._∘_ = _∘p_
  cat .∘-cong = ∘p-cong
  cat .id-left .transf-eq x = prop-setoid.id-left
  cat .id-right .transf-eq x = prop-setoid.id-right
  cat .assoc f g h .transf-eq x = prop-setoid.assoc _ _ _

module _ where

  open HasTerminal

  terminal : HasTerminal cat
  terminal .witness .fobj x = 𝟙
  terminal .witness .fmap f = idS 𝟙
  terminal .witness .fmap-cong x = ≈s-isEquivalence .refl
  terminal .witness .fmap-id x = ≈s-isEquivalence .refl
  terminal .witness .fmap-∘ f g = ≈s-isEquivalence .sym prop-setoid.id-left
  terminal .terminal-mor F .transf x = prop-setoid.to-𝟙
  terminal .terminal-mor F .natural f = prop-setoid.to-𝟙-unique _ _
  terminal .terminal-unique F α β .transf-eq x = prop-setoid.to-𝟙-unique _ _

module _ where

  open Category 𝒞
  open HasProducts

  module SP = HasProducts (Setoid-products (o ⊔ m ⊔ e ⊔ os ⊔ es) (o ⊔ m ⊔ e ⊔ es ⊔ os))

  _⊗_ : PreSheaf → PreSheaf → PreSheaf
  (F ⊗ G) .fobj x = SP.prod (F .fobj x) (G .fobj x)
  (F ⊗ G) .fmap f = SP.prod-m (F .fmap f) (G .fmap f)
  (F ⊗ G) .fmap-cong f≈g =
    SP.prod-m-cong (F .fmap-cong f≈g) (G .fmap-cong f≈g)
  (F ⊗ G) .fmap-id x =
    begin
      SP.prod-m (F .fmap (Category.id 𝒞 x)) (G .fmap (Category.id 𝒞 x))
    ≈⟨ SP.prod-m-cong (F .fmap-id x) (G .fmap-id x) ⟩
      SP.prod-m (idS _) (idS _)
    ≈⟨ SP.prod-m-id ⟩
      idS _
    ∎ where open ≈-Reasoning ≈s-isEquivalence
  (F ⊗ G) .fmap-∘ f g =
    begin
      SP.prod-m (F .fmap (f ∘ g)) (G .fmap (f ∘ g))
    ≈⟨ SP.prod-m-cong (F .fmap-∘ _ _) (G .fmap-∘ _ _) ⟩
      SP.prod-m (F .fmap g ∘S F .fmap f) (G .fmap g ∘S G .fmap f)
    ≈⟨ SP.pair-functorial _ _ _ _ ⟩
      SP.prod-m (F .fmap g) (G .fmap g) ∘S SP.prod-m (F .fmap f) (G .fmap f)
    ∎ where open ≈-Reasoning ≈s-isEquivalence

  products : HasProducts cat
  products .prod = _⊗_
  products .p₁ .transf x = SP.p₁
  products .p₁ .natural f = ≈s-isEquivalence .sym (SP.pair-p₁ _ _)
  products .p₂ .transf x = SP.p₂
  products .p₂ .natural f = ≈s-isEquivalence .sym (SP.pair-p₂ _ _)
  products .pair α β .transf x = SP.pair (α .transf x) (β .transf x)
  products .pair {F} {G} {H} α β .natural {x} {y} f =
    begin
      SP.prod-m (G .fmap f) (H .fmap f) ∘S SP.pair (α .transf y) (β .transf y)
    ≈⟨ SP.pair-compose _ _ _ _ ⟩
      SP.pair (G .fmap f ∘S α .transf y) (H .fmap f ∘S β .transf y)
    ≈⟨ SP.pair-cong (α .natural f) (β .natural f) ⟩
      SP.pair (α .transf x ∘S F .fmap f) (β .transf x ∘S F .fmap f)
    ≈⟨ ≈s-isEquivalence .sym (SP.pair-natural _ _ _) ⟩
      SP.pair (α .transf x) (β .transf x) ∘S F .fmap f
    ∎ where open ≈-Reasoning ≈s-isEquivalence
  products .pair-cong e₁ e₂ .transf-eq x = SP.pair-cong (e₁ .transf-eq x) (e₂ .transf-eq x)
  products .pair-p₁ f g .transf-eq x = SP.pair-p₁ _ _
  products .pair-p₂ f g .transf-eq x = SP.pair-p₂ _ _
  products .pair-ext f .transf-eq x = SP.pair-ext _

  open HasStrongCoproducts
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  _+_ : PreSheaf → PreSheaf → PreSheaf
  (F + G) .fobj x = +-setoid (F .fobj x) (G .fobj x)
  (F + G) .fmap f =
    prop-setoid.copair (prop-setoid.inject₁ ∘S F .fmap f)
                       (prop-setoid.inject₂ ∘S G .fmap f)
  (F + G) .fmap-cong f≈g ._≈s_.func-eq {inj₁ x} {inj₁ x₁} = F .fmap-cong f≈g ._≈s_.func-eq
  (F + G) .fmap-cong f≈g ._≈s_.func-eq {inj₂ y} {inj₂ y₁} = G .fmap-cong f≈g ._≈s_.func-eq
  (F + G) .fmap-id x ._≈s_.func-eq {inj₁ x₁} {inj₁ x₂} = F .fmap-id x ._≈s_.func-eq
  (F + G) .fmap-id x ._≈s_.func-eq {inj₂ y₁} {inj₂ y₂} = G .fmap-id x ._≈s_.func-eq
  (F + G) .fmap-∘ f g ._≈s_.func-eq {inj₁ x} {inj₁ x₁} = F .fmap-∘ f g ._≈s_.func-eq
  (F + G) .fmap-∘ f g ._≈s_.func-eq {inj₂ y} {inj₂ y₁} = G .fmap-∘ f g ._≈s_.func-eq

  strongCoproducts : HasStrongCoproducts cat products
  strongCoproducts .coprod = _+_
  strongCoproducts .in₁ .transf x = prop-setoid.inject₁
  strongCoproducts .in₁ {F}{G} .natural f ._≈s_.func-eq = F .fmap f ._⇒s_.func-resp-≈
  strongCoproducts .in₂ .transf x = prop-setoid.inject₂
  strongCoproducts .in₂ {F}{G} .natural f ._≈s_.func-eq = G .fmap f ._⇒s_.func-resp-≈
  strongCoproducts .copair α β .transf x = prop-setoid.case (α .transf x) (β .transf x)
  strongCoproducts .copair α β .natural f ._≈s_.func-eq {_ , inj₁ _} {_ , inj₁ _} = α .natural f ._≈s_.func-eq
  strongCoproducts .copair α β .natural f ._≈s_.func-eq {_ , inj₂ _} {_ , inj₂ _} = β .natural f ._≈s_.func-eq


-- Yoneda embedding and exponentials
module _ where

  open Category 𝒞
  open _⇒s_
  open _≈s_

  よ : obj → PreSheaf
  よ x .fobj y .Setoid.Carrier = Lift (o ⊔ m ⊔ e ⊔ os ⊔ es) (y ⇒ x)
  よ x .fobj y .Setoid._≈_ (lift f) (lift g) = LiftP (o ⊔ m ⊔ e ⊔ os ⊔ es) (f ≈ g)
  よ x .fobj y .Setoid.isEquivalence .refl = lift (isEquiv .refl)
  よ x .fobj y .Setoid.isEquivalence .sym (lift e) = lift (isEquiv .sym e)
  よ x .fobj y .Setoid.isEquivalence .trans (lift e₁) (lift e₂) = lift (isEquiv .trans e₁ e₂)
  よ x .fmap f .func (lift g) = lift (g ∘ f)
  よ x .fmap f .func-resp-≈ (lift g₁≈g₂) = lift (∘-cong g₁≈g₂ (isEquiv .refl))
  よ x .fmap-cong f≈g .func-eq (lift h₁≈h₂) = lift (∘-cong h₁≈h₂ f≈g)
  よ x .fmap-id y .func-eq (lift f≈g) = lift (isEquiv .trans id-right f≈g)
  よ x .fmap-∘ f g .func-eq (lift h₁≈h₂) .lower =
    isEquiv .trans (∘-cong h₁≈h₂ (isEquiv .refl)) (isEquiv .sym (assoc _ _ _))

  _⟶_ : PreSheaf → PreSheaf → PreSheaf
  (F ⟶ G) .fobj x = Category.hom-setoid cat (products .HasProducts.prod F (よ x)) G
  (F ⟶ G) .fmap f .func x .transf y .func (a , lift b) = x .transf y .func (a , (lift (f ∘ b)))
  (F ⟶ G) .fmap f .func x .transf y .func-resp-≈ (x₁≈x₂ , lift e) =
    x .transf y .func-resp-≈ (x₁≈x₂ , (lift (∘-cong (isEquiv .refl) e)))
  (F ⟶ G) .fmap f .func h .natural {y}{z} g .func-eq (a₁≈a₂ , lift e) =
    G .fobj y .Setoid.trans
      (h .natural g .func-eq (a₁≈a₂ , lift (∘-cong (isEquiv .refl) e)))
      (h .transf y .func-resp-≈ (F .fobj y .Setoid.refl , lift (assoc _ _ _)))
  (F ⟶ G) .fmap f .func-resp-≈ {h₁}{h₂} h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq x .func-eq (a₁≈a₂ , (lift (∘-cong (isEquiv .refl) e)))
  (F ⟶ G) .fmap-cong f≈g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (∘-cong f≈g e))
  (F ⟶ G) .fmap-id x .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift (isEquiv .trans id-left e))
  (F ⟶ G) .fmap-∘ f g .func-eq {h₁} {h₂} h₁≈h₂ .transf-eq y .func-eq (a₁≈a₂ , lift e) =
    h₁≈h₂ .transf-eq y .func-eq
      (a₁≈a₂ ,
       lift (isEquiv .trans (assoc _ _ _)
                            (∘-cong (isEquiv .refl) (∘-cong (isEquiv .refl) e))))

  eval : ∀ {F G} → ((F ⟶ G) ⊗ F) ⇒p G
  eval .transf x .func (g , a) = g .transf x .func (a , lift (id x))
  eval .transf x .func-resp-≈ (e , a₁≈a₂) =
    e .transf-eq x .func-eq (a₁≈a₂ , lift (isEquiv .refl))
  eval {F}{G} .natural {x} f .func-eq {h₁ , a₁} {h₂ , a₂} (e , a₁≈a₂) =
    G .fobj x .Setoid.trans
      (h₁ .natural f .func-eq (a₁≈a₂ , (lift (isEquiv .refl))))
      (e .transf-eq x .func-eq ( F .fobj x .Setoid.refl
                               , lift (isEquiv .trans id-left (isEquiv .sym id-right))))

  lambda : ∀ {F G H} → (F ⊗ G) ⇒p H → F ⇒p (G ⟶ H)
  lambda {F} f .transf x .func a .transf y .func (b , lift h) =
    f .transf y .func (F .fmap h .func a , b)
  lambda {F} f .transf x .func a .transf y .func-resp-≈ {a₁ , g₁} {a₂ , g₂} (a₁≈a₂ , lift g₁≈g₂) =
    f .transf y .func-resp-≈ (F .fmap-cong g₁≈g₂ .func-eq (F .fobj x .Setoid.refl) , a₁≈a₂)
  lambda {F}{G}{H} f .transf x .func a .natural {y} {z} g .func-eq {b₁ , lift h₁} {b₂ , lift h₂} (b₁≈b₂ , lift e) =
    H .fobj y .Setoid.trans
      (f .natural g .func-eq (F .fmap-cong e .func-eq (F .fobj x .Setoid.refl) , b₁≈b₂))
      (f .transf y .func-resp-≈ (F .fobj y .Setoid.sym (F .fmap-∘ h₂ g .func-eq (F .fobj x .Setoid.refl)) , G .fobj y .Setoid.refl))
  lambda {F}{G}{H} f .transf x .func-resp-≈ {a₁} {a₂} a₁≈a₂ .transf-eq y .func-eq {b₁ , lift g₁} {b₂ , lift g₂} (b₁≈b₂ , lift e) =
    f .transf y .func-resp-≈ (F .fmap-cong e .func-eq a₁≈a₂ , b₁≈b₂)
  lambda {F}{G}{H} f .natural {x} {y} g .func-eq {a₁} {a₂} a₁≈a₂ .transf-eq z .func-eq {b₁ , lift h₁} {b₂ , lift h₂} (b₁≈b₂ , lift e) =
    f .transf z .func-resp-≈
      (F .fobj z .Setoid.trans (F .fmap-∘ g h₁ .func-eq a₁≈a₂) (F .fmap-cong e .func-eq (F .fobj x .Setoid.refl))  ,
       b₁≈b₂)

  -- FIXME: equations for eval and lambda
