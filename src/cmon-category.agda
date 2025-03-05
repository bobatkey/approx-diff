{-# OPTIONS --prop --postfix-projections --safe #-}

module cmon-category where

open import Level
open import prop using (lift; lower)
open import prop-setoid using (module ≈-Reasoning; _∘S_; idS; IsEquivalence; Setoid)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import categories using (Category)
open import functor using (Functor; NatTrans; ≃-NatTrans; ≃-isEquivalence; id; _∘_; ∘NT-cong; NT-id-left; NT-id-right; NT-assoc; [_⇒_]; HasLimits'; _∘F_; _∘H_; ∘H-cong; constF; constF-F; interchange; constFmor; IsLimit; preserve-limits-of-shape)
open import cmon-enriched using (CMonEnriched; lambda-ε; lambda-+)
open import commutative-monoid using (CommutativeMonoid)
import commutative-monoid-cat

record CMonCategory o m e : Set (suc o ⊔ suc m ⊔ suc e) where
  no-eta-equality
  field
    cat : Category o m e
    cmon-enriched : CMonEnriched cat
  open Category cat hiding (opposite) public
  open CMonEnriched cmon-enriched public

  open CommutativeMonoid

  opposite : CMonCategory o m e
  opposite .cat = Category.opposite cat
  opposite .cmon-enriched .CMonEnriched.homCM x y .ε = homCM y x .ε
  opposite .cmon-enriched .CMonEnriched.homCM x y ._+_ = homCM y x ._+_
  opposite .cmon-enriched .CMonEnriched.homCM x y .+-cong = homCM y x .+-cong
  opposite .cmon-enriched .CMonEnriched.homCM x y .+-lunit = homCM y x .+-lunit
  opposite .cmon-enriched .CMonEnriched.homCM x y .+-assoc = homCM y x .+-assoc
  opposite .cmon-enriched .CMonEnriched.homCM x y .+-comm = homCM y x .+-comm
  opposite .cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g = comp-bilinear₂ g f₁ f₂
  opposite .cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ = comp-bilinear₁ g₁ g₂ f
  opposite .cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f = comp-bilinear-ε₂ f
  opposite .cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f = comp-bilinear-ε₁ f

-- FIXME: move this to commutative-monoid-cat?
CMon : ∀ o e → CMonCategory (suc o ⊔ suc e) (o ⊔ e) (o ⊔ e)
CMon o e .CMonCategory.cat = commutative-monoid-cat.cat o e
CMon o e .CMonCategory.cmon-enriched = commutative-monoid-cat.cmon-enriched

record CMonFunctor {o₁ m₁ e₁ o₂ m₂ e₂}
         (𝒞 : CMonCategory o₁ m₁ e₁)
         (𝒟 : CMonCategory o₂ m₂ e₂) : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ e₁ ⊔ e₂) where
  no-eta-equality
  private
    module 𝒞 = CMonCategory 𝒞
    module 𝒟 = CMonCategory 𝒟
  field
    functor : Functor 𝒞.cat 𝒟.cat
  open Functor functor public
  field
    fmor-ε : ∀ {x y} → fmor {x} {y} 𝒞.εm 𝒟.≈ 𝒟.εm
    fmor-+ : ∀ {x y} (f g : x 𝒞.⇒ y) → fmor (f 𝒞.+m g) 𝒟.≈ (fmor f 𝒟.+m fmor g)

module _ {o₁ m₁ e₁ o₂ m₂ e₂} {𝒞 : CMonCategory o₁ m₁ e₁} {𝒟 : CMonCategory o₂ m₂ e₂} where

  private
    module 𝒞 = CMonCategory 𝒞
    module 𝒟 = CMonCategory 𝒟
  open CMonFunctor

  CMonNatTrans : (F G : CMonFunctor 𝒞 𝒟) → Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂)
  CMonNatTrans F G = NatTrans (F .functor) (G .functor)

module _ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒞 : CMonCategory o₁ m₁ e₁) (𝒟 : CMonCategory o₂ m₂ e₂) where

  open CMonFunctor
  open CommutativeMonoid
  open NatTrans
  open ≃-NatTrans

  private
    module 𝒞 = CMonCategory 𝒞
    module 𝒟 = CMonCategory 𝒟

  CMon[_⇒_]₀ : Category (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) (o₁ ⊔ e₂)
  CMon[_⇒_]₀ .Category.obj = CMonFunctor 𝒞 𝒟
  CMon[_⇒_]₀ .Category._⇒_ = CMonNatTrans
  CMon[_⇒_]₀ .Category._≈_ = ≃-NatTrans
  CMon[_⇒_]₀ .Category.isEquiv = ≃-isEquivalence
  CMon[_⇒_]₀ .Category.id F = id (F .functor)
  CMon[_⇒_]₀ .Category._∘_ = _∘_
  CMon[_⇒_]₀ .Category.∘-cong = ∘NT-cong
  CMon[_⇒_]₀ .Category.id-left = NT-id-left
  CMon[_⇒_]₀ .Category.id-right = NT-id-right
  CMon[_⇒_]₀ .Category.assoc = NT-assoc

  homCM-F : ∀ F G → CommutativeMonoid (Category.hom-setoid CMon[_⇒_]₀ F G)
  homCM-F F G .ε .transf x = 𝒟.εm
  homCM-F F G .ε .natural f =
    𝒟.≈-trans (𝒟.comp-bilinear-ε₂ _) (𝒟.≈-sym (𝒟.comp-bilinear-ε₁ _))
  homCM-F F G ._+_ f₁ f₂ .transf x = 𝒟.homCM _ _ ._+_ (f₁ .transf x) (f₂ .transf x)
  homCM-F F G ._+_ f₁ f₂ .natural {x} {y} f =
    begin
      G .fmor f 𝒟.∘ (f₁ .transf x 𝒟.+m f₂ .transf x)
    ≈⟨ 𝒟.comp-bilinear₂ _ _ _ ⟩
      (G .fmor f 𝒟.∘ f₁ .transf x) 𝒟.+m (G .fmor f 𝒟.∘ f₂ .transf x)
    ≈⟨ 𝒟.homCM _ _ .+-cong (f₁ .natural f) (f₂ .natural f) ⟩
      (f₁ .transf y 𝒟.∘ F .fmor f) 𝒟.+m (f₂ .transf y 𝒟.∘ F .fmor f )
    ≈⟨ 𝒟.≈-sym (𝒟.comp-bilinear₁ _ _ _) ⟩
      (f₁ .transf y 𝒟.+m f₂ .transf y) 𝒟.∘ F .fmor f
    ∎
    where open ≈-Reasoning 𝒟.isEquiv
  homCM-F F G .+-cong f₁≈f₂ g₁≈g₂ .transf-eq x =
    𝒟.homCM _ _ .+-cong (f₁≈f₂ .transf-eq x) (g₁≈g₂ .transf-eq x)
  homCM-F F G .+-lunit .transf-eq x = 𝒟.homCM _ _ .+-lunit
  homCM-F F G .+-assoc .transf-eq x = 𝒟.homCM _ _ .+-assoc
  homCM-F F G .+-comm .transf-eq x = 𝒟.homCM _ _ .+-comm

  cmon-enriched : CMonEnriched CMon[_⇒_]₀
  cmon-enriched .CMonEnriched.homCM = homCM-F
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .transf-eq x = 𝒟.comp-bilinear₁ _ _ _
  cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ .transf-eq x = 𝒟.comp-bilinear₂ _ _ _
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .transf-eq x = 𝒟.comp-bilinear-ε₁ _
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .transf-eq x = 𝒟.comp-bilinear-ε₂ _

  CMon[_⇒_] : CMonCategory (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) (o₁ ⊔ e₂)
  CMon[_⇒_] .CMonCategory.cat = CMon[_⇒_]₀
  CMon[_⇒_] .CMonCategory.cmon-enriched = cmon-enriched

{-
  -- This doesn't exist! unless zero maps are the identities in 𝒟
  --
  -- Note: There is a const : CMonFunctor 𝒟 [ 𝒞 ⇒ 𝒟 ], because then we don't have to make a CmonFunctor!
  const : CMonFunctor 𝒟 CMon[_⇒_]
  const .functor .Functor.fobj x .functor .Functor.fobj _ = x
  const .functor .Functor.fobj x .functor .Functor.fmor _ = 𝒟.id x
  const .functor .Functor.fobj x .functor .Functor.fmor-cong _ = 𝒟.≈-refl
  const .functor .Functor.fobj x .functor .Functor.fmor-id = 𝒟.≈-refl
  const .functor .Functor.fobj x .functor .Functor.fmor-comp _ _ = 𝒟.≈-sym 𝒟.id-left
  const .functor .Functor.fobj x .fmor-ε = {!!}
  const .functor .Functor.fobj x .fmor-+ _ _ = {!!}
  const .functor .Functor.fmor f .transf _ = f
  const .functor .Functor.fmor f .natural _ = 𝒟.id-swap
  const .functor .Functor.fmor-cong f₁≈f₂  = {!!}
  const .functor .Functor.fmor-id = {!!}
  const .functor .Functor.fmor-comp = {!!}
  const .fmor-ε .transf-eq x = 𝒟.≈-refl
  const .fmor-+ f g .transf-eq x = 𝒟.≈-refl
-}

module _ {o₁ m₁ e₁ o₂ m₂ e₂} (𝒞 : CMonCategory o₁ m₁ e₁) (𝒟 : CMonCategory o₂ m₂ e₂) where

  open CMonFunctor
  open Functor
  open CommutativeMonoid
  open NatTrans
  open ≃-NatTrans

  private
    module 𝒞 = CMonCategory 𝒞
    module 𝒟 = CMonCategory 𝒟

  evalAt : CMonFunctor 𝒞 CMon[ CMon[ 𝒞 ⇒ 𝒟 ] ⇒ 𝒟 ]
  evalAt .functor .fobj x .functor .fobj F = F .fobj x
  evalAt .functor .fobj x .functor .fmor α = α .transf x
  evalAt .functor .fobj x .functor .fmor-cong F₁≃F₂ = F₁≃F₂ .transf-eq x
  evalAt .functor .fobj x .functor .fmor-id = 𝒟.≈-refl
  evalAt .functor .fobj x .functor .fmor-comp α β = 𝒟.≈-refl
  evalAt .functor .fobj x .fmor-ε = 𝒟.≈-refl
  evalAt .functor .fobj x .fmor-+ α β = 𝒟.≈-refl
  evalAt .functor .fmor f .transf F = F .fmor f
  evalAt .functor .fmor f .natural α = 𝒟.≈-sym (α .natural f)
  evalAt .functor .fmor-cong f₁≈f₂ .transf-eq F = F .fmor-cong f₁≈f₂
  evalAt .functor .fmor-id .transf-eq F = F .fmor-id
  evalAt .functor .fmor-comp f g .transf-eq F = F .fmor-comp f g
  evalAt .fmor-ε .transf-eq F = F .fmor-ε
  evalAt .fmor-+ f g .transf-eq F = F .fmor-+ _ _

--   evalAt .fmor 𝒞.εm ≈ (CMon[ CMon[ 𝒞 ⇒ 𝒟 ] ⇒ 𝒟 ] .εm)
--   and Natural transformations + horizontal composition is a CMon-category

  -- If 𝒟 has ordinary limits of shape 𝒮, then so does CMon[ 𝒞 ⇒ 𝒟 ]₀.
  module _ {o₃ m₃ e₃} (𝒮 : Category o₃ m₃ e₃) (𝒟-limits : HasLimits' 𝒮 𝒟.cat) where

    private
      module 𝒮 = Category 𝒮
      module DL = HasLimits' 𝒟-limits

    open IsEquivalence

    Π : Functor 𝒮 CMon[ 𝒞 ⇒ 𝒟 ]₀ → CMonFunctor 𝒞 𝒟
    Π F .functor .fobj x = DL.Π (evalAt .fobj x .functor ∘F F)
    Π F .functor .fmor f = DL.Π-map (evalAt .fmor f ∘H id F)
    Π F .functor .fmor-cong f₁≈f₂ =
      DL.Π-map-cong (∘H-cong (evalAt .fmor-cong f₁≈f₂) (≃-isEquivalence .refl {id F}))
    Π F .functor .fmor-id {x} =
      begin
        DL.Π-map (evalAt .fmor (𝒞.id x) ∘H id F)
      ≈⟨ DL.Π-map-cong (∘H-cong (evalAt .fmor-id) (≃-isEquivalence .refl {id F})) ⟩
        DL.Π-map (id (evalAt .fobj x .functor) ∘H id F)
      ≈⟨ DL.Π-map-cong (record { transf-eq = λ _ → 𝒟.id-left }) ⟩
        DL.Π-map (id _)
      ≈⟨ DL.Π-map-id ⟩
        𝒟.id (DL.Π (evalAt .fobj x .functor ∘F F))
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
    Π F .functor .fmor-comp {x} {y} {z} f g =
      begin
        DL.Π-map (evalAt .fmor (f 𝒞.∘ g) ∘H id F)
      ≈⟨ DL.Π-map-cong (∘H-cong (evalAt .fmor-comp f g) (≃-isEquivalence .sym NT-id-left)) ⟩
        DL.Π-map ((evalAt .fmor f ∘ evalAt .fmor g) ∘H (id F ∘ id F))
      ≈⟨ DL.Π-map-cong (interchange _ _ _ _) ⟩
        DL.Π-map ((evalAt .fmor f ∘H id F) ∘ (evalAt .fmor g ∘H id F))
      ≈⟨ DL.Π-map-comp _ _ ⟩
        DL.Π-map (evalAt .fmor f ∘H id F) 𝒟.∘ DL.Π-map (evalAt .fmor g ∘H id F)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
    Π F .fmor-ε = {!!}
    Π F .fmor-+ f g = {!!}

    lambdaΠ : ∀ (X : CMonFunctor 𝒞 𝒟) (F : Functor 𝒮 CMon[ 𝒞 ⇒ 𝒟 ]₀) →
              NatTrans (constF 𝒮 {CMon[ 𝒞 ⇒ 𝒟 ]₀} X) F →
              CMonNatTrans X (Π F)
    lambdaΠ X F α .transf x = DL.lambdaΠ _ _ ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X)
    lambdaΠ X F α .natural {x} {y} f =
      begin
        DL.Π-map (evalAt .fmor f ∘H id F) 𝒟.∘ DL.lambdaΠ (X .fobj x) (evalAt .fobj x .functor ∘F F) ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X)
      ≈⟨ DL.lambdaΠ-natural _ _ ⟩
        DL.lambdaΠ _ _ (((evalAt .fmor f ∘H id F) ∘ DL.evalΠ _) ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x .functor ∘F F) ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X)))
      ≈⟨ DL.lambda-cong (𝒮𝒟.assoc (evalAt .fmor f ∘H id F) (DL.evalΠ _) (constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x .functor ∘F F) ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X)))) ⟩
        DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ (DL.evalΠ _ ∘ constFmor (DL.lambdaΠ (X .fobj x) (evalAt .fobj x .functor ∘F F) ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X))))
      ≈⟨ DL.lambda-cong (𝒮𝒟.∘-cong (𝒮𝒟.≈-refl {f = evalAt .fmor f ∘H id F}) (DL.lambda-eval ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X))) ⟩
        DL.lambdaΠ _ _ ((evalAt .fmor f ∘H id F) ∘ ((id _ ∘H α) ∘ constF-F (evalAt .fobj x .functor) X))
      ≈˘⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
        DL.lambdaΠ _ _ (((evalAt .fmor f ∘H id F) ∘ (id _ ∘H α)) ∘ constF-F (evalAt .fobj x .functor) X)
      ≈˘⟨ DL.lambda-cong (∘NT-cong (interchange _ _ _ _) 𝒮𝒟.≈-refl) ⟩
        DL.lambdaΠ _ _ (((evalAt .fmor f ∘ id _) ∘H (id F ∘ α)) ∘ constF-F (evalAt .fobj x .functor) X)
      ≈⟨ DL.lambda-cong (∘NT-cong (∘H-cong (𝒞𝒟.≈-sym {evalAt .fobj x} {evalAt .fobj y} (𝒞𝒟.id-swap {evalAt .fobj x} {evalAt .fobj y})) 𝒮𝒞𝒟.id-swap) 𝒮𝒟.≈-refl) ⟩
        DL.lambdaΠ _ _ (((id _ ∘ evalAt .fmor f) ∘H (α ∘ id _)) ∘ constF-F (evalAt .fobj x .functor) X)
      ≈⟨ DL.lambda-cong (∘NT-cong (interchange _ _ _ _) 𝒮𝒟.≈-refl) ⟩
        DL.lambdaΠ _ _ (((id _ ∘H α) ∘ (evalAt .fmor f ∘H id _)) ∘ constF-F (evalAt .fobj x .functor) X)
      ≈⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
        DL.lambdaΠ _ _ ((id _ ∘H α) ∘ ((evalAt .fmor f ∘H id _) ∘ constF-F (evalAt .fobj x .functor) X))
      ≈⟨ DL.lambda-cong (∘NT-cong 𝒮𝒟.≈-refl (record { transf-eq = λ s → 𝒟.isEquiv .trans 𝒟.id-right (𝒟.≈-sym 𝒟.id-swap) })) ⟩
        DL.lambdaΠ _ _ ((id _ ∘H α) ∘ (constF-F (evalAt .fobj y .functor) X ∘ constFmor (X .fmor f)))
      ≈˘⟨ DL.lambda-cong (NT-assoc _ _ _) ⟩
        DL.lambdaΠ _ _ (((id _ ∘H α) ∘ constF-F (evalAt .fobj y .functor) X) ∘ constFmor (X .fmor f))
      ≈⟨ 𝒟.≈-sym (DL.lambdaΠ-natural _ _) ⟩
        DL.lambdaΠ _ _ ((id _ ∘H α) ∘ constF-F (evalAt .fobj y .functor) X) 𝒟.∘ X .fmor f
      ∎ where open ≈-Reasoning 𝒟.isEquiv
              module 𝒮𝒟 = Category [ 𝒮 ⇒ 𝒟.cat ]
              module 𝒞𝒟 = CMonCategory CMon[ CMon[ 𝒞 ⇒ 𝒟 ] ⇒ 𝒟 ]
              module 𝒮𝒞𝒟 = Category [ 𝒮 ⇒ CMon[ 𝒞 ⇒ 𝒟 ]₀ ]

    evalΠ : (F : Functor 𝒮 CMon[ 𝒞 ⇒ 𝒟 ]₀) → NatTrans (constF 𝒮 (Π F)) F
    evalΠ F .transf s .transf x = DL.evalΠ _ .transf s
    evalΠ F .transf s .natural {x} {y} f =
      begin
        F .fobj s .fmor f 𝒟.∘ DL.evalΠ (evalAt .fobj x .functor ∘F F) .transf s
      ≈⟨ 𝒟.∘-cong (𝒟.≈-sym 𝒟.id-right) 𝒟.≈-refl ⟩
        (F .fobj s .fmor f 𝒟.∘ 𝒟.id _) 𝒟.∘ DL.evalΠ (evalAt .fobj x .functor ∘F F) .transf s
      ≈⟨ 𝒟.≈-sym (DL.lambda-eval ((evalAt .fmor f ∘H id F) ∘ DL.evalΠ _) .transf-eq s) ⟩
        DL.evalΠ (evalAt .fobj y .functor ∘F F) .transf s 𝒟.∘ DL.Π-map (evalAt .fmor f ∘H id F)
      ∎
      where open ≈-Reasoning 𝒟.isEquiv
    evalΠ F .natural f .transf-eq x = DL.evalΠ _ .natural f

    limits : HasLimits' 𝒮 CMon[ 𝒞 ⇒ 𝒟 ]₀
    limits .HasLimits'.Π = Π
    limits .HasLimits'.lambdaΠ = lambdaΠ
    limits .HasLimits'.evalΠ = evalΠ
    limits .HasLimits'.lambda-cong α≃β .transf-eq x =
      DL.lambda-cong (∘NT-cong (∘H-cong (≃-isEquivalence .refl) α≃β) (≃-isEquivalence .refl))
    limits .HasLimits'.lambda-eval {X} {F} α .transf-eq s .transf-eq x =
      𝒟.isEquiv .trans
         (DL.lambda-eval _ .transf-eq s)
         (𝒟.isEquiv .trans (𝒟.∘-cong 𝒟.id-left 𝒟.≈-refl) 𝒟.id-right)
    limits .HasLimits'.lambda-ext {X} {F} α .transf-eq x =
      𝒟.isEquiv .trans
        (DL.lambda-cong (record { transf-eq = λ s → 𝒟.isEquiv .trans 𝒟.id-right 𝒟.id-left }))
        (DL.lambda-ext (α .transf x))

------------------------------------------------------------------------------
-- PreSheaves and Yoneda
module presheaves {o m e} os (𝒞 : CMonCategory o m e) where

  private
    module 𝒞 = CMonCategory 𝒞

  PSh₀ = CMon[ 𝒞.opposite ⇒ CMon (o ⊔ m ⊔ e ⊔ os) (o ⊔ m ⊔ e ⊔ os) ]₀
  PSh = CMon[ 𝒞.opposite ⇒ CMon (o ⊔ m ⊔ e ⊔ os) (o ⊔ m ⊔ e ⊔ os) ]

  open CMonFunctor
  open Functor
  open NatTrans
  open ≃-NatTrans
  open CommutativeMonoid
  open commutative-monoid-cat.Obj
  open commutative-monoid-cat._⇒_
  open commutative-monoid._=[_]>_
  open prop-setoid._⇒_
  open prop-setoid._≃m_

  よ : CMonFunctor 𝒞 PSh
  よ .functor .fobj x .functor .fobj y .carrier = 𝒞.hom-setoid-l (o ⊔ e ⊔ os) (o ⊔ m ⊔ os) y x
  よ .functor .fobj x .functor .fobj y .commMonoid .ε .lower = 𝒞.εm
  よ .functor .fobj x .functor .fobj y .commMonoid ._+_ f g .lower = f .lower 𝒞.+m g .lower
  よ .functor .fobj x .functor .fobj y .commMonoid .+-cong (lift p) (lift q) = lift (𝒞.homCM _ _ .+-cong p q)
  よ .functor .fobj x .functor .fobj y .commMonoid .+-lunit = lift (𝒞.homCM _ _ .+-lunit)
  よ .functor .fobj x .functor .fobj y .commMonoid .+-assoc = lift (𝒞.homCM _ _ .+-assoc)
  よ .functor .fobj x .functor .fobj y .commMonoid .+-comm = lift (𝒞.homCM _ _ .+-comm)
  よ .functor .fobj x .functor .fmor f .function .func (lift g) = lift (g 𝒞.∘ f)
  よ .functor .fobj x .functor .fmor f .function .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ 𝒞.≈-refl)
  よ .functor .fobj x .functor .fmor f .cmFunc .preserve-ε = lift (𝒞.comp-bilinear-ε₁ _)
  よ .functor .fobj x .functor .fmor f .cmFunc .preserve-+ {lift g₁} {lift g₂}= lift (𝒞.comp-bilinear₁ g₁ g₂ f)
  よ .functor .fobj x .functor .fmor-cong f₁≈f₂ .func-eq (lift g₁≈g₂) = lift (𝒞.∘-cong g₁≈g₂ f₁≈f₂)
  よ .functor .fobj x .functor .fmor-id .func-eq (lift g₁≈g₂) = lift (𝒞.≈-trans 𝒞.id-right g₁≈g₂)
  よ .functor .fobj x .functor .fmor-comp f g .func-eq (lift h₁≈h₂) = lift (𝒞.≈-trans (𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl) (𝒞.≈-sym (𝒞.assoc _ _ _)))
  よ .functor .fobj x .fmor-ε .func-eq (lift g₁≈g₂) = lift (𝒞.comp-bilinear-ε₂ _)
  よ .functor .fobj x .fmor-+ f g .func-eq (lift h₁≈h₂) = lift (𝒞.≈-trans (𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl) (𝒞.comp-bilinear₂ _ _ _))
  よ .functor .fmor f .transf x .function .func (lift g) = lift (f 𝒞.∘ g)
  よ .functor .fmor f .transf x .function .func-resp-≈ (lift g₁≈g₂) = lift (𝒞.∘-cong 𝒞.≈-refl g₁≈g₂)
  よ .functor .fmor f .transf x .cmFunc .preserve-ε = lift (𝒞.comp-bilinear-ε₂ f)
  よ .functor .fmor f .transf x .cmFunc .preserve-+ = lift (𝒞.comp-bilinear₂ _ _ _)
  よ .functor .fmor f .natural g .func-eq (lift h₁≈h₂) = lift (𝒞.≈-trans (𝒞.assoc _ _ _) (𝒞.∘-cong 𝒞.≈-refl (𝒞.∘-cong h₁≈h₂ 𝒞.≈-refl)))
  よ .functor .fmor-cong f₁≈f₂ .transf-eq x .func-eq (lift g₁≈g₂) = lift (𝒞.∘-cong f₁≈f₂ g₁≈g₂)
  よ .functor .fmor-id .transf-eq x .func-eq (lift g₁≈g₂) = lift (𝒞.≈-trans 𝒞.id-left g₁≈g₂)
  よ .functor .fmor-comp f g .transf-eq x .func-eq (lift h₁≈h₂) = lift (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.assoc _ _ _))
  よ .fmor-ε .transf-eq x .func-eq (lift g₁≈g₂)  = lift (𝒞.comp-bilinear-ε₁ _)
  よ .fmor-+ f g .transf-eq x .func-eq (lift h₁≈h₂) = lift (𝒞.≈-trans (𝒞.∘-cong 𝒞.≈-refl h₁≈h₂) (𝒞.comp-bilinear₁ _ _ _))

  PSh₀[_,_] : Category.obj PSh₀ → Category.obj PSh₀ → Setoid _ _
  PSh₀[_,_] F G = Category.hom-setoid PSh₀ F G

  lemma : ∀ F x → F .fobj x .carrier ⇒s PSh₀[ よ .fobj x , F ]
  lemma F x .func xF .transf y .function .func (lift f)  = F .fmor f .func xF
  lemma F x .func xF .transf y .function .func-resp-≈ (lift f₁≈f₂) = F .fmor-cong f₁≈f₂ .func-eq (F .fobj x .refl)
  lemma F x .func xF .transf y .cmFunc .preserve-ε = F .fmor-ε .func-eq (F .fobj x .refl)
  lemma F x .func xF .transf y .cmFunc .preserve-+ = F .fmor-+ _ _ .func-eq (F .fobj x .refl)
  lemma F x .func xF .natural {y} {z} g .func-eq {lift h₁} {lift h₂} (lift h₁≈h₂) =
    begin
      F .fmor g .func (F .fmor h₁ .func xF)
    ≈⟨ F .fmor g .func-resp-≈ (F .fmor-cong h₁≈h₂ .func-eq (F .fobj x .refl)) ⟩
      F .fmor g .func (F .fmor h₂ .func xF)
    ≈˘⟨ F .fmor-comp g h₂ .func-eq (F .fobj x .refl) ⟩
      F .fmor (h₂ 𝒞.∘ g) .func xF
    ∎
    where open ≈-Reasoning (F .fobj z .isEquivalence)
  lemma F x .func-resp-≈ x₁≈x₂ .transf-eq y .func-eq (lift f₁≈f₂) =
    F .fmor-cong f₁≈f₂ .func-eq x₁≈x₂

  lemma⁻¹ : ∀ F x →  PSh₀[ よ .fobj x , F ] ⇒s F .fobj x .carrier
  lemma⁻¹ F x .func α = α .transf x .func (lift (𝒞.id _))
  lemma⁻¹ F x .func-resp-≈ α₁≈α₂ = α₁≈α₂ .transf-eq x .func-eq (lift 𝒞.≈-refl)

  lemma∘lemma⁻¹ : ∀ F x → (lemma F x ∘S lemma⁻¹ F x) ≈s idS PSh₀[ よ .fobj x , F ]
  lemma∘lemma⁻¹ F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ .transf-eq y .func-eq {lift f} {lift g} (lift f≈g) =
    F .fobj y .trans (Fx₁ .natural f .func-eq (lift 𝒞.≈-refl)) (Fx₁≈Fx₂ .transf-eq y .func-eq (lift (𝒞.≈-trans 𝒞.id-left f≈g)))

  lemma⁻¹∘lemma : ∀ F x → (lemma⁻¹ F x ∘S lemma F x) ≈s idS (F .fobj x .carrier)
  lemma⁻¹∘lemma F x .func-eq {Fx₁} {Fx₂} Fx₁≈Fx₂ = F .fmor-id .func-eq Fx₁≈Fx₂

  -- FIXME: naturality

  よ⁻¹ : ∀ {x y} → Category._⇒_ PSh₀ (よ .fobj x) (よ .fobj y) → x 𝒞.⇒ y
  よ⁻¹ {x} {y} f = lemma⁻¹ (よ .fobj y) x .func f .lower

  preserve-limits : ∀ {o₁ m₁ e₁} (𝒮 : Category o₁ m₁ e₁) → preserve-limits-of-shape 𝒮 (よ .functor)
  preserve-limits 𝒮 D apex cone isLimit = lim
    where
    open IsLimit
    module 𝒮Psh = CMonEnriched (cmon-enriched.FunctorCat-cmon 𝒮 PSh₀ (cmon-enriched _ _))
    module 𝒮𝒞 = CMonEnriched (cmon-enriched.FunctorCat-cmon 𝒮 𝒞.cat 𝒞.cmon-enriched)

    conv-transf : ∀ {X x} → NatTrans (constF 𝒮 X) (よ .functor ∘F D) → X .fobj x .Carrier → NatTrans (constF 𝒮 x) D
    conv-transf {X} {x} α Xx .transf s = α .transf s .transf x .func Xx .lower
    conv-transf {X} {x} α Xx .natural f = 𝒞.≈-trans (α .natural f .transf-eq x .func-eq (X .fobj x .refl) .lower) (𝒞.≈-sym 𝒞.id-right)

    conv-transf-≈ : ∀ {X x α₁ α₂ Xx₁ Xx₂} →
                      ≃-NatTrans α₁ α₂ →
                      X .fobj x ._≈_ Xx₁ Xx₂ →
                      ≃-NatTrans (conv-transf {X} {x} α₁ Xx₁) (conv-transf {X} {x} α₂ Xx₂)
    conv-transf-≈ {X} {x} α₁≈α₂ Xx₁≈Xx₂ .transf-eq s = α₁≈α₂ .transf-eq s .transf-eq x .func-eq Xx₁≈Xx₂ .lower

    conv-transf-ε : ∀ {X x} (α : NatTrans (constF 𝒮 X) (よ .functor ∘F D)) →
                    ≃-NatTrans (conv-transf α (X .fobj x .ε)) 𝒮𝒞.εm
    conv-transf-ε {X} {x} α .transf-eq s = α .transf s .transf x .preserve-ε .lower

    conv-transf-+ : ∀ {X x} (α : NatTrans (constF 𝒮 X) (よ .functor ∘F D))
                      {x₁ x₂ : X .fobj x .Carrier} →
                    ≃-NatTrans
                      (conv-transf α (X .fobj x .commMonoid ._+_ x₁ x₂))
                      (conv-transf α x₁ 𝒮𝒞.+m conv-transf α x₂)
    conv-transf-+ {X} {x} α .transf-eq s = α .transf s .transf x .preserve-+ .lower

    lim : IsLimit (よ .functor ∘F D) (よ .fobj apex) ((id _ ∘H cone) ∘ constF-F (よ .functor) apex)
    lim .lambda X α .transf x .function .func Xx .lower = isLimit .lambda x (conv-transf α Xx)
    lim .lambda X α .transf x .function .func-resp-≈ Xx₁≈Xx₂ .lower = isLimit .lambda-cong (conv-transf-≈ (≃-isEquivalence .IsEquivalence.refl) Xx₁≈Xx₂)
    lim .lambda X α .transf x .cmFunc .preserve-ε .lower = begin
        isLimit .lambda x (conv-transf α (X .fobj x .commMonoid .ε))
      ≈⟨ isLimit .lambda-cong (conv-transf-ε α) ⟩
        isLimit .lambda x 𝒮𝒞.εm
      ≈⟨ lambda-ε 𝒞.cmon-enriched D (record { isLimit = isLimit }) ⟩
        𝒞.homCM x apex .ε
      ∎
      where open ≈-Reasoning 𝒞.isEquiv
    lim .lambda X α .transf x .cmFunc .preserve-+ {x₁}{x₂} .lower =
      begin
        isLimit .lambda x (conv-transf α (X .fobj x .commMonoid ._+_ x₁ x₂))
      ≈⟨ isLimit .lambda-cong (conv-transf-+ α) ⟩
        isLimit .lambda x (conv-transf α x₁ 𝒮𝒞.+m conv-transf α x₂)
      ≈˘⟨ lambda-+ 𝒞.cmon-enriched D (record { isLimit = isLimit }) _ _ ⟩
        isLimit .lambda x (conv-transf α x₁) 𝒞.+m isLimit .lambda x (conv-transf α x₂)
      ∎
      where open ≈-Reasoning 𝒞.isEquiv
    lim .lambda X α .natural {x} {y} f .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
      begin
        isLimit .lambda x (conv-transf α Xx₁) 𝒞.∘ f
      ≈⟨ lambda-natural isLimit (conv-transf α Xx₁) f ⟩
        isLimit .lambda y (conv-transf α Xx₁ ∘ constFmor f)
      ≈⟨ isLimit .lambda-cong (record { transf-eq = λ s → α .transf s .natural f .func-eq Xx₁≈Xx₂ .lower }) ⟩
        isLimit .lambda y (conv-transf α (X .functor .fmor f .function .func Xx₂))
      ∎
      where open ≈-Reasoning 𝒞.isEquiv
    lim .lambda-cong α≈β .transf-eq x .func-eq Xx₁≈Xx₂ .lower = isLimit .lambda-cong (conv-transf-≈ α≈β Xx₁≈Xx₂)
    lim .lambda-eval {X} α .transf-eq s .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
      𝒞.≈-trans (isLimit .lambda-eval (conv-transf α Xx₁) .transf-eq s)
                 (α .transf s .transf x .func-resp-≈ Xx₁≈Xx₂ .lower)
    lim .lambda-ext {X} f .transf-eq x .func-eq {Xx₁} {Xx₂} Xx₁≈Xx₂ .lower =
      {!!}
