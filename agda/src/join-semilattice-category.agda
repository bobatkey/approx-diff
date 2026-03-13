{-# OPTIONS --postfix-projections --prop --safe #-}

module join-semilattice-category where

open import Level using (suc; 0ℓ)
open import prop using (proj₁; proj₂; _,_; LiftS; liftS)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import basics using (IsPreorder; IsBottom; IsJoin)
open import preorder using (Preorder; _=>_; _×_) renaming (_≃m_ to _≃P_)
open import join-semilattice
  using ( JoinSemilattice; 𝟙
        ; εm; _+m_; +m-cong; +m-comm; +m-assoc; +m-lunit
        ; comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂)
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; id to idJ; _∘_ to _∘J_;
            _⊕_ to _⊕J_;
            ≃m-isEquivalence to ≃J-isEquivalence)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; HasInitial)
open import functor using (IsColimit; Colimit; HasColimits; IsLimit; Limit; HasLimits; Functor; NatTrans; ≃-NatTrans)
import two

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    joins   : JoinSemilattice carrier
  open Preorder carrier public
  open JoinSemilattice joins public
open Obj

record _⇒_ (X Y : Obj) : Set where
  no-eta-equality
  field
    *→* : X .joins =>J Y .joins
  open _=>J_ *→* public
  open preorder._=>_ func public
open _⇒_

record _≃m_ {X Y : Obj} (f g : X ⇒ Y) : Prop where
  no-eta-equality
  field
    f≃f : f .*→* ≃J g .*→*
  open _≃J_ f≃f public
  open preorder._≃m_ eqfunc public
open _≃m_

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv .IsEquivalence.refl .f≃f = ≃J-isEquivalence .IsEquivalence.refl
cat .Category.isEquiv .IsEquivalence.sym f≃g .f≃f = ≃J-isEquivalence .IsEquivalence.sym (f≃g .f≃f)
cat .Category.isEquiv .IsEquivalence.trans f≃g g≃h .f≃f =
  ≃J-isEquivalence .IsEquivalence.trans (f≃g .f≃f) (g≃h .f≃f)
cat .Category.id X .*→* = idJ
cat .Category._∘_ f g .*→* = f .*→* ∘J g .*→*
cat .Category.∘-cong f₁≃f₂ g₁≃g₂ .f≃f = join-semilattice.∘-cong (f₁≃f₂ .f≃f) (g₁≃g₂ .f≃f)
cat .Category.id-left .f≃f = join-semilattice.id-left
cat .Category.id-right .f≃f = join-semilattice.id-right
cat .Category.assoc f g h .f≃f = join-semilattice.assoc (f .*→*) (g .*→*) (h .*→*)

------------------------------------------------------------------------------
-- CMon-enrichment

open import commutative-monoid using (CommutativeMonoid)
open import cmon-enriched using (CMonEnriched)

cmon-enriched : CMonEnriched cat
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.ε .*→* = εm
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid._+_ f g .*→* = (f .*→*) +m (g .*→*)
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-cong f₁≃f₂ g₁≃g₂ .f≃f = +m-cong (f₁≃f₂ .f≃f) (g₁≃g₂ .f≃f)
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-lunit .f≃f = +m-lunit
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-assoc {f}{g}{h} .f≃f = +m-assoc {f = f .*→*} {g .*→*} {h .*→*}
cmon-enriched .CMonEnriched.homCM x y .CommutativeMonoid.+-comm {f}{g} .f≃f = +m-comm {f = f .*→*} {g .*→*}
cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .f≃f = comp-bilinear₁ (f₁ .*→*) (f₂ .*→*) (g .*→*)
cmon-enriched .CMonEnriched.comp-bilinear₂ f g₁ g₂ .f≃f = comp-bilinear₂ (f .*→*) (g₁ .*→*) (g₂ .*→*)
cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .f≃f = comp-bilinear-ε₁ (f .*→*)
cmon-enriched .CMonEnriched.comp-bilinear-ε₂ f .f≃f = comp-bilinear-ε₂ (f .*→*)


------------------------------------------------------------------------------
-- Colimits

module _ (𝒮 : Category 0ℓ 0ℓ 0ℓ) where

  private
    module 𝒮 = Category 𝒮

  open Functor
  open NatTrans
  open ≃-NatTrans
  open _≃J_
  open preorder._=>_
  open preorder._≃m_

  data ∐-carrier (D : Functor 𝒮 cat) : Set where
    bot  : ∐-carrier D
    join : ∐-carrier D → ∐-carrier D → ∐-carrier D
    elt  : (s : 𝒮.obj) → D .fobj s .Carrier → ∐-carrier D

  data le (D : Functor 𝒮 cat) : ∐-carrier D → ∐-carrier D → Set where
    le-refl     : ∀ {t} → le D t t
    le-trans    : ∀ {r s t} → le D r s → le D s t → le D r t
    le-bot      : ∀ {t} → le D bot t
    le-upper₁   : ∀ {t₁ t₂} → le D t₁ (join t₁ t₂)
    le-upper₂   : ∀ {t₁ t₂} → le D t₂ (join t₁ t₂)
    le-least    : ∀ {t₁ t₂ u} → le D t₁ u → le D t₂ u → le D (join t₁ t₂) u
    le-mono     : ∀ s {t u} → D .fobj s ._≤_ t u → le D (elt s t) (elt s u)
    le-elt-bot  : ∀ s → le D (elt s (D .fobj s .⊥)) bot
    le-elt-join : ∀ s {x₁ x₂} → le D (elt s (D .fobj s ._∨_ x₁ x₂)) (join (elt s x₁) (elt s x₂))
    le-nat₁     : ∀ {s₁ s₂ x} (f : s₁ 𝒮.⇒ s₂) → le D (elt s₁ x) (elt s₂ (D .fmor f .fun x))
    le-nat₂     : ∀ {s₁ s₂ x} (f : s₁ 𝒮.⇒ s₂) → le D (elt s₂ (D .fmor f .fun x)) (elt s₁ x)

  ∐ : Functor 𝒮 cat → Obj
  ∐ D .carrier .Preorder.Carrier = ∐-carrier D
  ∐ D .carrier .Preorder._≤_ s t = LiftS 0ℓ (le D s t)
  ∐ D .carrier .Preorder.≤-isPreorder .IsPreorder.refl = liftS le-refl
  ∐ D .carrier .Preorder.≤-isPreorder .IsPreorder.trans (liftS ϕ₁) (liftS ϕ₂) = liftS (le-trans ϕ₁ ϕ₂)
  ∐ D .joins .JoinSemilattice._∨_ = join
  ∐ D .joins .JoinSemilattice.⊥ = bot
  ∐ D .joins .JoinSemilattice.∨-isJoin .IsJoin.inl = liftS le-upper₁
  ∐ D .joins .JoinSemilattice.∨-isJoin .IsJoin.inr = liftS le-upper₂
  ∐ D .joins .JoinSemilattice.∨-isJoin .IsJoin.[_,_] (liftS ϕ₁) (liftS ϕ₂) = liftS (le-least ϕ₁ ϕ₂)
  ∐ D .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom = liftS le-bot

  colambda-fun : (D : Functor 𝒮 cat) (X : Obj) → NatTrans D (functor.constF 𝒮 X) → ∐ D .Carrier → X .Carrier
  colambda-fun D X α bot = X .⊥
  colambda-fun D X α (join t₁ t₂) = X ._∨_ (colambda-fun D X α t₁) (colambda-fun D X α t₂)
  colambda-fun D X α (elt s x) = α .transf s .fun x

  colambda-mono : ∀ (D : Functor 𝒮 cat) (X : Obj) (α : NatTrans D (functor.constF 𝒮 X)) {t₁ t₂} →
                  le D t₁ t₂ → X ._≤_ (colambda-fun D X α t₁) (colambda-fun D X α t₂)
  colambda-mono D X α le-refl = X .≤-refl
  colambda-mono D X α (le-trans t₁≤t₂ t₂≤t₃) = X .≤-trans (colambda-mono D X α t₁≤t₂) (colambda-mono D X α t₂≤t₃)
  colambda-mono D X α le-bot = X .≤-bottom
  colambda-mono D X α le-upper₁ = X .inl
  colambda-mono D X α le-upper₂ = X .inr
  colambda-mono D X α (le-least t₁≤t₃ t₂≤t₃) = X.[ colambda-mono D X α t₁≤t₃ ∨ colambda-mono D X α t₂≤t₃ ]
    where module X = Obj X
  colambda-mono D X α (le-mono s x₁≤x₂) = α .transf s .mono x₁≤x₂
  colambda-mono D X α (le-elt-bot s) = α .transf s .⊥-preserving
  colambda-mono D X α (le-elt-join s) = α .transf s .∨-preserving
  colambda-mono D X α (le-nat₁ {x = x} f) = α .natural f .eqfun x .proj₁
  colambda-mono D X α (le-nat₂ {x = x} f) = α .natural f .eqfun x .proj₂

  colambda-cong : ∀ (D : Functor 𝒮 cat) {X : Obj} {α β} →
                  ≃-NatTrans α β → ∀ t → _≃_ X (colambda-fun D X α t) (colambda-fun D X β t)
  colambda-cong D {X} α≃β bot = X .≃-refl
  colambda-cong D {X} α≃β (join t₁ t₂) = ∨-cong X (colambda-cong D α≃β t₁) (colambda-cong D α≃β t₂)
  colambda-cong D {X} α≃β (elt s x) = α≃β .transf-eq s .eqfun x

  colambda : (D : Functor 𝒮 cat) (x : Obj) → NatTrans D (functor.constF 𝒮 x) → ∐ D ⇒ x
  colambda D X α .*→* ._=>J_.func .fun = colambda-fun D X α
  colambda D X α .*→* ._=>J_.func .mono (liftS t₁≤t₂) = colambda-mono D X α t₁≤t₂
  colambda D X α .*→* ._=>J_.∨-preserving = X .≤-refl
  colambda D X α .*→* ._=>J_.⊥-preserving = X .≤-refl

  cocone : (D : Functor 𝒮 cat) → NatTrans D (functor.constF 𝒮 (∐ D))
  cocone D .transf s .*→* ._=>J_.func .fun x = elt s x
  cocone D .transf s .*→* ._=>J_.func .mono x₁≤x₂ = liftS (le-mono s x₁≤x₂)
  cocone D .transf s .*→* ._=>J_.∨-preserving = liftS (le-elt-join s)
  cocone D .transf s .*→* ._=>J_.⊥-preserving = liftS (le-elt-bot s)
  cocone D .natural {s₁} {s₂} f .f≃f .eqfunc .eqfun x .proj₁ = liftS (le-nat₁ f)
  cocone D .natural {s₁} {s₂} f .f≃f .eqfunc .eqfun x .proj₂ = liftS (le-nat₂ f)

  colambda-ext : ∀ D X f (x : ∐-carrier D) →
      _≃_ X (colambda-fun D X (functor.constFmor f functor.∘ cocone D) x) (f .fun x)
  colambda-ext D X f bot = X .≃-sym (⊥-preserving-≃ f)
  colambda-ext D X f (join t₁ t₂) = begin
      X ._∨_ (colambda-fun D X (functor.constFmor f functor.∘ cocone D) t₁) (colambda-fun D X (functor.constFmor f functor.∘ cocone D) t₂)
    ≈⟨ ∨-cong X (colambda-ext D X f t₁) (colambda-ext D X f t₂) ⟩
      X ._∨_ (f .fun t₁) (f .fun t₂)
    ≈˘⟨ ∨-preserving-≃ f ⟩
      f .fun (join t₁ t₂)
    ∎
    where open ≈-Reasoning (isEquivalence X)
  colambda-ext D X f (elt s x) = X .≃-refl


  colimits : HasColimits 𝒮 cat
  colimits D .Colimit.apex = ∐ D
  colimits D .Colimit.cocone = cocone D
  colimits D .Colimit.isColimit .IsColimit.colambda = colambda D
  colimits D .Colimit.isColimit .IsColimit.colambda-cong α≃β .f≃f .eqfunc .eqfun = colambda-cong D α≃β
  colimits D .Colimit.isColimit .IsColimit.colambda-coeval X α .transf-eq s .f≃f .eqfunc .eqfun x = X .≃-refl
  colimits D .Colimit.isColimit .IsColimit.colambda-ext X f .f≃f .eqfunc .eqfun = colambda-ext D X f

  ------------------------------------------------------------------------------
  -- Limits

  record Π-Carrier (D : Functor 𝒮 cat) : Set where
    field
      Π-func    : (x : 𝒮.obj) → D .fobj x .Carrier
      Π-natural : ∀ {x₁ x₂} (f : x₁ 𝒮.⇒ x₂) → _≃_ (D .fobj x₂) (D .fmor f .fun (Π-func x₁)) (Π-func x₂)
  open Π-Carrier

  Π : Functor 𝒮 cat → Obj
  Π D .carrier .Preorder.Carrier = Π-Carrier D
  Π D .carrier .Preorder._≤_ α₁ α₂ = ∀ s → D .fobj s ._≤_ (α₁ .Π-func s) (α₂ .Π-func s)
  Π D .carrier .Preorder.≤-isPreorder .IsPreorder.refl s = D .fobj s .≤-refl
  Π D .carrier .Preorder.≤-isPreorder .IsPreorder.trans α≤β β≤γ s = D .fobj s .≤-trans (α≤β s) (β≤γ s)
  Π D .joins .JoinSemilattice._∨_ α₁ α₂ .Π-func s = D .fobj s ._∨_ (α₁ .Π-func s) (α₂ .Π-func s)
  Π D .joins .JoinSemilattice._∨_ α₁ α₂ .Π-natural {s₁}{s₂} f =
    S₂ .≤-trans (Df .∨-preserving)
      (S₂ .[_∨_] (S₂ .≤-trans (proj₁ (α₁ .Π-natural f)) (S₂ .inl))
                  (S₂ .≤-trans (proj₁ (α₂ .Π-natural f)) (S₂ .inr))) ,
    S₂ .[_∨_] (S₂ .≤-trans (proj₂ (α₁ .Π-natural f)) (Df .mono (D .fobj s₁ .inl)))
              (S₂ .≤-trans (proj₂ (α₂ .Π-natural f)) (Df .mono (D .fobj s₁ .inr)))
    where S₂ = D .fobj s₂; Df = D .fmor f
  Π D .joins .JoinSemilattice.⊥ .Π-func s = D .fobj s .⊥
  Π D .joins .JoinSemilattice.⊥ .Π-natural {s₁}{s₂} f = D .fmor f .⊥-preserving , D .fobj s₂ .≤-bottom
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.inl s = D .fobj s .inl
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.inr s = D .fobj s .inr
  Π D .joins .JoinSemilattice.∨-isJoin .IsJoin.[_,_] α≤β α≤γ s = D .fobj s .[_∨_] (α≤β s) (α≤γ s)
  Π D .joins .JoinSemilattice.⊥-isBottom .IsBottom.≤-bottom s = D .fobj s .≤-bottom

coproducts : HasCoproducts cat
coproducts .HasCoproducts.coprod X Y .carrier = X .carrier × Y .carrier
coproducts .HasCoproducts.coprod X Y .joins = X .joins ⊕J Y .joins
coproducts .HasCoproducts.in₁ .*→* = join-semilattice.inject₁
coproducts .HasCoproducts.in₂ .*→* = join-semilattice.inject₂
coproducts .HasCoproducts.copair f g .*→* = join-semilattice.[ (f .*→*) , (g .*→*) ]
coproducts .HasCoproducts.copair-cong eq₁ eq₂ .f≃f = join-semilattice.[]-cong (eq₁ .f≃f) (eq₂ .f≃f)
coproducts .HasCoproducts.copair-in₁ f g .f≃f = join-semilattice.inj₁-copair (f .*→*) (g .*→*)
coproducts .HasCoproducts.copair-in₂ f g .f≃f = join-semilattice.inj₂-copair (f .*→*) (g .*→*)
coproducts .HasCoproducts.copair-ext f .f≃f = join-semilattice.copair-ext (f .*→*)

products : HasProducts cat
products .HasProducts.prod X Y .carrier = X .carrier × Y .carrier
products .HasProducts.prod X Y .joins = X .joins ⊕J Y .joins
products .HasProducts.p₁ .*→* = join-semilattice.project₁
products .HasProducts.p₂ .*→* = join-semilattice.project₂
products .HasProducts.pair f g .*→* = join-semilattice.⟨ (f .*→*) , (g .*→*) ⟩
products .HasProducts.pair-cong eq₁ eq₂ .f≃f = join-semilattice.⟨⟩-cong (eq₁ .f≃f) (eq₂ .f≃f)
products .HasProducts.pair-p₁ f g .f≃f = join-semilattice.pair-p₁ (f .*→*) (g .*→*)
products .HasProducts.pair-p₂ f g .f≃f = join-semilattice.pair-p₂ (f .*→*) (g .*→*)
products .HasProducts.pair-ext f .f≃f = join-semilattice.pair-ext (f .*→*)

initial : HasInitial cat
initial .HasInitial.witness = record { joins = 𝟙 }
initial .HasInitial.is-initial .categories.IsInitial.from-initial .*→* = join-semilattice.initial
initial .HasInitial.is-initial .categories.IsInitial.from-initial-ext f .f≃f = join-semilattice.initial-unique _ _ _

terminal : HasTerminal cat
terminal .HasTerminal.witness = record { joins = 𝟙 }
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal .*→* = join-semilattice.terminal
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal-ext f .f≃f = join-semilattice.terminal-unique _ _ _

TWO : Obj
TWO .carrier .Preorder.Carrier = two.Two
TWO .carrier .Preorder._≤_ = two._≤_
TWO .carrier .Preorder.≤-isPreorder = two.≤-isPreorder
TWO .joins .JoinSemilattice._∨_ = two._⊔_
TWO .joins .JoinSemilattice.⊥ = two.O
TWO .joins .JoinSemilattice.∨-isJoin = two.⊔-isJoin
TWO .joins .JoinSemilattice.⊥-isBottom = two.O-isBottom
