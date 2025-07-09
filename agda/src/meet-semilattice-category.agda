{-# OPTIONS --postfix-projections --prop --safe #-}

-- Category of meet semilattices and meet preserving morphisms, which
-- is complete and CMon-enriched.

module meet-semilattice-category where

open import Level using (suc; 0ℓ)
open import prop using (proj₁; proj₂)
open import prop-setoid using (IsEquivalence; module ≈-Reasoning)
open import basics using (IsPreorder; IsTop; IsMeet)
open import preorder using (Preorder; _×_)
open import meet-semilattice
  using ( MeetSemilattice
        ; εm; _+m_; +m-cong; +m-comm; +m-assoc; +m-lunit
        ; comp-bilinear₁; comp-bilinear₂; comp-bilinear-ε₁; comp-bilinear-ε₂; 𝟙)
  renaming (_=>_ to _=>M_; _≃m_ to _≃M_; id to idM; _∘_ to _∘M_;
            _⊕_ to _⊕M_;
            ≃m-isEquivalence to ≃M-isEquivalence)
open import categories using (Category; HasProducts; HasTerminal)
open import functor using (IsLimit; Limit; HasLimits; Functor; NatTrans; ≃-NatTrans)
import two

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
  open Preorder carrier public
  open MeetSemilattice meets public
open Obj

record _⇒_ (X Y : Obj) : Set where
  no-eta-equality
  field
    *→* : X .meets =>M Y .meets
  open _=>M_ *→* public
  open preorder._=>_ func public
open _⇒_

record _≃m_ {X Y : Obj} (f g : X ⇒ Y) : Prop where
  no-eta-equality
  field
    f≃f : f .*→* ≃M g .*→*
  open _≃M_ f≃f public
  open preorder._≃m_ eqfunc public
open _≃m_

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv .IsEquivalence.refl .f≃f = ≃M-isEquivalence .IsEquivalence.refl
cat .Category.isEquiv .IsEquivalence.sym f≃g .f≃f = ≃M-isEquivalence .IsEquivalence.sym (f≃g .f≃f)
cat .Category.isEquiv .IsEquivalence.trans f≃g g≃h .f≃f =
  ≃M-isEquivalence .IsEquivalence.trans (f≃g .f≃f) (g≃h .f≃f)
cat .Category.id X .*→* = idM
cat .Category._∘_ f g .*→* = f .*→* ∘M g .*→*
cat .Category.∘-cong f₁≃f₂ g₁≃g₂ .f≃f = meet-semilattice.∘-cong (f₁≃f₂ .f≃f) (g₁≃g₂ .f≃f)
cat .Category.id-left .f≃f = meet-semilattice.id-left
cat .Category.id-right .f≃f = meet-semilattice.id-right
cat .Category.assoc f g h .f≃f = meet-semilattice.assoc (f .*→*) (g .*→*) (h .*→*)

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
-- Limits

module _ (𝒮 : Category 0ℓ 0ℓ 0ℓ) where

  private
    module 𝒮 = Category 𝒮

  open Functor
  open NatTrans
  open ≃-NatTrans
  open _≃M_
  open preorder._=>_
  open preorder._≃m_

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
  Π D .meets .MeetSemilattice._∧_ α₁ α₂ .Π-func s = D .fobj s ._∧_ (α₁ .Π-func s) (α₂ .Π-func s)
  Π D .meets .MeetSemilattice._∧_ α₁ α₂ .Π-natural {s₁}{s₂} f = begin
      D .fmor f .fun (D .fobj s₁ ._∧_ (α₁ .Π-func s₁) (α₂ .Π-func s₁))
    ≈˘⟨ ∧-preserving-≃ (D .fmor f) ⟩
      D .fobj s₂ ._∧_ (D .fmor f .fun (α₁ .Π-func s₁)) (D .fmor f .fun (α₂ .Π-func s₁))
    ≈⟨ ∧-cong (D .fobj s₂) (α₁ .Π-natural f) (α₂ .Π-natural f) ⟩
      D .fobj s₂ ._∧_ (α₁ .Π-func s₂) (α₂ .Π-func s₂)
    ∎ where open ≈-Reasoning (isEquivalence (D .fobj s₂))
  Π D .meets .MeetSemilattice.⊤ .Π-func s = D .fobj s .⊤
  Π D .meets .MeetSemilattice.⊤ .Π-natural {s₁}{s₂} f = ≃-sym (D .fobj s₂) (⊤-preserving-≃ (D .fmor f))
  Π D .meets .MeetSemilattice.∧-isMeet .IsMeet.π₁ s = D .fobj s .∧-isMeet .IsMeet.π₁
  Π D .meets .MeetSemilattice.∧-isMeet .IsMeet.π₂ s = D .fobj s .∧-isMeet .IsMeet.π₂
  Π D .meets .MeetSemilattice.∧-isMeet .IsMeet.⟨_,_⟩ α≤β α≤γ s = D .fobj s .∧-isMeet .IsMeet.⟨_,_⟩ (α≤β s) (α≤γ s)
  Π D .meets .MeetSemilattice.⊤-isTop .IsTop.≤-top s = D .fobj s .⊤-isTop .IsTop.≤-top

  limits : HasLimits 𝒮 cat
  limits D .Limit.apex = Π D
  limits D .Limit.cone .transf x .*→* ._=>M_.func .fun α = α .Π-func x
  limits D .Limit.cone .transf x .*→* ._=>M_.func .mono α₁≤α₂ = α₁≤α₂ x
  limits D .Limit.cone .transf x .*→* ._=>M_.∧-preserving = D .fobj x .≤-refl
  limits D .Limit.cone .transf x .*→* ._=>M_.⊤-preserving = D .fobj x .≤-refl
  limits D .Limit.cone .natural {x} {y} f .f≃f .eqfunc .eqfun α = α .Π-natural f
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>M_.func .fun x .Π-func s = α .transf s .fun x
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>M_.func .fun x .Π-natural f = α .natural f .eqfun x
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>M_.func .mono x₁≤x₂ s = α .transf s .mono x₁≤x₂
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>M_.∧-preserving s = α .transf s .∧-preserving
  limits D .Limit.isLimit .IsLimit.lambda X α .*→* ._=>M_.⊤-preserving s = α .transf s .⊤-preserving
  limits D .Limit.isLimit .IsLimit.lambda-cong α≃β .f≃f .eqfunc .eqfun x .proj₁ s = α≃β .transf-eq s .eqfun x .proj₁
  limits D .Limit.isLimit .IsLimit.lambda-cong α≃β .f≃f .eqfunc .eqfun x .proj₂ s = α≃β .transf-eq s .eqfun x .proj₂
  limits D .Limit.isLimit .IsLimit.lambda-eval {X} α .transf-eq s .f≃f .eqfunc .eqfun x = D .fobj s .≃-refl
  limits D .Limit.isLimit .IsLimit.lambda-ext {X} f .f≃f .eqfunc .eqfun x .proj₁ s = D .fobj s .≤-refl
  limits D .Limit.isLimit .IsLimit.lambda-ext {X} f .f≃f .eqfunc .eqfun x .proj₂ s = D .fobj s .≤-refl

-- Do products and terminal object directly to get a nicer representation
products : HasProducts cat
products .HasProducts.prod X Y .carrier = X .carrier × Y .carrier
products .HasProducts.prod X Y .meets = X .meets ⊕M Y .meets
products .HasProducts.p₁ .*→* = meet-semilattice.project₁
products .HasProducts.p₂ .*→* = meet-semilattice.project₂
products .HasProducts.pair f g .*→* = meet-semilattice.⟨ (f .*→*) , (g .*→*) ⟩
products .HasProducts.pair-cong eq₁ eq₂ .f≃f = meet-semilattice.⟨⟩-cong (eq₁ .f≃f) (eq₂ .f≃f)
products .HasProducts.pair-p₁ f g .f≃f = meet-semilattice.pair-p₁ (f .*→*) (g .*→*)
products .HasProducts.pair-p₂ f g .f≃f = meet-semilattice.pair-p₂ (f .*→*) (g .*→*)
products .HasProducts.pair-ext f .f≃f = meet-semilattice.pair-ext (f .*→*)

terminal : HasTerminal cat
terminal .HasTerminal.witness = record { meets = 𝟙 }
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal .*→* = meet-semilattice.terminal
terminal .HasTerminal.is-terminal .categories.IsTerminal.to-terminal-ext f .f≃f =
  meet-semilattice.terminal-unique _ _ _

-- = limits→products cat (limits product-diagram.cat)
--   where open import product-diagram using (limits→products)

TWO : Obj
TWO .carrier .Preorder.Carrier = two.Two
TWO .carrier .Preorder._≤_ = two._≤_
TWO .carrier .Preorder.≤-isPreorder = two.≤-isPreorder
TWO .meets .MeetSemilattice._∧_ = two._⊓_
TWO .meets .MeetSemilattice.⊤ = two.I
TWO .meets .MeetSemilattice.∧-isMeet = two.⊓-isMeet
TWO .meets .MeetSemilattice.⊤-isTop .IsTop.≤-top = two.I-top
