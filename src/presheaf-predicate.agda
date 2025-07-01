{-# OPTIONS --postfix-projections --prop --allow-unsolved-metas #-}

open import Level using (_⊔_; suc)
open import Data.Product using (_,_) renaming (_×_ to _××_)
open import prop using (_,_; tt; ∃; _∧_; LiftS; liftS)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; module ≤-Reasoning; monoidOfMeet; IsJoin; IsClosureOp)
open import prop-setoid using (Setoid)
  renaming (_⇒_ to _⇒s_)
open import categories using (Category; HasProducts; HasTerminal; IsTerminal; HasCoproducts)
open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)
open import functor using (Functor; [_⇒_]; NatTrans; ≃-NatTrans)
open import predicate-system using (PredicateSystem; ClosureOp)
import setoid-predicate

module presheaf-predicate {o m e} os (𝒞 : Category o m e) where

open import yoneda os 𝒞

private
  ℓ = o ⊔ m ⊔ e ⊔ os
  module P = PredicateSystem (setoid-predicate.system {ℓ} {ℓ})
  module S = Category (SetoidCat ℓ ℓ)
  module SP = HasProducts (Setoid-products ℓ ℓ)
  module 𝒞 = Category 𝒞
  module PSh = Category PSh
  module PShP = HasProducts products

open Functor
open NatTrans
open ≃-NatTrans

record Predicate (X : PSh.obj) : Set (suc (suc ℓ)) where
  no-eta-equality
  field
    pred : ∀ a → P.Predicate (X .fobj a)
    pred-mor : ∀ {a b} (f : b 𝒞.⇒ a) → pred a P.⊑ (pred b P.[ X .fmor f ])
open Predicate

-- pred a : Predicate (X .fobj a)
-- pred b : Predicate (X .fobj b)

-- pred a ⟨ X .fmor CP.in₁ ⟩ : Predicate (X .fobj (CP.coprod a b))
-- pred (CP.coprod a b) : Predicate (X .fobj (CP.coprod a b))

record _⊑_ {X : PSh.obj} (P Q : Predicate X) : Prop (suc ℓ) where
  no-eta-equality
  field
    *⊑* : ∀ a → P .pred a P.⊑ Q .pred a
open _⊑_

infix 2 _⊑_

⊑-isPreorder : ∀ {X} → IsPreorder (_⊑_ {X})
⊑-isPreorder .IsPreorder.refl .*⊑* x = P.⊑-isPreorder .IsPreorder.refl
⊑-isPreorder .IsPreorder.trans ϕ ψ .*⊑* x = P.⊑-isPreorder .IsPreorder.trans (ϕ .*⊑* x) (ψ .*⊑* x)

_[_] : ∀ {X Y} → Predicate Y → X PSh.⇒ Y → Predicate X
(P [ α ]) .pred a = (P .pred a) P.[ α .transf a ]
_[_] {X} {Y} P α .pred-mor {a} {b} f = begin
    (P .pred a) P.[ α .transf a ]
  ≤⟨ P .pred-mor f P.[ α .transf a ]m ⟩
    (P .pred b) P.[ Y .fmor f ] P.[ α .transf a ]
  ≤⟨ P.[]-comp _ _ ⟩
    (P .pred b) P.[ Y .fmor f S.∘ α .transf a ]
  ≤⟨ P.[]-cong (α .natural f) ⟩
    (P .pred b) P.[ α .transf b S.∘ X .fmor f ]
  ≤⟨ P.[]-comp⁻¹ _ _ ⟩
    (P .pred b P.[ α .transf b ]) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

_⟨_⟩ : ∀ {X Y} → Predicate X → X PSh.⇒ Y → Predicate Y
_⟨_⟩ {X} {Y} P α .pred a = P .pred a P.⟨ α .transf a ⟩
_⟨_⟩ {X} {Y} P α .pred-mor {a} {b} f =
  P.adjoint₂ (begin
    P .pred a
  ≤⟨ P .pred-mor f ⟩
    P .pred b P.[ X .fmor f ]
  ≤⟨ P.unit _ P.[ _ ]m ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ α .transf b ] P.[ X .fmor f ]
  ≤⟨ P.[]-comp _ _ ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ α .transf b S.∘ X .fmor f ]
  ≤⟨ P.[]-cong (S.≈-sym (α .natural f)) ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ Y .fmor f S.∘ α .transf a ]
  ≤⟨ P.[]-comp⁻¹ _ _ ⟩
    (P .pred b P.⟨ α .transf b ⟩) P.[ Y .fmor f ] P.[ α .transf a ]
  ∎)
  where open ≤-Reasoning P.⊑-isPreorder

_[_]m     : ∀ {X Y} {P Q : Predicate Y} → P ⊑ Q → (f : X PSh.⇒ Y) → (P [ f ]) ⊑ (Q [ f ])
_[_]m {X} {Y} {P} {Q} P⊑Q f .*⊑* x = P⊑Q .*⊑* x P.[ _ ]m

[]-cong : ∀ {X Y} {P : Predicate Y}{f₁ f₂ : X PSh.⇒ Y} → f₁ PSh.≈ f₂ → (P [ f₁ ]) ⊑ (P [ f₂ ])
[]-cong f₁≈f₂ .*⊑* x = P.[]-cong (f₁≈f₂ .transf-eq x)

[]-id : ∀ {X} {P : Predicate X} → P ⊑ (P [ PSh.id _ ])
[]-id .*⊑* x = P.[]-id

[]-id⁻¹ : ∀ {X} {P : Predicate X} → (P [ PSh.id _ ]) ⊑ P
[]-id⁻¹ .*⊑* x = P.[]-id⁻¹

[]-comp : ∀ {X Y Z} {P : Predicate Z} (f : Y PSh.⇒ Z) (g : X PSh.⇒ Y) → ((P [ f ]) [ g ]) ⊑ (P [ f PSh.∘ g ])
[]-comp α β .*⊑* x = P.[]-comp _ _

[]-comp⁻¹ : ∀ {X Y Z} {P : Predicate Z} (f : Y PSh.⇒ Z) (g : X PSh.⇒ Y) → (P [ f PSh.∘ g ]) ⊑ ((P [ f ]) [ g ])
[]-comp⁻¹ f g .*⊑* x = P.[]-comp⁻¹ _ _

adjoint₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X PSh.⇒ Y} → P ⟨ f ⟩ ⊑ Q → P ⊑ Q [ f ]
adjoint₁ ϕ .*⊑* x = P.adjoint₁ (ϕ .*⊑* x)

adjoint₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {f : X PSh.⇒ Y} → P ⊑ Q [ f ] → P ⟨ f ⟩ ⊑ Q
adjoint₂ ϕ .*⊑* x = P.adjoint₂ (ϕ .*⊑* x)


open IsMeet

TT : ∀ {X} → Predicate X
TT .pred x = P.TT
TT .pred-mor f = P.[]-TT

TT-isTop : ∀ {X} → IsTop (⊑-isPreorder {X}) TT
TT-isTop .IsTop.≤-top .*⊑* a = P.TT-isTop .IsTop.≤-top

_&&_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P && Q) .pred x = (P .pred x) P.&& (Q .pred x)
_&&_ {X} P Q .pred-mor {x} {y} f = begin
    P .pred x P.&& Q .pred x
  ≤⟨ mono P.&&-isMeet (P .pred-mor f) (Q .pred-mor f) ⟩
    ((P .pred y) P.[ X .fmor f ]) P.&& ((Q .pred y) P.[ X .fmor f ])
  ≤⟨ P.[]-&& ⟩
    (P .pred y P.&& Q .pred y) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

&&-isMeet : ∀ {X} → IsMeet (⊑-isPreorder {X}) _&&_
&&-isMeet .π₁ .*⊑* a = P.&&-isMeet .π₁
&&-isMeet .π₂ .*⊑* a = P.&&-isMeet .π₂
&&-isMeet .⟨_,_⟩ ϕ ψ .*⊑* a = P.&&-isMeet .⟨_,_⟩ (ϕ .*⊑* a) (ψ .*⊑* a)

_++_ : ∀ {X} → Predicate X → Predicate X → Predicate X
(P ++ Q) .pred x = P .pred x P.++ Q .pred x
_++_ {X} P Q .pred-mor {a} {b} f = begin
    P .pred a P.++ Q .pred a
  ≤⟨ IsJoin.mono P.++-isJoin (P .pred-mor f) (Q .pred-mor f) ⟩
    (P .pred b P.[ X .fmor f ]) P.++ (Q .pred b P.[ X .fmor f ])
  ≤⟨ IsJoin.[_,_] P.++-isJoin ((IsJoin.inl P.++-isJoin) P.[ _ ]m) ((IsJoin.inr P.++-isJoin) P.[ _ ]m) ⟩
    (P .pred b P.++ Q .pred b) P.[ X .fmor f ]
  ∎
  where open ≤-Reasoning P.⊑-isPreorder

++-isJoin : ∀ {X} → IsJoin (⊑-isPreorder {X}) _++_
++-isJoin .IsJoin.inl .*⊑* a = P.++-isJoin .IsJoin.inl
++-isJoin .IsJoin.inr .*⊑* a = P.++-isJoin .IsJoin.inr
++-isJoin .IsJoin.[_,_] ϕ ψ .*⊑* a = IsJoin.[_,_] P.++-isJoin (ϕ .*⊑* a) (ψ .*⊑* a)

[]-++ : ∀ {X Y} {P Q : Predicate Y} {f : X PSh.⇒ Y} → ((P ++ Q) [ f ]) ⊑ ((P [ f ]) ++ (Q [ f ]))
[]-++ .*⊑* a = record { *⊑* = λ x z → z }

open setoid-predicate.Predicate
open setoid-predicate._⊑_
open prop-setoid.Setoid
open prop-setoid._⇒_
open prop-setoid._≃m_

_==>_ : ∀ {X} → Predicate X → Predicate X → Predicate X
_==>_ {X} P Q .pred a .pred x =
  ∀ b (f : b 𝒞.⇒ a) → P .pred b .pred (X .fmor f .func x) → Q .pred b .pred (X .fmor f .func x)
_==>_ {X} P Q .pred a .pred-≃ x₁≈x₂ ϕ b f p =
  Q .pred b .pred-≃ (X .fmor f .func-resp-≈ x₁≈x₂)
    (ϕ b f (P .pred b .pred-≃ (X .fobj b .sym (X .fmor f .func-resp-≈ x₁≈x₂)) p))
_==>_ {X} P Q .pred-mor {a} {b} f .*⊑* x ϕ c g p =
  Q .pred c .pred-≃ (X .fmor-comp g f .func-eq (X .fobj a .refl))
    (ϕ c (f 𝒞.∘ g) (P .pred c .pred-≃ (X .fobj c .sym (X .fmor-comp g f .func-eq (X .fobj a .refl))) p))

[]-==> : ∀ {X Y}{P Q : Predicate Y}{f : X PSh.⇒ Y} → ((P [ f ]) ==> (Q [ f ])) ⊑ (P ==> Q) [ f ]
[]-==> {X}{Y}{P}{Q}{α} .*⊑* a .*⊑* x ϕ b f p =
  Q .pred b .pred-≃ (Y .fobj b .sym (α .natural f .func-eq (X .fobj a .refl)))
    (ϕ b f (P .pred b .pred-≃ (α .natural f .func-eq (X .fobj a .refl)) p))

==>-residual : ∀ {X} → IsResidual ⊑-isPreorder (monoidOfMeet _ &&-isMeet TT-isTop) (_==>_ {X})
==>-residual {X} .IsResidual.lambda {P}{Q}{R} Φ .*⊑* a .*⊑* x p b f q =
  Φ .*⊑* b .*⊑* (X .fmor f .func x) (P .pred-mor f .*⊑* x p , q)
==>-residual {X} .IsResidual.eval {P} {Q} .*⊑* a .*⊑* x (ϕ , p) =
  Q .pred a .pred-≃ (X .fmor-id .func-eq (X .fobj a .refl))
    (ϕ a (𝒞.id _) (P .pred a .pred-≃ (X .fobj a .sym (X .fmor-id .func-eq (X .fobj a .refl))) p))

⋀ : ∀ {X Y} → Predicate (X × Y) → Predicate X
⋀ {X} {Y} P .pred a .pred x = ∀ b (f : b 𝒞.⇒ a) y → P .pred b .pred (X .fmor f .func x , y)
⋀ {X} {Y} P .pred a .pred-≃ x₁≈x₂ ϕ b f y =
  P .pred b .pred-≃ (X .fmor f .func-resp-≈ x₁≈x₂ , Y .fobj b .refl) (ϕ b f y)
⋀ {X} {Y} P .pred-mor {a} {b} f .*⊑* x ϕ c g y =
  P .pred c .pred-≃ (X .fmor-comp _ _ .func-eq (X .fobj a .refl) , Y .fobj c .refl) (ϕ c (f 𝒞.∘ g) y)

⋀-[] : ∀ {X X' Y} {P : Predicate (PShP.prod X Y)} {α : X' PSh.⇒ X} →
       (⋀ (P [ PShP.prod-m α (PSh.id _) ])) ⊑ (⋀ P) [ α ]
⋀-[] {X} {X'} {Y} {P} {α} .*⊑* a .*⊑* x ϕ b f y =
  P .pred b .pred-≃ (X .fobj b .sym (α .natural f .func-eq (X' .fobj a .refl)) , Y .fobj b .refl)
    (ϕ b f y)

⋀-eval : ∀ {X Y} {P : Predicate (PShP.prod X Y)} → ((⋀ P) [ PShP.p₁ ]) ⊑ P
⋀-eval {X} {Y} {P} .*⊑* a .*⊑* (x , y) ϕ =
  P .pred a .pred-≃ (X .fmor-id .func-eq (X .fobj a .refl) , Y .fobj a .refl) (ϕ a (𝒞.id _) y)

⋀-lambda : ∀ {X Y} {P : Predicate X} {Q : Predicate (PShP.prod X Y)} → P [ PShP.p₁ ] ⊑ Q → P ⊑ ⋀ Q
⋀-lambda {X} {Y} {P} {Q} Φ .*⊑* a .*⊑* x p b f y =
  Φ .*⊑* b .*⊑* (X .fmor f .func x , y) (P .pred-mor f .*⊑* x p)


system : PredicateSystem PSh products
system .PredicateSystem.Predicate = Predicate
system .PredicateSystem._⊑_ = _⊑_
system .PredicateSystem.⊑-isPreorder = ⊑-isPreorder
system .PredicateSystem._[_] = _[_]
system .PredicateSystem._⟨_⟩ = _⟨_⟩
system .PredicateSystem._[_]m = _[_]m
system .PredicateSystem.[]-cong = []-cong
system .PredicateSystem.[]-id = []-id
system .PredicateSystem.[]-id⁻¹ = []-id⁻¹
system .PredicateSystem.[]-comp = []-comp
system .PredicateSystem.[]-comp⁻¹ = []-comp⁻¹
system .PredicateSystem.adjoint₁ = adjoint₁
system .PredicateSystem.adjoint₂ = adjoint₂
system .PredicateSystem.TT = TT
system .PredicateSystem._&&_ = _&&_
system .PredicateSystem._++_ = _++_
system .PredicateSystem._==>_ = _==>_
system .PredicateSystem.⋀ {X} {Y} P = ⋀ {X} {Y} P
system .PredicateSystem.TT-isTop = TT-isTop
system .PredicateSystem.[]-TT = record { *⊑* = λ a → record { *⊑* = λ x _ → tt } }
system .PredicateSystem.&&-isMeet = &&-isMeet
system .PredicateSystem.[]-&& = record { *⊑* = λ a → record { *⊑* = λ x z → z } }
system .PredicateSystem.==>-residual = ==>-residual
system .PredicateSystem.[]-==> = []-==>
system .PredicateSystem.[]-++ = []-++
system .PredicateSystem.++-isJoin = ++-isJoin
system .PredicateSystem.⋀-[] = ⋀-[]
system .PredicateSystem.⋀-eval = ⋀-eval
system .PredicateSystem.⋀-lambda = ⋀-lambda

-- Coproduct closure
--
-- This requires the following stability property of the coproducts in 𝒞
--
-- FIXME: is the the same thing as extensive coproducts?
--
-- f : X₁ + X₂ ⇒ X
-- g : Y ⇒ X
--
-- Let Y₁ = { (y , x₁) | f(in₁ x₁) = g(y) }
-- Let Y₂ = { (y , x₂) | f(in₂ x₂) = g(y) }

record StableBits (𝒞CP : HasCoproducts 𝒞)
                  {x₁ x₂ x y}
                  (f : 𝒞.Iso (𝒞CP .HasCoproducts.coprod x₁ x₂) x)
                  (g : y 𝒞.⇒ x) : Set (o ⊔ m ⊔ e) where
  private
    module 𝒞CP = HasCoproducts 𝒞CP
  open 𝒞.Iso
  field
    y₁  : 𝒞.obj
    y₂  : 𝒞.obj
    h₁  : y₁ 𝒞.⇒ x₁
    h₂  : y₂ 𝒞.⇒ x₂
    h   : 𝒞.Iso (𝒞CP.coprod y₁ y₂) y
    eq₁ : (f .fwd 𝒞.∘ (𝒞CP.in₁ 𝒞.∘ h₁)) 𝒞.≈ (g 𝒞.∘ (h .fwd 𝒞.∘ 𝒞CP.in₁))
    eq₂ : (f .fwd 𝒞.∘ (𝒞CP.in₂ 𝒞.∘ h₂)) 𝒞.≈ (g 𝒞.∘ (h .fwd 𝒞.∘ 𝒞CP.in₂))

module CoproductMonad
         (𝒞CP : HasCoproducts 𝒞)
         (stable : ∀ {x₁ x₂ x y} f g → StableBits 𝒞CP {x₁} {x₂} {x} {y} f g)
         where

  private
    module 𝒞CP = HasCoproducts 𝒞CP

  open Setoid
  open _⇒s_
  open setoid-predicate.Predicate
  open setoid-predicate._⊑_
  open 𝒞.Iso

  data Context (X : PSh.obj) (P : Predicate X) : (a : 𝒞.obj) → X .fobj a .Carrier → Set ℓ where
    leaf : ∀ {a x} → P .pred a .pred x → Context X P a x
    node : ∀ a b {c} x y {z} (f : 𝒞.Iso (𝒞CP.coprod a b) c) →
           Context X P a x →
           Context X P b y →
           X .fobj a ._≈_ x (X .fmor (f .fwd 𝒞.∘ 𝒞CP.in₁) .func z) →
           X .fobj b ._≈_ y (X .fmor (f .fwd 𝒞.∘ 𝒞CP.in₂) .func z) →
           Context X P c z

  Context-reindex : ∀ {X : PSh.obj} (P : Predicate X) →
                    ∀ {a b} {x} (f : b 𝒞.⇒ a) → Context X P a x → Context X P b (X .fmor f .func x)
  Context-reindex {X} P {a} {b} {x} f (leaf p) =
    leaf (P .pred-mor f .*⊑* x p)
  Context-reindex {X} P {a} {b} {x} f (node a₁ a₂ y₁ y₂ g t₁ t₂ eq₁ eq₂) =
    node (stbl .StableBits.y₁) (stbl .StableBits.y₂)
         (X .fmor (stbl .StableBits.h₁) .func y₁)
         (X .fmor (stbl .StableBits.h₂) .func y₂)
         (stbl .StableBits.h)
         (Context-reindex P (stbl .StableBits.h₁) t₁)
         (Context-reindex P (stbl .StableBits.h₂) t₂)
         {!!}
         {!!}
    where stbl = stable g f

  Context-eq : ∀ {X} {P : Predicate X} {a x₁ x₂} → X .fobj a ._≈_ x₁ x₂ → Context X P a x₁ → Context X P a x₂
  Context-eq {X} {P} x₁≈x₂ (leaf p) = leaf (P .pred _ .pred-≃ x₁≈x₂ p)
  Context-eq {X} {P} x₁≈x₂ (node a b x y f t₁ t₂ eq₁ eq₂) =
    node a b x y f t₁ t₂
         (X .fobj a .trans eq₁ (X .fmor _ .func-resp-≈ x₁≈x₂))
         (X .fobj b .trans eq₂ (X .fmor _ .func-resp-≈ x₁≈x₂))

  𝐂 : ∀ {X} → Predicate X → Predicate X
  𝐂 P .pred a .pred x = LiftS ℓ (Context _ P a x)
  𝐂 P .pred a .pred-≃ x₁≈x₂ (liftS t) = liftS (Context-eq x₁≈x₂ t)
  𝐂 P .pred-mor f .*⊑* x (liftS p) = liftS (Context-reindex P f p)

  Context-unit : ∀ {X : PSh.obj} {P : Predicate X} →
                 ∀ {a x} → P .pred a .pred x → Context X P a x
  Context-unit p = leaf p

  Context-mono : ∀ {X : PSh.obj} {P Q : Predicate X} →
                 ∀ (P⊑Q : P ⊑ Q) →
                 ∀ {a x} → Context X P a x → Context X Q a x
  Context-mono P⊑Q (leaf p) = leaf (P⊑Q .*⊑* _ .*⊑* _ p)
  Context-mono P⊑Q (node a b x y f t t₁ x₁ x₂) = node a b x y f (Context-mono P⊑Q t) (Context-mono P⊑Q t₁) x₁ x₂

  Context-strong : ∀ {X : PSh.obj} {P Q : Predicate X} →
                   ∀ {a x} → Context X P a x → Q .pred a .pred x → Context X (P && Q) a x
  Context-strong (leaf p) q = leaf (p , q)
  Context-strong {X} {P} {Q} (node a b x y f t₁ t₂ eq₁ eq₂) q =
    node a b x y f
         (Context-strong t₁ (Q .pred a .pred-≃ (X .fobj a .sym eq₁) (Q .pred-mor (f .fwd 𝒞.∘ 𝒞CP.in₁) .*⊑* _ q)))
         (Context-strong t₂ (Q .pred b .pred-≃ (X .fobj b .sym eq₂) (Q .pred-mor (f .fwd 𝒞.∘ 𝒞CP.in₂) .*⊑* _ q)))
         eq₁
         eq₂

  Context-join : ∀ {X : PSh.obj} {P : Predicate X} →
                 ∀ {a x} → Context X (𝐂 P) a x → LiftS ℓ (Context X P a x)
  Context-join {X} {P} {a} {x} (leaf (liftS t)) = liftS t
  Context-join {X} {P} {a} {x} (node a₁ b x₁ y f t₁ t₂ eq₁ eq₂) with Context-join t₁
  ... | liftS t₁' with Context-join t₂
  ... | liftS t₂' = liftS (node a₁ b x₁ y f t₁' t₂' eq₁ eq₂)

  𝐂-isClosure : ∀ {X} → IsClosureOp (⊑-isPreorder {X}) 𝐂
  𝐂-isClosure .IsClosureOp.mono P⊑Q .*⊑* a .*⊑* x (liftS p) = liftS (Context-mono P⊑Q p)
  𝐂-isClosure .IsClosureOp.unit .*⊑* a .*⊑* x p = liftS (Context-unit p)
  𝐂-isClosure .IsClosureOp.closed .*⊑* a .*⊑* x (liftS p) = Context-join p

  𝐂-strong : ∀ {X} {P Q : Predicate X} → (𝐂 P && Q) ⊑ 𝐂 (P && Q)
  𝐂-strong .*⊑* a .*⊑* x (liftS p , q) = liftS (Context-strong p q)

  𝐂-[]⁻¹ : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} → (𝐂 P [ f ]) ⊑ 𝐂 (P [ f ])
  𝐂-[]⁻¹ .*⊑* a .*⊑* x (liftS (leaf p)) = liftS (leaf p)
  𝐂-[]⁻¹ {X} {Y} {P} {f} .*⊑* a .*⊑* x (liftS (node a₁ a₂ y₁ y₂ g t₁ t₂ eq₁ eq₂)) = {!!}
    -- liftS (node a₁ a₂
    --             (X .fmor (g 𝒞.∘ 𝒞CP.in₁) .func x)
    --             (X .fmor (g 𝒞.∘ 𝒞CP.in₂) .func x)
    --             g
    --             {!𝐂-[]⁻¹ {f = f} .*⊑* a₁ .*⊑* (X .fmor (g 𝒞.∘ 𝒞CP.in₁) .func x) (liftS ?)!}
    --             {!!}
    --             {!!}
    --             {!!})

  𝐂-[] : ∀ {X Y} {P : Predicate Y} {f : X PSh.⇒ Y} → 𝐂 (P [ f ]) ⊑ (𝐂 P [ f ])
  𝐂-[] = {!!}

  closureOp : ClosureOp PSh products system
  closureOp .ClosureOp.𝐂 = 𝐂
  closureOp .ClosureOp.𝐂-isClosure = 𝐂-isClosure
  closureOp .ClosureOp.𝐂-[] = 𝐂-[]
  closureOp .ClosureOp.𝐂-[]⁻¹ = 𝐂-[]⁻¹
  closureOp .ClosureOp.𝐂-strong = 𝐂-strong
