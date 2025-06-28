{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (_⊔_; suc)
open import Data.Product using (_,_)
open import prop using (_,_; tt)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; module ≤-Reasoning; monoidOfMeet)
open import prop-setoid using (Setoid)
open import categories using (Category; HasProducts; HasCoproducts; HasTerminal; IsTerminal)
open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)
open import functor using (Functor; [_⇒_]; NatTrans; ≃-NatTrans)
open import predicate-system using (PredicateSystem)
import setoid-predicate

module presheaf-predicate {o m e} os (𝒞 : Category o m e) where

open import yoneda os 𝒞

private
  ℓ = o ⊔ m ⊔ e ⊔ os
  module P = PredicateSystem (setoid-predicate.system {ℓ} {ℓ})
  module S = Category (SetoidCat ℓ ℓ)
  module SP = HasProducts (Setoid-products ℓ ℓ)
  module SCP = HasCoproducts (Setoid-coproducts ℓ ℓ)
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

_++_  : ∀ {X Y} → Predicate X → Predicate Y → Predicate (X + Y)
_++_ {X} {Y} P Q .pred x = P. pred x P.++ Q .pred x
_++_ {X} {Y} P Q .pred-mor {a} {b} f =
  P.++-copair left right
  where
    left : P .pred a P.⊑ ((P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) ]) P.[ SCP.in₁ ]
    left = begin
        P .pred a
      ≤⟨ P .pred-mor f ⟩
        P .pred b P.[ X .fmor f ]
      ≤⟨ P.++-in₁ P.[ _ ]m ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.in₁ ] P.[ X .fmor f ]
      ≤⟨ P.[]-comp _ _ ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.in₁ S.∘ X .fmor f ]
      ≤⟨ P.[]-cong (S.≈-sym (SCP.copair-in₁ _ _)) ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) S.∘ SCP.in₁ ]
      ≤⟨ P.[]-comp⁻¹ _ _ ⟩
        ((P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) ]) P.[ SCP.in₁ ]
      ∎
      where open ≤-Reasoning P.⊑-isPreorder

    right : Q .pred a P.⊑ ((P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) ]) P.[ SCP.in₂ ]
    right = begin
        Q .pred a
      ≤⟨ Q .pred-mor f ⟩
        Q .pred b P.[ Y .fmor f ]
      ≤⟨ P.++-in₂ P.[ _ ]m ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.in₂ ] P.[ Y .fmor f ]
      ≤⟨ P.[]-comp _ _ ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.in₂ S.∘ Y .fmor f ]
      ≤⟨ P.[]-cong (S.≈-sym (SCP.copair-in₂ _ _)) ⟩
        (P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) S.∘ SCP.in₂ ]
      ≤⟨ P.[]-comp⁻¹ _ _ ⟩
        ((P .pred b P.++ Q .pred b) P.[ SCP.coprod-m (X .fmor f) (Y .fmor f) ]) P.[ SCP.in₂ ]
      ∎
      where open ≤-Reasoning P.⊑-isPreorder

++-in₁ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} → P ⊑ (P ++ Q) [ +-in₁ ]
++-in₁ .*⊑* x = P.++-in₁

++-in₂ : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} → Q ⊑ (P ++ Q) [ +-in₂ ]
++-in₂ .*⊑* x = P.++-in₂

++-copair : ∀ {X Y} {P : Predicate X} {Q : Predicate Y} {R : Predicate (X + Y)} →
            P ⊑ R [ +-in₁ ] → Q ⊑ R [ +-in₂ ] → (P ++ Q) ⊑ R
++-copair ϕ ψ .*⊑* a = P.++-copair (ϕ .*⊑* a) (ψ .*⊑* a)


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


system : PredicateSystem PSh products coproducts
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
system .PredicateSystem.++-in₁ = ++-in₁
system .PredicateSystem.++-in₂ = ++-in₂
system .PredicateSystem.++-copair = ++-copair
system .PredicateSystem.⋀-[] = ⋀-[]
system .PredicateSystem.⋀-eval = ⋀-eval
system .PredicateSystem.⋀-lambda = ⋀-lambda
