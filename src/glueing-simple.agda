{-# OPTIONS --prop --postfix-projections --safe #-}

open import Level using (suc; _⊔_)
open import prop-setoid using (module ≈-Reasoning; IsEquivalence)
open import basics using (IsPreorder; IsMeet; IsTop; IsResidual; module ≤-Reasoning; IsJoin)
open import categories using (Category; HasProducts; HasExponentials; HasCoproducts; HasTerminal; IsTerminal)
open import functor using (Functor)
open import predicate-system using (PredicateSystem)

-- FIXME: refactor this into
--   1. glueing with predicates over 𝒞 directly
--   2. pullback of PredicateSystems along product preserving functors

module glueing-simple {o₁ m₁ e₁ o₂ m₂ e₂}
  (𝒞 : Category o₁ m₁ e₁)
  (𝒟 : Category o₂ m₂ e₂) (𝒟P : HasProducts 𝒟)
  (𝒟-predicates : PredicateSystem 𝒟 𝒟P)
  (F : Functor 𝒞 𝒟) where

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module 𝒟P = HasProducts 𝒟P
open Functor
open PredicateSystem 𝒟-predicates

⊑-refl : ∀ {X}{P : Predicate X} → P ⊑ P
⊑-refl = ⊑-isPreorder .IsPreorder.refl

record Obj : Set (suc o₁ ⊔ suc m₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc m₂ ⊔ suc e₂) where
  no-eta-equality
  field
    carrier : 𝒞.obj
    pred    : Predicate (F .fobj carrier)
open Obj

record _=>_ (X Y : Obj) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  no-eta-equality
  field
    morph : X .carrier 𝒞.⇒ Y .carrier
    presv : X .pred ⊑ (Y .pred [ F .fmor morph ])
open _=>_

record _≃m_ {X Y} (f g : X => Y) : Prop (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  no-eta-equality
  field
    f≃f : f .morph 𝒞.≈ g .morph
open _≃m_

id : ∀ X → X => X
id X .morph = 𝒞.id _
id X .presv = begin
     X .pred                       ≤⟨ []-id ⟩
     X .pred [ 𝒟.id _ ]           ≤⟨ []-cong (𝒟.≈-sym (F .fmor-id)) ⟩
     X .pred [ F .fmor (𝒞.id _) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

_∘_ : ∀ {X Y Z} → Y => Z → X => Y → X => Z
(f ∘ g) .morph = f .morph 𝒞.∘ g .morph
_∘_ {X}{Y}{Z} f g .presv = begin
    X .pred                                                 ≤⟨ g .presv ⟩
    Y .pred [ F .fmor (g .morph) ]                          ≤⟨ (f .presv) [ F .fmor (g .morph) ]m ⟩
    (Z .pred [ F .fmor (f .morph) ]) [ F .fmor (g .morph) ] ≤⟨ []-comp _ _ ⟩
    Z .pred [ F .fmor (f .morph) 𝒟.∘ F .fmor (g .morph) ]  ≤⟨ []-cong (𝒟.≈-sym (F .fmor-comp _ _)) ⟩
    Z .pred [ F .fmor (f .morph 𝒞.∘ g .morph) ]
  ∎
  where open ≤-Reasoning ⊑-isPreorder

cat : Category (suc o₁ ⊔ suc m₁ ⊔ suc e₁ ⊔ suc o₂ ⊔ suc m₂ ⊔ suc e₂) (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
cat .Category.obj = Obj
cat .Category._⇒_ = _=>_
cat .Category._≈_ = _≃m_
cat .Category.isEquiv .IsEquivalence.refl .f≃f = 𝒞.≈-refl
cat .Category.isEquiv .IsEquivalence.sym e .f≃f = 𝒞.≈-sym (e .f≃f)
cat .Category.isEquiv .IsEquivalence.trans e₁ e₂ .f≃f = 𝒞.≈-trans (e₁ .f≃f) (e₂ .f≃f)
cat .Category.id = id
cat .Category._∘_ = _∘_
cat .Category.∘-cong e₁ e₂ .f≃f = 𝒞.∘-cong (e₁ .f≃f) (e₂ .f≃f)
cat .Category.id-left .f≃f = 𝒞.id-left
cat .Category.id-right .f≃f = 𝒞.id-right
cat .Category.assoc f g h .f≃f = 𝒞.assoc (f .morph) (g .morph) (h .morph)

-- Binary Coproducts
module coproducts (CP : HasCoproducts 𝒞) where

  private
    module CP = HasCoproducts CP

  _[+]_ : Obj → Obj → Obj
  (X [+] Y) .carrier = CP.coprod (X .carrier) (Y .carrier)
  (X [+] Y) .pred = (X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)

  in₁ : ∀ {X Y} → X => (X [+] Y)
  in₁ .morph = CP.in₁
  in₁ {X} {Y} .presv = begin
      X .pred
    ≤⟨ unit _ ⟩
      X .pred ⟨ F .fmor CP.in₁ ⟩ [ F .fmor CP.in₁ ]
    ≤⟨ ++-isJoin .IsJoin.inl [ _ ]m ⟩
      ((X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)) [ F .fmor CP.in₁ ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  in₂ : ∀ {X Y} → Y => (X [+] Y)
  in₂ .morph = CP.in₂
  in₂ {X} {Y} .presv = begin
      Y .pred
    ≤⟨ unit _ ⟩
      Y .pred ⟨ F .fmor CP.in₂ ⟩ [ F .fmor CP.in₂ ]
    ≤⟨ ++-isJoin .IsJoin.inr [ _ ]m ⟩
      ((X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)) [ F .fmor CP.in₂ ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  copair : ∀ {X Y Z} → X => Z → Y => Z → (X [+] Y) => Z
  copair f g .morph = CP.copair (f .morph) (g .morph)
  copair {X} {Y} {Z} f g .presv = begin
      (X .pred ⟨ F .fmor CP.in₁ ⟩) ++ (Y .pred ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin (f .presv ⟨ _ ⟩m) (g .presv ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (f .morph) ] ⟨ F .fmor CP.in₁ ⟩) ++ (Z .pred [ F .fmor (g .morph) ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin ([]-cong (F .fmor-cong (𝒞.≈-sym (CP.copair-in₁ _ _))) ⟨ _ ⟩m)
                             ([]-cong (F .fmor-cong (𝒞.≈-sym (CP.copair-in₂ _ _))) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph) 𝒞.∘ CP.in₁) ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph) 𝒞.∘ CP.in₂) ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin ([]-cong (F .fmor-comp _ _) ⟨ _ ⟩m)
                             ([]-cong (F .fmor-comp _ _) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) 𝒟.∘ F .fmor CP.in₁ ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) 𝒟.∘ F .fmor CP.in₂ ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.mono ++-isJoin (([]-comp⁻¹ _ _) ⟨ _ ⟩m) (([]-comp⁻¹ _ _) ⟨ _ ⟩m) ⟩
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ] [ F .fmor CP.in₁ ] ⟨ F .fmor CP.in₁ ⟩)
        ++
      (Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ] [ F .fmor CP.in₂ ] ⟨ F .fmor CP.in₂ ⟩)
    ≤⟨ IsJoin.[_,_] ++-isJoin (counit _) (counit _) ⟩
      Z .pred [ F .fmor (CP.copair (f .morph) (g .morph)) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  coproducts : HasCoproducts cat
  coproducts .HasCoproducts.coprod = _[+]_
  coproducts .HasCoproducts.in₁ = in₁
  coproducts .HasCoproducts.in₂ = in₂
  coproducts .HasCoproducts.copair = copair
  coproducts .HasCoproducts.copair-cong e₁ e₂ .f≃f = CP.copair-cong (e₁ .f≃f) (e₂ .f≃f)
  coproducts .HasCoproducts.copair-in₁ f g .f≃f = CP.copair-in₁ (f .morph) (g .morph)
  coproducts .HasCoproducts.copair-in₂ f g .f≃f = CP.copair-in₂ (f .morph) (g .morph)
  coproducts .HasCoproducts.copair-ext f .f≃f = CP.copair-ext (f .morph)

-- products and exponentials
module products-and-exponentials
         (T : HasTerminal 𝒞) (P : HasProducts 𝒞) (E : HasExponentials 𝒞 P)
         (mul   : ∀ {x y} → 𝒟P.prod (F .fobj x) (F .fobj y) 𝒟.⇒ F .fobj (P .HasProducts.prod x y))
         (mul⁻¹ : ∀ {x y} → F .fobj (P .HasProducts.prod x y) 𝒟.⇒ 𝒟P.prod (F .fobj x) (F .fobj y))
         (mul-inv : ∀ {x y} → (mul {x} {y} 𝒟.∘ mul⁻¹) 𝒟.≈ 𝒟.id _)
         (mul-natural : ∀ {x x' y y'} {f : x 𝒞.⇒ x'} {g : y 𝒞.⇒ y'} → (F .fmor (HasProducts.prod-m P f g) 𝒟.∘ mul) 𝒟.≈ (mul 𝒟.∘ 𝒟P.prod-m (F .fmor f) (F .fmor g)))
         (F-p₁   : ∀ {x y} → (F .fmor (P .HasProducts.p₁ {x} {y}) 𝒟.∘ mul) 𝒟.≈ 𝒟P.p₁)
     where

  private
    module T = HasTerminal T
    module P = HasProducts P
    module E = HasExponentials E

  F-p₁' : ∀ {x y} → F .fmor (P .HasProducts.p₁ {x} {y}) 𝒟.≈ (𝒟P.p₁ 𝒟.∘ mul⁻¹)
  F-p₁' {x} {y} = begin
      F .fmor (P .HasProducts.p₁ {x} {y})                       ≈˘⟨ 𝒟.id-right ⟩
      F .fmor (P .HasProducts.p₁ {x} {y}) 𝒟.∘ 𝒟.id _           ≈˘⟨ 𝒟.∘-cong 𝒟.≈-refl mul-inv ⟩
      F .fmor (P .HasProducts.p₁ {x} {y}) 𝒟.∘ (mul 𝒟.∘ mul⁻¹)  ≈˘⟨ 𝒟.assoc _ _ _ ⟩
      (F .fmor (P .HasProducts.p₁ {x} {y}) 𝒟.∘ mul) 𝒟.∘ mul⁻¹  ≈⟨ 𝒟.∘-cong F-p₁ 𝒟.≈-refl ⟩
      𝒟P.p₁ 𝒟.∘ mul⁻¹
    ∎ where open ≈-Reasoning 𝒟.isEquiv

  open IsMeet

  -- Terminal
  [⊤] : Obj
  [⊤] .carrier = T.witness
  [⊤] .pred = TT

  to-terminal : ∀ {X} → X => [⊤]
  to-terminal .morph = T.is-terminal .IsTerminal.to-terminal
  to-terminal {X} .presv = begin
      X .pred
    ≤⟨ TT-isTop .IsTop.≤-top ⟩
      TT
    ≤⟨ []-TT ⟩
      TT [ F .fmor (T.is-terminal .IsTerminal.to-terminal) ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  terminal : HasTerminal cat
  terminal .HasTerminal.witness = [⊤]
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal = to-terminal
  terminal .HasTerminal.is-terminal .IsTerminal.to-terminal-ext f .f≃f =
    T.is-terminal .IsTerminal.to-terminal-ext (f .morph)

  -- Products
  _[×]_ : Obj → Obj → Obj
  (X [×] Y) .carrier = P.prod (X .carrier) (Y .carrier)
  (X [×] Y) .pred = (X .pred [ F .fmor P.p₁ ]) && (Y .pred [ F .fmor P.p₂ ])

  p₁ : ∀ {X Y} → (X [×] Y) => X
  p₁ .morph = P.p₁
  p₁ .presv = &&-isMeet .π₁

  p₂ : ∀ {X Y} → (X [×] Y) => Y
  p₂ .morph = P.p₂
  p₂ .presv = &&-isMeet .π₂

  pair : ∀ {X Y Z} → X => Y → X => Z → X => (Y [×] Z)
  pair f g .morph = P.pair (f .morph) (g .morph)
  pair {X} {Y} {Z} f g .presv = begin
      X .pred
    ≤⟨ &&-isMeet .⟨_,_⟩ (f .presv) (g .presv) ⟩
      (Y .pred [ F .fmor (f .morph) ]) && (Z .pred [ F .fmor (g .morph) ])
    ≤⟨ mono &&-isMeet ([]-cong (F .fmor-cong (𝒞.≈-sym (P.pair-p₁ _ _)))) ([]-cong (F .fmor-cong (𝒞.≈-sym (P.pair-p₂ _ _)))) ⟩
      (Y .pred [ F .fmor (P.p₁ 𝒞.∘ P.pair (f .morph) (g .morph)) ]) && (Z .pred [ F .fmor (P.p₂ 𝒞.∘ P.pair (f .morph) (g .morph)) ])
    ≤⟨ mono &&-isMeet ([]-cong (F .fmor-comp _ _)) ([]-cong (F .fmor-comp _ _)) ⟩
      (Y .pred [ F .fmor P.p₁ 𝒟.∘ F .fmor (P.pair (f .morph) (g .morph)) ]) && (Z .pred [ F .fmor P.p₂ 𝒟.∘ F .fmor (P.pair (f .morph) (g .morph)) ])
    ≤⟨ mono &&-isMeet ([]-comp⁻¹ _ _) ([]-comp⁻¹ _ _) ⟩
      ((Y .pred [ F .fmor P.p₁ ]) [ F .fmor (P.pair (f .morph) (g .morph)) ]) && ((Z .pred [ F .fmor P.p₂ ]) [ F .fmor (P.pair (f .morph) (g .morph)) ])
    ≤⟨ []-&& ⟩
      ((Y .pred [ F .fmor P.p₁ ]) && (Z .pred [ F .fmor P.p₂ ])) [ F .fmor (P.pair (f .morph) (g .morph)) ]
    ∎ where open ≤-Reasoning ⊑-isPreorder

  products : HasProducts cat
  products .HasProducts.prod = _[×]_
  products .HasProducts.p₁ = p₁
  products .HasProducts.p₂ = p₂
  products .HasProducts.pair = pair
  products .HasProducts.pair-cong e₁ e₂ .f≃f = P.pair-cong (e₁ .f≃f) (e₂ .f≃f)
  products .HasProducts.pair-p₁ f g .f≃f = P.pair-p₁ (f .morph) (g .morph)
  products .HasProducts.pair-p₂ f g .f≃f = P.pair-p₂ (f .morph) (g .morph)
  products .HasProducts.pair-ext f .f≃f = P.pair-ext (f .morph)

  -- Exponentials
  _[→]_ : Obj → Obj → Obj
  (X [→] Y) .carrier = E.exp (X .carrier) (Y .carrier)
  (X [→] Y) .pred = ⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ])

  eval : ∀ {X Y} → ((X [→] Y) [×] X) => Y
  eval .morph = E.eval
  eval {X} {Y} .presv = begin
      (⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ F .fmor P.p₁ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-cong F-p₁') ⊑-refl ⟩
      (⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.p₁ 𝒟.∘ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-comp⁻¹ _ _) ⊑-refl ⟩
      ((⋀ (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.p₁ ]) [ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet (⋀-eval [ _ ]m) ⊑-refl ⟩
      ((((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul ]) [ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-comp _ _) ⊑-refl ⟩
      (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ mul⁻¹ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet ([]-cong mul-inv) ⊑-refl ⟩
      (((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) [ 𝒟.id _ ]) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ mono &&-isMeet []-id⁻¹ ⊑-refl ⟩
      ((X .pred [ F .fmor P.p₂ ]) ==> (Y .pred [ F .fmor E.eval ])) && (X .pred [ F .fmor P.p₂ ])
    ≤⟨ ==>-residual .IsResidual.eval ⟩
      Y .pred [ F .fmor E.eval ]
    ∎
    where open ≤-Reasoning ⊑-isPreorder

  lambda : ∀ {X Y Z} → (X [×] Y) => Z → X => (Y [→] Z)
  lambda f .morph = E.lambda (f .morph)
  lambda {X} {Y} {Z} f .presv = begin
      X .pred
    ≤⟨ ⋀-lambda lemma ⟩
      ⋀ ((((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ])
    ≤⟨ ⋀-[] ⟩
      ⋀ (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ F .fmor (E.lambda (f .morph)) ]
    ∎
    where
      lemma : (X .pred [ 𝒟P.p₁ ]) ⊑ ((((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ])
      lemma = begin
          X .pred [ 𝒟P.p₁ ]
        ≤⟨ []-cong (𝒟.≈-sym F-p₁) ⟩
          X .pred [ F .fmor P.p₁ 𝒟.∘ mul ]
        ≤⟨ []-comp⁻¹ _ _ ⟩
          (X .pred [ F .fmor P.p₁ ]) [ mul ]
        ≤⟨ (==>-residual .IsResidual.lambda (f .presv)) [ _ ]m ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor (f .morph) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (F .fmor-cong 𝒞.id-left)) ⊑-refl [ mul ]m ⟩
          ((Y .pred [ F .fmor (𝒞.id _ 𝒞.∘ P.p₂) ]) ==> (Z .pred [ F .fmor (f .morph) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (F .fmor-cong (P.pair-p₂ _ _))) ([]-cong (F .fmor-cong (𝒞.≈-sym (E.eval-lambda _)))) [ mul ]m ⟩
          ((Y .pred [ F .fmor (P.p₂ 𝒞.∘ P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> (Z .pred [ F .fmor (E.eval 𝒞.∘ P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-cong (𝒟.≈-sym (F .fmor-comp _ _))) ([]-cong (F .fmor-comp _ _)) [ mul ]m ⟩
          ((Y .pred [ F .fmor P.p₂ 𝒟.∘ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> (Z .pred [ F .fmor E.eval 𝒟.∘ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ IsResidual.-∙-mono ==>-residual ([]-comp _ _) ([]-comp⁻¹ _ _) [ mul ]m ⟩
          (((Y .pred [ F .fmor P.p₂ ])  [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) ==> ((Z .pred [ F .fmor E.eval ]) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ])) [ mul ]
        ≤⟨ []-==> [ mul ]m ⟩
          (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) ]) [ mul ]
        ≤⟨ []-comp _ _ ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ F .fmor (P.prod-m (E.lambda (f .morph)) (𝒞.id _)) 𝒟.∘ mul ]
        ≤⟨ []-cong mul-natural ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (F .fmor (𝒞.id _)) ]
        ≤⟨ []-cong (𝒟.∘-cong 𝒟.≈-refl (𝒟P.prod-m-cong 𝒟.≈-refl (F .fmor-id))) ⟩
          ((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul 𝒟.∘ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ]
        ≤⟨ []-comp⁻¹ _ _ ⟩
          (((Y .pred [ F .fmor P.p₂ ]) ==> (Z .pred [ F .fmor E.eval ])) [ mul ]) [ 𝒟P.prod-m (F .fmor (E.lambda (f .morph))) (𝒟.id _) ]
        ∎
        where open ≤-Reasoning ⊑-isPreorder
      open ≤-Reasoning ⊑-isPreorder

  exponentials : HasExponentials cat products
  exponentials .HasExponentials.exp = _[→]_
  exponentials .HasExponentials.eval = eval
  exponentials .HasExponentials.lambda = lambda
  exponentials .HasExponentials.lambda-cong e .f≃f = E.lambda-cong (e .f≃f)
  exponentials .HasExponentials.eval-lambda f .f≃f = E.eval-lambda (f .morph)
  exponentials .HasExponentials.lambda-ext f .f≃f = E.lambda-ext (f .morph)
