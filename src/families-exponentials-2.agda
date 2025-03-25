{-# OPTIONS --prop --postfix-projections --safe #-}

-- This construction of exponentials in Fam(𝒞) is from this paper, but
-- here restricted to famiiles fibrations over Set:
--
-- Hermida, Claudio. ‘Some Properties of Fib as a Fibred
-- 2-Category’. Journal of Pure and Applied Algebra 134, no. 1 (5
-- January 1999): 83–109.
-- https://doi.org/10.1016/S0022-4049(97)00129-1
--
-- Unlike the construction in families-exponentials.agda, this one
-- requires 𝒞 to have small discrete limits and be cartesian closed
-- itself. The other construction requires small discrete completeness
-- and biproducts. It is not possible to have both biproducts and
-- cartesian closure without being trivial (
-- https://mathoverflow.net/questions/19004/is-the-category-commutative-monoids-cartesian-closed/136480#136480
-- ).
--
-- This construction also generalises to closure for monoidal
-- products, not just cartesian.

open import Level using (_⊔_)
open import Data.Product using (_,_)
open import prop
open import categories
open import prop-setoid using (Setoid; module ≈-Reasoning)
  renaming (_⇒_ to _⇒s_; _≃m_ to _≈s_)
open import functor
  using ( HasLimits; Limit; IsLimit; Functor; NatTrans; [_⇒_]
        ; module LimitFunctor)
open import fam
open import grothendieck using (module CategoryOfFamilies)
open import setoid-cat using (Setoid-exponentials)

module families-exponentials-2 {o m e} os
  (𝒞 : Category o m e)
  (T  : HasTerminal 𝒞)
  (P  : HasProducts 𝒞)
  (E  : HasExponentials 𝒞 P)
  (SP : ∀ (A : Setoid (m ⊔ e ⊔ os) (m ⊔ e ⊔ os)) → HasLimits (setoid→category A) 𝒞)
  where

module Fam𝒞 = CategoryOfFamilies (m ⊔ e ⊔ os) (os ⊔ m ⊔ e) 𝒞

open Fam𝒞
open Obj
open Fam
open _≃f_
open Mor
open _≃_

open products P

private
  module 𝒞 = Category 𝒞
  module P = HasProducts P
  module E = HasExponentials E
  module SE = HasExponentials (Setoid-exponentials (m ⊔ e ⊔ os))

open NatTrans
open Functor
open Limit
open Setoid
open _⇒s_
open _⇒f_
open _≈s_

_⇛_[_] : ∀ (X Y : Obj) (f : X .idx ⇒s Y .idx) → Functor (setoid→category (X .idx)) 𝒞
_⇛_[_] X Y f .fobj x = E.exp (X .fam .fm x) (Y .fam .fm (f .func x))
_⇛_[_] X Y f .fmor {x₁} {x₂} ⟪ x₁≈x₂ ⟫ = E.exp-fmor (X .fam .subst (X .idx .sym x₁≈x₂)) (Y .fam .subst (f .func-resp-≈ x₁≈x₂))
_⇛_[_] X Y f .fmor-cong tt = 𝒞.≈-refl
_⇛_[_] X Y f .fmor-id =
  𝒞.≈-trans (E.exp-cong (X .fam .refl*) (Y .fam .refl*))
             E.exp-id
_⇛_[_] X Y f .fmor-comp g h =
  𝒞.≈-trans (E.exp-cong (X .fam .trans* _ _) (Y .fam .trans* _ _))
             (E.exp-comp _ _ _ _)

Π : ∀ (A : Setoid (m ⊔ e ⊔ os) (m ⊔ e ⊔ os)) →
       Functor [ setoid→category A ⇒ 𝒞 ] 𝒞
Π A = F where open LimitFunctor (SP A) renaming (Π to F)

_⟶_ : Obj → Obj → Obj
(X ⟶ Y) .idx = SE.exp (X .idx) (Y .idx)
(X ⟶ Y) .fam .fm f = Π (X .idx) .fobj (X ⇛ Y [ f ])
(X ⟶ Y) .fam .subst {f₁} {f₂} f₁≈f₂ =
  Π (X .idx) .fmor
    (record { transf = λ x → E.exp-fmor (𝒞.id _) (Y .fam .subst (f₁≈f₂ .func-eq (X .idx .refl)))
            ; natural = λ f → 𝒞.≈-trans (𝒞.≈-sym (E.exp-comp _ _ _ _))
                             (𝒞.≈-trans (E.exp-cong (𝒞.≈-trans 𝒞.id-left (𝒞.≈-sym 𝒞.id-right))
                                                     (𝒞.≈-trans (𝒞.≈-sym (Y .fam .trans* _ _)) (Y .fam .trans* _ _)))
                                         (E.exp-comp _ _ _ _)) })
(X ⟶ Y) .fam .refl* =
  begin
    Π (X .idx) .fmor (record { transf = λ x → E.exp-fmor (𝒞.id _) (Y .fam .subst _) })
  ≈⟨ Π (X .idx) .fmor-cong (record { transf-eq = λ x → 𝒞.≈-trans (E.exp-cong 𝒞.≈-refl (Y .fam .refl*)) E.exp-id }) ⟩
    Π (X .idx) .fmor (Category.id [ setoid→category (X .idx) ⇒ 𝒞 ] _)
  ≈⟨ Π (X .idx) .fmor-id ⟩
    𝒞.id _
  ∎ where open ≈-Reasoning 𝒞.isEquiv
(X ⟶ Y) .fam .trans* e₁ e₂ = {!!}

eval⟶ : ∀ {X Y : Obj} → Mor ((X ⟶ Y) ⊗ X) Y
eval⟶ .idxf = SE.eval
eval⟶ .famf .transf (f , x) = E.eval 𝒞.∘ P.prod-m (SP _ _ .cone .transf x) (𝒞.id _)
eval⟶ .famf .natural (f₁≈f₂ , x₁≈x₂) = {!!}

lambda⟶ : ∀ {X Y Z} → Mor (X ⊗ Y) Z → Mor X (Y ⟶ Z)
lambda⟶ f .idxf = SE.lambda (f .idxf)
lambda⟶ f .famf .transf x = SP _ _ .lambda _ (record { transf = λ y → E.lambda (f .famf .transf (x , y))
                                                     ; natural = λ f → {!!} })
lambda⟶ f .famf .natural {x₁} {x₂} x₁≈x₂ = {!!}

exponentials : HasExponentials Fam𝒞.cat products
exponentials .HasExponentials.exp = _⟶_
exponentials .HasExponentials.eval = eval⟶
exponentials .HasExponentials.lambda = lambda⟶
exponentials .HasExponentials.lambda-cong f₁≈f₂ .idxf-eq = SE.lambda-cong (f₁≈f₂ .idxf-eq)
exponentials .HasExponentials.lambda-cong f₁≈f₂ .famf-eq .transf-eq {x} = {!!}
exponentials .HasExponentials.eval-lambda f .idxf-eq = SE.eval-lambda (f .idxf)
exponentials .HasExponentials.eval-lambda f .famf-eq .transf-eq {x , y} = {!!}
exponentials .HasExponentials.lambda-ext f .idxf-eq = SE.lambda-ext (f .idxf)
exponentials .HasExponentials.lambda-ext f .famf-eq .transf-eq {x} = {!!}
