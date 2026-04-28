{-# OPTIONS --prop --postfix-projections --safe #-}

module example-galois where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label
import galois
import conjugate

open import example-signature

module L = language-syntax Sig

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import prop-setoid

open import two renaming (I to ⊤; O to ⊥)
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

import example

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

-- Example with lifted numbers (Example (2) in Section 4.3)
module example1 where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open Galois.interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  bwd-slice : label.label → _
  bwd-slice l = ⟦ example.ex.query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun ⊤ .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Querying for the 'a' label uses the 1st and 3rd numbers
  test1 : bwd-slice label.a ≡ ((· , ⊤) , (· , ⊥) , (· , ⊤) , _)
  test1 = ≡-refl

  -- Querying for the 'b' label uses the 2nd number
  test2 : bwd-slice label.b ≡ ((· , ⊥) , (· , ⊤) , (· , ⊥) , _)
  test2 = ≡-refl

-- Example with interval-approximated numbers (Example (3) in Section 4.3)
module example2 where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open import prop-setoid using (idS)
    renaming (𝟙 to 𝟙ₛ; const to constₛ)
  open import approx-numbers using (module Galois)
  open import categories using (Category; HasProducts; HasTerminal)

  BaseInterp : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
  BaseInterp .Model.⟦sort⟧ number = Galois.ℚ-intv
  BaseInterp .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
  BaseInterp .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
  BaseInterp .Model.⟦op⟧ zero = Galois.zero-mor
  BaseInterp .Model.⟦op⟧ add = Galois.add-mor C.∘ binary2
  BaseInterp .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.cat .Category.id _ ]
  BaseInterp .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
  BaseInterp .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
  BaseInterp .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary

  open Galois.interp Sig BaseInterp
  open import Data.Nat hiding (_/_)
  open import Data.Rational renaming (_≤_ to _≤ℚ_; show to ℚ-show)
  open import Data.Integer hiding (_/_; show; -_)
  open import preorder using (bottom; <_>; LCarrier)
  open import approx-numbers using (Intv)
  open import prop using (liftS)
  open import Data.Product using (Σ) renaming (_×_ to _×ₜ_)

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0ℚ) , (label.b , 1ℚ) , (label.a , 1ℚ) , _

  open Intv

  interval : Intv 1ℚ
  interval .lower = + 9 / 10
  interval .upper = + 11 / 10
  interval .l≤q = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
  interval .q≤u = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))

  open import Data.Maybe

  extract-interval : ∀ {q} → LCarrier (Intv q) → Maybe (ℚ ×ₜ ℚ)
  extract-interval bottom = nothing
  extract-interval < x > = just (x .lower , x .upper)

  bwd-slice : _
  bwd-slice = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun < interval > .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Normalising 'bwd-slice' doesn't seem to work, possibly due to
  -- the use of records and/or the proofs attached to them. We have to
  -- project out the relevant bits individually and test them:

  test1 : extract-interval (bwd-slice .proj₁ .proj₂) ≡ just (- (+ 1 / 10) , + 1 / 10)
  test1 = ≡-refl

  test2 : extract-interval (bwd-slice .proj₂ .proj₁ .proj₂) ≡ nothing
  test2 = ≡-refl

  test3 : extract-interval (bwd-slice .proj₂ .proj₂ .proj₁ .proj₂) ≡ just (+ 9 / 10 , + 11 / 10)
  test3 = ≡-refl

-- Forward analysis using addᵀ (Tarski conjugate)
module example3 where
  open import ho-model
  open import example-signature-interpretation conjugate.cat conjugate.products conjugate.terminal conjugate.TWO conjugate.unit conjugate.conjunct
  open import prop-setoid using (idS)
    renaming (𝟙 to 𝟙ₛ; const to constₛ)
  open import approx-numbers using (module Conjugate; module Galois)
  open import categories using (Category; HasProducts; HasTerminal)

  BaseInterp : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
  BaseInterp .Model.⟦sort⟧ number = Conjugate.ℚ-intv
  BaseInterp .Model.⟦sort⟧ label = simple[ label.Label , conjugate.𝟙 ]
  BaseInterp .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , conjugate.TWO ]
  BaseInterp .Model.⟦op⟧ zero = Conjugate.zero-mor
  BaseInterp .Model.⟦op⟧ add = Conjugate.add-mor C.∘ binary2
  BaseInterp .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , conjugate.cat .Category.id _ ]
  BaseInterp .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
  BaseInterp .Model.⟦op⟧ approx-unit = simplef[ idS _ , conjugate.unit ]
  BaseInterp .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , conjugate.conjunct ] C.∘ binary

  open Conjugate.interp Sig BaseInterp
  open import Data.Rational
  open import Data.Rational.Properties using (≤-refl)
  open import preorder using (bottom; <_>; LCarrier)
  open import approx-numbers using (Intv)
  open import prop using (liftS)
  open import Data.Nat hiding (_/_)
  open import Data.Integer hiding (_/_; show; -_)

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0ℚ) , (label.b , 1ℚ) , (label.a , 1ℚ) , _

  open Intv

  intv1 : Intv 1ℚ
  intv1 .lower = + 4 / 5
  intv1 .upper = + 3 / 2
  intv1 .l≤q = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s z≤n))))))
  intv1 .q≤u = liftS (*≤* (+≤+ (s≤s (s≤s z≤n))))

  intv0 : Intv 0ℚ
  intv0 .lower = - (+ 1 / 2)
  intv0 .upper = 0ℚ
  intv0 .l≤q = liftS (*≤* -≤+)
  intv0 .q≤u = liftS Data.Rational.Properties.≤-refl

  open import Data.Maybe
  open import Data.Product using (Σ) renaming (_×_ to _×ₜ_)

  extract-interval : ∀ {q} → LCarrier (Intv q) → Maybe (ℚ ×ₜ ℚ)
  extract-interval bottom = nothing
  extract-interval < x > = just (x .lower , x .upper)

  -- Unfortunately this is a bit slow to normalise, so not using at the moment; instead have simpler isolated
  -- tests using the 'add' conjugate pair and Galois connection directly.
  fwd-slice : _
  fwd-slice = ⟦ example.ex.query label.a ⟧tm .famf .transf (_ , input) .proj₁ .*→* .func .fun
    (_ , (_ , < intv0 >) , (_ , bottom) , (_ , < intv1 >) , _)
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  fwd-addᵀ : _
  fwd-addᵀ = Conjugate.add-interval 0ℚ 1ℚ .conjugate._⇒c_.right .join-semilattice._=>_.func .preorder._=>_.fun
    (< intv0 > , < intv1 >)

  fwd-add⁎ : _
  fwd-add⁎ = Galois.add-interval 0ℚ 1ℚ .galois._⇒g_.right .preorder._=>_.fun
    (< intv0 > , < intv1 >)

  -- q₂-shifted intv0 = [1/2, 1]; q₁-shifted intv1 = [4/5, 3/2]. addᵀ takes the intersection.
  test-addᵀ : extract-interval fwd-addᵀ ≡ just (+ 4 / 5 , + 1 / 1)
  test-addᵀ = ≡-refl

  -- And add⁎ takes the union.
  test-add⁎ : extract-interval fwd-add⁎ ≡ just (+ 1 / 2 , + 3 / 2)
  test-add⁎ = ≡-refl


------------------------------------------------------------------------------
-- Example using CBN lifting
module cbn-example where
  open import ho-model
  open import example-signature-interpretation galois.cat galois.products galois.terminal galois.TWO galois.unit galois.conjunct
  open Galois.interp Sig BaseInterp0
  open example.ex using (Tag; cbn-query)

  input : ⟦ Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⟧ty .idx .Carrier
  input = _ , 3 , (_ , (_ , label.a) , (_ , 0)) , (_ , (_ , label.b) , (_ , 1)) , (_ , (_ , label.a) , (_ , 1)) , _

  bwd-slice : label.label → _
  bwd-slice l = ⟦ example.ex.cbn-query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun (⊤ , ·) .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  test1 : bwd-slice label.a ≡ (⊤ , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , ·)
  test1 = ≡-refl

  test2 : bwd-slice label.b ≡ (⊤ , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , ·)
  test2 = ≡-refl
