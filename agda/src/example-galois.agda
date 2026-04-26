{-# OPTIONS --prop --postfix-projections --safe #-}

module example-galois where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label
import galois

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
  open import approx-numbers using (ℚ-intv; add; zero)
  open import categories using (Category; HasProducts; HasTerminal)

  BaseInterp2 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
  BaseInterp2 .Model.⟦sort⟧ number = ℚ-intv
  BaseInterp2 .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
  BaseInterp2 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
  BaseInterp2 .Model.⟦op⟧ zero = approx-numbers.zero
  BaseInterp2 .Model.⟦op⟧ add = approx-numbers.add C.∘ binary2
  BaseInterp2 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.cat .Category.id _ ]
  BaseInterp2 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
  BaseInterp2 .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
  BaseInterp2 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary

  open Galois.interp Sig BaseInterp2
  open import Data.Nat hiding (_/_)
  open import Data.Rational renaming (_≤_ to _≤ℚ_; show to ℚ-show)
  open import Data.Integer hiding (_/_; show; -_)
  open import preorder using (bottom; <_>; LCarrier)
  open import approx-numbers using (Intv; add-left)
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
