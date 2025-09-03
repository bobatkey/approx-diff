{-# OPTIONS --prop --postfix-projections #-}

module example where

open import Level using (0ℓ; lift)
open import Data.List using (List; []; _∷_)
open import every using (Every; []; _∷_)
open import signature
import language-syntax
import label

open import example-signature

module L = language-syntax Sig

-- example query. Given `List (label [×] nat)`, add up all the
-- elements labelled with a specific label:
--
--   sum [ snd e | e <- xs, equal-label 'a' (fst e) ]
--
--   sum (concatMap x (e. if equal-label 'a' (fst e) then return (snd e) else nil))
--
--   sum = fold zero (add (var zero) (var (succ zero)))

module ex where
  open L

  -- writer monad over the approximation object
  Tag : type → type
  Tag τ = base approx [×] τ

  Tag-pure : ∀ {Γ τ} → Γ ⊢ τ [→] Tag τ
  Tag-pure = lam (pair (bop approx-unit []) (var zero))

  Tag-bind : ∀ {Γ σ τ} → Γ ⊢ Tag σ [→] (σ [→] Tag τ) [→] Tag τ
  Tag-bind = lam (lam (pair (bop approx-mult (fst (var (succ zero)) ∷ fst (app (var zero) (snd (var (succ zero)))) ∷ []))
                          (snd (app (var zero) (snd (var (succ zero)))))))

  Tag-monad : SynMonad
  Tag-monad .SynMonad.Mon = Tag
  Tag-monad .SynMonad.pure = Tag-pure
  Tag-monad .SynMonad.bind = Tag-bind

  -- Summation function
  sum : ∀ {Γ} → Γ ⊢ list (base number) [→] base number
  sum = lam (fold (bop zero []) (bop add (var zero ∷ var (succ zero) ∷ [])) (var zero))

  `_ : ∀ {Γ} → label.label → Γ ⊢ base label
  ` l = bop (lbl l) []

  _≟_ : ∀ {Γ} → Γ ⊢ base label → Γ ⊢ base label → Γ ⊢ bool
  M ≟ N = brel equal-label (M ∷ N ∷ [])

  query : label.label → emp , list (base label [×] base number) ⊢ base number
  query l = app sum
                (from var zero collect
                 when fst (var zero) ≟ (` l) ；
                 return (snd (var zero)))

  open import cbn-translation Sig Tag-monad

  cbn-query : label.label → emp , Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⊢ Tag (base number)
  cbn-query l = ⟪ query l ⟫tm

import indexed-family
import join-semilattice-category
import join-semilattice
import preorder
import nat
import prop-setoid

open import two renaming (I to ⊤; O to ⊥)
open import Data.Unit renaming (tt to ·; ⊤ to Unit) using ()
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open prop-setoid.Setoid

open L hiding (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

-- Example with lifted numbers (Example (2) in Section 4.3)
module example1 where
  open import ho-model
  open import example-signature-interpretation
  open interp Sig BaseInterp1

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0) , (label.b , 1) , (label.a , 1) , _

  back-slice : label.label → _
  back-slice l = ⟦ ex.query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun ⊤ .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

  -- Querying for the 'a' label uses the 1st and 3rd numbers
  test1 : back-slice label.a ≡ ((· , ⊤) , (· , ⊥) , (· , ⊤) , _)
  test1 = ≡-refl

  -- Querying for the 'b' label uses the 2nd number
  test2 : back-slice label.b ≡ ((· , ⊥) , (· , ⊤) , (· , ⊥) , _)
  test2 = ≡-refl

-- Example with interval-approximated numbers (Example (3) in Section 4.3)
module example2 where
  open import ho-model
  open import example-signature-interpretation
  open interp Sig BaseInterp2
  open import Data.Nat hiding (_/_)
  open import Data.Rational renaming (_≤_ to _≤ℚ_; show to ℚ-show)
  open import Data.Integer hiding (_/_; show; -_)
  open import preorder using (bottom; <_>; LCarrier)
  open import approx-numbers using (Intv; add-left)
  open import prop using (liftS)
  open import Data.Product using (_×_; Σ)

  input : ⟦ list (base label [×] base number) ⟧ty .idx .Carrier
  input = 3 , (label.a , 0ℚ) , (label.b , 1ℚ) , (label.a , 1ℚ) , _

  open Intv

  interval : Intv 1ℚ
  interval .lower = + 9 / 10
  interval .upper = + 11 / 10
  interval .l≤q = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
  interval .q≤u = liftS (*≤* (+≤+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))

  open import Data.Maybe

  extract-interval : ∀ {q} → LCarrier (Intv q) → Maybe (ℚ × ℚ)
  extract-interval bottom = nothing
  extract-interval < x > = just (x .lower , x .upper)

  back-slice : _
  back-slice = ⟦ ex.query label.a ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun < interval > .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  -- Normalising 'back-slice' doesn't seem to work, possibly due to
  -- the use of records and/or the proofs attached to them. We have to
  -- project out the relevant bits individually and test them:

  test1 : extract-interval (back-slice .proj₁ .proj₂) ≡ just (- (+ 1 / 10) , + 1 / 10)
  test1 = ≡-refl

  test2 : extract-interval (back-slice .proj₂ .proj₁ .proj₂) ≡ nothing
  test2 = ≡-refl

  test3 : extract-interval (back-slice .proj₂ .proj₂ .proj₁ .proj₂) ≡ just (+ 9 / 10 , + 11 / 10)
  test3 = ≡-refl

------------------------------------------------------------------------------
-- Example using CBN lifting
module cbn-example where
  open import ho-model
  open import example-signature-interpretation
  open interp Sig BaseInterp0
  open ex using (Tag; cbn-query)

  input : ⟦ Tag (list (Tag (Tag (base label) [×] Tag (base number)))) ⟧ty .idx .Carrier
  input = _ , 3 , (_ , (_ , label.a) , (_ , 0)) , (_ , (_ , label.b) , (_ , 1)) , (_ , (_ , label.a) , (_ , 1)) , _

  back-slice : label.label → _
  back-slice l = ⟦ ex.cbn-query l ⟧tm .famf .transf (_ , input) .proj₂ .*→* .func .fun (⊤ , ·) .proj₂
    where
      open indexed-family._⇒f_
      open join-semilattice-category._⇒_
      open join-semilattice._=>_
      open preorder._=>_

  open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

  test1 : back-slice label.a ≡ (⊤ , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , ·)
  test1 = ≡-refl

  test2 : back-slice label.b ≡ (⊤ , (⊤ , (⊤ , ·) , ⊥ , ·) , (⊤ , (⊤ , ·) , ⊤ , ·) , (⊤ , (⊤ , ·) , ⊥ , ·) , ·)
  test2 = ≡-refl
