{-# OPTIONS --postfix-projections --prop --safe #-}

module glueing-application where

open import Level using (suc; 0ℓ; lift)
open import prop using (_⇔_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import categories using (Category; HasTerminal; HasProducts; HasCoproducts)
open import functor using (HasLimits; op-colimit; limits→limits'; Functor)
open import cmon-category using (CMonCategory)
open import product-category using (product; product-limit)
import preorder
import prop-setoid
import cmon-enriched
import product-diagram
import empty-diagram
import meet-semilattice-category
import join-semilattice-category
import grothendieck
import fam

------------------------------------------------------------------------------
-- Meet × Join^op

M×Jop : CMonCategory (suc 0ℓ) 0ℓ 0ℓ
M×Jop .CMonCategory.cat =
  product meet-semilattice-category.cat (Category.opposite join-semilattice-category.cat)
M×Jop .CMonCategory.cmon-enriched =
  product-cmon-enriched meet-semilattice-category.cmon-enriched
                       (op-cmon-enriched join-semilattice-category.cmon-enriched)
  where open import cmon-enriched using (product-cmon-enriched; op-cmon-enriched)

M×Jop₀ = CMonCategory.cat M×Jop

Approx : Category.obj M×Jop₀
Approx .proj₁ = meet-semilattice-category.TWO
Approx .proj₂ = join-semilattice-category.TWO

M×Jop₀-limits-0 : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits 𝒮 M×Jop₀
M×Jop₀-limits-0 𝒮 D =
  product-limit _ _ 𝒮 D
    (meet-semilattice-category.limits 𝒮 _)
    (op-colimit _ (join-semilattice-category.colimits (Category.opposite 𝒮) _))

M×Jop-products : HasProducts M×Jop₀
M×Jop-products = product-diagram.limits→products M×Jop₀ (M×Jop₀-limits-0 _)

M×Jop-terminal : HasTerminal M×Jop₀
M×Jop-terminal = empty-diagram.limits→terminal M×Jop₀ (M×Jop₀-limits-0 _)

M×Jop-biproducts : ∀ x y → cmon-enriched.Biproduct (CMonCategory.cmon-enriched M×Jop) x y
M×Jop-biproducts =
  cmon-enriched.cmon+products→biproducts (M×Jop .CMonCategory.cmon-enriched) M×Jop-products

------------------------------------------------------------------------------
-- Fam(Meet × Join^op)

open grothendieck.CategoryOfFamilies 0ℓ 0ℓ M×Jop₀
  renaming ( cat to Fam⟨M×Jop⟩
           ; terminal to make-terminal
           ; coproducts to Fam⟨M×Jop⟩-coproducts )
  using (module products; Obj; Mor)
  public

Fam⟨M×Jop⟩-terminal : HasTerminal Fam⟨M×Jop⟩
Fam⟨M×Jop⟩-terminal = make-terminal M×Jop-terminal

open import families-exponentials 0ℓ 0ℓ
   M×Jop₀
   (M×Jop .CMonCategory.cmon-enriched)
   M×Jop-biproducts
   (fam.hasSetoidProducts 0ℓ 0ℓ M×Jop₀ λ A → limits→limits' (M×Jop₀-limits-0 _))
  renaming ( exponentials to Fam⟨M×Jop⟩-exponentials
           ; products     to Fam⟨M×Jop⟩-products )
  using    ()
  public

module _ where

  open Obj
  open fam.Fam

  Fam⟨Approx⟩ : Category.obj Fam⟨M×Jop⟩
  Fam⟨Approx⟩ .idx = prop-setoid.𝟙
  Fam⟨Approx⟩ .fam .fm _ = Approx
  Fam⟨Approx⟩ .fam .subst _ = Category.id M×Jop₀ _
  Fam⟨Approx⟩ .fam .refl* = Category.≈-refl M×Jop₀
  Fam⟨Approx⟩ .fam .trans* e₁ e₂ = Category.≈-sym M×Jop₀ (Category.id-left M×Jop₀)

  -- and this is a monoid wrt the finite products

------------------------------------------------------------------------------
module _ where
  import sconing
  open import prop-setoid using (Setoid; +-setoid; const) renaming (_⇒_ to _⇒s_)


  module Sc = sconing Fam⟨M×Jop⟩ Fam⟨M×Jop⟩-products Fam⟨Approx⟩
  open Sc using (Scone)

  private
    module CP = HasCoproducts Fam⟨M×Jop⟩-coproducts

  open Functor
  open _⇒s_
  open Mor
  open fam._⇒f_

  Scone-coprod : ∀ {X Y} → Scone .fobj (CP.coprod X Y) ⇒s +-setoid (Scone .fobj X) (Scone .fobj Y)
  Scone-coprod {X} {Y} .func f with f .idxf .func (lift tt)
  ... | inj₁ x = inj₁ (record { idxf = const _ x
                              ; famf = record { transf = λ _ → {!f .famf .transf (lift tt)!}
                                              ; natural = {!!} } })
  ... | inj₂ y = {!!}
  Scone-coprod {X} {Y} .func-resp-≈ = {!!}

open import setoid-cat using (SetoidCat; Setoid-products; Setoid-coproducts)
import glueing-simple
import setoid-predicate
module G = glueing-simple
             Fam⟨M×Jop⟩
             (SetoidCat 0ℓ 0ℓ) (Setoid-products 0ℓ 0ℓ) (Setoid-coproducts 0ℓ 0ℓ) setoid-predicate.predicate-system
             Sc.Scone

module GP = G.products-and-exponentials
               Fam⟨M×Jop⟩-products
               Fam⟨M×Jop⟩-exponentials
               Sc.mul
               Sc.mul⁻¹
               Sc.mul-inv
               Sc.mul-natural
               Sc.Scone-p₁

-- Now have a CCC, nearly with coproducts

module _ where
  open setoid-predicate.Predicate
  import two
  open Mor
  open fam._⇒f_
  open meet-semilattice-category._⇒_
  open join-semilattice-category._⇒_
  open preorder._=>_

  -- The glued interpretation of the approximation object is that it
  -- is a galois connection with the environment. FIXME: need to
  -- upgrade this to n-ary approximation environments.
  G⟨Approx⟩ : Category.obj G.cat
  G⟨Approx⟩ .G.Obj.carrier = Fam⟨Approx⟩
  G⟨Approx⟩ .G.Obj.pred .pred f = ∀ {x y} → y two.≤ fwd x ⇔ bwd y two.≤ x
   where fwd = f .famf .transf (lift tt) .proj₁ .func .fun
         bwd = f .famf .transf (lift tt) .proj₂ .func .fun
  G⟨Approx⟩ .G.Obj.pred .pred-≃ {f₁} {f₂} f₁≈f₂ f₁-is-galois-connection {x} {y} =
    {!!}

-- For any first-order type, and base element of the type, there is an
-- 'n ∈ ℕ' such that Fam⟨M×Jop⟩(Approx^n, ⟦ A ⟧) is an isomorphism in
-- the lower part.


-- 2. For each n, Scone(𝔸n) : Fam(Meet × Join^op) ⇒ SetoidCat
--    - preserves products and coproducts as appropriate
-- 3. Construct Glued(Scone(𝔸n)) from glueing-simple
-- 4. There is an approximation object in Glued(Scone(𝔸n))
--    - which ensures Galois connections by construction
-- 5. Derive the correctness properties:
--    (a) For every x : A ⊢ M : B, with A, B first order, ∀ a → ⟦ M ⟧ .famf a is a galois connection
--    (b) For every x : A ⊢ M : B, the set theoretic portions are equal. (sconing over 𝔸0)

-- Ideally:
-- 1. Fam(PSh_Cmon(GraphLang)) is a correct normaliser

-- If A is a first-order type, then:
--   1. T

data fo-type : Set where
  `base `approx : fo-type
  _`×_ _`+_ : fo-type → fo-type → fo-type

-- 1. fo-types can be interpreted in any category with products and coproducts
-- 2.
