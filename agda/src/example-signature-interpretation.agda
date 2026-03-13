{-# OPTIONS --postfix-projections --prop --safe #-}

open import Level using (0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts)

module example-signature-interpretation
  (𝒞 : Category (suc 0ℓ) 0ℓ 0ℓ)
  (𝒞-products : HasProducts 𝒞)
  (𝒞-terminal : HasTerminal 𝒞)
  (TWO : Category.obj 𝒞)
  (unit : Category._⇒_ 𝒞 (HasTerminal.witness 𝒞-terminal) TWO)
  (conjunct : Category._⇒_ 𝒞 (HasProducts.prod 𝒞-products TWO TWO) TWO)
  where

import fam

private
  module 𝒞m = Category 𝒞
  𝟙-base = HasTerminal.witness 𝒞-terminal
  to-𝟙-base : ∀ {X} → X 𝒞m.⇒ 𝟙-base
  to-𝟙-base = HasTerminal.to-terminal 𝒞-terminal

------------------------------------------------------------------------------
-- Construct the category of first-order approximations
module Fam⟨𝒞⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ 𝒞

open Fam⟨𝒞⟩ using (simple[_,_]; simplef[_,_]) public

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat = Fam⟨𝒞⟩.cat

module C = Category cat

open Fam⟨𝒞⟩.products 𝒞-products
  using (products; simple-monoidal)
  renaming (_⊗_ to _×_)
  public

terminal : HasTerminal cat
terminal = Fam⟨𝒞⟩.terminal 𝒞-terminal

coproducts : HasCoproducts cat
coproducts = Fam⟨𝒞⟩.coproducts

module P = HasProducts products

_+_ = HasCoproducts.coprod coproducts
𝟙 = HasTerminal.witness terminal

𝟚 : Category.obj cat
𝟚 = 𝟙 + 𝟙

------------------------------------------------------------------------------

open import Data.Sum using (inj₁; inj₂)
open import prop-setoid using (Setoid; idS)
  renaming (⊗-setoid to _×ₛ_; +-setoid to _+ₛ_; 𝟙 to 𝟙ₛ; _⇒_ to _⇒s_; const to constₛ)
import indexed-family

𝟚ₛ : Setoid 0ℓ 0ℓ
𝟚ₛ = 𝟙ₛ +ₛ 𝟙ₛ

open Fam⟨𝒞⟩.Mor
open Fam⟨𝒞⟩.Obj
open indexed-family.Fam
open indexed-family._⇒f_
open _⇒s_

private
  predicate-transf : ∀ X x y → X .fam .fm x 𝒞m.⇒ 𝟚 .fam .fm y
  predicate-transf X x (inj₁ _) = to-𝟙-base
  predicate-transf X x (inj₂ _) = to-𝟙-base

  predicate-natural : ∀ X {x₁} {x₂} {y₁} {y₂}
    (x-eq : X .idx .Setoid._≈_ x₁ x₂)
    (y-eq : 𝟚ₛ .Setoid._≈_ y₁ y₂) →
    𝒞m._≈_ (𝒞m._∘_ (predicate-transf X x₂ y₂) (X .fam .subst x-eq))
            (𝒞m._∘_ (𝟚 .fam .subst {y₁} {y₂} y-eq) (predicate-transf X x₁ y₁))
  predicate-natural X {x₁} {x₂} {inj₁ x} {inj₁ x₃} x-eq y-eq = HasTerminal.to-terminal-unique 𝒞-terminal _ _
  predicate-natural X {x₁} {x₂} {inj₂ y} {inj₂ y₁} x-eq y-eq = HasTerminal.to-terminal-unique 𝒞-terminal _ _

-- Convert predicates on setoids to ones that forget approximation information
predicate : ∀ {X} → X .idx ⇒s 𝟚ₛ → X C.⇒ 𝟚
predicate f .idxf = f
predicate {X} f .famf .transf x = predicate-transf X x (f .func x)
predicate {X} f .famf .natural {x₁}{x₂} x₁≈x₂ =
  predicate-natural X {y₁ = f .func x₁} x₁≈x₂ (f .func-resp-≈ x₁≈x₂)

-- Helpers for binary functions on simple families
binary2 : ∀ {X Y} → (X × (Y × 𝟙)) C.⇒ (X × Y)
binary2 = P.pair P.p₁ (P.p₁ C.∘ P.p₂)

binary : ∀ {X G} → (simple[ X , G ] × (simple[ X , G ] × 𝟙)) C.⇒ simple[ X ×ₛ X , 𝒞-products .HasProducts.prod G G ]
binary = simple-monoidal C.∘ binary2

open import example-signature
open import signature
import nat
import label

BaseInterp0 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp0 .Model.⟦sort⟧ number = simple[ nat.ℕₛ , 𝟙-base ]
BaseInterp0 .Model.⟦sort⟧ label = simple[ label.Label , 𝟙-base ]
BaseInterp0 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , TWO ]
BaseInterp0 .Model.⟦op⟧ zero = simplef[ nat.zero-m , 𝒞m.id _ ]
BaseInterp0 .Model.⟦op⟧ add = simplef[ nat.add , to-𝟙-base ] C.∘ binary
BaseInterp0 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , 𝒞m.id _ ]
BaseInterp0 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp0 .Model.⟦op⟧ approx-unit = simplef[ idS _ , unit ]
BaseInterp0 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , conjunct ] C.∘ binary

BaseInterp1 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp1 .Model.⟦sort⟧ number = simple[ nat.ℕₛ , TWO ]
BaseInterp1 .Model.⟦sort⟧ label = simple[ label.Label , 𝟙-base ]
BaseInterp1 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , TWO ]
BaseInterp1 .Model.⟦op⟧ zero = simplef[ nat.zero-m , unit ]
BaseInterp1 .Model.⟦op⟧ add = simplef[ nat.add , conjunct ] C.∘ binary
BaseInterp1 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , 𝒞m.id _ ]
BaseInterp1 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp1 .Model.⟦op⟧ approx-unit = simplef[ idS _ , unit ]
BaseInterp1 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , conjunct ] C.∘ binary
