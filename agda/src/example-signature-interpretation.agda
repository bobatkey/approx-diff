{-# OPTIONS --postfix-projections --prop --safe #-}

module example-signature-interpretation where

open import Level using (0ℓ; suc)
open import categories using (Category; HasProducts; HasTerminal; HasCoproducts)
import fam
import galois

------------------------------------------------------------------------------
-- Construct the category of first-order approximations
module Fam⟨LatGal⟩ = fam.CategoryOfFamilies 0ℓ 0ℓ galois.cat

open Fam⟨LatGal⟩ using (simple[_,_]; simplef[_,_])

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat = Fam⟨LatGal⟩.cat

module C = Category cat

open Fam⟨LatGal⟩.products galois.products
  using (products; simple-monoidal)
  renaming (_⊗_ to _×_)

terminal : HasTerminal cat
terminal = Fam⟨LatGal⟩.terminal galois.terminal

coproducts : HasCoproducts cat
coproducts = Fam⟨LatGal⟩.coproducts

module P = HasProducts products

_+_ = HasCoproducts.coprod coproducts
𝟙 = HasTerminal.witness terminal

𝟚 : Category.obj cat
𝟚 = 𝟙 + 𝟙

------------------------------------------------------------------------------

open import Data.Sum using (inj₁; inj₂)
open import prop-setoid using (Setoid; idS)
  renaming (⊗-setoid to _×ₛ_; +-setoid to _+ₛ_; 𝟙 to 𝟙ₛ; _⇒_ to _⇒s_; const to constₛ)
open galois using (_⊕_; _⇒g_; _∘g_; _≃g_)
import indexed-family

𝟚ₛ : Setoid 0ℓ 0ℓ
𝟚ₛ = 𝟙ₛ +ₛ 𝟙ₛ

open Fam⟨LatGal⟩.Mor
open Fam⟨LatGal⟩.Obj
open indexed-family.Fam
open indexed-family._⇒f_
open _⇒s_

private
  predicate-transf : ∀ X x y → X .fam .fm x ⇒g 𝟚 .fam .fm y
  predicate-transf X x (inj₁ _) = galois.to-𝟙 _
  predicate-transf X x (inj₂ _) = galois.to-𝟙 _

  predicate-natural : ∀ X {x₁} {x₂} {y₁} {y₂}
    (x-eq : X .idx .Setoid._≈_ x₁ x₂)
    (y-eq : 𝟚ₛ .Setoid._≈_ y₁ y₂) →
    (predicate-transf X x₂ y₂ ∘g X .fam .subst x-eq) ≃g (𝟚 .fam .subst {y₁} {y₂} y-eq ∘g predicate-transf X x₁ y₁)
  predicate-natural X {x₁} {x₂} {inj₁ x} {inj₁ x₃} x-eq y-eq = HasTerminal.to-terminal-unique galois.terminal _ _
  predicate-natural X {x₁} {x₂} {inj₂ y} {inj₂ y₁} x-eq y-eq = HasTerminal.to-terminal-unique galois.terminal _ _

-- Convert predicates on setoids to ones that forget approximation information
predicate : ∀ {X} → X .idx ⇒s 𝟚ₛ → X C.⇒ 𝟚
predicate f .idxf = f
predicate {X} f .famf .transf x = predicate-transf X x (f .func x)
predicate {X} f .famf .natural {x₁}{x₂} x₁≈x₂ =
  predicate-natural X {y₁ = f .func x₁} x₁≈x₂ (f .func-resp-≈ x₁≈x₂)

-- Helpers for binary functions on simple families
binary2 : ∀ {X Y} → (X × (Y × 𝟙)) C.⇒ (X × Y)
binary2 = P.pair P.p₁ (P.p₁ C.∘ P.p₂)

binary : ∀ {X G} → (simple[ X , G ] × (simple[ X , G ] × 𝟙)) C.⇒ simple[ X ×ₛ X , G ⊕ G ]
binary = simple-monoidal C.∘ binary2

open import example-signature
open import signature
import nat
import label

BaseInterp0 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp0 .Model.⟦sort⟧ number = simple[ nat.ℕₛ , galois.𝟙 ]
BaseInterp0 .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
BaseInterp0 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
BaseInterp0 .Model.⟦op⟧ zero = simplef[ nat.zero-m , galois.idg _ ]
BaseInterp0 .Model.⟦op⟧ add = simplef[ nat.add , galois.to-𝟙 _ ] C.∘ binary
BaseInterp0 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.idg _ ]
BaseInterp0 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp0 .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
BaseInterp0 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary

BaseInterp1 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp1 .Model.⟦sort⟧ number = simple[ nat.ℕₛ , galois.TWO ]
BaseInterp1 .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
BaseInterp1 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
BaseInterp1 .Model.⟦op⟧ zero = simplef[ nat.zero-m , galois.unit ]
BaseInterp1 .Model.⟦op⟧ add = simplef[ nat.add , galois.conjunct ] C.∘ binary
BaseInterp1 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.idg _ ]
BaseInterp1 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp1 .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
BaseInterp1 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary

open import approx-numbers using (ℚ-intv; add; zero)

BaseInterp2 : Model PFPC[ cat , terminal , products , 𝟚 ] Sig
BaseInterp2 .Model.⟦sort⟧ number = ℚ-intv
BaseInterp2 .Model.⟦sort⟧ label = simple[ label.Label , galois.𝟙 ]
BaseInterp2 .Model.⟦sort⟧ approx = simple[ 𝟙ₛ , galois.TWO ]
BaseInterp2 .Model.⟦op⟧ zero = approx-numbers.zero
BaseInterp2 .Model.⟦op⟧ add = approx-numbers.add C.∘ binary2
BaseInterp2 .Model.⟦op⟧ (lbl l) = simplef[ constₛ _ l , galois.idg _ ]
BaseInterp2 .Model.⟦rel⟧ equal-label = predicate label.equal-label C.∘ binary
BaseInterp2 .Model.⟦op⟧ approx-unit = simplef[ idS _ , galois.unit ]
BaseInterp2 .Model.⟦op⟧ approx-mult = simplef[ prop-setoid.to-𝟙 , galois.conjunct ] C.∘ binary
