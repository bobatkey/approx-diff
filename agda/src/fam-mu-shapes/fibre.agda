{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fibre layer of the shape-based Fam μ-type construction. A decoration of a
-- sort is a μ-body erasing to it, together with decorations of the sorts in
-- its assignment; the erasure appears in the decoration's index, so no
-- erasure equations arise. The fibre of a tree is the product over its
-- positions of the fibre named there, read off the decoration's constants and
-- the environment's families at the assigned indices, by recursion on the
-- shape. Transport along tree equality substitutes at the leaves; its laws
-- follow the same recursion, with the product laws at the pairs.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor)
open import indexed-family using (Fam)
import setoid-cat
import fam
import polynomial-functor
import fam-mu-shapes.shape

module fam-mu-shapes.fibre {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open Category 𝒞 public
open HasProducts P public
open fam.CategoryOfFamilies os (os ⊔ es) 𝒞 public
open Obj public
open Mor public
open _≃_ public
open Fam public
open indexed-family._⇒f_ public
module Fam𝒞 = Category cat
open products P public
module Fam𝒞-P = HasProducts products

module Sh = fam-mu-shapes.shape os es
open Sh using (mkSort)

Poly-C = polynomial-functor.Poly cat
open polynomial-functor.Poly public
open polynomial-functor using (extend; Poly-map) public
open polynomial-functor.Interp (terminal T) products strongCoproducts public
  using (fobj; HasMu; HasMuLaws)

private module SC = Category (setoid-cat.SetoidCat os (os ⊔ es))

-- The index functor: a family to its index setoid, a morphism to its index map.
Idx : Functor cat (setoid-cat.SetoidCat os (os ⊔ es))
Idx .Functor.fobj X = X .idx
Idx .Functor.fmor f = f .idxf
Idx .Functor.fmor-cong e = e .idxf-eq
Idx .Functor.fmor-id = SC.≈-refl
Idx .Functor.fmor-comp f g = SC.≈-refl

∣_∣ : ∀ {n} → Poly-C n → Sh.Poly n
∣_∣ = Poly-map Idx

private
  ℓD : Level
  ℓD = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

-- A decoration of a sort: a μ-body erasing to it, with the sorts in its
-- assignment decorated in turn. Decorations mention no environment, so they
-- are shared by every fibre instantiation at the same context.
module Decos (n : ℕ) where
  data Deco : Sh.Sort n → Set ℓD

  DecoAssign : Fin n ⊎ Sh.Sort n → Set ℓD
  DecoAssign (inj₁ _) = Lift ℓD ⊤
  DecoAssign (inj₂ s) = Deco s

  data Deco where
    mkDeco : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n} →
             ((i : Fin k) → DecoAssign (ρ̄ i)) → Deco (mkSort ∣ Q ∣ ρ̄)

  -- The body environment of a decorated μ-binder: slot 0 is the binder's own
  -- decoration, the rest are the ambient ones.
  deco-ext : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
             (d : ∀ i → DecoAssign (ρ̄ i)) →
             ∀ i → DecoAssign (extend ρ̄ (inj₂ (mkSort ∣ Q ∣ ρ̄)) i)
  deco-ext Q d Fin.zero = mkDeco Q d
  deco-ext Q d (Fin.suc i) = d i

module Fibre {n} (ι : Fin n → Setoid os (os ⊔ es)) (δf : ∀ i → Fam (ι i) 𝒞) where
  open Sh.Shapes n
  open Sh.Trees ι
  open Decos n public
  module E = Sh.TreeEq ι (λ i → Setoid._≈_ (ι i))
  module EE = E.Equiv (λ i x → ι i .Setoid.isEquivalence .prop-setoid.IsEquivalence.refl)
                      (λ i p → ι i .Setoid.isEquivalence .prop-setoid.IsEquivalence.sym p)
                      (λ i p q → ι i .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans p q)

  -- The fibre object at each tree: 𝒞-products at ×, the named family's object
  -- at the assigned index at each leaf.
  mutual
    fib : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
          (d : ∀ i → DecoAssign (ρ̄ i)) (w : W ∣ Q ∣ ρ̄) → Assign w → obj
    fib Q d (sup s) a = fib-shape Q (deco-ext Q d) s a

    fib-shape : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (η̄ i)) (s : Shape ∣ Q ∣ η̄) → AssignSh ∣ Q ∣ η̄ s → obj
    fib-shape (const A) d s a = A .fam .fm (a tt)
    fib-shape (var i)   d s a = fib-el _ (d i) s a
    fib-shape (P + Q) d (inj₁ s) a = fib-shape P d s a
    fib-shape (P + Q) d (inj₂ s) a = fib-shape Q d s a
    fib-shape (P × Q) d (s₁ , s₂) a =
      prod (fib-shape P d s₁ (λ p → a (inj₁ p))) (fib-shape Q d s₂ (λ p → a (inj₂ p)))
    fib-shape (μ Q') d s a = fib Q' d s a

    fib-el : (r : Fin n ⊎ Sh.Sort n) → DecoAssign r → (s : El r) → AssignEl r s → obj
    fib-el (inj₁ p) _ s a = δf p .fm (a tt)
    fib-el (inj₂ _) (mkDeco Q ρd) w a = fib Q ρd w a

  -- Transport of fibres along tree equality.
  mutual
    fib-subst : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (ρ̄ i)) {w₁ w₂ : W ∣ Q ∣ ρ̄} {a₁ a₂} →
                E.W≈ w₁ w₂ a₁ a₂ → fib Q d w₁ a₁ ⇒ fib Q d w₂ a₂
    fib-subst Q d {sup s₁} {sup s₂} p = fib-shape-subst Q (deco-ext Q d) p

    fib-shape-subst : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                      (d : ∀ i → DecoAssign (η̄ i)) {s₁ s₂ : Shape ∣ Q ∣ η̄} {a₁ a₂} →
                      E.Sh≈ ∣ Q ∣ η̄ s₁ s₂ a₁ a₂ →
                      fib-shape Q d s₁ a₁ ⇒ fib-shape Q d s₂ a₂
    fib-shape-subst (const A) d p = A .fam .subst p
    fib-shape-subst (var i)   d p = fib-el-subst _ (d i) p
    fib-shape-subst (P + Q) d {inj₁ _} {inj₁ _} p = fib-shape-subst P d p
    fib-shape-subst (P + Q) d {inj₂ _} {inj₂ _} p = fib-shape-subst Q d p
    fib-shape-subst (P × Q) d {_ , _} {_ , _} (p₁ , p₂) =
      prod-m (fib-shape-subst P d p₁) (fib-shape-subst Q d p₂)
    fib-shape-subst (μ Q') d {w₁} {w₂} p = fib-subst Q' d {w₁ = w₁} {w₂ = w₂} p

    fib-el-subst : ∀ (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) {s₁ s₂ : El r} {a₁ a₂} →
                   E.El≈ r s₁ s₂ a₁ a₂ → fib-el r dr s₁ a₁ ⇒ fib-el r dr s₂ a₂
    fib-el-subst (inj₁ p) _ e = δf p .subst e
    fib-el-subst (inj₂ _) (mkDeco Q ρd) {w₁} {w₂} e = fib-subst Q ρd {w₁ = w₁} {w₂ = w₂} e

  -- Transport along reflexivity is the identity.
  mutual
    fib-refl* : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                (d : ∀ i → DecoAssign (ρ̄ i)) (w : W ∣ Q ∣ ρ̄) (a : Assign w) →
                fib-subst Q d {w₁ = w} {w₂ = w} (EE.W≈-refl w a) ≈ id (fib Q d w a)
    fib-refl* Q d (sup s) a = fib-shape-refl* Q (deco-ext Q d) s a

    fib-shape-refl* : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                      (d : ∀ i → DecoAssign (η̄ i)) (s : Shape ∣ Q ∣ η̄) (a : AssignSh ∣ Q ∣ η̄ s) →
                      fib-shape-subst Q d (EE.Sh≈-refl ∣ Q ∣ η̄ s a) ≈ id (fib-shape Q d s a)
    fib-shape-refl* (const A) d s a = A .fam .refl*
    fib-shape-refl* (var i)   d s a = fib-el-refl* _ (d i) s a
    fib-shape-refl* (P + Q) d (inj₁ s) a = fib-shape-refl* P d s a
    fib-shape-refl* (P + Q) d (inj₂ s) a = fib-shape-refl* Q d s a
    fib-shape-refl* (P × Q) d (s₁ , s₂) a =
      ≈-trans (prod-m-cong (fib-shape-refl* P d s₁ (λ p → a (inj₁ p)))
                (fib-shape-refl* Q d s₂ (λ p → a (inj₂ p))))
        prod-m-id
    fib-shape-refl* (μ Q') d s a = fib-refl* Q' d s a

    fib-el-refl* : (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) (s : El r) (a : AssignEl r s) →
                   fib-el-subst r dr (EE.El≈-refl r s a) ≈ id (fib-el r dr s a)
    fib-el-refl* (inj₁ p) _ s a = δf p .refl*
    fib-el-refl* (inj₂ _) (mkDeco Q ρd) w a = fib-refl* Q ρd w a

  -- Transport is functorial: a composite is the composite of the transports.
  mutual
    fib-trans* : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
                 (d : ∀ i → DecoAssign (ρ̄ i)) {w₁ w₂ w₃ : W ∣ Q ∣ ρ̄} {a₁ a₂ a₃}
                 (q : E.W≈ w₂ w₃ a₂ a₃) (p : E.W≈ w₁ w₂ a₁ a₂) →
                 fib-subst Q d {w₁ = w₁} {w₂ = w₃}
                   (EE.W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} p q)
                   ≈ (fib-subst Q d {w₁ = w₂} {w₂ = w₃} q ∘ fib-subst Q d {w₁ = w₁} {w₂ = w₂} p)
    fib-trans* Q d {sup s₁} {sup s₂} {sup s₃} q p = fib-shape-trans* Q (deco-ext Q d) q p

    fib-shape-trans* : ∀ {j} (Q : Poly-C j) {η̄ : Fin j → Fin n ⊎ Sh.Sort n}
                       (d : ∀ i → DecoAssign (η̄ i)) {s₁ s₂ s₃ : Shape ∣ Q ∣ η̄} {a₁ a₂ a₃}
                       (q : E.Sh≈ ∣ Q ∣ η̄ s₂ s₃ a₂ a₃) (p : E.Sh≈ ∣ Q ∣ η̄ s₁ s₂ a₁ a₂) →
                       fib-shape-subst Q d (EE.Sh≈-trans ∣ Q ∣ η̄ p q)
                         ≈ (fib-shape-subst Q d q ∘ fib-shape-subst Q d p)
    fib-shape-trans* (const A) d q p = A .fam .trans* q p
    fib-shape-trans* (var i)   d q p = fib-el-trans* _ (d i) q p
    fib-shape-trans* (P + Q) d {inj₁ _} {inj₁ _} {inj₁ _} q p = fib-shape-trans* P d q p
    fib-shape-trans* (P + Q) d {inj₂ _} {inj₂ _} {inj₂ _} q p = fib-shape-trans* Q d q p
    fib-shape-trans* (P × Q) d {_ , _} {_ , _} {_ , _} (q₁ , q₂) (p₁ , p₂) =
      ≈-trans (prod-m-cong (fib-shape-trans* P d q₁ p₁) (fib-shape-trans* Q d q₂ p₂))
              (prod-m-comp _ _ _ _)
    fib-shape-trans* (μ Q') d {w₁} {w₂} {w₃} q p =
      fib-trans* Q' d {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} q p

    fib-el-trans* : ∀ (r : Fin n ⊎ Sh.Sort n) (dr : DecoAssign r) {s₁ s₂ s₃ : El r} {a₁ a₂ a₃}
                    (q : E.El≈ r s₂ s₃ a₂ a₃) (p : E.El≈ r s₁ s₂ a₁ a₂) →
                    fib-el-subst r dr (EE.El≈-trans r p q)
                      ≈ (fib-el-subst r dr q ∘ fib-el-subst r dr p)
    fib-el-trans* (inj₁ i) _ q p = δf i .trans* q p
    fib-el-trans* (inj₂ _) (mkDeco Q ρd) {w₁} {w₂} {w₃} q p =
      fib-trans* Q ρd {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} q p

  -- The fibre family of the μ-type at a decorated sort.
  WFam : ∀ {k} (Q : Poly-C (suc k)) {ρ̄ : Fin k → Fin n ⊎ Sh.Sort n}
         (d : ∀ i → DecoAssign (ρ̄ i)) → Fam (EE.TreeSetoid ∣ Q ∣ ρ̄) 𝒞
  WFam Q d .fm (w , a) = fib Q d w a
  WFam Q d .subst {w₁ , a₁} {w₂ , a₂} = fib-subst Q d {w₁ = w₁} {w₂ = w₂}
  WFam Q d .refl* {w , a} = fib-refl* Q d w a
  WFam Q d .trans* {w₁ , a₁} {w₂ , a₂} {w₃ , a₃} e₁ e₂ =
    fib-trans* Q d {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} e₁ e₂

-- The μ-type at the root sort: index by the category-free shape layer,
-- fibres by the canonical decoration, which resolves the μ-body's free
-- variables to the parameters.
μObj : ∀ {n} → Poly-C (suc n) → (Fin n → Obj) → Obj
μObj P δ .idx = Fibre.EE.TreeSetoid (λ i → δ i .idx) (λ i → δ i .fam) ∣ P ∣ (λ i → inj₁ i)
μObj P δ .fam = Fibre.WFam (λ i → δ i .idx) (λ i → δ i .fam) P {ρ̄ = λ i → inj₁ i} (λ i → lift tt)
