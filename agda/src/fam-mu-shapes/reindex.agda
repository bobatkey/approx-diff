{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Reindexing of trees along a morphism of index environments, given per
-- entry as a setoid morphism. The shape is left fixed and the assignment is
-- postcomposed at parameter positions: no recursion over the tree, and no
-- first-order morphism data for the recursion to be structural over.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using (_,_)
open import prop-setoid using (Setoid; _⇒_)
import fam-mu-shapes.shape

module fam-mu-shapes.reindex (os es : Level) where

open fam-mu-shapes.shape os es public
open _⇒_

module Reindex {n} {ι ι' : Fin n → Setoid os (os ⊔ es)} (g : ∀ i → ι i ⇒ ι' i) where
  open Shapes n

  reindexIx : (l : Setoid os (os ⊔ es) ⊎ Fin n) → Trees.Ix ι l → Trees.Ix ι' l
  reindexIx (inj₁ S) x = x
  reindexIx (inj₂ i) x = g i .func x

  reindex : ∀ {k} {Q : Poly (suc k)} {ρ} → Trees.Tree ι Q ρ → Trees.Tree ι' Q ρ
  reindex (w , a) = w , λ p → reindexIx (labelW w p) (a p)

  reindexSh : ∀ {k} {Q : Poly k} {η} → Trees.TreeSh ι Q η → Trees.TreeSh ι' Q η
  reindexSh {Q = Q} {η = η} (s , a) = s , λ p → reindexIx (labelSh Q η s p) (a p)

  module E = TreeEq ι (λ i → Setoid._≈_ (ι i))
  module E' = TreeEq ι' (λ i → Setoid._≈_ (ι' i))

  mutual
    reindex-W-resp : ∀ {k} {Q : Poly (suc k)} {ρ} {w₁ w₂ : W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                     E'.W≈ w₁ w₂ (λ p → reindexIx (labelW w₁ p) (a₁ p))
                       (λ p → reindexIx (labelW w₂ p) (a₂ p))
    reindex-W-resp {Q = Q} {ρ = ρ} {sup s₁} {sup s₂} p =
      reindex-Sh-resp Q (extend ρ (inj₂ (mkSort Q ρ))) p

    reindex-Sh-resp : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) {s₁ s₂ : Shape Q η} {a₁ a₂} →
                      E.Sh≈ Q η s₁ s₂ a₁ a₂ →
                      E'.Sh≈ Q η s₁ s₂ (λ p → reindexIx (labelSh Q η s₁ p) (a₁ p))
                        (λ p → reindexIx (labelSh Q η s₂ p) (a₂ p))
    reindex-Sh-resp (const S) η p = p
    reindex-Sh-resp (var j)   η p = reindex-El-resp (η j) p
    reindex-Sh-resp (P + Q)   η {inj₁ _} {inj₁ _} p = reindex-Sh-resp P η p
    reindex-Sh-resp (P + Q)   η {inj₂ _} {inj₂ _} p = reindex-Sh-resp Q η p
    reindex-Sh-resp (P × Q)   η {_ , _} {_ , _} (p , q) =
      reindex-Sh-resp P η p , reindex-Sh-resp Q η q
    reindex-Sh-resp (μ Q')    η {w₁} {w₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

    reindex-El-resp : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ : El r} {a₁ a₂} → E.El≈ r s₁ s₂ a₁ a₂ →
                      E'.El≈ r s₁ s₂ (λ p → reindexIx (labelEl r s₁ p) (a₁ p))
                        (λ p → reindexIx (labelEl r s₂ p) (a₂ p))
    reindex-El-resp (inj₁ i)            p = g i .func-resp-≈ p
    reindex-El-resp (inj₂ (mkSort Q ρ)) {w₁} {w₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

  reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ} {t₁ t₂ : Trees.Tree ι Q ρ} →
                 E.Tree≈ t₁ t₂ → E'.Tree≈ (reindex t₁) (reindex t₂)
  reindex-resp {t₁ = w₁ , a₁} {w₂ , a₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

-- Reindexing along pointwise-equal environment morphisms sends equal trees to
-- equal trees: the joint congruence in the morphism and the tree.
module ReindexCong {n} {ι ι' : Fin n → Setoid os (os ⊔ es)} (g₁ g₂ : ∀ i → ι i ⇒ ι' i)
                   (g≈ : ∀ i x → Setoid._≈_ (ι' i) (g₁ i .func x) (g₂ i .func x)) where
  open Shapes n
  module R₁ = Reindex g₁
  module R₂ = Reindex g₂
  module E = TreeEq ι (λ i → Setoid._≈_ (ι i))
  module E' = TreeEq ι' (λ i → Setoid._≈_ (ι' i))

  mutual
    reindex-W-cong : ∀ {k} {Q : Poly (suc k)} {ρ} {w₁ w₂ : W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                     E'.W≈ w₁ w₂ (λ p → R₁.reindexIx (labelW w₁ p) (a₁ p))
                       (λ p → R₂.reindexIx (labelW w₂ p) (a₂ p))
    reindex-W-cong {Q = Q} {ρ = ρ} {sup s₁} {sup s₂} p =
      reindex-Sh-cong Q (extend ρ (inj₂ (mkSort Q ρ))) p

    reindex-Sh-cong : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) {s₁ s₂ : Shape Q η} {a₁ a₂} →
                      E.Sh≈ Q η s₁ s₂ a₁ a₂ →
                      E'.Sh≈ Q η s₁ s₂ (λ p → R₁.reindexIx (labelSh Q η s₁ p) (a₁ p))
                        (λ p → R₂.reindexIx (labelSh Q η s₂ p) (a₂ p))
    reindex-Sh-cong (const S) η p = p
    reindex-Sh-cong (var j)   η p = reindex-El-cong (η j) p
    reindex-Sh-cong (P + Q)   η {inj₁ _} {inj₁ _} p = reindex-Sh-cong P η p
    reindex-Sh-cong (P + Q)   η {inj₂ _} {inj₂ _} p = reindex-Sh-cong Q η p
    reindex-Sh-cong (P × Q)   η {_ , _} {_ , _} (p , q) =
      reindex-Sh-cong P η p , reindex-Sh-cong Q η q
    reindex-Sh-cong (μ Q')    η {w₁} {w₂} p = reindex-W-cong {w₁ = w₁} {w₂ = w₂} p

    reindex-El-cong : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ : El r} {a₁ a₂} → E.El≈ r s₁ s₂ a₁ a₂ →
                      E'.El≈ r s₁ s₂ (λ p → R₁.reindexIx (labelEl r s₁ p) (a₁ p))
                        (λ p → R₂.reindexIx (labelEl r s₂ p) (a₂ p))
    reindex-El-cong (inj₁ i) {s₁} {s₂} {a₁} {a₂} p =
      ι' i .Setoid.isEquivalence .prop-setoid.IsEquivalence.trans
        (g₁ i .func-resp-≈ p) (g≈ i (a₂ tt))
    reindex-El-cong (inj₂ (mkSort Q ρ)) {w₁} {w₂} p = reindex-W-cong {w₁ = w₁} {w₂ = w₂} p

-- Two label-indexed maps of assignments agree pointwise: the generic
-- leaf-reflexivity induction, diagonal in the shape. Instances collapse
-- composite coercion/reindex layers against a single family.
module Pointwise {n} {ιA ιB : Fin n → Setoid os (os ⊔ es)}
                 (F G : (l : Setoid os (os ⊔ es) ⊎ Fin n) → Trees.Ix ιA l → Trees.Ix ιB l)
                 (hS : ∀ S x → Setoid._≈_ S (F (inj₁ S) x) (G (inj₁ S) x))
                 (hV : ∀ v x → Setoid._≈_ (ιB v) (F (inj₂ v) x) (G (inj₂ v) x)) where
  open Shapes n
  module EB = TreeEq ιB (λ v → Setoid._≈_ (ιB v))

  mutual
    agree-W : ∀ {k} {Q : Poly (suc k)} {ρ} (w : W Q ρ) (a : Trees.Assign ιA w) →
              EB.W≈ w w (λ p → F (labelW w p) (a p)) (λ p → G (labelW w p) (a p))
    agree-W {Q = Q} {ρ = ρ} (sup s) a = agree-Sh Q (extend ρ (inj₂ (mkSort Q ρ))) s a

    agree-Sh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s : Shape Q η)
               (a : Trees.AssignSh ιA Q η s) →
               EB.Sh≈ Q η s s (λ p → F (labelSh Q η s p) (a p)) (λ p → G (labelSh Q η s p) (a p))
    agree-Sh (const S) η s a = hS S (a tt)
    agree-Sh (var j)   η s a = agree-El (η j) s a
    agree-Sh (P + Q)   η (inj₁ s) a = agree-Sh P η s a
    agree-Sh (P + Q)   η (inj₂ s) a = agree-Sh Q η s a
    agree-Sh (P × Q)   η (s₁ , s₂) a =
      agree-Sh P η s₁ (λ p → a (inj₁ p)) , agree-Sh Q η s₂ (λ p → a (inj₂ p))
    agree-Sh (μ Q')    η s a = agree-W s a

    agree-El : ∀ (r : Fin n ⊎ Sort n) (s : El r) (a : Trees.AssignEl ιA r s) →
               EB.El≈ r s s (λ p → F (labelEl r s p) (a p)) (λ p → G (labelEl r s p) (a p))
    agree-El (inj₁ v)            s a = hV v (a tt)
    agree-El (inj₂ (mkSort Q ρ)) w a = agree-W w a
