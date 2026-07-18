{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The initial-algebra laws at the index level.
--
-- β: folding an assembled tree equals the algebra applied to the strong
-- action of the fold, which is reindexing along g (fold at the α-entry,
-- identity at the parameters). The shape is left fixed on both sides, so the
-- proof is a leaf-refl induction: at an α-position both sides are the fold of
-- the spliced subtree, by definition of g.
--
-- η: any h satisfying the β square agrees with the fold, by tree induction.
-- Each tree is rounded through the root decomposition so that both β squares
-- apply; the two strong actions then agree pointwise by the induction
-- hypothesis at the subtrees bundled at α-positions.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid; IsEquivalence; _⇒_)
import fam-mu-shapes.in-map

module fam-mu-shapes.initiality (os es : Level) where

open fam-mu-shapes.in-map os es public
open _⇒_

module Initiality {n} (ι : Fin n → Setoid os (os ⊔ es)) (Y : Setoid os (os ⊔ es))
                  (P : Poly (suc n)) where
  module S' = Shapes (suc n)
  module F = Fold ι Y P
  module I = InMap ι P

  private
    module YE = IsEquivalence (Y .Setoid.isEquivalence)

  module _ (alg : F.T'.TreeSh P params → Y .Setoid.Carrier)
           (alg-resp : ∀ {s₁ s₂ : S'.Shape P params} {a₁ a₂} →
                       F.E'.Sh≈ P params s₁ s₂ a₁ a₂ →
                       Setoid._≈_ Y (alg (s₁ , a₁)) (alg (s₂ , a₂))) where

    g : ∀ v → I.ιᵢ v ⇒ F.ι' v
    g zero .func t = F.fold alg (proj₁ t) (proj₂ t)
    g zero .func-resp-≈ {t₁} {t₂} p =
      F.fold-resp alg alg-resp {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} p
    g (suc i) .func x = x
    g (suc i) .func-resp-≈ p = p

    module Rg = Reindex g

    mutual
      β-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S'.W Q ρ') (a : I.Tᵢ.Assign w) →
               F.E'.W≈ (proj₁ (F.fold-reindex alg fm (proj₁ (I.in-tree fm w a)) (proj₂ (I.in-tree fm w a)))) w
                 (proj₂ (F.fold-reindex alg fm (proj₁ (I.in-tree fm w a)) (proj₂ (I.in-tree fm w a))))
                 (λ p → Rg.reindexIx (S'.labelW w p) (a p))
      β-tree {Q = Q} fm (S'.sup s) a = β-shape Q (fbind Q fm) s a

      β-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S'.Shape R ηB)
                (a : I.Tᵢ.AssignSh R ηB s) →
                F.E'.Sh≈ R ηB
                  (proj₁ (F.fold-shape alg R fm (proj₁ (I.in-shape R fm s a)) (proj₂ (I.in-shape R fm s a)))) s
                  (proj₂ (F.fold-shape alg R fm (proj₁ (I.in-shape R fm s a)) (proj₂ (I.in-shape R fm s a))))
                  (λ p → Rg.reindexIx (S'.labelSh R ηB s p) (a p))
      β-shape (const S) fm s a = S .Setoid.isEquivalence .IsEquivalence.refl
      β-shape (var v)   fm s a = β-el fm v s a
      β-shape (R₁ + R₂) fm (inj₁ s) a = β-shape R₁ fm s a
      β-shape (R₁ + R₂) fm (inj₂ s) a = β-shape R₂ fm s a
      β-shape (R₁ × R₂) fm (s₁ , s₂) a =
        β-shape R₁ fm s₁ (λ p → a (inj₁ p)) , β-shape R₂ fm s₂ (λ p → a (inj₂ p))
      β-shape (μ Q')    fm s a = β-tree fm s a

      β-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) (a : I.Tᵢ.AssignEl (ρ' v) s) →
             F.E'.El≈ (ρ' v)
               (proj₁ (F.fold-apply alg fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a)))) s
               (proj₂ (F.fold-apply alg fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a))))
               (λ p → Rg.reindexIx (S'.labelEl (ρ' v) s p) (a p))
      β-el fbase        zero    s a = YE.refl
      β-el fbase        (suc i) s a = ι i .Setoid.isEquivalence .IsEquivalence.refl
      β-el (fbind Q fm) zero    w a = β-tree fm w a
      β-el (fbind Q fm) (suc v) s a = β-el fm v s a

    β : (t : I.Tᵢ.TreeSh P params) →
        Setoid._≈_ Y (F.fold alg (proj₁ (I.inMap t)) (proj₂ (I.inMap t)))
          (alg (Rg.reindexSh {Q = P} {η = params} t))
    β (s , a) = alg-resp (β-shape P fbase s a)

    module _ (h : I.T.Tree P params → Y .Setoid.Carrier)
             (h-resp : ∀ {t₁ t₂ : I.T.Tree P params} → I.E.Tree≈ t₁ t₂ →
                       Setoid._≈_ Y (h t₁) (h t₂)) where

      hg : ∀ v → I.ιᵢ v ⇒ F.ι' v
      hg zero .func = h
      hg zero .func-resp-≈ = h-resp
      hg (suc i) .func x = x
      hg (suc i) .func-resp-≈ p = p

      module Rh = Reindex hg

      module _ (h-β : (t : I.Tᵢ.TreeSh P params) →
                      Setoid._≈_ Y (h (I.inMap t)) (alg (Rh.reindexSh {Q = P} {η = params} t))) where
        mutual
          η-tree : (w : F.S.W P params) (a : F.T.Assign w) →
                   Setoid._≈_ Y (h (w , a)) (F.fold alg w a)
          η-tree (F.S.sup s) a =
            YE.trans (YE.sym (h-resp (I.inMap-out (F.S.sup s , a))))
              (YE.trans (h-β (I.out (F.S.sup s , a)))
                (YE.trans (alg-resp (η-out-shape P fbase s a))
                  (YE.trans (YE.sym (β (I.out (F.S.sup s , a))))
                    (F.fold-resp alg alg-resp (I.inMap-out (F.S.sup s , a))))))

          η-out-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : F.S.W Q ρ)
                       (a : F.T.Assign w) →
                       F.E'.W≈ (proj₁ (I.out-tree fm w a)) (proj₁ (I.out-tree fm w a))
                         (λ p → Rh.reindexIx (S'.labelW (proj₁ (I.out-tree fm w a)) p) (proj₂ (I.out-tree fm w a) p))
                         (λ p → Rg.reindexIx (S'.labelW (proj₁ (I.out-tree fm w a)) p) (proj₂ (I.out-tree fm w a) p))
          η-out-tree {Q = Q} fm (F.S.sup s) a = η-out-shape Q (fbind Q fm) s a

          η-out-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : F.S.Shape R ηA)
                        (a : F.T.AssignSh R ηA s) →
                        F.E'.Sh≈ R ηB (proj₁ (I.out-shape R fm s a)) (proj₁ (I.out-shape R fm s a))
                          (λ p → Rh.reindexIx (S'.labelSh R ηB (proj₁ (I.out-shape R fm s a)) p) (proj₂ (I.out-shape R fm s a) p))
                          (λ p → Rg.reindexIx (S'.labelSh R ηB (proj₁ (I.out-shape R fm s a)) p) (proj₂ (I.out-shape R fm s a) p))
          η-out-shape (const S) fm s a = S .Setoid.isEquivalence .IsEquivalence.refl
          η-out-shape (var v)   fm s a = η-out-el fm v s a
          η-out-shape (R₁ + R₂) fm (inj₁ s) a = η-out-shape R₁ fm s a
          η-out-shape (R₁ + R₂) fm (inj₂ s) a = η-out-shape R₂ fm s a
          η-out-shape (R₁ × R₂) fm (s₁ , s₂) a =
            η-out-shape R₁ fm s₁ (λ p → a (inj₁ p)) , η-out-shape R₂ fm s₂ (λ p → a (inj₂ p))
          η-out-shape (μ Q')    fm s a = η-out-tree fm s a

          η-out-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : F.S.El (ρ v))
                     (a : F.T.AssignEl (ρ v) s) →
                     F.E'.El≈ (ρ' v) (proj₁ (I.out-el fm v s a)) (proj₁ (I.out-el fm v s a))
                       (λ p → Rh.reindexIx (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
                       (λ p → Rg.reindexIx (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
          η-out-el fbase        zero    w a = η-tree w a
          η-out-el fbase        (suc i) s a = ι i .Setoid.isEquivalence .IsEquivalence.refl
          η-out-el (fbind Q fm) zero    w a = η-out-tree fm w a
          η-out-el (fbind Q fm) (suc v) s a = η-out-el fm v s a

        η : (t : I.T.Tree P params) → Setoid._≈_ Y (h t) (F.fold alg (proj₁ t) (proj₂ t))
        η (w , a) = η-tree w a
