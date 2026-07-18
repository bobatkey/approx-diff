{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The initial-algebra laws at the index level, in an ambient context Γ with
-- the Γ-element fixed along each instance.
--
-- β: folding an assembled tree equals the algebra applied to the strong
-- action of the fold, which is reindexing along g γ (the fold at γ at the
-- α-entry, identity at the parameters). The shape is left fixed on both
-- sides, so the proof is a leaf-refl induction: at an α-position both sides
-- are the fold of the spliced subtree, by definition of g.
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

module Initiality {n} (ι : Fin n → Setoid os (os ⊔ es)) (Γ Y : Setoid os (os ⊔ es))
                  (P : Poly (suc n)) where
  module S' = Shapes (suc n)
  module F = Fold ι Γ Y P
  module I = InMap ι P

  private
    module ΓE = IsEquivalence (Γ .Setoid.isEquivalence)
    module YE = IsEquivalence (Y .Setoid.isEquivalence)

  module _ (alg : Γ .Setoid.Carrier → F.T'.TreeSh P params → Y .Setoid.Carrier)
           (alg-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂)
                       {s₁ s₂ : S'.Shape P params} {a₁ a₂} →
                       F.E'.Sh≈ P params s₁ s₂ a₁ a₂ →
                       Setoid._≈_ Y (alg γ₁ (s₁ , a₁)) (alg γ₂ (s₂ , a₂))) where

    g : Γ .Setoid.Carrier → ∀ v → I.ιᵢ v ⇒ F.ι' v
    g γ zero .func t = F.fold alg γ (proj₁ t) (proj₂ t)
    g γ zero .func-resp-≈ {t₁} {t₂} p =
      F.fold-resp alg alg-resp ΓE.refl {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} p
    g γ (suc i) .func x = x
    g γ (suc i) .func-resp-≈ p = p

    module Rg (γ : Γ .Setoid.Carrier) = Reindex (g γ)

    mutual
      β-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (γ : Γ .Setoid.Carrier) (fm : FMor P ρ ρ')
               (w : S'.W Q ρ') (a : I.Tᵢ.Assign w) →
               F.E'.W≈ (proj₁ (F.fold-reindex alg γ fm (proj₁ (I.in-tree fm w a)) (proj₂ (I.in-tree fm w a)))) w
                 (proj₂ (F.fold-reindex alg γ fm (proj₁ (I.in-tree fm w a)) (proj₂ (I.in-tree fm w a))))
                 (λ p → Rg.reindexIx γ (S'.labelW w p) (a p))
      β-tree {Q = Q} γ fm (S'.sup s) a = β-shape γ Q (fbind Q fm) s a

      β-shape : ∀ {j} (γ : Γ .Setoid.Carrier) (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB)
                (s : S'.Shape R ηB) (a : I.Tᵢ.AssignSh R ηB s) →
                F.E'.Sh≈ R ηB
                  (proj₁ (F.fold-shape alg γ R fm (proj₁ (I.in-shape R fm s a)) (proj₂ (I.in-shape R fm s a)))) s
                  (proj₂ (F.fold-shape alg γ R fm (proj₁ (I.in-shape R fm s a)) (proj₂ (I.in-shape R fm s a))))
                  (λ p → Rg.reindexIx γ (S'.labelSh R ηB s p) (a p))
      β-shape γ (const S) fm s a = S .Setoid.isEquivalence .IsEquivalence.refl
      β-shape γ (var v)   fm s a = β-el γ fm v s a
      β-shape γ (R₁ + R₂) fm (inj₁ s) a = β-shape γ R₁ fm s a
      β-shape γ (R₁ + R₂) fm (inj₂ s) a = β-shape γ R₂ fm s a
      β-shape γ (R₁ × R₂) fm (s₁ , s₂) a =
        β-shape γ R₁ fm s₁ (λ p → a (inj₁ p)) , β-shape γ R₂ fm s₂ (λ p → a (inj₂ p))
      β-shape γ (μ Q')    fm s a = β-tree γ fm s a

      β-el : ∀ {k} {ρ ρ'} (γ : Γ .Setoid.Carrier) (fm : FMor P ρ ρ') (v : Fin k)
             (s : S'.El (ρ' v)) (a : I.Tᵢ.AssignEl (ρ' v) s) →
             F.E'.El≈ (ρ' v)
               (proj₁ (F.fold-apply alg γ fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a)))) s
               (proj₂ (F.fold-apply alg γ fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a))))
               (λ p → Rg.reindexIx γ (S'.labelEl (ρ' v) s p) (a p))
      β-el γ fbase        zero    s a = YE.refl
      β-el γ fbase        (suc i) s a = ι i .Setoid.isEquivalence .IsEquivalence.refl
      β-el γ (fbind Q fm) zero    w a = β-tree γ fm w a
      β-el γ (fbind Q fm) (suc v) s a = β-el γ fm v s a

    β : (γ : Γ .Setoid.Carrier) (t : I.Tᵢ.TreeSh P params) →
        Setoid._≈_ Y (F.fold alg γ (proj₁ (I.inMap t)) (proj₂ (I.inMap t)))
          (alg γ (Rg.reindexSh γ {Q = P} {η = params} t))
    β γ (s , a) = alg-resp ΓE.refl (β-shape γ P fbase s a)

    module _ (h : Γ .Setoid.Carrier → I.T.Tree P params → Y .Setoid.Carrier)
             (h-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂) {t₁ t₂ : I.T.Tree P params} →
                       I.E.Tree≈ t₁ t₂ → Setoid._≈_ Y (h γ₁ t₁) (h γ₂ t₂)) where

      hg : Γ .Setoid.Carrier → ∀ v → I.ιᵢ v ⇒ F.ι' v
      hg γ zero .func = h γ
      hg γ zero .func-resp-≈ = h-resp ΓE.refl
      hg γ (suc i) .func x = x
      hg γ (suc i) .func-resp-≈ p = p

      module Rh (γ : Γ .Setoid.Carrier) = Reindex (hg γ)

      module _ (h-β : (γ : Γ .Setoid.Carrier) (t : I.Tᵢ.TreeSh P params) →
                      Setoid._≈_ Y (h γ (I.inMap t)) (alg γ (Rh.reindexSh γ {Q = P} {η = params} t))) where
        mutual
          η-tree : (γ : Γ .Setoid.Carrier) (w : F.S.W P params) (a : F.T.Assign w) →
                   Setoid._≈_ Y (h γ (w , a)) (F.fold alg γ w a)
          η-tree γ (F.S.sup s) a =
            YE.trans (YE.sym (h-resp ΓE.refl (I.inMap-out (F.S.sup s , a))))
              (YE.trans (h-β γ (I.out (F.S.sup s , a)))
                (YE.trans (alg-resp ΓE.refl (η-out-shape γ P fbase s a))
                  (YE.trans (YE.sym (β γ (I.out (F.S.sup s , a))))
                    (F.fold-resp alg alg-resp ΓE.refl (I.inMap-out (F.S.sup s , a))))))

          η-out-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (γ : Γ .Setoid.Carrier) (fm : FMor P ρ ρ')
                       (w : F.S.W Q ρ) (a : F.T.Assign w) →
                       F.E'.W≈ (proj₁ (I.out-tree fm w a)) (proj₁ (I.out-tree fm w a))
                         (λ p → Rh.reindexIx γ (S'.labelW (proj₁ (I.out-tree fm w a)) p) (proj₂ (I.out-tree fm w a) p))
                         (λ p → Rg.reindexIx γ (S'.labelW (proj₁ (I.out-tree fm w a)) p) (proj₂ (I.out-tree fm w a) p))
          η-out-tree {Q = Q} γ fm (F.S.sup s) a = η-out-shape γ Q (fbind Q fm) s a

          η-out-shape : ∀ {j} (γ : Γ .Setoid.Carrier) (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB)
                        (s : F.S.Shape R ηA) (a : F.T.AssignSh R ηA s) →
                        F.E'.Sh≈ R ηB (proj₁ (I.out-shape R fm s a)) (proj₁ (I.out-shape R fm s a))
                          (λ p → Rh.reindexIx γ (S'.labelSh R ηB (proj₁ (I.out-shape R fm s a)) p) (proj₂ (I.out-shape R fm s a) p))
                          (λ p → Rg.reindexIx γ (S'.labelSh R ηB (proj₁ (I.out-shape R fm s a)) p) (proj₂ (I.out-shape R fm s a) p))
          η-out-shape γ (const S) fm s a = S .Setoid.isEquivalence .IsEquivalence.refl
          η-out-shape γ (var v)   fm s a = η-out-el γ fm v s a
          η-out-shape γ (R₁ + R₂) fm (inj₁ s) a = η-out-shape γ R₁ fm s a
          η-out-shape γ (R₁ + R₂) fm (inj₂ s) a = η-out-shape γ R₂ fm s a
          η-out-shape γ (R₁ × R₂) fm (s₁ , s₂) a =
            η-out-shape γ R₁ fm s₁ (λ p → a (inj₁ p)) , η-out-shape γ R₂ fm s₂ (λ p → a (inj₂ p))
          η-out-shape γ (μ Q')    fm s a = η-out-tree γ fm s a

          η-out-el : ∀ {k} {ρ ρ'} (γ : Γ .Setoid.Carrier) (fm : FMor P ρ ρ') (v : Fin k)
                     (s : F.S.El (ρ v)) (a : F.T.AssignEl (ρ v) s) →
                     F.E'.El≈ (ρ' v) (proj₁ (I.out-el fm v s a)) (proj₁ (I.out-el fm v s a))
                       (λ p → Rh.reindexIx γ (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
                       (λ p → Rg.reindexIx γ (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
          η-out-el γ fbase        zero    w a = η-tree γ w a
          η-out-el γ fbase        (suc i) s a = ι i .Setoid.isEquivalence .IsEquivalence.refl
          η-out-el γ (fbind Q fm) zero    w a = η-out-tree γ fm w a
          η-out-el γ (fbind Q fm) (suc v) s a = η-out-el γ fm v s a

        η : (γ : Γ .Setoid.Carrier) (t : I.T.Tree P params) →
            Setoid._≈_ Y (h γ t) (F.fold alg γ (proj₁ t) (proj₂ t))
        η γ (w , a) = η-tree γ w a
