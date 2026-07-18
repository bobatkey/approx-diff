{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The fold (catamorphism) at the index level, in an ambient context Γ so no
-- exponentials are required: the algebra and the fold take a Γ-element,
-- threaded unchanged through the recursion. The algebra consumes a one-level
-- unfolding over ι[α ↦ Y]: a shape of P over context (suc n) whose
-- α-positions hold folded values. Inner sorts are translated to the extended
-- context by fold-shape; FMor relates a source assignment to its translation,
-- fbase sending the root binder to the fresh parameter and fbind recording
-- descent under an inner binder, so every recursive call is structural.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid; IsEquivalence)
import fam-mu-shapes.reindex

module fam-mu-shapes.fold (os es : Level) where

open fam-mu-shapes.reindex os es public

-- The identity assignment, sending each variable to the matching parameter,
-- and the body environment of a root binder.
params : ∀ {n} → Fin n → Fin n ⊎ Sort n
params i = inj₁ i

η₀ : ∀ {n} → Poly (suc n) → Fin (suc n) → Fin n ⊎ Sort n
η₀ P = extend params (inj₂ (mkSort P params))

-- Relates a source assignment over n to its translation over suc n: fbase
-- sends the root binder of P to the fresh parameter, fbind records descent
-- under an inner binder. First-order so that recursion over it is structural;
-- shared by the fold and the algebra map.
data FMor {n} (P : Poly (suc n)) : ∀ {k} → (Fin k → Fin n ⊎ Sort n) →
                                   (Fin k → Fin (suc n) ⊎ Sort (suc n)) →
                                   Set (lsuc os ⊔ lsuc es) where
  fbase : FMor P (η₀ P) params
  fbind : ∀ {k} {ρ ρ'} (Q : Poly (suc k)) → FMor P ρ ρ' →
          FMor P (extend ρ (inj₂ (mkSort Q ρ))) (extend ρ' (inj₂ (mkSort Q ρ')))

module Fold {n} (ι : Fin n → Setoid os (os ⊔ es)) (Γ Y : Setoid os (os ⊔ es))
            (P : Poly (suc n)) where
  module S = Shapes n
  module S' = Shapes (suc n)

  ι' : Fin (suc n) → Setoid os (os ⊔ es)
  ι' = extend ι Y

  module T = Trees ι
  module T' = Trees ι'

  module E = TreeEq ι (λ i → Setoid._≈_ (ι i))
  module E' = TreeEq ι' (λ i → Setoid._≈_ (ι' i))

  module _ (alg : Γ .Setoid.Carrier → T'.TreeSh P params → Y .Setoid.Carrier) where
    mutual
      fold : Γ .Setoid.Carrier → (w : S.W P params) → T.Assign w → Y .Setoid.Carrier
      fold γ (S.sup s) a = alg γ (fold-shape γ P fbase s a)

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (γ : Γ .Setoid.Carrier)
                     (fm : FMor P ρ ρ') (w : S.W Q ρ) → T.Assign w → Σ (S'.W Q ρ') T'.Assign
      fold-reindex {Q = Q} γ fm (S.sup s) a =
        let (s' , a') = fold-shape γ Q (fbind Q fm) s a in S'.sup s' , a'

      fold-shape : ∀ {j} (γ : Γ .Setoid.Carrier) (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB)
                   (s : S.Shape R ηA) → T.AssignSh R ηA s → T'.TreeSh R ηB
      fold-shape γ (const S) fm s a = tt , a
      fold-shape γ (var v)   fm s a = fold-apply γ fm v s a
      fold-shape γ (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = fold-shape γ R₁ fm s a in inj₁ s' , a'
      fold-shape γ (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = fold-shape γ R₂ fm s a in inj₂ s' , a'
      fold-shape γ (R₁ × R₂) fm (s₁ , s₂) a =
        let (s₁' , a₁') = fold-shape γ R₁ fm s₁ (λ p → a (inj₁ p))
            (s₂' , a₂') = fold-shape γ R₂ fm s₂ (λ p → a (inj₂ p))
        in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
      fold-shape γ (μ Q')    fm s a = fold-reindex γ fm s a

      fold-apply : ∀ {k} {ρ ρ'} (γ : Γ .Setoid.Carrier) (fm : FMor P ρ ρ') (v : Fin k)
                   (s : S.El (ρ v)) → T.AssignEl (ρ v) s → Σ (S'.El (ρ' v)) (T'.AssignEl (ρ' v))
      fold-apply γ fbase        zero    t a = tt , λ _ → fold γ t a
      fold-apply γ fbase        (suc i) s a = tt , a
      fold-apply γ (fbind Q fm) zero    w a = fold-reindex γ fm w a
      fold-apply γ (fbind Q fm) (suc v) s a = fold-apply γ fm v s a

    module _ (alg-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂)
                         {s₁ s₂ : S'.Shape P params} {a₁ a₂} →
                         E'.Sh≈ P params s₁ s₂ a₁ a₂ →
                         Setoid._≈_ Y (alg γ₁ (s₁ , a₁)) (alg γ₂ (s₂ , a₂))) where
      mutual
        fold-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂) {w₁ w₂ : S.W P params} {a₁ a₂} →
                    E.W≈ w₁ w₂ a₁ a₂ → Setoid._≈_ Y (fold γ₁ w₁ a₁) (fold γ₂ w₂ a₂)
        fold-resp γ≈ {S.sup s₁} {S.sup s₂} p = alg-resp γ≈ (fold-shape-resp γ≈ P fbase p)

        fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂)
                            (fm : FMor P ρ ρ') {w₁ w₂ : S.W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                            E'.Tree≈ (fold-reindex γ₁ fm w₁ a₁) (fold-reindex γ₂ fm w₂ a₂)
        fold-reindex-resp {Q = Q} γ≈ fm {S.sup s₁} {S.sup s₂} p =
          fold-shape-resp γ≈ Q (fbind Q fm) p

        fold-shape-resp : ∀ {j} {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂) (R : Poly j) {ηA ηB}
                          (fm : FMor P ηA ηB) {s₁ s₂ : S.Shape R ηA} {a₁ a₂} →
                          E.Sh≈ R ηA s₁ s₂ a₁ a₂ →
                          E'.Sh≈ R ηB (proj₁ (fold-shape γ₁ R fm s₁ a₁)) (proj₁ (fold-shape γ₂ R fm s₂ a₂))
                            (proj₂ (fold-shape γ₁ R fm s₁ a₁)) (proj₂ (fold-shape γ₂ R fm s₂ a₂))
        fold-shape-resp γ≈ (const S) fm p = p
        fold-shape-resp γ≈ (var v)   fm p = fold-apply-resp γ≈ fm v p
        fold-shape-resp γ≈ (R₁ + R₂) fm {inj₁ _} {inj₁ _} p = fold-shape-resp γ≈ R₁ fm p
        fold-shape-resp γ≈ (R₁ + R₂) fm {inj₂ _} {inj₂ _} p = fold-shape-resp γ≈ R₂ fm p
        fold-shape-resp γ≈ (R₁ × R₂) fm {_ , _} {_ , _} (p , q) =
          fold-shape-resp γ≈ R₁ fm p , fold-shape-resp γ≈ R₂ fm q
        fold-shape-resp γ≈ (μ Q')    fm {w₁} {w₂} p = fold-reindex-resp γ≈ fm {w₁ = w₁} {w₂ = w₂} p

        fold-apply-resp : ∀ {k} {ρ ρ'} {γ₁ γ₂} (γ≈ : Setoid._≈_ Γ γ₁ γ₂) (fm : FMor P ρ ρ')
                          (v : Fin k) {s₁ s₂ : S.El (ρ v)} {a₁ a₂} → E.El≈ (ρ v) s₁ s₂ a₁ a₂ →
                          E'.El≈ (ρ' v) (proj₁ (fold-apply γ₁ fm v s₁ a₁)) (proj₁ (fold-apply γ₂ fm v s₂ a₂))
                            (proj₂ (fold-apply γ₁ fm v s₁ a₁)) (proj₂ (fold-apply γ₂ fm v s₂ a₂))
        fold-apply-resp γ≈ fbase        zero    {t₁} {t₂} p = fold-resp γ≈ {w₁ = t₁} {w₂ = t₂} p
        fold-apply-resp γ≈ fbase        (suc i) p = p
        fold-apply-resp γ≈ (fbind Q fm) zero    {w₁} {w₂} p = fold-reindex-resp γ≈ fm {w₁ = w₁} {w₂ = w₂} p
        fold-apply-resp γ≈ (fbind Q fm) (suc v) p = fold-apply-resp γ≈ fm v p
