{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The algebra map at the index level: assemble a tree of the root sort from a
-- one-level unfolding over ι[α ↦ carrier], whose α-positions hold whole
-- trees; in-el splices them in without traversing them. out decomposes at the
-- root; the two are mutually inverse up to tree equality. The carrier setoid
-- of trees at the root sort sits at the α-entry of the extended environment,
-- so its equality is tree equality and no separate relation family is needed.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid; IsEquivalence)
import fam-mu-shapes.fold

module fam-mu-shapes.in-map (os es : Level) where

open fam-mu-shapes.fold os es public
open IsEquivalence

module InMap {n} (ι : Fin n → Setoid os (os ⊔ es)) (P : Poly (suc n)) where
  module S = Shapes n
  module S' = Shapes (suc n)

  module T = Trees ι
  module E = TreeEq ι (λ i → Setoid._≈_ (ι i))
  module EE = E.Equiv (λ i x → ι i .Setoid.isEquivalence .refl)
                      (λ i p → ι i .Setoid.isEquivalence .sym p)
                      (λ i p q → ι i .Setoid.isEquivalence .trans p q)

  -- The carrier setoid of the μ-type at the root sort.
  TreeSetoid : Setoid os (os ⊔ es)
  TreeSetoid = EE.TreeSetoid P params

  ιᵢ : Fin (suc n) → Setoid os (os ⊔ es)
  ιᵢ = extend ι TreeSetoid

  module Tᵢ = Trees ιᵢ
  module Eᵢ = TreeEq ιᵢ (λ v → Setoid._≈_ (ιᵢ v))

  mutual
    in-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S'.W Q ρ') →
              Tᵢ.Assign w → T.Tree Q ρ
    in-tree {Q = Q} fm (S'.sup s) a =
      let (s' , a') = in-shape Q (fbind Q fm) s a in S.sup s' , a'

    in-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S'.Shape R ηB) →
               Tᵢ.AssignSh R ηB s → T.TreeSh R ηA
    in-shape (const S) fm s a = tt , a
    in-shape (var v)   fm s a = in-el fm v s a
    in-shape (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = in-shape R₁ fm s a in inj₁ s' , a'
    in-shape (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = in-shape R₂ fm s a in inj₂ s' , a'
    in-shape (R₁ × R₂) fm (s₁ , s₂) a =
      let (s₁' , a₁') = in-shape R₁ fm s₁ (λ p → a (inj₁ p))
          (s₂' , a₂') = in-shape R₂ fm s₂ (λ p → a (inj₂ p))
      in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
    in-shape (μ Q')    fm s a = in-tree fm s a

    in-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) →
            Tᵢ.AssignEl (ρ' v) s → T.TreeEl (ρ v)
    in-el fbase        zero    s a = a tt
    in-el fbase        (suc i) s a = tt , a
    in-el (fbind Q fm) zero    w a = in-tree fm w a
    in-el (fbind Q fm) (suc v) s a = in-el fm v s a

  inMap : Tᵢ.TreeSh P params → T.Tree P params
  inMap (s , a) = let (s' , a') = in-shape P fbase s a in S.sup s' , a'

  mutual
    out-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S.W Q ρ) →
               T.Assign w → Tᵢ.Tree Q ρ'
    out-tree {Q = Q} fm (S.sup s) a =
      let (s' , a') = out-shape Q (fbind Q fm) s a in S'.sup s' , a'

    out-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S.Shape R ηA) →
                T.AssignSh R ηA s → Tᵢ.TreeSh R ηB
    out-shape (const S) fm s a = tt , a
    out-shape (var v)   fm s a = out-el fm v s a
    out-shape (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = out-shape R₁ fm s a in inj₁ s' , a'
    out-shape (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = out-shape R₂ fm s a in inj₂ s' , a'
    out-shape (R₁ × R₂) fm (s₁ , s₂) a =
      let (s₁' , a₁') = out-shape R₁ fm s₁ (λ p → a (inj₁ p))
          (s₂' , a₂') = out-shape R₂ fm s₂ (λ p → a (inj₂ p))
      in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
    out-shape (μ Q')    fm s a = out-tree fm s a

    out-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S.El (ρ v)) →
             T.AssignEl (ρ v) s → Tᵢ.TreeEl (ρ' v)
    out-el fbase        zero    w a = tt , λ _ → (w , a)
    out-el fbase        (suc i) s a = tt , a
    out-el (fbind Q fm) zero    w a = out-tree fm w a
    out-el (fbind Q fm) (suc v) s a = out-el fm v s a

  out : T.Tree P params → Tᵢ.TreeSh P params
  out (S.sup s , a) = out-shape P fbase s a

  mutual
    io-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S.W Q ρ) (a : T.Assign w) →
              E.Tree≈ (in-tree fm (proj₁ (out-tree fm w a)) (proj₂ (out-tree fm w a))) (w , a)
    io-tree {Q = Q} fm (S.sup s) a = io-shape Q (fbind Q fm) s a

    io-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S.Shape R ηA)
               (a : T.AssignSh R ηA s) →
               E.Sh≈ R ηA (proj₁ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) s
                 (proj₂ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) a
    io-shape (const S) fm s a = S .Setoid.isEquivalence .refl
    io-shape (var v)   fm s a = io-el fm v s a
    io-shape (R₁ + R₂) fm (inj₁ s) a = io-shape R₁ fm s a
    io-shape (R₁ + R₂) fm (inj₂ s) a = io-shape R₂ fm s a
    io-shape (R₁ × R₂) fm (s₁ , s₂) a =
      io-shape R₁ fm s₁ (λ p → a (inj₁ p)) , io-shape R₂ fm s₂ (λ p → a (inj₂ p))
    io-shape (μ Q')    fm s a = io-tree fm s a

    io-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S.El (ρ v)) (a : T.AssignEl (ρ v) s) →
            E.El≈ (ρ v) (proj₁ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) s
              (proj₂ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) a
    io-el fbase        zero    w a = EE.W≈-refl w a
    io-el fbase        (suc i) s a = ι i .Setoid.isEquivalence .refl
    io-el (fbind Q fm) zero    w a = io-tree fm w a
    io-el (fbind Q fm) (suc v) s a = io-el fm v s a

  inMap-out : (t : T.Tree P params) → E.Tree≈ (inMap (out t)) t
  inMap-out (S.sup s , a) = io-shape P fbase s a

  mutual
    oi-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S'.W Q ρ') (a : Tᵢ.Assign w) →
              Eᵢ.Tree≈ (out-tree fm (proj₁ (in-tree fm w a)) (proj₂ (in-tree fm w a))) (w , a)
    oi-tree {Q = Q} fm (S'.sup s) a = oi-shape Q (fbind Q fm) s a

    oi-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S'.Shape R ηB)
               (a : Tᵢ.AssignSh R ηB s) →
               Eᵢ.Sh≈ R ηB (proj₁ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) s
                 (proj₂ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) a
    oi-shape (const S) fm s a = S .Setoid.isEquivalence .refl
    oi-shape (var v)   fm s a = oi-el fm v s a
    oi-shape (R₁ + R₂) fm (inj₁ s) a = oi-shape R₁ fm s a
    oi-shape (R₁ + R₂) fm (inj₂ s) a = oi-shape R₂ fm s a
    oi-shape (R₁ × R₂) fm (s₁ , s₂) a =
      oi-shape R₁ fm s₁ (λ p → a (inj₁ p)) , oi-shape R₂ fm s₂ (λ p → a (inj₂ p))
    oi-shape (μ Q')    fm s a = oi-tree fm s a

    oi-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) (a : Tᵢ.AssignEl (ρ' v) s) →
            Eᵢ.El≈ (ρ' v) (proj₁ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) s
              (proj₂ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) a
    oi-el fbase        zero    s a = EE.W≈-refl (proj₁ (a tt)) (proj₂ (a tt))
    oi-el fbase        (suc i) s a = ι i .Setoid.isEquivalence .refl
    oi-el (fbind Q fm) zero    w a = oi-tree fm w a
    oi-el (fbind Q fm) (suc v) s a = oi-el fm v s a

  out-inMap : (t : Tᵢ.TreeSh P params) →
              Eᵢ.Sh≈ P params (proj₁ (out (inMap t))) (proj₁ t) (proj₂ (out (inMap t))) (proj₂ t)
  out-inMap (s , a) = oi-shape P fbase s a
