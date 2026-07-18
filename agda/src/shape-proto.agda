{-# OPTIONS --safe #-}

------------------------------------------------------------------------------
-- Shape-based μ-type carrier: shapes, positions, index assignments,
-- reindexing and the fold.
--
-- An inductive family of shapes needs equation constructors rho i = inj_ ...,
-- whose computed indices dependent matching on positions cannot unify;
-- computing the set of shapes by recursion fails termination, because sorts
-- are mutually recursive. Instead W has a single constructor wrapping a
-- computed one-level unfolding: W is inductive, so recursion on trees bottoms
-- out, and the unfolding is computed by matching on the polynomial, so no
-- computed indices arise. Shapes carry no leaf data; the data lives in the
-- index assignment.
--
-- n is the number of parameters (the outer context Delta); shapes and
-- positions are environment-free. The kinding environment delta enters only
-- through the index assignment of a tree.
------------------------------------------------------------------------------

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

module shape-proto where

private
  variable
    a : Level

data Poly (k : ℕ) : Set₁ where
  const : Set → Poly k
  var   : Fin k → Poly k
  _⊕_   : Poly k → Poly k → Poly k
  _⊗_   : Poly k → Poly k → Poly k
  μ     : Poly (suc k) → Poly k

-- A sort is an index-erased μ-body together with an assignment of its free
-- variables to parameters or other sorts.
data Sort (n : ℕ) : Set₁ where
  mkSort : ∀ {k} → Poly (suc k) → (Fin k → Fin n ⊎ Sort n) → Sort n

extend : ∀ {A : Set a} {k} → (Fin k → A) → A → Fin (suc k) → A
extend ρ x zero    = x
extend ρ x (suc i) = ρ i

module Shapes (n : ℕ) where

  ------------------------------------------------------------------------------
  -- Shapes. A shape of sort (mkSort Q rho) is W Q rho; Shape computes the
  -- one-level unfolding, El resolves a variable to a leaf or a sub-shape.
  ------------------------------------------------------------------------------
  mutual
    data W {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) : Set where
      sup : Shape Q (extend ρ (inj₂ (mkSort Q ρ))) → W Q ρ

    Shape : ∀ {k} → Poly k → (Fin k → Fin n ⊎ Sort n) → Set
    Shape (const X) η = ⊤                          -- one leaf, no data
    Shape (var j)   η = El (η j)
    Shape (P ⊕ Q)   η = Shape P η ⊎ Shape Q η
    Shape (P ⊗ Q)   η = Shape P η × Shape Q η
    Shape (μ Q')    η = W Q' η

    El : Fin n ⊎ Sort n → Set
    El (inj₁ p)            = ⊤                      -- parameter leaf, no data
    El (inj₂ (mkSort Q ρ)) = W Q ρ

  mutual
    PosW : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → Set
    PosW {Q = Q} {ρ = ρ} (sup s) = PosSh Q (extend ρ (inj₂ (mkSort Q ρ))) s

    PosSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Shape Q η → Set
    PosSh (const X) η s        = ⊤
    PosSh (var j)   η s        = PosEl (η j) s
    PosSh (P ⊕ Q)   η (inj₁ s) = PosSh P η s
    PosSh (P ⊕ Q)   η (inj₂ s) = PosSh Q η s
    PosSh (P ⊗ Q)   η (s₁ , s₂) = PosSh P η s₁ ⊎ PosSh Q η s₂
    PosSh (μ Q')    η s        = PosW s

    PosEl : (r : Fin n ⊎ Sort n) → El r → Set
    PosEl (inj₁ p)            s = ⊤
    PosEl (inj₂ (mkSort Q ρ)) s = PosW s

  ------------------------------------------------------------------------------
  -- The set naming a position, environment-free: a const-leaf names its set X,
  -- a parameter-leaf names its parameter (an element of Delta, here Fin n).
  ------------------------------------------------------------------------------
  mutual
    labelW : ∀ {k} {Q : Poly (suc k)} {ρ} (w : W Q ρ) → PosW w → Set ⊎ Fin n
    labelW {Q = Q} {ρ = ρ} (sup s) p = labelSh Q (extend ρ (inj₂ (mkSort Q ρ))) s p

    labelSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s : Shape Q η) →
              PosSh Q η s → Set ⊎ Fin n
    labelSh (const X) η s        p        = inj₁ X
    labelSh (var j)   η s        p        = labelEl (η j) s p
    labelSh (P ⊕ Q)   η (inj₁ s) p        = labelSh P η s p
    labelSh (P ⊕ Q)   η (inj₂ s) p        = labelSh Q η s p
    labelSh (P ⊗ Q)   η (s₁ , s₂) (inj₁ p) = labelSh P η s₁ p
    labelSh (P ⊗ Q)   η (s₁ , s₂) (inj₂ p) = labelSh Q η s₂ p
    labelSh (μ Q')    η s        p        = labelW s p

    labelEl : (r : Fin n ⊎ Sort n) (s : El r) → PosEl r s → Set ⊎ Fin n
    labelEl (inj₁ p)            s q = inj₂ p
    labelEl (inj₂ (mkSort Q ρ)) s q = labelW s q

------------------------------------------------------------------------------
-- Trees over a kinding environment δ: a shape plus an index assignment
-- sending each position to an element of the set naming it.
------------------------------------------------------------------------------
module Trees {n} (δ : Fin n → Set) where
  open Shapes n

  Ix : Set ⊎ Fin n → Set
  Ix (inj₁ X) = X
  Ix (inj₂ i) = δ i

  Assign : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → Set
  Assign w = (p : PosW w) → Ix (labelW w p)

  AssignSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Shape Q η → Set
  AssignSh Q η s = (p : PosSh Q η s) → Ix (labelSh Q η s p)

  AssignEl : (r : Fin n ⊎ Sort n) (s : El r) → Set
  AssignEl r s = (p : PosEl r s) → Ix (labelEl r s p)

  Tree : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Set
  Tree Q ρ = Σ (W Q ρ) Assign

  TreeSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Set
  TreeSh Q η = Σ (Shape Q η) (AssignSh Q η)

  TreeEl : (r : Fin n ⊎ Sort n) → Set
  TreeEl r = Σ (El r) (AssignEl r)

------------------------------------------------------------------------------
-- Tree equality: shapes agree constructor by constructor and the assignments
-- agree pointwise, defined by simultaneous recursion on the two shapes so no
-- transport along a shape equality is needed.
------------------------------------------------------------------------------
module TreeEq {n} (δ : Fin n → Set) where
  open Shapes n
  open Trees δ

  mutual
    W≈ : ∀ {k} {Q : Poly (suc k)} {ρ} (w₁ w₂ : W Q ρ) → Assign w₁ → Assign w₂ → Set
    W≈ {Q = Q} {ρ = ρ} (sup s₁) (sup s₂) a₁ a₂ =
      Sh≈ Q (extend ρ (inj₂ (mkSort Q ρ))) s₁ s₂ a₁ a₂

    Sh≈ : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s₁ s₂ : Shape Q η) →
          AssignSh Q η s₁ → AssignSh Q η s₂ → Set
    Sh≈ (const X) η s₁ s₂ a₁ a₂ = a₁ tt ≡ a₂ tt
    Sh≈ (var j)   η s₁ s₂ a₁ a₂ = El≈ (η j) s₁ s₂ a₁ a₂
    Sh≈ (P ⊕ Q)   η (inj₁ s₁) (inj₁ s₂) a₁ a₂ = Sh≈ P η s₁ s₂ a₁ a₂
    Sh≈ (P ⊕ Q)   η (inj₁ _)  (inj₂ _)  a₁ a₂ = ⊥
    Sh≈ (P ⊕ Q)   η (inj₂ _)  (inj₁ _)  a₁ a₂ = ⊥
    Sh≈ (P ⊕ Q)   η (inj₂ s₁) (inj₂ s₂) a₁ a₂ = Sh≈ Q η s₁ s₂ a₁ a₂
    Sh≈ (P ⊗ Q)   η (s₁ , t₁) (s₂ , t₂) a₁ a₂ =
      Sh≈ P η s₁ s₂ (λ p → a₁ (inj₁ p)) (λ p → a₂ (inj₁ p)) ×
      Sh≈ Q η t₁ t₂ (λ p → a₁ (inj₂ p)) (λ p → a₂ (inj₂ p))
    Sh≈ (μ Q')    η w₁ w₂ a₁ a₂ = W≈ w₁ w₂ a₁ a₂

    El≈ : (r : Fin n ⊎ Sort n) (s₁ s₂ : El r) → AssignEl r s₁ → AssignEl r s₂ → Set
    El≈ (inj₁ i)            s₁ s₂ a₁ a₂ = a₁ tt ≡ a₂ tt
    El≈ (inj₂ (mkSort Q ρ)) w₁ w₂ a₁ a₂ = W≈ w₁ w₂ a₁ a₂

  Tree≈ : ∀ {k} {Q : Poly (suc k)} {ρ} → Tree Q ρ → Tree Q ρ → Set
  Tree≈ (w₁ , a₁) (w₂ , a₂) = W≈ w₁ w₂ a₁ a₂

  TreeEl≈ : (r : Fin n ⊎ Sort n) → TreeEl r → TreeEl r → Set
  TreeEl≈ r (s₁ , a₁) (s₂ , a₂) = El≈ r s₁ s₂ a₁ a₂

  mutual
    W≈-refl : ∀ {k} {Q : Poly (suc k)} {ρ} (w : W Q ρ) (a : Assign w) → W≈ w w a a
    W≈-refl {Q = Q} {ρ = ρ} (sup s) a = Sh≈-refl Q (extend ρ (inj₂ (mkSort Q ρ))) s a

    Sh≈-refl : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s : Shape Q η)
               (a : AssignSh Q η s) → Sh≈ Q η s s a a
    Sh≈-refl (const X) η s a = refl
    Sh≈-refl (var j)   η s a = El≈-refl (η j) s a
    Sh≈-refl (P ⊕ Q)   η (inj₁ s) a = Sh≈-refl P η s a
    Sh≈-refl (P ⊕ Q)   η (inj₂ s) a = Sh≈-refl Q η s a
    Sh≈-refl (P ⊗ Q)   η (s₁ , s₂) a =
      Sh≈-refl P η s₁ (λ p → a (inj₁ p)) , Sh≈-refl Q η s₂ (λ p → a (inj₂ p))
    Sh≈-refl (μ Q')    η w a = W≈-refl w a

    El≈-refl : (r : Fin n ⊎ Sort n) (s : El r) (a : AssignEl r s) → El≈ r s s a a
    El≈-refl (inj₁ i)            s a = refl
    El≈-refl (inj₂ (mkSort Q ρ)) w a = W≈-refl w a

  mutual
    W≈-sym : ∀ {k} {Q : Poly (suc k)} {ρ} {w₁ w₂ : W Q ρ} {a₁ a₂} →
             W≈ w₁ w₂ a₁ a₂ → W≈ w₂ w₁ a₂ a₁
    W≈-sym {Q = Q} {ρ = ρ} {sup s₁} {sup s₂} p = Sh≈-sym Q (extend ρ (inj₂ (mkSort Q ρ))) p

    Sh≈-sym : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) {s₁ s₂ : Shape Q η} {a₁ a₂} →
              Sh≈ Q η s₁ s₂ a₁ a₂ → Sh≈ Q η s₂ s₁ a₂ a₁
    Sh≈-sym (const X) η p = sym p
    Sh≈-sym (var j)   η p = El≈-sym (η j) p
    Sh≈-sym (P ⊕ Q)   η {inj₁ _} {inj₁ _} p = Sh≈-sym P η p
    Sh≈-sym (P ⊕ Q)   η {inj₁ _} {inj₂ _} ()
    Sh≈-sym (P ⊕ Q)   η {inj₂ _} {inj₁ _} ()
    Sh≈-sym (P ⊕ Q)   η {inj₂ _} {inj₂ _} p = Sh≈-sym Q η p
    Sh≈-sym (P ⊗ Q)   η {_ , _} {_ , _} (p , q) = Sh≈-sym P η p , Sh≈-sym Q η q
    Sh≈-sym (μ Q')    η {w₁} {w₂} p = W≈-sym {w₁ = w₁} {w₂ = w₂} p

    El≈-sym : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ : El r} {a₁ a₂} →
              El≈ r s₁ s₂ a₁ a₂ → El≈ r s₂ s₁ a₂ a₁
    El≈-sym (inj₁ i)            p = sym p
    El≈-sym (inj₂ (mkSort Q ρ)) {w₁} {w₂} p = W≈-sym {w₁ = w₁} {w₂ = w₂} p

  mutual
    W≈-trans : ∀ {k} {Q : Poly (suc k)} {ρ} {w₁ w₂ w₃ : W Q ρ} {a₁ a₂ a₃} →
               W≈ w₁ w₂ a₁ a₂ → W≈ w₂ w₃ a₂ a₃ → W≈ w₁ w₃ a₁ a₃
    W≈-trans {Q = Q} {ρ = ρ} {sup s₁} {sup s₂} {sup s₃} p q =
      Sh≈-trans Q (extend ρ (inj₂ (mkSort Q ρ))) p q

    Sh≈-trans : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) {s₁ s₂ s₃ : Shape Q η} {a₁ a₂ a₃} →
                Sh≈ Q η s₁ s₂ a₁ a₂ → Sh≈ Q η s₂ s₃ a₂ a₃ → Sh≈ Q η s₁ s₃ a₁ a₃
    Sh≈-trans (const X) η p q = trans p q
    Sh≈-trans (var j)   η p q = El≈-trans (η j) p q
    Sh≈-trans (P ⊕ Q)   η {inj₁ _} {inj₁ _} {inj₁ _} p q = Sh≈-trans P η p q
    Sh≈-trans (P ⊕ Q)   η {inj₁ _} {inj₁ _} {inj₂ _} p ()
    Sh≈-trans (P ⊕ Q)   η {inj₁ _} {inj₂ _} ()
    Sh≈-trans (P ⊕ Q)   η {inj₂ _} {inj₁ _} ()
    Sh≈-trans (P ⊕ Q)   η {inj₂ _} {inj₂ _} {inj₁ _} p ()
    Sh≈-trans (P ⊕ Q)   η {inj₂ _} {inj₂ _} {inj₂ _} p q = Sh≈-trans Q η p q
    Sh≈-trans (P ⊗ Q)   η {_ , _} {_ , _} {_ , _} (p₁ , p₂) (q₁ , q₂) =
      Sh≈-trans P η p₁ q₁ , Sh≈-trans Q η p₂ q₂
    Sh≈-trans (μ Q')    η {w₁} {w₂} {w₃} p q = W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} p q

    El≈-trans : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ s₃ : El r} {a₁ a₂ a₃} →
                El≈ r s₁ s₂ a₁ a₂ → El≈ r s₂ s₃ a₂ a₃ → El≈ r s₁ s₃ a₁ a₃
    El≈-trans (inj₁ i)            p q = trans p q
    El≈-trans (inj₂ (mkSort Q ρ)) {w₁} {w₂} {w₃} p q = W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} p q

------------------------------------------------------------------------------
-- Reindexing along g : δ → δ' leaves the shape fixed and postcomposes the
-- assignment at parameter positions: no recursion over the tree.
------------------------------------------------------------------------------
module Reindex {n} {δ δ' : Fin n → Set} (g : ∀ i → δ i → δ' i) where
  open Shapes n

  reindexIx : (l : Set ⊎ Fin n) → Trees.Ix δ l → Trees.Ix δ' l
  reindexIx (inj₁ X) x = x
  reindexIx (inj₂ i) x = g i x

  reindex : ∀ {k} {Q : Poly (suc k)} {ρ} → Trees.Tree δ Q ρ → Trees.Tree δ' Q ρ
  reindex (w , a) = w , λ p → reindexIx (labelW w p) (a p)

  module E = TreeEq δ
  module E' = TreeEq δ'

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
    reindex-Sh-resp (const X) η p = p
    reindex-Sh-resp (var j)   η p = reindex-El-resp (η j) p
    reindex-Sh-resp (P ⊕ Q)   η {inj₁ _} {inj₁ _} p = reindex-Sh-resp P η p
    reindex-Sh-resp (P ⊕ Q)   η {inj₁ _} {inj₂ _} ()
    reindex-Sh-resp (P ⊕ Q)   η {inj₂ _} {inj₁ _} ()
    reindex-Sh-resp (P ⊕ Q)   η {inj₂ _} {inj₂ _} p = reindex-Sh-resp Q η p
    reindex-Sh-resp (P ⊗ Q)   η {_ , _} {_ , _} (p , q) =
      reindex-Sh-resp P η p , reindex-Sh-resp Q η q
    reindex-Sh-resp (μ Q')    η {w₁} {w₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

    reindex-El-resp : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ : El r} {a₁ a₂} → E.El≈ r s₁ s₂ a₁ a₂ →
                      E'.El≈ r s₁ s₂ (λ p → reindexIx (labelEl r s₁ p) (a₁ p))
                        (λ p → reindexIx (labelEl r s₂ p) (a₂ p))
    reindex-El-resp (inj₁ i)            p = cong (g i) p
    reindex-El-resp (inj₂ (mkSort Q ρ)) {w₁} {w₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

  reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ} {t₁ t₂ : Trees.Tree δ Q ρ} →
                 E.Tree≈ t₁ t₂ → E'.Tree≈ (reindex t₁) (reindex t₂)
  reindex-resp {t₁ = w₁ , a₁} {w₂ , a₂} p = reindex-W-resp {w₁ = w₁} {w₂ = w₂} p

------------------------------------------------------------------------------
-- The fold at the index level. The algebra consumes a one-level unfolding
-- over δ[α ↦ Y]: a shape of P over context (suc n) whose α-positions hold
-- folded values. Inner sorts are translated to the extended context by
-- fold-shape; FMor relates a source assignment to its translation, fbase
-- sending the root binder to the fresh parameter and fbind recording descent
-- under an inner binder, so every recursive call is structural.
------------------------------------------------------------------------------
module Fold {n} (δ : Fin n → Set) (Y : Set) (P : Poly (suc n)) where
  module S = Shapes n
  module S' = Shapes (suc n)

  δ' : Fin (suc n) → Set
  δ' = extend δ Y

  module T = Trees δ
  module T' = Trees δ'

  module E = TreeEq δ
  module E' = TreeEq δ'

  ρ₀ : Fin n → Fin n ⊎ Sort n
  ρ₀ i = inj₁ i

  ι' : Fin (suc n) → Fin (suc n) ⊎ Sort (suc n)
  ι' v = inj₁ v

  data FMor : ∀ {k} → (Fin k → Fin n ⊎ Sort n) → (Fin k → Fin (suc n) ⊎ Sort (suc n)) → Set₁ where
    fbase : FMor (extend ρ₀ (inj₂ (mkSort P ρ₀))) ι'
    fbind : ∀ {k} {ρ ρ'} (Q : Poly (suc k)) → FMor ρ ρ' →
            FMor (extend ρ (inj₂ (mkSort Q ρ))) (extend ρ' (inj₂ (mkSort Q ρ')))

  module _ (alg : T'.TreeSh P ι' → Y) where
    mutual
      fold : (w : S.W P ρ₀) → T.Assign w → Y
      fold (S.sup s) a = alg (fold-shape P fbase s a)

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor ρ ρ') (w : S.W Q ρ) →
                     T.Assign w → Σ (S'.W Q ρ') T'.Assign
      fold-reindex {Q = Q} fm (S.sup s) a =
        let (s' , a') = fold-shape Q (fbind Q fm) s a in S'.sup s' , a'

      fold-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor ηA ηB) (s : S.Shape R ηA) →
                   T.AssignSh R ηA s → T'.TreeSh R ηB
      fold-shape (const X) fm s a = tt , a
      fold-shape (var v)   fm s a = fold-apply fm v s a
      fold-shape (R₁ ⊕ R₂) fm (inj₁ s) a = let (s' , a') = fold-shape R₁ fm s a in inj₁ s' , a'
      fold-shape (R₁ ⊕ R₂) fm (inj₂ s) a = let (s' , a') = fold-shape R₂ fm s a in inj₂ s' , a'
      fold-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
        let (s₁' , a₁') = fold-shape R₁ fm s₁ (λ p → a (inj₁ p))
            (s₂' , a₂') = fold-shape R₂ fm s₂ (λ p → a (inj₂ p))
        in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
      fold-shape (μ Q')    fm s a = fold-reindex fm s a

      fold-apply : ∀ {k} {ρ ρ'} (fm : FMor ρ ρ') (v : Fin k) (s : S.El (ρ v)) →
                   T.AssignEl (ρ v) s → Σ (S'.El (ρ' v)) (T'.AssignEl (ρ' v))
      fold-apply fbase        zero    t a = tt , λ _ → fold t a
      fold-apply fbase        (suc i) s a = tt , a
      fold-apply (fbind Q fm) zero    w a = fold-reindex fm w a
      fold-apply (fbind Q fm) (suc v) s a = fold-apply fm v s a

    module _ (alg-resp : ∀ {s₁ s₂ : S'.Shape P ι'} {a₁ a₂} →
                         E'.Sh≈ P ι' s₁ s₂ a₁ a₂ → alg (s₁ , a₁) ≡ alg (s₂ , a₂)) where
      mutual
        fold-resp : ∀ {w₁ w₂ : S.W P ρ₀} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ → fold w₁ a₁ ≡ fold w₂ a₂
        fold-resp {S.sup s₁} {S.sup s₂} p = alg-resp (fold-shape-resp P fbase p)

        fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor ρ ρ')
                            {w₁ w₂ : S.W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                            E'.Tree≈ (fold-reindex fm w₁ a₁) (fold-reindex fm w₂ a₂)
        fold-reindex-resp {Q = Q} fm {S.sup s₁} {S.sup s₂} p =
          fold-shape-resp Q (fbind Q fm) p

        fold-shape-resp : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor ηA ηB)
                          {s₁ s₂ : S.Shape R ηA} {a₁ a₂} → E.Sh≈ R ηA s₁ s₂ a₁ a₂ →
                          E'.Sh≈ R ηB (proj₁ (fold-shape R fm s₁ a₁)) (proj₁ (fold-shape R fm s₂ a₂))
                            (proj₂ (fold-shape R fm s₁ a₁)) (proj₂ (fold-shape R fm s₂ a₂))
        fold-shape-resp (const X) fm p = p
        fold-shape-resp (var v)   fm p = fold-apply-resp fm v p
        fold-shape-resp (R₁ ⊕ R₂) fm {inj₁ _} {inj₁ _} p = fold-shape-resp R₁ fm p
        fold-shape-resp (R₁ ⊕ R₂) fm {inj₁ _} {inj₂ _} ()
        fold-shape-resp (R₁ ⊕ R₂) fm {inj₂ _} {inj₁ _} ()
        fold-shape-resp (R₁ ⊕ R₂) fm {inj₂ _} {inj₂ _} p = fold-shape-resp R₂ fm p
        fold-shape-resp (R₁ ⊗ R₂) fm {_ , _} {_ , _} (p , q) =
          fold-shape-resp R₁ fm p , fold-shape-resp R₂ fm q
        fold-shape-resp (μ Q')    fm {w₁} {w₂} p = fold-reindex-resp fm {w₁ = w₁} {w₂ = w₂} p

        fold-apply-resp : ∀ {k} {ρ ρ'} (fm : FMor ρ ρ') (v : Fin k)
                          {s₁ s₂ : S.El (ρ v)} {a₁ a₂} → E.El≈ (ρ v) s₁ s₂ a₁ a₂ →
                          E'.El≈ (ρ' v) (proj₁ (fold-apply fm v s₁ a₁)) (proj₁ (fold-apply fm v s₂ a₂))
                            (proj₂ (fold-apply fm v s₁ a₁)) (proj₂ (fold-apply fm v s₂ a₂))
        fold-apply-resp fbase        zero    {t₁} {t₂} p = fold-resp {w₁ = t₁} {w₂ = t₂} p
        fold-apply-resp fbase        (suc i) p = p
        fold-apply-resp (fbind Q fm) zero    {w₁} {w₂} p = fold-reindex-resp fm {w₁ = w₁} {w₂ = w₂} p
        fold-apply-resp (fbind Q fm) (suc v) p = fold-apply-resp fm v p

------------------------------------------------------------------------------
-- Smoke test: naturals as μα. ⊤ + α; the fold to ℕ computes by refl.
------------------------------------------------------------------------------
module Example-nat where
  natP : Poly 1
  natP = const ⊤ ⊕ var zero

  δ₀ : Fin 0 → Set
  δ₀ ()

  open Fold δ₀ ℕ natP

  Nat : Set
  Nat = T.Tree natP ρ₀

  zeroT : Nat
  zeroT = S.sup (inj₁ tt) , λ _ → tt

  sucT : Nat → Nat
  sucT (w , a) = S.sup (inj₂ w) , a

  algℕ : T'.TreeSh natP ι' → ℕ
  algℕ (inj₁ s , a) = 0
  algℕ (inj₂ s , a) = suc (a tt)

  toℕ : Nat → ℕ
  toℕ (w , a) = fold algℕ w a

  _ : toℕ (sucT (sucT zeroT)) ≡ 2
  _ = refl

------------------------------------------------------------------------------
-- Smoke test with a nested μ whose body mentions the outer binder: rose trees
-- as μα. ℕ × μβ.(⊤ + α × β); counting nodes computes by refl.
------------------------------------------------------------------------------
module Example-rose where
  listB : Poly 2
  listB = const ⊤ ⊕ (var (suc zero) ⊗ var zero)

  roseP : Poly 1
  roseP = const ℕ ⊗ μ listB

  δ₀ : Fin 0 → Set
  δ₀ ()

  open Fold δ₀ ℕ roseP

  Rose : Set
  Rose = T.Tree roseP ρ₀

  leaf : ℕ → Rose
  leaf x = S.sup (tt , S.sup (inj₁ tt)) , λ { (inj₁ _) → x ; (inj₂ _) → tt }

  node2 : ℕ → Rose → Rose → Rose
  node2 x (w₁ , a₁) (w₂ , a₂) =
    S.sup (tt , S.sup (inj₂ (w₁ , S.sup (inj₂ (w₂ , S.sup (inj₁ tt)))))) ,
    λ { (inj₁ _) → x
      ; (inj₂ (inj₁ p)) → a₁ p
      ; (inj₂ (inj₂ (inj₁ p))) → a₂ p
      ; (inj₂ (inj₂ (inj₂ _))) → tt }

  -- Sum the folded values sitting at the α-positions of a translated forest.
  sumF : (f : S'.W listB ι') → T'.Assign f → ℕ
  sumF (S'.sup (inj₁ _)) a = 0
  sumF (S'.sup (inj₂ (t , f))) a = a (inj₁ tt) + sumF f (λ p → a (inj₂ p))

  algCount : T'.TreeSh roseP ι' → ℕ
  algCount ((tt , f) , a) = suc (sumF f (λ p → a (inj₂ p)))

  countRose : Rose → ℕ
  countRose (w , a) = fold algCount w a

  _ : countRose (node2 5 (leaf 1) (leaf 2)) ≡ 3
  _ = refl
