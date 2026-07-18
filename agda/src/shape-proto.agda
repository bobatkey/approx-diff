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

open import Level using (Level; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

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
-- transport along a shape equality is needed. Values at parameter leaves are
-- compared by a supplied relation R, values at constant leaves by ≡.
------------------------------------------------------------------------------
module TreeEq {n} (δ : Fin n → Set) (R : ∀ i → δ i → δ i → Set) where
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
    El≈ (inj₁ i)            s₁ s₂ a₁ a₂ = R i (a₁ tt) (a₂ tt)
    El≈ (inj₂ (mkSort Q ρ)) w₁ w₂ a₁ a₂ = W≈ w₁ w₂ a₁ a₂

  Tree≈ : ∀ {k} {Q : Poly (suc k)} {ρ} → Tree Q ρ → Tree Q ρ → Set
  Tree≈ (w₁ , a₁) (w₂ , a₂) = W≈ w₁ w₂ a₁ a₂

  TreeEl≈ : (r : Fin n ⊎ Sort n) → TreeEl r → TreeEl r → Set
  TreeEl≈ r (s₁ , a₁) (s₂ , a₂) = El≈ r s₁ s₂ a₁ a₂

  module Equiv (R-refl : ∀ i (x : δ i) → R i x x)
               (R-sym : ∀ i {x y : δ i} → R i x y → R i y x)
               (R-trans : ∀ i {x y z : δ i} → R i x y → R i y z → R i x z) where
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
      El≈-refl (inj₁ i)            s a = R-refl i (a tt)
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
      El≈-sym (inj₁ i)            p = R-sym i p
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
      El≈-trans (inj₁ i)            p q = R-trans i p q
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

  reindexSh : ∀ {k} {Q : Poly k} {η} → Trees.TreeSh δ Q η → Trees.TreeSh δ' Q η
  reindexSh {Q = Q} {η = η} (s , a) = s , λ p → reindexIx (labelSh Q η s p) (a p)

  module E = TreeEq δ (λ i → _≡_)
  module E' = TreeEq δ' (λ i → _≡_)

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
-- Decorations: the data the fibre layer adds over a shape. A decorated
-- polynomial is indexed by its erasure, so a decoration of a sort needs no
-- erasure equations; parameters carry no decoration, their fibres coming from
-- the environment.
------------------------------------------------------------------------------
data Deco {k : ℕ} : Poly k → Set₁ where
  const : (X : Set) (∂X : X → Set) → Deco (const X)
  var   : (j : Fin k) → Deco (var j)
  _⊕_   : ∀ {P Q} → Deco P → Deco Q → Deco (P ⊕ Q)
  _⊗_   : ∀ {P Q} → Deco P → Deco Q → Deco (P ⊗ Q)
  μ     : ∀ {Q'} → Deco Q' → Deco (μ Q')

module Decos (n : ℕ) where
  mutual
    data DecoSort : Sort n → Set₁ where
      mkDeco : ∀ {k} {Q : Poly (suc k)} {ρ : Fin k → Fin n ⊎ Sort n} →
               Deco Q → (∀ v → DecoRef (ρ v)) → DecoSort (mkSort Q ρ)

    DecoRef : Fin n ⊎ Sort n → Set₁
    DecoRef (inj₁ i) = Lift (lsuc lzero) ⊤
    DecoRef (inj₂ σ) = DecoSort σ

  DecoEnv : ∀ {k} → (Fin k → Fin n ⊎ Sort n) → Set₁
  DecoEnv η = ∀ v → DecoRef (η v)

  extendD : ∀ {k} {η : Fin k → Fin n ⊎ Sort n} {r} → DecoEnv η → DecoRef r → DecoEnv (extend η r)
  extendD dη d zero    = d
  extendD dη d (suc v) = dη v

------------------------------------------------------------------------------
-- The fibre of a tree: the product over its positions of the fibre named
-- there, the decoration's at a constant position and the environment's (δ∂)
-- at a parameter position, computed by recursion on the shape. Transport
-- along tree equality substitutes at the leaves.
------------------------------------------------------------------------------
module Fibre {n} (δ : Fin n → Set) (δ∂ : ∀ i → δ i → Set) where
  open Shapes n
  open Trees δ
  open Decos n

  mutual
    ∂W : ∀ {k} {Q : Poly (suc k)} {ρ} → Deco Q → DecoEnv ρ → (w : W Q ρ) → Assign w → Set
    ∂W Q̂ dρ (sup s) a = ∂Sh Q̂ (extendD dρ (mkDeco Q̂ dρ)) s a

    ∂Sh : ∀ {j} {R : Poly j} (R̂ : Deco R) {η} (dη : DecoEnv η) (s : Shape R η) →
          AssignSh R η s → Set
    ∂Sh (const X ∂X) dη s a = ∂X (a tt)
    ∂Sh (var j)      dη s a = ∂El (dη j) s a
    ∂Sh (R̂₁ ⊕ R̂₂)   dη (inj₁ s) a = ∂Sh R̂₁ dη s a
    ∂Sh (R̂₁ ⊕ R̂₂)   dη (inj₂ s) a = ∂Sh R̂₂ dη s a
    ∂Sh (R̂₁ ⊗ R̂₂)   dη (s₁ , s₂) a =
      ∂Sh R̂₁ dη s₁ (λ p → a (inj₁ p)) × ∂Sh R̂₂ dη s₂ (λ p → a (inj₂ p))
    ∂Sh (μ Q̂')      dη s a = ∂W Q̂' dη s a

    ∂El : ∀ {r} → DecoRef r → (s : El r) → AssignEl r s → Set
    ∂El {inj₁ i}            _              s a = δ∂ i (a tt)
    ∂El {inj₂ (mkSort Q ρ)} (mkDeco Q̂ dρ) w a = ∂W Q̂ dρ w a

  module E = TreeEq δ (λ i → _≡_)

  mutual
    ∂W-subst : ∀ {k} {Q : Poly (suc k)} {ρ} (Q̂ : Deco Q) (dρ : DecoEnv ρ) {w₁ w₂ : W Q ρ} {a₁ a₂} →
               E.W≈ w₁ w₂ a₁ a₂ → ∂W Q̂ dρ w₁ a₁ → ∂W Q̂ dρ w₂ a₂
    ∂W-subst Q̂ dρ {sup s₁} {sup s₂} p x = ∂Sh-subst Q̂ (extendD dρ (mkDeco Q̂ dρ)) p x

    ∂Sh-subst : ∀ {j} {R : Poly j} (R̂ : Deco R) {η} (dη : DecoEnv η) {s₁ s₂ : Shape R η} {a₁ a₂} →
                E.Sh≈ R η s₁ s₂ a₁ a₂ → ∂Sh R̂ dη s₁ a₁ → ∂Sh R̂ dη s₂ a₂
    ∂Sh-subst (const X ∂X) dη p x = subst ∂X p x
    ∂Sh-subst (var j)      dη p x = ∂El-subst (dη j) p x
    ∂Sh-subst (R̂₁ ⊕ R̂₂)   dη {inj₁ _} {inj₁ _} p x = ∂Sh-subst R̂₁ dη p x
    ∂Sh-subst (R̂₁ ⊕ R̂₂)   dη {inj₁ _} {inj₂ _} ()
    ∂Sh-subst (R̂₁ ⊕ R̂₂)   dη {inj₂ _} {inj₁ _} ()
    ∂Sh-subst (R̂₁ ⊕ R̂₂)   dη {inj₂ _} {inj₂ _} p x = ∂Sh-subst R̂₂ dη p x
    ∂Sh-subst (R̂₁ ⊗ R̂₂)   dη {_ , _} {_ , _} (p , q) (x , y) =
      ∂Sh-subst R̂₁ dη p x , ∂Sh-subst R̂₂ dη q y
    ∂Sh-subst (μ Q̂')      dη {w₁} {w₂} p x = ∂W-subst Q̂' dη {w₁ = w₁} {w₂ = w₂} p x

    ∂El-subst : ∀ {r} (d : DecoRef r) {s₁ s₂ : El r} {a₁ a₂} →
                E.El≈ r s₁ s₂ a₁ a₂ → ∂El d s₁ a₁ → ∂El d s₂ a₂
    ∂El-subst {inj₁ i}            _              p x = subst (δ∂ i) p x
    ∂El-subst {inj₂ (mkSort Q ρ)} (mkDeco Q̂ dρ) {w₁} {w₂} p x = ∂W-subst Q̂ dρ {w₁ = w₁} {w₂ = w₂} p x

------------------------------------------------------------------------------
-- The fibre action of reindexing: constant positions are untouched, parameter
-- positions map by the fibre part g∂ of the environment morphism; the shape
-- and the product structure are left fixed.
------------------------------------------------------------------------------
module FibreReindex {n} {δ δ' : Fin n → Set} (g : ∀ i → δ i → δ' i)
                    (δ∂ : ∀ i → δ i → Set) (δ∂' : ∀ i → δ' i → Set)
                    (g∂ : ∀ i (x : δ i) → δ∂ i x → δ∂' i (g i x)) where
  open Shapes n
  open Decos n
  module Fδ = Fibre δ δ∂
  module Fδ' = Fibre δ' δ∂'
  module Rg = Reindex g

  mutual
    reindex-∂W : ∀ {k} {Q : Poly (suc k)} {ρ} (Q̂ : Deco Q) (dρ : DecoEnv ρ)
                 (w : W Q ρ) (a : Trees.Assign δ w) →
                 Fδ.∂W Q̂ dρ w a → Fδ'.∂W Q̂ dρ w (λ p → Rg.reindexIx (labelW w p) (a p))
    reindex-∂W Q̂ dρ (sup s) a x = reindex-∂Sh Q̂ (extendD dρ (mkDeco Q̂ dρ)) s a x

    reindex-∂Sh : ∀ {j} {R : Poly j} (R̂ : Deco R) {η} (dη : DecoEnv η) (s : Shape R η)
                  (a : Trees.AssignSh δ R η s) →
                  Fδ.∂Sh R̂ dη s a → Fδ'.∂Sh R̂ dη s (λ p → Rg.reindexIx (labelSh R η s p) (a p))
    reindex-∂Sh (const X ∂X) dη s a x = x
    reindex-∂Sh (var j)      dη s a x = reindex-∂El (dη j) s a x
    reindex-∂Sh (R̂₁ ⊕ R̂₂)   dη (inj₁ s) a x = reindex-∂Sh R̂₁ dη s a x
    reindex-∂Sh (R̂₁ ⊕ R̂₂)   dη (inj₂ s) a x = reindex-∂Sh R̂₂ dη s a x
    reindex-∂Sh (R̂₁ ⊗ R̂₂)   dη (s₁ , s₂) a (x , y) =
      reindex-∂Sh R̂₁ dη s₁ (λ p → a (inj₁ p)) x , reindex-∂Sh R̂₂ dη s₂ (λ p → a (inj₂ p)) y
    reindex-∂Sh (μ Q̂')      dη s a x = reindex-∂W Q̂' dη s a x

    reindex-∂El : ∀ {r} (d : DecoRef r) (s : El r) (a : Trees.AssignEl δ r s) →
                  Fδ.∂El d s a → Fδ'.∂El d s (λ p → Rg.reindexIx (labelEl r s p) (a p))
    reindex-∂El {inj₁ i}            _              s a x = g∂ i (a tt) x
    reindex-∂El {inj₂ (mkSort Q ρ)} (mkDeco Q̂ dρ) w a x = reindex-∂W Q̂ dρ w a x

-- The identity assignment, sending each variable to the matching parameter.
ι : ∀ {n} → Fin n → Fin n ⊎ Sort n
ι i = inj₁ i

-- Relates a source assignment over n to its translation over suc n: fbase
-- sends the root binder of P to the fresh parameter, fbind records descent
-- under an inner binder. First-order so that recursion over it is structural;
-- shared by the fold and the algebra map.
data FMor {n} (P : Poly (suc n)) : ∀ {k} → (Fin k → Fin n ⊎ Sort n) →
                                   (Fin k → Fin (suc n) ⊎ Sort (suc n)) → Set₁ where
  fbase : FMor P (extend ι (inj₂ (mkSort P ι))) ι
  fbind : ∀ {k} {ρ ρ'} (Q : Poly (suc k)) → FMor P ρ ρ' →
          FMor P (extend ρ (inj₂ (mkSort Q ρ))) (extend ρ' (inj₂ (mkSort Q ρ')))

------------------------------------------------------------------------------
-- The fold at the index level. The algebra consumes a one-level unfolding
-- over δ[α ↦ Y]: a shape of P over context (suc n) whose α-positions hold
-- folded values. Inner sorts are translated to the extended context by
-- fold-shape, with every recursive call structural.
------------------------------------------------------------------------------
module Fold {n} (δ : Fin n → Set) (Y : Set) (P : Poly (suc n)) where
  module S = Shapes n
  module S' = Shapes (suc n)

  δ' : Fin (suc n) → Set
  δ' = extend δ Y

  module T = Trees δ
  module T' = Trees δ'

  module E = TreeEq δ (λ i → _≡_)
  module E' = TreeEq δ' (λ i → _≡_)

  module _ (alg : T'.TreeSh P ι → Y) where
    mutual
      fold : (w : S.W P ι) → T.Assign w → Y
      fold (S.sup s) a = alg (fold-shape P fbase s a)

      fold-reindex : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S.W Q ρ) →
                     T.Assign w → Σ (S'.W Q ρ') T'.Assign
      fold-reindex {Q = Q} fm (S.sup s) a =
        let (s' , a') = fold-shape Q (fbind Q fm) s a in S'.sup s' , a'

      fold-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S.Shape R ηA) →
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

      fold-apply : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S.El (ρ v)) →
                   T.AssignEl (ρ v) s → Σ (S'.El (ρ' v)) (T'.AssignEl (ρ' v))
      fold-apply fbase        zero    t a = tt , λ _ → fold t a
      fold-apply fbase        (suc i) s a = tt , a
      fold-apply (fbind Q fm) zero    w a = fold-reindex fm w a
      fold-apply (fbind Q fm) (suc v) s a = fold-apply fm v s a

    module _ (alg-resp : ∀ {s₁ s₂ : S'.Shape P ι} {a₁ a₂} →
                         E'.Sh≈ P ι s₁ s₂ a₁ a₂ → alg (s₁ , a₁) ≡ alg (s₂ , a₂)) where
      mutual
        fold-resp : ∀ {w₁ w₂ : S.W P ι} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ → fold w₁ a₁ ≡ fold w₂ a₂
        fold-resp {S.sup s₁} {S.sup s₂} p = alg-resp (fold-shape-resp P fbase p)

        fold-reindex-resp : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ')
                            {w₁ w₂ : S.W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                            E'.Tree≈ (fold-reindex fm w₁ a₁) (fold-reindex fm w₂ a₂)
        fold-reindex-resp {Q = Q} fm {S.sup s₁} {S.sup s₂} p =
          fold-shape-resp Q (fbind Q fm) p

        fold-shape-resp : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB)
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

        fold-apply-resp : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k)
                          {s₁ s₂ : S.El (ρ v)} {a₁ a₂} → E.El≈ (ρ v) s₁ s₂ a₁ a₂ →
                          E'.El≈ (ρ' v) (proj₁ (fold-apply fm v s₁ a₁)) (proj₁ (fold-apply fm v s₂ a₂))
                            (proj₂ (fold-apply fm v s₁ a₁)) (proj₂ (fold-apply fm v s₂ a₂))
        fold-apply-resp fbase        zero    {t₁} {t₂} p = fold-resp {w₁ = t₁} {w₂ = t₂} p
        fold-apply-resp fbase        (suc i) p = p
        fold-apply-resp (fbind Q fm) zero    {w₁} {w₂} p = fold-reindex-resp fm {w₁ = w₁} {w₂ = w₂} p
        fold-apply-resp (fbind Q fm) (suc v) p = fold-apply-resp fm v p

------------------------------------------------------------------------------
-- The algebra map at the index level: assemble a tree of the root sort from a
-- one-level unfolding over δ[α ↦ Carrier], whose α-positions hold whole
-- trees; in-el splices them in without traversing them. out decomposes at the
-- root; the two are mutually inverse up to tree equality, the trees at
-- α-positions compared by Tree≈.
------------------------------------------------------------------------------
module InMap {n} (δ : Fin n → Set) (P : Poly (suc n)) where
  module S = Shapes n
  module S' = Shapes (suc n)

  module T = Trees δ
  module E = TreeEq δ (λ i → _≡_)
  module EE = E.Equiv (λ i x → refl) (λ i p → sym p) (λ i p q → trans p q)

  Carrier : Set
  Carrier = T.Tree P ι

  δᵢ : Fin (suc n) → Set
  δᵢ = extend δ Carrier

  module Tᵢ = Trees δᵢ

  mutual
    in-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S'.W Q ρ') →
              Tᵢ.Assign w → T.Tree Q ρ
    in-tree {Q = Q} fm (S'.sup s) a =
      let (s' , a') = in-shape Q (fbind Q fm) s a in S.sup s' , a'

    in-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S'.Shape R ηB) →
               Tᵢ.AssignSh R ηB s → T.TreeSh R ηA
    in-shape (const X) fm s a = tt , a
    in-shape (var v)   fm s a = in-el fm v s a
    in-shape (R₁ ⊕ R₂) fm (inj₁ s) a = let (s' , a') = in-shape R₁ fm s a in inj₁ s' , a'
    in-shape (R₁ ⊕ R₂) fm (inj₂ s) a = let (s' , a') = in-shape R₂ fm s a in inj₂ s' , a'
    in-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
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

  inMap : Tᵢ.TreeSh P ι → Carrier
  inMap (s , a) = let (s' , a') = in-shape P fbase s a in S.sup s' , a'

  mutual
    out-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S.W Q ρ) →
               T.Assign w → Tᵢ.Tree Q ρ'
    out-tree {Q = Q} fm (S.sup s) a =
      let (s' , a') = out-shape Q (fbind Q fm) s a in S'.sup s' , a'

    out-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S.Shape R ηA) →
                T.AssignSh R ηA s → Tᵢ.TreeSh R ηB
    out-shape (const X) fm s a = tt , a
    out-shape (var v)   fm s a = out-el fm v s a
    out-shape (R₁ ⊕ R₂) fm (inj₁ s) a = let (s' , a') = out-shape R₁ fm s a in inj₁ s' , a'
    out-shape (R₁ ⊕ R₂) fm (inj₂ s) a = let (s' , a') = out-shape R₂ fm s a in inj₂ s' , a'
    out-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
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

  out : Carrier → Tᵢ.TreeSh P ι
  out (S.sup s , a) = out-shape P fbase s a

  -- Equality at the extended environment: the α-entry compared by Tree≈,
  -- parameters by ≡.
  Rᵢ : ∀ v → δᵢ v → δᵢ v → Set
  Rᵢ zero    = E.Tree≈ {Q = P} {ρ = ι}
  Rᵢ (suc i) = _≡_

  module Eᵢ = TreeEq δᵢ Rᵢ

  mutual
    io-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S.W Q ρ) (a : T.Assign w) →
              E.Tree≈ (in-tree fm (proj₁ (out-tree fm w a)) (proj₂ (out-tree fm w a))) (w , a)
    io-tree {Q = Q} fm (S.sup s) a = io-shape Q (fbind Q fm) s a

    io-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S.Shape R ηA)
               (a : T.AssignSh R ηA s) →
               E.Sh≈ R ηA (proj₁ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) s
                 (proj₂ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) a
    io-shape (const X) fm s a = refl
    io-shape (var v)   fm s a = io-el fm v s a
    io-shape (R₁ ⊕ R₂) fm (inj₁ s) a = io-shape R₁ fm s a
    io-shape (R₁ ⊕ R₂) fm (inj₂ s) a = io-shape R₂ fm s a
    io-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
      io-shape R₁ fm s₁ (λ p → a (inj₁ p)) , io-shape R₂ fm s₂ (λ p → a (inj₂ p))
    io-shape (μ Q')    fm s a = io-tree fm s a

    io-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S.El (ρ v)) (a : T.AssignEl (ρ v) s) →
            E.El≈ (ρ v) (proj₁ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) s
              (proj₂ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) a
    io-el fbase        zero    w a = EE.W≈-refl w a
    io-el fbase        (suc i) s a = refl
    io-el (fbind Q fm) zero    w a = io-tree fm w a
    io-el (fbind Q fm) (suc v) s a = io-el fm v s a

  inMap-out : (t : Carrier) → E.Tree≈ (inMap (out t)) t
  inMap-out (S.sup s , a) = io-shape P fbase s a

  mutual
    oi-tree : ∀ {k} {Q : Poly (suc k)} {ρ ρ'} (fm : FMor P ρ ρ') (w : S'.W Q ρ') (a : Tᵢ.Assign w) →
              Eᵢ.Tree≈ (out-tree fm (proj₁ (in-tree fm w a)) (proj₂ (in-tree fm w a))) (w , a)
    oi-tree {Q = Q} fm (S'.sup s) a = oi-shape Q (fbind Q fm) s a

    oi-shape : ∀ {j} (R : Poly j) {ηA ηB} (fm : FMor P ηA ηB) (s : S'.Shape R ηB)
               (a : Tᵢ.AssignSh R ηB s) →
               Eᵢ.Sh≈ R ηB (proj₁ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) s
                 (proj₂ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) a
    oi-shape (const X) fm s a = refl
    oi-shape (var v)   fm s a = oi-el fm v s a
    oi-shape (R₁ ⊕ R₂) fm (inj₁ s) a = oi-shape R₁ fm s a
    oi-shape (R₁ ⊕ R₂) fm (inj₂ s) a = oi-shape R₂ fm s a
    oi-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
      oi-shape R₁ fm s₁ (λ p → a (inj₁ p)) , oi-shape R₂ fm s₂ (λ p → a (inj₂ p))
    oi-shape (μ Q')    fm s a = oi-tree fm s a

    oi-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) (a : Tᵢ.AssignEl (ρ' v) s) →
            Eᵢ.El≈ (ρ' v) (proj₁ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) s
              (proj₂ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) a
    oi-el fbase        zero    s a = EE.W≈-refl (proj₁ (a tt)) (proj₂ (a tt))
    oi-el fbase        (suc i) s a = refl
    oi-el (fbind Q fm) zero    w a = oi-tree fm w a
    oi-el (fbind Q fm) (suc v) s a = oi-el fm v s a

  out-inMap : (t : Tᵢ.TreeSh P ι) →
              Eᵢ.Sh≈ P ι (proj₁ (out (inMap t))) (proj₁ t) (proj₂ (out (inMap t))) (proj₂ t)
  out-inMap (s , a) = oi-shape P fbase s a

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
module Initiality {n} (δ : Fin n → Set) (Y : Set) (P : Poly (suc n)) where
  module S' = Shapes (suc n)
  module F = Fold δ Y P
  module I = InMap δ P

  module _ (alg : F.T'.TreeSh P ι → Y) where
    g : ∀ v → I.δᵢ v → F.δ' v
    g zero    t = F.fold alg (proj₁ t) (proj₂ t)
    g (suc i) x = x

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
      β-shape (const X) fm s a = refl
      β-shape (var v)   fm s a = β-el fm v s a
      β-shape (R₁ ⊕ R₂) fm (inj₁ s) a = β-shape R₁ fm s a
      β-shape (R₁ ⊕ R₂) fm (inj₂ s) a = β-shape R₂ fm s a
      β-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
        β-shape R₁ fm s₁ (λ p → a (inj₁ p)) , β-shape R₂ fm s₂ (λ p → a (inj₂ p))
      β-shape (μ Q')    fm s a = β-tree fm s a

      β-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) (a : I.Tᵢ.AssignEl (ρ' v) s) →
             F.E'.El≈ (ρ' v)
               (proj₁ (F.fold-apply alg fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a)))) s
               (proj₂ (F.fold-apply alg fm v (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a))))
               (λ p → Rg.reindexIx (S'.labelEl (ρ' v) s p) (a p))
      β-el fbase        zero    s a = refl
      β-el fbase        (suc i) s a = refl
      β-el (fbind Q fm) zero    w a = β-tree fm w a
      β-el (fbind Q fm) (suc v) s a = β-el fm v s a

    module _ (alg-resp : ∀ {s₁ s₂ : S'.Shape P ι} {a₁ a₂} →
                         F.E'.Sh≈ P ι s₁ s₂ a₁ a₂ → alg (s₁ , a₁) ≡ alg (s₂ , a₂)) where
      β : (t : I.Tᵢ.TreeSh P ι) →
          F.fold alg (proj₁ (I.inMap t)) (proj₂ (I.inMap t)) ≡ alg (Rg.reindexSh {Q = P} {η = ι} t)
      β (s , a) = alg-resp (β-shape P fbase s a)

      module _ (h : I.Carrier → Y) where
        hg : ∀ v → I.δᵢ v → F.δ' v
        hg zero    t = h t
        hg (suc i) x = x

        module Rh = Reindex hg

        module _ (h-resp : ∀ {t₁ t₂ : I.Carrier} → I.E.Tree≈ t₁ t₂ → h t₁ ≡ h t₂)
                 (h-β : (t : I.Tᵢ.TreeSh P ι) → h (I.inMap t) ≡ alg (Rh.reindexSh {Q = P} {η = ι} t)) where
          mutual
            η-tree : (w : F.S.W P ι) (a : F.T.Assign w) → h (w , a) ≡ F.fold alg w a
            η-tree (F.S.sup s) a =
              trans (sym (h-resp (I.inMap-out (F.S.sup s , a))))
                (trans (h-β (I.out (F.S.sup s , a)))
                  (trans (alg-resp (η-out-shape P fbase s a))
                    (trans (sym (β (I.out (F.S.sup s , a))))
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
            η-out-shape (const X) fm s a = refl
            η-out-shape (var v)   fm s a = η-out-el fm v s a
            η-out-shape (R₁ ⊕ R₂) fm (inj₁ s) a = η-out-shape R₁ fm s a
            η-out-shape (R₁ ⊕ R₂) fm (inj₂ s) a = η-out-shape R₂ fm s a
            η-out-shape (R₁ ⊗ R₂) fm (s₁ , s₂) a =
              η-out-shape R₁ fm s₁ (λ p → a (inj₁ p)) , η-out-shape R₂ fm s₂ (λ p → a (inj₂ p))
            η-out-shape (μ Q')    fm s a = η-out-tree fm s a

            η-out-el : ∀ {k} {ρ ρ'} (fm : FMor P ρ ρ') (v : Fin k) (s : F.S.El (ρ v))
                       (a : F.T.AssignEl (ρ v) s) →
                       F.E'.El≈ (ρ' v) (proj₁ (I.out-el fm v s a)) (proj₁ (I.out-el fm v s a))
                         (λ p → Rh.reindexIx (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
                         (λ p → Rg.reindexIx (S'.labelEl (ρ' v) (proj₁ (I.out-el fm v s a)) p) (proj₂ (I.out-el fm v s a) p))
            η-out-el fbase        zero    w a = η-tree w a
            η-out-el fbase        (suc i) s a = refl
            η-out-el (fbind Q fm) zero    w a = η-out-tree fm w a
            η-out-el (fbind Q fm) (suc v) s a = η-out-el fm v s a

          η : (t : I.Carrier) → h t ≡ F.fold alg (proj₁ t) (proj₂ t)
          η (w , a) = η-tree w a
