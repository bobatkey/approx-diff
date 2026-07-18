{-# OPTIONS --safe #-}

------------------------------------------------------------------------------
-- Prototype for the shape-based mu-type carrier (notes section on positions
-- and reindexing): shapes, positions, index assignments, reindexing and the
-- fold, to test whether the structure is workable in Agda before adding the
-- setoid and fibre layers.
--
-- Two naive encodings fail. An inductive family (shapes indexed by polynomial
-- and assignment, positions indexed over shapes) needs equation constructors
-- rho i = inj_ ..., and dependent matching on positions then hits green slime.
-- Computing the set of shapes by recursion fails termination, because sorts
-- are mutually recursive (a shape of one sort contains shapes of others), so
-- the recursion has no structural decrease.
--
-- The encoding below is the one already used for trees in
-- fam-mu-types/sort.agda: a datatype W with a single constructor wrapping a
-- computed one-level unfolding. W is inductive, so the recursion bottoms out;
-- the unfolding is matched on the polynomial, so there is no green slime. The
-- shape design reuses that carrier structure, with the leaf data moved out
-- into the index assignment.
--
-- n is the number of parameters (the outer context Delta); shapes and
-- positions are parameter-indexed but environment-free. The kinding
-- environment delta enters only through the index assignment of a tree.
------------------------------------------------------------------------------

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

  ------------------------------------------------------------------------------
  -- Positions of a shape.
  ------------------------------------------------------------------------------
  mutual
    PosW : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → Set
    PosW {Q = Q} {ρ = ρ} (sup s) = PosSh Q (extend ρ (inj₂ (mkSort Q ρ))) s

    PosSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Shape Q η → Set
    PosSh (const X) η s        = ⊤                  -- the single leaf position
    PosSh (var j)   η s        = PosEl (η j) s
    PosSh (P ⊕ Q)   η (inj₁ s) = PosSh P η s
    PosSh (P ⊕ Q)   η (inj₂ s) = PosSh Q η s
    PosSh (P ⊗ Q)   η (s₁ , s₂) = PosSh P η s₁ ⊎ PosSh Q η s₂
    PosSh (μ Q')    η s        = PosW s

    PosEl : (r : Fin n ⊎ Sort n) → El r → Set
    PosEl (inj₁ p)            s = ⊤                 -- the parameter-leaf position
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
