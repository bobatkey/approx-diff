{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Category-free shape layer of the Fam μ-type construction, with the leaf
-- data moved out of the trees. A shape is a tree over the index-erased
-- polynomials with trivial leaves; its positions are the leaves, each naming
-- an index setoid (a constant's, or an environment entry's via a parameter).
-- A tree is a shape together with an index assignment sending each position
-- to an element of the setoid naming it. The environment therefore enters
-- only through the assignment, so reindexing leaves the shape fixed.
--
-- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005.
-- Abbott, Altenkirch, Ghani. Representing nested inductive types using W-types. ICALP 2004.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_) renaming (_×_ to _×T_)
open import Data.Unit using (⊤; tt)
open import prop using (_∧_; _,_; ⊥)
open import prop-setoid using (Setoid; IsEquivalence)
import setoid-cat
import polynomial-functor

module fam-mu-shapes.shape (os es : Level) where

open Setoid using (Carrier; isEquivalence) renaming (_≈_ to _≈s_)
open IsEquivalence

-- Index-erased polynomials: constants are index setoids.
𝒮 = setoid-cat.SetoidCat os (os ⊔ es)
Poly = polynomial-functor.Poly 𝒮
open polynomial-functor.Poly public
open polynomial-functor using (extend) public

-- A sort is an index-erased μ-body together with an assignment of its free
-- variables to parameters or other sorts.
data Sort (n : ℕ) : Set (lsuc os ⊔ lsuc es) where
  mkSort : ∀ {k} → Poly (suc k) → (Fin k → Fin n ⊎ Sort n) → Sort n

module Shapes (n : ℕ) where

  ------------------------------------------------------------------------------
  -- Shapes. A shape of sort (mkSort Q ρ) is W Q ρ; Shape computes the
  -- one-level unfolding, El resolves a variable to a leaf or a sub-shape.
  ------------------------------------------------------------------------------
  mutual
    data W {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) : Set where
      sup : Shape Q (extend ρ (inj₂ (mkSort Q ρ))) → W Q ρ

    Shape : ∀ {k} → Poly k → (Fin k → Fin n ⊎ Sort n) → Set
    Shape (const S) η = ⊤                           -- one leaf, no data
    Shape (var j)   η = El (η j)
    Shape (P + Q)   η = Shape P η ⊎ Shape Q η
    Shape (P × Q)   η = Shape P η ×T Shape Q η
    Shape (μ Q')    η = W Q' η

    El : Fin n ⊎ Sort n → Set
    El (inj₁ p)            = ⊤                      -- parameter leaf, no data
    El (inj₂ (mkSort Q ρ)) = W Q ρ

  mutual
    PosW : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → Set
    PosW {Q = Q} {ρ = ρ} (sup s) = PosSh Q (extend ρ (inj₂ (mkSort Q ρ))) s

    PosSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Shape Q η → Set
    PosSh (const S) η s        = ⊤
    PosSh (var j)   η s        = PosEl (η j) s
    PosSh (P + Q)   η (inj₁ s) = PosSh P η s
    PosSh (P + Q)   η (inj₂ s) = PosSh Q η s
    PosSh (P × Q)   η (s₁ , s₂) = PosSh P η s₁ ⊎ PosSh Q η s₂
    PosSh (μ Q')    η s        = PosW s

    PosEl : (r : Fin n ⊎ Sort n) → El r → Set
    PosEl (inj₁ p)            s = ⊤
    PosEl (inj₂ (mkSort Q ρ)) s = PosW s

  ------------------------------------------------------------------------------
  -- The setoid naming a position: a const-leaf names its index setoid, a
  -- parameter-leaf names its parameter.
  ------------------------------------------------------------------------------
  mutual
    labelW : ∀ {k} {Q : Poly (suc k)} {ρ} (w : W Q ρ) → PosW w → Setoid os (os ⊔ es) ⊎ Fin n
    labelW {Q = Q} {ρ = ρ} (sup s) p = labelSh Q (extend ρ (inj₂ (mkSort Q ρ))) s p

    labelSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s : Shape Q η) →
              PosSh Q η s → Setoid os (os ⊔ es) ⊎ Fin n
    labelSh (const S) η s        p        = inj₁ S
    labelSh (var j)   η s        p        = labelEl (η j) s p
    labelSh (P + Q)   η (inj₁ s) p        = labelSh P η s p
    labelSh (P + Q)   η (inj₂ s) p        = labelSh Q η s p
    labelSh (P × Q)   η (s₁ , s₂) (inj₁ p) = labelSh P η s₁ p
    labelSh (P × Q)   η (s₁ , s₂) (inj₂ p) = labelSh Q η s₂ p
    labelSh (μ Q')    η s        p        = labelW s p

    labelEl : (r : Fin n ⊎ Sort n) (s : El r) → PosEl r s → Setoid os (os ⊔ es) ⊎ Fin n
    labelEl (inj₁ p)            s q = inj₂ p
    labelEl (inj₂ (mkSort Q ρ)) s q = labelW s q

------------------------------------------------------------------------------
-- Trees over the index setoids ι of a kinding environment.
------------------------------------------------------------------------------
module Trees {n} (ι : Fin n → Setoid os (os ⊔ es)) where
  open Shapes n

  Ix : Setoid os (os ⊔ es) ⊎ Fin n → Set os
  Ix (inj₁ S) = S .Carrier
  Ix (inj₂ i) = ι i .Carrier

  Assign : ∀ {k} {Q : Poly (suc k)} {ρ} → W Q ρ → Set os
  Assign w = (p : PosW w) → Ix (labelW w p)

  AssignSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Shape Q η → Set os
  AssignSh Q η s = (p : PosSh Q η s) → Ix (labelSh Q η s p)

  AssignEl : (r : Fin n ⊎ Sort n) → El r → Set os
  AssignEl r s = (p : PosEl r s) → Ix (labelEl r s p)

  Tree : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Set os
  Tree Q ρ = Σ (W Q ρ) Assign

  TreeSh : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) → Set os
  TreeSh Q η = Σ (Shape Q η) (AssignSh Q η)

  TreeEl : (r : Fin n ⊎ Sort n) → Set os
  TreeEl r = Σ (El r) (AssignEl r)

------------------------------------------------------------------------------
-- Tree equality: shapes agree constructor by constructor and the assignments
-- agree pointwise, defined by simultaneous recursion on the two shapes so no
-- transport along a shape equality is needed. Values at const leaves are
-- compared by the named setoid; values at parameter leaves by a supplied
-- relation R, instantiated with the environment's setoid equalities in the
-- carrier and with tree equality itself at the algebra-map laws.
------------------------------------------------------------------------------
module TreeEq {n} (ι : Fin n → Setoid os (os ⊔ es))
              (R : ∀ i → ι i .Carrier → ι i .Carrier → Prop (os ⊔ es)) where
  open Shapes n
  open Trees ι

  mutual
    W≈ : ∀ {k} {Q : Poly (suc k)} {ρ} (w₁ w₂ : W Q ρ) → Assign w₁ → Assign w₂ → Prop (os ⊔ es)
    W≈ {Q = Q} {ρ = ρ} (sup s₁) (sup s₂) a₁ a₂ =
      Sh≈ Q (extend ρ (inj₂ (mkSort Q ρ))) s₁ s₂ a₁ a₂

    Sh≈ : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s₁ s₂ : Shape Q η) →
          AssignSh Q η s₁ → AssignSh Q η s₂ → Prop (os ⊔ es)
    Sh≈ (const S) η s₁ s₂ a₁ a₂ = _≈s_ S (a₁ tt) (a₂ tt)
    Sh≈ (var j)   η s₁ s₂ a₁ a₂ = El≈ (η j) s₁ s₂ a₁ a₂
    Sh≈ (P + Q)   η (inj₁ s₁) (inj₁ s₂) a₁ a₂ = Sh≈ P η s₁ s₂ a₁ a₂
    Sh≈ (P + Q)   η (inj₁ _)  (inj₂ _)  a₁ a₂ = ⊥
    Sh≈ (P + Q)   η (inj₂ _)  (inj₁ _)  a₁ a₂ = ⊥
    Sh≈ (P + Q)   η (inj₂ s₁) (inj₂ s₂) a₁ a₂ = Sh≈ Q η s₁ s₂ a₁ a₂
    Sh≈ (P × Q)   η (s₁ , t₁) (s₂ , t₂) a₁ a₂ =
      Sh≈ P η s₁ s₂ (λ p → a₁ (inj₁ p)) (λ p → a₂ (inj₁ p)) ∧
      Sh≈ Q η t₁ t₂ (λ p → a₁ (inj₂ p)) (λ p → a₂ (inj₂ p))
    Sh≈ (μ Q')    η w₁ w₂ a₁ a₂ = W≈ w₁ w₂ a₁ a₂

    El≈ : (r : Fin n ⊎ Sort n) (s₁ s₂ : El r) → AssignEl r s₁ → AssignEl r s₂ → Prop (os ⊔ es)
    El≈ (inj₁ i)            s₁ s₂ a₁ a₂ = R i (a₁ tt) (a₂ tt)
    El≈ (inj₂ (mkSort Q ρ)) w₁ w₂ a₁ a₂ = W≈ w₁ w₂ a₁ a₂

  Tree≈ : ∀ {k} {Q : Poly (suc k)} {ρ} → Tree Q ρ → Tree Q ρ → Prop (os ⊔ es)
  Tree≈ (w₁ , a₁) (w₂ , a₂) = W≈ w₁ w₂ a₁ a₂

  TreeEl≈ : (r : Fin n ⊎ Sort n) → TreeEl r → TreeEl r → Prop (os ⊔ es)
  TreeEl≈ r (s₁ , a₁) (s₂ , a₂) = El≈ r s₁ s₂ a₁ a₂

  module Equiv (R-refl : ∀ i (x : ι i .Carrier) → R i x x)
               (R-sym : ∀ i {x y : ι i .Carrier} → R i x y → R i y x)
               (R-trans : ∀ i {x y z : ι i .Carrier} → R i x y → R i y z → R i x z) where
    mutual
      W≈-refl : ∀ {k} {Q : Poly (suc k)} {ρ} (w : W Q ρ) (a : Assign w) → W≈ w w a a
      W≈-refl {Q = Q} {ρ = ρ} (sup s) a = Sh≈-refl Q (extend ρ (inj₂ (mkSort Q ρ))) s a

      Sh≈-refl : ∀ {k} (Q : Poly k) (η : Fin k → Fin n ⊎ Sort n) (s : Shape Q η)
                 (a : AssignSh Q η s) → Sh≈ Q η s s a a
      Sh≈-refl (const S) η s a = S .isEquivalence .refl
      Sh≈-refl (var j)   η s a = El≈-refl (η j) s a
      Sh≈-refl (P + Q)   η (inj₁ s) a = Sh≈-refl P η s a
      Sh≈-refl (P + Q)   η (inj₂ s) a = Sh≈-refl Q η s a
      Sh≈-refl (P × Q)   η (s₁ , s₂) a =
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
      Sh≈-sym (const S) η p = S .isEquivalence .sym p
      Sh≈-sym (var j)   η p = El≈-sym (η j) p
      Sh≈-sym (P + Q)   η {inj₁ _} {inj₁ _} p = Sh≈-sym P η p
      Sh≈-sym (P + Q)   η {inj₂ _} {inj₂ _} p = Sh≈-sym Q η p
      Sh≈-sym (P × Q)   η {_ , _} {_ , _} (p , q) = Sh≈-sym P η p , Sh≈-sym Q η q
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
      Sh≈-trans (const S) η p q = S .isEquivalence .trans p q
      Sh≈-trans (var j)   η p q = El≈-trans (η j) p q
      Sh≈-trans (P + Q)   η {inj₁ _} {inj₁ _} {inj₁ _} p q = Sh≈-trans P η p q
      Sh≈-trans (P + Q)   η {inj₂ _} {inj₂ _} {inj₂ _} p q = Sh≈-trans Q η p q
      Sh≈-trans (P × Q)   η {_ , _} {_ , _} {_ , _} (p₁ , p₂) (q₁ , q₂) =
        Sh≈-trans P η p₁ q₁ , Sh≈-trans Q η p₂ q₂
      Sh≈-trans (μ Q')    η {w₁} {w₂} {w₃} p q = W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} p q

      El≈-trans : ∀ (r : Fin n ⊎ Sort n) {s₁ s₂ s₃ : El r} {a₁ a₂ a₃} →
                  El≈ r s₁ s₂ a₁ a₂ → El≈ r s₂ s₃ a₂ a₃ → El≈ r s₁ s₃ a₁ a₃
      El≈-trans (inj₁ i)            p q = R-trans i p q
      El≈-trans (inj₂ (mkSort Q ρ)) {w₁} {w₂} {w₃} p q = W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃} p q

    -- The setoid of trees at a sort.
    TreeSetoid : ∀ {k} (Q : Poly (suc k)) (ρ : Fin k → Fin n ⊎ Sort n) → Setoid os (os ⊔ es)
    TreeSetoid Q ρ .Setoid.Carrier = Tree Q ρ
    TreeSetoid Q ρ .Setoid._≈_ = Tree≈
    TreeSetoid Q ρ .Setoid.isEquivalence .refl {w , a} = W≈-refl w a
    TreeSetoid Q ρ .Setoid.isEquivalence .sym {w₁ , a₁} {w₂ , a₂} = W≈-sym {w₁ = w₁} {w₂ = w₂}
    TreeSetoid Q ρ .Setoid.isEquivalence .trans {w₁ , a₁} {w₂ , a₂} {w₃ , a₃} =
      W≈-trans {w₁ = w₁} {w₂ = w₂} {w₃ = w₃}
