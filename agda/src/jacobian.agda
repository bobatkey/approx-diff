{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import two using (Two; I; O; _⊓_; _⊔_; ⊔-upper₂; ≤-isPreorder; ⊓-isMeet; I-isTop)
open import basics using (IsPreorder; IsTop)
open IsPreorder ≤-isPreorder using () renaming (_≃_ to _≃t_; ≃-refl to ≃t-refl; ≃-trans to ≃t-trans)
import join-semilattice-category
import meet-semilattice-category
import meet-semilattice
import galois

-- Objects: Two^n as a bounded lattice, the n-fold product of TWO.
-- FIXME: using galois.Obj as a stand-in for BoundedLattice, which we don't have yet.

Two^ : ℕ → galois.Obj
Two^ zero    = galois.𝟙
Two^ (suc n) = galois._⊕_ galois.TWO (Two^ n)

-- Join-semilattice and meet-semilattice views.
Two^-join : ℕ → join-semilattice-category.Obj
Two^-join n .join-semilattice-category.Obj.carrier = Two^ n .galois.Obj.carrier
Two^-join n .join-semilattice-category.Obj.joins = Two^ n .galois.Obj.joins

Two^-meet : ℕ → meet-semilattice-category.Obj
Two^-meet n .meet-semilattice-category.Obj.carrier = Two^ n .galois.Obj.carrier
Two^-meet n .meet-semilattice-category.Obj.meets = Two^ n .galois.Obj.meets

open galois.Obj

-- Basis vectors, projection and tabulation for Two^n.

e : ∀ {n} → Fin n → Two^ n .Carrier
e {suc n} zero = I , Two^ n .⊥
e {suc n} (suc i) = O , e i

proj : ∀ {n} → Fin n → Two^ n .Carrier → Two
proj zero (b , _)  = b
proj (suc i) (_ , v) = proj i v

open import Data.Unit using (tt)
open import prop using (tt; _,_; _∧_; proj₁; proj₂)

tabulate : ∀ {n} → (Fin n → Two) → Two^ n .Carrier
tabulate {zero} _ = tt
tabulate {suc n} f = f zero , tabulate {n} (λ i → f (suc i))

-- n-ary join in a join semilattice.
module _ where
  open join-semilattice-category.Obj

  ⋁ : (J : join-semilattice-category.Obj) → ∀ n → (Fin n → J .Carrier) → J .Carrier
  ⋁ J zero _ = J .⊥
  ⋁ J (suc n) g = J ._∨_ (g zero) (⋁ J n (λ i → g (suc i)))

-- Dot product: u ⋅ v = (u₀ ⊓ v₀) ⊔ ... ⊔ (uₙ ⊓ vₙ).
module _ where
  _⋅_ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier → Two
  _⋅_ {zero}  _ _ = O
  _⋅_ {suc n} (a , u) (b , v) = (a ⊓ b) ⊔ _⋅_ {n} u v

  -- ⋅ is join-preserving and monotone in its second argument.
  ⋅-⊥ : ∀ {n} (u : Two^ n .Carrier) → two._≤_ (_⋅_ {n} u (Two^ n .⊥)) O
  ⋅-⊥ {zero}  _ = tt
  ⋅-⊥ {suc n} (O , v) = ⋅-⊥ {n} v
  ⋅-⊥ {suc n} (I , v) = ⋅-⊥ {n} v

  ⋅-∨ : ∀ {n} (u v w : Two^ n .Carrier) →
        two._≤_ (_⋅_ {n} u (Two^ n ._∨_ v w)) ((_⋅_ {n} u v) ⊔ (_⋅_ {n} u w))
  ⋅-∨ {zero} _ _ _ = tt
  ⋅-∨ {suc n} (O , u) (_ , v) (_ , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (O , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (I , w) = ⊔-upper₂
  ⋅-∨ {suc n} (I , u) (I , v) (_ , w) = tt

  ⋅-mono : ∀ {n} (u : Two^ n .Carrier) {v w : Two^ n .Carrier} →
           Two^ n ._≤_ v w → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} u w)
  ⋅-mono {zero}  _ _ = tt
  ⋅-mono {suc n} (O , u) {_ , v} {_ , w} (_ , v≤w) = ⋅-mono {n} u v≤w
  ⋅-mono {suc n} (I , u) {O , v} {_ , w} (_   , v≤w) = two.≤-trans (⋅-mono {n} u v≤w) ⊔-upper₂
  ⋅-mono {suc n} (I , u) {I , v} {I , w} (_   , v≤w) = tt

-- Pointwise negation on Two^n.
¬ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier
¬ {zero}  _       = tt
¬ {suc n} (a , u) = two.¬ a , ¬ {n} u

¬-anti : ∀ {a b : Two} → two._≤_ a b → two._≤_ (two.¬ b) (two.¬ a)
¬-anti {O} {O} _ = tt
¬-anti {O} {I} _ = tt
¬-anti {I} {I} _ = tt

¬-anti^ : ∀ {n} {v w : Two^ n .Carrier} → Two^ n ._≤_ v w → Two^ n ._≤_ (¬ {n} w) (¬ {n} v)
¬-anti^ {zero}  _           = tt
¬-anti^ {suc n} (a≤b , v≤w) = ¬-anti a≤b , ¬-anti^ {n} v≤w

-- Co-dot product (De Morgan dual of ⋅).
_⊡_ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier → Two
_⊡_ {n} u v = two.¬ (_⋅_ {n} (¬ {n} u) (¬ {n} v))

-- ⊡ is monotone in its second argument (via De Morgan from ⋅-mono).
⊡-mono : ∀ {n} (u : Two^ n .Carrier) {v w : Two^ n .Carrier} →
         Two^ n ._≤_ v w → two._≤_ (_⊡_ {n} u v) (_⊡_ {n} u w)
⊡-mono {n} u v≤w = ¬-anti (⋅-mono {n} (¬ {n} u) (¬-anti^ {n} v≤w))

-- Scales the vector u by the Two value a.
_·⊓_ : ∀ {n} → Two → Two^ n .Carrier → Two^ n .Carrier
_·⊓_ {zero}  _ _       = tt
_·⊓_ {suc n} a (b , u) = (a ⊓ b) , _·⊓_ {n} a u

-- O scales to ⊥; I is the identity.
·⊓-O : ∀ {n} (u : Two^ n .Carrier) → _≃_ (Two^ n) (_·⊓_ {n} O u) (Two^ n .⊥)
·⊓-O {zero}  _       = tt , tt
·⊓-O {suc n} (_ , u) = (tt , ·⊓-O {n} u .proj₁) , (tt , ·⊓-O {n} u .proj₂)

·⊓-I : ∀ {n} (u : Two^ n .Carrier) → _≃_ (Two^ n) (_·⊓_ {n} I u) u
·⊓-I {zero}  _       = tt , tt
·⊓-I {suc n} (_ , u) = (two.≤-refl , ·⊓-I {n} u .proj₁) , (two.≤-refl , ·⊓-I {n} u .proj₂)

-- Pointwise lifting of meet/implication adjunction.
⊡-adj₁ : ∀ n (a : Two) (u v : Two^ n .Carrier) →
         Two^ n ._≤_ (_·⊓_ {n} a u) v → two._≤_ a (_⊡_ {n} (¬ {n} u) v)
⊡-adj₁ zero a u v p = I-isTop .IsTop.≤-top
⊡-adj₁ (suc n) O u v p = tt
⊡-adj₁ (suc n) I (O , u) (_ , v) (h , t) = ⊡-adj₁ n I u v t
⊡-adj₁ (suc n) I (I , _) (O , _) (() , _)
⊡-adj₁ (suc n) I (I , u) (I , v) (_ , t) = ⊡-adj₁ n I u v t

⊡-adj₂ : ∀ n (a : Two) (u v : Two^ n .Carrier) →
         two._≤_ a (_⊡_ {n} (¬ {n} u) v) → Two^ n ._≤_ (_·⊓_ {n} a u) v
⊡-adj₂ zero a u v p = tt
⊡-adj₂ (suc n) O (u₀ , u) (v₀ , v) h = tt , ⊡-adj₂ n O u v tt
⊡-adj₂ (suc n) I (O , u) (v₀ , v) h = tt , ⊡-adj₂ n I u v h
⊡-adj₂ (suc n) I (I , u) (O , v) ()
⊡-adj₂ (suc n) I (I , u) (I , v) h = tt , ⊡-adj₂ n I u v h

¬-⊤ : ∀ {n} → Two^ n ._≤_ (¬ {n} (Two^ n .⊤)) (Two^ n .⊥)
¬-⊤ {zero}  = tt
¬-⊤ {suc n} = tt , ¬-⊤ {n}

-- ⊡ preserves ∧ in its second argument.
⊡-∧ : ∀ {n} (u v w : Two^ n .Carrier) →
      two._≤_ ((_⊡_ {n} u v) ⊓ (_⊡_ {n} u w)) (_⊡_ {n} u (galois.Obj._∧_ (Two^ n) v w))
⊡-∧ {zero}  _ _ _ = tt
⊡-∧ {suc n} (O , u) (O , v) (_ , w) = tt
⊡-∧ {suc n} (O , u) (I , v) (O , w) = two.⊓-lower₂
⊡-∧ {suc n} (O , u) (I , v) (I , w) = ⊡-∧ {n} u v w
⊡-∧ {suc n} (I , u) (_ , v) (_ , w) = ⊡-∧ {n} u v w

-- ⊡ with ⊤ is I (via De Morgan from ⋅-⊥).
⊡-⊤ : ∀ {n} (u : Two^ n .Carrier) → two._≤_ I (_⊡_ {n} u (Two^ n .⊤))
⊡-⊤ {n} u = ¬-anti (two.≤-trans (⋅-mono {n} (¬ {n} u) (¬-⊤ {n})) (⋅-⊥ {n} (¬ {n} u)))

-- Two^n as a conjugate.Obj (Heyting algebra).
import conjugate

Two^-conj : ℕ → conjugate.Obj
Two^-conj n .conjugate.Obj.carrier = Two^ n .carrier
Two^-conj n .conjugate.Obj.meets = Two^ n .meets
Two^-conj n .conjugate.Obj.joins = Two^ n .joins
Two^-conj zero .conjugate.Obj.#-reflect _ = tt
Two^-conj (suc n) .conjugate.Obj.#-reflect {x₁ , x₂} {y₁ , y₂} h =
  conjugate.Obj.#-reflect conjugate.TWO (λ z₁ y#z →
    proj₁ (h (z₁ , Two^ n .⊥) (y#z , conjugate.Obj.π₂ (Two^-conj n)))) ,
  conjugate.Obj.#-reflect (Two^-conj n) (λ z₂ y#z →
    proj₂ (h (O , z₂) (conjugate.Obj.π₂ conjugate.TWO , y#z)))
Two^-conj zero .conjugate.Obj.∧-∨-distrib _ _ _ = tt
Two^-conj (suc n) .conjugate.Obj.∧-∨-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
  conjugate.Obj.∧-∨-distrib conjugate.TWO x₁ y₁ z₁ ,
  conjugate.Obj.∧-∨-distrib (Two^-conj n) x₂ y₂ z₂
Two^-conj zero .conjugate.Obj.∨-∧-distrib _ _ _ = tt
Two^-conj (suc n) .conjugate.Obj.∨-∧-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
  conjugate.Obj.∨-∧-distrib conjugate.TWO x₁ y₁ z₁ ,
  conjugate.Obj.∨-∧-distrib (Two^-conj n) x₂ y₂ z₂

-- Morphisms: join-semilattice morphisms Two^m → Two^n.
-- Every such map is determined by its values on basis vectors, i.e. by an n × m Boolean matrix.
-- Transpose (conjugate backward): f^T(v)_i = f(e_i) ⋅ v (join-preserving, using dot).
-- Adjoint (galois backward):      f*(v)_i = ¬f(e_i) ⊡ v (meet-preserving, using co-dot on negated matrix).
module _ where
  open join-semilattice-category using () renaming (_⇒_ to _⇒J_)
  open meet-semilattice-category using () renaming (_⇒_ to _⇒M_)
  open join-semilattice-category._⇒_ using (fun) renaming (*→* to *→*J)
  open meet-semilattice-category._⇒_ renaming (*→* to *→*M; fun to funM)
  import join-semilattice
  open join-semilattice._=>_ renaming (func to funcJ)
  open meet-semilattice._=>_ renaming (func to funcM)
  open import preorder using (_=>_)
  open preorder._=>_ using () renaming (fun to funP)

  private
    -- tabulate is a join-semilattice isomorphism from (Fin m → Two) to Two^m
    -- (with proj as inverse). We only need the forward direction here.
    tabulate-mono : ∀ {m} (g h : Fin m → Two) →
                    (∀ i → two._≤_ (g i) (h i)) → Two^ m ._≤_ (tabulate {m} g) (tabulate {m} h)
    tabulate-mono {zero}  g h p = tt
    tabulate-mono {suc m} g h p = p zero , tabulate-mono {m} _ _ (λ i → p (suc i))

    tabulate-⊥ : ∀ {m} → Two^ m ._≤_ (tabulate {m} (λ _ → O)) (Two^ m .⊥)
    tabulate-⊥ {zero}  = tt
    tabulate-⊥ {suc m} = tt , tabulate-⊥ {m}

    tabulate-⊤ : ∀ {m} → Two^ m ._≤_ (Two^ m .⊤) (tabulate {m} (λ _ → I))
    tabulate-⊤ {zero}  = tt
    tabulate-⊤ {suc m} = tt , tabulate-⊤ {m}

    tabulate-∨ : ∀ {m} (g h : Fin m → Two) →
                 Two^ m ._≤_ (tabulate {m} (λ i → g i ⊔ h i)) (Two^ m ._∨_ (tabulate {m} g) (tabulate {m} h))
    tabulate-∨ {zero}  g h = tt
    tabulate-∨ {suc m} g h = two.≤-refl , tabulate-∨ {m} (λ i → g (suc i)) (λ i → h (suc i))

    tabulate-∧ : ∀ {m} (g h : Fin m → Two) →
                 Two^ m ._≤_ (galois.Obj._∧_ (Two^ m) (tabulate {m} g) (tabulate {m} h)) (tabulate {m} (λ i → g i ⊓ h i))
    tabulate-∧ {zero}  g h = tt
    tabulate-∧ {suc m} g h = two.≤-refl , tabulate-∧ {m} (λ i → g (suc i)) (λ i → h (suc i))

    proj-tabulate : ∀ {n} (g : Fin n → Two) (i : Fin n) → proj i (tabulate {n} g) ≃t g i
    proj-tabulate {suc n} g zero = ≃t-refl
    proj-tabulate {suc n} g (suc i) = proj-tabulate {n} (λ i → g (suc i)) i

  transpose : ∀ {m n} → Two^-join m ⇒J Two^-join n → Two^-join n ⇒J Two^-join m
  transpose {m} {n} f .*→*J .funcJ .funP v = tabulate {m} (λ i → _⋅_ {n} (fun f (e i)) v)
  transpose {m} {n} f .*→*J .funcJ .preorder._=>_.mono v≤w =
    tabulate-mono {m} _ _ (λ i → ⋅-mono {n} (fun f (e i)) v≤w)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.∨-preserving {v} {w} =
    Two^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-∨ {n} (fun f (e i)) v w))
                     (tabulate-∨ {m} _ _)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.⊥-preserving =
    Two^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-⊥ {n} (fun f (e i))))
                     (tabulate-⊥ {m})

  adjoint : ∀ {m n} → Two^-join m ⇒J Two^-join n → Two^-meet n ⇒M Two^-meet m
  adjoint {m} {n} f .*→*M .funcM .funP v = tabulate {m} (λ i → _⊡_ {n} (¬ {n} (fun f (e i))) v)
  adjoint {m} {n} f .*→*M .funcM .preorder._=>_.mono v≤w =
    tabulate-mono {m} _ _ (λ i → ⊡-mono {n} (¬ {n} (fun f (e i))) v≤w)
  adjoint {m} {n} f .*→*M .meet-semilattice._=>_.∧-preserving {v} {w} =
    Two^ m .≤-trans (tabulate-∧ {m} _ _)
                     (tabulate-mono {m} _ _ (λ i → ⊡-∧ {n} (¬ {n} (fun f (e i))) v w))
  adjoint {m} {n} f .*→*M .meet-semilattice._=>_.⊤-preserving =
    Two^ m .≤-trans (tabulate-⊤ {m})
                     (tabulate-mono {m} _ _ (λ i → ⊡-⊤ {n} (¬ {n} (fun f (e i)))))

  -- Restrict f to its "tail": f-tail(z) = f(O, z).
  f-tail : ∀ {m n} → Two^-join (suc m) ⇒J Two^-join n → Two^-join m ⇒J Two^-join n
  f-tail {m} {n} f .*→*J .funcJ .funP v = fun f (O , v)
  f-tail {m} {n} f .*→*J .funcJ .preorder._=>_.mono v≤v' =
    f .*→*J .funcJ .preorder._=>_.mono (tt , v≤v')
  f-tail {m} {n} f .*→*J .join-semilattice._=>_.∨-preserving =
    f .*→*J .join-semilattice._=>_.∨-preserving
  f-tail {m} {n} f .*→*J .join-semilattice._=>_.⊥-preserving = f .*→*J .join-semilattice._=>_.⊥-preserving

  -- Join-preserving maps f : Two^m → Two^n are determined by their values on basis vectors:
  -- f(y) equals the join of f(e_i) scaled by y[i].
  f-basis : ∀ {m n} (f : Two^-join m ⇒J Two^-join n) (y : Two^ m .Carrier) → _≃_ (Two^ n) (fun f y)
                    (⋁ (Two^-join n) m (λ i → _·⊓_ {n} (proj i y) (fun f (e i))))
  f-basis {zero}  {n} f y .proj₁ = f .*→*J .join-semilattice._=>_.⊥-preserving
  f-basis {zero}  {n} f y .proj₂ = Two^ n .≤-bottom
  -- Strategy for suc case: use ∨-preserving to split f(y₀, y') = f(y₀, ⊥) ∨ f(O, y'),
  -- then handle head via case analysis on y₀, and tail via IH (f-basis on f-tail).
  f-basis {suc m} {n} f (y₀ , y') .proj₁ =
    Two^ n .≤-trans
      (f .*→*J .funcJ .preorder._=>_.mono {x₂ = Two^ (suc m) ._∨_ (y₀ , Two^ m .⊥) (O , y')} (two.⊔-upper₁ , Two^ m .inr))
      (Two^ n .≤-trans (f .*→*J .join-semilattice._=>_.∨-preserving {(y₀ , Two^ m .⊥)} {(O , y')})
        (∨-mono (Two^ n) (head-proof y₀) (f-basis (f-tail f) y' .proj₁)))
    where
      head-proof : ∀ y₀ → Two^ n ._≤_ (fun f (y₀ , Two^ m .⊥)) (_·⊓_ {n} y₀ (fun f (I , Two^ m .⊥)))
      head-proof O = Two^ n .≤-trans (f .*→*J .join-semilattice._=>_.⊥-preserving) (Two^ n .≤-bottom)
      head-proof I = ·⊓-I {n} (fun f (I , Two^ m .⊥)) .proj₂
  f-basis {suc m} {n} f (y₀ , y') .proj₂ =
    Two^ n .[_∨_] (head-proof y₀) (tail-proof)
    where
      head-proof : ∀ y₀ → Two^ n ._≤_ (_·⊓_ {n} y₀ (fun f (I , Two^ m .⊥))) (fun f (y₀ , y'))
      head-proof O = Two^ n .≤-trans (·⊓-O {n} (fun f (I , Two^ m .⊥)) .proj₁) (Two^ n .≤-bottom)
      head-proof I =
        Two^ n .≤-trans
          (·⊓-I {n} (fun f (I , Two^ m .⊥)) .proj₁)
          (f .*→*J .funcJ .preorder._=>_.mono {(I , Two^ m .⊥)} {(I , y')} (tt , Two^ m .≤-bottom))
      tail-proof : Two^ n ._≤_
                     (⋁ (Two^-join n) m (λ i → _·⊓_ {n} (proj i y') (fun f (O , e i))))
                     (fun f (y₀ , y'))
      tail-proof = Two^ n .≤-trans
                     (f-basis (f-tail f) y' .proj₂)
                     (f .*→*J .funcJ .preorder._=>_.mono {(O , y')} {(y₀ , y')} (tt , Two^ m .≤-refl {y'}))

  -- Sanity-check: transpose corresponds to transposing the implied matrix.
  private
    matrix : ∀ {m n} → Two^-join m ⇒J Two^-join n → Fin n → Fin m → Two
    matrix f j i = proj j (fun f (e i))

    ⋅-e : ∀ {n} (u : Two^ n .Carrier) (j : Fin n) → _⋅_ {n} u (e j) ≃t proj j u
    ⋅-e {suc n} (O , u) zero = ⋅-⊥ {n} u , tt
    ⋅-e {suc n} (I , u) zero = tt , tt
    ⋅-e {suc n} (O , u) (suc j) = ⋅-e {n} u j
    ⋅-e {suc n} (I , u) (suc j) = ⋅-e {n} u j

    transpose-matrix : ∀ m n (f : Two^-join m ⇒J Two^-join n) (i : Fin m) (j : Fin n) →
                      matrix {n} {m} (transpose {m} {n} f) i j ≃t matrix {m} {n} f j i
    transpose-matrix m n f i j =
      ≃t-trans (proj-tabulate {m} (λ k → _⋅_ {n} (fun f (e k)) (e j)) i)
              (⋅-e {n} (fun f (e i)) j)

    -- FIXME: analogous De Morgan dual statement for adjoint.

  -- Conjugate embedding: (transpose f, f) forms a conjugate pair Two^n ⇒c Two^m.
  to-conj : ∀ {m n} → Two^-join m ⇒J Two^-join n → conjugate._⇒c_ (Two^-conj n) (Two^-conj m)
  to-conj {m} {n} f .conjugate._⇒c_.right = transpose {m} {n} f .*→*J .funcJ
  to-conj {m} {n} f .conjugate._⇒c_.left  = f .*→*J .funcJ
  to-conj {m} {n} f .conjugate._⇒c_.conjugate .proj₁ = {!!}
  to-conj {m} {n} f .conjugate._⇒c_.conjugate .proj₂ = {!!}

  -- Galois embedding: (adjoint f, f) forms a Galois connection.
  to-gal : ∀ {m n} → Two^-join m ⇒J Two^-join n → galois._⇒g_ (Two^ n) (Two^ m)
  to-gal {m} {n} f .galois._⇒g_.right = adjoint {m} {n} f .*→*M .funcM
  to-gal {m} {n} f .galois._⇒g_.left  = f .*→*J .funcJ
  to-gal {zero}  {n} f .galois._⇒g_.left⊣right .proj₁ _ =
    Two^ n .≤-trans (f .*→*J .join-semilattice._=>_.⊥-preserving) (Two^ n .≤-bottom)
  to-gal {suc m} {n} f .galois._⇒g_.left⊣right .proj₁ = {!!}
  to-gal {zero}  {n} f .galois._⇒g_.left⊣right .proj₂ _ = tt
  to-gal {suc m} {n} f .galois._⇒g_.left⊣right .proj₂ = {!!}
