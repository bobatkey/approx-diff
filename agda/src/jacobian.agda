{-# OPTIONS --postfix-projections --prop --safe #-}

module jacobian where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_)
open import two using (Two; I; O; _⊓_; _⊔_; ⊔-upper₂; ≤-isPreorder; ⊓-isMeet; I-isTop)
open import basics using (IsPreorder)
open IsPreorder ≤-isPreorder using (_≃_; ≃-refl; ≃-trans)
import join-semilattice-category
import meet-semilattice-category
import meet-semilattice
import galois

-- Objects: Bool^n as a bounded lattice, the n-fold product of TWO.
-- FIXME: using galois.Obj as a stand-in for BoundedLattice, which we don't have yet.

Bool^ : ℕ → galois.Obj
Bool^ zero    = galois.𝟙
Bool^ (suc n) = galois._⊕_ galois.TWO (Bool^ n)

-- Join-semilattice and meet-semilattice views.
Bool^-join : ℕ → join-semilattice-category.Obj
Bool^-join n .join-semilattice-category.Obj.carrier = Bool^ n .galois.Obj.carrier
Bool^-join n .join-semilattice-category.Obj.joins   = Bool^ n .galois.Obj.joins

Bool^-meet : ℕ → meet-semilattice-category.Obj
Bool^-meet n .meet-semilattice-category.Obj.carrier = Bool^ n .galois.Obj.carrier
Bool^-meet n .meet-semilattice-category.Obj.meets   = Bool^ n .galois.Obj.meets

open galois.Obj hiding (_≃_; ≃-refl; ≃-sym; ≃-trans)

-- Basis vectors, projection and tabulation for Bool^n.

e : ∀ {n} → Fin n → Bool^ n .Carrier
e {suc n} zero = I , Bool^ n .⊥
e {suc n} (suc i) = O , e i

proj : ∀ {n} → Fin n → Bool^ n .Carrier → Two
proj zero (b , _)  = b
proj (suc i) (_ , v) = proj i v

open import Data.Unit using (tt)
open import prop using (tt; _,_; _∧_; proj₁; proj₂)

tabulate : ∀ {n} → (Fin n → Two) → Bool^ n .Carrier
tabulate {zero} _ = tt
tabulate {suc n} f = f zero , tabulate {n} (λ i → f (suc i))

-- Dot product: u ⋅ v = (u₀ ⊓ v₀) ⊔ ... ⊔ (uₙ ⊓ vₙ).
module _ where
  _⋅_ : ∀ {n} → Bool^ n .Carrier → Bool^ n .Carrier → Two
  _⋅_ {zero}  _ _ = O
  _⋅_ {suc n} (a , u) (b , v) = (a ⊓ b) ⊔ _⋅_ {n} u v

  -- ⋅ is join-preserving and monotone in its second argument.
  ⋅-⊥ : ∀ {n} (u : Bool^ n .Carrier) → two._≤_ (_⋅_ {n} u (Bool^ n .⊥)) O
  ⋅-⊥ {zero}  _ = tt
  ⋅-⊥ {suc n} (O , v) = ⋅-⊥ {n} v
  ⋅-⊥ {suc n} (I , v) = ⋅-⊥ {n} v

  ⋅-∨ : ∀ {n} (u v w : Bool^ n .Carrier) →
        two._≤_ (_⋅_ {n} u (Bool^ n ._∨_ v w)) ((_⋅_ {n} u v) ⊔ (_⋅_ {n} u w))
  ⋅-∨ {zero} _ _ _ = tt
  ⋅-∨ {suc n} (O , u) (_ , v) (_ , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (O , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (I , w) = ⊔-upper₂
  ⋅-∨ {suc n} (I , u) (I , v) (_ , w) = tt

  ⋅-mono : ∀ {n} (u : Bool^ n .Carrier) {v w : Bool^ n .Carrier} →
           Bool^ n ._≤_ v w → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} u w)
  ⋅-mono {zero}  _ _ = tt
  ⋅-mono {suc n} (O , u) {_ , v} {_ , w} (_ , v≤w) = ⋅-mono {n} u v≤w
  ⋅-mono {suc n} (I , u) {O , v} {_ , w} (_   , v≤w) = two.≤-trans (⋅-mono {n} u v≤w) ⊔-upper₂
  ⋅-mono {suc n} (I , u) {I , v} {I , w} (_   , v≤w) = tt

-- Pointwise negation on Bool^n.
¬ : ∀ {n} → Bool^ n .Carrier → Bool^ n .Carrier
¬ {zero}  _       = tt
¬ {suc n} (a , u) = two.¬ a , ¬ {n} u

¬-anti : ∀ {a b : Two} → two._≤_ a b → two._≤_ (two.¬ b) (two.¬ a)
¬-anti {O} {O} _ = tt
¬-anti {O} {I} _ = tt
¬-anti {I} {I} _ = tt

¬-anti^ : ∀ {n} {v w : Bool^ n .Carrier} → Bool^ n ._≤_ v w → Bool^ n ._≤_ (¬ {n} w) (¬ {n} v)
¬-anti^ {zero}  _           = tt
¬-anti^ {suc n} (a≤b , v≤w) = ¬-anti a≤b , ¬-anti^ {n} v≤w

-- Co-dot product (De Morgan dual of ⋅).
_⊡_ : ∀ {n} → Bool^ n .Carrier → Bool^ n .Carrier → Two
_⊡_ {n} u v = two.¬ (_⋅_ {n} (¬ {n} u) (¬ {n} v))

-- ⊡ is monotone in its second argument (via De Morgan from ⋅-mono).
⊡-mono : ∀ {n} (u : Bool^ n .Carrier) {v w : Bool^ n .Carrier} →
         Bool^ n ._≤_ v w → two._≤_ (_⊡_ {n} u v) (_⊡_ {n} u w)
⊡-mono {n} u v≤w = ¬-anti (⋅-mono {n} (¬ {n} u) (¬-anti^ {n} v≤w))

-- ¬ swaps ⊤ and ⊥.
¬-⊤ : ∀ {n} → Bool^ n ._≤_ (¬ {n} (Bool^ n .⊤)) (Bool^ n .⊥)
¬-⊤ {zero}  = tt
¬-⊤ {suc n} = tt , ¬-⊤ {n}

-- ⊡ preserves ∧ in its second argument.
⊡-∧ : ∀ {n} (u v w : Bool^ n .Carrier) →
      two._≤_ ((_⊡_ {n} u v) ⊓ (_⊡_ {n} u w)) (_⊡_ {n} u (galois.Obj._∧_ (Bool^ n) v w))
⊡-∧ {zero}  _ _ _ = tt
⊡-∧ {suc n} (O , u) (O , v) (_ , w) = tt
⊡-∧ {suc n} (O , u) (I , v) (O , w) = two.⊓-lower₂
⊡-∧ {suc n} (O , u) (I , v) (I , w) = ⊡-∧ {n} u v w
⊡-∧ {suc n} (I , u) (_ , v) (_ , w) = ⊡-∧ {n} u v w

-- ⊡ with ⊤ is I (via De Morgan from ⋅-⊥).
⊡-⊤ : ∀ {n} (u : Bool^ n .Carrier) → two._≤_ I (_⊡_ {n} u (Bool^ n .⊤))
⊡-⊤ {n} u = ¬-anti (two.≤-trans (⋅-mono {n} (¬ {n} u) (¬-⊤ {n})) (⋅-⊥ {n} (¬ {n} u)))

-- Bool^n as a conjugate.Obj (Heyting algebra).
import conjugate

Bool^-conj : ℕ → conjugate.Obj
Bool^-conj n .conjugate.Obj.carrier = Bool^ n .carrier
Bool^-conj n .conjugate.Obj.meets = Bool^ n .meets
Bool^-conj n .conjugate.Obj.joins = Bool^ n .joins
Bool^-conj zero .conjugate.Obj.#-reflect _ = tt
Bool^-conj (suc n) .conjugate.Obj.#-reflect {x₁ , x₂} {y₁ , y₂} h =
  conjugate.Obj.#-reflect conjugate.TWO (λ z₁ y#z →
    proj₁ (h (z₁ , Bool^ n .⊥) (y#z , conjugate.Obj.π₂ (Bool^-conj n)))) ,
  conjugate.Obj.#-reflect (Bool^-conj n) (λ z₂ y#z →
    proj₂ (h (O , z₂) (conjugate.Obj.π₂ conjugate.TWO , y#z)))
Bool^-conj zero .conjugate.Obj.∧-∨-distrib _ _ _ = tt
Bool^-conj (suc n) .conjugate.Obj.∧-∨-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
  conjugate.Obj.∧-∨-distrib conjugate.TWO x₁ y₁ z₁ ,
  conjugate.Obj.∧-∨-distrib (Bool^-conj n) x₂ y₂ z₂
Bool^-conj zero .conjugate.Obj.∨-∧-distrib _ _ _ = tt
Bool^-conj (suc n) .conjugate.Obj.∨-∧-distrib (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) =
  conjugate.Obj.∨-∧-distrib conjugate.TWO x₁ y₁ z₁ ,
  conjugate.Obj.∨-∧-distrib (Bool^-conj n) x₂ y₂ z₂

-- Morphisms: join-semilattice morphisms Bool^m → Bool^n.
-- Every such map is determined by its values on basis vectors, i.e. by an n×m Bool matrix.
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
    -- tabulate is a join-semilattice isomorphism from (Fin m → Two) to Bool^m
    -- (with proj as inverse). We only need the forward direction here.
    tabulate-mono : ∀ {m} (g h : Fin m → Two) →
                    (∀ i → two._≤_ (g i) (h i)) → Bool^ m ._≤_ (tabulate {m} g) (tabulate {m} h)
    tabulate-mono {zero}  g h p = tt
    tabulate-mono {suc m} g h p = p zero , tabulate-mono {m} _ _ (λ i → p (suc i))

    tabulate-⊥ : ∀ {m} → Bool^ m ._≤_ (tabulate {m} (λ _ → O)) (Bool^ m .⊥)
    tabulate-⊥ {zero}  = tt
    tabulate-⊥ {suc m} = tt , tabulate-⊥ {m}

    tabulate-⊤ : ∀ {m} → Bool^ m ._≤_ (Bool^ m .⊤) (tabulate {m} (λ _ → I))
    tabulate-⊤ {zero}  = tt
    tabulate-⊤ {suc m} = tt , tabulate-⊤ {m}

    tabulate-∨ : ∀ {m} (g h : Fin m → Two) →
                 Bool^ m ._≤_ (tabulate {m} (λ i → g i ⊔ h i)) (Bool^ m ._∨_ (tabulate {m} g) (tabulate {m} h))
    tabulate-∨ {zero}  g h = tt
    tabulate-∨ {suc m} g h = two.≤-refl , tabulate-∨ {m} (λ i → g (suc i)) (λ i → h (suc i))

    tabulate-∧ : ∀ {m} (g h : Fin m → Two) →
                 Bool^ m ._≤_ (galois.Obj._∧_ (Bool^ m) (tabulate {m} g) (tabulate {m} h)) (tabulate {m} (λ i → g i ⊓ h i))
    tabulate-∧ {zero}  g h = tt
    tabulate-∧ {suc m} g h = two.≤-refl , tabulate-∧ {m} (λ i → g (suc i)) (λ i → h (suc i))

    proj-tabulate : ∀ {n} (g : Fin n → Two) (i : Fin n) → proj i (tabulate {n} g) ≃ g i
    proj-tabulate {suc n} g zero = ≃-refl
    proj-tabulate {suc n} g (suc i) = proj-tabulate {n} (λ i → g (suc i)) i

  transpose : ∀ {m n} → Bool^-join m ⇒J Bool^-join n → Bool^-join n ⇒J Bool^-join m
  transpose {m} {n} f .*→*J .funcJ .funP v = tabulate {m} (λ i → _⋅_ {n} (fun f (e i)) v)
  transpose {m} {n} f .*→*J .funcJ .preorder._=>_.mono v≤w =
    tabulate-mono {m} _ _ (λ i → ⋅-mono {n} (fun f (e i)) v≤w)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.∨-preserving {v} {w} =
    Bool^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-∨ {n} (fun f (e i)) v w))
                     (tabulate-∨ {m} _ _)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.⊥-preserving =
    Bool^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-⊥ {n} (fun f (e i))))
                     (tabulate-⊥ {m})

  adjoint : ∀ {m n} → Bool^-join m ⇒J Bool^-join n → Bool^-meet n ⇒M Bool^-meet m
  adjoint {m} {n} f .*→*M .funcM .funP v = tabulate {m} (λ i → _⊡_ {n} (¬ {n} (fun f (e i))) v)
  adjoint {m} {n} f .*→*M .funcM .preorder._=>_.mono v≤w =
    tabulate-mono {m} _ _ (λ i → ⊡-mono {n} (¬ {n} (fun f (e i))) v≤w)
  adjoint {m} {n} f .*→*M .meet-semilattice._=>_.∧-preserving {v} {w} =
    Bool^ m .≤-trans (tabulate-∧ {m} _ _)
                     (tabulate-mono {m} _ _ (λ i → ⊡-∧ {n} (¬ {n} (fun f (e i))) v w))
  adjoint {m} {n} f .*→*M .meet-semilattice._=>_.⊤-preserving =
    Bool^ m .≤-trans (tabulate-⊤ {m})
                     (tabulate-mono {m} _ _ (λ i → ⊡-⊤ {n} (¬ {n} (fun f (e i)))))

  -- Sanity-check: transpose corresponds to transposing the implied matrix.
  private
    matrix : ∀ {m n} → Bool^-join m ⇒J Bool^-join n → Fin n → Fin m → Two
    matrix f j i = proj j (fun f (e i))

    ⋅-e : ∀ {n} (u : Bool^ n .Carrier) (j : Fin n) → _⋅_ {n} u (e j) ≃ proj j u
    ⋅-e {suc n} (O , u) zero = ⋅-⊥ {n} u , tt
    ⋅-e {suc n} (I , u) zero = tt , tt
    ⋅-e {suc n} (O , u) (suc j) = ⋅-e {n} u j
    ⋅-e {suc n} (I , u) (suc j) = ⋅-e {n} u j

    transpose-matrix : ∀ m n (f : Bool^-join m ⇒J Bool^-join n) (i : Fin m) (j : Fin n) →
                      matrix {n} {m} (transpose {m} {n} f) i j ≃ matrix {m} {n} f j i
    transpose-matrix m n f i j =
      ≃-trans (proj-tabulate {m} (λ k → _⋅_ {n} (fun f (e k)) (e j)) i)
              (⋅-e {n} (fun f (e i)) j)

    -- FIXME: analogous De Morgan dual statement for adjoint.

  -- Conjugate embedding: (f, transpose f) forms a conjugate pair.
  to-conj : ∀ {m n} → Bool^-join m ⇒J Bool^-join n → conjugate._⇒c_ (Bool^-conj m) (Bool^-conj n)
  to-conj {m} {n} f .conjugate._⇒c_.right = f .*→*J .funcJ
  to-conj {m} {n} f .conjugate._⇒c_.left  = transpose {m} {n} f .*→*J .funcJ
  to-conj {zero}  {n} f .conjugate._⇒c_.conjugate .proj₁ _ = tt
  to-conj {suc m} {n} f .conjugate._⇒c_.conjugate .proj₁ = {!!}
  to-conj {zero}  {n} f .conjugate._⇒c_.conjugate .proj₂ _ =
    Bool^ n .≤-trans (galois.Obj.∧-mono (Bool^ n) (Bool^ n .≤-refl) (f .*→*J .join-semilattice._=>_.⊥-preserving))
                     (galois.Obj.π₂ (Bool^ n))
  to-conj {suc m} {n} f .conjugate._⇒c_.conjugate .proj₂ = {!!}
