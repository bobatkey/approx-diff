{-# OPTIONS --postfix-projections --prop --safe #-}

module bool-jacobian where

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
import conjugate

open conjugate.Obj

-- Objects: Two^n as iterated biproduct of TWO in HeytConj. Taking the biproduct in HeytConj rather than
-- LatGal means the Heyting-algebra structure propagates through biproducts for free, so Two^n is automatically
-- Heyting.
Two^ : ℕ → conjugate.Obj
Two^ zero = conjugate.𝟙
Two^ (suc n) = conjugate._⊕_ conjugate.TWO (Two^ n)

-- Forgetful map to galois.Obj.
Two^-gal : ℕ → galois.Obj
Two^-gal n .galois.Obj.carrier = Two^ n .carrier
Two^-gal n .galois.Obj.meets = Two^ n .meets
Two^-gal n .galois.Obj.joins = Two^ n .joins

-- Join-semilattice and meet-semilattice views.
Two^J : ℕ → join-semilattice-category.Obj
Two^J n .join-semilattice-category.Obj.carrier = Two^ n .carrier
Two^J n .join-semilattice-category.Obj.joins = Two^ n .joins

Two^M : ℕ → meet-semilattice-category.Obj
Two^M n .meet-semilattice-category.Obj.carrier = Two^ n .carrier
Two^M n .meet-semilattice-category.Obj.meets = Two^ n .meets

-- Standard basis vectors
e : ∀ {n} → Fin n → Two^ n .Carrier
e {suc n} zero = I , Two^ n .⊥
e {suc n} (suc i) = O , e i

proj : ∀ {n} → Fin n → Two^ n .Carrier → Two
proj zero (b , _)  = b
proj (suc i) (_ , v) = proj i v

open import Data.Unit using (tt)
open import prop using (tt; _,_; _∧_; _⇔_; proj₁; proj₂)

-- Join of a finite family of join semilattices (so neither binary IsJoin nor arbitrary IsBigJoin). Be nicer
-- to define in terms of the iterated product, but the function representation is convenient for now.
module _ (J : join-semilattice-category.Obj) where
  open join-semilattice-category.Obj

  ⋁ : ∀ n → (Fin n → J .Carrier) → J .Carrier
  ⋁ zero _ = J .⊥
  ⋁ (suc n) f = J ._∨_ (f zero) (⋁ n (λ i → f (suc i)))

  ⋁-upper : ∀ n (f : Fin n → J .Carrier) (i : Fin n) → J ._≤_ (f i) (⋁ n f)
  ⋁-upper (suc n) f zero = J .inl
  ⋁-upper (suc n) f (suc i) = J .≤-trans (⋁-upper n (λ j → f (suc j)) i) (J .inr)

  ⋁-lub : ∀ n (f : Fin n → J .Carrier) (x : J .Carrier) → (∀ i → J ._≤_ (f i) x) → J ._≤_ (⋁ n f) x
  ⋁-lub zero f x p = J .≤-bottom
  ⋁-lub (suc n) f x p = J .[_∨_] (p zero) (⋁-lub n (λ i → f (suc i)) x (λ i → p (suc i)))

-- Dot product (sum of products of entries of equal-length vectors):
--   u ⋅ v = (u₀ ⊓ v₀) ⊔ ... ⊔ (uₙ ⊓ vₙ)
module _ where
  _⋅_ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier → Two
  _⋅_ {zero} _ _ = O
  _⋅_ {suc n} (a , u) (b , v) = (a ⊓ b) ⊔ _⋅_ {n} u v

  ⋅-comm : ∀ {n} (u v : Two^ n .Carrier) → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} v u)
  ⋅-comm {zero}  _ _ = tt
  ⋅-comm {suc n} (O , u) (O , v) = ⋅-comm {n} u v
  ⋅-comm {suc n} (O , u) (I , v) = ⋅-comm {n} u v
  ⋅-comm {suc n} (I , u) (O , v) = ⋅-comm {n} u v
  ⋅-comm {suc n} (I , u) (I , v) = tt

  -- Bilinear (join-preserving in each argument), but one side is enough.
  ⋅-⊥ : ∀ {n} (u : Two^ n .Carrier) → two._≤_ (_⋅_ {n} u (Two^ n .⊥)) O
  ⋅-⊥ {zero} _ = tt
  ⋅-⊥ {suc n} (O , v) = ⋅-⊥ {n} v
  ⋅-⊥ {suc n} (I , v) = ⋅-⊥ {n} v

  ⋅-∨ : ∀ {n} (u v w : Two^ n .Carrier) →
        two._≤_ (_⋅_ {n} u (Two^ n ._∨_ v w)) ((_⋅_ {n} u v) ⊔ (_⋅_ {n} u w))
  ⋅-∨ {zero} _ _ _ = tt
  ⋅-∨ {suc n} (O , u) (_ , v) (_ , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (O , w) = ⋅-∨ {n} u v w
  ⋅-∨ {suc n} (I , u) (O , v) (I , w) = ⊔-upper₂
  ⋅-∨ {suc n} (I , u) (I , v) (_ , w) = tt

  private
    ⋅-monoᵣ : ∀ {n} (u : Two^ n .Carrier) {v w : Two^ n .Carrier} →
               Two^ n ._≤_ v w → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} u w)
    ⋅-monoᵣ {zero} _ _ = tt
    ⋅-monoᵣ {suc n} (O , u) {_ , v} {_ , w} (_ , v≤w) = ⋅-monoᵣ {n} u v≤w
    ⋅-monoᵣ {suc n} (I , u) {O , v} {_ , w} (_ , v≤w) = two.≤-trans (⋅-monoᵣ {n} u v≤w) ⊔-upper₂
    ⋅-monoᵣ {suc n} (I , u) {I , v} {I , w} (_ , v≤w) = tt

  ⋅-mono : ∀ {n} {u u' v v' : Two^ n .Carrier} →
           Two^ n ._≤_ u u' → Two^ n ._≤_ v v' → two._≤_ (_⋅_ {n} u v) (_⋅_ {n} u' v')
  ⋅-mono {n} {u} {u'} {v} {v'} u≤u' v≤v' =
    begin
      _⋅_ {n} u v
    ≤⟨ ⋅-monoᵣ {n} u v≤v' ⟩
      _⋅_ {n} u v'
    ≤⟨ ⋅-comm {n} u v' ⟩
      _⋅_ {n} v' u
    ≤⟨ ⋅-monoᵣ {n} v' u≤u' ⟩
      _⋅_ {n} v' u'
    ≤⟨ ⋅-comm {n} v' u' ⟩
      _⋅_ {n} u' v'
    ∎ where open basics.≤-Reasoning two.≤-isPreorder

-- Two^n is itself Boolean, with negation defined componentwise.
module _ where
  ¬ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier
  ¬ {zero} _ = tt
  ¬ {suc n} (a , u) = two.¬ a , ¬ {n} u

  ¬-anti : ∀ {a b : Two} → two._≤_ a b → two._≤_ (two.¬ b) (two.¬ a)
  ¬-anti {O} {O} _ = tt
  ¬-anti {O} {I} _ = tt
  ¬-anti {I} {I} _ = tt

  ¬-anti^ : ∀ {n} {v w : Two^ n .Carrier} → Two^ n ._≤_ v w → Two^ n ._≤_ (¬ {n} w) (¬ {n} v)
  ¬-anti^ {zero} _ = tt
  ¬-anti^ {suc n} (a≤b , v≤w) = ¬-anti a≤b , ¬-anti^ {n} v≤w

  ¬-involutive : ∀ {n} (u : Two^ n .Carrier) → _≃_ (Two^ n) u (¬ {n} (¬ {n} u))
  ¬-involutive {zero}  _ = tt , tt
  ¬-involutive {suc n} (O , u) = (tt , ¬-involutive {n} u .proj₁) , (tt , ¬-involutive {n} u .proj₂)
  ¬-involutive {suc n} (I , u) = (tt , ¬-involutive {n} u .proj₁) , (tt , ¬-involutive {n} u .proj₂)

-- "Co-dot" product (De Morgan dual of ⋅), or dot product in the dual semiring.
--   u ⊡ v = (u₀ ⊔ v₀) ⊓ ... ⊓ (uₙ ⊔ vₙ)
_⊡_ : ∀ {n} → Two^ n .Carrier → Two^ n .Carrier → Two
_⊡_ {n} u v = two.¬ (_⋅_ {n} (¬ {n} u) (¬ {n} v))

⊡-mono : ∀ {n} (u : Two^ n .Carrier) {v w : Two^ n .Carrier} →
         Two^ n ._≤_ v w → two._≤_ (_⊡_ {n} u v) (_⊡_ {n} u w)
⊡-mono {n} u v≤w = ¬-anti (⋅-mono {n} (Two^ n .≤-refl) (¬-anti^ {n} v≤w))

-- Scalar product, with O as annihilator and I as identity.
module _ where
  _·⊓_ : ∀ {n} → Two → Two^ n .Carrier → Two^ n .Carrier
  _·⊓_ {zero} _ _ = tt
  _·⊓_ {suc n} a (b , u) = (a ⊓ b) , _·⊓_ {n} a u

  ·⊓-O : ∀ {n} (u : Two^ n .Carrier) → _≃_ (Two^ n) (_·⊓_ {n} O u) (Two^ n .⊥)
  ·⊓-O {zero} _ = tt , tt
  ·⊓-O {suc n} (_ , u) = (tt , ·⊓-O {n} u .proj₁) , (tt , ·⊓-O {n} u .proj₂)

  ·⊓-I : ∀ {n} (u : Two^ n .Carrier) → _≃_ (Two^ n) (_·⊓_ {n} I u) u
  ·⊓-I {zero} _ = tt , tt
  ·⊓-I {suc n} (_ , u) = (two.≤-refl , ·⊓-I {n} u .proj₁) , (two.≤-refl , ·⊓-I {n} u .proj₂)

-- Pointwise lifting of meet/implication adjunction.
⊡-adj : ∀ n (a : Two) (u v : Two^ n .Carrier) →
        Two^ n ._≤_ (_·⊓_ {n} a u) v ⇔ two._≤_ a (_⊡_ {n} (¬ {n} u) v)
⊡-adj zero    a u v .proj₁ _ = I-isTop .IsTop.≤-top
⊡-adj (suc n) O u v .proj₁ _ = tt
⊡-adj (suc n) I (O , u) (_ , v) .proj₁ (h , t) = ⊡-adj n I u v .proj₁ t
⊡-adj (suc n) I (I , _) (O , _) .proj₁ (() , _)
⊡-adj (suc n) I (I , u) (I , v) .proj₁ (_ , t) = ⊡-adj n I u v .proj₁ t
⊡-adj zero    a u v .proj₂ _ = tt
⊡-adj (suc n) O (u₀ , u) (v₀ , v) .proj₂ h = tt , ⊡-adj n O u v .proj₂ tt
⊡-adj (suc n) I (O , u) (v₀ , v) .proj₂ h = tt , ⊡-adj n I u v .proj₂ h
⊡-adj (suc n) I (I , u) (O , v) .proj₂ ()
⊡-adj (suc n) I (I , u) (I , v) .proj₂ h = tt , ⊡-adj n I u v .proj₂ h

¬-⊤ : ∀ {n} → Two^ n ._≤_ (¬ {n} (Two^ n .⊤)) (Two^ n .⊥)
¬-⊤ {zero}  = tt
¬-⊤ {suc n} = tt , ¬-⊤ {n}

-- ⊡ preserves ∧ in its second argument.
⊡-∧ : ∀ {n} (u v w : Two^ n .Carrier) →
      two._≤_ ((_⊡_ {n} u v) ⊓ (_⊡_ {n} u w)) (_⊡_ {n} u (conjugate.Obj._∧_ (Two^ n) v w))
⊡-∧ {zero}  _ _ _ = tt
⊡-∧ {suc n} (O , u) (O , v) (_ , w) = tt
⊡-∧ {suc n} (O , u) (I , v) (O , w) = two.⊓-lower₂
⊡-∧ {suc n} (O , u) (I , v) (I , w) = ⊡-∧ {n} u v w
⊡-∧ {suc n} (I , u) (_ , v) (_ , w) = ⊡-∧ {n} u v w

-- ⊡ with ⊤ is I (via De Morgan from ⋅-⊥).
⊡-⊤ : ∀ {n} (u : Two^ n .Carrier) → two._≤_ I (_⊡_ {n} u (Two^ n .⊤))
⊡-⊤ {n} u = ¬-anti (two.≤-trans (⋅-mono {n} (Two^ n .≤-refl) (¬-⊤ {n})) (⋅-⊥ {n} (¬ {n} u)))

-- Holds in any Boolean algebra.
#-↔-≤ : ∀ {n} (u v : Two^ n .Carrier) → conjugate.Obj._#_ (Two^ n) u v ⇔ Two^ n ._≤_ u (¬ {n} v)
#-↔-≤ {zero}  _       _       .proj₁ _ = tt
#-↔-≤ {suc n} (O , _) (_ , _) .proj₁ (_ , t) = tt , #-↔-≤ {n} _ _ .proj₁ t
#-↔-≤ {suc n} (I , _) (O , _) .proj₁ (_ , t) = tt , #-↔-≤ {n} _ _ .proj₁ t
#-↔-≤ {suc n} (I , _) (I , _) .proj₁ (() , _)
#-↔-≤ {zero}  _       _       .proj₂ _ = tt
#-↔-≤ {suc n} (O , _) (_ , _) .proj₂ (_ , t) = tt , #-↔-≤ {n} _ _ .proj₂ t
#-↔-≤ {suc n} (I , _) (O , _) .proj₂ (_ , t) = tt , #-↔-≤ {n} _ _ .proj₂ t
#-↔-≤ {suc n} (I , _) (I , _) .proj₂ (() , _)

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
    -- (tabulate, proj) is a join-semilattice isomorphism from (Fin m → Two) to Two^m.
    tabulate : ∀ {n} → (Fin n → Two) → Two^ n .Carrier
    tabulate {zero} _ = tt
    tabulate {suc n} f = f zero , tabulate {n} (λ i → f (suc i))

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
                 Two^ m ._≤_ (conjugate.Obj._∧_ (Two^ m) (tabulate {m} g) (tabulate {m} h)) (tabulate {m} (λ i → g i ⊓ h i))
    tabulate-∧ {zero}  g h = tt
    tabulate-∧ {suc m} g h = two.≤-refl , tabulate-∧ {m} (λ i → g (suc i)) (λ i → h (suc i))

    -- ¬ distributes over tabulate: ¬ (tabulate g) ≃ tabulate (λ i → two.¬ (g i)).
    ¬-tabulate : ∀ {m} (g : Fin m → Two) →
                 _≃_ (Two^ m) (¬ {m} (tabulate {m} g)) (tabulate {m} (λ i → two.¬ (g i)))
    ¬-tabulate {zero}  _ = tt , tt
    ¬-tabulate {suc m} g =
      (two.≤-refl , ¬-tabulate {m} (λ i → g (suc i)) .proj₁) ,
      (two.≤-refl , ¬-tabulate {m} (λ i → g (suc i)) .proj₂)

    -- Two^ m ._≤_ v w ⇔ ∀ i. two._≤_ (proj i v) (proj i w).
    proj-mono : ∀ {m} (v w : Two^ m .Carrier) →
                Two^ m ._≤_ v w ⇔ (∀ (i : Fin m) → two._≤_ (proj i v) (proj i w))
    proj-mono {zero}  _ _ .proj₁ _ ()
    proj-mono {zero}  _ _ .proj₂ _ = tt
    proj-mono {suc m} (_ , v) (_ , w) .proj₁ (h , _) zero    = h
    proj-mono {suc m} (_ , v) (_ , w) .proj₁ (_ , t) (suc i) = proj-mono {m} v w .proj₁ t i
    proj-mono {suc m} (_ , v) (_ , w) .proj₂ p = p zero , proj-mono {m} v w .proj₂ (λ i → p (suc i))

    proj-tabulate : ∀ {n} (g : Fin n → Two) (i : Fin n) → proj i (tabulate {n} g) ≃t g i
    proj-tabulate {suc n} g zero = ≃t-refl
    proj-tabulate {suc n} g (suc i) = proj-tabulate {n} (λ i → g (suc i)) i

  transpose : ∀ {m n} → Two^J m ⇒J Two^J n → Two^J n ⇒J Two^J m
  transpose {m} {n} f .*→*J .funcJ .funP v = tabulate {m} (λ i → _⋅_ {n} (fun f (e i)) v)
  transpose {m} {n} f .*→*J .funcJ .preorder._=>_.mono v≤w =
    tabulate-mono {m} _ _ (λ i → ⋅-mono {n} (Two^ n .≤-refl) v≤w)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.∨-preserving {v} {w} =
    Two^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-∨ {n} (fun f (e i)) v w))
                    (tabulate-∨ {m} _ _)
  transpose {m} {n} f .*→*J .join-semilattice._=>_.⊥-preserving =
    Two^ m .≤-trans (tabulate-mono {m} _ _ (λ i → ⋅-⊥ {n} (fun f (e i))))
                    (tabulate-⊥ {m})

  adjoint : ∀ {m n} → Two^J m ⇒J Two^J n → Two^M n ⇒M Two^M m
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
  f-tail : ∀ {m n} → Two^J (suc m) ⇒J Two^J n → Two^J m ⇒J Two^J n
  f-tail {m} {n} f .*→*J .funcJ .funP v = fun f (O , v)
  f-tail {m} {n} f .*→*J .funcJ .preorder._=>_.mono v≤v' =
    f .*→*J .funcJ .preorder._=>_.mono (tt , v≤v')
  f-tail {m} {n} f .*→*J .join-semilattice._=>_.∨-preserving =
    f .*→*J .join-semilattice._=>_.∨-preserving
  f-tail {m} {n} f .*→*J .join-semilattice._=>_.⊥-preserving = f .*→*J .join-semilattice._=>_.⊥-preserving

  -- Join-preserving maps f : Two^m → Two^n are determined by their values on basis vectors:
  -- f(y) equals the join of f(e_i) scaled by y[i].
  f-basis : ∀ {m n} (f : Two^J m ⇒J Two^J n) (y : Two^ m .Carrier) → _≃_ (Two^ n) (fun f y)
                    (⋁ (Two^J n) m (λ i → _·⊓_ {n} (proj i y) (fun f (e i))))
  f-basis {zero}  {n} f y .proj₁ = f .*→*J .join-semilattice._=>_.⊥-preserving
  f-basis {zero}  {n} f y .proj₂ = Two^ n .≤-bottom
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
    Two^ n .[_∨_]
      (head-proof y₀)
      (Two^ n .≤-trans
        (f-basis (f-tail f) y' .proj₂)
        (f .*→*J .funcJ .preorder._=>_.mono {(O , y')} {(y₀ , y')} (tt , Two^ m .≤-refl {y'})))
    where
      head-proof : ∀ y₀ → Two^ n ._≤_ (_·⊓_ {n} y₀ (fun f (I , Two^ m .⊥))) (fun f (y₀ , y'))
      head-proof O = Two^ n .≤-trans (·⊓-O {n} (fun f (I , Two^ m .⊥)) .proj₁) (Two^ n .≤-bottom)
      head-proof I =
        Two^ n .≤-trans
          (·⊓-I {n} (fun f (I , Two^ m .⊥)) .proj₁)
          (f .*→*J .funcJ .preorder._=>_.mono {(I , Two^ m .⊥)} {(I , y')} (tt , Two^ m .≤-bottom))

  -- Sanity-check: transpose corresponds to transposing the implied matrix.
  private
    matrix : ∀ {m n} → Two^J m ⇒J Two^J n → Fin n → Fin m → Two
    matrix f j i = proj j (fun f (e i))

    ⋅-e : ∀ {n} (u : Two^ n .Carrier) (j : Fin n) → _⋅_ {n} u (e j) ≃t proj j u
    ⋅-e {suc n} (O , u) zero = ⋅-⊥ {n} u , tt
    ⋅-e {suc n} (I , u) zero = tt , tt
    ⋅-e {suc n} (O , u) (suc j) = ⋅-e {n} u j
    ⋅-e {suc n} (I , u) (suc j) = ⋅-e {n} u j

    transpose-matrix : ∀ m n (f : Two^J m ⇒J Two^J n) (i : Fin m) (j : Fin n) →
                      matrix {n} {m} (transpose {m} {n} f) i j ≃t matrix {m} {n} f j i
    transpose-matrix m n f i j =
      ≃t-trans (proj-tabulate {m} (λ k → _⋅_ {n} (fun f (e k)) (e j)) i)
              (⋅-e {n} (fun f (e i)) j)

  -- (adjoint f) and (transpose f) are De Morgan dual.
  ¬transpose≃adjoint¬ : ∀ {m n} (f : Two^J m ⇒J Two^J n) (x : Two^ n .Carrier) →
                       _≃_ (Two^ m) (¬ {m} (fun (transpose {m} {n} f) x))
                                    (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun (¬ {n} x))
  ¬transpose≃adjoint¬ {m} {n} f x .proj₁ =
    Two^ m .≤-trans (¬-tabulate {m} (λ k → _⋅_ {n} (fun f (e k)) x) .proj₁) (tabulate-mono {m} _ _ per-i)
    where
      per-i : (i : Fin m) → two._≤_ (two.¬ (_⋅_ {n} (fun f (e i)) x))
                                    (_⊡_ {n} (¬ {n} (fun f (e i))) (¬ {n} x))
      per-i i = ¬-anti (⋅-mono {n} (¬-involutive {n} (fun f (e i)) .proj₂) (¬-involutive {n} x .proj₂))
  ¬transpose≃adjoint¬ {m} {n} f x .proj₂ =
    Two^ m .≤-trans (tabulate-mono {m} _ _ per-i) (¬-tabulate {m} (λ k → _⋅_ {n} (fun f (e k)) x) .proj₂)
    where
      per-i : (i : Fin m) → two._≤_ (_⊡_ {n} (¬ {n} (fun f (e i))) (¬ {n} x))
                                    (two.¬ (_⋅_ {n} (fun f (e i)) x))
      per-i i = ¬-anti (⋅-mono {n} (¬-involutive {n} (fun f (e i)) .proj₁) (¬-involutive {n} x .proj₁))

  -- Galois embedding: (adjoint f, f) forms a Galois connection.
  to-gal : ∀ {m n} → Two^J m ⇒J Two^J n → galois._⇒g_ (Two^-gal n) (Two^-gal m)
  to-gal {m} {n} f .galois._⇒g_.right = adjoint {m} {n} f .*→*M .funcM
  to-gal {m} {n} f .galois._⇒g_.left  = f .*→*J .funcJ
  to-gal {m} {n} f .galois._⇒g_.left⊣right {x} {y} .proj₁ y≤adj =
    let open basics.≤-Reasoning (Two^ n .conjugate.Obj.≤-isPreorder) in
    begin
      fun f y
    ≤⟨ f-basis f y .proj₁ ⟩
      ⋁ (Two^J n) m (λ i → _·⊓_ {n} (proj i y) (fun f (e i)))
    ≤⟨ ⋁-lub (Two^J n) m _ x per-i ⟩
      x
    ∎
    where
      per-i : (i : Fin m) → Two^ n ._≤_ (_·⊓_ {n} (proj i y) (fun f (e i))) x
      per-i i = ⊡-adj n (proj i y) (fun f (e i)) x .proj₂
        (begin
          proj i y
        ≤⟨ proj-mono {m} y (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun x) .proj₁ y≤adj i ⟩
          proj i (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun x)
        ≤⟨ proj-tabulate {m} (λ k → _⊡_ {n} (¬ {n} (fun f (e k))) x) i .proj₁ ⟩
          _⊡_ {n} (¬ {n} (fun f (e i))) x
        ∎)
        where open basics.≤-Reasoning two.≤-isPreorder
  to-gal {m} {n} f .galois._⇒g_.left⊣right {x} {y} .proj₂ fy≤x =
    proj-mono {m} y (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun x) .proj₂ per-i
    where
      per-i : (i : Fin m) → two._≤_ (proj i y) (proj i (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun x))
      per-i i =
        begin
          proj i y
        ≤⟨ ⊡-adj n (proj i y) (fun f (e i)) x .proj₁
             (Two^ n .≤-trans (⋁-upper (Two^J n) m _ i) (Two^ n .≤-trans (f-basis f y .proj₂) fy≤x)) ⟩
          _⊡_ {n} (¬ {n} (fun f (e i))) x
        ≤⟨ proj-tabulate {m} (λ k → _⊡_ {n} (¬ {n} (fun f (e k))) x) i .proj₂ ⟩
          proj i (adjoint {m} {n} f .*→*M .funcM .preorder._=>_.fun x)
        ∎
        where open basics.≤-Reasoning two.≤-isPreorder

  -- Conjugate embedding: (transpose f, f) forms a conjugate pair Two^n ⇒c Two^m.
  -- Derive from to-gal via De Morgan duality.
  to-conj : ∀ {m n} → Two^J m ⇒J Two^J n → conjugate._⇒c_ (Two^ n) (Two^ m)
  to-conj {m} {n} f .conjugate._⇒c_.right = transpose {m} {n} f .*→*J .funcJ
  to-conj {m} {n} f .conjugate._⇒c_.left  = f .*→*J .funcJ
  to-conj {m} {n} f .conjugate._⇒c_.conjugate {x} {y} .proj₁ y#tr =
    #-↔-≤ {n} (fun f y) x .proj₂
      (to-gal {m} {n} f .galois._⇒g_.left⊣right {¬ {n} x} {y} .proj₁
        (Two^ m .≤-trans
          (#-↔-≤ {m} y (fun (transpose {m} {n} f) x) .proj₁ y#tr)
          (¬transpose≃adjoint¬ f x .proj₁)))
  to-conj {m} {n} f .conjugate._⇒c_.conjugate {x} {y} .proj₂ fy#x =
    #-↔-≤ {m} y (fun (transpose {m} {n} f) x) .proj₂
      (Two^ m .≤-trans
        (to-gal {m} {n} f .galois._⇒g_.left⊣right {¬ {n} x} {y} .proj₂ (#-↔-≤ {n} (fun f y) x .proj₁ fy#x))
        (¬transpose≃adjoint¬ f x .proj₂))
