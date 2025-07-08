{-# OPTIONS --postfix-projections --prop --safe #-}

module approx-numbers where

open import Level using (0ℓ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import prop using (⊤; tt; ⊥; LiftS; liftS; _∧_; _,_; proj₁; proj₂)
open import preorder using (Preorder; _=>_)
open import meet-semilattice using (MeetSemilattice)
open import join-semilattice using (JoinSemilattice)
open import basics using (IsPreorder; IsMeet; IsTop; IsJoin; IsBottom)

import galois

{-
import categories
import grothendieck

module D = grothendieck.CategoryOfFamilies 0ℓ 0ℓ galois.cat
module DP = D.products galois.products
-}

open import Data.Rational using (ℚ; _≤_; _⊔_; _⊓_; _+_; _-_; 0ℚ; -_; Positive; _*_; _÷_; NonZero)
open import Data.Rational.Properties using (≤-refl; ≤-trans; ⊓-glb; ⊔-lub; p⊓q≤p; p⊓q≤q; +-mono-≤; module ≤-Reasoning; +-comm; ≤-reflexive; +-assoc; +-inverseʳ; +-identityʳ; +-identityˡ; ⊓-mono-≤; p≤p⊔q; p≤q⊔p; neg-antimono-≤; pos⇒nonZero; pos⇒nonNeg; *-monoˡ-≤-nonNeg)
open import Relation.Binary.PropositionalEquality using (sym)

open IsPreorder

------------------------------------------------------------------------------
adjoint₁ : ∀ {x y z} → x ≤ y + z → x - y ≤ z
adjoint₁ {x} {y} {z} ϕ = begin
    x - y
  ≤⟨ +-mono-≤ ϕ ≤-refl ⟩
    (y + z) - y
  ≤⟨ +-mono-≤ (≤-reflexive (+-comm y z)) ≤-refl ⟩
    (z + y) - y
  ≤⟨ ≤-reflexive (+-assoc z y (- y)) ⟩
    z + (y - y)
  ≤⟨ +-mono-≤ (≤-refl {z}) (≤-reflexive (+-inverseʳ y)) ⟩
    z + 0ℚ
  ≤⟨ ≤-reflexive (+-identityʳ z) ⟩
    z
  ∎
  where open ≤-Reasoning

adjoint₂ : ∀ {x y z} → x - y ≤ z → x ≤ y + z
adjoint₂ {x} {y} {z} ϕ = begin
    x
  ≤⟨ ≤-reflexive (sym (+-identityˡ x)) ⟩
    0ℚ + x
  ≤⟨ +-mono-≤ (≤-reflexive (sym (+-inverseʳ y))) ≤-refl ⟩
    (y + (- y)) + x
  ≤⟨ ≤-reflexive (+-assoc y (- y) x) ⟩
    y + ((- y) + x)
  ≤⟨ +-mono-≤ (≤-refl {y}) (≤-reflexive (+-comm (- y) x)) ⟩
    y + (x - y)
  ≤⟨ +-mono-≤ (≤-refl {y}) ϕ ⟩
    y + z
  ∎
  where open ≤-Reasoning

adjoint₂' : ∀ {x y z} → x + y ≤ z → y ≤ z - x
adjoint₂' {x} {y} {z} ϕ =
  ≤-trans (adjoint₂ {y} { - x} {z} {!!}) (≤-reflexive (+-comm (- x) z))

------------------------------------------------------------------------------
-- Intervals, without bottom

record Intv (q : ℚ) : Set where
  field
    lower : ℚ
    upper : ℚ
    l≤q   : lower ≤ q
    q≤u   : q ≤ upper
open Intv

_⊑_ : ∀ {q} → Intv q → Intv q → Prop
x ⊑ y = LiftS 0ℓ (x .lower ≤ y .lower) ∧ LiftS 0ℓ (y .upper ≤ x .upper)

⊑I-isPreorder : ∀ {q} → IsPreorder (_⊑_ {q})
⊑I-isPreorder .refl = (liftS ≤-refl) , (liftS ≤-refl)
⊑I-isPreorder .trans (liftS ϕ₁ , liftS ϕ₂) (liftS ψ₁ , liftS ψ₂) =
  (liftS (≤-trans ϕ₁ ψ₁)) , (liftS (≤-trans ψ₂ ϕ₂))

_⊓I_ : ∀ {q} → Intv q → Intv q → Intv q
(x ⊓I y) .lower = x .lower ⊓ y .lower
(x ⊓I y) .upper = x .upper ⊔ y .upper
(x ⊓I y) .l≤q = ≤-trans (p⊓q≤p _ _) (x .l≤q)
(x ⊓I y) .q≤u = ≤-trans (x .q≤u) (p≤p⊔q _ _)

⊤I : ∀ {q} → Intv q
⊤I {q} .lower = q
⊤I {q} .upper = q
⊤I {q} .l≤q = ≤-refl
⊤I {q} .q≤u = ≤-refl

⊔I-isMeet : ∀ {q} → IsMeet (⊑I-isPreorder {q}) _⊓I_
⊔I-isMeet .IsMeet.π₁ = (liftS {!!}) , (liftS {!!})
⊔I-isMeet .IsMeet.π₂ = (liftS {!!}) , (liftS {!!})
⊔I-isMeet .IsMeet.⟨_,_⟩ = {!!}

_⊔I_ : ∀ {q} → Intv q → Intv q → Intv q
(x ⊔I y) .lower = x .lower ⊔ y .lower
(x ⊔I y) .upper = x .upper ⊓ y .upper
(x ⊔I y) .l≤q = ⊔-lub (x .l≤q) (y .l≤q)
(x ⊔I y) .q≤u = ⊓-glb (x .q≤u) (y .q≤u)

------------------------------------------------------------------------------
-- Addition

add-right : ∀ q₁ q₂ → Intv q₁ → Intv q₂ → Intv (q₁ + q₂)
add-right q₁ q₂ x y .lower = (q₂ + x .lower) ⊓ (q₁ + y .lower)
add-right q₁ q₂ x y .upper = (q₂ + x .upper) ⊔ (q₁ + y .upper)
add-right q₁ q₂ x y .l≤q = ≤-trans (p⊓q≤q (q₂ + x .lower) (q₁ + y .lower)) (+-mono-≤ (≤-refl {q₁}) (y .l≤q))
add-right q₁ q₂ x y .q≤u = ≤-trans (+-mono-≤ (≤-refl {q₁}) (y .q≤u)) (p≤q⊔p (q₂ + x .upper) _)

add-left : ∀ q₁ q₂ → Intv (q₁ + q₂) → Intv q₁ × Intv q₂
add-left q₁ q₂ x .proj₁ .lower = x .lower - q₂
add-left q₁ q₂ x .proj₁ .upper = x .upper - q₂
add-left q₁ q₂ x .proj₁ .l≤q = adjoint₁ {x .lower} {q₂} {q₁} (≤-trans (x .l≤q) (≤-reflexive (+-comm q₁ q₂)))
add-left q₁ q₂ x .proj₁ .q≤u = adjoint₂' {q₂} {q₁} {x .upper} (≤-trans (≤-reflexive (+-comm q₂ q₁)) (x .q≤u))
add-left q₁ q₂ x .proj₂ .lower = x .lower - q₁
add-left q₁ q₂ x .proj₂ .upper = x .upper - q₁
add-left q₁ q₂ x .proj₂ .l≤q = adjoint₁ {x .lower} {q₁} {q₂} (x .l≤q)
add-left q₁ q₂ x .proj₂ .q≤u = adjoint₂' {q₁} {q₂} {x .upper} (x .q≤u)

galois₁ : ∀ q₁ q₂ x y z →
          z ⊑ (add-right q₁ q₂ x y) → (add-left q₁ q₂ z .proj₁ ⊑ x) ∧ (add-left q₁ q₂ z .proj₂ ⊑ y)
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₁ =
  liftS (adjoint₁ {z .lower} {q₂} {x .lower} (≤-trans ϕ₁ (p⊓q≤p _ _))) ,
  liftS (adjoint₂' {q₂} {x .upper} {z .upper} (≤-trans (p≤p⊔q (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))
galois₁ q₁ q₂ x y z (liftS ϕ₁ , liftS ϕ₂) .proj₂ =
  liftS (adjoint₁ {z .lower} {q₁} {y .lower} (≤-trans ϕ₁ (p⊓q≤q (q₂ + x .lower) _))) ,
  liftS (adjoint₂' {q₁} {y .upper} {z .upper} (≤-trans (p≤q⊔p (q₂ + x .upper) (q₁ + y .upper)) ϕ₂))

galois₂ : ∀ q₁ q₂ x y z →
          (add-left q₁ q₂ z .proj₁ ⊑ x) ∧ (add-left q₁ q₂ z .proj₂ ⊑ y) → z ⊑ (add-right q₁ q₂ x y)
galois₂ q₁ q₂ x y z ((liftS ϕ₁ , liftS ϕ₂) , (liftS ψ₁ , liftS ψ₂)) =
  liftS (⊓-glb (adjoint₂ ϕ₁) (adjoint₂ ψ₁)) ,
  liftS {!!} -- (⊔-lub {!!} {!!})

------------------------------------------------------------------------------
-- Negation

neg-right : ∀ q → Intv q → Intv (- q)
neg-right q x .lower = - (x .upper)
neg-right q x .upper = - (x .lower)
neg-right q x .l≤q = neg-antimono-≤ (x .q≤u)
neg-right q x .q≤u = neg-antimono-≤ (x .l≤q)

neg-left : ∀ q → Intv (- q) → Intv q
neg-left q x .lower = - (x .upper)
neg-left q x .upper = - (x .lower)
neg-left q x .l≤q = ≤-trans (neg-antimono-≤ (x .q≤u)) (≤-reflexive {!!})
neg-left q x .q≤u = ≤-trans (≤-reflexive {!!}) (neg-antimono-≤ (x .l≤q))

------------------------------------------------------------------------------
-- Scaling
module _ (r : ℚ) {{_ : Positive r}} where

  instance r≥0 = pos⇒nonNeg r
  instance r≠0 = pos⇒nonZero r

  scale-right : ∀ q → Intv q → Intv (r * q)
  scale-right q x .lower = r * x .lower
  scale-right q x .upper = r * x .upper
  scale-right q x .l≤q = *-monoˡ-≤-nonNeg r (x .l≤q)
  scale-right q x .q≤u = *-monoˡ-≤-nonNeg r (x .q≤u)

  scale-left : ∀ q → Intv (r * q) → Intv q
  scale-left q x .lower = x .lower ÷ r
  scale-left q x .upper = x .upper ÷ r
  scale-left q x .l≤q = {!!}
  scale-left q x .q≤u = {!!}

  scale-galois₁ : ∀ q x y → y ⊑ scale-right q x → scale-left q y ⊑ x
  scale-galois₁ q x y (liftS ϕ₁ , liftS ϕ₂) =
    (liftS {!!}) ,
    (liftS {!!})


------------------------------------------------------------------------------
-- Lower bounds
data LB (q : ℚ) : Set where
  -∞    : LB q
  [_,_] : ∀ l → l ≤ q → LB q

_≤LB_ : ∀ {q} → LB q → LB q → Prop
-∞         ≤LB _          = ⊤
[ _ , _ ]  ≤LB -∞         = ⊥
[ l₁ , _ ] ≤LB [ l₂ , x ] = LiftS 0ℓ (l₁ ≤ l₂)

≤LB-isPreorder : ∀ {q} → IsPreorder (_≤LB_ {q})
≤LB-isPreorder .refl { -∞} = tt
≤LB-isPreorder .refl {[ l , x ]} = liftS ≤-refl
≤LB-isPreorder .trans { -∞} {_} {_} ϕ ψ = tt
≤LB-isPreorder .trans {[ l , x ]} {[ l₁ , x₁ ]} {[ l₂ , x₂ ]} (liftS ϕ) (liftS ψ) = liftS (≤-trans ϕ ψ)

⊤LB : ∀ {q} → LB q
⊤LB {q} = [ q , ≤-refl ]

⊤LB-isTop : ∀ {q} → IsTop (≤LB-isPreorder {q}) ⊤LB
⊤LB-isTop {q} .IsTop.≤-top { -∞} = tt
⊤LB-isTop {q} .IsTop.≤-top {[ l , x ]} = liftS x

⊥LB : ∀ {q} → LB q
⊥LB = -∞

⊥LB-isBottom : ∀ {q} → IsBottom (≤LB-isPreorder {q}) ⊥LB
⊥LB-isBottom .IsBottom.≤-bottom = tt

_∧LB_ : ∀ {q} → LB q → LB q → LB q
-∞          ∧LB _           = -∞
[ _ , _ ]   ∧LB -∞          = -∞
[ l₁ , ϕ₁ ] ∧LB [ l₂ , ϕ₂ ] = [ l₁ ⊓ l₂ , ≤-trans (p⊓q≤p _ _) ϕ₁ ]

∧LB-isMeet : ∀ {q} → IsMeet (≤LB-isPreorder {q}) _∧LB_
∧LB-isMeet .IsMeet.π₁ { -∞} {_} = tt
∧LB-isMeet .IsMeet.π₁ {[ l₁ , x ]} { -∞} = tt
∧LB-isMeet .IsMeet.π₁ {[ l₁ , x ]} {[ l₂ , x₁ ]} = liftS (p⊓q≤p l₁ l₂)
∧LB-isMeet .IsMeet.π₂ { -∞} {l₂} = tt
∧LB-isMeet .IsMeet.π₂ {[ l , x ]} { -∞} = tt
∧LB-isMeet .IsMeet.π₂ {[ l₁ , _ ]} {[ l₂ , _ ]} = liftS (p⊓q≤q l₁ l₂)
IsMeet.⟨_,_⟩ ∧LB-isMeet { -∞} {y} {z} ϕ ψ = tt
IsMeet.⟨_,_⟩ ∧LB-isMeet {[ l , x ]} {[ l₁ , x₁ ]} {[ l₂ , x₂ ]} (liftS ϕ) (liftS ψ) =
  liftS (⊓-glb ϕ ψ)

_∨LB_ : ∀ {q} → LB q → LB q → LB q
-∞ ∨LB y = y
[ l , x ] ∨LB -∞ = [ l , x ]
[ l₁ , ϕ₁ ] ∨LB [ l₂ , ϕ₂ ] = [ l₁ ⊔ l₂ , ⊔-lub ϕ₁ ϕ₂ ]

∨LB-isJoin : ∀ {q} → IsJoin (≤LB-isPreorder {q}) _∨LB_
∨LB-isJoin .IsJoin.inl { -∞} {_} = tt
∨LB-isJoin .IsJoin.inl {[ _ , _ ]} { -∞} = liftS ≤-refl
∨LB-isJoin .IsJoin.inl {[ l₁ , _ ]} {[ l₂ , _ ]} = liftS (p≤p⊔q l₁ l₂)
∨LB-isJoin .IsJoin.inr { -∞} {_} = ≤LB-isPreorder .refl
∨LB-isJoin .IsJoin.inr {[ l , x ]} { -∞} = tt
∨LB-isJoin .IsJoin.inr {[ l₁ , x ]} {[ l₂ , x₁ ]} = liftS (p≤q⊔p l₁ l₂)
IsJoin.[_,_] ∨LB-isJoin { -∞} {y} {z} ϕ ψ = ψ
IsJoin.[_,_] ∨LB-isJoin {[ l , x ]} { -∞} {z} ϕ ψ = ϕ
IsJoin.[_,_] ∨LB-isJoin {[ l₁ , _ ]} {[ l₂ , _ ]} {[ l , _ ]} (liftS ϕ) (liftS ψ) = liftS (⊔-lub ϕ ψ)

open galois using (_⇒g_; _⊕_)

LowerBounds : ℚ → galois.Obj
LowerBounds q .galois.Obj.carrier .Preorder.Carrier = LB q
LowerBounds q .galois.Obj.carrier .Preorder._≤_ = _≤LB_
LowerBounds q .galois.Obj.carrier .Preorder.≤-isPreorder = ≤LB-isPreorder
LowerBounds q .galois.Obj.meets .MeetSemilattice._∧_ = _∧LB_
LowerBounds q .galois.Obj.meets .MeetSemilattice.⊤ = ⊤LB
LowerBounds q .galois.Obj.meets .MeetSemilattice.∧-isMeet = ∧LB-isMeet
LowerBounds q .galois.Obj.meets .MeetSemilattice.⊤-isTop = ⊤LB-isTop
LowerBounds q .galois.Obj.joins .JoinSemilattice._∨_ = _∨LB_
LowerBounds q .galois.Obj.joins .JoinSemilattice.⊥ = ⊥LB
LowerBounds q .galois.Obj.joins .JoinSemilattice.∨-isJoin = ∨LB-isJoin
LowerBounds q .galois.Obj.joins .JoinSemilattice.⊥-isBottom = ⊥LB-isBottom

------------------------------------------------------------------------------
-- Addition

-- For any monotone function with an adjoint:
--   x ≤ f(y,z) ⇔ g(x,y) ≤ z
-- or with left and right adjoints?
--
-- In general, if we have a lattice with a bottom, then we could
-- construct the lattice of lower bounds, and for any monotone
-- function with an adjoint, we get a
--
--    x ≤ yz ⇔ (x/y) ≤ z
--
-- 0/0 = 0 and x/0 = ∞ ??

add-lb-fwd : ∀ q₁ q₂ → LB q₁ × LB q₂ → LB (q₁ + q₂)
add-lb-fwd q₁ q₂ (-∞ , lb₂) = -∞
add-lb-fwd q₁ q₂ ([ l , _ ] , -∞) = -∞
add-lb-fwd q₁ q₂ ([ l₁ , ϕ₁ ] , [ l₂ , ϕ₂ ]) = [ (q₂ + l₁) ⊓ (q₁ + l₂) , ≤-trans (p⊓q≤q (q₂ + l₁) (q₁ + l₂)) (+-mono-≤ (≤-refl {q₁}) ϕ₂) ]

add-lb-bwd : ∀ q₁ q₂ → LB (q₁ + q₂) → LB q₁ × LB q₂
add-lb-bwd q₁ q₂ -∞ = -∞ , -∞
add-lb-bwd q₁ q₂ [ l , x ] =
  [ l - q₂ , adjoint₁ {l} {q₂} {q₁} (≤-trans x (≤-reflexive (+-comm q₁ q₂))) ] ,
  [ l - q₁ , adjoint₁ {l} {q₁} {q₂} x ]

add-lb : ∀ q₁ q₂ → (LowerBounds q₁ ⊕ LowerBounds q₂) ⇒g LowerBounds (q₁ + q₂)
add-lb q₁ q₂ ._⇒g_.right ._=>_.fun = add-lb-fwd q₁ q₂
add-lb q₁ q₂ ._⇒g_.right ._=>_.mono { -∞ , lb₂} {lb₁' , lb₂'} ϕ = tt
add-lb q₁ q₂ ._⇒g_.right ._=>_.mono {[ l , x ] , -∞} {_ , _} ϕ = tt
add-lb q₁ q₂ ._⇒g_.right ._=>_.mono {[ l₁ , x ] , [ l₂ , x₂ ]} {[ l₁' , x₁ ] , [ l₂' , x₃ ]} (liftS l₁≤l₁' , liftS l₂≤l₂') =
  liftS (⊓-mono-≤ (+-mono-≤ (≤-refl {q₂}) l₁≤l₁') (+-mono-≤ (≤-refl {q₁}) l₂≤l₂'))
add-lb q₁ q₂ ._⇒g_.left ._=>_.fun = add-lb-bwd q₁ q₂
add-lb q₁ q₂ ._⇒g_.left ._=>_.mono { -∞} {l'} ϕ = tt , tt
add-lb q₁ q₂ ._⇒g_.left ._=>_.mono {[ l , x ]} {[ l' , x₁ ]} (liftS l≤l') =
  liftS (+-mono-≤ l≤l' ≤-refl) , liftS (+-mono-≤ l≤l' ≤-refl)
add-lb q₁ q₂ ._⇒g_.left⊣right { -∞ , -∞} { -∞} = (λ _ → tt , tt) , (λ _ → tt)
add-lb q₁ q₂ ._⇒g_.left⊣right { -∞ , -∞} {[ l , x ]} = (λ ()) , (λ ())
add-lb q₁ q₂ ._⇒g_.left⊣right { -∞ , [ l , x ]} { -∞} = (λ _ → tt , tt) , (λ _ → tt)
add-lb q₁ q₂ ._⇒g_.left⊣right { -∞ , [ l , x ]} {[ l₁ , x₁ ]} = (λ ()) , (λ ())
add-lb q₁ q₂ ._⇒g_.left⊣right {[ l , x ] , -∞} { -∞} = (λ _ → tt , tt) , (λ _ → tt)
add-lb q₁ q₂ ._⇒g_.left⊣right {[ l , x ] , -∞} {[ l₁ , x₁ ]} = (λ ()) , (λ ())
add-lb q₁ q₂ ._⇒g_.left⊣right {[ l , x ] , [ l₁ , x₁ ]} { -∞} = (λ _ → tt , tt) , (λ _ → tt)
add-lb q₁ q₂ ._⇒g_.left⊣right {[ l₁ , x₁ ] , [ l₂ , x₂ ]} {[ l , x ]} .proj₁ (liftS ϕ) =
  liftS (adjoint₁ {l} {q₂} {l₁} (≤-trans ϕ (p⊓q≤p (q₂ + l₁) (q₁ + l₂)))) ,
  liftS (adjoint₁ {l} {q₁} {l₂} (≤-trans ϕ (p⊓q≤q (q₂ + l₁) (q₁ + l₂))))
add-lb q₁ q₂ ._⇒g_.left⊣right {[ l₁ , x₁ ] , [ l₂ , x₂ ]} {[ l , x ]} .proj₂ (liftS ϕ₁ , liftS ϕ₂) =
  liftS (⊓-glb (adjoint₂ ϕ₁) (adjoint₂ ϕ₂))

-- For example, if 2 + 5 = 7, the backwards pass starting from 7 gives (2, 5) as the least numbers we could have taken.
-- but if we used 5 as the approximation, then we'd get (0, 3)
--
-- can read this as "if the left the other parts fixed, what is the
-- least number we could use here to get the required output?"

-- if x = 0:
--
-- LowerBounds q ⇒g (if q = 0 then 1 else 1)
--
-- Conditionals?

------------------------------------------------------------------------------

-- FIXME: there is another Galois connection that takes l₁, l₂ ↦ ⊤ and
-- l ↦ ⊥, which is less useful, but shows that there are choices.

------------------------------------------------------------------------------
-- Upper bounds
data UB (q : ℚ) : Set where
  ∞     : UB q
  [_,_] : ∀ u → q ≤ u → UB q

_≤UB_ : ∀ {q} → UB q → UB q → Prop
∞          ≤UB ∞            = ⊤
∞          ≤UB [ u , x ]    = ⊥
[ _ , _ ]   ≤UB ∞           = ⊤
[ u₁ , x₁ ] ≤UB [ u₂ , x₂ ] = LiftS 0ℓ (u₁ ≤ u₂)

≤UB-isPreorder : ∀ {q} → IsPreorder (_≤UB_ {q})
≤UB-isPreorder .refl {∞} = tt
≤UB-isPreorder .refl {[ u , x ]} = liftS ≤-refl
≤UB-isPreorder .trans {∞} {∞} {∞} ϕ₁ ϕ₂ = tt
≤UB-isPreorder .trans {[ u , x ]} {∞} {∞} ϕ₁ ϕ₂ = tt
≤UB-isPreorder .trans {[ u , x ]} {[ u₁ , x₁ ]} {∞} ϕ₁ ϕ₂ = tt
≤UB-isPreorder .trans {[ u , x ]} {[ u₁ , x₁ ]} {[ u₂ , x₂ ]} (liftS ϕ₁) (liftS ϕ₂) = liftS (≤-trans ϕ₁ ϕ₂)

-- ⊤LB : ∀ {q} →

------------------------------------------------------------------------------
-- Intervals that contain a specific point

{-
record Approx (q : ℚ) : Set where
  field
    lb : LB q
    ub : UB q
open Approx

_⊑_ : ∀ {q} → Approx q → Approx q → Prop
a₁ ⊑ a₂ = (a₁ .lb ≤LB a₂ .lb) ∧ (a₂ .ub ≤UB a₁ .ub)

⊑-isPreorder : ∀ {q} → IsPreorder (_⊑_ {q})
⊑-isPreorder .refl = ≤LB-isPreorder .refl , ≤UB-isPreorder .refl
⊑-isPreorder .trans (lb₁ , ub₁) (lb₂ , ub₂) =
  ≤LB-isPreorder .trans lb₁ lb₂ , ≤UB-isPreorder .trans ub₂ ub₁

-- and this is a bounded lattice as well
-}
