{-# OPTIONS --postfix-projections --safe --without-K #-}

module reverse where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import join-semilattice


------------------------------------------------------------------------------
--
-- Join Semilattices, and an implementation of reverse-mode automatic
-- approximation.
--
-- TODO:
--   1. Add join-preserving to the definition of JoinSemilattice morphism
--   2. Prove the expected categorical properties of JoinSemilattices
--   3. Prove the expected categorical properties of ApproxSets
--   4. Add in the forward approximation pass to ApproxSets
--   5. Show that a typed λ-calculus can be interpreted using ApproxSets
--   6. Show that the forwards and reverse-mode approximations form a Galois
--      connection at first order type.
--
--   7. Show that ApproxSets (with forward approximation) form a
--      Tangent Category
--
--   8. Abstract the development below to any category with biproducts
--      and Set-sigmas
--
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Sets-with-approximations, the central concept

record ApproxSet : Set (suc 0ℓ) where
  field
    elem   : Set
    approx : elem → JoinSemilattice
    -- FIXME: do the forward approximation preorder at the same time
    -- is there a relationship between the two that always holds?
open ApproxSet

record _⇒_ (X Y : ApproxSet) : Set where
  field
    fwd : X .elem → Y .elem
    bwd : (x : X .elem) → Y .approx (fwd x) => X .approx x
open _⇒_

-- Have a bicartesian closed category... here's the definitions at least:

-- Any old set becomes a “discrete” object
Disc : Set → ApproxSet
Disc A .elem = A
Disc A .approx _ = 𝟙

Disc-f : ∀ {A B} → (A → B) → Disc A ⇒ Disc B
Disc-f f .fwd = f
Disc-f f .bwd x = id

-- Disc preserves sums and products too

-- Terminal Object
⊤ₐ : ApproxSet
⊤ₐ .elem = ⊤
⊤ₐ .approx tt = 𝟙

-- Products
_⊗_ : ApproxSet → ApproxSet → ApproxSet
(X ⊗ Y) .elem = X .elem × Y .elem
(X ⊗ Y) .approx (x , y) = X .approx x ⊕ Y .approx y

π₁ : ∀ {X Y} → (X ⊗ Y) ⇒ X
π₁ .fwd = proj₁
π₁ .bwd (x , y) = inject₁

π₂ : ∀ {X Y} → (X ⊗ Y) ⇒ Y
π₂ .fwd = proj₂
π₂ .bwd (x , y) = inject₂

pair : ∀ {X Y Z} → (X ⇒ Y) → (X ⇒ Z) → X ⇒ (Y ⊗ Z)
pair f g .fwd x = f .fwd x , g .fwd x
pair f g .bwd x = [ f .bwd x , g .bwd x ]

-- Sums
_+_ : ApproxSet → ApproxSet → ApproxSet
(X + Y) .elem = X .elem ⊎ Y .elem
(X + Y) .approx (inj₁ x) = X .approx x
(X + Y) .approx (inj₂ y) = Y .approx y

inl : ∀ {X Y} → X ⇒ (X + Y)
inl .fwd = inj₁
inl .bwd x = id

inr : ∀ {X Y} → Y ⇒ (X + Y)
inr .fwd = inj₂
inr .bwd y = id

case : ∀ {W X Y Z} → (W ⊗ X) ⇒ Z → (W ⊗ Y) ⇒ Z → (W ⊗ (X + Y)) ⇒ Z
case m₁ m₂ .fwd (w , inj₁ x) = m₁ .fwd (w , x)
case m₁ m₂ .fwd (w , inj₂ y) = m₂ .fwd (w , y)
case m₁ m₂ .bwd (w , inj₁ x) = m₁ .bwd (w , x)
case m₁ m₂ .bwd (w , inj₂ y) = m₂ .bwd (w , y)

-- Functions
_⊸_ : ApproxSet → ApproxSet → ApproxSet
(X ⊸ Y) .elem = X ⇒ Y
(X ⊸ Y) .approx f = ⨁ (X .elem) λ x → Y .approx (f .fwd x)

eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
eval .fwd (f , x) = f .fwd x
eval {X}{Y} .bwd (f , x) =
  ⟨ inj-⨁ (X .elem) (λ x → Y .approx (f .fwd x)) x , f .bwd x ⟩

lambda : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
lambda m .fwd x .fwd y = m .fwd (x , y)
lambda m .fwd x .bwd y = project₂ ∘ m .bwd (x , y)
lambda m .bwd x = elim-⨁ _ _ _ λ y → project₁ ∘ m .bwd (x , y)

-- Lifting
ℒ : ApproxSet → ApproxSet
ℒ X .elem = X .elem
ℒ X .approx x = L (X .approx x)

ℒ-unit : ∀ {X} → X ⇒ ℒ X
ℒ-unit .fwd x = x
ℒ-unit .bwd x = ⊥-map

ℒ-join : ∀ {X} → ℒ (ℒ X) ⇒ ℒ X
ℒ-join .fwd x = x
ℒ-join .bwd x = L-dup

-- FIXME: strength, functoriality

-- Approximable lists: μY. 1 + ℒ(X × Y)
--
-- These are lists that can be approximated by forgetting their tails
open import Data.List using (List; []; _∷_)

Ls-approx : ∀ X → List (X .elem) → JoinSemilattice
Ls-approx X [] = 𝟙
Ls-approx X (x ∷ xs) = L (X .approx x ⊕ Ls-approx X xs)

Ls : ApproxSet → ApproxSet
Ls X .elem = List (X .elem)
Ls X .approx = Ls-approx X

nil : ∀ {X} → ⊤ₐ ⇒ Ls X
nil .fwd tt = []
nil .bwd tt = id

cons : ∀ {X} → ℒ (X ⊗ Ls X) ⇒ Ls X
cons .fwd (x , xs) = x ∷ xs
cons .bwd (x , xs) = id

module _ {W X Y} (nil-f : W ⇒ Y) (cons-f : (W ⊗ ℒ (X ⊗ Y)) ⇒ Y) where

  elim-fwd : W .elem × List (X .elem) → Y .elem
  elim-fwd (w , [])     = nil-f .fwd w
  elim-fwd (w , x ∷ xs) = cons-f .fwd (w , x , elim-fwd (w , xs))

  elim-bwd : (x : W .elem × List (X .elem)) → Y .approx (elim-fwd x) => (W .approx (x .proj₁) ⊕ Ls-approx X (x .proj₂))
  elim-bwd (w , []) = inject₁ ∘ nil-f .bwd w
  elim-bwd (w , x ∷ xs) =
    -- FIXME: this is a bit muddled, and probably shouldn't be passing W around
    ⟨ project₁ , (L-func ⟨ project₁ , ((project₂ ∘ elim-bwd (w , xs)) ∘ project₂) ⟩ ∘ project₂) ⟩ ∘ cons-f .bwd (w , x , elim-fwd (w , xs))

  Ls-elim : (W ⊗ Ls X) ⇒ Y
  Ls-elim .fwd = elim-fwd
  Ls-elim .bwd = elim-bwd
