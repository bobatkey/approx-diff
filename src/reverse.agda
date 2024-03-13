{-# OPTIONS --postfix-projections --safe --without-K #-}

module reverse where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import join-semilattice
  renaming (_=>_ to _=>J_; 𝟙 to 𝟙J; _⊕_ to _⊕J_; ⟨_,_⟩ to ⟨_,_⟩J;
            project₁ to project₁J; project₂ to project₂J;
            L to LJ)
open import meet-semilattice
  renaming (_=>_ to _=>M_; 𝟙 to 𝟙M; _⊕_ to _⊕M_; ⟨_,_⟩ to ⟨_,_⟩M;
            project₁ to project₁M; project₂ to project₂M;
            inject₁ to inject₁M;
            L to LM; _∘_ to _∘M_; id to idM)

------------------------------------------------------------------------------
--
-- Join Semilattices, and an implementation of reverse-mode automatic
-- approximation.
--
-- TODO:
--   1. Prove the expected categorical properties of JoinSemilattices
--   2. Prove the expected categorical properties of ApproxSets
--   3. Add in the forward approximation pass to ApproxSets
--   4. Show that a typed λ-calculus can be interpreted using ApproxSets
--   5. Show that the forwards and reverse-mode approximations form a Galois
--      connection at first order type.
--
--   6. Show that ApproxSets (with forward approximation) form a
--      Tangent Category
--
--   7. Abstract the development below to any category with biproducts
--      and Set-sigmas
--
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Sets-with-approximations, the central concept

record ApproxSet : Set (suc 0ℓ) where
  field
    elem    : Set
    fapprox : elem → MeetSemilattice
    rapprox : elem → JoinSemilattice
open ApproxSet

record _⇒_ (X Y : ApproxSet) : Set where
  field
    func : X .elem → Y .elem
    fwd : (x : X .elem) → X .fapprox x =>M Y .fapprox (func x)
    bwd : (x : X .elem) → Y .rapprox (func x) =>J X .rapprox x
open _⇒_

-- Have a bicartesian closed category... here's the definitions at least:

-- Any old set becomes a “discrete” object
Disc : Set → ApproxSet
Disc A .elem = A
Disc A .rapprox _ = 𝟙J
Disc A .fapprox _ = 𝟙M

Disc-f : ∀ {A B} → (A → B) → Disc A ⇒ Disc B
Disc-f f .func = f
Disc-f f .fwd x = idM
Disc-f f .bwd x = id

-- Disc preserves sums and products too

-- Terminal Object
⊤ₐ : ApproxSet
⊤ₐ .elem = ⊤
⊤ₐ .rapprox tt = 𝟙J
⊤ₐ .fapprox tt = 𝟙M

-- Products
_⊗_ : ApproxSet → ApproxSet → ApproxSet
(X ⊗ Y) .elem = X .elem × Y .elem
(X ⊗ Y) .fapprox (x , y) = X .fapprox x ⊕M Y .fapprox y
(X ⊗ Y) .rapprox (x , y) = X .rapprox x ⊕J Y .rapprox y

π₁ : ∀ {X Y} → (X ⊗ Y) ⇒ X
π₁ .func = proj₁
π₁ .fwd (x , y) = project₁M
π₁ .bwd (x , y) = inject₁

π₂ : ∀ {X Y} → (X ⊗ Y) ⇒ Y
π₂ .func = proj₂
π₂ .fwd (x , y) = project₂M
π₂ .bwd (x , y) = inject₂

pair : ∀ {X Y Z} → X ⇒ Y → X ⇒ Z → X ⇒ (Y ⊗ Z)
pair f g .func x = f .func x , g .func x
pair f g .fwd x = ⟨ f .fwd x , g .fwd x ⟩M
pair f g .bwd x = [ f .bwd x , g .bwd x ]

-- Sums
_+_ : ApproxSet → ApproxSet → ApproxSet
(X + Y) .elem = X .elem ⊎ Y .elem
(X + Y) .rapprox (inj₁ x) = X .rapprox x
(X + Y) .rapprox (inj₂ y) = Y .rapprox y
(X + Y) .fapprox (inj₁ x) = X .fapprox x
(X + Y) .fapprox (inj₂ y) = Y .fapprox y

inl : ∀ {X Y} → X ⇒ (X + Y)
inl .func = inj₁
inl .fwd x = idM
inl .bwd x = id

inr : ∀ {X Y} → Y ⇒ (X + Y)
inr .func = inj₂
inr .fwd y = idM
inr .bwd y = id

case : ∀ {W X Y Z} → (W ⊗ X) ⇒ Z → (W ⊗ Y) ⇒ Z → (W ⊗ (X + Y)) ⇒ Z
case m₁ m₂ .func (w , inj₁ x) = m₁ .func (w , x)
case m₁ m₂ .func (w , inj₂ y) = m₂ .func (w , y)
case m₁ m₂ .fwd (w , inj₁ x) = m₁ .fwd (w , x)
case m₁ m₂ .fwd (w , inj₂ y) = m₂ .fwd (w , y)
case m₁ m₂ .bwd (w , inj₁ x) = m₁ .bwd (w , x)
case m₁ m₂ .bwd (w , inj₂ y) = m₂ .bwd (w , y)

-- Functions
_⊸_ : ApproxSet → ApproxSet → ApproxSet
(X ⊸ Y) .elem = X ⇒ Y
(X ⊸ Y) .rapprox f = ⨁ (X .elem) λ x → Y .rapprox (f .func x)
(X ⊸ Y) .fapprox f = Π (X .elem) λ x → Y .fapprox (f .func x)

eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
eval .func (f , x) = f .func x
eval {X}{Y} .fwd (f , x) = proj-Π _ _ x ∘M project₁M
eval {X}{Y} .bwd (f , x) =
  ⟨ inj-⨁ (X .elem) (λ x → Y .rapprox (f .func x)) x , f .bwd x ⟩J

lambda : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
lambda m .func x .func y = m .func (x , y)
lambda m .func x .fwd y = m .fwd (x , y) ∘M {!!}
lambda m .func x .bwd y = project₂J ∘ m .bwd (x , y)
lambda m .fwd x = lambda-Π _ _ λ y → m .fwd (x , y) ∘M inject₁M
lambda m .bwd x = elim-⨁ _ _ _ λ y → project₁J ∘ m .bwd (x , y)

-- Lifting
ℒ : ApproxSet → ApproxSet
ℒ X .elem = X .elem
ℒ X .rapprox x = LJ (X .rapprox x)
ℒ X .fapprox x = LM (X .fapprox x)

ℒ-unit : ∀ {X} → X ⇒ ℒ X
ℒ-unit .func x = x
ℒ-unit .fwd x = L-unit
ℒ-unit .bwd x = ⊥-map

ℒ-join : ∀ {X} → ℒ (ℒ X) ⇒ ℒ X
ℒ-join .func x = x
ℒ-join .fwd x = meet-semilattice.L-join
ℒ-join .bwd x = L-dup

-- FIXME: strength, functoriality

-- Approximable lists: μY. 1 + ℒ(X × Y)
--
-- These are lists that can be approximated by forgetting their tails
open import Data.List using (List; []; _∷_)

Ls-rapprox : ∀ X → List (X .elem) → JoinSemilattice
Ls-rapprox X []       = 𝟙J
Ls-rapprox X (x ∷ xs) = LJ (X .rapprox x ⊕J Ls-rapprox X xs)

Ls-fapprox : ∀ X → List (X .elem) → MeetSemilattice
Ls-fapprox X []       = 𝟙M
Ls-fapprox X (x ∷ xs) = LM (X .fapprox x ⊕M Ls-fapprox X xs)

Ls : ApproxSet → ApproxSet
Ls X .elem = List (X .elem)
Ls X .rapprox = Ls-rapprox X
Ls X .fapprox = Ls-fapprox X

nil : ∀ {X} → ⊤ₐ ⇒ Ls X
nil .func tt = []
nil .fwd tt = idM
nil .bwd tt = id

cons : ∀ {X} → ℒ (X ⊗ Ls X) ⇒ Ls X
cons .func (x , xs) = x ∷ xs
cons .fwd (x , xs) = idM
cons .bwd (x , xs) = id

module _ {W X Y} (nil-f : W ⇒ Y) (cons-f : (W ⊗ ℒ (X ⊗ Y)) ⇒ Y) where

  elim-func : W .elem × List (X .elem) → Y .elem
  elim-func (w , [])     = nil-f .func w
  elim-func (w , x ∷ xs) = cons-f .func (w , x , elim-func (w , xs))

  elim-bwd : (x : W .elem × List (X .elem)) → Y .rapprox (elim-func x) =>J (W .rapprox (x .proj₁) ⊕J Ls-rapprox X (x .proj₂))
  elim-bwd (w , []) = inject₁ ∘ nil-f .bwd w
  elim-bwd (w , x ∷ xs) =
    -- FIXME: this is a bit muddled, and probably shouldn't be passing W around
    ⟨ project₁J , (L-func ⟨ project₁J , ((project₂J ∘ elim-bwd (w , xs)) ∘ project₂J) ⟩J ∘ project₂J) ⟩J ∘ cons-f .bwd (w , x , elim-func (w , xs))

  Ls-elim : (W ⊗ Ls X) ⇒ Y
  Ls-elim .func = elim-func
  Ls-elim .fwd = {!!}
  Ls-elim .bwd = elim-bwd
