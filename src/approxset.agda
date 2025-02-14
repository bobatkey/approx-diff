{-# OPTIONS --postfix-projections --safe --without-K #-}

module approxset where

open import Level
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Nullary
open import preorder using (Preorder)

open import join-semilattice
  renaming (_=>_ to _=>J_; 𝟙 to 𝟙J; _⊕_ to _⊕J_; ⟨_,_⟩ to ⟨_,_⟩J; [_,_] to [_,_]J;
            project₁ to project₁J; project₂ to project₂J;
            L to LJ; _∘_ to _∘J_; id to idJ)
  hiding (initial)
open import meet-semilattice
  renaming (_=>_ to _=>M_; 𝟙 to 𝟙M; _⊕_ to _⊕M_; ⟨_,_⟩ to ⟨_,_⟩M; [_,_] to [_,_]M;
            project₁ to project₁M; project₂ to project₂M;
            inject₁ to inject₁M; inject₂ to inject₂M;
            L to LM; _∘_ to _∘M_; id to idM)
  hiding (terminal)

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
    forder : elem → Preorder
    rorder : elem → Preorder
    fapprox : (x : elem) → MeetSemilattice (forder x)
    rapprox : (x : elem) → JoinSemilattice (rorder x)
open ApproxSet

record _⇒_ (X Y : ApproxSet) : Set where
  field
    func : X .elem → Y .elem
    fwd : (x : X .elem) → X .fapprox x =>M Y .fapprox (func x)
    bwd : (x : X .elem) → Y .rapprox (func x) =>J X .rapprox x
open _⇒_

-- Have a bicartesian closed category... here's the definitions at least:

id : ∀ {X} → X ⇒ X
id .func x = x
id .fwd x = idM
id .bwd x = idJ

_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .fwd x = f .fwd (g .func x) ∘M g .fwd x
(f ∘ g) .bwd x = g .bwd x ∘J f .bwd (g .func x)

infixr 10 _∘_

-- Terminal Object
⊤ₐ : ApproxSet
⊤ₐ .elem = ⊤
⊤ₐ .forder _ = preorder.𝟙
⊤ₐ .rorder _ = preorder.𝟙
⊤ₐ .rapprox tt = 𝟙J
⊤ₐ .fapprox tt = 𝟙M

terminal : ∀ {X} → X ⇒ ⊤ₐ
terminal .func x = tt
terminal .fwd x = meet-semilattice.terminal
terminal .bwd x = join-semilattice.initial

-- Products
_⊗_ : ApproxSet → ApproxSet → ApproxSet
(X ⊗ Y) .elem = X .elem × Y .elem
(X ⊗ Y) .forder (x , y) = X .forder x preorder.× Y .forder y
(X ⊗ Y) .rorder (x , y) = X .rorder x preorder.× Y .rorder y
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
pair f g .bwd x = join-semilattice.[ f .bwd x , g .bwd x ]

-- Initial object
⊥ₐ : ApproxSet
⊥ₐ .elem = ⊥
⊥ₐ .rapprox ()
⊥ₐ .fapprox ()

initial : ∀ {X} → ⊥ₐ ⇒ X
initial .func ()
initial .fwd ()
initial .bwd ()

-- Sums
_+_ : ApproxSet → ApproxSet → ApproxSet
(X + Y) .elem = X .elem ⊎ Y .elem
(X + Y) .forder (inj₁ x) = X .forder x
(X + Y) .forder (inj₂ y) = Y .forder y
(X + Y) .rorder (inj₁ x) = X .rorder x
(X + Y) .rorder (inj₂ y) = Y .rorder y
(X + Y) .rapprox (inj₁ x) = X .rapprox x
(X + Y) .rapprox (inj₂ y) = Y .rapprox y
(X + Y) .fapprox (inj₁ x) = X .fapprox x
(X + Y) .fapprox (inj₂ y) = Y .fapprox y

inl : ∀ {X Y} → X ⇒ (X + Y)
inl .func = inj₁
inl .fwd x = idM
inl .bwd x = idJ

inr : ∀ {X Y} → Y ⇒ (X + Y)
inr .func = inj₂
inr .fwd y = idM
inr .bwd y = idJ

[_,_] : ∀ {W X Y Z} → (W ⊗ X) ⇒ Z → (W ⊗ Y) ⇒ Z → (W ⊗ (X + Y)) ⇒ Z
[ m₁ , m₂ ] .func (w , inj₁ x) = m₁ .func (w , x)
[ m₁ , m₂ ] .func (w , inj₂ y) = m₂ .func (w , y)
[ m₁ , m₂ ] .fwd (w , inj₁ x) = m₁ .fwd (w , x)
[ m₁ , m₂ ] .fwd (w , inj₂ y) = m₂ .fwd (w , y)
[ m₁ , m₂ ] .bwd (w , inj₁ x) = m₁ .bwd (w , x)
[ m₁ , m₂ ] .bwd (w , inj₂ y) = m₂ .bwd (w , y)

-- Functions
_⊸_ : ApproxSet → ApproxSet → ApproxSet
(X ⊸ Y) .elem = X ⇒ Y
(X ⊸ Y) .forder f = Π-preorder (X .elem) λ x → Y .fapprox (f .func x)
(X ⊸ Y) .rorder f = ⨁-preorder (X .elem) λ x → Y .rapprox (f .func x)
(X ⊸ Y) .rapprox f = ⨁ (X .elem) λ x → Y .rapprox (f .func x)
(X ⊸ Y) .fapprox f = Π (X .elem) λ x → Y .fapprox (f .func x)

eval : ∀ {X Y} → ((X ⊸ Y) ⊗ X) ⇒ Y
eval .func (f , x) = f .func x
eval .fwd (f , x) = proj-Π _ _ x ∘M project₁M
eval .bwd (f , x) = ⟨ inj-⨁ _ _ x , f .bwd x ⟩J

lambda : ∀ {X Y Z} → (X ⊗ Y) ⇒ Z → X ⇒ (Y ⊸ Z)
lambda m .func x .func y = m .func (x , y)
lambda m .func x .fwd y = m .fwd (x , y) ∘M inject₂M
lambda m .func x .bwd y = project₂J ∘J m .bwd (x , y)
lambda m .fwd x = lambda-Π _ _ λ y → m .fwd (x , y) ∘M inject₁M
lambda m .bwd x = elim-⨁ _ _ _ λ y → project₁J ∘J m .bwd (x , y)

-- Any old set becomes a “discrete” object
Disc : Set → ApproxSet
Disc A .elem = A
Disc A .forder _ = preorder.𝟙
Disc A .rorder _ = preorder.𝟙
Disc A .rapprox _ = 𝟙J
Disc A .fapprox _ = 𝟙M

Disc-f : ∀ {A B} → (A → B) → Disc A ⇒ Disc B
Disc-f f .func = f
Disc-f f .fwd x = idM
Disc-f f .bwd x = idJ

Disc-const : ∀ {A} → A → ⊤ₐ ⇒ Disc A
Disc-const x .func tt = x
Disc-const x .fwd tt = idM
Disc-const x .bwd tt = idJ

-- Disc also preserves products and preserves and reflects sums, but we only need this
Disc-reflects-products : ∀ {A B} → (Disc A ⊗ Disc B) ⇒ Disc (A × B)
Disc-reflects-products .func ab = ab
Disc-reflects-products .fwd _ = [ idM , idM ]M
Disc-reflects-products .bwd _ = ⟨ idJ , idJ ⟩J

-- Helper for binary predicate over a set
binPred : ∀ {ℓ A} {_∼_ : Rel A ℓ} → Decidable _∼_ → Disc (A × A) ⇒ (⊤ₐ + ⊤ₐ)
binPred _∼_ .func (x , y) with x ∼ y
... | yes _ = inj₁ tt
... | no _ = inj₂ tt
binPred _∼_ .fwd (x , y) with x ∼ y
... | yes _ = idM
... | no _ = idM
binPred _∼_ .bwd (x , y) with x ∼ y
... | yes _ = idJ
... | no _ = idJ

-- Lifting
ℒ : ApproxSet → ApproxSet
ℒ X .elem = X .elem
ℒ X .forder x = preorder.L (X .forder x)
ℒ X .rorder x = preorder.L (X .rorder x)
ℒ X .rapprox x = LJ (X .rapprox x)
ℒ X .fapprox x = LM (X .fapprox x)

ℒ-unit : ∀ {X} → X ⇒ ℒ X
ℒ-unit .func x = x
ℒ-unit .fwd x = meet-semilattice.L-unit
ℒ-unit .bwd x = join-semilattice.L-counit

ℒ-join : ∀ {X} → ℒ (ℒ X) ⇒ ℒ X
ℒ-join .func x = x
ℒ-join .fwd x = meet-semilattice.L-join
ℒ-join .bwd x = join-semilattice.L-dup

ℒ-map : ∀ {X Y} → X ⇒ Y → ℒ X ⇒ ℒ Y
ℒ-map f .func = f .func
ℒ-map f .fwd x = meet-semilattice.L-map (f .fwd x)
ℒ-map f .bwd x = join-semilattice.L-map (f .bwd x)

ℒ-strength : ∀ {X Y} → (X ⊗ ℒ Y) ⇒ ℒ (X ⊗ Y)
ℒ-strength .func xy = xy
ℒ-strength .fwd (x , y) = [ L-unit ∘M inject₁M , meet-semilattice.L-map inject₂M ]M
ℒ-strength .bwd (x , y) = ⟨ project₁J ∘J L-counit , join-semilattice.L-map project₂J ⟩J

{-
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
    ⟨ project₁J , (L-map ⟨ project₁J , ((project₂J ∘ elim-bwd (w , xs)) ∘ project₂J) ⟩J ∘ project₂J) ⟩J ∘ cons-f .bwd (w , x , elim-func (w , xs))

  Ls-elim : (W ⊗ Ls X) ⇒ Y
  Ls-elim .func = elim-func
  Ls-elim .fwd = {!!}
  Ls-elim .bwd = elim-bwd
-}
