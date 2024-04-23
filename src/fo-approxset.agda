{-# OPTIONS --postfix-projections --safe --without-K #-}

module fo-approxset where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level
open import basics
open import preorder using (Preorder; L)
open import meet-semilattice
  renaming (_=>_ to _=>M_; _⊕_ to _⊕M_; id to idM; _∘_ to _∘M_; L to LM; [_,_] to [_,_]M; ⟨_,_⟩ to ⟨_,_⟩M;
            project₁ to project₁M; project₂ to project₂M; inject₁ to inject₁M; inject₂ to inject₂M)
open import join-semilattice
  renaming (_=>_ to _=>J_; _⊕_ to _⊕J_; id to idJ; _∘_ to _∘J_; L to LJ; [_,_] to [_,_]J; ⟨_,_⟩ to ⟨_,_⟩J;
            project₁ to project₁J; project₂ to project₂J; inject₁ to inject₁J; inject₂ to inject₂J)

record FOApproxSet : Set (suc 0ℓ) where
  field
    elem    : Set
    order  : elem → Preorder
    fapprox : (x : elem) → MeetSemilattice (order x)
    rapprox : (x : elem) → JoinSemilattice (order x)

open FOApproxSet

record _⇒_ (X Y : FOApproxSet) : Set where
  open _=>M_
  open Preorder

  field
    func : X .elem → Y .elem
    fwd : (x : X .elem) → X .fapprox x =>M Y. fapprox (func x)
    bwd : (x : X .elem) → Y .rapprox (func x) =>J X .rapprox x
    bwd⊣fwd : ∀ (x : X .elem) {x' y'} →
              Y .order (func x) ._≤_ y' (fwd x ._=>M_.func x') ⇔ X .order x ._≤_ (bwd x ._=>J_.func y') x'

open _⇒_

-- Definitions for category

id : ∀ {X} → X ⇒ X
id .func x = x
id .fwd x = idM
id .bwd x = idJ
id .bwd⊣fwd x .proj₁ x'≤ = x'≤
id .bwd⊣fwd x .proj₂ ≤x' = ≤x'

_∘_ : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f ∘ g) .func x = f .func (g .func x)
(f ∘ g) .fwd x = f .fwd (g .func x) ∘M g .fwd x
(f ∘ g) .bwd x = g .bwd x ∘J f .bwd (g .func x)
(f ∘ g) .bwd⊣fwd x .proj₁ z'≤fgx' =
  g .bwd⊣fwd x .proj₁ (f .bwd⊣fwd (g .func x) .proj₁ z'≤fgx')
(f ∘ g) .bwd⊣fwd x .proj₂ gfz'≤x' =
  f .bwd⊣fwd (g .func x) .proj₂ (g .bwd⊣fwd x .proj₂ gfz'≤x')

infixr 10 _∘_

-- Products
module _ where
  open JoinSemilattice

  _⊗_ : FOApproxSet → FOApproxSet → FOApproxSet
  (X ⊗ Y) .elem = X .elem × Y .elem
  (X ⊗ Y) .order (x , y) = X .order x preorder.× Y .order y
  (X ⊗ Y) .fapprox (x , y) = X .fapprox x ⊕M Y .fapprox y
  (X ⊗ Y) .rapprox (x , y) = X .rapprox x ⊕J Y .rapprox y

  π₁ : ∀ {X Y} → (X ⊗ Y) ⇒ X
  π₁ .func = proj₁
  π₁ .fwd (x , y) = project₁M
  π₁ .bwd (x , y) = inject₁J
  π₁ {Y = Y} .bwd⊣fwd (x , y) .proj₁ y'≤ = y'≤ , IsBottom.≤-bottom (Y .rapprox y .⊥-isBottom)
  π₁ .bwd⊣fwd (x , y) .proj₂ = proj₁

  π₂ : ∀ {X Y} → (X ⊗ Y) ⇒ Y
  π₂ .func = proj₂
  π₂ .fwd (x , y) = project₂M
  π₂ .bwd (x , y) = inject₂J
  π₂ {X} .bwd⊣fwd (x , y) .proj₁ ≤x' = IsBottom.≤-bottom (X .rapprox x .⊥-isBottom) , ≤x'
  π₂ .bwd⊣fwd (x , y) .proj₂ = proj₂

  pair : ∀ {X Y Z} → X ⇒ Y → X ⇒ Z → X ⇒ (Y ⊗ Z)
  pair f g .func x = f .func x , g .func x
  pair f g .fwd x = ⟨ f .fwd x , g .fwd x ⟩M
  pair f g .bwd x = [ f .bwd x , g .bwd x ]J
  pair {X} f g .bwd⊣fwd x .proj₁ (y'≤ , z'≤) =
    [ f .bwd⊣fwd x .proj₁ y'≤ , g .bwd⊣fwd x .proj₁ z'≤ ]
    where open IsJoin (X .rapprox x .∨-isJoin)
  pair {X} f g .bwd⊣fwd x .proj₂ ≤x' .proj₁ =
    f .bwd⊣fwd x .proj₂ (≤-trans (X .order x) inl ≤x')
    where open IsJoin (X .rapprox x .∨-isJoin)
  pair {X}{Z = Z} f g .bwd⊣fwd x {y' = y' , z'} .proj₂ ≤x' .proj₂ =
    g .bwd⊣fwd x .proj₂ (≤-trans (X .order x) inr ≤x')
    where open IsJoin (X .rapprox x .∨-isJoin)

-- Sums
module _ where
  _+_ : FOApproxSet → FOApproxSet → FOApproxSet
  (X + Y) .elem = X .elem ⊎ Y .elem
  (X + Y) .order (inj₁ x) = X .order x
  (X + Y) .order (inj₂ y) = Y .order y
  (X + Y) .rapprox (inj₁ x) = X .rapprox x
  (X + Y) .rapprox (inj₂ y) = Y .rapprox y
  (X + Y) .fapprox (inj₁ x) = X .fapprox x
  (X + Y) .fapprox (inj₂ y) = Y .fapprox y

  inl : ∀ {X Y} → X ⇒ (X + Y)
  inl .func = inj₁
  inl .fwd x = idM
  inl .bwd x = idJ
  inl .bwd⊣fwd x .proj₁ x'≤ = x'≤
  inl .bwd⊣fwd x .proj₂ ≤x' = ≤x'

  inr : ∀ {X Y} → Y ⇒ (X + Y)
  inr .func = inj₂
  inr .fwd y = idM
  inr .bwd y = idJ
  inr .bwd⊣fwd y .proj₁ y'≤ = y'≤
  inr .bwd⊣fwd y .proj₂ ≤y' = ≤y'

  [_,_] : ∀ {W X Y Z} → (W ⊗ X) ⇒ Z → (W ⊗ Y) ⇒ Z → (W ⊗ (X + Y)) ⇒ Z
  [ m₁ , m₂ ] .func (w , inj₁ x) = m₁ .func (w , x)
  [ m₁ , m₂ ] .func (w , inj₂ y) = m₂ .func (w , y)
  [ m₁ , m₂ ] .fwd (w , inj₁ x) = m₁ .fwd (w , x)
  [ m₁ , m₂ ] .fwd (w , inj₂ y) = m₂ .fwd (w , y)
  [ m₁ , m₂ ] .bwd (w , inj₁ x) = m₁ .bwd (w , x)
  [ m₁ , m₂ ] .bwd (w , inj₂ y) = m₂ .bwd (w , y)
  [ m₁ , m₂ ] .bwd⊣fwd (w , inj₁ x) = m₁ .bwd⊣fwd (w , x)
  [ m₁ , m₂ ] .bwd⊣fwd (w , inj₂ y) = m₂ .bwd⊣fwd (w , y)

-- Function spaces will be provided by presheaf category

-- Lifting
module _ where
  open JoinSemilattice
  open preorder.LCarrier

  ℒ : FOApproxSet → FOApproxSet
  ℒ X .elem = X .elem
  ℒ X .order x = L (X .order x)
  ℒ X .fapprox x = LM (X .fapprox x)
  ℒ X .rapprox x = LJ (X .rapprox x)

  ℒ-unit : ∀ {X} → X ⇒ ℒ X
  ℒ-unit .func x = x
  ℒ-unit .fwd x = meet-semilattice.L-unit
  ℒ-unit .bwd x = join-semilattice.L-counit
  ℒ-unit {X} .bwd⊣fwd x {y' = bottom} .proj₁ _ = IsBottom.≤-bottom (X .rapprox x .⊥-isBottom)
  ℒ-unit .bwd⊣fwd x {y' = < x' >} .proj₁ x'≤ = x'≤
  ℒ-unit .bwd⊣fwd x {y' = bottom} .proj₂ _ = tt
  ℒ-unit .bwd⊣fwd x {y' = < x' >} .proj₂ ≤x' = ≤x'

  ℒ-join : ∀ {X} → ℒ (ℒ X) ⇒ ℒ X
  ℒ-join .func x = x
  ℒ-join .fwd x = meet-semilattice.L-join
  ℒ-join .bwd x = join-semilattice.L-dup
  ℒ-join .bwd⊣fwd x {bottom} {bottom} .proj₁ _ = tt
  ℒ-join .bwd⊣fwd x {bottom} {< x₂ >} .proj₁ ()
  ℒ-join .bwd⊣fwd x {< bottom >} {bottom} .proj₁ _ = tt
  ℒ-join .bwd⊣fwd x {< bottom >} {< x₂ >} .proj₁ ()
  ℒ-join .bwd⊣fwd x {< < x₁ > >} {bottom} .proj₁ _ = tt
  ℒ-join .bwd⊣fwd x {< < x₁ > >} {< x₂ >} .proj₁ x₂≤ = x₂≤
  ℒ-join .bwd⊣fwd x {bottom} {bottom} .proj₂ _ = tt
  ℒ-join .bwd⊣fwd x {bottom} {< x₂ >} .proj₂ ()
  ℒ-join .bwd⊣fwd x {< bottom >} {bottom} .proj₂ _ = tt
  ℒ-join .bwd⊣fwd x {< bottom >} {< x₂ >} .proj₂ ()
  ℒ-join .bwd⊣fwd x {< < x₁ > >} {bottom} .proj₂ _ = tt
  ℒ-join .bwd⊣fwd x {< < x₁ > >} {< x₂ >} .proj₂ ≤x₁ = ≤x₁

  ℒ-func : ∀ {X Y} → X ⇒ Y → ℒ X ⇒ ℒ Y
  ℒ-func f .func = f .func
  ℒ-func f .fwd x = meet-semilattice.L-func (f .fwd x)
  ℒ-func f .bwd x = join-semilattice.L-func (f .bwd x)
  ℒ-func f .bwd⊣fwd x {bottom} {bottom} .proj₁ _ = tt
  ℒ-func f .bwd⊣fwd x {bottom} {< y' >} .proj₁ ()
  ℒ-func f .bwd⊣fwd x {< x' >} {bottom} .proj₁ _ = tt
  ℒ-func f .bwd⊣fwd x {< x' >} {< y' >} .proj₁ = f .bwd⊣fwd x .proj₁
  ℒ-func f .bwd⊣fwd x {bottom} {bottom} .proj₂ _ = tt
  ℒ-func f .bwd⊣fwd x {bottom} {< x₁ >} .proj₂ ()
  ℒ-func f .bwd⊣fwd x {< x₁ >} {bottom} .proj₂ _ = tt
  ℒ-func f .bwd⊣fwd x {< x₁ >} {< x₂ >} .proj₂ = f .bwd⊣fwd x .proj₂

  -- TODO: strength
