{-# OPTIONS --postfix-projections --prop --safe #-}

module conjugate where

open import Level
open import prop hiding (_∨_; ⊥; _∧_)
open import prop-setoid using (IsEquivalence)
open import preorder hiding (𝟙)
open import categories
open import meet-semilattice
  using (MeetSemilattice)
  renaming (_=>_ to _=>M_; _⊕_ to _⊕M_)
open import join-semilattice
  using (JoinSemilattice)
  renaming (_=>_ to _=>J_; _≃m_ to _≃J_; _⊕_ to _⊕J_)
open import cmon-enriched

-- Category of Heyting algebras (residuated lattices) and Tarski conjugates between them.
-- FIXME: express using the standard definition of Heyting algebra (although I think this is equivalent).
-- To bounded lattices, Heyting algebras add distributivity and "disjointness separation" (the annihilator map
-- Ann(x) := { z | z # x } is injective). The latter corresponds to Ann(x) being a principal ideal ↓(¬x)
-- where ¬x is the unique pseudocomplement. This seems to be the minimum structure required for conjugates to
-- preserve joins; in particular we don't need double negation.

record Obj : Set (suc 0ℓ) where
  no-eta-equality
  field
    carrier : Preorder
    meets   : MeetSemilattice carrier
    joins   : JoinSemilattice carrier

  open Preorder carrier public
  open MeetSemilattice meets renaming (idem to ∧-idem; interchange to ∧-interchange) public
  open JoinSemilattice joins renaming (idem to ∨-idem; interchange to ∨-interchange) public

  _#_ : carrier .Preorder.Carrier -> carrier .Preorder.Carrier -> Prop
  x # y = (x ∧ y) ≤ ⊥

  #-sym : ∀ {x y} → x # y → y # x
  #-sym = ≤-trans ∧-comm

  ⊥-# : ∀ {x} → ⊥ # x
  ⊥-# = π₁

  -- annihilator map preserves ≤ automatically, and reflects ≤ as an additional assumption
  #-mono : ∀ {x y} → x ≤ y → ∀ z → y # z → x # z
  #-mono x≤y z = ≤-trans (∧-mono x≤y ≤-refl)

  field
    #-reflect : ∀ {x y} → (∀ z → y # z → x # z) → y ≤ x
    ∧-∨-distrib : ∀ x y z → x ∧ (y ∨ z) ≤ (x ∧ y) ∨ (x ∧ z)
    ∨-∧-distrib : ∀ x y z → x ∨ (y ∧ z) ≤ (x ∨ y) ∧ (x ∨ z)

  #-distrib : ∀ {x y z} → x # y → x # z → x # (y ∨ z)
  #-distrib x#y x#z = ≤-trans (∧-∨-distrib _ _ _) (≤-trans (∨-mono x#y x#z) (∨-idem .proj₁))

open Obj

record _⇒c_ (X Y : Obj) : Set where
  no-eta-equality
  open _=>J_
  open preorder._=>_

  private
    module X = Obj X
    module Y = Obj Y
    module XJ = JoinSemilattice (X .joins)
    module YJ = JoinSemilattice (Y .joins)
    module YM = MeetSemilattice (Y .meets)
  field
    -- situation is symmetric, so names here just refer to direction relative to X ⇒c Y
    right : X .carrier preorder.=> Y .carrier
    left : Y .carrier preorder.=> X .carrier
    -- since disjointness determines the order, really just another way of saying that left is adjoint to
    -- (¬ ∘ right) or equivalently that right is adjoint to (¬ ∘ left)
    conjugate : ∀ {x y} → y Y.# right .fun x ⇔ left .fun y X.# x

  right-∨ : X .joins =>J Y .joins
  right-∨ .func = right
  right-∨ .∨-preserving {x} {x'} = Y .#-reflect suffices
    where
    suffices : ∀ y → right .fun (x XJ.∨ x') Y.# y → (right .fun x YJ.∨ right .fun x') Y.# y
    suffices y fx∨x'#y =
      Y.#-sym (Y.#-distrib
        (conjugate .proj₂ (X.#-sym (X.#-mono (inl X) (left .fun y) (X.#-sym gy#x∨x'))))
        (conjugate .proj₂ (X.#-sym (X.#-mono (inr X) (left .fun y) (X.#-sym gy#x∨x')))))
      where
      gy#x∨x' : left .fun y X.# (x XJ.∨ x')
      gy#x∨x' = conjugate .proj₁ (Y.#-sym fx∨x'#y)

  right-∨ .⊥-preserving = Y .#-reflect λ _ _ -> π₁ Y

  left-∨ : Y .joins =>J X .joins
  left-∨ .func = left
  left-∨ .∨-preserving {y} {y'} = X .#-reflect suffices
    where
    suffices : ∀ x → left .fun (y YJ.∨ y') X.# x → (left .fun y XJ.∨ left .fun y') X.# x
    suffices x gy∨y'#x =
      X.#-sym (X.#-distrib
        (X.#-sym (conjugate .proj₁ (Y.#-mono (inl Y) (right .fun x) fx#y∨y')))
        (X.#-sym (conjugate .proj₁ (Y.#-mono (inr Y) (right .fun x) fx#y∨y'))))
      where
      fx#y∨y' : (y YJ.∨ y') Y.# right .fun x
      fx#y∨y' = conjugate .proj₂ gy∨y'#x
  left-∨ .⊥-preserving = X .#-reflect λ _ _ -> π₁ X

open _⇒c_

record _≃c_ {X Y : Obj} (f g : X ⇒c Y) : Prop where
  open preorder._=>_
  open _=>J_

  field
    right-eq : f .right ≃m g .right
    left-eq : f .left ≃m g .left

  right-∨-cong : right-∨ f ≃J right-∨ g
  right-∨-cong ._≃J_.eqfunc = right-eq

  left-∨-cong : left-∨ f ≃J left-∨ g
  left-∨-cong ._≃J_.eqfunc = left-eq

open _≃c_

open IsEquivalence
open preorder using (≃m-isEquivalence)

≃c-isEquivalence : ∀ {X Y} → IsEquivalence (_≃c_ {X} {Y})
≃c-isEquivalence .refl .right-eq = ≃m-isEquivalence .refl
≃c-isEquivalence .refl .left-eq = ≃m-isEquivalence .refl
≃c-isEquivalence .sym e .right-eq = ≃m-isEquivalence .sym (e .right-eq)
≃c-isEquivalence .sym e .left-eq = ≃m-isEquivalence .sym (e .left-eq)
≃c-isEquivalence .trans e₁ e₂ .right-eq = ≃m-isEquivalence .trans (e₁ .right-eq) (e₂ .right-eq)
≃c-isEquivalence .trans e₁ e₂ .left-eq = ≃m-isEquivalence .trans (e₁ .left-eq) (e₂ .left-eq)

idc : (X : Obj) → X ⇒c X
idc X .right = id
idc X .left = id
idc X .conjugate = refl-⇔

_∘c_ : ∀ {X Y Z : Obj} → Y ⇒c Z → X ⇒c Y → X ⇒c Z
(f ∘c g) .right = f .right ∘ g .right
(f ∘c g) .left = g .left ∘ f .left
(f ∘c g) .conjugate = trans-⇔ (f .conjugate) (g .conjugate)

∘c-cong : ∀ {X Y Z}{f₁ f₂ : Y ⇒c Z}{g₁ g₂ : X ⇒c Y} → f₁ ≃c f₂ → g₁ ≃c g₂ → (f₁ ∘c g₁) ≃c (f₂ ∘c g₂)
∘c-cong f₁≈f₂ g₁≈g₂ .right-eq = ∘-cong (f₁≈f₂ .right-eq) (g₁≈g₂ .right-eq)
∘c-cong f₁≈f₂ g₁≈g₂ .left-eq = ∘-cong (g₁≈g₂ .left-eq) (f₁≈f₂ .left-eq)

cat : Category (suc 0ℓ) 0ℓ 0ℓ
cat .Category.obj = Obj
cat .Category._⇒_ = _⇒c_
cat .Category._≈_ = _≃c_
cat .Category.isEquiv = ≃c-isEquivalence
cat .Category.id = idc
cat .Category._∘_ = _∘c_
cat .Category.∘-cong = ∘c-cong
cat .Category.id-left .right-eq = id-left
cat .Category.id-left .left-eq = id-right
cat .Category.id-right .right-eq = id-right
cat .Category.id-right .left-eq = id-left
cat .Category.assoc f g h .right-eq = assoc (f .right) (g .right) (h .right)
cat .Category.assoc f g h .left-eq =
  ≃m-isEquivalence .sym (assoc (h .left) (g .left) (f .left))

-- CMon enrichment
module _ {X Y : Obj} where
  open _=>_
  open preorder._=>_
  open preorder._≃m_

  private
    module YJ = JoinSemilattice (Y .joins)
    module XJ = JoinSemilattice (X .joins)

  εm : X ⇒c Y
  εm .right = join-semilattice.εm {X = X .joins} {Y = Y .joins} ._=>J_.func
  εm .left = join-semilattice.εm {X = Y .joins} {Y = X .joins} ._=>J_.func
  εm .conjugate .proj₁ _ = π₁ X
  εm .conjugate .proj₂ _ = π₂ Y

  _+m_ : X ⇒c Y → X ⇒c Y → X ⇒c Y
  (f +m g) .right = join-semilattice._+m_ (right-∨ f) (right-∨ g) ._=>J_.func
  (f +m g) .left = join-semilattice._+m_ (left-∨ f) (left-∨ g) ._=>J_.func
  (f +m g) .conjugate {x} {y} .proj₁ h =
    #-sym X (#-distrib X
      (#-sym X (conjugate f .proj₁ (≤-trans Y (∧-mono Y (≤-refl Y) (inl Y)) h)))
      (#-sym X (conjugate g .proj₁ (≤-trans Y (∧-mono Y (≤-refl Y) (inr Y)) h))))
  (f +m g) .conjugate {x} {y} .proj₂ h =
    #-distrib Y
      (conjugate f .proj₂ (#-mono X (inl X) x h))
      (conjugate g .proj₂ (#-mono X (inr X) x h))

  +m-cong : ∀ {f₁ f₂ g₁ g₂ : X ⇒c Y} → f₁ ≃c f₂ → g₁ ≃c g₂ → (f₁ +m g₁) ≃c (f₂ +m g₂)
  +m-cong f₁≃f₂ g₁≃g₂ .right-eq = join-semilattice.+m-cong (right-∨-cong f₁≃f₂) (right-∨-cong g₁≃g₂) ._≃J_.eqfunc
  +m-cong f₁≃f₂ g₁≃g₂ .left-eq = join-semilattice.+m-cong (left-∨-cong f₁≃f₂) (left-∨-cong g₁≃g₂) ._≃J_.eqfunc

  +m-comm : ∀ {f g} → (f +m g) ≃c (g +m f)
  +m-comm {f} {g} .right-eq = join-semilattice.+m-comm {f = right-∨ f} {right-∨ g} ._≃J_.eqfunc
  +m-comm {f} {g} .left-eq = join-semilattice.+m-comm {f = left-∨ f} {left-∨ g} ._≃J_.eqfunc

  +m-assoc : ∀ {f g h} → ((f +m g) +m h) ≃c (f +m (g +m h))
  +m-assoc {f} {g} {h} .right-eq = join-semilattice.+m-assoc {f = right-∨ f} {g = right-∨ g} {h = right-∨ h} ._≃J_.eqfunc
  +m-assoc {f} {g} {h} .left-eq = join-semilattice.+m-assoc {f = left-∨ f} {g = left-∨ g} {h = left-∨ h} ._≃J_.eqfunc

  +m-lunit : ∀ {f} → (εm +m f) ≃c f
  +m-lunit {f} .right-eq = join-semilattice.+m-lunit {f = right-∨ f} ._≃J_.eqfunc
  +m-lunit {f} .left-eq = join-semilattice.+m-lunit {f = left-∨ f} ._≃J_.eqfunc

module _ where
  open import commutative-monoid
  open CommutativeMonoid
  open _=>_
  open preorder._≃m_

  cmon-enriched : CMonEnriched cat
  cmon-enriched .CMonEnriched.homCM X Y .ε = εm
  cmon-enriched .CMonEnriched.homCM X Y ._+_ = _+m_
  cmon-enriched .CMonEnriched.homCM X Y .+-cong = +m-cong
  cmon-enriched .CMonEnriched.homCM X Y .+-lunit = +m-lunit
  cmon-enriched .CMonEnriched.homCM X Y .+-assoc = +m-assoc
  cmon-enriched .CMonEnriched.homCM X Y .+-comm = +m-comm
  cmon-enriched .CMonEnriched.comp-bilinear₁ {Z = Z} f₁ f₂ g .right-eq .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear₁ f₁ f₂ g .left-eq .eqfun x = _=>J_.∨-preserving-≃ (left-∨ g)
  cmon-enriched .CMonEnriched.comp-bilinear₂ {Z = Z} f g₁ g₂ .right-eq .eqfun x = _=>J_.∨-preserving-≃ (right-∨ f)
  cmon-enriched .CMonEnriched.comp-bilinear₂ {X = X} f g₁ g₂ .left-eq .eqfun x = X .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ {Z = Z} f .right-eq .eqfun x = Z .≃-refl
  cmon-enriched .CMonEnriched.comp-bilinear-ε₁ f .left-eq .eqfun x = _=>J_.⊥-preserving-≃ (left-∨ f)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {Z = Z} f .right-eq .eqfun x = _=>J_.⊥-preserving-≃ (right-∨ f)
  cmon-enriched .CMonEnriched.comp-bilinear-ε₂ {X = X} f .left-eq .eqfun x = X .≃-refl

-- Terminal object
module _ where
  open IsTerminal
  open HasTerminal
  open preorder._≃m_

  𝟙 : Obj
  𝟙 .carrier = preorder.𝟙
  𝟙 .meets = meet-semilattice.𝟙
  𝟙 .joins = join-semilattice.𝟙
  𝟙 .#-reflect _ = tt
  𝟙 .∧-∨-distrib _ _ _ = tt
  𝟙 .∨-∧-distrib _ _ _ = tt

  to-𝟙 : ∀ X → X ⇒c 𝟙
  to-𝟙 X .right = meet-semilattice.terminal {X = X .meets} ._=>M_.func
  to-𝟙 X .left  = join-semilattice.initial  {X = X .joins} ._=>J_.func
  to-𝟙 X .conjugate .proj₁ _ = π₁ X
  to-𝟙 X .conjugate .proj₂ _ = tt

  terminal : HasTerminal cat
  terminal .witness = 𝟙
  terminal .is-terminal .to-terminal = to-𝟙 _
  terminal .is-terminal .to-terminal-ext {X} f .right-eq .eqfun _ = tt , tt
  terminal .is-terminal .to-terminal-ext {X} f .left-eq .eqfun _ =
    X .≤-bottom ,
    X .#-reflect (λ _ _ → π₁ X)

------------------------------------------------------------------------------
-- Products
module _ where

  open HasProducts
  open import Data.Product using (proj₁; proj₂; _,_)
  open JoinSemilattice
  open MeetSemilattice
  open _=>_
  open preorder._≃m_

  _⊕_ : Obj → Obj → Obj
  (X ⊕ Y) .carrier = X .carrier × Y .carrier
  (X ⊕ Y) .meets = X .meets ⊕M Y .meets
  (X ⊕ Y) .joins = X .joins ⊕J Y .joins
  (X ⊕ Y) .#-reflect h =
    #-reflect X (λ a x'#a → proj₁ (h (a , Y .⊥) (x'#a , π₂ Y))) ,
    #-reflect Y (λ b y'#b → proj₂ (h (X .⊥ , b) (π₂ X , y'#b)))
  (X ⊕ Y) .∧-∨-distrib (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) =
    ∧-∨-distrib X x₁ x₂ x₃ , ∧-∨-distrib Y y₁ y₂ y₃
  (X ⊕ Y) .∨-∧-distrib (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) =
    ∨-∧-distrib X x₁ x₂ x₃ , ∨-∧-distrib Y y₁ y₂ y₃

  products : HasProducts cat
  products .prod = _⊕_
  products .p₁ {X} {Y} .right = join-semilattice.project₁ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₁ {X} {Y} .left = join-semilattice.inject₁ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₁ {X} {Y} .conjugate .proj₁ z#x = z#x , π₁ Y
  products .p₁ .conjugate .proj₂ = proj₁
  products .p₂ {X} {Y} .right = join-semilattice.project₂ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₂ {X} {Y} .left = join-semilattice.inject₂ {X = X .joins} {Y = Y .joins} ._=>J_.func
  products .p₂ {X} {Y} .conjugate .proj₁ z#y = π₁ X , z#y
  products .p₂ .conjugate .proj₂ = proj₂
  products .pair f g .right = join-semilattice.⟨ right-∨ f , right-∨ g ⟩ ._=>J_.func
  products .pair f g .left = join-semilattice.[ left-∨ f , left-∨ g ] ._=>J_.func
  products .pair f g .conjugate .proj₁ = {!   !}
  products .pair f g .conjugate .proj₂ = {!   !}
  products .pair-cong f₁≈f₂ g₁≈g₂ .right-eq =
    join-semilattice.⟨⟩-cong (right-∨-cong f₁≈f₂) (right-∨-cong g₁≈g₂) ._≃J_.eqfunc
  products .pair-cong f₁≈f₂ g₁≈g₂ .left-eq =
    join-semilattice.[]-cong (left-∨-cong f₁≈f₂) (left-∨-cong g₁≈g₂) ._≃J_.eqfunc
  products .pair-p₁ f g .right-eq = join-semilattice.pair-p₁ (right-∨ f) (right-∨ g) ._≃J_.eqfunc
  products .pair-p₁ f g .left-eq = join-semilattice.inj₁-copair (left-∨ f) (left-∨ g) ._≃J_.eqfunc
  products .pair-p₂ f g .right-eq = join-semilattice.pair-p₂ (right-∨ f) (right-∨ g) ._≃J_.eqfunc
  products .pair-p₂ f g .left-eq = join-semilattice.inj₂-copair (left-∨ f) (left-∨ g) ._≃J_.eqfunc
  products .pair-ext f .right-eq = join-semilattice.pair-ext (right-∨ f) ._≃J_.eqfunc
  products .pair-ext f .left-eq = join-semilattice.copair-ext (left-∨ f) ._≃J_.eqfunc

