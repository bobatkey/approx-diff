{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The μ-carrier of a polynomial coincides with its constant-free
-- form at the environment extended by the constants: a constant and a
-- variable bound to an equal environment entry contribute the same carrier
-- data, so the two W-types agree up to renaming of tree constructors.
-- Decorations are passed explicitly: the T₂-side decoration is consumed at
-- shifted positions, so it cannot be inferred by pattern unification.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
import Data.Fin as Fin
open Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import prop using () renaming (_,_ to _,ₚ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; subst-subst-sym; subst-sym-subst)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; subst to ≡-subst)
open import categories using (Category; HasTerminal; HasProducts)
open import prop-setoid using (Setoid)
open import indexed-family using (_≃f_)
import polynomial-functor
import fam-mu-types.carrier

module gf-preserves-mu.constant-free {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (P : HasProducts 𝒞) where

open fam-mu-types.carrier os es T P
open polynomial-functor using (#c; constant-free; constant-free-go; consts; _++e_)

-- Fixed data for one instance of the lemma: an environment and a constant
-- block over the Fam category.
module ConstantFree {n k : ℕ} (δ : Fin n → Obj) (cs : Fin k → Obj) where

  δ⁺ : Fin (n +ℕ k) → Obj
  δ⁺ = δ ++e cs

  module T₁ = Tree δ
  module T₂ = Tree δ⁺

  -- Relate source references (environment positions or sorts) to target ones,
  -- with their decorations: environment positions inject on the left; sorts
  -- relate recursively, with the constant block of the source polynomial
  -- pointing at the constant entries of the extended environment.
  mutual
    data RefRel : (r₁ : Fin n ⊎ Sort n) (r₂ : Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                  T₁.DecoAssign r₁ → T₂.DecoAssign r₂ → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      env : ∀ {p} → RefRel (inj₁ p) (inj₁ (p ↑ˡ k)) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortRel s₁ s₂ e₁ e₂ → RefRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortRel : (s₁ : Sort n) (s₂ : Sort (n +ℕ k)) →
                   T₁.Deco s₁ → T₂.Deco s₂ → Set (o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es) where
      mk : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
           (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           SortRel (mkSort ∣ Q ∣ ρ₁) (mkSort ∣ constant-free-go Q ι ∣ ρ₂)
                   (T₁.mkDeco Q d₁) (T₂.mkDeco (constant-free-go Q ι) d₂)

  -- The forward tree map: rename constant leaves to their variable images.
  mutual
    wfwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
           (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           T₁.W ∣ Q ∣ ρ₁ → T₂.W ∣ constant-free-go Q ι ∣ ρ₂
    wfwd {j} Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (T₁.sup x) =
      T₂.sup (shape-fwd Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
                (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
                (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x)

    -- The extended environments stay related when entering a binder.
    extend-vars : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
                  (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                  (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i)) →
                  (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                  (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                  (∀ c → cs (ι c) ≡ consts Q c) →
                  ∀ i → RefRel (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁)) i)
                               (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)) (i ↑ˡ k))
                               (T₁.deco-ext Q d₁ i)
                               (T₂.deco-ext (constant-free-go Q ι) d₂ (i ↑ˡ k))
    extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok Fin.zero    = srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)
    extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (Fin.suc i) = vars i

    extend-fresh : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
                   (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)) →
                   (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                   ∀ (c : Fin k) → extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)) (suc j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)
    extend-fresh Q ρ₁ ι ρ₂ fresh c = fresh c

    shape-fwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i)) →
                (∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                (∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                (∀ c → cs (ι c) ≡ consts Q c) →
                T₁.⟦ ∣ Q ∣ ⟧shape η₁ → T₂.⟦ ∣ constant-free-go Q ι ∣ ⟧shape η₂
    shape-fwd {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok x =
      ≡-subst T₂.El (≡-sym (fresh (ι Fin.zero)))
        (≡-subst (λ B → B .idx .Carrier)
          (≡-sym (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))) x)
    shape-fwd (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok x = el-fwd (vars i) x
    shape-fwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₁ x) =
      inj₁ (shape-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
              (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x)
    shape-fwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₂ y) =
      inj₂ (shape-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
              (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y)
    shape-fwd (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok (x , y) =
      shape-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      , shape-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fwd (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok x = wfwd Q' η₁ ι η₂ d₁ d₂ vars fresh csok x

    -- References transport elements.
    el-fwd : ∀ {r₁ r₂ dr₁ dr₂} → RefRel r₁ r₂ dr₁ dr₂ → T₁.El r₁ → T₂.El r₂
    el-fwd (env {p}) x =
      ≡-subst (λ B → B .idx .Carrier) (≡-sym (cong [ δ , cs ]′ (splitAt-↑ˡ n p k))) x
    el-fwd (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) x = wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x

  -- Casts commute with the setoid equalities, by identity elimination.
  private
    cast-≈ : ∀ {B B' : Obj} (e : B ≡ B') {x y : B .idx .Carrier} →
             B .idx ._≈s_ x y →
             B' .idx ._≈s_ (≡-subst (λ Z → Z .idx .Carrier) e x) (≡-subst (λ Z → Z .idx .Carrier) e y)
    cast-≈ ≡-refl p = p

    el-cast-≈ : ∀ {r r' : Fin (n +ℕ k) ⊎ Sort (n +ℕ k)} (e : r ≡ r') {x y : T₂.El r} →
                T₂.elEq r x y → T₂.elEq r' (≡-subst T₂.El e x) (≡-subst T₂.El e y)
    el-cast-≈ ≡-refl p = p

  -- The forward map preserves bisimilarity.
  mutual
    w≈-fwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
             (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
             (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
             (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
             (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
             (csok : ∀ c → cs (ι c) ≡ consts Q c) →
             {x y : T₁.W ∣ Q ∣ ρ₁} → T₁.W-≈ x y →
             T₂.W-≈ (wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x) (wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y)
    w≈-fwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {T₁.sup x} {T₁.sup y} p =
      shape≈-fwd Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok p

    shape≈-fwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                 (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                 (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
                 (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                 (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                 (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                 {x y : T₁.⟦ ∣ Q ∣ ⟧shape η₁} → T₁.shape≈ ∣ Q ∣ η₁ x y →
                 T₂.shape≈ ∣ constant-free-go Q ι ∣ η₂ (shape-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok x) (shape-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok y)
    shape≈-fwd {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok p =
      el-cast-≈ (≡-sym (fresh (ι Fin.zero)))
        (cast-≈ (≡-sym (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))) p)
    shape≈-fwd (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok p = elEq-fwd (vars i) p
    shape≈-fwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₁ _} {inj₁ _} p =
      shape≈-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
    shape≈-fwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₂ _} {inj₂ _} p =
      shape≈-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) p
    shape≈-fwd (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-fwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
      ,ₚ shape≈-fwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) q
    shape≈-fwd (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} p =
      w≈-fwd Q' η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} p

    elEq-fwd : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) {x y : T₁.El r₁} →
               T₁.elEq r₁ x y → T₂.elEq r₂ (el-fwd r x) (el-fwd r y)
    elEq-fwd (env {p}) q =
      cast-≈ (≡-sym (cong [ δ , cs ]′ (splitAt-↑ˡ n p k))) q
    elEq-fwd (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) {x} {y} q =
      w≈-fwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {x} {y} q

  -- The backward tree map: rename the fresh variable leaves back to constants.
  mutual
    wbwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
           (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i)) →
           (∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
           (∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (∀ c → cs (ι c) ≡ consts Q c) →
           T₂.W ∣ constant-free-go Q ι ∣ ρ₂ → T₁.W ∣ Q ∣ ρ₁
    wbwd {j} Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (T₂.sup x) =
      T₁.sup (shape-bwd Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
                (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
                (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x)

    shape-bwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i)) →
                (∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                (∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                (∀ c → cs (ι c) ≡ consts Q c) →
                T₂.⟦ ∣ constant-free-go Q ι ∣ ⟧shape η₂ → T₁.⟦ ∣ Q ∣ ⟧shape η₁
    shape-bwd {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok x =
      ≡-subst (λ B → B .idx .Carrier)
        (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))
        (≡-subst T₂.El (fresh (ι Fin.zero)) x)
    shape-bwd (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok x = el-bwd (vars i) x
    shape-bwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₁ x) =
      inj₁ (shape-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
              (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x)
    shape-bwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₂ y) =
      inj₂ (shape-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
              (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y)
    shape-bwd (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok (x , y) =
      shape-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      , shape-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bwd (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok x = wbwd Q' η₁ ι η₂ d₁ d₂ vars fresh csok x

    el-bwd : ∀ {r₁ r₂ dr₁ dr₂} → RefRel r₁ r₂ dr₁ dr₂ → T₂.El r₂ → T₁.El r₁
    el-bwd (env {p}) x =
      ≡-subst (λ B → B .idx .Carrier) (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)) x
    el-bwd (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) x = wbwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x

  -- Equal elements are setoid-equal.
  private
    obj-≡-to-≈ : ∀ {B : Obj} {x y : B .idx .Carrier} → x ≡ y → B .idx ._≈s_ x y
    obj-≡-to-≈ {B} {x} ≡-refl = B .idx .isEquivalence .refl

    ≡-to-≈₁ : ∀ {r} {x y : T₁.El r} → x ≡ y → T₁.elEq r x y
    ≡-to-≈₁ {r} {x} ≡-refl = T₁.elEq-refl r x

    ≡-to-≈₂ : ∀ {r} {x y : T₂.El r} → x ≡ y → T₂.elEq r x y
    ≡-to-≈₂ {r} {x} ≡-refl = T₂.elEq-refl r x

    Car : Obj → Set os
    Car B = B .idx .Carrier

  -- Round trips: the two maps are mutually inverse up to bisimilarity.
  mutual
    w-fb : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
           (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
           (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
           (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (csok : ∀ c → cs (ι c) ≡ consts Q c) →
           (x : T₁.W ∣ Q ∣ ρ₁) →
           T₁.W-≈ (wbwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x)) x
    w-fb Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (T₁.sup x) =
      shape-fb Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x

    shape-fb : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
               (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
               (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
               (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
               (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
               (csok : ∀ c → cs (ι c) ≡ consts Q c) →
               (x : T₁.⟦ ∣ Q ∣ ⟧shape η₁) →
               T₁.shape≈ ∣ Q ∣ η₁ (shape-bwd Q η₁ ι η₂ d₁ d₂ vars fresh csok (shape-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok x)) x
    shape-fb {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok x =
      obj-≡-to-≈ {B = A} (≡-trans (cong (≡-subst Car E) (subst-subst-sym {P = T₂.El} F)) (subst-subst-sym {P = Car} E))
      where
        E = ≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)
        F = fresh (ι Fin.zero)
    shape-fb (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok x = el-fb (vars i) x
    shape-fb (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₁ x) =
      shape-fb Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
    shape-fb (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₂ y) =
      shape-fb R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fb (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok (x , y) =
      shape-fb Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      ,ₚ shape-fb R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-fb (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok x = w-fb Q' η₁ ι η₂ d₁ d₂ vars fresh csok x

    el-fb : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) (x : T₁.El r₁) →
            T₁.elEq r₁ (el-bwd r (el-fwd r x)) x
    el-fb (env {p}) x = obj-≡-to-≈ {B = δ p} (subst-subst-sym {P = Car} (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)))
    el-fb (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) x = w-fb Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x

  mutual
    w-bf : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
           (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
           (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
           (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
           (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
           (csok : ∀ c → cs (ι c) ≡ consts Q c) →
           (y : T₂.W ∣ constant-free-go Q ι ∣ ρ₂) →
           T₂.W-≈ (wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (wbwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y)) y
    w-bf Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (T₂.sup y) =
      shape-bf Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok y

    shape-bf : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
               (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
               (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
               (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
               (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
               (csok : ∀ c → cs (ι c) ≡ consts Q c) →
               (y : T₂.⟦ ∣ constant-free-go Q ι ∣ ⟧shape η₂) →
               T₂.shape≈ ∣ constant-free-go Q ι ∣ η₂ (shape-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok (shape-bwd Q η₁ ι η₂ d₁ d₂ vars fresh csok y)) y
    shape-bf {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok y =
      ≡-to-≈₂ {r = η₂ (jv ↑ʳ ι Fin.zero)} (≡-trans (cong (≡-subst T₂.El (≡-sym F)) (subst-sym-subst {P = Car} E)) (subst-sym-subst {P = T₂.El} F))
      where
        E = ≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)
        F = fresh (ι Fin.zero)
    shape-bf (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok y = el-bf (vars i) y
    shape-bf (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₁ y) =
      shape-bf Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) y
    shape-bf (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₂ y) =
      shape-bf R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bf (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok (x , y) =
      shape-bf Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
      ,ₚ shape-bf R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    shape-bf (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok y = w-bf Q' η₁ ι η₂ d₁ d₂ vars fresh csok y

    el-bf : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) (y : T₂.El r₂) →
            T₂.elEq r₂ (el-fwd r (el-bwd r y)) y
    el-bf (env {p}) y = obj-≡-to-≈ {B = δ⁺ (p ↑ˡ k)} (subst-sym-subst {P = Car} (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)))
    el-bf (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) y = w-bf Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y

  -- The backward map preserves bisimilarity.
  mutual
    w≈-bwd : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
             (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
             (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
             (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
             (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
             (csok : ∀ c → cs (ι c) ≡ consts Q c) →
             {x y : T₂.W ∣ constant-free-go Q ι ∣ ρ₂} → T₂.W-≈ x y →
             T₁.W-≈ (wbwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x) (wbwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y)
    w≈-bwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {T₂.sup x} {T₂.sup y} p =
      shape≈-bwd Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok p

    shape≈-bwd : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                 (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                 (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
                 (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                 (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                 (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                 {x y : T₂.⟦ ∣ constant-free-go Q ι ∣ ⟧shape η₂} → T₂.shape≈ ∣ constant-free-go Q ι ∣ η₂ x y →
                 T₁.shape≈ ∣ Q ∣ η₁ (shape-bwd Q η₁ ι η₂ d₁ d₂ vars fresh csok x) (shape-bwd Q η₁ ι η₂ d₁ d₂ vars fresh csok y)
    shape≈-bwd {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok p =
      cast-≈ (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero))
        (el-cast-≈ (fresh (ι Fin.zero)) p)
    shape≈-bwd (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok p = elEq-bwd (vars i) p
    shape≈-bwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₁ _} {inj₁ _} p =
      shape≈-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
    shape≈-bwd (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₂ _} {inj₂ _} p =
      shape≈-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) p
    shape≈-bwd (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-bwd Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) p
      ,ₚ shape≈-bwd R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) q
    shape≈-bwd (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} p =
      w≈-bwd Q' η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} p

    elEq-bwd : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) {x y : T₂.El r₂} →
               T₂.elEq r₂ x y → T₁.elEq r₁ (el-bwd r x) (el-bwd r y)
    elEq-bwd (env {p}) q =
      cast-≈ (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)) q
    elEq-bwd (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) {x} {y} q =
      w≈-bwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {x} {y} q

  -- The fibres of matched trees are equal objects.
  private
    fib-el-castF : ∀ {r q} (F : r ≡ inj₁ q) {dr : T₂.DecoAssign r} (z : T₂.El (inj₁ q)) →
                   T₂.fib-el r dr (≡-subst T₂.El (≡-sym F) z) ≡ T₂.fib-el (inj₁ q) (lift tt) z
    fib-el-castF ≡-refl z = ≡-refl

    fib-castE : ∀ {B B'} (E : B ≡ B') (x : B' .idx .Carrier) →
                B .fam .fm (≡-subst Car (≡-sym E) x) ≡ B' .fam .fm x
    fib-castE ≡-refl x = ≡-refl

  mutual
    fib-fwd-≡ : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
                (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
                (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                (x : T₁.W ∣ Q ∣ ρ₁) →
                T₂.fib (constant-free-go Q ι) d₂ (wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x) ≡ T₁.fib Q d₁ x
    fib-fwd-≡ Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok (T₁.sup x) =
      fib-shape-≡ Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok x

    fib-shape-≡ : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                  (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                  (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
                  (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                  (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                  (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                  (x : T₁.⟦ ∣ Q ∣ ⟧shape η₁) →
                  T₂.fib-shape (constant-free-go Q ι) d₂ (shape-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok x) ≡ T₁.fib-shape Q d₁ x
    fib-shape-≡ {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok x =
      ≡-trans (fib-el-castF (fresh (ι Fin.zero)) _)
        (fib-castE (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)) x)
    fib-shape-≡ (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok x = fib-el-≡ (vars i) x
    fib-shape-≡ (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₁ x) =
      fib-shape-≡ Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x
    fib-shape-≡ (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok (inj₂ y) =
      fib-shape-≡ R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y
    fib-shape-≡ (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok (x , y) =
      cong₂ prod
        (fib-shape-≡ Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) x)
        (fib-shape-≡ R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
          (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) y)
    fib-shape-≡ (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok x = fib-fwd-≡ Q' η₁ ι η₂ d₁ d₂ vars fresh csok x

    fib-el-≡ : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) (x : T₁.El r₁) →
               T₂.fib-el r₂ dr₂ (el-fwd r x) ≡ T₁.fib-el r₁ dr₁ x
    fib-el-≡ (env {p}) x = fib-castE (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)) x
    fib-el-≡ (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) x = fib-fwd-≡ Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x

  -- Object equalities induce morphisms; the casts commute with the fibre
  -- transports.
  private
    ≡-mor : ∀ {A B : obj} → A ≡ B → A ⇒ B
    ≡-mor ≡-refl = id _

    -- Leaf square: a cast built from a reference equality and an object
    -- equality commutes with the underlying family's transport.
    leaf-compat : ∀ {r q} (F : r ≡ inj₁ q) {dr : T₂.DecoAssign r} {B} (E : δ⁺ q ≡ B)
                  {x y : B .idx .Carrier} (p : B .idx ._≈s_ x y) →
                  (≡-mor (≡-sym (≡-trans (fib-el-castF F {dr} (≡-subst Car (≡-sym E) y)) (fib-castE E y)))
                    ∘ B .fam .subst p)
                  ≈ (T₂.fib-el-subst r dr (el-cast-≈ (≡-sym F) (cast-≈ (≡-sym E) p))
                    ∘ ≡-mor (≡-sym (≡-trans (fib-el-castF F {dr} (≡-subst Car (≡-sym E) x)) (fib-castE E x))))
    leaf-compat ≡-refl ≡-refl p = ≈-trans id-left (≈-sym id-right)

    env-compat : ∀ {B B'} (E : B' ≡ B) {x y : B .idx .Carrier} (p : B .idx ._≈s_ x y) →
                 (≡-mor (≡-sym (fib-castE E y)) ∘ B .fam .subst p)
                 ≈ (B' .fam .subst (cast-≈ (≡-sym E) p) ∘ ≡-mor (≡-sym (fib-castE E x)))
    env-compat ≡-refl p = ≈-trans id-left (≈-sym id-right)

    prod-sq : ∀ {A₁ A₂ B₁ B₂ A₁' A₂' B₁' B₂' : obj}
              (ey₁ : A₁' ≡ A₁) (ey₂ : A₂' ≡ A₂) (ex₁ : B₁' ≡ B₁) (ex₂ : B₂' ≡ B₂)
              {s₁ : B₁ ⇒ A₁} {s₂ : B₂ ⇒ A₂} {s₁' : B₁' ⇒ A₁'} {s₂' : B₂' ⇒ A₂'} →
              (≡-mor (≡-sym ey₁) ∘ s₁) ≈ (s₁' ∘ ≡-mor (≡-sym ex₁)) →
              (≡-mor (≡-sym ey₂) ∘ s₂) ≈ (s₂' ∘ ≡-mor (≡-sym ex₂)) →
              (≡-mor (≡-sym (cong₂ prod ey₁ ey₂)) ∘ prod-m s₁ s₂)
              ≈ (prod-m s₁' s₂' ∘ ≡-mor (≡-sym (cong₂ prod ex₁ ex₂)))
    prod-sq ≡-refl ≡-refl ≡-refl ≡-refl h₁ h₂ =
      ≈-trans id-left
        (≈-trans (prod-m-cong (≈-trans (≈-sym id-left) (≈-trans h₁ id-right))
                              (≈-trans (≈-sym id-left) (≈-trans h₂ id-right)))
          (≈-sym id-right))

  mutual
    w-compat : ∀ {j} (Q : Poly (suc j)) (ρ₁ : Fin j → Fin n ⊎ Sort n)
               (ι : Fin (#c Q) → Fin k) (ρ₂ : Fin (j +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
               (d₁ : ∀ i → T₁.DecoAssign (ρ₁ i)) (d₂ : ∀ i → T₂.DecoAssign (ρ₂ i))
               (vars : ∀ i → RefRel (ρ₁ i) (ρ₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
               (fresh : ∀ (c : Fin k) → ρ₂ (j ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
               (csok : ∀ c → cs (ι c) ≡ consts Q c) →
               {x y : T₁.W ∣ Q ∣ ρ₁} (e : T₁.W-≈ x y) →
               (≡-mor (≡-sym (fib-fwd-≡ Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y)) ∘ T₁.fib-subst Q d₁ {x = x} {y = y} e)
               ≈ (T₂.fib-subst (constant-free-go Q ι) d₂
                    {x = wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x} {y = wfwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok y}
                    (w≈-fwd Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {x} {y} e)
                  ∘ ≡-mor (≡-sym (fib-fwd-≡ Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok x)))
    w-compat Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {T₁.sup x} {T₁.sup y} e =
      shape-compat Q (extend ρ₁ (inj₂ (mkSort ∣ Q ∣ ρ₁))) ι (extend ρ₂ (inj₂ (mkSort ∣ constant-free-go Q ι ∣ ρ₂)))
        (T₁.deco-ext Q d₁) (T₂.deco-ext (constant-free-go Q ι) d₂)
        (extend-vars Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok) (extend-fresh Q ρ₁ ι ρ₂ fresh) csok e

    shape-compat : ∀ {jv} (Q : Poly jv) (η₁ : Fin jv → Fin n ⊎ Sort n)
                   (ι : Fin (#c Q) → Fin k) (η₂ : Fin (jv +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k))
                   (d₁ : ∀ i → T₁.DecoAssign (η₁ i)) (d₂ : ∀ i → T₂.DecoAssign (η₂ i))
                   (vars : ∀ i → RefRel (η₁ i) (η₂ (i ↑ˡ k)) (d₁ i) (d₂ (i ↑ˡ k))) →
                   (fresh : ∀ (c : Fin k) → η₂ (jv ↑ʳ c) ≡ inj₁ (n ↑ʳ c)) →
                   (csok : ∀ c → cs (ι c) ≡ consts Q c) →
                   {x y : T₁.⟦ ∣ Q ∣ ⟧shape η₁} (e : T₁.shape≈ ∣ Q ∣ η₁ x y) →
                   (≡-mor (≡-sym (fib-shape-≡ Q η₁ ι η₂ d₁ d₂ vars fresh csok y)) ∘ T₁.fib-shape-subst Q d₁ e)
                   ≈ (T₂.fib-shape-subst (constant-free-go Q ι) d₂ (shape≈-fwd Q η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} e)
                      ∘ ≡-mor (≡-sym (fib-shape-≡ Q η₁ ι η₂ d₁ d₂ vars fresh csok x)))
    shape-compat {jv} (const A) η₁ ι η₂ d₁ d₂ vars fresh csok e =
      leaf-compat (fresh (ι Fin.zero))
        (≡-trans (cong [ δ , cs ]′ (splitAt-↑ʳ n k (ι Fin.zero))) (csok Fin.zero)) e
    shape-compat (var i)   η₁ ι η₂ d₁ d₂ vars fresh csok e = el-compat (vars i) e
    shape-compat (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₁ _} {inj₁ _} e =
      shape-compat Q η₁ (λ c → ι (c ↑ˡ #c R)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))) e
    shape-compat (Q + R)   η₁ ι η₂ d₁ d₂ vars fresh csok {inj₂ _} {inj₂ _} e =
      shape-compat R η₁ (λ c → ι (#c Q ↑ʳ c)) η₂ d₁ d₂ vars fresh
        (λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))) e
    shape-compat (Q × R)   η₁ ι η₂ d₁ d₂ vars fresh csok {x₁ , x₂} {y₁ , y₂} (e₁ ,ₚ e₂) =
      prod-sq (fib-shape-≡ Q η₁ ιQ η₂ d₁ d₂ vars fresh csokQ y₁) (fib-shape-≡ R η₁ ιR η₂ d₁ d₂ vars fresh csokR y₂)
              (fib-shape-≡ Q η₁ ιQ η₂ d₁ d₂ vars fresh csokQ x₁) (fib-shape-≡ R η₁ ιR η₂ d₁ d₂ vars fresh csokR x₂)
              (shape-compat Q η₁ ιQ η₂ d₁ d₂ vars fresh csokQ e₁)
              (shape-compat R η₁ ιR η₂ d₁ d₂ vars fresh csokR e₂)
      where
        ιQ = λ c → ι (c ↑ˡ #c R)
        ιR = λ c → ι (#c Q ↑ʳ c)
        csokQ = λ c → ≡-trans (csok (c ↑ˡ #c R)) (cong [ consts Q , consts R ]′ (splitAt-↑ˡ (#c Q) c (#c R)))
        csokR = λ c → ≡-trans (csok (#c Q ↑ʳ c)) (cong [ consts Q , consts R ]′ (splitAt-↑ʳ (#c Q) (#c R) c))
    shape-compat (μ Q')    η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} e =
      w-compat Q' η₁ ι η₂ d₁ d₂ vars fresh csok {x} {y} e

    el-compat : ∀ {r₁ r₂ dr₁ dr₂} (r : RefRel r₁ r₂ dr₁ dr₂) {x y : T₁.El r₁} (e : T₁.elEq r₁ x y) →
                (≡-mor (≡-sym (fib-el-≡ r y)) ∘ T₁.fib-el-subst r₁ dr₁ e)
                ≈ (T₂.fib-el-subst r₂ dr₂ (elEq-fwd r {x} {y} e) ∘ ≡-mor (≡-sym (fib-el-≡ r x)))
    el-compat (env {p}) e = env-compat (cong [ δ , cs ]′ (splitAt-↑ˡ n p k)) e
    el-compat (srt (mk Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok)) {x} {y} e =
      w-compat Q ρ₁ ι ρ₂ d₁ d₂ vars fresh csok {x} {y} e

  -- Helper kit for the isomorphism assembly.
  private
    ≡-mor-cancel : ∀ {A B : obj} (e : A ≡ B) → (≡-mor e ∘ ≡-mor (≡-sym e)) ≈ id B
    ≡-mor-cancel ≡-refl = id-left

    ≡-mor-cancel' : ∀ {A B : obj} (e : A ≡ B) → (≡-mor (≡-sym e) ∘ ≡-mor e) ≈ id A
    ≡-mor-cancel' ≡-refl = id-left

    flip-compat : ∀ {A A' B B' : obj} (eA : A' ≡ A) (eB : B' ≡ B)
                  {f : A ⇒ B} {g : A' ⇒ B'} →
                  (≡-mor (≡-sym eB) ∘ f) ≈ (g ∘ ≡-mor (≡-sym eA)) →
                  (f ∘ ≡-mor eA) ≈ (≡-mor eB ∘ g)
    flip-compat ≡-refl ≡-refl h =
      ≈-trans id-right (≈-trans (≈-sym id-left) (≈-trans h (≈-trans id-right (≈-sym id-left))))

  -- A polynomial against its constant-free form, at the extended environment.
  module Inst (P : Poly (suc n)) (ι : Fin (#c P) → Fin k)
              (csok : ∀ c → cs (ι c) ≡ consts P c) where

    private
      ρ₀ : Fin n → Fin n ⊎ Sort n
      ρ₀ i = inj₁ i

      ρ₀' : Fin (n +ℕ k) → Fin (n +ℕ k) ⊎ Sort (n +ℕ k)
      ρ₀' i = inj₁ i

      d₁₀ : ∀ i → T₁.DecoAssign (ρ₀ i)
      d₁₀ i = lift tt

      d₂₀ : ∀ i → T₂.DecoAssign (ρ₀' i)
      d₂₀ i = lift tt

      v₀ : ∀ i → RefRel (ρ₀ i) (ρ₀' (i ↑ˡ k)) (d₁₀ i) (d₂₀ (i ↑ˡ k))
      v₀ i = env

      f₀ : ∀ (c : Fin k) → ρ₀' (n ↑ʳ c) ≡ inj₁ (n ↑ʳ c)
      f₀ c = ≡-refl

      Fw : T₁.W ∣ P ∣ ρ₀ → T₂.W ∣ constant-free-go P ι ∣ ρ₀'
      Fw = wfwd P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok

      Bw : T₂.W ∣ constant-free-go P ι ∣ ρ₀' → T₁.W ∣ P ∣ ρ₀
      Bw = wbwd P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok

      fibeq : ∀ t → T₂.fib (constant-free-go P ι) d₂₀ (Fw t) ≡ T₁.fib P d₁₀ t
      fibeq = fib-fwd-≡ P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok

    fwd-mor : Mor (μObj P δ) (μObj (constant-free-go P ι) δ⁺)
    fwd-mor .idxf .prop-setoid._⇒_.func = Fw
    fwd-mor .idxf .prop-setoid._⇒_.func-resp-≈ {x₁} {x₂} = w≈-fwd P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok {x₁} {x₂}
    fwd-mor .famf .transf t = ≡-mor (≡-sym (fibeq t))
    fwd-mor .famf .natural {t₁} {t₂} e = w-compat P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok {x = t₁} {y = t₂} e

    bwd-mor : Mor (μObj (constant-free-go P ι) δ⁺) (μObj P δ)
    bwd-mor .idxf .prop-setoid._⇒_.func = Bw
    bwd-mor .idxf .prop-setoid._⇒_.func-resp-≈ {x₁} {x₂} = w≈-bwd P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok {x₁} {x₂}
    bwd-mor .famf .transf s =
      ≡-mor (fibeq (Bw s)) ∘
      T₂.fib-subst (constant-free-go P ι) d₂₀ {x = s} {y = Fw (Bw s)}
        (T₂.W-≈-sym {x = Fw (Bw s)} {y = s} (w-bf P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok s))
    bwd-mor .famf .natural {s₁} {s₂} e =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (≈-sym (T₂.fib-trans* (constant-free-go P ι) d₂₀
                                    {x = s₁} {y = s₂} {z = Fw (Bw s₂)} _ _)))
          (≈-sym
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (flip-compat (fibeq (Bw s₁)) (fibeq (Bw s₂))
                          (w-compat P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok {x = Bw s₁} {y = Bw s₂}
                            (w≈-bwd P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok {s₁} {s₂} e))))
                (≈-trans (assoc _ _ _)
                  (∘-cong₂ (≈-sym (T₂.fib-trans* (constant-free-go P ι) d₂₀
                                     {x = s₁} {y = Fw (Bw s₁)} {z = Fw (Bw s₂)} _ _))))))))

    private
      st-collapse₁ : ∀ {j} (Q : Poly (suc j)) {ρ} (d : ∀ i → T₁.DecoAssign (ρ i)) {a b : T₁.W ∣ Q ∣ ρ}
                     (p : T₁.W-≈ a b) (q : T₁.W-≈ b a) →
                     (T₁.fib-subst Q d {x = b} {y = a} q ∘ T₁.fib-subst Q d {x = a} {y = b} p) ≈ id (T₁.fib Q d a)
      st-collapse₁ Q d {a} {b} p q =
        ≈-trans (≈-sym (T₁.fib-trans* Q d {x = a} {y = b} {z = a} q p)) (T₁.fib-refl* Q d a)

      st-collapse₂ : ∀ {j} (Q : Poly (suc j)) {ρ} (d : ∀ i → T₂.DecoAssign (ρ i)) {a b : T₂.W ∣ Q ∣ ρ}
                     (p : T₂.W-≈ a b) (q : T₂.W-≈ b a) →
                     (T₂.fib-subst Q d {x = b} {y = a} q ∘ T₂.fib-subst Q d {x = a} {y = b} p) ≈ id (T₂.fib Q d a)
      st-collapse₂ Q d {a} {b} p q =
        ≈-trans (≈-sym (T₂.fib-trans* Q d {x = a} {y = b} {z = a} q p)) (T₂.fib-refl* Q d a)

    fb-≃ : Fam𝒞._≈_ (Mor-∘ fwd-mor bwd-mor) (Mor-id _)
    fb-≃ ._≃_.idxf-eq = prop-setoid.mk-≃m (λ s → w-bf P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok s)
    fb-≃ ._≃_.famf-eq ._≃f_.transf-eq {s} =
      ≈-trans (∘-cong₂ id-left)
        (≈-trans (∘-cong₂ (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (≡-mor-cancel' (fibeq (Bw s)))) id-left)))
          (st-collapse₂ (constant-free-go P ι) d₂₀ {a = s} {b = Fw (Bw s)} _ _))

    bf-≃ : Fam𝒞._≈_ (Mor-∘ bwd-mor fwd-mor) (Mor-id _)
    bf-≃ ._≃_.idxf-eq = prop-setoid.mk-≃m (λ t → w-fb P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok t)
    bf-≃ ._≃_.famf-eq ._≃f_.transf-eq {t} =
      ≈-trans (∘-cong₂ id-left)
        (≈-trans (∘-cong₂ (≈-trans (assoc _ _ _)
            (≈-trans (∘-cong₂ (≈-sym (w-compat P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok
                {x = t} {y = Bw (Fw t)}
                (T₁.W-≈-sym {x = Bw (Fw t)} {y = t} (w-fb P ρ₀ ι ρ₀' d₁₀ d₂₀ v₀ f₀ csok t)))))
              (≈-trans (≈-sym (assoc _ _ _))
                (≈-trans (∘-cong₁ (≡-mor-cancel (fibeq (Bw (Fw t))))) id-left)))))
          (st-collapse₁ P d₁₀ {a = t} {b = Bw (Fw t)} _ _))

    constant-free-inst-iso : Fam𝒞.Iso (μObj P δ) (μObj (constant-free-go P ι) δ⁺)
    constant-free-inst-iso .Fam𝒞.Iso.fwd = fwd-mor
    constant-free-inst-iso .Fam𝒞.Iso.bwd = bwd-mor
    constant-free-inst-iso .Fam𝒞.Iso.fwd∘bwd≈id = fb-≃
    constant-free-inst-iso .Fam𝒞.Iso.bwd∘fwd≈id = bf-≃

-- The μ-carrier of a polynomial coincides with its constant-free
-- form at the environment extended by its constants.
constant-free-μ-iso : ∀ {n} (P : Poly (suc n)) (δ : Fin n → Obj) →
                 Fam𝒞.Iso (μObj P δ) (μObj (constant-free P) (δ ++e consts P))
constant-free-μ-iso P δ = constant-free-inst-iso
  where open ConstantFree δ (consts P)
        open Inst P (λ c → c) (λ c → ≡-refl)
