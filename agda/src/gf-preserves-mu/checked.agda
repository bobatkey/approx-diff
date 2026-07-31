{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Checking commutes with μ at constant-free forms. A family is "checked"
-- by applying a functor G to its singleton fibres; the μ-carrier of a constant-free form
-- over an environment then agrees with the μ-carrier of the same constant-free over
-- the checked environment. The two constant-free forms live over the two Fam categories
-- but share their sorts and trees, which are built from index setoids alone;
-- the transports below relate the two erasures by recursion on the polynomial,
-- with identities at the leaves.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ) renaming (suc to sucℕ; _+_ to _+ℕ_)
import Data.Fin as Fin
open Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import prop using () renaming (_,_ to _,ₚ_)
open import categories using (Category; HasTerminal; HasProducts)
open import functor using (Functor; _∘F_; functor-preserve-iso)
open import finite-product-functor
  using (preserve-chosen-products; module preserve-chosen-products-consequences)
open import prop-setoid using (Setoid; 𝟙; idS; module ≈-Reasoning)
open import indexed-family using (functor→fam; Fam)
import fam
import fam-presentation
import polynomial-functor
import fam-mu-types.sort
import fam-mu-types.fibre

module gf-preserves-mu.checked {o m e o₂ m₂ e₂} (os es : Level)
    {𝒞 : Category o m e} (𝒞T : HasTerminal 𝒞) (𝒞P : HasProducts 𝒞)
    {𝒢 : Category o₂ m₂ e₂} (𝒢T : HasTerminal 𝒢) (𝒢P : HasProducts 𝒢)
    (G : Functor (fam.CategoryOfFamilies.cat os (os ⊔ es) 𝒞) 𝒢)
    (G-prod : preserve-chosen-products G
                (fam.CategoryOfFamilies.products.products os (os ⊔ es) 𝒞 𝒞P) 𝒢P)
    where

private
  module F𝒞 = fam.CategoryOfFamilies os (os ⊔ es) 𝒞
  module F𝒢 = fam.CategoryOfFamilies os (os ⊔ es) 𝒢
  module Sh = fam-mu-types.sort os es
  module Fc = fam-mu-types.fibre os es 𝒞T 𝒞P
  module Fg = fam-mu-types.fibre os es 𝒢T 𝒢P
  module PresC = fam-presentation os (os ⊔ es) {𝒞}
  module 𝒢C = Category 𝒢
  module 𝒢Pm = HasProducts 𝒢P

open Sh using (Sort; mkSort)
open polynomial-functor using (Poly; #c; constant-free; constant-free-go; extend)
open prop-setoid using (mk-≃m)
open prop-setoid._⇒_
open Functor
open F𝒞.Obj
open F𝒢.Obj
open F𝒢.Mor
open F𝒢._≃_
open indexed-family._⇒f_
open indexed-family._≃f_
open 𝒢C
open Iso

private
  -- Conjugating a commuting square by isomorphisms on both sides.
  iso-flip : ∀ {a b c d} (i : Iso a b) (j : Iso c d)
             {f : a ⇒ c} {g : b ⇒ d} →
             (j .fwd ∘ f) ≈ (g ∘ i .fwd) →
             (f ∘ i .bwd) ≈ (j .bwd ∘ g)
  iso-flip i j {f} {g} sq =
    ≈-trans (≈-sym id-left)
      (≈-trans (∘-cong (≈-sym (j .bwd∘fwd≈id)) ≈-refl)
        (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong ≈-refl (≈-sym (assoc _ _ _)))
            (≈-trans (∘-cong ≈-refl (∘-cong sq ≈-refl))
              (≈-trans (∘-cong ≈-refl (assoc _ _ _))
                (≈-trans (∘-cong ≈-refl
                    (∘-cong ≈-refl (i .fwd∘bwd≈id)))
                  (∘-cong ≈-refl id-right)))))))

ℓk : Level
ℓk = o ⊔ m ⊔ e ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ lsuc os ⊔ lsuc es

-- The checked family: G applied to the singleton fibres, over the same index
-- setoid.
check : F𝒞.Obj → F𝒢.Obj
check X .idx = X .idx
check X .fam = functor→fam (G ∘F PresC.singletons X)

module Checked {N : ℕ} (k : ℕ) (δ : Fin N → F𝒞.Obj) where
  module T  = Sh.Tree (λ i → δ i .idx)
  module C  = Fc.Fibre δ
  module Gd = Fg.Fibre (λ i → check (δ i))

  -- The same polynomial in constant-free form over either Fam category.
  skC : ∀ {j} (Q : Poly F𝒞.cat j) → (Fin (#c Q) → Fin k) → Poly F𝒞.cat (j +ℕ k)
  skC = constant-free-go

  skG : ∀ {j} (Q : Poly F𝒞.cat j) → (Fin (#c Q) → Fin k) → Poly F𝒢.cat (j +ℕ k)
  skG = constant-free-go

  -- Relate references and decorated sorts of the two constant-free forms:
  -- environment positions coincide, and sorts relate recursively through the
  -- μ-body from which both are formed.
  mutual
    data SRel : (r₁ r₂ : Fin N ⊎ Sort N) → C.DecoAssign r₁ → Gd.DecoAssign r₂ → Set ℓk where
      env : ∀ {p} → SRel (inj₁ p) (inj₁ p) (lift tt) (lift tt)
      srt : ∀ {s₁ s₂ e₁ e₂} → SortChk s₁ s₂ e₁ e₂ → SRel (inj₂ s₁) (inj₂ s₂) e₁ e₂

    data SortChk : (s₁ s₂ : Sort N) → C.Deco s₁ → Gd.Deco s₂ → Set ℓk where
      mk : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i)) →
           (∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           SortChk (mkSort Fc.∣ skC Q ι ∣ ρ₁) (mkSort Fg.∣ skG Q ι ∣ ρ₂)
                   (C.mkDeco (skC Q ι) d₁) (Gd.mkDeco (skG Q ι) d₂)

  -- Forward tree transport, by recursion on the polynomial; the leaves are
  -- identities.
  mutual
    cfwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fc.∣ skC Q ι ∣ ρ₁ → T.W Fg.∣ skG Q ι ∣ ρ₂
    cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cfwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
               (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
               (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x)

    extend-rel : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
                 (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
                 (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
                 ∀ i → SRel (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)) i)
                            (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)) i)
                            (C.deco-ext (skC Q ι) d₁ i)
                            (Gd.deco-ext (skG Q ι) d₂ i)
    extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel Fin.zero    = srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)
    extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel (Fin.suc i) = rel i

    shape-cfwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                 (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁ → T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂
    shape-cfwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cfwd (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cfwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cfwd (rel (i ↑ˡ k)) x
    shape-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      inj₁ (shape-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x)
    shape-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      inj₂ (shape-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y)
    shape-cfwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      , shape-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = cfwd Q' ι η₁ η₂ d₁ d₂ rel t

    el-cfwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₁ → T.El r₂
    el-cfwd env x = x
    el-cfwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x

  -- The forward transport preserves bisimilarity.
  mutual
    c≈fwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
            (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fc.∣ skC Q ι ∣ ρ₁} → T.W-≈ x y →
            T.W-≈ (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x) (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)
    c≈fwd Q ι ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cfwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cfwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                  (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁} → T.shape≈ Fc.∣ skC Q ι ∣ η₁ x y →
                  T.shape≈ Fg.∣ skG Q ι ∣ η₂ (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel x) (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel y)
    shape≈-cfwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel p = elEq-cfwd (rel (jv ↑ʳ ι Fin.zero)) p
    shape≈-cfwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel p = elEq-cfwd (rel (i ↑ˡ k)) p
    shape≈-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p =
      shape≈-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p =
      shape≈-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel p
    shape≈-cfwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cfwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
      ,ₚ shape≈-cfwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel q
    shape≈-cfwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel {x} {y} p = c≈fwd Q' ι η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cfwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₁} →
                T.elEq r₁ x y → T.elEq r₂ (el-cfwd r x) (el-cfwd r y)
    elEq-cfwd env p = p
    elEq-cfwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈fwd Q ι ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Backward tree transport.
  mutual
    cbwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           T.W Fg.∣ skG Q ι ∣ ρ₂ → T.W Fc.∣ skC Q ι ∣ ρ₁
    cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      T.sup (shape-cbwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
               (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
               (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
               (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x)

    shape-cbwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                 (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                 (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                 (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                 T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂ → T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁
    shape-cbwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cbwd (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cbwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cbwd (rel (i ↑ˡ k)) x
    shape-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      inj₁ (shape-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x)
    shape-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      inj₂ (shape-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y)
    shape-cbwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      , shape-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = cbwd Q' ι η₁ η₂ d₁ d₂ rel t

    el-cbwd : ∀ {r₁ r₂ e₁ e₂} → SRel r₁ r₂ e₁ e₂ → T.El r₂ → T.El r₁
    el-cbwd env x = x
    el-cbwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel x

  -- The backward transport preserves bisimilarity.
  mutual
    c≈bwd : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
            (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
            (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
            (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
            {x y : T.W Fg.∣ skG Q ι ∣ ρ₂} → T.W-≈ x y →
            T.W-≈ (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel x) (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)
    c≈bwd Q ι ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup y} p =
      shape≈-cbwd Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) p

    shape≈-cbwd : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                  (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                  (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                  (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                  {x y : T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂} → T.shape≈ Fg.∣ skG Q ι ∣ η₂ x y →
                  T.shape≈ Fc.∣ skC Q ι ∣ η₁ (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel x) (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel y)
    shape≈-cbwd {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel p = elEq-cbwd (rel (jv ↑ʳ ι Fin.zero)) p
    shape≈-cbwd (Poly.var i)   ι η₁ η₂ d₁ d₂ rel p = elEq-cbwd (rel (i ↑ˡ k)) p
    shape≈-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p =
      shape≈-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p =
      shape≈-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel p
    shape≈-cbwd (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel {_ , _} {_ , _} (p ,ₚ q) =
      shape≈-cbwd Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
      ,ₚ shape≈-cbwd R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel q
    shape≈-cbwd (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel {x} {y} p = c≈bwd Q' ι η₁ η₂ d₁ d₂ rel {x} {y} p

    elEq-cbwd : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x y : T.El r₂} →
                T.elEq r₂ x y → T.elEq r₁ (el-cbwd r x) (el-cbwd r y)
    elEq-cbwd env p = p
    elEq-cbwd (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) {x} {y} p = c≈bwd Q ι ρ₁ ρ₂ d₁ d₂ rel {x} {y} p

  -- Round trips: the two transports are mutually inverse up to bisimilarity.
  mutual
    c-fb : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (x : T.W Fc.∣ skC Q ι ∣ ρ₁) →
           T.W-≈ (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel x)) x
    c-fb Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      shape-cfb Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x

    shape-cfb : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (x : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁) →
                T.shape≈ Fc.∣ skC Q ι ∣ η₁ (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel x)) x
    shape-cfb {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = el-cfb (rel (jv ↑ʳ ι Fin.zero)) x
    shape-cfb (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = el-cfb (rel (i ↑ˡ k)) x
    shape-cfb (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      shape-cfb Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
    shape-cfb (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      shape-cfb R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfb (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cfb Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      ,ₚ shape-cfb R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cfb (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = c-fb Q' ι η₁ η₂ d₁ d₂ rel t

    el-cfb : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
             T.elEq r₁ (el-cbwd r (el-cfwd r x)) x
    el-cfb (env {p}) x = T.elEq-refl (inj₁ p) x
    el-cfb (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = c-fb Q ι ρ₁ ρ₂ d₁ d₂ rel x

  mutual
    c-bf : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
           (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
           (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
           (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i)) →
           (y : T.W Fg.∣ skG Q ι ∣ ρ₂) →
           T.W-≈ (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel (cbwd Q ι ρ₁ ρ₂ d₁ d₂ rel y)) y
    c-bf Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup y) =
      shape-cbf Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) y

    shape-cbf : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i)) →
                (y : T.⟦ Fg.∣ skG Q ι ∣ ⟧shape η₂) →
                T.shape≈ Fg.∣ skG Q ι ∣ η₂ (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel (shape-cbwd Q ι η₁ η₂ d₁ d₂ rel y)) y
    shape-cbf {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel y = el-cbf (rel (jv ↑ʳ ι Fin.zero)) y
    shape-cbf (Poly.var i)   ι η₁ η₂ d₁ d₂ rel y = el-cbf (rel (i ↑ˡ k)) y
    shape-cbf (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ y) =
      shape-cbf Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      shape-cbf R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      shape-cbf Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
      ,ₚ shape-cbf R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    shape-cbf (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = c-bf Q' ι η₁ η₂ d₁ d₂ rel t

    el-cbf : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (y : T.El r₂) →
             T.elEq r₂ (el-cfwd r (el-cbwd r y)) y
    el-cbf (env {p}) y = T.elEq-refl (inj₁ p) y
    el-cbf (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) y = c-bf Q ι ρ₁ ρ₂ d₁ d₂ rel y

  -- The fibre isomorphisms: G of the checked singleton fibre at a tree against
  -- the 𝒢-side μ-fibre at the transported tree. The leaves are identities by
  -- the construction of check; products go through simple-⊗ and G's
  -- preservation of products.
  mutual
    fib-ciso : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
               (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
               (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
               (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i))
               (w : T.W Fc.∣ skC Q ι ∣ ρ₁) →
               Iso (G .fobj F𝒞.simple[ 𝟙 , C.fib (skC Q ι) d₁ w ])
                      (Gd.fib (skG Q ι) d₂ (cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel w))
    fib-ciso Q ι ρ₁ ρ₂ d₁ d₂ rel (T.sup x) =
      fib-shape-ciso Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) x

    fib-shape-ciso : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                     (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                     (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                     (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i))
                     (x : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁) →
                     Iso (G .fobj F𝒞.simple[ 𝟙 , C.fib-shape (skC Q ι) d₁ x ])
                            (Gd.fib-shape (skG Q ι) d₂ (shape-cfwd Q ι η₁ η₂ d₁ d₂ rel x))
    fib-shape-ciso {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel x = fib-el-ciso (rel (jv ↑ʳ ι Fin.zero)) x
    fib-shape-ciso (Poly.var i)   ι η₁ η₂ d₁ d₂ rel x = fib-el-ciso (rel (i ↑ˡ k)) x
    fib-shape-ciso (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₁ x) =
      fib-shape-ciso Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x
    fib-shape-ciso (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel (inj₂ y) =
      fib-shape-ciso R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y
    fib-shape-ciso (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel (x , y) =
      Iso-trans (functor-preserve-iso G (PresC.simple-⊗ 𝒞P))
        (Iso-trans (IsIso→Iso G-prod)
          (𝒢Pm.product-preserves-iso
            (fib-shape-ciso Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel x)
            (fib-shape-ciso R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel y)))
    fib-shape-ciso (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel t = fib-ciso Q' ι η₁ η₂ d₁ d₂ rel t

    fib-el-ciso : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) (x : T.El r₁) →
                  Iso (G .fobj F𝒞.simple[ 𝟙 , C.fib-el r₁ e₁ x ])
                         (Gd.fib-el r₂ e₂ (el-cfwd r x))
    fib-el-ciso (env {p}) x = Iso-refl
    fib-el-ciso (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) x = fib-ciso Q ι ρ₁ ρ₂ d₁ d₂ rel x

  open preserve-chosen-products-consequences G (F𝒞.products.products 𝒞P) 𝒢P G-prod
    using (mul⁻¹-natural)

  -- The fibre isomorphisms commute with transport along bisimilarity.
  mutual
    fib-cnat : ∀ {j} (Q : Poly F𝒞.cat (sucℕ j)) (ι : Fin (#c Q) → Fin k)
               (ρ₁ ρ₂ : Fin (j +ℕ k) → Fin N ⊎ Sort N)
               (d₁ : ∀ i → C.DecoAssign (ρ₁ i)) (d₂ : ∀ i → Gd.DecoAssign (ρ₂ i))
               (rel : ∀ i → SRel (ρ₁ i) (ρ₂ i) (d₁ i) (d₂ i))
               {w w' : T.W Fc.∣ skC Q ι ∣ ρ₁} (p : T.W-≈ w w') →
               ((fib-ciso Q ι ρ₁ ρ₂ d₁ d₂ rel w' .fwd)
                 ∘ G .fmor F𝒞.simplef[ idS 𝟙 , C.fib-subst (skC Q ι) d₁ {x = w} {y = w'} p ])
               ≈ ((Gd.fib-subst (skG Q ι) d₂
                        {x = cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel w} {y = cfwd Q ι ρ₁ ρ₂ d₁ d₂ rel w'}
                        (c≈fwd Q ι ρ₁ ρ₂ d₁ d₂ rel {w} {w'} p))
                     ∘ (fib-ciso Q ι ρ₁ ρ₂ d₁ d₂ rel w .fwd))
    fib-cnat Q ι ρ₁ ρ₂ d₁ d₂ rel {T.sup x} {T.sup x'} p =
      fib-shape-cnat Q ι (extend ρ₁ (inj₂ (mkSort Fc.∣ skC Q ι ∣ ρ₁)))
        (extend ρ₂ (inj₂ (mkSort Fg.∣ skG Q ι ∣ ρ₂)))
        (C.deco-ext (skC Q ι) d₁) (Gd.deco-ext (skG Q ι) d₂)
        (extend-rel Q ι ρ₁ ρ₂ d₁ d₂ rel) {x} {x'} p

    fib-shape-cnat : ∀ {jv} (Q : Poly F𝒞.cat jv) (ι : Fin (#c Q) → Fin k)
                     (η₁ η₂ : Fin (jv +ℕ k) → Fin N ⊎ Sort N)
                     (d₁ : ∀ i → C.DecoAssign (η₁ i)) (d₂ : ∀ i → Gd.DecoAssign (η₂ i))
                     (rel : ∀ i → SRel (η₁ i) (η₂ i) (d₁ i) (d₂ i))
                     {x x' : T.⟦ Fc.∣ skC Q ι ∣ ⟧shape η₁} (p : T.shape≈ Fc.∣ skC Q ι ∣ η₁ x x') →
                     ((fib-shape-ciso Q ι η₁ η₂ d₁ d₂ rel x' .fwd)
                       ∘ G .fmor F𝒞.simplef[ idS 𝟙 , C.fib-shape-subst (skC Q ι) d₁ p ])
                     ≈ ((Gd.fib-shape-subst (skG Q ι) d₂ (shape≈-cfwd Q ι η₁ η₂ d₁ d₂ rel {x} {x'} p))
                           ∘ (fib-shape-ciso Q ι η₁ η₂ d₁ d₂ rel x .fwd))
    fib-shape-cnat {jv} (Poly.const A) ι η₁ η₂ d₁ d₂ rel p = fib-el-cnat (rel (jv ↑ʳ ι Fin.zero)) p
    fib-shape-cnat (Poly.var i)   ι η₁ η₂ d₁ d₂ rel p = fib-el-cnat (rel (i ↑ˡ k)) p
    fib-shape-cnat (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₁ _} {inj₁ _} p =
      fib-shape-cnat Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel p
    fib-shape-cnat (Q Poly.+ R) ι η₁ η₂ d₁ d₂ rel {inj₂ _} {inj₂ _} p =
      fib-shape-cnat R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel p
    fib-shape-cnat (Q Poly.× R) ι η₁ η₂ d₁ d₂ rel {x₁ , x₂} {x₁' , x₂'} (p₁ ,ₚ p₂) =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong ≈-refl
            (≈-trans (≈-sym (G .fmor-comp _ _))
              (≈-trans (G .fmor-cong (PresC.simple-⊗-natural 𝒞P s₁ s₂))
                (G .fmor-comp _ _))))
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong (assoc _ _ _) ≈-refl)
              (≈-trans (∘-cong (∘-cong ≈-refl
                  (mul⁻¹-natural {f = smp s₁} {g = smp s₂})) ≈-refl)
                (≈-trans (∘-cong (≈-sym (assoc _ _ _)) ≈-refl)
                  (≈-trans (∘-cong (∘-cong
                      (≈-trans (≈-sym (𝒢Pm.prod-m-comp _ _ _ _))
                        (≈-trans
                          (𝒢Pm.prod-m-cong
                            (fib-shape-cnat Q (λ c → ι (c ↑ˡ #c R)) η₁ η₂ d₁ d₂ rel {x₁} {x₁'} p₁)
                            (fib-shape-cnat R (λ c → ι (#c Q ↑ʳ c)) η₁ η₂ d₁ d₂ rel {x₂} {x₂'} p₂))
                          (𝒢Pm.prod-m-comp _ _ _ _))) ≈-refl) ≈-refl)
                    (≈-trans (∘-cong (assoc _ _ _) ≈-refl)
                      (assoc _ _ _))))))))
      where
        s₁ = C.fib-shape-subst (skC Q (λ c → ι (c ↑ˡ #c R))) d₁ p₁
        s₂ = C.fib-shape-subst (skC R (λ c → ι (#c Q ↑ʳ c))) d₁ p₂

        smp : ∀ {a b} → Category._⇒_ 𝒞 a b → F𝒞.Mor F𝒞.simple[ 𝟙 , a ] F𝒞.simple[ 𝟙 , b ]
        smp h = F𝒞.simplef[ idS 𝟙 , h ]
    fib-shape-cnat (Poly.μ Q')  ι η₁ η₂ d₁ d₂ rel {t} {t'} p = fib-cnat Q' ι η₁ η₂ d₁ d₂ rel {t} {t'} p

    fib-el-cnat : ∀ {r₁ r₂ e₁ e₂} (r : SRel r₁ r₂ e₁ e₂) {x x' : T.El r₁} (p : T.elEq r₁ x x') →
                  ((fib-el-ciso r x' .fwd)
                    ∘ G .fmor F𝒞.simplef[ idS 𝟙 , C.fib-el-subst r₁ e₁ p ])
                  ≈ ((Gd.fib-el-subst r₂ e₂ (elEq-cfwd r {x} {x'} p))
                        ∘ (fib-el-ciso r x .fwd))
    fib-el-cnat (env {p}) q = ≈-trans id-left (≈-sym id-right)
    fib-el-cnat (srt (mk Q ι ρ₁ ρ₂ d₁ d₂ rel)) {x} {x'} q = fib-cnat Q ι ρ₁ ρ₂ d₁ d₂ rel {x} {x'} q

-- The assembled comparison: check commutes with μ at the constant-free form,
-- as an isomorphism of Fam(𝒢)-objects.
module ChkMu {n : ℕ} (P : Poly F𝒞.cat (sucℕ n)) (ε : Fin (n +ℕ #c P) → F𝒞.Obj) where
  open Checked (#c P) ε
  open Fam

  private
    ρ₀ : Fin (n +ℕ #c P) → Fin (n +ℕ #c P) ⊎ Sort (n +ℕ #c P)
    ρ₀ i = inj₁ i

    d₁₀ : ∀ i → C.DecoAssign (ρ₀ i)
    d₁₀ i = lift tt

    d₂₀ : ∀ i → Gd.DecoAssign (ρ₀ i)
    d₂₀ i = lift tt

    rel₀ : ∀ i → SRel (ρ₀ i) (ρ₀ i) (d₁₀ i) (d₂₀ i)
    rel₀ i = env

    Fw = cfwd P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀
    Bw = cbwd P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀
    ci = fib-ciso P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀

  fwd-mor : F𝒢.Mor (check (Fc.μObj (constant-free P) ε)) (Fg.μObj (constant-free P) (λ i → check (ε i)))
  fwd-mor .idxf .func = Fw
  fwd-mor .idxf .func-resp-≈ {w} {w'} =
    c≈fwd P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {w'}
  fwd-mor .famf .transf w = ci w .fwd
  fwd-mor .famf .natural {w} {w'} q =
    fib-cnat P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {w'} q

  bwd-mor : F𝒢.Mor (Fg.μObj (constant-free P) (λ i → check (ε i))) (check (Fc.μObj (constant-free P) ε))
  bwd-mor .idxf .func = Bw
  bwd-mor .idxf .func-resp-≈ {s} {s'} =
    c≈bwd P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {s} {s'}
  bwd-mor .famf .transf s =
    ci (Bw s) .bwd ∘
    Gd.fib-subst (constant-free P) d₂₀ {x = s} {y = Fw (Bw s)}
      (T.W-≈-sym {x = Fw (Bw s)} {y = s} (c-bf P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ s))
  bwd-mor .famf .natural {s₁} {s₂} q =
    ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (≈-sym (Gd.fib-trans* (constant-free P) d₂₀
                                           {x = s₁} {y = s₂} {z = Fw (Bw s₂)} _ q)))
        (≈-sym
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (iso-flip (ci (Bw s₁)) (ci (Bw s₂))
                (fib-cnat P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {Bw s₁} {Bw s₂}
                  (c≈bwd P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {s₁} {s₂} q))))
              (≈-trans (assoc _ _ _)
                (∘-cong₂ (≈-sym (Gd.fib-trans* (constant-free P) d₂₀
                                          {x = s₁} {y = Fw (Bw s₁)} {z = Fw (Bw s₂)} _ _))))))))

  fb-≃ : Category._≈_ F𝒢.cat
           (Category._∘_ F𝒢.cat fwd-mor bwd-mor) (Category.id F𝒢.cat _)
  fb-≃ .idxf-eq =
    mk-≃m (λ s → c-bf P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ s)
  fb-≃ .famf-eq .transf-eq {s} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (ci (Bw s) .fwd∘bwd≈id)) id-left)))
        (≈-trans (≈-sym (Gd.fib-trans* (constant-free P) d₂₀
                                  {x = s} {y = Fw (Bw s)} {z = s} _ _))
          (Gd.fib-refl* (constant-free P) d₂₀ s)))

  bf-≃ : Category._≈_ F𝒢.cat
           (Category._∘_ F𝒢.cat bwd-mor fwd-mor) (Category.id F𝒢.cat _)
  bf-≃ .idxf-eq =
    mk-≃m (λ w → c-fb P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ w)
  bf-≃ .famf-eq .transf-eq {w} =
    ≈-trans (∘-cong₂ id-left)
      (≈-trans (∘-cong₂ (≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (≈-sym
              (fib-cnat P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ {w} {Bw (Fw w)}
                (T.W-≈-sym {x = Bw (Fw w)} {y = w} (c-fb P (λ c → c) ρ₀ ρ₀ d₁₀ d₂₀ rel₀ w)))))
            (≈-trans (≈-sym (assoc _ _ _))
              (≈-trans (∘-cong₁ (ci (Bw (Fw w)) .bwd∘fwd≈id)) id-left)))))
        (≈-trans (≈-sym (check (Fc.μObj (constant-free P) ε) .fam .trans*
                                  {x = w} {y = Bw (Fw w)} {z = w} _ _))
          (check (Fc.μObj (constant-free P) ε) .fam .refl* {x = w})))

  check-μ-iso : Category.Iso F𝒢.cat
                  (check (Fc.μObj (constant-free P) ε)) (Fg.μObj (constant-free P) (λ i → check (ε i)))
  check-μ-iso .Category.Iso.fwd = fwd-mor
  check-μ-iso .Category.Iso.bwd = bwd-mor
  check-μ-iso .Category.Iso.fwd∘bwd≈id = fb-≃
  check-μ-iso .Category.Iso.bwd∘fwd≈id = bf-≃
