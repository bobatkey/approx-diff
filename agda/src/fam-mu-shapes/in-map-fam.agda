{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- Fibre side of the algebra map. DecoF carries the canonical decorations of
-- both sides of an FMor translation, its binder bodies undecorated on the
-- target side because the extended environment supplies their fibres. The
-- fibre action of the context shift in-shape is then built from identities
-- and 𝒞-products: at an α-position the spliced subtree's fibre is the
-- μ-object's fibre on the nose, so the splice is the identity.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid)
open import categories using (Category; HasTerminal; HasProducts)
open import indexed-family using (Fam)
import fam-mu-shapes.fibre
import fam-mu-shapes.initiality

module fam-mu-shapes.in-map-fam {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CP : HasProducts 𝒞) where

open fam-mu-shapes.fibre os es T CP public
module IX = fam-mu-shapes.initiality os es

private
  ℓD : Level
  ℓD = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

-- The canonical root decoration, and decorations of the two sides of an FMor
-- translation. Decorations are environment-free, so these are shared by the
-- algebra map (target environment ι[α ↦ carrier]) and the fold (target
-- environment ι[α ↦ Y]).
module DecoDefs {n} (P : Poly-C (suc n)) where
  d₀ : ∀ i → Decos.DecoAssign n (IX.params i)
  d₀ i = lift tt

  data DecoF : ∀ {k} {ρ : Fin k → Fin n ⊎ Sh.Sort n} {ρ'} → IX.FMor ∣ P ∣ ρ ρ' →
               ((v : Fin k) → Decos.DecoAssign n (ρ v)) →
               ((v : Fin k) → Decos.DecoAssign (suc n) (ρ' v)) → Set ℓD where
    dbase : DecoF IX.fbase (Decos.deco-ext n P d₀) (λ v → lift tt)
    dbind : ∀ {k} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'} (Q : Poly-C (suc k)) →
            DecoF fm d d' →
            DecoF (IX.fbind ∣ Q ∣ fm) (Decos.deco-ext n Q d) (Decos.deco-ext (suc n) Q d')

module InMapFam {n} (P : Poly-C (suc n)) (δ : Fin n → Obj) where
  ι : Fin n → Setoid os (os ⊔ es)
  ι i = δ i .idx

  δf : ∀ i → Fam (ι i) 𝒞
  δf i = δ i .fam

  module I = IX.InMap ι ∣ P ∣
  module Fδ = Fibre ι δf

  δf' : ∀ v → Fam (I.ιᵢ v) 𝒞
  δf' = extendF δf (μObj P δ .fam)

  module Fδ' = Fibre I.ιᵢ δf'

  open DecoDefs P

  mutual
    in-fam-tree : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                  (df : DecoF fm d d') (w : I.S'.W ∣ Q ∣ ρ') (a : I.Tᵢ.Assign w) →
                  Fδ'.fib Q d' w a ⇒ Fδ.fib Q d (proj₁ (I.in-tree fm w a)) (proj₂ (I.in-tree fm w a))
    in-fam-tree {Q = Q} df (I.S'.sup s) a = in-fam-shape Q (dbind Q df) s a

    in-fam-shape : ∀ {j} (R : Poly-C j) {ηA ηB} {fm : IX.FMor ∣ P ∣ ηA ηB} {d d'}
                   (df : DecoF fm d d') (s : I.S'.Shape ∣ R ∣ ηB) (a : I.Tᵢ.AssignSh ∣ R ∣ ηB s) →
                   Fδ'.fib-shape R d' s a ⇒
                     Fδ.fib-shape R d (proj₁ (I.in-shape ∣ R ∣ fm s a)) (proj₂ (I.in-shape ∣ R ∣ fm s a))
    in-fam-shape (const A) df s a = id _
    in-fam-shape (var v)   df s a = in-fam-el df v s a
    in-fam-shape (R₁ + R₂) df (inj₁ s) a = in-fam-shape R₁ df s a
    in-fam-shape (R₁ + R₂) df (inj₂ s) a = in-fam-shape R₂ df s a
    in-fam-shape (R₁ × R₂) df (s₁ , s₂) a =
      prod-m (in-fam-shape R₁ df s₁ (λ p → a (inj₁ p))) (in-fam-shape R₂ df s₂ (λ p → a (inj₂ p)))
    in-fam-shape (μ Q')    df s a = in-fam-tree df s a

    in-fam-el : ∀ {k} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'} (df : DecoF fm d d') (v : Fin k)
                (s : I.S'.El (ρ' v)) (a : I.Tᵢ.AssignEl (ρ' v) s) →
                Fδ'.fib-el (ρ' v) (d' v) s a ⇒
                  Fδ.fib-el (ρ v) (d v) (proj₁ (I.in-el fm v s a)) (proj₂ (I.in-el fm v s a))
    in-fam-el dbase        zero    s a = id _
    in-fam-el dbase        (suc i) s a = id _
    in-fam-el (dbind Q df) zero    w a = in-fam-tree df w a
    in-fam-el (dbind Q df) (suc v) s a = in-fam-el df v s a

  -- Naturality of the fibre action: it commutes with transport along tree
  -- equality on the two sides. Leaf cases close by proof irrelevance of the
  -- transported proofs and the identity laws.
  mutual
    in-fam-tree-nat : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                      (df : DecoF fm d d') {w₁ w₂ : I.S'.W ∣ Q ∣ ρ'} {a₁ a₂}
                      (p : Fδ'.E.W≈ w₁ w₂ a₁ a₂) →
                      (in-fam-tree df w₂ a₂ ∘ Fδ'.fib-subst Q d' {w₁ = w₁} {w₂ = w₂} p)
                        ≈ (Fδ.fib-subst Q d {w₁ = proj₁ (I.in-tree fm w₁ a₁)}
                             {w₂ = proj₁ (I.in-tree fm w₂ a₂)}
                             (I.in-tree-resp fm {w₁ = w₁} {w₂ = w₂} p)
                             ∘ in-fam-tree df w₁ a₁)
    in-fam-tree-nat {Q = Q} df {I.S'.sup s₁} {I.S'.sup s₂} p =
      in-fam-shape-nat Q (dbind Q df) p

    in-fam-shape-nat : ∀ {j} (R : Poly-C j) {ηA ηB} {fm : IX.FMor ∣ P ∣ ηA ηB} {d d'}
                       (df : DecoF fm d d') {s₁ s₂ : I.S'.Shape ∣ R ∣ ηB} {a₁ a₂}
                       (p : Fδ'.E.Sh≈ ∣ R ∣ ηB s₁ s₂ a₁ a₂) →
                       (in-fam-shape R df s₂ a₂ ∘ Fδ'.fib-shape-subst R d' p)
                         ≈ (Fδ.fib-shape-subst R d (I.in-shape-resp ∣ R ∣ fm p)
                              ∘ in-fam-shape R df s₁ a₁)
    in-fam-shape-nat (const A) df p = ≈-trans id-left (≈-sym id-right)
    in-fam-shape-nat (var v)   df p = in-fam-el-nat df v p
    in-fam-shape-nat (R₁ + R₂) df {inj₁ _} {inj₁ _} p = in-fam-shape-nat R₁ df p
    in-fam-shape-nat (R₁ + R₂) df {inj₂ _} {inj₂ _} p = in-fam-shape-nat R₂ df p
    in-fam-shape-nat (R₁ × R₂) df {_ , _} {_ , _} (p₁ , p₂) =
      ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (in-fam-shape-nat R₁ df p₁) (in-fam-shape-nat R₂ df p₂))
          (prod-m-comp _ _ _ _))
    in-fam-shape-nat (μ Q')    df {w₁} {w₂} p = in-fam-tree-nat df {w₁ = w₁} {w₂ = w₂} p

    in-fam-el-nat : ∀ {k} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'} (df : DecoF fm d d')
                    (v : Fin k) {s₁ s₂ : I.S'.El (ρ' v)} {a₁ a₂}
                    (p : Fδ'.E.El≈ (ρ' v) s₁ s₂ a₁ a₂) →
                    (in-fam-el df v s₂ a₂ ∘ Fδ'.fib-el-subst (ρ' v) (d' v) p)
                      ≈ (Fδ.fib-el-subst (ρ v) (d v) (I.in-el-resp fm v p)
                           ∘ in-fam-el df v s₁ a₁)
    in-fam-el-nat dbase        zero    p = ≈-trans id-left (≈-sym id-right)
    in-fam-el-nat dbase        (suc i) p = ≈-trans id-left (≈-sym id-right)
    in-fam-el-nat (dbind Q df) zero    {w₁} {w₂} p = in-fam-tree-nat df {w₁ = w₁} {w₂ = w₂} p
    in-fam-el-nat (dbind Q df) (suc v) p = in-fam-el-nat df v p

  ------------------------------------------------------------------------------
  -- The object-level extended environment, which fobj interprets over, and
  -- the coercion from its trees to the setoid-extended spelling used by the
  -- algebra map. The two agree at every applied index, so the coercion is the
  -- identity at each label; it exists only because the two spellings of the
  -- environment are not convertible at a neutral index.
  ------------------------------------------------------------------------------
  δ'F : Fin (suc n) → Obj
  δ'F = extend δ (μObj P δ)

  ιᵐ : Fin (suc n) → Setoid os (os ⊔ es)
  ιᵐ v = δ'F v .idx

  module Fμ' = Fibre ιᵐ (λ v → δ'F v .fam)
  module Eᵐ = Sh.TreeEq ιᵐ (λ v → Setoid._≈_ (ιᵐ v))

  open Decos (suc n) using (mkDeco)

  coeIx : (l : Setoid os (os ⊔ es) ⊎ Fin (suc n)) → Sh.Trees.Ix ιᵐ l → Sh.Trees.Ix I.ιᵢ l
  coeIx (inj₁ S)       x = x
  coeIx (inj₂ zero)    x = x
  coeIx (inj₂ (suc i)) x = x

  mutual
    coe-W-resp : ∀ {k} {Q : Sh.Poly (suc k)} {ρ̄} {w₁ w₂ : I.S'.W Q ρ̄} {a₁ a₂} →
                 Eᵐ.W≈ w₁ w₂ a₁ a₂ →
                 I.Eᵢ.W≈ w₁ w₂ (λ p → coeIx (I.S'.labelW w₁ p) (a₁ p))
                   (λ p → coeIx (I.S'.labelW w₂ p) (a₂ p))
    coe-W-resp {Q = Q} {ρ̄} {I.S'.sup s₁} {I.S'.sup s₂} p =
      coe-Sh-resp Q (extend ρ̄ (inj₂ (Sh.mkSort Q ρ̄))) p

    coe-Sh-resp : ∀ {k} (Q : Sh.Poly k) (η̄ : Fin k → Fin (suc n) ⊎ Sh.Sort (suc n))
                  {s₁ s₂ : I.S'.Shape Q η̄} {a₁ a₂} → Eᵐ.Sh≈ Q η̄ s₁ s₂ a₁ a₂ →
                  I.Eᵢ.Sh≈ Q η̄ s₁ s₂ (λ p → coeIx (I.S'.labelSh Q η̄ s₁ p) (a₁ p))
                    (λ p → coeIx (I.S'.labelSh Q η̄ s₂ p) (a₂ p))
    coe-Sh-resp (const S) η̄ p = p
    coe-Sh-resp (var j)   η̄ p = coe-El-resp (η̄ j) p
    coe-Sh-resp (Q₁ + Q₂) η̄ {inj₁ _} {inj₁ _} p = coe-Sh-resp Q₁ η̄ p
    coe-Sh-resp (Q₁ + Q₂) η̄ {inj₂ _} {inj₂ _} p = coe-Sh-resp Q₂ η̄ p
    coe-Sh-resp (Q₁ × Q₂) η̄ {_ , _} {_ , _} (p , q) = coe-Sh-resp Q₁ η̄ p , coe-Sh-resp Q₂ η̄ q
    coe-Sh-resp (μ Q')    η̄ {w₁} {w₂} p = coe-W-resp {w₁ = w₁} {w₂ = w₂} p

    coe-El-resp : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) {s₁ s₂ : I.S'.El r} {a₁ a₂} →
                  Eᵐ.El≈ r s₁ s₂ a₁ a₂ →
                  I.Eᵢ.El≈ r s₁ s₂ (λ p → coeIx (I.S'.labelEl r s₁ p) (a₁ p))
                    (λ p → coeIx (I.S'.labelEl r s₂ p) (a₂ p))
    coe-El-resp (inj₁ zero)    p = p
    coe-El-resp (inj₁ (suc i)) p = p
    coe-El-resp (inj₂ (Sh.mkSort Q ρ̄)) {w₁} {w₂} p = coe-W-resp {w₁ = w₁} {w₂ = w₂} p

  mutual
    coe-fam-tree : ∀ {k} {Q : Poly-C (suc k)} {ρ̄} (d : ∀ v → Fδ'.DecoAssign (ρ̄ v))
                   (w : I.S'.W ∣ Q ∣ ρ̄) (a : Sh.Trees.Assign ιᵐ w) →
                   Fμ'.fib Q d w a ⇒ Fδ'.fib Q d w (λ p → coeIx (I.S'.labelW w p) (a p))
    coe-fam-tree {Q = Q} d (I.S'.sup s) a = coe-fam-shape Q (Fδ'.deco-ext Q d) s a

    coe-fam-shape : ∀ {j} (Q : Poly-C j) {η̄} (d : ∀ v → Fδ'.DecoAssign (η̄ v))
                    (s : I.S'.Shape ∣ Q ∣ η̄) (a : Sh.Trees.AssignSh ιᵐ ∣ Q ∣ η̄ s) →
                    Fμ'.fib-shape Q d s a ⇒
                      Fδ'.fib-shape Q d s (λ p → coeIx (I.S'.labelSh ∣ Q ∣ η̄ s p) (a p))
    coe-fam-shape (const A) d s a = id _
    coe-fam-shape (var j)   d s a = coe-fam-el _ (d j) s a
    coe-fam-shape (Q₁ + Q₂) d (inj₁ s) a = coe-fam-shape Q₁ d s a
    coe-fam-shape (Q₁ + Q₂) d (inj₂ s) a = coe-fam-shape Q₂ d s a
    coe-fam-shape (Q₁ × Q₂) d (s₁ , s₂) a =
      prod-m (coe-fam-shape Q₁ d s₁ (λ p → a (inj₁ p))) (coe-fam-shape Q₂ d s₂ (λ p → a (inj₂ p)))
    coe-fam-shape (μ Q')    d s a = coe-fam-tree d s a

    coe-fam-el : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) (dr : Fδ'.DecoAssign r)
                 (s : I.S'.El r) (a : Sh.Trees.AssignEl ιᵐ r s) →
                 Fμ'.fib-el r dr s a ⇒ Fδ'.fib-el r dr s (λ p → coeIx (I.S'.labelEl r s p) (a p))
    coe-fam-el (inj₁ zero)    _ s a = id _
    coe-fam-el (inj₁ (suc i)) _ s a = id _
    coe-fam-el (inj₂ _) (mkDeco Q ρd) w a = coe-fam-tree ρd w a

  coe-treeSh : ∀ {k} {Q : Sh.Poly k} {η̄} → Sh.Trees.TreeSh ιᵐ Q η̄ → Sh.Trees.TreeSh I.ιᵢ Q η̄
  coe-treeSh {Q = Q} {η̄ = η̄} (s , a) = s , λ p → coeIx (I.S'.labelSh Q η̄ s p) (a p)

  mutual
    coe-fam-tree-nat : ∀ {k} {Q : Poly-C (suc k)} {ρ̄} (d : ∀ v → Fδ'.DecoAssign (ρ̄ v))
                       {w₁ w₂ : I.S'.W ∣ Q ∣ ρ̄} {a₁ a₂} (p : Eᵐ.W≈ w₁ w₂ a₁ a₂) →
                       (coe-fam-tree d w₂ a₂ ∘ Fμ'.fib-subst Q d {w₁ = w₁} {w₂ = w₂} p)
                         ≈ (Fδ'.fib-subst Q d {w₁ = w₁} {w₂ = w₂} (coe-W-resp {w₁ = w₁} {w₂ = w₂} p)
                              ∘ coe-fam-tree d w₁ a₁)
    coe-fam-tree-nat {Q = Q} d {I.S'.sup s₁} {I.S'.sup s₂} p =
      coe-fam-shape-nat Q (Fδ'.deco-ext Q d) p

    coe-fam-shape-nat : ∀ {j} (Q : Poly-C j) {η̄} (d : ∀ v → Fδ'.DecoAssign (η̄ v))
                        {s₁ s₂ : I.S'.Shape ∣ Q ∣ η̄} {a₁ a₂} (p : Eᵐ.Sh≈ ∣ Q ∣ η̄ s₁ s₂ a₁ a₂) →
                        (coe-fam-shape Q d s₂ a₂ ∘ Fμ'.fib-shape-subst Q d p)
                          ≈ (Fδ'.fib-shape-subst Q d (coe-Sh-resp ∣ Q ∣ η̄ p)
                               ∘ coe-fam-shape Q d s₁ a₁)
    coe-fam-shape-nat (const A) d p = ≈-trans id-left (≈-sym id-right)
    coe-fam-shape-nat (var v)   d p = coe-fam-el-nat _ (d v) p
    coe-fam-shape-nat (Q₁ + Q₂) d {inj₁ _} {inj₁ _} p = coe-fam-shape-nat Q₁ d p
    coe-fam-shape-nat (Q₁ + Q₂) d {inj₂ _} {inj₂ _} p = coe-fam-shape-nat Q₂ d p
    coe-fam-shape-nat (Q₁ × Q₂) d {_ , _} {_ , _} (p₁ , p₂) =
      ≈-trans (≈-sym (prod-m-comp _ _ _ _))
        (≈-trans (prod-m-cong (coe-fam-shape-nat Q₁ d p₁) (coe-fam-shape-nat Q₂ d p₂))
          (prod-m-comp _ _ _ _))
    coe-fam-shape-nat (μ Q')    d {w₁} {w₂} p = coe-fam-tree-nat d {w₁ = w₁} {w₂ = w₂} p

    coe-fam-el-nat : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) (dr : Fδ'.DecoAssign r)
                     {s₁ s₂ : I.S'.El r} {a₁ a₂} (p : Eᵐ.El≈ r s₁ s₂ a₁ a₂) →
                     (coe-fam-el r dr s₂ a₂ ∘ Fμ'.fib-el-subst r dr p)
                       ≈ (Fδ'.fib-el-subst r dr (coe-El-resp r p) ∘ coe-fam-el r dr s₁ a₁)
    coe-fam-el-nat (inj₁ zero)    _ p = ≈-trans id-left (≈-sym id-right)
    coe-fam-el-nat (inj₁ (suc i)) _ p = ≈-trans id-left (≈-sym id-right)
    coe-fam-el-nat (inj₂ _) (mkDeco Q ρd) {w₁} {w₂} p = coe-fam-tree-nat ρd {w₁ = w₁} {w₂ = w₂} p

  ------------------------------------------------------------------------------
  -- Bridge fobj's native structure to shapes with assignments over the
  -- object-level environment: leaves become the one-position shape with the
  -- element as its assignment, and an inner μ is the identity, both sides
  -- being the same trees.
  ------------------------------------------------------------------------------
  embed-idx : (Q : Poly-C (suc n)) → fobj μObj Q δ'F .idx .Setoid.Carrier →
              Sh.Trees.TreeSh ιᵐ ∣ Q ∣ IX.params
  embed-idx (const A) a = tt , λ _ → a
  embed-idx (var v)   a = tt , λ _ → a
  embed-idx (Q₁ + Q₂) (inj₁ x) = let (s , a) = embed-idx Q₁ x in inj₁ s , a
  embed-idx (Q₁ + Q₂) (inj₂ y) = let (s , a) = embed-idx Q₂ y in inj₂ s , a
  embed-idx (Q₁ × Q₂) (x , y) =
    let (s₁ , a₁) = embed-idx Q₁ x
        (s₂ , a₂) = embed-idx Q₂ y
    in (s₁ , s₂) , λ { (inj₁ p) → a₁ p ; (inj₂ p) → a₂ p }
  embed-idx (μ Q')    t = t

  embed-resp : (Q : Poly-C (suc n)) {x y : fobj μObj Q δ'F .idx .Setoid.Carrier} →
               Setoid._≈_ (fobj μObj Q δ'F .idx) x y →
               Eᵐ.Sh≈ ∣ Q ∣ IX.params (proj₁ (embed-idx Q x)) (proj₁ (embed-idx Q y))
                 (proj₂ (embed-idx Q x)) (proj₂ (embed-idx Q y))
  embed-resp (const A) p = p
  embed-resp (var v)   p = p
  embed-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-resp Q₁ p
  embed-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-resp Q₂ p
  embed-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-resp Q₁ p₁ , embed-resp Q₂ p₂
  embed-resp (μ Q')    p = p

  embed-fam : (Q : Poly-C (suc n)) (x : fobj μObj Q δ'F .idx .Setoid.Carrier) →
              fobj μObj Q δ'F .fam .fm x ⇒
                Fμ'.fib-shape Q (λ v → lift tt) (proj₁ (embed-idx Q x)) (proj₂ (embed-idx Q x))
  embed-fam (const A) a = id _
  embed-fam (var v)   a = id _
  embed-fam (Q₁ + Q₂) (inj₁ x) = embed-fam Q₁ x
  embed-fam (Q₁ + Q₂) (inj₂ y) = embed-fam Q₂ y
  embed-fam (Q₁ × Q₂) (x , y) = prod-m (embed-fam Q₁ x) (embed-fam Q₂ y)
  embed-fam (μ Q')    t = id _

  embed-fam-natural : (Q : Poly-C (suc n)) {x y : fobj μObj Q δ'F .idx .Setoid.Carrier}
                      (e : Setoid._≈_ (fobj μObj Q δ'F .idx) x y) →
                      (embed-fam Q y ∘ fobj μObj Q δ'F .fam .subst e)
                        ≈ (Fμ'.fib-shape-subst Q (λ v → lift tt) (embed-resp Q e) ∘ embed-fam Q x)
  embed-fam-natural (const A) e = ≈-trans id-left (≈-sym id-right)
  embed-fam-natural (var v)   e = ≈-trans id-left (≈-sym id-right)
  embed-fam-natural (Q₁ + Q₂) {inj₁ _} {inj₁ _} e = embed-fam-natural Q₁ e
  embed-fam-natural (Q₁ + Q₂) {inj₂ _} {inj₂ _} e = embed-fam-natural Q₂ e
  embed-fam-natural (Q₁ × Q₂) {_ , _} {_ , _} (e₁ , e₂) =
    ≈-trans (≈-sym (prod-m-comp _ _ _ _))
      (≈-trans (prod-m-cong (embed-fam-natural Q₁ e₁) (embed-fam-natural Q₂ e₂))
        (prod-m-comp _ _ _ _))
  embed-fam-natural (μ Q')    e = ≈-trans id-left (≈-sym id-right)

  ------------------------------------------------------------------------------
  -- The algebra map as a Fam-morphism: embed fobj's element, coerce, and
  -- assemble; on fibres, the three actions compose, each built from
  -- identities and products.
  ------------------------------------------------------------------------------
  open prop-setoid._⇒_

  inMor : Fam𝒞._⇒_ (fobj μObj P δ'F) (μObj P δ)
  inMor .idxf .func x = I.inMap (coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (embed-idx P x))
  inMor .idxf .func-resp-≈ p =
    I.in-shape-resp ∣ P ∣ IX.fbase (coe-Sh-resp ∣ P ∣ IX.params (embed-resp P p))
  inMor .famf .transf x =
    in-fam-shape P dbase (proj₁ (coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (embed-idx P x))) (proj₂ (coe-treeSh {Q = ∣ P ∣} {η̄ = IX.params} (embed-idx P x)))
      ∘ (coe-fam-shape P (λ v → lift tt) (proj₁ (embed-idx P x)) (proj₂ (embed-idx P x))
         ∘ embed-fam P x)
  inMor .famf .natural {x₁} {x₂} e =
    ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (assoc _ _ _))
        (≈-trans (∘-cong₂ (∘-cong₂ (embed-fam-natural P e)))
          (≈-trans (∘-cong₂ (≈-sym (assoc _ _ _)))
            (≈-trans (∘-cong₂ (∘-cong₁ (coe-fam-shape-nat P (λ v → lift tt) (embed-resp P e))))
              (≈-trans (∘-cong₂ (assoc _ _ _))
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong₁ (in-fam-shape-nat P dbase (coe-Sh-resp ∣ P ∣ IX.params (embed-resp P e))))
                    (assoc _ _ _))))))))
