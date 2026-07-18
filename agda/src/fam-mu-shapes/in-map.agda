{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The algebra map of the Fam μ-type, over an environment of Fam objects
-- extended at α by the μ-object itself. At the index level: assemble a tree
-- of the root sort from a one-level unfolding whose α-positions hold whole
-- trees; in-el splices them in without traversing them. out decomposes at
-- the root; the two are mutually inverse up to tree equality. On fibres,
-- DecoF carries the canonical decorations of both sides of an FMor
-- translation, its binder bodies undecorated on the target side because the
-- extended environment supplies their fibres; the fibre action of in-shape
-- is then built from identities and 𝒞-products, the splice at an α-position
-- being the identity on the μ-object's fibre. embed bridges fobj's native
-- one-level structure to shapes with assignments: leaves become the
-- one-position shape with the element as its assignment, and an inner μ is
-- the identity, both sides being the same trees.
------------------------------------------------------------------------------

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import prop using (_,_)
open import prop-setoid using (Setoid; IsEquivalence)
open import categories using (Category; HasTerminal; HasProducts)
open import indexed-family using (Fam)
import fam-mu-shapes.fibre
import fam-mu-shapes.reindex

module fam-mu-shapes.in-map {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CP : HasProducts 𝒞) where

open fam-mu-shapes.fibre os es T CP public
module IX = fam-mu-shapes.reindex os es
open IsEquivalence

private
  ℓD : Level
  ℓD = o ⊔ m ⊔ e ⊔ lsuc os ⊔ lsuc es

-- The canonical root decoration, and decorations of the two sides of an FMor
-- translation. Decorations are environment-free, so these are shared by the
-- algebra map and the fold.
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

module InMap {n} (P : Poly-C (suc n)) (δ : Fin n → Obj) where
  ι : Fin n → Setoid os (os ⊔ es)
  ι i = δ i .idx

  δf : ∀ i → Fam (ι i) 𝒞
  δf i = δ i .fam

  module S = Sh.Shapes n
  module S' = Sh.Shapes (suc n)

  module T = Sh.Trees ι
  module E = Sh.TreeEq ι (λ i → Setoid._≈_ (ι i))
  module EE = E.Equiv (λ i x → ι i .Setoid.isEquivalence .refl)
                      (λ i p → ι i .Setoid.isEquivalence .sym p)
                      (λ i p q → ι i .Setoid.isEquivalence .trans p q)

  -- The carrier setoid of the μ-type at the root sort.
  TreeSetoid : Setoid os (os ⊔ es)
  TreeSetoid = μObj P δ .idx

  -- The environment extended at α by the μ-object, and its index setoids.
  δᵢ : Fin (suc n) → Obj
  δᵢ = extend δ (μObj P δ)

  ιᵢ : Fin (suc n) → Setoid os (os ⊔ es)
  ιᵢ v = δᵢ v .idx

  module Tᵢ = Sh.Trees ιᵢ
  module Eᵢ = Sh.TreeEq ιᵢ (λ v → Setoid._≈_ (ιᵢ v))

  mutual
    in-tree : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (w : S'.W Q ρ') →
              Tᵢ.Assign w → T.Tree Q ρ
    in-tree {Q = Q} fm (S'.sup s) a =
      let (s' , a') = in-shape Q (IX.fbind Q fm) s a in S.sup s' , a'

    in-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) (s : S'.Shape R ηB) →
               Tᵢ.AssignSh R ηB s → T.TreeSh R ηA
    in-shape (const S) fm s a = tt , a
    in-shape (var v)   fm s a = in-el fm v s a
    in-shape (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = in-shape R₁ fm s a in inj₁ s' , a'
    in-shape (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = in-shape R₂ fm s a in inj₂ s' , a'
    in-shape (R₁ × R₂) fm (s₁ , s₂) a =
      let (s₁' , a₁') = in-shape R₁ fm s₁ (λ p → a (inj₁ p))
          (s₂' , a₂') = in-shape R₂ fm s₂ (λ p → a (inj₂ p))
      in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
    in-shape (μ Q')    fm s a = in-tree fm s a

    in-el : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) →
            Tᵢ.AssignEl (ρ' v) s → T.TreeEl (ρ v)
    in-el IX.fbase        zero    s a = a tt
    in-el IX.fbase        (suc i) s a = tt , a
    in-el (IX.fbind Q fm) zero    w a = in-tree fm w a
    in-el (IX.fbind Q fm) (suc v) s a = in-el fm v s a

  inMap : Tᵢ.TreeSh ∣ P ∣ IX.params → T.Tree ∣ P ∣ IX.params
  inMap (s , a) = let (s' , a') = in-shape ∣ P ∣ IX.fbase s a in S.sup s' , a'

  mutual
    out-tree : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (w : S.W Q ρ) →
               T.Assign w → Tᵢ.Tree Q ρ'
    out-tree {Q = Q} fm (S.sup s) a =
      let (s' , a') = out-shape Q (IX.fbind Q fm) s a in S'.sup s' , a'

    out-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) (s : S.Shape R ηA) →
                T.AssignSh R ηA s → Tᵢ.TreeSh R ηB
    out-shape (const S) fm s a = tt , a
    out-shape (var v)   fm s a = out-el fm v s a
    out-shape (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = out-shape R₁ fm s a in inj₁ s' , a'
    out-shape (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = out-shape R₂ fm s a in inj₂ s' , a'
    out-shape (R₁ × R₂) fm (s₁ , s₂) a =
      let (s₁' , a₁') = out-shape R₁ fm s₁ (λ p → a (inj₁ p))
          (s₂' , a₂') = out-shape R₂ fm s₂ (λ p → a (inj₂ p))
      in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
    out-shape (μ Q')    fm s a = out-tree fm s a

    out-el : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) (s : S.El (ρ v)) →
             T.AssignEl (ρ v) s → Tᵢ.TreeEl (ρ' v)
    out-el IX.fbase        zero    w a = tt , λ _ → (w , a)
    out-el IX.fbase        (suc i) s a = tt , a
    out-el (IX.fbind Q fm) zero    w a = out-tree fm w a
    out-el (IX.fbind Q fm) (suc v) s a = out-el fm v s a

  out : T.Tree ∣ P ∣ IX.params → Tᵢ.TreeSh ∣ P ∣ IX.params
  out (S.sup s , a) = out-shape ∣ P ∣ IX.fbase s a

  mutual
    in-tree-resp : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') {w₁ w₂ : S'.W Q ρ'} {a₁ a₂} →
                   Eᵢ.W≈ w₁ w₂ a₁ a₂ → E.Tree≈ (in-tree fm w₁ a₁) (in-tree fm w₂ a₂)
    in-tree-resp {Q = Q} fm {S'.sup s₁} {S'.sup s₂} p = in-shape-resp Q (IX.fbind Q fm) p

    in-shape-resp : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) {s₁ s₂ : S'.Shape R ηB} {a₁ a₂} →
                    Eᵢ.Sh≈ R ηB s₁ s₂ a₁ a₂ →
                    E.Sh≈ R ηA (proj₁ (in-shape R fm s₁ a₁)) (proj₁ (in-shape R fm s₂ a₂))
                      (proj₂ (in-shape R fm s₁ a₁)) (proj₂ (in-shape R fm s₂ a₂))
    in-shape-resp (const S) fm p = p
    in-shape-resp (var v)   fm p = in-el-resp fm v p
    in-shape-resp (R₁ + R₂) fm {inj₁ _} {inj₁ _} p = in-shape-resp R₁ fm p
    in-shape-resp (R₁ + R₂) fm {inj₂ _} {inj₂ _} p = in-shape-resp R₂ fm p
    in-shape-resp (R₁ × R₂) fm {_ , _} {_ , _} (p , q) =
      in-shape-resp R₁ fm p , in-shape-resp R₂ fm q
    in-shape-resp (μ Q')    fm {w₁} {w₂} p = in-tree-resp fm {w₁ = w₁} {w₂ = w₂} p

    in-el-resp : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) {s₁ s₂ : S'.El (ρ' v)} {a₁ a₂} →
                 Eᵢ.El≈ (ρ' v) s₁ s₂ a₁ a₂ →
                 E.El≈ (ρ v) (proj₁ (in-el fm v s₁ a₁)) (proj₁ (in-el fm v s₂ a₂))
                   (proj₂ (in-el fm v s₁ a₁)) (proj₂ (in-el fm v s₂ a₂))
    in-el-resp IX.fbase        zero    p = p
    in-el-resp IX.fbase        (suc i) p = p
    in-el-resp (IX.fbind Q fm) zero    {w₁} {w₂} p = in-tree-resp fm {w₁ = w₁} {w₂ = w₂} p
    in-el-resp (IX.fbind Q fm) (suc v) p = in-el-resp fm v p

  mutual
    io-tree : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (w : S.W Q ρ) (a : T.Assign w) →
              E.Tree≈ (in-tree fm (proj₁ (out-tree fm w a)) (proj₂ (out-tree fm w a))) (w , a)
    io-tree {Q = Q} fm (S.sup s) a = io-shape Q (IX.fbind Q fm) s a

    io-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) (s : S.Shape R ηA)
               (a : T.AssignSh R ηA s) →
               E.Sh≈ R ηA (proj₁ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) s
                 (proj₂ (in-shape R fm (proj₁ (out-shape R fm s a)) (proj₂ (out-shape R fm s a)))) a
    io-shape (const S) fm s a = S .Setoid.isEquivalence .refl
    io-shape (var v)   fm s a = io-el fm v s a
    io-shape (R₁ + R₂) fm (inj₁ s) a = io-shape R₁ fm s a
    io-shape (R₁ + R₂) fm (inj₂ s) a = io-shape R₂ fm s a
    io-shape (R₁ × R₂) fm (s₁ , s₂) a =
      io-shape R₁ fm s₁ (λ p → a (inj₁ p)) , io-shape R₂ fm s₂ (λ p → a (inj₂ p))
    io-shape (μ Q')    fm s a = io-tree fm s a

    io-el : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) (s : S.El (ρ v)) (a : T.AssignEl (ρ v) s) →
            E.El≈ (ρ v) (proj₁ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) s
              (proj₂ (in-el fm v (proj₁ (out-el fm v s a)) (proj₂ (out-el fm v s a)))) a
    io-el IX.fbase        zero    w a = EE.W≈-refl w a
    io-el IX.fbase        (suc i) s a = ι i .Setoid.isEquivalence .refl
    io-el (IX.fbind Q fm) zero    w a = io-tree fm w a
    io-el (IX.fbind Q fm) (suc v) s a = io-el fm v s a

  inMap-out : (t : T.Tree ∣ P ∣ IX.params) → E.Tree≈ (inMap (out t)) t
  inMap-out (S.sup s , a) = io-shape ∣ P ∣ IX.fbase s a

  mutual
    oi-tree : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (w : S'.W Q ρ') (a : Tᵢ.Assign w) →
              Eᵢ.Tree≈ (out-tree fm (proj₁ (in-tree fm w a)) (proj₂ (in-tree fm w a))) (w , a)
    oi-tree {Q = Q} fm (S'.sup s) a = oi-shape Q (IX.fbind Q fm) s a

    oi-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) (s : S'.Shape R ηB)
               (a : Tᵢ.AssignSh R ηB s) →
               Eᵢ.Sh≈ R ηB (proj₁ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) s
                 (proj₂ (out-shape R fm (proj₁ (in-shape R fm s a)) (proj₂ (in-shape R fm s a)))) a
    oi-shape (const S) fm s a = S .Setoid.isEquivalence .refl
    oi-shape (var v)   fm s a = oi-el fm v s a
    oi-shape (R₁ + R₂) fm (inj₁ s) a = oi-shape R₁ fm s a
    oi-shape (R₁ + R₂) fm (inj₂ s) a = oi-shape R₂ fm s a
    oi-shape (R₁ × R₂) fm (s₁ , s₂) a =
      oi-shape R₁ fm s₁ (λ p → a (inj₁ p)) , oi-shape R₂ fm s₂ (λ p → a (inj₂ p))
    oi-shape (μ Q')    fm s a = oi-tree fm s a

    oi-el : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) (s : S'.El (ρ' v)) (a : Tᵢ.AssignEl (ρ' v) s) →
            Eᵢ.El≈ (ρ' v) (proj₁ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) s
              (proj₂ (out-el fm v (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a)))) a
    oi-el IX.fbase        zero    s a = EE.W≈-refl (proj₁ (a tt)) (proj₂ (a tt))
    oi-el IX.fbase        (suc i) s a = ι i .Setoid.isEquivalence .refl
    oi-el (IX.fbind Q fm) zero    w a = oi-tree fm w a
    oi-el (IX.fbind Q fm) (suc v) s a = oi-el fm v s a

  out-inMap : (t : Tᵢ.TreeSh ∣ P ∣ IX.params) →
              Eᵢ.Sh≈ ∣ P ∣ IX.params (proj₁ (out (inMap t))) (proj₁ t) (proj₂ (out (inMap t))) (proj₂ t)
  out-inMap (s , a) = oi-shape ∣ P ∣ IX.fbase s a

  ------------------------------------------------------------------------------
  -- The fibre action of the context shift in-shape, built from identities and
  -- 𝒞-products: at an α-position the spliced subtree's fibre is the μ-object's
  -- fibre on the nose, so the splice is the identity.
  ------------------------------------------------------------------------------
  module Fδ = Fibre ι δf
  module Fδ' = Fibre ιᵢ (λ v → δᵢ v .fam)

  open DecoDefs P

  mutual
    in-fam-tree : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                  (df : DecoF fm d d') (w : S'.W ∣ Q ∣ ρ') (a : Tᵢ.Assign w) →
                  Fδ'.fib Q d' w a ⇒ Fδ.fib Q d (proj₁ (in-tree fm w a)) (proj₂ (in-tree fm w a))
    in-fam-tree {Q = Q} df (S'.sup s) a = in-fam-shape Q (dbind Q df) s a

    in-fam-shape : ∀ {j} (R : Poly-C j) {ηA ηB} {fm : IX.FMor ∣ P ∣ ηA ηB} {d d'}
                   (df : DecoF fm d d') (s : S'.Shape ∣ R ∣ ηB) (a : Tᵢ.AssignSh ∣ R ∣ ηB s) →
                   Fδ'.fib-shape R d' s a ⇒
                     Fδ.fib-shape R d (proj₁ (in-shape ∣ R ∣ fm s a)) (proj₂ (in-shape ∣ R ∣ fm s a))
    in-fam-shape (const A) df s a = id _
    in-fam-shape (var v)   df s a = in-fam-el df v s a
    in-fam-shape (R₁ + R₂) df (inj₁ s) a = in-fam-shape R₁ df s a
    in-fam-shape (R₁ + R₂) df (inj₂ s) a = in-fam-shape R₂ df s a
    in-fam-shape (R₁ × R₂) df (s₁ , s₂) a =
      prod-m (in-fam-shape R₁ df s₁ (λ p → a (inj₁ p))) (in-fam-shape R₂ df s₂ (λ p → a (inj₂ p)))
    in-fam-shape (μ Q')    df s a = in-fam-tree df s a

    in-fam-el : ∀ {k} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'} (df : DecoF fm d d') (v : Fin k)
                (s : S'.El (ρ' v)) (a : Tᵢ.AssignEl (ρ' v) s) →
                Fδ'.fib-el (ρ' v) (d' v) s a ⇒
                  Fδ.fib-el (ρ v) (d v) (proj₁ (in-el fm v s a)) (proj₂ (in-el fm v s a))
    in-fam-el dbase        zero    s a = id _
    in-fam-el dbase        (suc i) s a = id _
    in-fam-el (dbind Q df) zero    w a = in-fam-tree df w a
    in-fam-el (dbind Q df) (suc v) s a = in-fam-el df v s a

  -- Naturality of the fibre action: it commutes with transport along tree
  -- equality on the two sides. Leaf cases close by proof irrelevance of the
  -- transported proofs and the identity laws.
  mutual
    in-fam-tree-nat : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                      (df : DecoF fm d d') {w₁ w₂ : S'.W ∣ Q ∣ ρ'} {a₁ a₂}
                      (p : Fδ'.E.W≈ w₁ w₂ a₁ a₂) →
                      (in-fam-tree df w₂ a₂ ∘ Fδ'.fib-subst Q d' {w₁ = w₁} {w₂ = w₂} p)
                        ≈ (Fδ.fib-subst Q d {w₁ = proj₁ (in-tree fm w₁ a₁)}
                             {w₂ = proj₁ (in-tree fm w₂ a₂)}
                             (in-tree-resp fm {w₁ = w₁} {w₂ = w₂} p)
                             ∘ in-fam-tree df w₁ a₁)
    in-fam-tree-nat {Q = Q} df {S'.sup s₁} {S'.sup s₂} p =
      in-fam-shape-nat Q (dbind Q df) p

    in-fam-shape-nat : ∀ {j} (R : Poly-C j) {ηA ηB} {fm : IX.FMor ∣ P ∣ ηA ηB} {d d'}
                       (df : DecoF fm d d') {s₁ s₂ : S'.Shape ∣ R ∣ ηB} {a₁ a₂}
                       (p : Fδ'.E.Sh≈ ∣ R ∣ ηB s₁ s₂ a₁ a₂) →
                       (in-fam-shape R df s₂ a₂ ∘ Fδ'.fib-shape-subst R d' p)
                         ≈ (Fδ.fib-shape-subst R d (in-shape-resp ∣ R ∣ fm p)
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
                    (v : Fin k) {s₁ s₂ : S'.El (ρ' v)} {a₁ a₂}
                    (p : Fδ'.E.El≈ (ρ' v) s₁ s₂ a₁ a₂) →
                    (in-fam-el df v s₂ a₂ ∘ Fδ'.fib-el-subst (ρ' v) (d' v) p)
                      ≈ (Fδ.fib-el-subst (ρ v) (d v) (in-el-resp fm v p)
                           ∘ in-fam-el df v s₁ a₁)
    in-fam-el-nat dbase        zero    p = ≈-trans id-left (≈-sym id-right)
    in-fam-el-nat dbase        (suc i) p = ≈-trans id-left (≈-sym id-right)
    in-fam-el-nat (dbind Q df) zero    {w₁} {w₂} p = in-fam-tree-nat df {w₁ = w₁} {w₂ = w₂} p
    in-fam-el-nat (dbind Q df) (suc v) p = in-fam-el-nat df v p

  ------------------------------------------------------------------------------
  -- Bridge fobj's native structure to shapes with assignments over the
  -- extended environment: leaves become the one-position shape with the
  -- element as its assignment, and an inner μ is the identity, both sides
  -- being the same trees.
  ------------------------------------------------------------------------------
  embed-idx : (Q : Poly-C (suc n)) → fobj μObj Q δᵢ .idx .Setoid.Carrier →
              Tᵢ.TreeSh ∣ Q ∣ IX.params
  embed-idx (const A) a = tt , λ _ → a
  embed-idx (var v)   a = tt , λ _ → a
  embed-idx (Q₁ + Q₂) (inj₁ x) = let (s , a) = embed-idx Q₁ x in inj₁ s , a
  embed-idx (Q₁ + Q₂) (inj₂ y) = let (s , a) = embed-idx Q₂ y in inj₂ s , a
  embed-idx (Q₁ × Q₂) (x , y) =
    let (s₁ , a₁) = embed-idx Q₁ x
        (s₂ , a₂) = embed-idx Q₂ y
    in (s₁ , s₂) , λ { (inj₁ p) → a₁ p ; (inj₂ p) → a₂ p }
  embed-idx (μ Q')    t = t

  embed-resp : (Q : Poly-C (suc n)) {x y : fobj μObj Q δᵢ .idx .Setoid.Carrier} →
               Setoid._≈_ (fobj μObj Q δᵢ .idx) x y →
               Eᵢ.Sh≈ ∣ Q ∣ IX.params (proj₁ (embed-idx Q x)) (proj₁ (embed-idx Q y))
                 (proj₂ (embed-idx Q x)) (proj₂ (embed-idx Q y))
  embed-resp (const A) p = p
  embed-resp (var v)   p = p
  embed-resp (Q₁ + Q₂) {inj₁ _} {inj₁ _} p = embed-resp Q₁ p
  embed-resp (Q₁ + Q₂) {inj₂ _} {inj₂ _} p = embed-resp Q₂ p
  embed-resp (Q₁ × Q₂) {_ , _} {_ , _} (p₁ , p₂) = embed-resp Q₁ p₁ , embed-resp Q₂ p₂
  embed-resp (μ Q')    p = p

  embed-fam : (Q : Poly-C (suc n)) (x : fobj μObj Q δᵢ .idx .Setoid.Carrier) →
              fobj μObj Q δᵢ .fam .fm x ⇒
                Fδ'.fib-shape Q (λ v → lift tt) (proj₁ (embed-idx Q x)) (proj₂ (embed-idx Q x))
  embed-fam (const A) a = id _
  embed-fam (var v)   a = id _
  embed-fam (Q₁ + Q₂) (inj₁ x) = embed-fam Q₁ x
  embed-fam (Q₁ + Q₂) (inj₂ y) = embed-fam Q₂ y
  embed-fam (Q₁ × Q₂) (x , y) = prod-m (embed-fam Q₁ x) (embed-fam Q₂ y)
  embed-fam (μ Q')    t = id _

  embed-fam-natural : (Q : Poly-C (suc n)) {x y : fobj μObj Q δᵢ .idx .Setoid.Carrier}
                      (e : Setoid._≈_ (fobj μObj Q δᵢ .idx) x y) →
                      (embed-fam Q y ∘ fobj μObj Q δᵢ .fam .subst e)
                        ≈ (Fδ'.fib-shape-subst Q (λ v → lift tt) (embed-resp Q e) ∘ embed-fam Q x)
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
  -- The algebra map as a Fam-morphism: embed fobj's element and assemble; on
  -- fibres, the two actions compose, each built from identities and products.
  ------------------------------------------------------------------------------
  open prop-setoid._⇒_

  inMor : Fam𝒞._⇒_ (fobj μObj P δᵢ) (μObj P δ)
  inMor .idxf .func x = inMap (embed-idx P x)
  inMor .idxf .func-resp-≈ p = in-shape-resp ∣ P ∣ IX.fbase (embed-resp P p)
  inMor .famf .transf x =
    in-fam-shape P dbase (proj₁ (embed-idx P x)) (proj₂ (embed-idx P x)) ∘ embed-fam P x
  inMor .famf .natural {x₁} {x₂} e =
    ≈-trans (assoc _ _ _)
      (≈-trans (∘-cong₂ (embed-fam-natural P e))
        (≈-trans (≈-sym (assoc _ _ _))
          (≈-trans (∘-cong₁ (in-fam-shape-nat P dbase (embed-resp P e)))
            (assoc _ _ _))))

------------------------------------------------------------------------------
-- Reindexing commutes with the algebra map: assembling and then reindexing
-- along g equals reindexing the unfolding pointwise (along g extended by the
-- reindexing of whole trees at the α-entry) and then assembling. Leaf-refl
-- induction; the α-case is definitional on both sides.
------------------------------------------------------------------------------
module ReindexInMap {n} (δ δ' : Fin n → Obj) (g : ∀ i → δ i .idx prop-setoid.⇒ δ' i .idx)
                    (P : Poly-C (suc n)) where
  open prop-setoid._⇒_

  module I  = InMap P δ
  module I' = InMap P δ'
  module Rg = IX.Reindex g

  ĝ : ∀ v → I.ιᵢ v prop-setoid.⇒ I'.ιᵢ v
  ĝ zero .func t = Rg.reindex t
  ĝ zero .func-resp-≈ {t₁} {t₂} p = Rg.reindex-resp {t₁ = t₁} {t₂ = t₂} p
  ĝ (suc i) = g i

  module Rĝ = IX.Reindex ĝ

  mutual
    ri-tree : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (w : I.S'.W Q ρ')
              (a : I.Tᵢ.Assign w) →
              I'.E.Tree≈ (Rg.reindex (I.in-tree fm w a))
                (I'.in-tree fm w (λ p → Rĝ.reindexIx (I.S'.labelW w p) (a p)))
    ri-tree {Q = Q} fm (I.S'.sup s) a = ri-shape Q (IX.fbind Q fm) s a

    ri-shape : ∀ {j} (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB) (s : I.S'.Shape R ηB)
               (a : I.Tᵢ.AssignSh R ηB s) →
               I'.E.Sh≈ R ηA
                 (proj₁ (I.in-shape R fm s a))
                 (proj₁ (I'.in-shape R fm s (λ p → Rĝ.reindexIx (I.S'.labelSh R ηB s p) (a p))))
                 (λ p → Rg.reindexIx (I.S.labelSh R ηA (proj₁ (I.in-shape R fm s a)) p)
                          (proj₂ (I.in-shape R fm s a) p))
                 (proj₂ (I'.in-shape R fm s (λ p → Rĝ.reindexIx (I.S'.labelSh R ηB s p) (a p))))
    ri-shape (const S) fm s a = S .Setoid.isEquivalence .refl
    ri-shape (var v)   fm s a = ri-el fm v s a
    ri-shape (R₁ + R₂) fm (inj₁ s) a = ri-shape R₁ fm s a
    ri-shape (R₁ + R₂) fm (inj₂ s) a = ri-shape R₂ fm s a
    ri-shape (R₁ × R₂) fm (s₁ , s₂) a =
      ri-shape R₁ fm s₁ (λ p → a (inj₁ p)) , ri-shape R₂ fm s₂ (λ p → a (inj₂ p))
    ri-shape (μ Q')    fm s a = ri-tree fm s a

    ri-el : ∀ {k} {ρ ρ'} (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k) (s : I.S'.El (ρ' v))
            (a : I.Tᵢ.AssignEl (ρ' v) s) →
            I'.E.El≈ (ρ v)
              (proj₁ (I.in-el fm v s a))
              (proj₁ (I'.in-el fm v s (λ p → Rĝ.reindexIx (I.S'.labelEl (ρ' v) s p) (a p))))
              (λ p → Rg.reindexIx (I.S.labelEl (ρ v) (proj₁ (I.in-el fm v s a)) p)
                       (proj₂ (I.in-el fm v s a) p))
              (proj₂ (I'.in-el fm v s (λ p → Rĝ.reindexIx (I.S'.labelEl (ρ' v) s p) (a p))))
    ri-el IX.fbase        zero    s a =
      I'.EE.W≈-refl (proj₁ (Rg.reindex (a tt))) (proj₂ (Rg.reindex (a tt)))
    ri-el IX.fbase        (suc i) s a = δ' i .idx .Setoid.isEquivalence .refl
    ri-el (IX.fbind Q fm) zero    w a = ri-tree fm w a
    ri-el (IX.fbind Q fm) (suc v) s a = ri-el fm v s a

  reindex-inMap : (t : I.Tᵢ.TreeSh ∣ P ∣ IX.params) →
                  I'.E.Tree≈ (Rg.reindex (I.inMap t))
                    (I'.inMap (Rĝ.reindexSh {Q = ∣ P ∣} {η = IX.params} t))
  reindex-inMap (s , a) = ri-shape ∣ P ∣ IX.fbase s a
