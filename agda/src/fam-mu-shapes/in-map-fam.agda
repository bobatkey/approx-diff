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

  -- The canonical root decoration: parameters carry none.
  d₀ : ∀ i → Fδ.DecoAssign (IX.params i)
  d₀ i = lift tt

  -- Decorations of the two sides of an FMor translation.
  data DecoF : ∀ {k} {ρ : Fin k → Fin n ⊎ Sh.Sort n} {ρ'} → IX.FMor ∣ P ∣ ρ ρ' →
               ((v : Fin k) → Fδ.DecoAssign (ρ v)) →
               ((v : Fin k) → Fδ'.DecoAssign (ρ' v)) → Set ℓD where
    dbase : DecoF IX.fbase (Fδ.deco-ext P d₀) (λ v → lift tt)
    dbind : ∀ {k} {ρ ρ'} {fm : IX.FMor ∣ P ∣ ρ ρ'} {d d'} (Q : Poly-C (suc k)) →
            DecoF fm d d' →
            DecoF (IX.fbind ∣ Q ∣ fm) (Fδ.deco-ext Q d) (Fδ'.deco-ext Q d')

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
