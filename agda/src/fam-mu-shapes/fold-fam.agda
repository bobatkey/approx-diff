{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The fold as a Fam-morphism in an ambient context Γ. The index part is the
-- Γ-threaded fold with the algebra's index map behind the reverse bridges
-- (uncoerce to the object-level environment spelling, then unembed into
-- fobj's native structure); the fibre part threads the Γ-fibre, consuming
-- the algebra's fibre map at the root and pairing through the recursion.
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
import fam-mu-shapes.in-map-fam

module fam-mu-shapes.fold-fam {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CP : HasProducts 𝒞) where

open fam-mu-shapes.in-map-fam os es T CP public

module FoldFam {n} (Γ A : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj) where
  ι : Fin n → Setoid os (os ⊔ es)
  ι i = δ i .idx

  δf : ∀ i → Fam (ι i) 𝒞
  δf i = δ i .fam

  module F = IX.Fold ι (Γ .idx) (A .idx) ∣ P ∣
  module Fδ = Fibre ι δf

  δᴬF : Fin (suc n) → Obj
  δᴬF = extend δ A

  ιᴬμ : Fin (suc n) → Setoid os (os ⊔ es)
  ιᴬμ v = δᴬF v .idx

  module FA' = Fibre F.ι' (extendF δf (A .fam))
  module FAμ = Fibre ιᴬμ (λ v → δᴬF v .fam)
  module EAμ = Sh.TreeEq ιᴬμ (λ v → Setoid._≈_ (ιᴬμ v))

  open DecoDefs P
  open Decos (suc n) using (mkDeco)
  open prop-setoid._⇒_

  ------------------------------------------------------------------------------
  -- Reverse bridges: from the fold-target spelling ι[α ↦ Y] to the
  -- object-level spelling, and from shapes with assignments back to fobj's
  -- native structure. Mirror images of the coercion and embed layers.
  ------------------------------------------------------------------------------
  uncoeIx : (l : Setoid os (os ⊔ es) ⊎ Fin (suc n)) → Sh.Trees.Ix F.ι' l → Sh.Trees.Ix ιᴬμ l
  uncoeIx (inj₁ S)       x = x
  uncoeIx (inj₂ zero)    x = x
  uncoeIx (inj₂ (suc i)) x = x

  uncoe-treeSh : ∀ {k} (Q : Sh.Poly k) (η̄ : Fin k → Fin (suc n) ⊎ Sh.Sort (suc n)) →
                 Sh.Trees.TreeSh F.ι' Q η̄ → Sh.Trees.TreeSh ιᴬμ Q η̄
  uncoe-treeSh Q η̄ (s , a) = s , λ p → uncoeIx (F.S'.labelSh Q η̄ s p) (a p)

  mutual
    uncoe-W-resp : ∀ {k} {Q : Sh.Poly (suc k)} {ρ̄} {w₁ w₂ : F.S'.W Q ρ̄} {a₁ a₂} →
                   F.E'.W≈ w₁ w₂ a₁ a₂ →
                   EAμ.W≈ w₁ w₂ (λ p → uncoeIx (F.S'.labelW w₁ p) (a₁ p))
                     (λ p → uncoeIx (F.S'.labelW w₂ p) (a₂ p))
    uncoe-W-resp {Q = Q} {ρ̄} {F.S'.sup s₁} {F.S'.sup s₂} p =
      uncoe-Sh-resp Q (extend ρ̄ (inj₂ (Sh.mkSort Q ρ̄))) p

    uncoe-Sh-resp : ∀ {k} (Q : Sh.Poly k) (η̄ : Fin k → Fin (suc n) ⊎ Sh.Sort (suc n))
                    {s₁ s₂ : F.S'.Shape Q η̄} {a₁ a₂} → F.E'.Sh≈ Q η̄ s₁ s₂ a₁ a₂ →
                    EAμ.Sh≈ Q η̄ s₁ s₂ (λ p → uncoeIx (F.S'.labelSh Q η̄ s₁ p) (a₁ p))
                      (λ p → uncoeIx (F.S'.labelSh Q η̄ s₂ p) (a₂ p))
    uncoe-Sh-resp (const S) η̄ p = p
    uncoe-Sh-resp (var j)   η̄ p = uncoe-El-resp (η̄ j) p
    uncoe-Sh-resp (Q₁ + Q₂) η̄ {inj₁ _} {inj₁ _} p = uncoe-Sh-resp Q₁ η̄ p
    uncoe-Sh-resp (Q₁ + Q₂) η̄ {inj₂ _} {inj₂ _} p = uncoe-Sh-resp Q₂ η̄ p
    uncoe-Sh-resp (Q₁ × Q₂) η̄ {_ , _} {_ , _} (p , q) = uncoe-Sh-resp Q₁ η̄ p , uncoe-Sh-resp Q₂ η̄ q
    uncoe-Sh-resp (μ Q')    η̄ {w₁} {w₂} p = uncoe-W-resp {w₁ = w₁} {w₂ = w₂} p

    uncoe-El-resp : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) {s₁ s₂ : F.S'.El r} {a₁ a₂} →
                    F.E'.El≈ r s₁ s₂ a₁ a₂ →
                    EAμ.El≈ r s₁ s₂ (λ p → uncoeIx (F.S'.labelEl r s₁ p) (a₁ p))
                      (λ p → uncoeIx (F.S'.labelEl r s₂ p) (a₂ p))
    uncoe-El-resp (inj₁ zero)    p = p
    uncoe-El-resp (inj₁ (suc i)) p = p
    uncoe-El-resp (inj₂ (Sh.mkSort Q ρ̄)) {w₁} {w₂} p = uncoe-W-resp {w₁ = w₁} {w₂ = w₂} p

  mutual
    uncoe-fam-tree : ∀ {k} {Q : Poly-C (suc k)} {ρ̄} (d : ∀ v → Decos.DecoAssign (suc n) (ρ̄ v))
                     (w : F.S'.W ∣ Q ∣ ρ̄) (a : Sh.Trees.Assign F.ι' w) →
                     FA'.fib Q d w a ⇒ FAμ.fib Q d w (λ p → uncoeIx (F.S'.labelW w p) (a p))
    uncoe-fam-tree {Q = Q} d (F.S'.sup s) a = uncoe-fam-shape Q (FA'.deco-ext Q d) s a

    uncoe-fam-shape : ∀ {j} (Q : Poly-C j) {η̄} (d : ∀ v → Decos.DecoAssign (suc n) (η̄ v))
                      (s : F.S'.Shape ∣ Q ∣ η̄) (a : Sh.Trees.AssignSh F.ι' ∣ Q ∣ η̄ s) →
                      FA'.fib-shape Q d s a ⇒
                        FAμ.fib-shape Q d s (λ p → uncoeIx (F.S'.labelSh ∣ Q ∣ η̄ s p) (a p))
    uncoe-fam-shape (const A') d s a = id _
    uncoe-fam-shape (var j)    d s a = uncoe-fam-el _ (d j) s a
    uncoe-fam-shape (Q₁ + Q₂)  d (inj₁ s) a = uncoe-fam-shape Q₁ d s a
    uncoe-fam-shape (Q₁ + Q₂)  d (inj₂ s) a = uncoe-fam-shape Q₂ d s a
    uncoe-fam-shape (Q₁ × Q₂)  d (s₁ , s₂) a =
      prod-m (uncoe-fam-shape Q₁ d s₁ (λ p → a (inj₁ p))) (uncoe-fam-shape Q₂ d s₂ (λ p → a (inj₂ p)))
    uncoe-fam-shape (μ Q')     d s a = uncoe-fam-tree d s a

    uncoe-fam-el : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) (dr : Decos.DecoAssign (suc n) r)
                   (s : F.S'.El r) (a : Sh.Trees.AssignEl F.ι' r s) →
                   FA'.fib-el r dr s a ⇒ FAμ.fib-el r dr s (λ p → uncoeIx (F.S'.labelEl r s p) (a p))
    uncoe-fam-el (inj₁ zero)    _ s a = id _
    uncoe-fam-el (inj₁ (suc i)) _ s a = id _
    uncoe-fam-el (inj₂ _) (mkDeco Q ρd) w a = uncoe-fam-tree ρd w a

  unembed-idx : (Q : Poly-C (suc n)) → Sh.Trees.TreeSh ιᴬμ ∣ Q ∣ IX.params →
                fobj μObj Q δᴬF .idx .Setoid.Carrier
  unembed-idx (const A') (s , a) = a tt
  unembed-idx (var v)    (s , a) = a tt
  unembed-idx (Q₁ + Q₂)  (inj₁ s , a) = inj₁ (unembed-idx Q₁ (s , a))
  unembed-idx (Q₁ + Q₂)  (inj₂ s , a) = inj₂ (unembed-idx Q₂ (s , a))
  unembed-idx (Q₁ × Q₂)  ((s₁ , s₂) , a) =
    unembed-idx Q₁ (s₁ , λ p → a (inj₁ p)) , unembed-idx Q₂ (s₂ , λ p → a (inj₂ p))
  unembed-idx (μ Q')     t = t

  unembed-resp : ∀ (Q : Poly-C (suc n)) {s₁ s₂ : F.S'.Shape ∣ Q ∣ IX.params} {a₁ a₂} →
                 EAμ.Sh≈ ∣ Q ∣ IX.params s₁ s₂ a₁ a₂ →
                 Setoid._≈_ (fobj μObj Q δᴬF .idx) (unembed-idx Q (s₁ , a₁)) (unembed-idx Q (s₂ , a₂))
  unembed-resp (const A') p = p
  unembed-resp (var v)    p = p
  unembed-resp (Q₁ + Q₂)  {inj₁ _} {inj₁ _} p = unembed-resp Q₁ p
  unembed-resp (Q₁ + Q₂)  {inj₂ _} {inj₂ _} p = unembed-resp Q₂ p
  unembed-resp (Q₁ × Q₂)  {_ , _} {_ , _} (p₁ , p₂) = unembed-resp Q₁ p₁ , unembed-resp Q₂ p₂
  unembed-resp (μ Q')     p = p

  unembed-fam : (Q : Poly-C (suc n)) (s : F.S'.Shape ∣ Q ∣ IX.params)
                (a : Sh.Trees.AssignSh ιᴬμ ∣ Q ∣ IX.params s) →
                FAμ.fib-shape Q (λ v → lift tt) s a ⇒ fobj μObj Q δᴬF .fam .fm (unembed-idx Q (s , a))
  unembed-fam (const A') s a = id _
  unembed-fam (var v)    s a = id _
  unembed-fam (Q₁ + Q₂)  (inj₁ s) a = unembed-fam Q₁ s a
  unembed-fam (Q₁ + Q₂)  (inj₂ s) a = unembed-fam Q₂ s a
  unembed-fam (Q₁ × Q₂)  (s₁ , s₂) a =
    prod-m (unembed-fam Q₁ s₁ (λ p → a (inj₁ p))) (unembed-fam Q₂ s₂ (λ p → a (inj₂ p)))
  unembed-fam (μ Q')     t a = id _

  unembed-fam-natural : ∀ (Q : Poly-C (suc n)) {s₁ s₂ : F.S'.Shape ∣ Q ∣ IX.params} {a₁ a₂}
                        (p : EAμ.Sh≈ ∣ Q ∣ IX.params s₁ s₂ a₁ a₂) →
                        (unembed-fam Q s₂ a₂ ∘ FAμ.fib-shape-subst Q (λ v → lift tt) p)
                          ≈ (fobj μObj Q δᴬF .fam .subst (unembed-resp Q p) ∘ unembed-fam Q s₁ a₁)
  unembed-fam-natural (const A') p = ≈-trans id-left (≈-sym id-right)
  unembed-fam-natural (var v)    p = ≈-trans id-left (≈-sym id-right)
  unembed-fam-natural (Q₁ + Q₂)  {inj₁ _} {inj₁ _} p = unembed-fam-natural Q₁ p
  unembed-fam-natural (Q₁ + Q₂)  {inj₂ _} {inj₂ _} p = unembed-fam-natural Q₂ p
  unembed-fam-natural (Q₁ × Q₂)  {_ , _} {_ , _} (p₁ , p₂) =
    ≈-trans (≈-sym (prod-m-comp _ _ _ _))
      (≈-trans (prod-m-cong (unembed-fam-natural Q₁ p₁) (unembed-fam-natural Q₂ p₂))
        (prod-m-comp _ _ _ _))
  unembed-fam-natural (μ Q')     p = ≈-trans id-left (≈-sym id-right)

  ------------------------------------------------------------------------------
  -- The fibre fold, threading the Γ-fibre: the algebra's fibre map is
  -- consumed at the root behind the reverse bridges; the recursion drops the
  -- Γ-fibre at leaves and duplicates it at pairs.
  ------------------------------------------------------------------------------
  module _ (alg : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (fobj μObj P δᴬF)) A) where
    algIx : Γ .idx .Setoid.Carrier → F.T'.TreeSh ∣ P ∣ IX.params → A .idx .Setoid.Carrier
    algIx γ t = alg .idxf .func (γ , unembed-idx P (uncoe-treeSh ∣ P ∣ IX.params t))

    algIx-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                 {s₁ s₂ : F.S'.Shape ∣ P ∣ IX.params} {a₁ a₂} →
                 F.E'.Sh≈ ∣ P ∣ IX.params s₁ s₂ a₁ a₂ →
                 Setoid._≈_ (A .idx) (algIx γ₁ (s₁ , a₁)) (algIx γ₂ (s₂ , a₂))
    algIx-resp γ≈ p = alg .idxf .func-resp-≈ (γ≈ , unembed-resp P (uncoe-Sh-resp ∣ P ∣ IX.params p))

    -- The root bridge on fibres, from the fold-target world to fobj's fibre.
    rootB : (γ : Γ .idx .Setoid.Carrier) (s : F.S.Shape ∣ P ∣ (IX.η₀ ∣ P ∣))
            (a : F.T.AssignSh ∣ P ∣ (IX.η₀ ∣ P ∣) s) →
            FA'.fib-shape P (λ v → lift tt) (proj₁ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a))
              (proj₂ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a)) ⇒
            fobj μObj P δᴬF .fam .fm (unembed-idx P (uncoe-treeSh ∣ P ∣ IX.params (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a)))
    rootB γ s a =
      unembed-fam P (proj₁ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a))
        (λ p → uncoeIx (F.S'.labelSh ∣ P ∣ IX.params (proj₁ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a)) p)
                 (proj₂ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a) p))
        ∘ uncoe-fam-shape P (λ v → lift tt) (proj₁ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a))
            (proj₂ (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a))

    mutual
      fold-fam : (γ : Γ .idx .Setoid.Carrier) (w : F.S.W ∣ P ∣ IX.params) (a : F.T.Assign w) →
                 prod (Γ .fam .fm γ) (Fδ.fib P d₀ w a) ⇒ A .fam .fm (F.fold algIx γ w a)
      fold-fam γ (F.S.sup s) a =
        alg .famf .transf (γ , unembed-idx P (uncoe-treeSh ∣ P ∣ IX.params (F.fold-shape algIx γ ∣ P ∣ IX.fbase s a)))
          ∘ pair p₁ ((rootB γ s a) ∘ fold-shape-fam γ P dbase s a)

      fold-tree-fam : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                      (γ : Γ .idx .Setoid.Carrier) (df : DecoF fmr d d')
                      (w : F.S.W ∣ Q ∣ ρ) (a : F.T.Assign w) →
                      prod (Γ .fam .fm γ) (Fδ.fib Q d w a) ⇒
                        FA'.fib Q d' (proj₁ (F.fold-reindex algIx γ fmr w a)) (proj₂ (F.fold-reindex algIx γ fmr w a))
      fold-tree-fam {Q = Q} γ df (F.S.sup s) a = fold-shape-fam γ Q (dbind Q df) s a

      fold-shape-fam : ∀ {j} (γ : Γ .idx .Setoid.Carrier) (R : Poly-C j) {ηA ηB}
                       {fmr : IX.FMor ∣ P ∣ ηA ηB} {d d'} (df : DecoF fmr d d')
                       (s : F.S.Shape ∣ R ∣ ηA) (a : F.T.AssignSh ∣ R ∣ ηA s) →
                       prod (Γ .fam .fm γ) (Fδ.fib-shape R d s a) ⇒
                         FA'.fib-shape R d' (proj₁ (F.fold-shape algIx γ ∣ R ∣ fmr s a))
                           (proj₂ (F.fold-shape algIx γ ∣ R ∣ fmr s a))
      fold-shape-fam γ (const A') df s a = p₂
      fold-shape-fam γ (var v)    df s a = fold-apply-fam γ df v s a
      fold-shape-fam γ (R₁ + R₂)  df (inj₁ s) a = fold-shape-fam γ R₁ df s a
      fold-shape-fam γ (R₁ + R₂)  df (inj₂ s) a = fold-shape-fam γ R₂ df s a
      fold-shape-fam γ (R₁ × R₂)  df (s₁ , s₂) a =
        strong-prod-m (fold-shape-fam γ R₁ df s₁ (λ p → a (inj₁ p)))
          (fold-shape-fam γ R₂ df s₂ (λ p → a (inj₂ p)))
      fold-shape-fam γ (μ Q')     df s a = fold-tree-fam γ df s a

      fold-apply-fam : ∀ {k} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                       (γ : Γ .idx .Setoid.Carrier) (df : DecoF fmr d d') (v : Fin k)
                       (s : F.S.El (ρ v)) (a : F.T.AssignEl (ρ v) s) →
                       prod (Γ .fam .fm γ) (Fδ.fib-el (ρ v) (d v) s a) ⇒
                         FA'.fib-el (ρ' v) (d' v) (proj₁ (F.fold-apply algIx γ fmr v s a))
                           (proj₂ (F.fold-apply algIx γ fmr v s a))
      fold-apply-fam γ dbase        zero    w a = fold-fam γ w a
      fold-apply-fam γ dbase        (suc i) s a = p₂
      fold-apply-fam γ (dbind Q df) zero    w a = fold-tree-fam γ df w a
      fold-apply-fam γ (dbind Q df) (suc v) s a = fold-apply-fam γ df v s a

    mutual
      uncoe-fam-tree-nat : ∀ {k} {Q : Poly-C (suc k)} {ρ̄} (d : ∀ v → Decos.DecoAssign (suc n) (ρ̄ v))
                           {w₁ w₂ : F.S'.W ∣ Q ∣ ρ̄} {a₁ a₂} (p : F.E'.W≈ w₁ w₂ a₁ a₂) →
                           (uncoe-fam-tree d w₂ a₂ ∘ FA'.fib-subst Q d {w₁ = w₁} {w₂ = w₂} p)
                             ≈ (FAμ.fib-subst Q d {w₁ = w₁} {w₂ = w₂} (uncoe-W-resp {w₁ = w₁} {w₂ = w₂} p)
                                  ∘ uncoe-fam-tree d w₁ a₁)
      uncoe-fam-tree-nat {Q = Q} d {F.S'.sup s₁} {F.S'.sup s₂} p =
        uncoe-fam-shape-nat Q (FA'.deco-ext Q d) p

      uncoe-fam-shape-nat : ∀ {j} (Q : Poly-C j) {η̄} (d : ∀ v → Decos.DecoAssign (suc n) (η̄ v))
                            {s₁ s₂ : F.S'.Shape ∣ Q ∣ η̄} {a₁ a₂} (p : F.E'.Sh≈ ∣ Q ∣ η̄ s₁ s₂ a₁ a₂) →
                            (uncoe-fam-shape Q d s₂ a₂ ∘ FA'.fib-shape-subst Q d p)
                              ≈ (FAμ.fib-shape-subst Q d (uncoe-Sh-resp ∣ Q ∣ η̄ p)
                                   ∘ uncoe-fam-shape Q d s₁ a₁)
      uncoe-fam-shape-nat (const A') d p = ≈-trans id-left (≈-sym id-right)
      uncoe-fam-shape-nat (var v)    d p = uncoe-fam-el-nat _ (d v) p
      uncoe-fam-shape-nat (Q₁ + Q₂)  d {inj₁ _} {inj₁ _} p = uncoe-fam-shape-nat Q₁ d p
      uncoe-fam-shape-nat (Q₁ + Q₂)  d {inj₂ _} {inj₂ _} p = uncoe-fam-shape-nat Q₂ d p
      uncoe-fam-shape-nat (Q₁ × Q₂)  d {_ , _} {_ , _} (p₁ , p₂) =
        ≈-trans (≈-sym (prod-m-comp _ _ _ _))
          (≈-trans (prod-m-cong (uncoe-fam-shape-nat Q₁ d p₁) (uncoe-fam-shape-nat Q₂ d p₂))
            (prod-m-comp _ _ _ _))
      uncoe-fam-shape-nat (μ Q')     d {w₁} {w₂} p = uncoe-fam-tree-nat d {w₁ = w₁} {w₂ = w₂} p

      uncoe-fam-el-nat : ∀ (r : Fin (suc n) ⊎ Sh.Sort (suc n)) (dr : Decos.DecoAssign (suc n) r)
                         {s₁ s₂ : F.S'.El r} {a₁ a₂} (p : F.E'.El≈ r s₁ s₂ a₁ a₂) →
                         (uncoe-fam-el r dr s₂ a₂ ∘ FA'.fib-el-subst r dr p)
                           ≈ (FAμ.fib-el-subst r dr (uncoe-El-resp r p) ∘ uncoe-fam-el r dr s₁ a₁)
      uncoe-fam-el-nat (inj₁ zero)    _ p = ≈-trans id-left (≈-sym id-right)
      uncoe-fam-el-nat (inj₁ (suc i)) _ p = ≈-trans id-left (≈-sym id-right)
      uncoe-fam-el-nat (inj₂ _) (mkDeco Q ρd) {w₁} {w₂} p = uncoe-fam-tree-nat ρd {w₁ = w₁} {w₂ = w₂} p

    rootB-nat : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                {s₁ s₂ : F.S.Shape ∣ P ∣ (IX.η₀ ∣ P ∣)} {a₁ a₂}
                (p : F.E.Sh≈ ∣ P ∣ (IX.η₀ ∣ P ∣) s₁ s₂ a₁ a₂) →
                (rootB γ₂ s₂ a₂ ∘ FA'.fib-shape-subst P (λ v → lift tt)
                   (F.fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p))
                  ≈ (fobj μObj P δᴬF .fam .subst
                       (unembed-resp P (uncoe-Sh-resp ∣ P ∣ IX.params
                          (F.fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p)))
                     ∘ rootB γ₁ s₁ a₁)
    rootB-nat γ≈ p =
      ≈-trans (assoc _ _ _)
        (≈-trans (∘-cong₂ (uncoe-fam-shape-nat P (λ v → lift tt)
                             (F.fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p)))
          (≈-trans (≈-sym (assoc _ _ _))
            (≈-trans (∘-cong₁ (unembed-fam-natural P (uncoe-Sh-resp ∣ P ∣ IX.params
                                 (F.fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p))))
              (assoc _ _ _))))

    mutual
      fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                         {w₁ w₂ : F.S.W ∣ P ∣ IX.params} {a₁ a₂} (p : F.E.W≈ w₁ w₂ a₁ a₂) →
                         (fold-fam γ₂ w₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-subst P d₀ {w₁ = w₁} {w₂ = w₂} p))
                           ≈ (A .fam .subst (F.fold-resp algIx algIx-resp γ≈ {w₁ = w₁} {w₂ = w₂} p)
                                ∘ fold-fam γ₁ w₁ a₁)
      fold-fam-natural γ≈ {F.S.sup s₁} {F.S.sup s₂} p =
        ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (pair-natural _ _ _))
            (≈-trans (∘-cong₂ (pair-cong (pair-p₁ _ _)
                        (≈-trans (assoc _ _ _)
                          (≈-trans (∘-cong₂ (fold-shape-fam-natural γ≈ P dbase p))
                            (≈-trans (≈-sym (assoc _ _ _))
                              (≈-trans (∘-cong₁ (rootB-nat γ≈ p)) (assoc _ _ _)))))))
              (≈-trans (∘-cong₂ (≈-sym (pair-compose _ _ _ _)))
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong₁ (alg .famf .natural
                              (γ≈ , unembed-resp P (uncoe-Sh-resp ∣ P ∣ IX.params
                                       (F.fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p)))))
                    (assoc _ _ _))))))

      fold-tree-fam-natural : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                              {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (df : DecoF fmr d d')
                              {w₁ w₂ : F.S.W ∣ Q ∣ ρ} {a₁ a₂} (p : F.E.W≈ w₁ w₂ a₁ a₂) →
                              (fold-tree-fam γ₂ df w₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-subst Q d {w₁ = w₁} {w₂ = w₂} p))
                                ≈ (FA'.fib-subst Q d' {w₁ = proj₁ (F.fold-reindex algIx γ₁ fmr w₁ a₁)}
                                     {w₂ = proj₁ (F.fold-reindex algIx γ₂ fmr w₂ a₂)}
                                     (F.fold-reindex-resp algIx algIx-resp γ≈ fmr {w₁ = w₁} {w₂ = w₂} p)
                                   ∘ fold-tree-fam γ₁ df w₁ a₁)
      fold-tree-fam-natural {Q = Q} γ≈ df {F.S.sup s₁} {F.S.sup s₂} p =
        fold-shape-fam-natural γ≈ Q (dbind Q df) p

      fold-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (R : Poly-C j)
                               {ηA ηB} {fmr : IX.FMor ∣ P ∣ ηA ηB} {d d'} (df : DecoF fmr d d')
                               {s₁ s₂ : F.S.Shape ∣ R ∣ ηA} {a₁ a₂} (p : F.E.Sh≈ ∣ R ∣ ηA s₁ s₂ a₁ a₂) →
                               (fold-shape-fam γ₂ R df s₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-shape-subst R d p))
                                 ≈ (FA'.fib-shape-subst R d' (F.fold-shape-resp algIx algIx-resp γ≈ ∣ R ∣ fmr p)
                                      ∘ fold-shape-fam γ₁ R df s₁ a₁)
      fold-shape-fam-natural γ≈ (const A') df p = pair-p₂ _ _
      fold-shape-fam-natural γ≈ (var v)    df p = fold-apply-fam-natural γ≈ df v p
      fold-shape-fam-natural γ≈ (R₁ + R₂)  df {inj₁ _} {inj₁ _} p = fold-shape-fam-natural γ≈ R₁ df p
      fold-shape-fam-natural γ≈ (R₁ + R₂)  df {inj₂ _} {inj₂ _} p = fold-shape-fam-natural γ≈ R₂ df p
      fold-shape-fam-natural γ≈ (R₁ × R₂)  df {_ , _} {_ , _} (p₁ , p₂) =
        strong-prod-m-natural (fold-shape-fam-natural γ≈ R₁ df p₁) (fold-shape-fam-natural γ≈ R₂ df p₂)
      fold-shape-fam-natural γ≈ (μ Q')     df {w₁} {w₂} p = fold-tree-fam-natural γ≈ df {w₁ = w₁} {w₂ = w₂} p

      fold-apply-fam-natural : ∀ {k} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'} {γ₁ γ₂}
                               (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (df : DecoF fmr d d') (v : Fin k)
                               {s₁ s₂ : F.S.El (ρ v)} {a₁ a₂} (p : F.E.El≈ (ρ v) s₁ s₂ a₁ a₂) →
                               (fold-apply-fam γ₂ df v s₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-el-subst (ρ v) (d v) p))
                                 ≈ (FA'.fib-el-subst (ρ' v) (d' v) (F.fold-apply-resp algIx algIx-resp γ≈ fmr v p)
                                      ∘ fold-apply-fam γ₁ df v s₁ a₁)
      fold-apply-fam-natural γ≈ dbase        zero    {w₁} {w₂} p = fold-fam-natural γ≈ {w₁ = w₁} {w₂ = w₂} p
      fold-apply-fam-natural γ≈ dbase        (suc i) p = pair-p₂ _ _
      fold-apply-fam-natural γ≈ (dbind Q df) zero    {w₁} {w₂} p = fold-tree-fam-natural γ≈ df {w₁ = w₁} {w₂ = w₂} p
      fold-apply-fam-natural γ≈ (dbind Q df) (suc v) p = fold-apply-fam-natural γ≈ df v p

    foldMor : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (μObj P δ)) A
    foldMor .idxf .func (γ , t) = F.fold algIx γ (proj₁ t) (proj₂ t)
    foldMor .idxf .func-resp-≈ {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      F.fold-resp algIx algIx-resp γ≈ {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} t≈
    foldMor .famf .transf (γ , t) = fold-fam γ (proj₁ t) (proj₂ t)
    foldMor .famf .natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      fold-fam-natural γ≈ {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} t≈

-- The μ-type structure for the Fam construction.
hasMu : HasMu
hasMu .HasMu.μ-obj = μObj
hasMu .HasMu.inMap P δ = InMapFam.inMor P δ
hasMu .HasMu.⦅_⦆ {n} {Γ} {A} {P} {δ} alg = FoldFam.foldMor Γ A P δ alg
