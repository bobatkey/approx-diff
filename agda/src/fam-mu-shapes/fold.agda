{-# OPTIONS --prop --postfix-projections --safe #-}

------------------------------------------------------------------------------
-- The fold (catamorphism) of the Fam μ-type, in an ambient context Γ so no
-- exponentials are required: the algebra and the fold take a Γ-element,
-- threaded unchanged through the recursion. The algebra consumes a one-level
-- unfolding over the environment extended at α by the fold's target, whose
-- α-positions hold folded values. Inner sorts are translated to the extended
-- context by fold-shape, with FMor relating a source assignment to its
-- translation so every recursive call is structural. unembed bridges shapes
-- with assignments back to fobj's native structure, so the algebra can be
-- given as a Fam-morphism out of the polynomial interpretation; the fibre
-- fold threads the Γ-fibre, consuming the algebra's fibre map at the root
-- and pairing through the recursion.
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
import fam-mu-shapes.in-map

module fam-mu-shapes.fold {o m e} (os es : Level) {𝒞 : Category o m e}
    (T : HasTerminal 𝒞) (CP : HasProducts 𝒞) where

open fam-mu-shapes.in-map os es T CP public

module Fold {n} (Γ A : Obj) (P : Poly-C (suc n)) (δ : Fin n → Obj) where
  ι : Fin n → Setoid os (os ⊔ es)
  ι i = δ i .idx

  δf : ∀ i → Fam (ι i) 𝒞
  δf i = δ i .fam

  module S = Sh.Shapes n
  module S' = Sh.Shapes (suc n)

  -- The environment extended at α by the fold's target, and its index setoids.
  δᴬ : Fin (suc n) → Obj
  δᴬ = extend δ A

  ι' : Fin (suc n) → Setoid os (os ⊔ es)
  ι' v = δᴬ v .idx

  module T = Sh.Trees ι
  module T' = Sh.Trees ι'

  module E = Sh.TreeEq ι (λ i → Setoid._≈_ (ι i))
  module E' = Sh.TreeEq ι' (λ v → Setoid._≈_ (ι' v))

  module _ (alg : Γ .idx .Setoid.Carrier → T'.TreeSh ∣ P ∣ IX.params → A .idx .Setoid.Carrier) where
    mutual
      fold : Γ .idx .Setoid.Carrier → (w : S.W ∣ P ∣ IX.params) → T.Assign w → A .idx .Setoid.Carrier
      fold γ (S.sup s) a = alg γ (fold-shape γ ∣ P ∣ IX.fbase s a)

      fold-reindex : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} (γ : Γ .idx .Setoid.Carrier)
                     (fm : IX.FMor ∣ P ∣ ρ ρ') (w : S.W Q ρ) → T.Assign w → Σ (S'.W Q ρ') T'.Assign
      fold-reindex {Q = Q} γ fm (S.sup s) a =
        let (s' , a') = fold-shape γ Q (IX.fbind Q fm) s a in S'.sup s' , a'

      fold-shape : ∀ {j} (γ : Γ .idx .Setoid.Carrier) (R : Sh.Poly j) {ηA ηB} (fm : IX.FMor ∣ P ∣ ηA ηB)
                   (s : S.Shape R ηA) → T.AssignSh R ηA s → T'.TreeSh R ηB
      fold-shape γ (const S) fm s a = tt , a
      fold-shape γ (var v)   fm s a = fold-apply γ fm v s a
      fold-shape γ (R₁ + R₂) fm (inj₁ s) a = let (s' , a') = fold-shape γ R₁ fm s a in inj₁ s' , a'
      fold-shape γ (R₁ + R₂) fm (inj₂ s) a = let (s' , a') = fold-shape γ R₂ fm s a in inj₂ s' , a'
      fold-shape γ (R₁ × R₂) fm (s₁ , s₂) a =
        let (s₁' , a₁') = fold-shape γ R₁ fm s₁ (λ p → a (inj₁ p))
            (s₂' , a₂') = fold-shape γ R₂ fm s₂ (λ p → a (inj₂ p))
        in (s₁' , s₂') , λ { (inj₁ p) → a₁' p ; (inj₂ p) → a₂' p }
      fold-shape γ (μ Q')    fm s a = fold-reindex γ fm s a

      fold-apply : ∀ {k} {ρ ρ'} (γ : Γ .idx .Setoid.Carrier) (fm : IX.FMor ∣ P ∣ ρ ρ') (v : Fin k)
                   (s : S.El (ρ v)) → T.AssignEl (ρ v) s → Σ (S'.El (ρ' v)) (T'.AssignEl (ρ' v))
      fold-apply γ IX.fbase        zero    t a = tt , λ _ → fold γ t a
      fold-apply γ IX.fbase        (suc i) s a = tt , a
      fold-apply γ (IX.fbind Q fm) zero    w a = fold-reindex γ fm w a
      fold-apply γ (IX.fbind Q fm) (suc v) s a = fold-apply γ fm v s a

    module _ (alg-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                         {s₁ s₂ : S'.Shape ∣ P ∣ IX.params} {a₁ a₂} →
                         E'.Sh≈ ∣ P ∣ IX.params s₁ s₂ a₁ a₂ →
                         Setoid._≈_ (A .idx) (alg γ₁ (s₁ , a₁)) (alg γ₂ (s₂ , a₂))) where
      mutual
        fold-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) {w₁ w₂ : S.W ∣ P ∣ IX.params} {a₁ a₂} →
                    E.W≈ w₁ w₂ a₁ a₂ → Setoid._≈_ (A .idx) (fold γ₁ w₁ a₁) (fold γ₂ w₂ a₂)
        fold-resp γ≈ {S.sup s₁} {S.sup s₂} p = alg-resp γ≈ (fold-shape-resp γ≈ ∣ P ∣ IX.fbase p)

        fold-reindex-resp : ∀ {k} {Q : Sh.Poly (suc k)} {ρ ρ'} {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                            (fm : IX.FMor ∣ P ∣ ρ ρ') {w₁ w₂ : S.W Q ρ} {a₁ a₂} → E.W≈ w₁ w₂ a₁ a₂ →
                            E'.Tree≈ (fold-reindex γ₁ fm w₁ a₁) (fold-reindex γ₂ fm w₂ a₂)
        fold-reindex-resp {Q = Q} γ≈ fm {S.sup s₁} {S.sup s₂} p =
          fold-shape-resp γ≈ Q (IX.fbind Q fm) p

        fold-shape-resp : ∀ {j} {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (R : Sh.Poly j) {ηA ηB}
                          (fm : IX.FMor ∣ P ∣ ηA ηB) {s₁ s₂ : S.Shape R ηA} {a₁ a₂} →
                          E.Sh≈ R ηA s₁ s₂ a₁ a₂ →
                          E'.Sh≈ R ηB (proj₁ (fold-shape γ₁ R fm s₁ a₁)) (proj₁ (fold-shape γ₂ R fm s₂ a₂))
                            (proj₂ (fold-shape γ₁ R fm s₁ a₁)) (proj₂ (fold-shape γ₂ R fm s₂ a₂))
        fold-shape-resp γ≈ (const S) fm p = p
        fold-shape-resp γ≈ (var v)   fm p = fold-apply-resp γ≈ fm v p
        fold-shape-resp γ≈ (R₁ + R₂) fm {inj₁ _} {inj₁ _} p = fold-shape-resp γ≈ R₁ fm p
        fold-shape-resp γ≈ (R₁ + R₂) fm {inj₂ _} {inj₂ _} p = fold-shape-resp γ≈ R₂ fm p
        fold-shape-resp γ≈ (R₁ × R₂) fm {_ , _} {_ , _} (p , q) =
          fold-shape-resp γ≈ R₁ fm p , fold-shape-resp γ≈ R₂ fm q
        fold-shape-resp γ≈ (μ Q')    fm {w₁} {w₂} p = fold-reindex-resp γ≈ fm {w₁ = w₁} {w₂ = w₂} p

        fold-apply-resp : ∀ {k} {ρ ρ'} {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (fm : IX.FMor ∣ P ∣ ρ ρ')
                          (v : Fin k) {s₁ s₂ : S.El (ρ v)} {a₁ a₂} → E.El≈ (ρ v) s₁ s₂ a₁ a₂ →
                          E'.El≈ (ρ' v) (proj₁ (fold-apply γ₁ fm v s₁ a₁)) (proj₁ (fold-apply γ₂ fm v s₂ a₂))
                            (proj₂ (fold-apply γ₁ fm v s₁ a₁)) (proj₂ (fold-apply γ₂ fm v s₂ a₂))
        fold-apply-resp γ≈ IX.fbase        zero    {t₁} {t₂} p = fold-resp γ≈ {w₁ = t₁} {w₂ = t₂} p
        fold-apply-resp γ≈ IX.fbase        (suc i) p = p
        fold-apply-resp γ≈ (IX.fbind Q fm) zero    {w₁} {w₂} p = fold-reindex-resp γ≈ fm {w₁ = w₁} {w₂ = w₂} p
        fold-apply-resp γ≈ (IX.fbind Q fm) (suc v) p = fold-apply-resp γ≈ fm v p

  ------------------------------------------------------------------------------
  -- Bridge shapes with assignments back to fobj's native structure, so the
  -- algebra can be given as a Fam-morphism out of the polynomial
  -- interpretation.
  ------------------------------------------------------------------------------
  module Fδ = Fibre ι δf
  module FA = Fibre ι' (λ v → δᴬ v .fam)

  open DecoDefs P

  unembed-idx : (Q : Poly-C (suc n)) → T'.TreeSh ∣ Q ∣ IX.params →
                fobj μObj Q δᴬ .idx .Setoid.Carrier
  unembed-idx (const A') (s , a) = a tt
  unembed-idx (var v)    (s , a) = a tt
  unembed-idx (Q₁ + Q₂)  (inj₁ s , a) = inj₁ (unembed-idx Q₁ (s , a))
  unembed-idx (Q₁ + Q₂)  (inj₂ s , a) = inj₂ (unembed-idx Q₂ (s , a))
  unembed-idx (Q₁ × Q₂)  ((s₁ , s₂) , a) =
    unembed-idx Q₁ (s₁ , λ p → a (inj₁ p)) , unembed-idx Q₂ (s₂ , λ p → a (inj₂ p))
  unembed-idx (μ Q')     t = t

  unembed-resp : ∀ (Q : Poly-C (suc n)) {s₁ s₂ : S'.Shape ∣ Q ∣ IX.params} {a₁ a₂} →
                 E'.Sh≈ ∣ Q ∣ IX.params s₁ s₂ a₁ a₂ →
                 Setoid._≈_ (fobj μObj Q δᴬ .idx) (unembed-idx Q (s₁ , a₁)) (unembed-idx Q (s₂ , a₂))
  unembed-resp (const A') p = p
  unembed-resp (var v)    p = p
  unembed-resp (Q₁ + Q₂)  {inj₁ _} {inj₁ _} p = unembed-resp Q₁ p
  unembed-resp (Q₁ + Q₂)  {inj₂ _} {inj₂ _} p = unembed-resp Q₂ p
  unembed-resp (Q₁ × Q₂)  {_ , _} {_ , _} (p₁ , p₂) = unembed-resp Q₁ p₁ , unembed-resp Q₂ p₂
  unembed-resp (μ Q')     p = p

  unembed-fam : (Q : Poly-C (suc n)) (s : S'.Shape ∣ Q ∣ IX.params)
                (a : T'.AssignSh ∣ Q ∣ IX.params s) →
                FA.fib-shape Q (λ v → lift tt) s a ⇒ fobj μObj Q δᴬ .fam .fm (unembed-idx Q (s , a))
  unembed-fam (const A') s a = id _
  unembed-fam (var v)    s a = id _
  unembed-fam (Q₁ + Q₂)  (inj₁ s) a = unembed-fam Q₁ s a
  unembed-fam (Q₁ + Q₂)  (inj₂ s) a = unembed-fam Q₂ s a
  unembed-fam (Q₁ × Q₂)  (s₁ , s₂) a =
    prod-m (unembed-fam Q₁ s₁ (λ p → a (inj₁ p))) (unembed-fam Q₂ s₂ (λ p → a (inj₂ p)))
  unembed-fam (μ Q')     t a = id _

  unembed-fam-natural : ∀ (Q : Poly-C (suc n)) {s₁ s₂ : S'.Shape ∣ Q ∣ IX.params} {a₁ a₂}
                        (p : E'.Sh≈ ∣ Q ∣ IX.params s₁ s₂ a₁ a₂) →
                        (unembed-fam Q s₂ a₂ ∘ FA.fib-shape-subst Q (λ v → lift tt) p)
                          ≈ (fobj μObj Q δᴬ .fam .subst (unembed-resp Q p) ∘ unembed-fam Q s₁ a₁)
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
  -- consumed at the root behind unembed; the recursion drops the Γ-fibre at
  -- leaves and duplicates it at pairs.
  ------------------------------------------------------------------------------
  module _ (alg : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (fobj μObj P δᴬ)) A) where
    open prop-setoid._⇒_

    algIx : Γ .idx .Setoid.Carrier → T'.TreeSh ∣ P ∣ IX.params → A .idx .Setoid.Carrier
    algIx γ t = alg .idxf .func (γ , unembed-idx P t)

    algIx-resp : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                 {s₁ s₂ : S'.Shape ∣ P ∣ IX.params} {a₁ a₂} →
                 E'.Sh≈ ∣ P ∣ IX.params s₁ s₂ a₁ a₂ →
                 Setoid._≈_ (A .idx) (algIx γ₁ (s₁ , a₁)) (algIx γ₂ (s₂ , a₂))
    algIx-resp γ≈ p = alg .idxf .func-resp-≈ (γ≈ , unembed-resp P p)

    mutual
      fold-fam : (γ : Γ .idx .Setoid.Carrier) (w : S.W ∣ P ∣ IX.params) (a : T.Assign w) →
                 prod (Γ .fam .fm γ) (Fδ.fib P d₀ w a) ⇒ A .fam .fm (fold algIx γ w a)
      fold-fam γ (S.sup s) a =
        alg .famf .transf (γ , unembed-idx P (fold-shape algIx γ ∣ P ∣ IX.fbase s a))
          ∘ pair p₁ (unembed-fam P (proj₁ (fold-shape algIx γ ∣ P ∣ IX.fbase s a))
                       (proj₂ (fold-shape algIx γ ∣ P ∣ IX.fbase s a))
                     ∘ fold-shape-fam γ P dbase s a)

      fold-tree-fam : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                      (γ : Γ .idx .Setoid.Carrier) (df : DecoF fmr d d')
                      (w : S.W ∣ Q ∣ ρ) (a : T.Assign w) →
                      prod (Γ .fam .fm γ) (Fδ.fib Q d w a) ⇒
                        FA.fib Q d' (proj₁ (fold-reindex algIx γ fmr w a)) (proj₂ (fold-reindex algIx γ fmr w a))
      fold-tree-fam {Q = Q} γ df (S.sup s) a = fold-shape-fam γ Q (dbind Q df) s a

      fold-shape-fam : ∀ {j} (γ : Γ .idx .Setoid.Carrier) (R : Poly-C j) {ηA ηB}
                       {fmr : IX.FMor ∣ P ∣ ηA ηB} {d d'} (df : DecoF fmr d d')
                       (s : S.Shape ∣ R ∣ ηA) (a : T.AssignSh ∣ R ∣ ηA s) →
                       prod (Γ .fam .fm γ) (Fδ.fib-shape R d s a) ⇒
                         FA.fib-shape R d' (proj₁ (fold-shape algIx γ ∣ R ∣ fmr s a))
                           (proj₂ (fold-shape algIx γ ∣ R ∣ fmr s a))
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
                       (s : S.El (ρ v)) (a : T.AssignEl (ρ v) s) →
                       prod (Γ .fam .fm γ) (Fδ.fib-el (ρ v) (d v) s a) ⇒
                         FA.fib-el (ρ' v) (d' v) (proj₁ (fold-apply algIx γ fmr v s a))
                           (proj₂ (fold-apply algIx γ fmr v s a))
      fold-apply-fam γ dbase        zero    w a = fold-fam γ w a
      fold-apply-fam γ dbase        (suc i) s a = p₂
      fold-apply-fam γ (dbind Q df) zero    w a = fold-tree-fam γ df w a
      fold-apply-fam γ (dbind Q df) (suc v) s a = fold-apply-fam γ df v s a

    mutual
      fold-fam-natural : ∀ {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂)
                         {w₁ w₂ : S.W ∣ P ∣ IX.params} {a₁ a₂} (p : E.W≈ w₁ w₂ a₁ a₂) →
                         (fold-fam γ₂ w₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-subst P d₀ {w₁ = w₁} {w₂ = w₂} p))
                           ≈ (A .fam .subst (fold-resp algIx algIx-resp γ≈ {w₁ = w₁} {w₂ = w₂} p)
                                ∘ fold-fam γ₁ w₁ a₁)
      fold-fam-natural γ≈ {S.sup s₁} {S.sup s₂} p =
        ≈-trans (assoc _ _ _)
          (≈-trans (∘-cong₂ (pair-natural _ _ _))
            (≈-trans (∘-cong₂ (pair-cong (pair-p₁ _ _)
                        (≈-trans (assoc _ _ _)
                          (≈-trans (∘-cong₂ (fold-shape-fam-natural γ≈ P dbase p))
                            (≈-trans (≈-sym (assoc _ _ _))
                              (≈-trans (∘-cong₁ (unembed-fam-natural P
                                          (fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p)))
                                (assoc _ _ _)))))))
              (≈-trans (∘-cong₂ (≈-sym (pair-compose _ _ _ _)))
                (≈-trans (≈-sym (assoc _ _ _))
                  (≈-trans (∘-cong₁ (alg .famf .natural
                              (γ≈ , unembed-resp P
                                      (fold-shape-resp algIx algIx-resp γ≈ ∣ P ∣ IX.fbase p))))
                    (assoc _ _ _))))))

      fold-tree-fam-natural : ∀ {k} {Q : Poly-C (suc k)} {ρ ρ'} {fmr : IX.FMor ∣ P ∣ ρ ρ'} {d d'}
                              {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (df : DecoF fmr d d')
                              {w₁ w₂ : S.W ∣ Q ∣ ρ} {a₁ a₂} (p : E.W≈ w₁ w₂ a₁ a₂) →
                              (fold-tree-fam γ₂ df w₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-subst Q d {w₁ = w₁} {w₂ = w₂} p))
                                ≈ (FA.fib-subst Q d' {w₁ = proj₁ (fold-reindex algIx γ₁ fmr w₁ a₁)}
                                     {w₂ = proj₁ (fold-reindex algIx γ₂ fmr w₂ a₂)}
                                     (fold-reindex-resp algIx algIx-resp γ≈ fmr {w₁ = w₁} {w₂ = w₂} p)
                                   ∘ fold-tree-fam γ₁ df w₁ a₁)
      fold-tree-fam-natural {Q = Q} γ≈ df {S.sup s₁} {S.sup s₂} p =
        fold-shape-fam-natural γ≈ Q (dbind Q df) p

      fold-shape-fam-natural : ∀ {j} {γ₁ γ₂} (γ≈ : Setoid._≈_ (Γ .idx) γ₁ γ₂) (R : Poly-C j)
                               {ηA ηB} {fmr : IX.FMor ∣ P ∣ ηA ηB} {d d'} (df : DecoF fmr d d')
                               {s₁ s₂ : S.Shape ∣ R ∣ ηA} {a₁ a₂} (p : E.Sh≈ ∣ R ∣ ηA s₁ s₂ a₁ a₂) →
                               (fold-shape-fam γ₂ R df s₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-shape-subst R d p))
                                 ≈ (FA.fib-shape-subst R d' (fold-shape-resp algIx algIx-resp γ≈ ∣ R ∣ fmr p)
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
                               {s₁ s₂ : S.El (ρ v)} {a₁ a₂} (p : E.El≈ (ρ v) s₁ s₂ a₁ a₂) →
                               (fold-apply-fam γ₂ df v s₂ a₂ ∘ prod-m (Γ .fam .subst γ≈) (Fδ.fib-el-subst (ρ v) (d v) p))
                                 ≈ (FA.fib-el-subst (ρ' v) (d' v) (fold-apply-resp algIx algIx-resp γ≈ fmr v p)
                                      ∘ fold-apply-fam γ₁ df v s₁ a₁)
      fold-apply-fam-natural γ≈ dbase        zero    {w₁} {w₂} p = fold-fam-natural γ≈ {w₁ = w₁} {w₂ = w₂} p
      fold-apply-fam-natural γ≈ dbase        (suc i) p = pair-p₂ _ _
      fold-apply-fam-natural γ≈ (dbind Q df) zero    {w₁} {w₂} p = fold-tree-fam-natural γ≈ df {w₁ = w₁} {w₂ = w₂} p
      fold-apply-fam-natural γ≈ (dbind Q df) (suc v) p = fold-apply-fam-natural γ≈ df v p

    foldMor : Fam𝒞._⇒_ (Fam𝒞-P.prod Γ (μObj P δ)) A
    foldMor .idxf .func (γ , t) = fold algIx γ (proj₁ t) (proj₂ t)
    foldMor .idxf .func-resp-≈ {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      fold-resp algIx algIx-resp γ≈ {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} t≈
    foldMor .famf .transf (γ , t) = fold-fam γ (proj₁ t) (proj₂ t)
    foldMor .famf .natural {γ₁ , t₁} {γ₂ , t₂} (γ≈ , t≈) =
      fold-fam-natural γ≈ {w₁ = proj₁ t₁} {w₂ = proj₁ t₂} t≈

-- The μ-type structure for the Fam construction.
hasMu : HasMu
hasMu .HasMu.μ-obj = μObj
hasMu .HasMu.inMap P δ = InMap.inMor P δ
hasMu .HasMu.⦅_⦆ {n} {Γ} {A} {P} {δ} alg = Fold.foldMor Γ A P δ alg
