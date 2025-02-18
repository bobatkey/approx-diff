{-# OPTIONS --prop --postfix-projections --safe #-}

module example2 where

open import Level

import galois
open import categories
  using (Category; opposite; HasProducts; HasExponentials; setoid→category)
open import functor using ([_⇒_]; HasLimits)
open import cmon-enriched using (CMonEnriched; FunctorCat-cmon; Biproduct)
open import grothendieck
open import commutative-monoid-cat using ()
  renaming ( cat to CMon; Obj to CMonObj; limits to CMon-limits
           ; cmon-enriched to CMon-enriched
           ; products to CMon-products)

PShGalois : Category (suc (suc 0ℓ)) (suc 0ℓ) (suc 0ℓ)
PShGalois = [ opposite galois.cat ⇒ CMon (suc 0ℓ) (suc 0ℓ) ]

PShGalois-limits : (𝒮 : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)) → HasLimits 𝒮 PShGalois
PShGalois-limits 𝒮 = limits
  where
    open import functor-cat-limits _ _ 𝒮 (CMon-limits (suc 0ℓ) 𝒮)

PShGalois-cmon : CMonEnriched PShGalois
PShGalois-cmon = FunctorCat-cmon _ _ CMon-enriched

PShGalois-biproducts : ∀ x y → Biproduct PShGalois-cmon x y
PShGalois-biproducts x y = biproducts
  where open import functor-cat-products (opposite galois.cat) (CMon (suc 0ℓ) (suc 0ℓ))
                       {!!} -- FIXME: CMon-terminal
                       CMon-products
        open cmon-enriched.cmon+products→biproducts PShGalois-cmon {!!}

------------------------------------------------------------------------------
module D = CategoryOfFamilies (suc 0ℓ) (suc 0ℓ) PShGalois
module DP = D.products (cmon-enriched.biproducts→products _ PShGalois-biproducts)

D-products : HasProducts D.cat
D-products = DP.products

D-exponentials : HasExponentials D.cat D-products
D-exponentials = exponentials
  where open import fam using (hasSetoidProducts)
        open import families-exponentials (suc 0ℓ) (suc 0ℓ)
                          PShGalois
                          PShGalois-cmon
                          PShGalois-biproducts
                          (hasSetoidProducts _ _ PShGalois
                             λ A → PShGalois-limits (setoid→category A))

-- And also:
--   1. Terminal object
--   2. Booleans
--   3. Lists
