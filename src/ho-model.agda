{-# OPTIONS --postfix-projections --prop --safe #-}

module ho-model where

-- PLAN
-- 1. galois is a CMonCategory
-- 2. PSh(galois) is a complete CMonCategory
-- 3. So PSh(galois) is a Category with biproducts and all discrete products
-- 4. So Fam(PSh(galois)) is Cartesian Closed with all coproducts

open import Level using (suc; 0ℓ)
open import categories using (Category; HasProducts; HasTerminal; setoid→category)
open import functor using (HasLimits'; limits'→limits)
import galois
import fam
open import cmon-category using (CMonCategory)
import commutative-monoid-cat
import cmon-category
import cmon-enriched
import grothendieck
import product-diagram

------------------------------------------------------------------------------
-- Stage 0 : the base category
Gal : CMonCategory (suc 0ℓ) 0ℓ 0ℓ
Gal = record { cat = galois.cat ; cmon-enriched = galois.cmon-enriched }

------------------------------------------------------------------------------
-- Stage 1 : Presheaves over the base category

open cmon-category.presheaves 0ℓ Gal
  renaming (PSh to PSh⟨Gal⟩; PSh₀ to PSh⟨Gal⟩₀)

-- FIXME: the following three should be in cmon-category.presheaves

PSh⟨Gal⟩-limits : ∀ (𝒮 : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)) → HasLimits' 𝒮 PSh⟨Gal⟩₀
PSh⟨Gal⟩-limits 𝒮 = cmon-category.limits (CMonCategory.opposite Gal) (cmon-category.CMon (suc 0ℓ) (suc 0ℓ)) 𝒮
  λ D → commutative-monoid-cat.limits 0ℓ 𝒮 D

{-
PSh⟨Gal⟩-limits-0 : ∀ (𝒮 : Category 0ℓ 0ℓ 0ℓ) → HasLimits' 𝒮 PSh⟨Gal⟩₀
PSh⟨Gal⟩-limits-0 𝒮 = cmon-category.limits (CMonCategory.opposite Gal) (cmon-category.CMon (suc 0ℓ) (suc 0ℓ)) 𝒮
  λ D → commutative-monoid-cat.limits 0ℓ 𝒮 D
-}

-- FIXME: if we have all limits, then we can get all products. This
-- has been partially done in product-diagram.agda. FIXME: need to make this
PSh⟨Gal⟩-products : HasProducts (PSh⟨Gal⟩ .CMonCategory.cat)
PSh⟨Gal⟩-products =
  product-diagram.limits→products (CMonCategory.cat PSh⟨Gal⟩) (limits'→limits {!PSh⟨Gal⟩-limits !})

PSh⟨Gal⟩-terminal : HasTerminal (PSh⟨Gal⟩ .CMonCategory.cat)
PSh⟨Gal⟩-terminal = {!!}

PSh⟨Gal⟩-biproducts : (x y : Category.obj (CMonCategory.cat PSh⟨Gal⟩)) →
     cmon-enriched.Biproduct (CMonCategory.cmon-enriched PSh⟨Gal⟩) x y
PSh⟨Gal⟩-biproducts =
  cmon-enriched.cmon+products→biproducts (PSh⟨Gal⟩ .CMonCategory.cmon-enriched) PSh⟨Gal⟩-products

------------------------------------------------------------------------------
-- Stage 2 : Families over presheaves is a model of the higher order language

open grothendieck.CategoryOfFamilies 0ℓ 0ℓ (PSh⟨Gal⟩ .CMonCategory.cat)
  renaming ( cat to Fam⟨PSh⟨Gal⟩⟩
           ; terminal to make-terminal
           )
  using (module products; lists)

-- FIXME: terminal object

Fam⟨PSh⟨Gal⟩⟩-terminal : HasTerminal Fam⟨PSh⟨Gal⟩⟩
Fam⟨PSh⟨Gal⟩⟩-terminal = make-terminal PSh⟨Gal⟩-terminal

open products PSh⟨Gal⟩-products
  renaming ( products         to Fam⟨PSh⟨Gal⟩⟩-products
           ; strongCoproducts to Fam⟨PSh⟨Gal⟩⟩-strongCoproducts
           )
  using ()
  public

open import families-exponentials
  0ℓ 0ℓ (PSh⟨Gal⟩ .CMonCategory.cat) (PSh⟨Gal⟩ .CMonCategory.cmon-enriched) PSh⟨Gal⟩-biproducts
    (fam.hasSetoidProducts (suc 0ℓ) (suc 0ℓ) (PSh⟨Gal⟩ .CMonCategory.cat) λ A → PSh⟨Gal⟩-limits (setoid→category A))
  renaming ( exponentials     to Fam⟨PSh⟨Gal⟩⟩-exponentials )
  using    ()
  public
