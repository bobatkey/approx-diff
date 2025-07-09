{-# OPTIONS --prop --postfix-projections --safe #-}

open import prop
open import basics using (IsPreorder; IsMonoid; IsBigJoin; module ≤-Reasoning)

module kleene-star {aℓ bℓ cℓ}
  {A : Set aℓ} {_⊑_ : A → A → Prop bℓ} (⊑-isPreorder : IsPreorder _⊑_)
  {_▷_ ι}      (▷-isMonoid : IsMonoid ⊑-isPreorder _▷_ ι)
  {⋃}          (⋃-isBigJoin : IsBigJoin ⊑-isPreorder cℓ ⋃)
  (let open IsPreorder ⊑-isPreorder)
  (▷-⋃-distribₗ : ∀ {I X Y} → (⋃ I X ▷ Y) ≃ ⋃ I (λ i → X i ▷ Y))
  (▷-⋃-distribᵣ : ∀ {I X Y} → (X ▷ ⋃ I Y) ≃ ⋃ I (λ i → X ▷ Y i))
  where

open IsBigJoin ⋃-isBigJoin
  renaming (mono to ⋃-mono)
open IsMonoid ▷-isMonoid

data shape : Set cℓ where
  leaf : shape
  step : shape
  seq  : shape → shape → shape

Seq : A → shape → A
Seq X leaf      = ι
Seq X step      = X
Seq X (seq l r) = Seq X l ▷ Seq X r

Star : A → A
Star X = ⋃ shape (Seq X)

unit : ∀ {X} → X ⊑ Star X
unit = upper _ _ step

sequence : ∀ {X} → (Star X ▷ Star X) ⊑ Star X
sequence {X} =
  begin
    Star X ▷ Star X
  ≡⟨⟩
    ⋃ shape (Seq X) ▷ ⋃ shape (Seq X)
  ≤⟨ ▷-⋃-distribₗ .proj₁ ⟩
    ⋃ shape (λ s₁ → Seq X s₁ ▷ ⋃ shape (Seq X))
  ≤⟨ ⋃-mono (λ s₁ → ▷-⋃-distribᵣ .proj₁) ⟩
    ⋃ shape (λ s₁ → ⋃ shape (λ s₂ → (Seq X s₁ ▷ Seq X s₂)))
  ≤⟨ least _ _ _ (λ s₁ → least _ _ _ λ s₂ → upper _ _ (seq s₁ s₂)) ⟩
    ⋃ shape (Seq X)
  ∎ where open ≤-Reasoning ⊑-isPreorder

nil : ∀ {X} → ι ⊑ Star X
nil = upper _ _ leaf

induction : ∀ {X Y} → ι ⊑ Y → (Y ▷ Y) ⊑ Y → X ⊑ Y → Star X ⊑ Y
induction {X} {Y} ⊑-leaf ⊑-seq ⊑-step = least _ _ _ go
  where go : ∀ s → Seq X s ⊑ Y
        go leaf = ⊑-leaf
        go step = ⊑-step
        go (seq s₁ s₂) = trans (mono (go s₁) (go s₂)) ⊑-seq

-- Kleene co-star:
--
--  CoStar X = ⋂ shape (Seq X)
--
-- Assuming X ⊗ Y ≤ ι
--
--   Star X ⊗ CoStar Y
-- ≡ (⋃ shape (Seq X)) ⊗ (⋂ shape (Seq Y))
-- ≃ ⋃ shape (λ s → Seq X s ⊗ (⋂ shape (Seq Y)))   (distributivity)
-- ≤ ⋃ shape (λ s → Seq X s ⊗ Seq Y s)             (⋂ lower)
-- ≤ ⋃ shape (λ s → Seq (X ⊗ Y) s)                 (zipping by duoidality)
-- ≤ ⋃ shape (λ s → Seq ι s)                       (interaction)
-- ≤ ⋃ shape (λ s → ι)                             (constant)
-- ≤ ι
