-- | Linearity bookkeeping for `R-Choice`: the two communicating handles occur
--   exactly once in the binder structure of the restriction, hence not at all
--   in the frames, in the other thread, or in the parallel remainder.
module BorrowedCF.Safety.Preservation.Choice.Count where

open import Data.Nat.ListAction using (sum)
open import Data.Fin.Subset using (_∉_)
open import Data.Fin.Subset.Properties using (∉⊥)

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Domain using (dom)
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed using (BindGroup; structNSeq; structBinder)
open import BorrowedCF.Terms using (weakenᵣ)
open import BorrowedCF.Types

open import BorrowedCF.Simulation.Support.Confine
  using (count; count-self; count0⇒∉dom; ∉dom⇒count0; count-join-Dir; count-join-PS; ≼⇒count≤; ∉∪⁻; ∉-join-Dir⁺)

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Support.ComWeaken using (⋯ᵣ∘; ⋯ᵣ-cong; structBinder-suc; Fr)

open Nat.Variables
open Fin.Patterns

private variable N : ℕ

------------------------------------------------------------------------
-- count under a renaming that misses `x`, and count through a pattern.
------------------------------------------------------------------------

count-⋯ᵣ-∉ : (γ : Struct m) (ρ : 𝔽 m → 𝔽 N) (x : 𝔽 N) →
  (∀ u → ρ u ≢ x) → count x (γ 𝐂.⋯ᵣ ρ) ≡ 0
count-⋯ᵣ-∉ (` u) ρ x ¬eq with x Fin.≟ ρ u
... | yes eq = ⊥-elim (¬eq u (sym eq))
... | no  _  = refl
count-⋯ᵣ-∉ [] ρ x ¬eq = refl
count-⋯ᵣ-∉ (α ∥ β) ρ x ¬eq = cong₂ _+_ (count-⋯ᵣ-∉ α ρ x ¬eq) (count-⋯ᵣ-∉ β ρ x ¬eq)
count-⋯ᵣ-∉ (α ; β) ρ x ¬eq = cong₂ _+_ (count-⋯ᵣ-∉ α ρ x ¬eq) (count-⋯ᵣ-∉ β ρ x ¬eq)

count-[-]𝓅 : (𝒫 : CxPat n) (x : 𝔽 n) (γ : Struct n) →
  count x (𝒫 [ γ ]𝓅) ≡ count x (𝒫 [ [] ]𝓅) + count x γ
count-[-]𝓅 [] x γ = refl
count-[-]𝓅 ((d , α) ∷ 𝒫) x γ =
    count-join-Dir d x α (𝒫 [ γ ]𝓅)
  ■ cong (count x α +_) (count-[-]𝓅 𝒫 x γ)
  ■ sym (Nat.+-assoc (count x α) (count x (𝒫 [ [] ]𝓅)) (count x γ))
  ■ cong (_+ count x γ) (sym (count-join-Dir d x α (𝒫 [ [] ]𝓅)))

------------------------------------------------------------------------
-- Each communicated handle occurs exactly once in the binder structure.
------------------------------------------------------------------------

module _ (b₁ : ℕ) (B₁ : BindGroup) (b₂ : ℕ) (B₂ : BindGroup)
         {kk : ℕ} (γ : Struct kk) where
  private
    aa cc : ℕ
    aa = b₁ + sum B₁
    cc = b₂ + sum B₂

    g₁ : 𝔽 (suc aa) → 𝔽 (suc aa + suc cc + kk)
    g₁ u = (u ↑ˡ suc cc) ↑ˡ kk

    g₂ : 𝔽 (suc cc) → 𝔽 (suc aa + suc cc + kk)
    g₂ u = (suc aa ↑ʳ u) ↑ˡ kk

    P₁ P₂ : Struct aa
    P₁ = structNSeq b₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁)
    P₂ = structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ b₁

    R₁ R₂ : Struct cc
    R₁ = structNSeq b₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)
    R₂ = structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ b₂

    blk₁ : ∀ (Q : Struct (suc aa)) →
      Q 𝐂.⋯ᵣ 𝐂.wkʳ (suc cc) 𝐂.⋯ᵣ 𝐂.wkʳ kk ≡ Q 𝐂.⋯ᵣ g₁
    blk₁ Q = ⋯ᵣ∘ Q _ _

    blk₂ : ∀ (Q : Struct (suc cc)) →
      Q 𝐂.⋯ᵣ 𝐂.wkˡ (suc aa) 𝐂.⋯ᵣ 𝐂.wkʳ kk ≡ Q 𝐂.⋯ᵣ g₂
    blk₂ Q = ⋯ᵣ∘ Q _ _

  yv : 𝔽 (suc aa + suc cc + kk)
  yv = (suc aa ↑ʳ Fin.zero {cc}) ↑ˡ kk

  count-Fr-x : count 0F (Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ) ≡ 1
  count-Fr-x = cong₂ _+_ (cong₂ _+_ part₁ part₂) part₃
    where
    part₁ : count 0F (structBinder (suc b₁ ∷ B₁) 𝐂.⋯ᵣ 𝐂.wkʳ (suc cc) 𝐂.⋯ᵣ 𝐂.wkʳ kk) ≡ 1
    part₁ = cong (count 0F) (blk₁ (structBinder (suc b₁ ∷ B₁)) ■ cong (𝐂._⋯ᵣ g₁) (structBinder-suc b₁ B₁))
          ■ cong₂ _+_
              (cong (1 +_) (cong (count 0F) (⋯ᵣ∘ P₁ weakenᵣ g₁)
                            ■ count-⋯ᵣ-∉ P₁ (g₁ ∘ weakenᵣ) 0F (λ _ ())))
              (cong (count 0F) (⋯ᵣ∘ P₂ weakenᵣ g₁)
                ■ count-⋯ᵣ-∉ P₂ (g₁ ∘ weakenᵣ) 0F (λ _ ()))
    part₂ : count 0F (structBinder (suc b₂ ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ (suc aa) 𝐂.⋯ᵣ 𝐂.wkʳ kk) ≡ 0
    part₂ = cong (count 0F) (blk₂ (structBinder (suc b₂ ∷ B₂)))
          ■ count-⋯ᵣ-∉ (structBinder (suc b₂ ∷ B₂)) g₂ 0F (λ _ ())
    part₃ : count 0F (γ 𝐂.⋯ᵣ 𝐂.weaken* (suc aa + suc cc)) ≡ 0
    part₃ = count-⋯ᵣ-∉ γ (𝐂.weaken* (suc aa + suc cc)) 0F (λ _ ())

  count-Fr-y : count yv (Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ) ≡ 1
  count-Fr-y = cong₂ _+_ (cong₂ _+_ part₁ part₂) part₃
    where
    part₁ : count yv (structBinder (suc b₁ ∷ B₁) 𝐂.⋯ᵣ 𝐂.wkʳ (suc cc) 𝐂.⋯ᵣ 𝐂.wkʳ kk) ≡ 0
    part₁ = cong (count yv) (blk₁ (structBinder (suc b₁ ∷ B₁)))
          ■ count-⋯ᵣ-∉ (structBinder (suc b₁ ∷ B₁)) g₁ yv
              (λ u eq → Fin.↑ˡ≢↑ʳ (Fin.↑ˡ-injective kk _ _ eq))
    part₂ : count yv (structBinder (suc b₂ ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ (suc aa) 𝐂.⋯ᵣ 𝐂.wkʳ kk) ≡ 1
    part₂ = cong (count yv) (blk₂ (structBinder (suc b₂ ∷ B₂)) ■ cong (𝐂._⋯ᵣ g₂) (structBinder-suc b₂ B₂))
          ■ cong₂ _+_ (cong₂ _+_ (count-self yv) e₁) e₂
      where
      e₁ : count yv (R₁ 𝐂.⋯ᵣ weakenᵣ 𝐂.⋯ᵣ g₂) ≡ 0
      e₁ = cong (count yv) (⋯ᵣ∘ R₁ weakenᵣ g₂)
         ■ count-⋯ᵣ-∉ R₁ (g₂ ∘ weakenᵣ) yv
             (λ w eq → case Fin.↑ʳ-injective (suc aa) _ _ (Fin.↑ˡ-injective kk _ _ eq) of λ ())
      e₂ : count yv (R₂ 𝐂.⋯ᵣ weakenᵣ 𝐂.⋯ᵣ g₂) ≡ 0
      e₂ = cong (count yv) (⋯ᵣ∘ R₂ weakenᵣ g₂)
         ■ count-⋯ᵣ-∉ R₂ (g₂ ∘ weakenᵣ) yv
             (λ w eq → case Fin.↑ʳ-injective (suc aa) _ _ (Fin.↑ˡ-injective kk _ _ eq) of λ ())
    part₃ : count yv (γ 𝐂.⋯ᵣ 𝐂.weaken* (suc aa + suc cc)) ≡ 0
    part₃ = count-⋯ᵣ-∉ γ (𝐂.weaken* (suc aa + suc cc)) yv
              (λ u eq → Fin.↑ˡ≢↑ʳ (sym (sym (𝐂.weaken*~wkˡ (suc aa + suc cc) u) ■ eq)))

------------------------------------------------------------------------
-- `∉ dom` bookkeeping used by `Choice.Retype`.
------------------------------------------------------------------------

∉-join-Dir⁻ : ∀ {x : 𝔽 N} (d : Dir) (α β : Struct N) →
  x ∉ dom (join d α β) → (x ∉ dom α) × (x ∉ dom β)
∉-join-Dir⁻ 𝟙 α β x∉ = ∉∪⁻ x∉
∉-join-Dir⁻ L α β x∉ = ∉∪⁻ x∉
∉-join-Dir⁻ R α β x∉ = Π.swap (∉∪⁻ x∉)

∉-[-]𝓅⁻ : ∀ {x : 𝔽 N} (𝒫 : CxPat N) (γ : Struct N) →
  x ∉ dom (𝒫 [ γ ]𝓅) → (x ∉ dom (𝒫 [ [] ]𝓅)) × (x ∉ dom γ)
∉-[-]𝓅⁻ [] γ x∉ = ∉⊥ , x∉
∉-[-]𝓅⁻ ((d , α) ∷ 𝒫) γ x∉ =
  let a∉ , r∉ = ∉-join-Dir⁻ d α (𝒫 [ γ ]𝓅) x∉
      p∉ , g∉ = ∉-[-]𝓅⁻ 𝒫 γ r∉
  in ∉-join-Dir⁺ d α (𝒫 [ [] ]𝓅) a∉ p∉ , g∉

∉-[-]𝓅-++ : ∀ {x : 𝔽 N} (𝒫₁ 𝒫₂ : CxPat N) →
  x ∉ dom ((𝒫₁ ++ 𝒫₂) [ [] ]𝓅) → (x ∉ dom (𝒫₁ [ [] ]𝓅)) × (x ∉ dom (𝒫₂ [ [] ]𝓅))
∉-[-]𝓅-++ {x = x} 𝒫₁ 𝒫₂ x∉ =
  ∉-[-]𝓅⁻ 𝒫₁ (𝒫₂ [ [] ]𝓅) (subst (λ z → x ∉ dom z) ([-]𝓅-dist-++ 𝒫₁ 𝒫₂ []) x∉)

-- A variable of the ambient tail never occurs in a binder block.
∉-block : ∀ {m kk NN} (Q : Struct m) (f : 𝔽 m → 𝔽 kk) (x : 𝔽 NN) →
  (kk ↑ʳ x) ∉ dom (Q 𝐂.⋯ᵣ (λ u → f u ↑ˡ NN))
∉-block {kk = kk} {NN = NN} Q f x =
  count0⇒∉dom (Q 𝐂.⋯ᵣ (λ u → f u ↑ˡ NN))
    (count-⋯ᵣ-∉ Q (λ u → f u ↑ˡ NN) (kk ↑ʳ x) (λ u eq → Fin.↑ˡ≢↑ʳ eq))

count-wkˡ : ∀ kk (γ : Struct N) (x : 𝔽 N) → count (kk ↑ʳ x) (γ 𝐂.⋯ᵣ 𝐂.wkˡ kk) ≡ count x γ
count-wkˡ kk (` u) x with kk ↑ʳ x Fin.≟ kk ↑ʳ u | x Fin.≟ u
... | yes _  | yes _ = refl
... | no  _  | no  _ = refl
... | yes eq | no ¬p = ⊥-elim (¬p (Fin.↑ʳ-injective kk _ _ eq))
... | no ¬eq | yes p = ⊥-elim (¬eq (cong (kk ↑ʳ_) p))
count-wkˡ kk [] x = refl
count-wkˡ kk (α ∥ β) x = cong₂ _+_ (count-wkˡ kk α x) (count-wkˡ kk β x)
count-wkˡ kk (α ; β) x = cong₂ _+_ (count-wkˡ kk α x) (count-wkˡ kk β x)

∉-wk* : ∀ {NN} kk (γ : Struct NN) (x : 𝔽 NN) → x ∉ dom γ → (kk ↑ʳ x) ∉ dom (γ 𝐂.⋯ᵣ 𝐂.weaken* kk)
∉-wk* kk γ x x∉ = count0⇒∉dom (γ 𝐂.⋯ᵣ 𝐂.weaken* kk)
  (cong (count (kk ↑ʳ x)) (⋯ᵣ-cong γ (𝐂.weaken*~wkˡ kk))
    ■ count-wkˡ kk γ x ■ ∉dom⇒count0 γ x∉)
