-- | The `R-Choice` synchronisation: a `select` and a `branch` on the two head
--   handles of one `ν` reduce.
--
--   `CanonicalPair.canon-pair` already produces literally the left-hand side of
--   `R-Choice` (that is what its `CanonPair` record is shaped after), so the
--   only work here is to push the two renamings `ρ₁` / `ρ₂` through the frame
--   stacks (`⋯ᶠ*-[]*`) and to rewrite the two handles with the record's
--   `x₁-eq` / `x₂-eq`.  `R-Choice` renames nothing and takes an arbitrary
--   residual, so no confinement is needed.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Choice where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_; R-Choice; R-Struct)

open import BorrowedCF.Safety.Progress.Expr.Plug using (⋯ᶠ*-[]*)
open import BorrowedCF.Safety.Progress.Redex.Context using (red-in-ctx)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; plug; ≡→≋)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using (ProcessContext₂; plug₂; Binder₂; CanonPair; canonPair; canon-pair; HeadShape₂)

open Nat.Variables
open Variables
open Fin.Patterns

choice-step : {k₁ k₂ : ℕ} {c : ProcessContext₂ k₁ k₂ 0} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd : Binder₂ c x₁ x₂) →
  HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd) (Binder₂.local₁ bnd) (Binder₂.local₂ bnd) →
  (E₁ : Frame* k₁) (i : Side) (E₂ : Frame* k₂) →
  Σ[ P′ ∈ Proc 0 ]
    plug₂ c ⟪ E₁ [ K (`select i) ·¹ (` x₁) ]* ⟫ ⟪ E₂ [ K `branch ·¹ (` x₂) ]* ⟫ ─→ₚ P′
choice-step {x₁ = x₁} {x₂ = x₂} bnd hs E₁ i E₂
  with canon-pair (E₁ [ K (`select i) ·¹ (` x₁) ]*) (E₂ [ K `branch ·¹ (` x₂) ]*) bnd hs
... | canonPair {midᵖ = mid} b₁ b₂ B₁ B₂ above′ ρ₁ ρ₂ resid ≋c xeq₁ xeq₂ _ _ =
  _ , R-Struct (≋c ◅◅ ≡→≋ shapeEq) (red-in-ctx above′ step) ≋-refl
  where
  F₁ = E₁ ⋯ᶠ* ρ₁
  F₂ = E₂ ⋯ᶠ* ρ₂
  hd₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)
  hd₂ = wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

  lhs : Proc mid
  lhs = ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((⟪ F₁ [ K (`select i) ·¹ (` 0F) ]* ⟫ ∥ ⟪ F₂ [ K `branch ·¹ (` hd₂) ]* ⟫) ∥ resid)

  step : lhs ─→ₚ _
  step = R-Choice F₁ F₂ i

  shapeEq :
    plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ (E₁ [ K (`select i) ·¹ (` x₁) ]*) ⋯ ρ₁ ⟫
        ∥ ⟪ (E₂ [ K `branch ·¹ (` x₂) ]*) ⋯ ρ₂ ⟫) ∥ resid))
      ≡ plug above′ lhs
  shapeEq = cong (plug above′) (cong (ν _ _) (cong₂ _∥_ (cong₂ _∥_
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₁ _ ρ₁
        ■ cong (λ z → F₁ [ K (`select i) ·¹ (` z) ]*) xeq₁))
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₂ _ ρ₂
        ■ cong (λ z → F₂ [ K `branch ·¹ (` z) ]*) xeq₂)))
      refl))
