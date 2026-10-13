-- | The rule dispatch of `sync-redex` (agent G2).
--
--   The two head kinds are dual (`Sync/Heads.head-kinds`), so exactly six
--   constant pairs survive.  Each is one of the three synchronising rules, with
--   the endpoints exchanged (`binderR`, `heads-rl`) when the FIRST thread sits
--   on the second endpoint.
--
--   PERFORMANCE.  The two rewritings along `plugL` / `plugR` MUST go through
--   `transport-red` / `transport-⊢`, which match the equation with `refl` while
--   both processes are still variables.  Doing them with `subst` instead (and
--   projecting the rule worker's result with a pattern-`let`) makes Agda unfold
--   `plug`, `plug₂` and `compose₂` under the equation and blows the heap: the
--   same six clauses then take >10 GB, against 10 s and 1.6 GB here.
module BorrowedCF.Safety.Progress.Sync.Dispatch where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_)

open import BorrowedCF.Safety.Blocked using (head₂)
open import BorrowedCF.Safety.Progress.Sync.Front using (HKind; dualKind)
open import BorrowedCF.Safety.Progress.Sync.Heads
  using (BCShape; send; recv; select; branch; end)
open import BorrowedCF.Safety.Progress.Sync.Binder
open import BorrowedCF.Safety.Progress.Sync.Com using (com-step)
open import BorrowedCF.Safety.Progress.Sync.Choice using (choice-step)
open import BorrowedCF.Safety.Progress.Sync.Close using (close-step)

open import BorrowedCF.Simulation.BackwardSoup.Locate using (ProcessContext; plug)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using (ProcessContext₂; plug₂; wt₁; wt₂; heads-lr; heads-rl)

open Nat.Variables
open Variables
open Fin.Patterns

transport-red : {X Y : Proc 0} → X ≡ Y →
  Σ[ P′ ∈ Proc 0 ] X ─→ₚ P′ → Σ[ P′ ∈ Proc 0 ] Y ─→ₚ P′
transport-red refl r = r

transport-⊢ : {X Y : Proc 0} → X ≡ Y → [] ; [] ⊢ₚ X → [] ; [] ⊢ₚ Y
transport-⊢ refl ⊢X = ⊢X

dispatch : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k))
  {hk : HKind} {f₁ : Tm k₁} {f₂ : Tm k₂} →
  BCShape (wt₁ c₀ 0F) hk f₁ →
  BCShape (wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) (dualKind hk) f₂ →
  [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) →
  Σ[ P′ ∈ Proc 0 ]
    plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ ⟪ f₁ ⟫ ⟪ f₂ ⟫)) ─→ₚ P′
dispatch ctx b₁ b₂ B₁ B₂ c₀ (send E₁ {v} V) (recv E₂) ⊢P =
  transport-red
    (plugL ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K `send ·¹ (v ⊗ (` wt₁ c₀ 0F)) ]* ⟫
      ⟪ E₂ [ K `recv ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫)
    (com-step (binderL ctx b₁ b₂ B₁ B₂ c₀) (heads-lr b₁ B₁ b₂ B₂) E₁ V E₂
      (transport-⊢
        (sym (plugL ctx b₁ b₂ B₁ B₂ c₀
               ⟪ E₁ [ K `send ·¹ (v ⊗ (` wt₁ c₀ 0F)) ]* ⟫
               ⟪ E₂ [ K `recv ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫))
        ⊢P))
dispatch ctx b₁ b₂ B₁ B₂ c₀ (recv E₁) (send E₂ {v} V) ⊢P =
  transport-red
    (plugR ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K `recv ·¹ (` wt₁ c₀ 0F) ]* ⟫
      ⟪ E₂ [ K `send ·¹ (v ⊗ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂))) ]* ⟫)
    (com-step (binderR ctx b₁ b₂ B₁ B₂ c₀) (heads-rl b₁ B₁ b₂ B₂) E₂ V E₁
      (transport-⊢
        (sym (plugR ctx b₁ b₂ B₁ B₂ c₀
               ⟪ E₁ [ K `recv ·¹ (` wt₁ c₀ 0F) ]* ⟫
               ⟪ E₂ [ K `send ·¹ (v ⊗ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂))) ]* ⟫))
        ⊢P))
dispatch ctx b₁ b₂ B₁ B₂ c₀ (select E₁ i) (branch E₂) ⊢P =
  transport-red
    (plugL ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K (`select i) ·¹ (` wt₁ c₀ 0F) ]* ⟫
      ⟪ E₂ [ K `branch ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫)
    (choice-step (binderL ctx b₁ b₂ B₁ B₂ c₀) (heads-lr b₁ B₁ b₂ B₂) E₁ i E₂)
dispatch ctx b₁ b₂ B₁ B₂ c₀ (branch E₁) (select E₂ i) ⊢P =
  transport-red
    (plugR ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K `branch ·¹ (` wt₁ c₀ 0F) ]* ⟫
      ⟪ E₂ [ K (`select i) ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫)
    (choice-step (binderR ctx b₁ b₂ B₁ B₂ c₀) (heads-rl b₁ B₁ b₂ B₂) E₂ i E₁)
dispatch ctx b₁ b₂ B₁ B₂ c₀ (end E₁ ‼) (end E₂ ⁇) ⊢P =
  transport-red
    (plugL ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K (`end ‼) ·¹ (` wt₁ c₀ 0F) ]* ⟫
      ⟪ E₂ [ K (`end ⁇) ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫)
    (close-step (binderL ctx b₁ b₂ B₁ B₂ c₀) (heads-lr b₁ B₁ b₂ B₂) E₁ E₂
      (transport-⊢
        (sym (plugL ctx b₁ b₂ B₁ B₂ c₀
               ⟪ E₁ [ K (`end ‼) ·¹ (` wt₁ c₀ 0F) ]* ⟫
               ⟪ E₂ [ K (`end ⁇) ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫))
        ⊢P))
dispatch ctx b₁ b₂ B₁ B₂ c₀ (end E₁ ⁇) (end E₂ ‼) ⊢P =
  transport-red
    (plugR ctx b₁ b₂ B₁ B₂ c₀
      ⟪ E₁ [ K (`end ⁇) ·¹ (` wt₁ c₀ 0F) ]* ⟫
      ⟪ E₂ [ K (`end ‼) ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫)
    (close-step (binderR ctx b₁ b₂ B₁ B₂ c₀) (heads-rl b₁ B₁ b₂ B₂) E₂ E₁
      (transport-⊢
        (sym (plugR ctx b₁ b₂ B₁ B₂ c₀
               ⟪ E₁ [ K (`end ⁇) ·¹ (` wt₁ c₀ 0F) ]* ⟫
               ⟪ E₂ [ K (`end ‼) ·¹ (` wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) ]* ⟫))
        ⊢P))
