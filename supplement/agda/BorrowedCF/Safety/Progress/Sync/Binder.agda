-- | The two-hole binder of the `ν` at the hole of a process context, in both
--   orientations (agent G2).
--
--   `sync-redex` starts from `plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q)`, so
--   the binder that `CanonicalPair.canon-pair` needs is right there: `ctx` is
--   the `above`, the `ν` node is the `bind₂`, and the two local indices are the
--   heads `0F` and `head₂` of the two endpoints.  `binderL` presents the
--   thread blocked on `0F` as the FIRST hole (`heads-lr`), `binderR` the one
--   blocked on `head₂` (`heads-rl`, via `Sync/Locate.swap₂`).
module BorrowedCF.Safety.Progress.Sync.Binder where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Safety.Blocked using (head₂)
open import BorrowedCF.Safety.Progress.Sync.Locate
  using (swap₂; plug-swap₂; wt₁-swap₂; wt₂-swap₂)

open import BorrowedCF.Simulation.BackwardSoup.Locate using (ProcessContext; plug)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; bind₂; plug₂; compose₂; plug-compose₂
        ; wt₁; wt₂; Binder₂; binder₂)

open Nat.Variables
open Fin.Patterns

binderL : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
  Binder₂ (compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) c₀))
          (wt₁ c₀ 0F) (wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂))
binderL ctx b₁ b₂ B₁ B₂ c₀ =
  binder₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) ctx c₀ refl
    0F (sum (suc b₁ ∷ B₁) ↑ʳ 0F) refl refl

binderR : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
  Binder₂ (compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (swap₂ c₀)))
          (wt₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) (wt₁ c₀ 0F)
binderR ctx b₁ b₂ B₁ B₂ c₀ =
  binder₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) ctx (swap₂ c₀) refl
    (sum (suc b₁ ∷ B₁) ↑ʳ 0F) 0F
    (wt₁-swap₂ c₀ (head₂ (suc b₁ ∷ B₁) b₂ B₂)) (wt₂-swap₂ c₀ 0F)

plugL : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k))
  (R₁ : Proc k₁) (R₂ : Proc k₂) →
  plug₂ (compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) c₀)) R₁ R₂
    ≡ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ R₁ R₂))
plugL ctx b₁ b₂ B₁ B₂ c₀ R₁ R₂ =
  plug-compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) c₀) R₁ R₂

plugR : ∀ {k k₁ k₂} (ctx : ProcessContext k 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
  (c₀ : ProcessContext₂ k₁ k₂ (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k))
  (R₁ : Proc k₁) (R₂ : Proc k₂) →
  plug₂ (compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (swap₂ c₀))) R₂ R₁
    ≡ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (plug₂ c₀ R₁ R₂))
plugR ctx b₁ b₂ B₁ B₂ c₀ R₁ R₂ =
  plug-compose₂ ctx (bind₂ (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) (swap₂ c₀)) R₂ R₁
  ■ cong (λ z → plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) z)) (plug-swap₂ c₀ R₁ R₂)

0≢head₂ : ∀ {k} (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) →
  0F ≢ head₂ {k} (suc b₁ ∷ B₁) b₂ B₂
0≢head₂ b₁ b₂ B₁ B₂ ()
