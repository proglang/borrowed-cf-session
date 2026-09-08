-- | The session-type content of `R-Choice`.
--
--   Both endpoints of the channel resolve the same choice, so the residual
--   protocol on the sender's side and the one on the receiver's side stay dual.
module BorrowedCF.Safety.Preservation.Choice.Session where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Ctx; _⸴_)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Support.BrnView
open import BorrowedCF.Safety.Preservation.Choice.BindCtxBrn

open Nat.Variables

private variable
  i : Bool
  b₁ b₂ : ℕ

¬skips-end : ∀ {s : 𝕊 0} {p} → ¬ Skips (s ; end p)
¬skips-end (_ ; ())

-- | Resolving the `i`-th branch on both endpoints of one channel.
choice-split : ∀ (i : Bool) {p} {s σ₁ σ₂ τ₁ τ₂ sh₁ sh₂ : 𝕊 0}
  {B₁ B₂ : BindGroup} {Γ₁ : Ctx (b₁ + sum B₁)} {Γ₂ : Ctx (b₂ + sum B₂)} →
  New s →
  sh₁ ≃ brn ‼ σ₁ σ₂ →
  sh₂ ≃ brn ⁇ τ₁ τ₂ →
  BindCtx (s ; end p) (suc b₁ ∷ B₁) (⟨ sh₁ ⟩ ⸴ Γ₁) →
  BindCtx (dual s ; end (dualPol p)) (suc b₂ ∷ B₂) (⟨ sh₂ ⟩ ⸴ Γ₂) →
  ∃[ s* ] ∃[ t₁ ] ∃[ t₂ ]
      New s*
    × ((if i then σ₁ else σ₂) ≃ t₁)
    × ((if i then τ₁ else τ₂) ≃ t₂)
    × BindCtx (s* ; end p) (suc b₁ ∷ B₁) (⟨ t₁ ⟩ ⸴ Γ₁)
    × BindCtx (dual s* ; end (dualPol p)) (suc b₂ ∷ B₂) (⟨ t₂ ⟩ ⸴ Γ₂)
choice-split i N eq₁ eq₂ C₁ C₂
  with t₁ , V₁ , σ≃ ← ≃-brnv {i = i} (≃-sym eq₁) here
  with t₂ , V₂ , τ≃ ← ≃-brnv {i = i} (≃-sym eq₂) here
  with S*₁ , VS₁ , Rb₁ ← bindCtx-brn V₁ C₁
  with S*₂ , VS₂ , Rb₂ ← bindCtx-brn V₂ C₂
  with VS₁
... | tl _ ()
... | hd c₁ =
  _ , t₁ , t₂
    , brnv-new N c₁
    , σ≃ , τ≃
    , Rb₁ ¬skips-end ≃-refl
    , Rb₂ ¬skips-end (brnv-unique VS₂ (hd (brnv-dual c₁)))
