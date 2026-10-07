------------------------------------------------------------------------
-- `Local t₂` (with `¬ Skips t₂`) rules out an acq head of t₂ up to ≃.
--
-- Group.agda proves this as the PRIVATE `local⇒¬acqHead`, with one open
-- `mu` hole (see DECISION-local-mu.md).  To keep that hole in one place we
-- do not reprove it: we run Group's public `bindCtx-rsplit` on a two-group
-- binder context whose first group is empty, so the split group is a
-- non-first group and its new head ⟨ skip ; ret ⟩ must be acq-headed,
-- which it is not.  Replace by `local⇒¬acqHead` once Group exports it.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.LocalHead where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomCons using (acq-;-split; acq-;-¬skips; acq-;-≄ret)

open import BorrowedCF.Safety.Preservation.Splits.Chain using (InsR; here)
open import BorrowedCF.Safety.Preservation.Splits.Group using (Same; nilS; consS; bindCtx-rsplit)

private
  -- The head of a binder context whose first group is empty carries an acq.
  head0 : ∀ {s b B} {Γ : Ctx (sum (0 ∷ b ∷ B))} → BindCtx s (0 ∷ b ∷ B) Γ → AcqHeadCtx Γ
  head0 (cons-acq _ ah)                            = ah
  head0 (cons-ret/acq _ {Γ₁ = V.[]} _ _ _ _ ah) = ah

  ¬acq-skipret : ∀ {h : 𝕊 0} → ¬ (skip ; ret ≃ acq ; h)
  ¬acq-skipret eq with acq-;-split eq
  ... | inj₁ (_ , e)      = acq-;-≄ret e
  ... | inj₂ (_ , e , _)  = acq-;-¬skips skip e

local⇒¬acqHead′ : ∀ {t₂ : 𝕊 0} → Local t₂ → ¬ Skips t₂ → ∀ u → ¬ (t₂ ≃ acq ; u)
local⇒¬acqHead′ {t₂} L₂ ¬S₂ u eq =
  ¬acq-skipret (head0 C′ .proj₂)
  where
    C₀ : BindCtx u (0 ∷ 1 ∷ []) (⟨ t₂ ⟩ ⸴ V.[])
    C₀ = cons-acq
           (last (cons t₂ skip (λ Sk → acq-;-¬skips Sk ≃-refl)
                           (≃-trans ≃-skipʳ eq) (nil skip)))
           (u , eq)
    I : InsR (⟨ t₂ ⟩) (⟨ skip ; ret ⟩) (⟨ acq ; t₂ ⟩)
             (⟨ t₂ ⟩ ⸴ V.[]) (⟨ skip ; ret ⟩ ⸴ V.[]) (⟨ acq ; t₂ ⟩ ⸴ V.[])
    I = here
    C′ : BindCtx u (0 ∷ 1 ∷ 1 ∷ []) (⟨ skip ; ret ⟩ ⸴ ⟨ acq ; t₂ ⟩ ⸴ V.[])
    C′ = bindCtx-rsplit (0 ∷ []) {B₂ = []} {Γr = V.[]} L₂ ¬S₂ (≃-sym ≃-skipˡ) I C₀ (consS V.[] nilS)
