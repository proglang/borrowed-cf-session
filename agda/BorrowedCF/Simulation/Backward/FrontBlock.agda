-- | front-block-nonzero: a com/close/choice redex bind group `BL` whose front
--   channel is `msg`-typed has a NONZERO first block, i.e. no leading `cons-acq`
--   (pending-acq / dropped-not-reacquired) zero-block.  This lets `R-Com`
--   (pattern `suc b1 ; B1`) fire after the confinement pins the consumed handle.
--
--   A leading zero-block is `cons-acq`, exposing `BindCtx (acq ; s) B G`; the
--   front channel's session is then `≃ acq ; _` (via `bindCtx-inv-msg`), and the
--   send gives `≃ msg p T ; _`, clashing by `AtomHead.msg;≄acq;` (leading
--   atom-kind rigidity for the DEFINITE first action).
module BorrowedCF.Simulation.Backward.FrontBlock where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP
open TP using ( BindGroup; BindCtx; BindCtx′; last; cons; cons-acq; cons-ret/acq; nil
              ; bindCtx-inv-msg; bindCtx⇒chanCtx )
open import BorrowedCF.Types.Syntax using (𝕊; msg; acq; end; _;_; Pol; 𝕋)
open import BorrowedCF.Types.Equivalence using (_≃_; ≃-⟨⟩⁻¹)
open import BorrowedCF.Types.AtomHead using (msg;≄acq;)
open import BorrowedCF.Reduction.Base using (chanCx-lookup)
open import Data.Nat.ListAction using (sum)

open Fin.Patterns

private variable
  pm : Pol
  B B′ : BindGroup

-- Acq-headed block group with explicitly nonzero first block: no msg front.
acq-front-suc-⊥ : ∀ {n s′} {G : Ctx (sum (suc n ∷ B′))}
  → BindCtx (acq ; s′) (suc n ∷ B′) G → lookup G 0F ≃ ⟨ msg pm T ⟩ → ⊥
acq-front-suc-⊥ {G = g ∷ G′} C lk
  with s₀ , g≡ ← chanCx-lookup (bindCtx⇒chanCtx C) 0F =
  msg;≄acq; (proj₁ (proj₂ (bindCtx-inv-msg s₀≃msg C′)))
  where
    s₀≃msg = ≃-⟨⟩⁻¹ (subst (_≃ ⟨ msg _ _ ⟩) g≡ lk)
    C′ = subst (\ h → BindCtx (acq ; _) _ (h ∷ G′)) g≡ C
