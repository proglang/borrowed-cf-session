-- | Re-typing the head of a binder group after a choice.
--
--   `R-Choice` keeps both binder groups exactly as they are; only the two
--   communicating handles change type, from `brn p σ₁ σ₂` to the selected
--   branch.  `bindCtx-brn` says that a group whose FIRST handle starts with a
--   `p`-choice has a session that starts with the same `p`-choice, and it
--   hands back a rebuilder that reassembles the group with the branch in place
--   of the choice.  It is the `brn` counterpart of
--   `Processes.Typed.bindCtx-inv-msg`, except that a choice head cannot be
--   peeled off the group (the group keeps its arity), so what comes back is a
--   re-typing function rather than a shorter `BindCtx`.
module BorrowedCF.Safety.Preservation.Choice.BindCtxBrn where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Ctx; _⸴_; _⸴*_)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)

open import BorrowedCF.Safety.Preservation.Support.BrnView

open Nat.Variables

private variable
  i : Bool
  t : 𝕊 0

-- The rebuilder: given a session `v` equivalent to the projected one, the
-- group is well typed again with `t` (the branch) as its first handle.
Rebuild : ∀ (p : Pol) (i : Bool) (t : 𝕊 0) (n : ℕ) (B : BindGroup) →
  Ctx (n + sum B) → 𝕊 0 → Set
Rebuild p i t n B Γ S* =
  ∀ {v} → ¬ Skips v → S* ≃ v → BindCtx v (suc n ∷ B) (⟨ t ⟩ ⸴ Γ)

bindCtx-brn : ∀ {p} {s′ S : 𝕊 0} {n B} {Γ : Ctx (n + sum B)} →
  BrnV p i s′ t →
  BindCtx S (suc n ∷ B) (⟨ s′ ⟩ ⸴ Γ) →
  ∃[ S* ] BrnV p i S S* × Rebuild p i t n B Γ S*
bindCtx-brn {s′ = s′} {Γ = Γ} V C with ⟨ s′ ⟩ ⸴ Γ in Γ-eq

bindCtx-brn V (last (cons s₁ w ¬skips split rest)) | _
  with (refl , refl) ← V.∷-injective Γ-eq
  with S* , VS , tw≃ ← ≃-brnv split (hd V)
  = S* , VS , λ ¬Sk S*≃v → last (cons _ w ¬Sk (≃-trans tw≃ S*≃v) rest)

bindCtx-brn {t = t} V (cons-ret/acq s₁ {s₂ = s₂} s≃ ¬skips₂ (cons sh w ¬skips split rest) C ah) | _
  with (refl , refl) ← V.∷-injective Γ-eq
  with atom-;-unsnoc ret split
... | inj₂ (w′ , shw′≃ , w′ret≃w)
  with z , Vz , tw′≃z ← ≃-brnv shw′≃ (hd V)
  with S* , VS , zs₂≃ ← ≃-brnv s≃ (hd Vz)
  = S* , VS , λ ¬Sk S*≃v →
      cons-ret/acq (t ; w′)
        (≃-trans (≃-; tw′≃z ≃-refl) (≃-trans zs₂≃ S*≃v))
        ¬skips₂
        (cons t w (λ{ (_ ; ()) })
          (≃-trans (≃-; ≃-refl (≃-sym w′ret≃w)) (≃-sym ≃-assoc-;))
          rest)
        C ah

bindCtx-brn {t = t} V (cons-ret/acq s₁ {s₂ = s₂} s≃ ¬skips₂ (cons sh w ¬skips split rest) C ah) | _
    | inj₁ Skw
  with (refl , refl) ← V.∷-injective Γ-eq
  with _ , Vsr , t≃ ← ≃-brnv (≃-trans (≃-sym (≃-skipsʳ Skw)) split) V
  with Vsr
... | tl _ ()
... | hd {z = z′} c
  with S* , VS , z′s₂≃ ← ≃-brnv s≃ (hd c)
  = S* , VS , λ ¬Sk S*≃v →
      cons-ret/acq z′
        (≃-trans z′s₂≃ S*≃v)
        ¬skips₂
        (cons t w (λ{ (_ ; ()) })
          (≃-trans (≃-skipsʳ Skw) t≃)
          rest)
        C ah
