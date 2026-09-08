-- Removing the head binder of the first group from a `BindCtx`, for the two
-- administrative reductions.  `bindCtx-discard` drops a `⟨ skip ⟩` head,
-- `bindCtx-drop` drops a `⟨ ret ⟩` head (and, on the way, shows that the head
-- group of an R-Drop redex is exactly one binder wide).
module BorrowedCF.Safety.Preservation.Handles.BindCtx where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)

open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; noRet-;-fst; ¬noRet-ret
        ; RetTip; noRet-front-cons; retTip-Sc-skips; retTip-≃ )

open Nat.Variables
open Fin.Patterns

private
  ⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃ ⟨ eq ⟩ = eq

  -- `sh ; ret ≃ ret` forces `sh` to skip.
  skips-front : ∀ {sh : 𝕊 0} → sh ; ret ≃ skip ; ret → Skips sh
  skips-front eq with atom-;-unsnoc ret eq
  ... | inj₁ ()
  ... | inj₂ (_ , shy≃skip , _) with ≃-skips (≃-sym shy≃skip) skip
  ...   | (S₁ ; _) = S₁

-- R-Discard: the head of the first group skips, so it can be deleted from the
-- group without touching the rest of the derivation.
bindCtx-discard : ∀ {b₁ B₁} {Γ : Ctx (suc b₁ + sum B₁)} {s : 𝕊 0} {p} →
  (Γ ﹫ 0F) ≃ ⟨ skip ⟩ →
  BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ →
  BindCtx (s ; end p) (b₁ ∷ B₁) (V.tail Γ)
bindCtx-discard head≃ (last (cons s₁ s₂ ¬sk s-split rest)) =
  last (bindCtx′-≃ (≃-trans (≃-trans (≃-sym ≃-skipˡ)
                              (≃-; (≃-sym (⟨⟩≃ head≃)) ≃-refl)) s-split)
                   rest)
bindCtx-discard head≃ (cons-ret/acq sh s≃ ¬skips₂ (cons s₁ s₂ ¬sk s-split rest) C ah) =
  cons-ret/acq sh s≃ ¬skips₂
    (bindCtx′-≃ (≃-trans (≃-trans (≃-sym ≃-skipˡ)
                           (≃-; (≃-sym (⟨⟩≃ head≃)) ≃-refl)) s-split)
                rest)
    C ah

-- R-Drop: the head of the first group returns.  A `last` block is impossible
-- (its session is `New`-derived, hence has no `ret`), and a `cons-ret/acq`
-- block whose front holds a second borrow is impossible too; what remains is a
-- one-binder front block, which turns into a `cons-acq`.
bindCtx-drop : ∀ {b₁ B₁} {Γ : Ctx (suc b₁ + sum B₁)} {s : 𝕊 0} {p} →
  New s → (Γ ﹫ 0F) ≃ ⟨ ret ⟩ →
  BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ →
  BindCtx (s ; end p) (b₁ ∷ B₁) (V.tail Γ)
bindCtx-drop N head≃ (last (cons s₁ s₂ ¬sk s-split rest)) =
  ⊥-elim (¬noRet-ret
    (noRet-≃ (⟨⟩≃ head≃)
      (noRet-;-fst (noRet-≃ (≃-sym s-split) (NoRet._;_ (new⇒noRet N) NoRet.end)))))
bindCtx-drop N head≃ (cons-ret/acq sh s≃ ¬skips₂ (cons s₁ s₂ʰ ¬sk s-split (nil Sk₂)) C ah) =
  cons-acq
    (bindCtx-≃ (≃-; ≃-refl
      (≃-trans (≃-trans (≃-sym ≃-skipˡ)
                 (≃-; (skips⇒skip≃ (skips-front frontEq)) ≃-refl)) s≃))
      C)
    ah
  where
  frontEq : sh ; ret ≃ skip ; ret
  frontEq =
    ≃-trans (≃-sym s-split)
      (≃-trans (≃-; (⟨⟩≃ head≃) (≃-sym (skips⇒skip≃ Sk₂)))
        (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)))
bindCtx-drop N head≃
  (cons-ret/acq sh s≃ ¬skips₂ (cons s₁ s₂ʰ ¬sk s-split (cons _ _ ¬skTail _ _)) C ah) =
  ⊥-elim (¬skTail (retTip-Sc-skips
    (retTip-≃ (≃-sym s-split) (noRet-front-cons noRet-sh)) (⟨⟩≃ head≃)))
  where
  noRet-sh : NoRet sh
  noRet-sh = noRet-;-fst (noRet-≃ (≃-sym s≃) (NoRet._;_ (new⇒noRet N) NoRet.end))
