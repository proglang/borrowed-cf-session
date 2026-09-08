-- | The R-Acq probe (agent P4b).
--
--   P4's `pres-Acq` obstacle was: the structure-equivalence rule
--   `∥′-tm-;` lets a `;` be split into a `∥` at a MOBILE handle, so the
--   binder group `x₀ ; x₁ ; …` of a `TP-Res` could in principle be split
--   across two parallel threads whenever the group's head `x₀ : ⟨ acq ; t ⟩`
--   is mobile.  After `acq x₀` the head is `⟨ t ⟩` and no longer mobile, so
--   such a split could not be replayed on the reduct, and preservation would
--   fail for R-Acq.
--
--   THE PROBE FAILS: the left-hand side of such a counterexample is not
--   typable.  `Mobile ⟨ acq ; t ⟩` says `Bounded t`, i.e. the head's own
--   continuation already carries the group's terminator (`ret` for a
--   non-final group, `end p` for the final one), and nothing may follow a
--   terminator inside one group (`BindCtx′.cons` demands `¬ Skips`).  So a
--   mobile head is ALONE in its group, and conversely a group of width ≥ 2
--   has an IMMOBILE head — `head-¬mobile` below.  No `∥′-tm-;` step is then
--   available at the acquired handle, which is what makes `pres-Acq`
--   provable (`Safety/Preservation/Handles/Acq.agda`).
--
--   This is the `BindCtx`-local half of `Simulation/BackwardSoup/Position/
--   Crux.agda`'s `mobile-head-alone` / `group-head-¬mobile`; those are stated
--   over the `GroupOf` navigation of a whole binder list, and their
--   `block-mobile-head-width1` core is `private`.  The version here is the
--   one R-Acq needs (index `0F`, the head of the group that `cons-acq`
--   introduces) and costs no `Simulation/` import.
module BorrowedCF.Safety.Preservation.Handles.AcqProbe where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Types.NoTerm
  using ( NoTerm; new⇒noTerm; noTerm-acq; noTerm-split
        ; TermAtom; termAtom-ret; termAtom-end; bounded-tail-skips )

open Nat.Variables
open Fin.Patterns

private
  -- A mobile handle at the front of a block ENDS the block: its `Bounded`
  -- continuation already reaches the chain's trailing terminator, so the
  -- remainder skips and the `BindCtx′` chain stops.
  block-width1 : ∀ {n} {Γ : Ctx (suc n)} {c q τ : 𝕊 0} →
    TermAtom τ → NoTerm q → c ≃ q ; τ → BindCtx′ c Γ →
    Mobile (Γ ﹫ 0F) → n ≡ 0
  block-width1 A NTq eq (cons u₁ rest ¬sk split (nil _)) mob = refl
  block-width1 A NTq eq (cons u₁ rest ¬sk split (cons _ _ ¬sk′ _ _)) ⟨ w , Bw , u≃ ⟩ =
    ⊥-elim (¬sk′ (bounded-tail-skips A NTq
                    (≃-bounded (≃-sym u≃) (-;₂ Bw)) (≃-trans split eq)))

-- THE PROBE RESULT.  The head of a binder group of width ≥ 2 is immobile.
head-¬mobile : ∀ {b B} {Γ : Ctx (sum (suc (suc b) ∷ B))} {c q τ : 𝕊 0} →
  TermAtom τ → NoTerm q → c ≃ q ; τ →
  BindCtx c (suc (suc b) ∷ B) Γ → ¬ Mobile (Γ ﹫ 0F)
head-¬mobile A NTq eq (last C) mob =
  case block-width1 A NTq eq C mob of λ ()
head-¬mobile A NTq eq
  (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ ¬sk₂ front rest ah) mob
  with noTerm-split A NTq ¬sk₂ (≃-trans s≃ eq)
... | q′ , NTs₁ , NTq′ , s₂≃ =
  case block-width1 termAtom-ret NTs₁ ≃-refl front
         (subst Mobile (V.lookup-++ˡ Γ₁ Γ₂ 0F) mob) of λ ()

-- The instance R-Acq needs: the group that `cons-acq` opens is governed by
-- `acq ; (s ; end p)` with `New s`, so if it is at least two binders wide its
-- head — the handle the `acq` consumes — is immobile.
acq-head-¬mobile : ∀ {b B} {Γ : Ctx (sum (suc (suc b) ∷ B))} {s : 𝕊 0} {p} →
  New s → BindCtx (acq ; (s ; end p)) (suc (suc b) ∷ B) Γ → ¬ Mobile (Γ ﹫ 0F)
acq-head-¬mobile N C =
  head-¬mobile termAtom-end (noTerm-acq (new⇒noTerm N)) (≃-sym ≃-assoc-;) C
