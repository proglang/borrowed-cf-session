module BorrowedCF.Simulation2.RevComPayloadSkip where

-- MACHINE-CHECKED refutation of the reverse-RU-Com "count-0" premise
-- (SkipUsableProbe's soundness claim) = the task's Step 1.
--
-- SkipUsableProbe argues: a leading <skip> borrow before a BLOCKED com send is
-- UNUSED, because using it gives a parallel usage and "a || b is NOT <= a ; b".
-- THAT CLAIM IS FALSE for an Unr borrow: the ~=-generator
--   ||'-tm : UnrCx G a + UnrCx G b -> a || b ~= a ; b
-- moves an Unr resource FREELY between parallel and sequential.  Since <skip> is
-- Unr, (` 0F) || (` 1F) ~= (` 0F) ; (` 1F), so the ∥ALLEL send-arg usage DOES
-- fit the ORDERED block-1 binder structNSeq 2 = (` 0F) ; (` 1F).
--
-- Consequence: SkipUsableProbe.⊢thread -- the BLOCKED com send whose channel is
-- 1F (block-1 position 1) and whose PAYLOAD is the skip borrow 0F (position 0,
-- count 1) -- re-types at the ordered com binder.  So position 0 (< the send
-- channel position 1) is USED, hence NOT R-Discardable / not wkn-strippable,
-- and normalize-block1 CANNOT bring the send channel to 0F.  The typed R-Com
-- fires ONLY when the send channel is block-1 position 0F, so this well-typed,
-- blocked com send has no matching typed R-Com: the reverse-simulation RU-Com
-- case is not closable for this configuration without a typing/calculus change.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Simulation2.SkipUsableProbe using (G2; skip-Unr; ⊢thread)
open import BorrowedCF.Simulation2.Confine using (count)

open Fin.Patterns
open Nat.Variables

U0 : UnrCx G2 (` 0F)
U0 = ` skip-Unr

transmute : G2 ∶ (` 0F) ∥ (` 1F) ≈ (` 0F) ; (` 1F)
transmute = ∥/;-transmute (inj₁ U0)

par-below-seq : G2 ∶ ((` 0F) ∥ (` 1F)) ≼ ((` 0F) ; (` 1F))
par-below-seq = ≼-refl transmute

⊢thread-ordered : G2 ; ((` 0F) ; (` 1F)) ⊢ₚ ⟪ K `send ·¹ ((` 0F) ⊗ (` 1F)) ⟫
⊢thread-ordered = TP-Weaken (≼-trans (≼-refl ∥-unit₁) par-below-seq) ⊢thread

pos0-used : count {2} 0F ((` 0F) ; (` 1F)) ≡ 1
pos0-used = refl
