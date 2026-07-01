{-# OPTIONS --rewriting #-}
-- ============================================================================
--  RSPLIT BISIMULATION ISSUE — the DOWNSTREAM-SIBLING case, machine-checked.
--
--  RsplitCounterexample.agda exhibits the OFF-HANDLE sibling (owning the split
--  chain's own second borrow).  That redex is VACUOUS: no well-typed process
--  can have a sibling own the split chain's off-handle (RsplitTypingRefute /
--  RsplitFramedRedex).  So it does NOT refute the simulation.
--
--  Here we take the DOWNSTREAM-SIBLING case: a SEPARATE chain (in B₂, after the
--  split chain), owned by the sibling.  Separate chains compose in parallel
--  freely, so this is NOT vacuous.  Config:
--       B₁ = [],  b₁ = 0,  B₂ = 1 ∷ [],  B = [].
--   front bind group  =  B₁ ++ suc b₁ ∷ B₂  =  1 ∷ 1 ∷ []
--     chain 0 (borrow 0F) = the split chain (rsplit fires here, handle inj 0F)
--     chain 1 (borrow 1F) = the DOWNSTREAM sibling chain (owned by P)
--   grown group       =  B₁ ++ 1 ∷ suc b₁ ∷ B₂  =  1 ∷ 1 ∷ 1 ∷ []
--
--  We compute, with the REAL U[_] and the REAL reductions, the three terms
--    Usrc = U[src],  Ured = U[typed-reduct],  Q = untyped reduct of Usrc,
--  and ask the DECISIVE question the leafRec ≋ obligation turns on:
--    is  Q ≋ Ured  (bridgeable — no bug, translation fine) or  ¬(Q ≋ Ured)
--    (genuine bisimulation failure — real translation bug)?
--
--  Unlike the off-handle case (variable-vs-CONSTANT, trivially ¬≋ but vacuous),
--  the downstream mismatch is variable-vs-VARIABLE (` 0F vs ` 1F), which is
--  exactly where a binder-reordering ≋ move could in principle bridge.
-- ============================================================================

module BorrowedCF.RsplitBisimIssue where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Congruence
open import BorrowedCF.Processes.Typed using (BindGroup)

open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)

import BorrowedCF.RsplitOwnershipProbe as Probe
import BorrowedCF.Processes.Typed as T
import BorrowedCF.Reduction.Processes.Typed as TR
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Reduction.Processes.Untyped as UR

open T.Proc
open U.Proc
open TR using (_─→ₚ_)

-- split-renamings for  B₁ = [],  B₂ = 1 ∷ [],  B = [].
module 𝐒 = TR.SplitRenamings [] (1 ∷ []) []

sₚ : 𝕊 0
sₚ = Probe.sP

-- The R-RSplit redex body at scope  sum (1 ∷ 1 ∷ []) + sum [] + 0 = 2:
--   rsplit thread on the split-chain handle  inj 0F,
--   sibling  << recv · ` 1F >>  owning the DOWNSTREAM chain's borrow 1F.
redexBody : T.Proc 2
redexBody =
    ⟪ [] [ K (`rsplit sₚ) · (` 𝐒.inj {1 ∷ []} {0} 0F) ]* ⟫
  ∥ ⟪ K `recv · (` 1F) ⟫

src : T.Proc 0
src = ν (1 ∷ 1 ∷ []) [] redexBody

-- typed step, constructor DEFINES the reduct (no hand-transcription).
src─→Σ : Σ[ Q ∈ T.Proc 0 ] (src ─→ₚ Q)
src─→Σ = _ , TR.R-RSplit {B₁ = []} {B₂ = 1 ∷ []} {B = []} {b₁ = 0} {s = sₚ} {E = []}

typedReduct : T.Proc 0
typedReduct = proj₁ src─→Σ

src─→typedReduct : src ─→ₚ typedReduct
src─→typedReduct = proj₂ src─→Σ

Usrc : U.Proc 0
Usrc = U[ src ] (λ())

Ured : U.Proc 0
Ured = U[ typedReduct ] (λ())

-- Ured's inner body (under ν + 2 φ drop), from the normalize output.
BODY : U.Proc 4
BODY =   ⟪ ((* ⊗ (` 2F)) ⊗ (` 1F)) ⊗ (((` 1F) ⊗ (` 2F)) ⊗ (` 0F)) ⟫
       ∥ ⟪ K `recv · (((` 0F) ⊗ (` 2F)) ⊗ *) ⟫

-- The φ-comm move (swapping the two φ drop binders) applies assocSwapᵣ 1 1.
BODY-swap : U.Proc 4
BODY-swap = BODY U.⋯ₚ assocSwapᵣ 1 1

-- ============================================================================
--  THE DECISIVE TEST — is the slot-0 mismatch ≋-bridgeable (proof-gap) or not
--  (translation bug)?  Both  Ured  and the untyped reduct  Q  have skeleton
--  ν (φ drop (φ drop (T ∥ S))) — TWO φ drop binders, which φ-comm′ can swap
--  (applying  assocSwapᵣ 1 1).  We test whether that swap reconciles the
--  sibling triple with the untyped reduct's  ( · )ₚ weakenᵣ  image.
-- ============================================================================

-- Ured's sibling receive-triple (under ν + 2 φ):  slot0 = ` 0F  (a φ drop).
Ured-sib : Tm 4
Ured-sib = ((` 0F) ⊗ (` 2F)) ⊗ *

-- The φ-comm move on the two φ drops applies  assocSwapᵣ 1 1  to the body,
-- sending  ` 0F ↦ ` 1F  in slot0:
swap-sib : Tm 4
swap-sib = ((` 1F) ⊗ (` 2F)) ⊗ *

sib-under-φcomm : Ured-sib ⋯ assocSwapᵣ 1 1 ≡ swap-sib
sib-under-φcomm = refl

-- Usrc's sibling receive-triple (under ν + 1 φ):  slot0 = ` 0F.
Usrc-sib : Tm 3
Usrc-sib = ((` 0F) ⊗ (` 1F)) ⊗ *

-- The UNTYPED reduct gives the sibling  ( · )ₚ weakenᵣ  (shift-by-one for the
-- fresh φ drop RU-RSplit introduces):
reduct-sib-matches : Usrc-sib ⋯ weakenᵣ ≡ swap-sib
reduct-sib-matches = refl

-- ⇒ φ-comm(Ured-sibling)  =  weakenᵣ(Usrc-sibling)  =  untyped-reduct-sibling.
-- The slot-0 "flip" is EXACTLY a φ-comm (binder-reorder) artifact: it is
-- ≋-bridgeable at the sibling.  This is UNLIKE the vacuous off-handle case
-- (RsplitCounterexample), where the mismatch is  ` 0F  vs  K `unit  (variable
-- vs CONSTANT) — no renaming bridges that.  Here it is variable-vs-variable
-- (` 0F vs ` 1F), and the specific ≋ move (φ-comm) closes it.
sibling-reconciles : (Ured-sib ⋯ assocSwapᵣ 1 1) ≡ (Usrc-sib ⋯ weakenᵣ)
sibling-reconciles = refl

-- ============================================================================
--  WHAT THIS DOES AND DOES NOT ESTABLISH (honest scope).
--
--  ESTABLISHED (machine-checked above):
--   * For the DOWNSTREAM-SIBLING (non-vacuous) rsplit redex, the leafRec-level
--     mismatch that RsplitLeaf reported (grown slot0 = ` 0F vs weakenᵣ-ungrown
--     slot0 = ` 1F) is variable-vs-VARIABLE, and at the SIBLING it is exactly a
--     φ-comm binder-reorder artifact: φ-comm(Ured-sib) = reduct-sib.
--   * This is categorically UNLIKE RsplitCounterexample's off-handle mismatch,
--     which is variable-vs-CONSTANT (` 0F vs K `unit) — no renaming/≋ bridges
--     that (but that redex is vacuous anyway: RsplitTypingRefute).
--   * leafRec is stated as a ≋ (structural congruence up-to), but Splits.agda
--     discharges it via ≡→≋ leafRec≡; RsplitLeaf proved the ≡ (leafRec≡) FALSE.
--     The ≡ being false does NOT imply the ≋ is false — and the ≋ constructors
--     (Untyped: ν-swap/ν-comm/φ-comm/νφ-comm) are exactly the binder reorders
--     that move slot0 between ` 0F and ` 1F.
--
--  NOT ESTABLISHED (the decisive open verification):
--   * The FULL leafRec ≋ for the thread as well.  The untyped reduct sits at a
--     DIFFERENT binder order (φ drop (ν (φ drop …)), from νφ-comm-expose then
--     RU-RSplit) than Ured (ν (φ drop (φ drop …))), so the thread reconcile is
--     a MULTI-move ≋ (expose, fire, pull back, align), not a single φ-comm.
--     Whether that full ≋ closes = whether U-rsplit's leafRec is provable via a
--     ≋-transpose proof (NOT the ≡→≋ shortcut).
--
--  UPSHOT: the evidence points to a PROOF-STRATEGY gap (leafRec needs a genuine
--  ≋ proof, mirroring the Bφ-φ-comm machinery already present in Splits.agda),
--  NOT a translation bug — and hence NO translation redesign.  The decisive
--  confirmation is closing leafRec via ≋-transpose (or refuting it with a
--  ≋-invariant).  Until then this is strong evidence, not a proof of no-bug.
-- ============================================================================

