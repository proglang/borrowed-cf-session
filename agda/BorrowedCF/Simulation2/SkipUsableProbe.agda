module BorrowedCF.Simulation2.SkipUsableProbe where

-- Why the RU-Com send-side normalize is SOUND (NOT a roadblock) -- a subtle
-- clarification of the "leading skip borrows are UNUSED" claim.
--
-- The reverse RU-Com send handle sits at some block-1 slot z (com-image-block1).
-- The block-1 head 0F CAN be a <skip> borrow (New admits `skip ; ...` via
-- New.skip / New._;_; BindCtx' admits a skip head -- its not-Skips premise only
-- forbids an ALL-skip session).  A skip head is Unr, so `com-xS-min` cannot
-- force z == 0 (it only excludes NON-Unr borrows before the send).  The fallback
-- is to R-Discard the leading skip borrows, which needs them UNUSED (count 0).
--
-- NAIVE WORRY (refuted here): a <skip> borrow IS usable IN ISOLATION -- it is
-- Unr => Mobile => a legal `send` payload (⊢thread), and can even be used
-- strictly ;-before a send in a T-Seq thread (⊢seq-thread).  So "skips are
-- inherently unusable" is FALSE.
--
-- WHY THE SEND-SIDE IS SOUND ANYWAY: the block-1 binder `structBinder` is
-- `structNSeq` = an ORDERED ;-chain `0F ; 1F ; ...`, and `a || b` is NOT <= `a ; b`
-- (only ; <= ||).  A com send thread must be BLOCKED with the send at the head
-- (value frames only); the only seq frame is `[] ; e` (hole on the LEFT), and
-- `E-Seq : Value e1 -> e1 ; e2 --> e2` fires the moment a VALUE precedes a `;`.
-- Hence:
--   (a) a borrow used ;-BEFORE the blocked send (in its thread) is a value-;
--       prefix that E-Seq-reduces -- so the send would NOT be blocked;
--   (b) a borrow used in a PARALLEL residual thread gives usage `0F || z`, which
--       is NOT <= the sequential binder `0F ; ... ; z` (parallel never fits ;).
-- Therefore every block-1 borrow ;-BEFORE the blocked send handle z is UNUSED
-- (count 0), so R-Discard / strengthen-Proc-gen legitimately peels them and
-- normalize-block1 brings the live handle to 0F.  The ⊢seq-thread witness below
-- is NOT a counterexample: its send is NOT blocked (E-Seq fires first), so it is
-- not a valid com redex.  NET: normalize is SOUND; the count-0 lemma the proof
-- needs is discharged via this ordering+blockedness argument (NOT via any
-- "skips are inherently unused" claim, which is false).

open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Simulation2.Confine using (count)

open Fin.Patterns
open Nat.Variables

-- A context whose slot 0F is a <skip> borrow (Unr) and slot 1F is the
-- msg-send handle whose payload type is <skip>.
G2 : Ctx 2
G2 = ⟨ skip ⟩ F.∷ ⟨ msg ‼ ⟨ skip ⟩ ⟩ F.∷ (λ ())

-- <skip> is Unr, hence Mobile -- so it is a legal `send` payload.
skip-Unr : Unr ⟨ skip {0} ⟩
skip-Unr = ⟨ skip ⟩

skip-Mobile : Mobile ⟨ skip {0} ⟩
skip-Mobile = unr⇒mobile skip-Unr

-- The pair (payload = the skip borrow 0F) (x) (handle = 1F).
⊢pair : G2 ; (` 0F) ∥ (` 1F) ⊢ (` 0F) ⊗ (` 1F) ∶ ⟨ skip ⟩ ⊗¹ ⟨ msg ‼ ⟨ skip ⟩ ⟩ ∣ ℙ
⊢pair = T-Pair par par (T-Var 0F refl) (T-Var 1F refl)

-- ISOLATED thread using the skip borrow 0F as a send payload (parallel usage
-- `0F || 1F`, which does NOT fit a com's sequential block-1 binder `0F ; 1F`).
⊢send : G2 ; [] ∥ ((` 0F) ∥ (` 1F)) ⊢ K `send ·¹ ((` 0F) ⊗ (` 1F)) ∶ `⊤ ∣ 𝕀
⊢send = T-AppUnr refl 𝕀≤𝕀
          (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send skip-Mobile)))
          (T-Conv ≃-refl ℙ≤ϵ ⊢pair)

⊢thread : G2 ; [] ∥ ((` 0F) ∥ (` 1F)) ⊢ₚ ⟪ K `send ·¹ ((` 0F) ⊗ (` 1F)) ⟫
⊢thread = TP-Expr ⊢send

skip-used : count {2} 0F ([] ∥ ((` 0F) ∥ (` 1F))) ≡ 1
skip-used = refl

-- New admits a leading skip prefix, so the block-1 session can start with skip.
new-leading-skip : New {0} (skip ; msg ‼ ⟨ skip {0} ⟩)
new-leading-skip = skip ; msg

-- ── ORDERING-RESPECTING variant (still NOT a com redex) ──────────────────────
-- Here the skip 0F is used strictly ;-before the send handle 1F (usage
-- `0F ; ([] || ([] || 1F))`, matching the sequential binder).  BUT the send is
-- NOT the head redex: `` ` 0F `` is a VALUE, so `E-Seq` fires first and the
-- thread steps to the send -- it is not "blocked on send".  So this thread is
-- also not a valid com redex; it demonstrates precisely why a BLOCKED send
-- cannot have a ;-earlier borrow use.
G2b : Ctx 2
G2b = ⟨ skip ⟩ F.∷ ⟨ msg ‼ `⊤ ⟩ F.∷ (λ ())

⊢seq-send : G2b ; ((` 0F) ; ([] ∥ ([] ∥ (` 1F))))
          ⊢ (` 0F) ; (K `send ·¹ (K `unit ⊗ (` 1F))) ∶ `⊤ ∣ 𝕀
⊢seq-send =
  T-Seq ⟨ skip ⟩
    (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl))
    (T-AppUnr refl 𝕀≤𝕀
      (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send (unr⇒mobile `⊤))))
      (T-Conv ≃-refl ℙ≤ϵ (T-Pair par par (T-Const `unit) (T-Var 1F refl))))

⊢seq-thread : G2b ; ((` 0F) ; ([] ∥ ([] ∥ (` 1F))))
            ⊢ₚ ⟪ (` 0F) ; (K `send ·¹ (K `unit ⊗ (` 1F))) ⟫
⊢seq-thread = TP-Expr ⊢seq-send

seq-skip-used : count {2} 0F ((` 0F) ; ([] ∥ ([] ∥ (` 1F)))) ≡ 1
seq-skip-used = refl
