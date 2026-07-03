module BorrowedCF.Simulation2.RevComFrontier where

-- ============================================================================
-- DETERMINATION of the reverse-RU-Com send-position frontier (BUILD vs REFUTE).
--
-- QUESTION: in sim← , given an untyped RU-Com step on the translation image of a
-- WELL-TYPED ν-process, can the send's session channel sit at a BLOCK-1 POSITION
-- z > 0F (behind a leading ⟨skip⟩ borrow at 0F that is USED as the send's
-- message PAYLOAD), such that the untyped RU-Com FIRES (its channel triple middle
-- IS the ν data channel) but the typed TR.R-Com — which fires ONLY with the send
-- channel literally ` 0F — CANNOT match?
--
-- VERDICT: **BUILD SUCCEEDS**.  The typed binder does NOT force the ν-bound
-- communicating channel to the block-1 head.  A concrete, fully well-typed
-- ν (3 ∷ []) (3 ∷ []) is constructed below (⊢ν), in which
--   * the block-1 head 0F is a ⟨skip⟩ borrow (Unr) used as the send PAYLOAD,
--   * the com-send's channel handle ⟨ msg ‼ ⟨skip⟩ ⟩ sits at block-1 position 1F,
--   * dually the recv's handle ⟨ msg ⁇ ⟨skip⟩ ⟩ sits at block-2 position 1F,
-- so the untyped image fires RU-Com on the ν data channels (fires-untyped), but
-- the send channel is ` 1F ≠ ` 0F, so no R-Com pattern matches (off-head), and
-- the skip at 0F is USED (count ≡ 1) so it is not R-Discardable to bring the
-- handle to 0F.
--
-- This DIRECTLY refutes the REFUTE hypothesis ("BindCtx′/New/structBinder
-- structurally place the ν-bound communicating channel at the block-1 head"):
-- see `com-handle-off-head`.  Hence sim← is FALSE as written; the fix is to
-- GENERALIZE TR.R-Com to fire at any block-1 msg-channel position (a calculus
-- change the user must approve).
--
-- Realizes RevComPayloadSkip's thread-level crux (skip-payload at 0F, com at 1F)
-- as a full ν-bound process, and refutes ComHandleProbe's "send-handle ≡ 0F"
-- verdict: its argument (B) only rules out a ;-EARLIER live borrow, not a skip
-- borrow consumed as the send's PAYLOAD (a ⊗-parallel use that ∥/;-transmutes
-- into the ordered block-1 binder because ⟨skip⟩ is Unr).
-- ============================================================================

open import Data.Vec.Functional as F using ()
open import Data.List.Relation.Unary.All as All using (All)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using ()
import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Equivalence as CE

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Types.Equivalence using (≃𝕊-assoc; ≃𝕊-skipʳ; ≃𝕊-skipˡ)
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Simulation2.Confine using (count)
open import BorrowedCF.Processes.Bisim using (chanTriple; Ub[_])

open Fin.Patterns
open Nat.Variables

-- ── The bound session : starts with a skip, then a msg ‼ ⟨skip⟩ ──────────────
Sess : 𝕊 0
Sess = skip ; msg ‼ ⟨ skip ⟩

Ns : New Sess
Ns = New._;_ New.skip New.msg

skip-Unr : Unr ⟨ skip {0} ⟩
skip-Unr = ⟨ skip ⟩

skip-Mobile : Mobile ⟨ skip {0} ⟩
skip-Mobile = unr⇒mobile skip-Unr

-- ── Block-1 (send side) : session (skip ; msg ‼ ⟨skip⟩) ; end ‼ ─────────────
--    peeled into 3 handles  0F : ⟨skip⟩ , 1F : ⟨msg ‼ ⟨skip⟩⟩ , 2F : ⟨end ‼⟩.
Γs : Ctx 3
Γs = ⟨ skip ⟩ F.∷ ⟨ msg ‼ ⟨ skip ⟩ ⟩ F.∷ ⟨ end ‼ ⟩ F.∷ (λ ())

↑ˡ0-3 : (x : 𝔽 3) → x ↑ˡ 0 ≡ x
↑ˡ0-3 0F = refl
↑ˡ0-3 1F = refl
↑ˡ0-3 2F = refl

bc1′ : BindCtx′ (Sess ; end ‼) 3 (Γs ∘ wkʳ 0)
bc1′ =
  cons {s₁ = skip} {s₂ = msg ‼ ⟨ skip ⟩ ; end ‼}
       (λ { (_ ; ()) }) (≃-sym (Eq*.return ≃𝕊-assoc)) (λ x → sym (cong Γs (↑ˡ0-3 x)))
    (cons {s₁ = msg ‼ ⟨ skip ⟩} {s₂ = end ‼}
          (λ { (() ; _) }) ≃-refl (λ _ → refl)
      (cons {s₁ = end ‼} {s₂ = skip}
            (λ ()) ≃-skipʳ (λ _ → refl)
        (nil skip)))

C1 : BindCtx (Sess ; end ‼) (3 ∷ []) Γs
C1 = last bc1′

-- ── Block-2 (recv side) : dual session (skip ; msg ⁇ ⟨skip⟩) ; end ⁇ ────────
Γr : Ctx 3
Γr = ⟨ skip ⟩ F.∷ ⟨ msg ⁇ ⟨ skip ⟩ ⟩ F.∷ ⟨ end ⁇ ⟩ F.∷ (λ ())

bc2′ : BindCtx′ (dual Sess ; end (dualPol ‼)) 3 (Γr ∘ wkʳ 0)
bc2′ =
  cons {s₁ = skip} {s₂ = msg ⁇ ⟨ skip ⟩ ; end ⁇}
       (λ { (_ ; ()) }) (≃-sym (Eq*.return ≃𝕊-assoc)) (λ x → sym (cong Γr (↑ˡ0-3 x)))
    (cons {s₁ = msg ⁇ ⟨ skip ⟩} {s₂ = end ⁇}
          (λ { (() ; _) }) ≃-refl (λ _ → refl)
      (cons {s₁ = end ⁇} {s₂ = skip}
            (λ ()) ≃-skipʳ (λ _ → refl)
        (nil skip)))

C2 : BindCtx (dual Sess ; end (dualPol ‼)) (3 ∷ []) Γr
C2 = last bc2′

-- The DECISIVE structural fact refuting REFUTE: the com-send handle is at 1F,
-- behind a ⟨skip⟩ at 0F — the binder does NOT place the com-channel at the head.
com-handle-off-head : (Γs 0F ≡ ⟨ skip ⟩) × (Γs 1F ≡ ⟨ msg ‼ ⟨ skip ⟩ ⟩)
com-handle-off-head = refl , refl

⊢B₁ : ⊢ᴮ (3 ∷ [])
⊢B₁ = All.[]
⊢B₂ : ⊢ᴮ (3 ∷ [])
⊢B₂ = All.[]

-- ── The body context : Γs (0..2) then Γr (3..5) ─────────────────────────────
Γbody : Ctx 6
Γbody = (Γs ⸴* Γr) ⸴* (λ ())

-- ── Send thread : send (payload = skip 0F) over channel 1F, then close end 2F ─
sendThread : Tm 6
sendThread = (K `send ·¹ ((` 0F) ⊗ (` 1F))) ; (K (`end ‼) ·¹ (` 2F))

⊢pair : Γbody ; (` 0F) ∥ (` 1F) ⊢ (` 0F) ⊗ (` 1F) ∶ ⟨ skip ⟩ ⊗¹ ⟨ msg ‼ ⟨ skip ⟩ ⟩ ∣ ℙ
⊢pair = T-Pair par par (T-Var 0F refl) (T-Var 1F refl)

⊢sendCore : Γbody ; (` 0F) ∥ (` 1F) ⊢ K `send ·¹ ((` 0F) ⊗ (` 1F)) ∶ `⊤ ∣ 𝕀
⊢sendCore = T-Weaken (≼-refl ∥-unit₁)
  (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send skip-Mobile)))
    (T-Conv ≃-refl ℙ≤ϵ ⊢pair))

⊢end2 : Γbody ; (` 2F) ⊢ K (`end ‼) ·¹ (` 2F) ∶ `⊤ ∣ 𝕀
⊢end2 = T-Weaken (≼-refl ∥-unit₁)
  (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end))
    (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 2F refl)))

⊢sendThread : Γbody ; (((` 0F) ∥ (` 1F)) ; (` 2F)) ⊢ₚ ⟪ sendThread ⟫
⊢sendThread = TP-Expr (T-Seq `⊤ ⊢sendCore ⊢end2)

-- ── Recv thread : recv over channel 4F, then close end 5F (blocked on recv) ──
recvThread : Tm 6
recvThread = (K `recv ·¹ (` 4F)) ; (K (`end ⁇) ·¹ (` 5F))

⊢recv4 : Γbody ; (` 4F) ⊢ K `recv ·¹ (` 4F) ∶ ⟨ skip ⟩ ∣ 𝕀
⊢recv4 = T-Weaken (≼-refl ∥-unit₁)
  (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`recv skip-Mobile)))
    (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 4F refl)))

⊢end5 : Γbody ; (` 5F) ⊢ K (`end ⁇) ·¹ (` 5F) ∶ `⊤ ∣ 𝕀
⊢end5 = T-Weaken (≼-refl ∥-unit₁)
  (T-AppUnr refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end))
    (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 5F refl)))

⊢recvThread : Γbody ; ((` 4F) ; (` 5F)) ⊢ₚ ⟪ recvThread ⟫
⊢recvThread = TP-Expr (T-Seq ⟨ skip ⟩ ⊢recv4 ⊢end5)

-- ── Discard thread : consume the block-2 leading ⟨skip⟩ at 3F ─────────────────
discThread : Tm 6
discThread = (` 3F) ; *

⊢discThread : Γbody ; ((` 3F) ; []) ⊢ₚ ⟪ discThread ⟫
⊢discThread = TP-Expr
  (T-Seq ⟨ skip ⟩ (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 3F refl))
                  (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)))

bodyProc : Proc 6
bodyProc = ⟪ sendThread ⟫ ∥ (⟪ recvThread ⟫ ∥ ⟪ discThread ⟫)

cleanStruct : Struct 6
cleanStruct = (((` 0F) ∥ (` 1F)) ; (` 2F))
            ∥ (((` 4F) ; (` 5F)) ∥ ((` 3F) ; []))

⊢bodyClean : Γbody ; cleanStruct ⊢ₚ bodyProc
⊢bodyClean = TP-Par ⊢sendThread (TP-Par ⊢recvThread ⊢discThread)

resStruct : Struct 6
resStruct = (structBinder (3 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 3 𝐂.⋯ᵣ 𝐂.wkʳ 0)
          ∥ (structBinder (3 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 3 𝐂.⋯ᵣ 𝐂.wkʳ 0)
          ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 6)

U0 : UnrCx Γbody (` 0F)
U0 = ` skip-Unr

U3 : UnrCx Γbody (` 3F)
U3 = ` skip-Unr

transmute01 : Γbody ∶ ((` 0F) ∥ (` 1F)) ≈ ((` 0F) ; (` 1F))
transmute01 = ∥/;-transmute (inj₁ U0)

transmute3R : Γbody ∶ ((` 3F) ∥ ((` 4F) ; (` 5F))) ≈ ((` 3F) ; ((` 4F) ; (` 5F)))
transmute3R = ∥/;-transmute (inj₁ U3)

L≈A : Γbody ∶ (((` 0F) ∥ (` 1F)) ; (` 2F))
              ≈ (((` 0F) ; ((` 1F) ; ((` 2F) ; []))) ∥ [])
L≈A = ≈-trans (CE.;-cong transmute01 ≈-refl)
        (≈-trans CE.;-assoc
          (≈-trans (CE.;-cong ≈-refl (CE.;-cong ≈-refl (≈-sym ;-unit₂)))
            (≈-sym ∥-unit₂)))

R≈B : Γbody ∶ (((` 4F) ; (` 5F)) ∥ ((` 3F) ; []))
              ≈ (((` 3F) ; ((` 4F) ; ((` 5F) ; []))) ∥ [])
R≈B = ≈-trans (CE.∥-cong ≈-refl ;-unit₂)
        (≈-trans CE.∥-comm
          (≈-trans transmute3R
            (≈-trans (CE.;-cong ≈-refl (CE.;-cong ≈-refl (≈-sym ;-unit₂)))
              (≈-sym ∥-unit₂))))

-- resStruct in normal form (∥ is left-associative : (blk1 ∥ blk2) ∥ []).
NF : Struct 6
NF = ((((` 0F) ; ((` 1F) ; ((` 2F) ; []))) ∥ [])
      ∥ (((` 3F) ; ((` 4F) ; ((` 5F) ; []))) ∥ []))
      ∥ []

resStruct≡NF : resStruct ≡ NF
resStruct≡NF = refl

clean≈NF : Γbody ∶ cleanStruct ≈ NF
clean≈NF = ≈-trans (≈-sym ∥-unit₂) (CE.∥-cong (CE.∥-cong L≈A R≈B) ≈-refl)

body≼ : Γbody ∶ cleanStruct ≼ resStruct
body≼ = subst (λ z → Γbody ∶ cleanStruct ≼ z) (sym resStruct≡NF) (≼-refl clean≈NF)

⊢resBody : Γbody ; resStruct ⊢ₚ bodyProc
⊢resBody = TP-Weaken body≼ ⊢bodyClean

theProc : Proc 0
theProc = ν (3 ∷ []) (3 ∷ []) bodyProc

⊢ν : (λ ()) ; [] ⊢ₚ theProc
⊢ν = TP-Res Ns ‼ ⊢B₁ ⊢B₂ C1 C2 ⊢resBody

-- ── The skip at block-1 head 0F is USED (count ≡ 1) : not R-Discardable ──────
skip0-used : count {6} 0F cleanStruct ≡ 1
skip0-used = refl

-- ── (ii) fires-untyped ───────────────────────────────────────────────────────
-- Under U[_], EVERY block handle (in particular the send channel at block-1
-- position 1F) maps to a chanTriple whose MIDDLE is that block's ν data channel
-- c.  With c the block-1 data channel, the send channel is chanTriple(_,c,_) =
-- RU-Com's send form 𝓒[ _ × c × _ ]; dually the recv channel (block-2 position
-- 1F) has middle = the block-2 data channel.  So the untyped image presents the
-- RU-Com redex REGARDLESS of the 1F block-position (both endpoints are Values).
block1-pos1-image : ∀ {N} (e₁ e₂ : Tm N) (c : 𝔽 N)
  → Ub[ 3 ] (e₁ , c , e₂) 1F ≡ chanTriple (* , c , *)
block1-pos1-image e₁ e₂ c = refl

-- ── (iii) off-head ───────────────────────────────────────────────────────────
-- The com-send's channel handle in sendThread is ` 1F (block-1 position 1),
-- whereas TR.R-Com (Reduction/Processes/Typed.agda) fires ONLY with the send
-- channel literally ` 0F.  Since ` 1F ≠ ` 0F, and the block-1 head 0F is occupied
-- by the ⟨skip⟩ PAYLOAD (skip0-used : count ≡ 1, hence not R-Discardable to
-- bring a handle to 0F), NO R-Com pattern matches this well-typed ν-process.
send-channel : Tm 6
send-channel = ` 1F

off-head : ¬ (send-channel ≡ ` 0F)
off-head ()
