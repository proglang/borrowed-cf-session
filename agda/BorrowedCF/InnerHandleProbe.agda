module BorrowedCF.InnerHandleProbe where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()
open import Data.List.Relation.Unary.All as All using (All)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Equivalence as CE
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as RR
open import BorrowedCF.Simulation2.Confine using (count)
import BorrowedCF.RsplitTypingRefute as R
open import Data.Sum using (_⊎_; inj₁; inj₂)

open Fin.Patterns
open Nat.Variables

-- ============================================================================
-- INNER-HANDLE CLOSE PROBE.
--
-- Reverse decision R2: R-Close acts ONLY on the HEAD borrow (0F) of a WIDTH-1
-- front block (B₁ = [1]).  The reverse RU-Close/Com/Choice/Acquire cases need
-- to reflect an untyped channel-op back to a typed R-Close/…, but a WELL-TYPED
-- process might present the consumed (close) handle at an INNER (non-head)
-- borrow of a WIDE front block.
--
-- BindCtx′ alone "inhabits" the inner-handle shape (e.g. the front chain
-- msg ‼ ⊤ ; end ⁇ splits into slot0 = ⟨msg ‼ ⊤⟩, slot1 = ⟨end ⁇⟩, with the
-- CLOSE handle ⟨end ⁇⟩ at the SECOND borrow).  The research question is whether
-- that survives at the FULL _;_⊢ₚ_ / TP-Res level -- exactly as the rsplit
-- off-handle "inhabited" a bare BindCtx′ but was refuted at TP-Res by the Sep
-- wall (RsplitTypingRefute / RsplitFramedRedex).
--
-- The rsplit refutation worked because the off-handle needed the two front
-- borrows 0F,1F in DIFFERENT ∥-components (Sep wall: TP-Par yields ∥, but the
-- borrows of one chain are ;-ordered in structBinder).  For CLOSE the SAME
-- thread owns BOTH front borrows and consumes them ;-ORDERED (send slot0, then
-- close slot1) -- which is exactly (` 0F ; ` 1F), the SHAPE structBinder
-- produces.  So there is NO Sep obstruction.
--
-- VERDICT (proved below, machine-checked, hole/postulate-free): REACHABLE.
-- A genuinely well-typed TP-Res process ⊢ ν [2] [1] (front ∥ back) exists whose
-- SINGLE front thread closes the SECOND (inner) borrow ⟨end ⁇⟩ of its width-2
-- front block, after linearly consuming the FIRST borrow ⟨msg ‼ ⊤⟩ (via send).
-- The inner borrow is NOT discardable (R-Discard needs the body to NOT mention
-- the discarded borrow, but slot0 is linearly used).  Hence R2 = "constrain to
-- head" is FALSE: reverse RU-Close needs a calculus rule that closes an inner
-- block handle (or an equivalent narrowing that consumes-then-discards).
-- ============================================================================

sParam : 𝕊 0
sParam = msg ‼ `⊤

Ns : New sParam
Ns = New.msg

↑ˡ0-2 : (x : 𝔽 2) → x ↑ˡ 0 ≡ x
↑ˡ0-2 0F = refl
↑ˡ0-2 1F = refl

-- ── Front bind context:  BindCtx (msg ‼ ⊤ ; end ⁇) (2 ∷ []) Γfront.
--    slot0 = ⟨ msg ‼ ⊤ ⟩  (NON-handle, consumed by send)
--    slot1 = ⟨ end ⁇ ⟩     (CLOSE HANDLE -- the INNER borrow!)
Γfront : Ctx 2
Γfront = ⟨ msg ‼ `⊤ ⟩ F.∷ ⟨ end ⁇ ⟩ F.∷ (λ ())

bc-front′ : BindCtx′ (sParam ; end ⁇) 2 (Γfront ∘ wkʳ 0)
bc-front′ =
  cons (λ { (() ; _) }) ≃-refl (λ x → sym (cong Γfront (↑ˡ0-2 x)))
    (cons (λ ()) ≃-skipʳ (λ _ → refl)
      (nil skip))

Cfront : BindCtx (sParam ; end ⁇) (2 ∷ []) Γfront
Cfront = last bc-front′

-- ── Back bind context:  BindCtx (dual sParam ; end ‼) (1 ∷ []) Γback.
--    dual (msg ‼ ⊤) = msg ⁇ ⊤,  so  msg ⁇ ⊤ ; end ‼.   1 borrow.
Γback : Ctx 1
Γback = (λ _ → ⟨ (msg ⁇ `⊤) ; end ‼ ⟩)

bc-back′ : BindCtx′ ((dual sParam) ; end ‼) 1 (Γback ∘ wkʳ 0)
bc-back′ = cons (λ { (() ; _) }) ≃-skipʳ (λ { 0F → refl }) (nil skip)

Cback : BindCtx ((dual sParam) ; end ‼) (1 ∷ []) Γback
Cback = last bc-back′

-- ── Well-formedness of the bind groups (drop 1 is empty ⇒ trivially All). ──
⊢B₁ : ⊢ᴮ (2 ∷ [])
⊢B₁ = All.[]

⊢B₂ : ⊢ᴮ (1 ∷ [])
⊢B₂ = All.[]

-- ============================================================================
-- The body context: db0,db1 = front borrows, db2 = back borrow.
-- ============================================================================
Γbody : Ctx 3
Γbody = (Γfront ⸴* Γback) ⸴* (λ ())

-- ── FRONT (close) thread.  Owns BOTH front borrows 0F,1F.  Consumes slot0
--    ⟨msg ‼ ⊤⟩ by send, THEN closes slot1 ⟨end ⁇⟩ by `end ⁇` -- the CLOSE at
--    the INNER (second) borrow.  Typed ;-ordered at (` 0F ; ` 1F).
frontThread : Tm 3
frontThread = (K `send · (* ⊗ (` 0F))) ; (K (`end ⁇) · (` 1F))

⊢fsend : Γbody ; (` 0F) ⊢ K `send · (* ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
⊢fsend = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁))
  (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
    (T-Pair par par (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))

⊢fclose : Γbody ; (` 1F) ⊢ K (`end ⁇) · (` 1F) ∶ `⊤ ∣ 𝕀
⊢fclose = T-Weaken (≼-refl ∥-unit₁)
  (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))

⊢frontBody : Γbody ; (((` 0F) ; (` 1F)) ∥ []) ⊢ frontThread ∶ `⊤ ∣ 𝕀
⊢frontBody = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢fsend ⊢fclose)

⊢frontThread : Γbody ; ((` 0F) ; (` 1F)) ⊢ₚ ⟪ frontThread ⟫
⊢frontThread = TP-Expr (T-Weaken (≼-refl ∥-unit₂) ⊢frontBody)

-- ── BACK thread.  Owns db2 = ⟨ msg ⁇ ⊤ ; end ‼ ⟩; recv then close via end ‼.
backThread : Tm 3
backThread =
  `let⊗ (K (`lsplit (msg ⁇ `⊤)) · (` 2F))
   `in ((K `recv · (` 0F)) ; (K (`end ‼) · (` 1F)))

⊢backThread : Γbody ; (` 2F) ⊢ₚ ⟪ backThread ⟫
⊢backThread = TP-Expr (T-Weaken (≼-refl (≈-trans ∥-unit₂ ∥-unit₁)) (T-LetPair par ⊢blsplit ⊢bbody))
  where
    ⊢blsplit : Γbody ; ([] ∥ (` 2F)) ⊢ K (`lsplit (msg ⁇ `⊤)) · (` 2F) ∶ ⟨ msg ⁇ `⊤ ⟩ ⊗ᴸ ⟨ end ‼ ⟩ ∣ 𝕀
    ⊢blsplit = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ
      (T-AppLin refl ℙ≤ϵ (T-Const (`lsplit (λ ()) (end ‼))) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 2F refl)))
    Γbk : Ctx 5
    Γbk = ⟨ msg ⁇ `⊤ ⟩ ⸴ ⟨ end ‼ ⟩ ⸴ Γbody
    ⊢brecv : Γbk ; (` 0F) ⊢ K `recv · (` 0F) ∶ `⊤ ∣ 𝕀
    ⊢brecv = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`recv `⊤))) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))
    ⊢bend : Γbk ; (` 1F) ⊢ K (`end ‼) · (` 1F) ∶ `⊤ ∣ 𝕀
    ⊢bend = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))
    ⊢bbody : Γbk ; (((` 0F) ; (` 1F)) ∥ []) ⊢ (K `recv · (` 0F)) ; (K (`end ‼) · (` 1F)) ∶ `⊤ ∣ 𝕀
    ⊢bbody = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢brecv ⊢bend)

-- ============================================================================
-- The body process, typed at the CLEAN struct  ((` 0F) ; (` 1F)) ∥ (` 2F).
-- Note: front borrows are ;-ordered in ONE thread -- NO Sep wall.
-- ============================================================================
bodyProc : Proc 3
bodyProc = ⟪ frontThread ⟫ ∥ ⟪ backThread ⟫

⊢bodyClean : Γbody ; (((` 0F) ; (` 1F)) ∥ (` 2F)) ⊢ₚ bodyProc
⊢bodyClean = TP-Par ⊢frontThread ⊢backThread

-- ============================================================================
-- THE TP-Res BODY STRUCT for  ν [2] [1] (…)  at outer scope n = 0.
--   structBinder [2] ⋯wkʳ 1 ⋯wkʳ 0 ∥ structBinder [1] ⋯wkˡ 2 ⋯wkʳ 0 ∥ [] ⋯weaken* 3
-- normalizes to  ((` 0F ; (` 1F ; [])) ∥ []) ∥ ((` 2F ; []) ∥ []) ∥ [].
-- ============================================================================
resBodyStruct : Struct 3
resBodyStruct = (structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ (structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 3)

resBodyStructEq : resBodyStruct ≡ ((((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ (((` 2F) ; []) ∥ []) ∥ [])
resBodyStructEq = refl

-- Weaken the clean body up to the TP-Res body struct.  Unlike the rsplit case,
-- the front borrows sit under `;` on BOTH sides, so this ≼ EXISTS (it is just
-- ∥/;-unit padding), no Sep wall.
resBodyLit : Struct 3
resBodyLit = ((((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ (((` 2F) ; []) ∥ []) ∥ [])

body≼ : Γbody ∶ (((` 0F) ; (` 1F)) ∥ (` 2F)) ≼ resBodyLit
body≼ = ≼-refl (≈-sym chain)
  where
    open ≈-Reasoning
    chain : Γbody ∶ resBodyLit ≈ (((` 0F) ; (` 1F)) ∥ (` 2F))
    chain = begin
        ((((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ (((` 2F) ; []) ∥ [])) ∥ []
          ≈⟨ ∥-unit₂ ⟩
        (((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ (((` 2F) ; []) ∥ [])
          ≈⟨ CE.∥-cong ∥-unit₂ ∥-unit₂ ⟩
        ((` 0F) ; ((` 1F) ; [])) ∥ ((` 2F) ; [])
          ≈⟨ CE.∥-cong (CE.;-cong ≈-refl ;-unit₂) ;-unit₂ ⟩
        ((` 0F) ; (` 1F)) ∥ (` 2F)
          ∎

⊢resBody : Γbody ; resBodyStruct ⊢ₚ bodyProc
⊢resBody = subst-γₚ (sym resBodyStructEq) (TP-Weaken body≼ ⊢bodyClean)

-- ============================================================================
-- THE FULL WELL-TYPED PROCESS  ν [2] [1] bodyProc  at outer scope 0.
-- (Γ = λ() : Ctx 0.)  This is a COMPLETE _;_⊢ₚ_ / TP-Res derivation with the
-- CLOSE handle at the INNER (second) front borrow.
-- ============================================================================
theProc : Proc 0
theProc = ν (2 ∷ []) (1 ∷ []) bodyProc

⊢theProc : (λ ()) ; [] ⊢ₚ theProc
⊢theProc = TP-Res Ns ⊢B₁ ⊢B₂ Cfront Cback ⊢resBody

-- ============================================================================
-- DECISIVE COROLLARIES (all refl / machine-checked) -- why this is a genuine
-- R2 obstruction, not an artefact narrowable to the head.
-- ============================================================================

-- (1)  The front block has WIDTH 2, strictly wider than R-Close's forced [1].
--      (R-LSplit/R-RSplit DO produce width-≥2 front blocks in typed reduction,
--       so wide front blocks are reachable, not degenerate.)
frontWidth : sum (2 ∷ []) ≡ 2
frontWidth = refl

-- (2)  The CLOSE handle ⟨end ⁇⟩ is the borrow at Fin index 1F -- the INNER
--      (non-head) slot of the front block; slot 0F carries ⟨msg ‼ ⊤⟩ instead.
handleSlot : Γbody 1F ≡ ⟨ end ⁇ ⟩
handleSlot = refl

headSlot : Γbody 0F ≡ ⟨ msg ‼ `⊤ ⟩
headSlot = refl

handle-not-head : _≢_ {A = 𝔽 3} 1F 0F
handle-not-head ()

-- (3)  Borrow 0F is a LIVE linear resource of the body: it occurs in the body
--      struct (count = 1 in the ;-chain of the front thread).  Hence the body
--      genuinely MENTIONS 0F, so R-Discard (which requires the body to be
--      P ⋯ₚ weakenᵣ, i.e. to NOT mention the discarded index) does NOT apply to
--      this front block -- the width-2 block cannot be narrowed to [1].
0F-live : count {n = 3} 0F (((` 0F) ; (` 1F)) ∥ (` 2F)) ≡ 1
0F-live = refl

-- ============================================================================
-- (4)  THE Sep-WALL, specialized to this witness -- the deeper R2 resolution.
--
-- Although the INNER-handle TYPING is reachable (⊢theProc above), the earlier
-- same-block borrow (slot 0F, ⟨msg ‼ ⊤⟩) can NEVER be owned by a PARALLEL
-- SIBLING of the close thread: that would ∥-separate 0F and 1F, but both sit
-- under `;` in resBodyStruct (the structBinder geometry) -- reusing the proven
-- sep-monotonicity of BorrowedCF.RsplitTypingRefute (sep is UPWARD-monotone
-- under ≼ for non-Unr slots; a pure ;-sequence has NO separation).
--
-- CONSEQUENCE for the reverse simulation:  when the close `end ⁇`·(inner) is
-- the HEAD redex (the operative RU-Close case), the pre-handle borrows have
-- already been consumed BY THE CLOSE THREAD ITSELF (they cannot be live in a
-- sibling), so the body no longer mentions them and R-Discard narrows the
-- block [2] → [1], after which the head R-Close fires.  Hence the reverse
-- RU-Close codomain is the multi-step  (R-Discard* ◅◅ R-Close)  -- NO new
-- inner-close calculus rule is required.
-- ============================================================================

¬u0 : ¬ Unr (Γbody 0F)
¬u0 (⟨ () ⟩)

¬u1 : ¬ Unr (Γbody 1F)
¬u1 (⟨ () ⟩)

-- resBodyStruct does NOT ∥-separate 0F and 1F (they are ;-ordered).  We work on
-- the LITERAL normal form (resBodyLit ≡ resBodyStruct, refl) with every peel
-- pinned, so nothing is left for the elaborator to guess.
LEFT2 : Struct 3
LEFT2 = (` 0F) ; ((` 1F) ; [])

RIGHT2 : Struct 3
RIGHT2 = ((` 2F) ; []) ∥ []

-- 0F,1F ∉ RIGHT2 ⇒ a separation of the (LEFT2∥[])∥RIGHT2 lands in the LEFT arm.
peelR : R.sep 0F 1F ((LEFT2 ∥ []) ∥ RIGHT2) → R.sep 0F 1F (LEFT2 ∥ [])
peelR (inj₁ (_ , y∈R)) = ⊥-elim (y∈R refl)
peelR (inj₂ (inj₁ (x∈R , _))) = ⊥-elim (x∈R refl)
peelR (inj₂ (inj₂ (inj₁ sL))) = sL
peelR (inj₂ (inj₂ (inj₂ (inj₁ (x∈2 , _))))) = ⊥-elim (x∈2 refl)
peelR (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , y∈2)))))) = ⊥-elim (y∈2 refl)
peelR (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (inj₁ ())))))))
peelR (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (inj₂ ())))))))
peelR (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ ()))))))

¬sep-lit : ¬ R.sep 0F 1F resBodyLit
¬sep-lit sp = R.sep-seq2-no {n = 3} {x = 0F} {y = 1F} 0F 1F
  (R.sep-∥[]ʳ {x = 0F} {y = 1F} LEFT2
    (peelR
      (R.sep-∥[]ʳ {x = 0F} {y = 1F} ((LEFT2 ∥ []) ∥ RIGHT2) sp)))

¬sep-res : ¬ R.sep 0F 1F resBodyStruct
¬sep-res sp = ¬sep-lit (subst (R.sep 0F 1F) resBodyStructEq sp)

-- PROCESS-LEVEL: no TP-Par split of resBodyStruct routes the handle 0F and the
-- earlier borrow 1F to two parallel sibling components.  (Same obstruction the
-- rsplit off-handle hit -- the borrows of ONE chain are ;-ordered.)
no-sibling-earlier :
    (γH γS : Struct 3)
  → Γbody ∶ γH ∥ γS ≼ resBodyStruct
  → 0F R.∈ₘ γH → 1F R.∈ₘ γS → ⊥
no-sibling-earlier γH γS le 0∈H 1∈S =
  ¬sep-res (R.sep-mono-≼ ¬u0 ¬u1 le (inj₁ (0∈H , 1∈S)))
