module BorrowedCF.Simulation2.RsplitFramedRedex where

open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as RR
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_) renaming (ε to refl⋆)
open import BorrowedCF.Simulation2.Confine using (count; ≼⇒count≤)

open Fin.Patterns
open Nat.Variables

sParam : 𝕊 0
sParam = msg ‼ `⊤

nskips-s : ¬ Skips sParam
nskips-s ()

ΓL : Ctx 1
ΓL = (λ _ → ⟨ msg ‼ `⊤ ; ret ⟩)

consumeL : Tm 1
consumeL =
  `let⊗ (K (`lsplit sParam) · (` 0F))
   `in ((K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F)))

⊢lsplitL : ΓL ; ([] ∥ (` 0F)) ⊢ K (`lsplit sParam) · (` 0F) ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ ret ⟩ ∣ 𝕀
⊢lsplitL = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ (T-AppLin refl ℙ≤ϵ (T-Const (`lsplit nskips-s ret)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))

Γ2 : Ctx 3
Γ2 = ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ ret ⟩ ⸴ ΓL

⊢sendL : Γ2 ; (` 0F) ⊢ K `send · (* ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
⊢sendL = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁)) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
           (T-Pair par par (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))

⊢dropL : Γ2 ; (` 1F) ⊢ K `drop · (` 1F) ∶ `⊤ ∣ 𝕀
⊢dropL = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Const `drop)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))

⊢bodyL : Γ2 ; (((` 0F) ; (` 1F)) ∥ []) ⊢ (K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F)) ∶ `⊤ ∣ 𝕀
⊢bodyL = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢sendL ⊢dropL)

⊢consumeL : ΓL ; (([] ∥ (` 0F)) ∥ []) ⊢ consumeL ∶ `⊤ ∣ 𝕀
⊢consumeL = T-LetPair par ⊢lsplitL ⊢bodyL

-- ============================================================================
-- Step 2: consume RIGHT half ⟨ acq ; skip ⟩ down to ⊤ at 𝕀, in a 1-chan ctx.
-- acq : ⟨ acq ; skip ⟩ →1M ⟨ skip ⟩;  ⟨ skip ⟩ is Unr (Skips skip), discard via T-Seq.
-- ============================================================================

ΓR : Ctx 1
ΓR = (λ _ → ⟨ acq ; skip ⟩)

consumeR : Tm 1
consumeR = (K `acq · (` 0F)) ; *

⊢acqR : ΓR ; (` 0F) ⊢ K `acq · (` 0F) ∶ ⟨ skip ⟩ ∣ 𝕀
⊢acqR = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Const `acq)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))

⊢consumeR : ΓR ; ((` 0F) ; []) ⊢ consumeR ∶ `⊤ ∣ 𝕀
⊢consumeR = T-Seq ⟨ skip ⟩ ⊢acqR (T-Conv `⊤ ℙ≤ϵ (T-Const `unit))

-- ============================================================================
-- Step 3: the rsplit thread body  E[ rsplit sParam · ` 0F ]  in a 2-chan ctx.
-- ν binds a 2-borrow front chain; slot 0F is the handle ⟨ msg ‼ ⊤ ⟩, slot 1F
-- the off-handle borrow ⟨ msg ⁇ ⊤ ⟩ (owned by the sibling, not here).
-- The outer let⊗ destructs the rsplit pair ⟨msg‼⊤;ret⟩ ⊗¹ ⟨acq;skip⟩ and the
-- body consumes BOTH halves to ⊤ (left via lsplit+send+drop, right via acq+discard).
-- ============================================================================

-- The 2-channel context for the front chain (matches RsplitOwnershipProbe.g2).
g2 : Ctx 3
g2 = ⟨ msg ‼ `⊤ ⟩ F.∷ ⟨ end ⁇ ⟩ F.∷ ⟨ (msg ⁇ `⊤) ; end ‼ ⟩ F.∷ (λ ())

-- The frame E (non-empty): the outer let⊗ around the rsplit redex.
E : Frame 3
E = `let⊗-`in (((`let⊗ (K (`lsplit sParam) · (` 0F))
                 `in ((K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F))))
              ; ((K `acq · (` 1F)) ; *)))

-- The full rsplit-thread body term:  E [ rsplit sParam · ` 0F ].
rsplitBody : Tm 3
rsplitBody = E [ K (`rsplit sParam) · (` 0F) ]

-- rsplit applied to the handle slot 0F : the PAIR (positive control, lifted to 𝕀).
⊢rsplitPair : g2 ; ([] ∥ (` 0F)) ⊢ K (`rsplit sParam) · (` 0F)
            ∶ ⟨ sParam ; ret ⟩ ⊗¹ ⟨ acq ; skip ⟩ ∣ 𝕀
⊢rsplitPair = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ
  (T-AppLin refl ℙ≤ϵ (T-Const (`rsplit nskips-s skip))
    (T-Conv ⟨ ≃-sym ≃-skipʳ ⟩ ℙ≤ϵ (T-Var 0F refl)))

-- The let⊗-body context:  db0 = ⟨msg‼⊤;ret⟩, db1 = ⟨acq;skip⟩, db2 = handle, db3 = off.
Γb : Ctx 5
Γb = ⟨ sParam ; ret ⟩ ⸴ ⟨ acq ; skip ⟩ ⸴ g2

-- LEFT consumer on db0.
⊢L0 : Γb ; (` 0F) ⊢ (`let⊗ (K (`lsplit sParam) · (` 0F))
                        `in ((K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F)))) ∶ `⊤ ∣ 𝕀
⊢L0 = T-Weaken (≼-refl (≈-trans ∥-unit₂ ∥-unit₁)) (T-LetPair par ⊢lsplit0 ⊢body0)
  where
    ⊢lsplit0 : Γb ; ([] ∥ (` 0F)) ⊢ K (`lsplit sParam) · (` 0F) ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ ret ⟩ ∣ 𝕀
    ⊢lsplit0 = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ (T-AppLin refl ℙ≤ϵ (T-Const (`lsplit nskips-s ret)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))
    Γb2 : Ctx 7
    Γb2 = ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ ret ⟩ ⸴ Γb
    ⊢send0 : Γb2 ; (` 0F) ⊢ K `send · (* ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
    ⊢send0 = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁)) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
               (T-Pair par par (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))
    ⊢drop0 : Γb2 ; (` 1F) ⊢ K `drop · (` 1F) ∶ `⊤ ∣ 𝕀
    ⊢drop0 = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Const `drop)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))
    ⊢body0 : Γb2 ; (((` 0F) ; (` 1F)) ∥ []) ⊢ (K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F)) ∶ `⊤ ∣ 𝕀
    ⊢body0 = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢send0 ⊢drop0)

-- RIGHT consumer on db1.
⊢R1 : Γb ; (` 1F) ⊢ ((K `acq · (` 1F)) ; *) ∶ `⊤ ∣ 𝕀
⊢R1 = T-Weaken (≼-refl ;-unit₂) (T-Seq ⟨ skip ⟩ ⊢acq1 (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)))
  where
    ⊢acq1 : Γb ; (` 1F) ⊢ K `acq · (` 1F) ∶ ⟨ skip ⟩ ∣ 𝕀
    ⊢acq1 = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Const `acq)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))

-- e₂ for the outer let⊗: consume both halves (db0 ∥ db1), reaching ⊤ ∣ 𝕀.
⊢outerBody : Γb ; (((` 0F) ∥ (` 1F)) ∥ []) ⊢
  (`let⊗ (K (`lsplit sParam) · (` 0F))
     `in ((K `send · (* ⊗ (` 0F))) ; (K `drop · (` 1F))))
  ; ((K `acq · (` 1F)) ; *) ∶ `⊤ ∣ 𝕀
⊢outerBody = T-Weaken (≼-trans ;-≼-∥ (≼-refl (≈-sym ∥-unit₂))) (T-Seq `⊤ ⊢L0 ⊢R1)

-- THE rsplit thread body typing:  g2 ; (` 0F) ⊢ E[ rsplit · ` 0F ] ∶ ⊤ ∣ 𝕀.
-- The thread uses ONLY the handle slot 0F.
⊢rsplitBody : g2 ; (([] ∥ (` 0F)) ∥ []) ⊢ rsplitBody ∶ `⊤ ∣ 𝕀
⊢rsplitBody = T-LetPair par ⊢rsplitPair ⊢outerBody

-- ============================================================================
-- HONEST FINDING about the literal src = ν (2 ∷ []) [] (...):
--   (W1)  B₂ = [] is STRUCTURALLY IMPOSSIBLE: TP-Res needs
--         C′ : BindCtx (dual s ; end ‼) B₂ Γ₂, and BindCtx has NO constructor
--         for an empty bind group (every BindCtx needs a nonempty B).
--         See `BorrowedCF.EmptyBProbe`.
--   (W2)  With s = msg ‼ ⊤ and the front chain B₁ = 2 ∷ [], the second borrow
--         (slot inj 1F) of  s ; end ⁇ = msg ‼ ⊤ ; end ⁇  is FORCED to ⟨ end ⁇ ⟩,
--         NOT ⟨ msg ⁇ ⊤ ⟩.  A `recv` sibling needs ⟨ msg ⁇ ⊤ ⟩ ≄ ⟨ end ⁇ ⟩.
-- So the literal src is vacuous as written.  Below we build the HONEST nearest
-- realisable rsplit redex and give it a FULL TP-Res derivation, to settle the
-- research question (can a sibling own an off-handle borrow of the split chain?).
--
-- Honest choice:  s = msg ‼ ⊤,  B₁ = 2 ∷ [],  B₂ = 1 ∷ [].
--   front chain  s ; end ⁇ = msg ‼ ⊤ ; end ⁇  over 2 borrows:
--       slot inj 0F = ⟨ msg ‼ ⊤ ⟩  (handle, rsplit splits this)
--       slot inj 1F = ⟨ end ⁇ ⟩     (off-handle borrow, owned by a sibling)
--   back chain   dual s ; end ‼ = msg ⁇ ⊤ ; end ‼  over 1 borrow.
-- ============================================================================

Ns : New sParam
Ns = New.msg

↑ˡ0-2 : (x : 𝔽 2) → x ↑ˡ 0 ≡ x
↑ˡ0-2 0F = refl
↑ˡ0-2 1F = refl

↑ˡ0-1 : (x : 𝔽 1) → x ↑ˡ 0 ≡ x
↑ˡ0-1 0F = refl



-- Front bind context:  BindCtx (msg ‼ ⊤ ; end ⁇) (2 ∷ []) Γ₁.
-- 2-borrow chain:  slot0 = ⟨ msg ‼ ⊤ ⟩, slot1 = ⟨ end ⁇ ⟩.
Γfront : Ctx 2
Γfront = ⟨ msg ‼ `⊤ ⟩ F.∷ ⟨ end ⁇ ⟩ F.∷ (λ ())

bc-front′ : BindCtx′ (sParam ; end ⁇) 2 (Γfront ∘ wkʳ 0)
bc-front′ =
  cons (λ { (() ; _) }) ≃-refl (λ x → sym (cong Γfront (↑ˡ0-2 x)))
    (cons (λ ()) ≃-skipʳ (λ _ → refl)
      (nil skip))

Cfront : BindCtx (sParam ; end ⁇) (2 ∷ []) Γfront
Cfront = last bc-front′

-- Back bind context:  BindCtx (dual sParam ; end ‼) (1 ∷ []) Γ₂.
-- dual (msg ‼ ⊤) = msg ⁇ ⊤,  so  msg ⁇ ⊤ ; end ‼.   1 borrow: ⟨ msg ⁇ ⊤ ; end ‼ ⟩.
Γback : Ctx 1
Γback = (λ _ → ⟨ (msg ⁇ `⊤) ; end ‼ ⟩)

bc-back′ : BindCtx′ ((dual sParam) ; end ‼) 1 (Γback ∘ wkʳ 0)
bc-back′ = cons (λ { (() ; _) }) ≃-skipʳ (λ { 0F → refl }) (nil skip)

Cback : BindCtx ((dual sParam) ; end ‼) (1 ∷ []) Γback
Cback = last bc-back′

-- ============================================================================
-- The full source process and its TP-Res derivation.
--   src = ν (2 ∷ []) (1 ∷ []) ( (⟪ rsplitBody ⟫ ∥ ⟪ off-thread ⟫) ∥ ⟪ back-thread ⟫ )
-- rsplit thread owns handle slot 0F; off-thread owns off-handle slot 1F (⟨end⁇⟩);
-- back-thread owns the single back-chain borrow.
-- ============================================================================

-- body context: db0,db1 = front borrows, db2 = back borrow.
Γbody : Ctx 3
Γbody = g2

probeBodyStruct : Struct 3
probeBodyStruct = (structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0) ∥ (structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0) ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 3)

bodyStructEq : probeBodyStruct ≡ ((((` 0F) ; ((` 1F) ; [])) ∥ []) ∥ (((` 2F) ; []) ∥ []) ∥ [])
bodyStructEq = refl

-- off-handle sibling: owns front slot 1F = ⟨ end ⁇ ⟩, consumes via `end ⁇` to ⊤.
offThread : Tm 3
offThread = K (`end ⁇) · (` 1F)

⊢offThread : Γbody ; (` 1F) ⊢ₚ ⟪ offThread ⟫
⊢offThread = TP-Expr (T-Weaken (≼-refl ∥-unit₁)
  (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl))))

-- back-chain thread: owns db2 = ⟨ msg ⁇ ⊤ ; end ‼ ⟩.
-- consume:  recv the msg⁇⊤ then `end ‼` the cap.  lsplit ⟨msg⁇⊤;end‼⟩ -> ⟨msg⁇⊤⟩ ⊗ᴸ ⟨end‼⟩.
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
-- ASSEMBLY ATTEMPT: type the body  (⟪rsplitBody⟫ ∥ ⟪offThread⟫) ∥ ⟪backThread⟫
-- at the TP-Res body struct  bodyStruct ≈ (` 0F ; ` 1F) ∥ ` 2F.
-- ============================================================================

-- The body process.
bodyProc : Proc 3
bodyProc = (⟪ rsplitBody ⟫ ∥ ⟪ offThread ⟫) ∥ ⟪ backThread ⟫

-- rsplit thread at a CLEAN handle struct (` 0F).
⊢rsplitClean : Γbody ; (` 0F) ⊢ₚ ⟪ rsplitBody ⟫
⊢rsplitClean = TP-Weaken (≼-refl (≈-trans ∥-unit₂ ∥-unit₁)) (TP-Expr ⊢rsplitBody)

-- The front pair (rsplit ∥ off): handle 0F in parallel with off-handle 1F.
⊢frontPair : Γbody ; ((` 0F) ∥ (` 1F)) ⊢ₚ ⟪ rsplitBody ⟫ ∥ ⟪ offThread ⟫
⊢frontPair = TP-Par ⊢rsplitClean ⊢offThread

-- back thread at clean (` 2F).
⊢backClean : Γbody ; (` 2F) ⊢ₚ ⟪ backThread ⟫
⊢backClean = ⊢backThread

-- The whole body at the CLEAN struct ((` 0F) ∥ (` 1F)) ∥ (` 2F).
⊢bodyClean : Γbody ; (((` 0F) ∥ (` 1F)) ∥ (` 2F)) ⊢ₚ bodyProc
⊢bodyClean = TP-Par ⊢frontPair ⊢backClean

-- THE WALL: to feed TP-Res we must weaken ⊢bodyClean UP to bodyStruct, i.e.
--   Γbody ∶ ((` 0F) ∥ (` 1F)) ∥ (` 2F)  ≼  bodyStruct
-- but bodyStruct ≈ (` 0F ; ` 1F) ∥ ` 2F, and the front needs  ` 0F ∥ ` 1F ≼ ` 0F ; ` 1F,
-- i.e. ∥ ≼ ; on two NON-Unr borrows.  No such ≼ exists (only ;-≼-∥ holds).
-- (the real `wall` refutation is proven below, after the Sep machinery)

-- ============================================================================
-- THE WALL, PROVEN (machine-checked refutation, no hole, no postulate).
-- We show NO  Γbody ∶ (` 0F ∥ ` 1F) ∥ ` 2F ≼ (` 0F ; ` 1F) ∥ ` 2F  exists, hence
-- the body CANNOT be re-typed at the TP-Res body struct, hence src is UNTYPEABLE
-- with the rsplit-thread + off-handle-sibling split.  The obstruction is purely
-- ORDERING:  the two borrows of ONE chain sit under `;` in structBinder, and
-- TP-Par (which yields `∥`) cannot route them to two parallel sibling threads.
--
-- Invariant `Sep`:  0F and 1F occur on opposite sides of some `∥`.
-- `≼` (from α to β) preserves it; `(` 0F ; ` 1F) ∥ ` 2F` does not have it.
-- ============================================================================

-- occurrence of a fin in a struct (≥ 1 leaf).
occ : 𝔽 3 → Struct 3 → Set
occ x (` y) = x ≡ y
occ x [] = ⊥
occ x (α ∥ β) = occ x α ⊎ occ x β
occ x (α ; β) = occ x α ⊎ occ x β

-- 0F and 1F separated across a `∥`.
data Sep : Struct 3 → Set where
  parLR : ∀ {α β} → occ 0F α → occ 1F β → Sep (α ∥ β)
  parRL : ∀ {α β} → occ 1F α → occ 0F β → Sep (α ∥ β)
  sepPl : ∀ {α β} → Sep α → Sep (α ∥ β)
  sepPr : ∀ {α β} → Sep β → Sep (α ∥ β)
  sepSl : ∀ {α β} → Sep α → Sep (α ; β)
  sepSr : ∀ {α β} → Sep β → Sep (α ; β)

¬unr0 : ¬ Unr (Γbody 0F)
¬unr0 (⟨ () ⟩)

¬unr1 : ¬ Unr (Γbody 1F)
¬unr1 (⟨ () ⟩)

-- a context that is Unr cannot contain an occurrence of a non-Unr variable.
occ⇒¬unrCx : ∀ {x} {γ} → (¬ Unr (Γbody x)) → occ x γ → ¬ UnrCx Γbody γ
occ⇒¬unrCx {x} {` y} ¬u oc (` u) rewrite oc = ¬u u
occ⇒¬unrCx {x} {α ∥ β} ¬u (inj₁ oc) (Uα ∥ Uβ) = occ⇒¬unrCx ¬u oc Uα
occ⇒¬unrCx {x} {α ∥ β} ¬u (inj₂ oc) (Uα ∥ Uβ) = occ⇒¬unrCx ¬u oc Uβ
occ⇒¬unrCx {x} {α ; β} ¬u (inj₁ oc) (Uα ; Uβ) = occ⇒¬unrCx ¬u oc Uα
occ⇒¬unrCx {x} {α ; β} ¬u (inj₂ oc) (Uα ; Uβ) = occ⇒¬unrCx ¬u oc Uβ

-- occ is invariant under ≈′ (leaves are preserved; dup/unit/tm keep the leaf set).
occ-≈′→ : ∀ {x α β} → Γbody ∶ α ≈′ β → occ x α → occ x β
occ-≈′→ ;′-assoc (inj₁ (inj₁ o)) = inj₁ o
occ-≈′→ ;′-assoc (inj₁ (inj₂ o)) = inj₂ (inj₁ o)
occ-≈′→ ;′-assoc (inj₂ o) = inj₂ (inj₂ o)
occ-≈′→ (;′-cong₁ e) (inj₁ o) = inj₁ (occ-≈′→ e o)
occ-≈′→ (;′-cong₁ e) (inj₂ o) = inj₂ o
occ-≈′→ (;′-cong₂ e) (inj₁ o) = inj₁ o
occ-≈′→ (;′-cong₂ e) (inj₂ o) = inj₂ (occ-≈′→ e o)
occ-≈′→ ∥′-unit (inj₁ o) = o
occ-≈′→ ∥′-unit (inj₂ ())
occ-≈′→ ∥′-assoc (inj₁ (inj₁ o)) = inj₁ o
occ-≈′→ ∥′-assoc (inj₁ (inj₂ o)) = inj₂ (inj₁ o)
occ-≈′→ ∥′-assoc (inj₂ o) = inj₂ (inj₂ o)
occ-≈′→ ∥′-comm (inj₁ o) = inj₂ o
occ-≈′→ ∥′-comm (inj₂ o) = inj₁ o
occ-≈′→ (∥′-cong₁ e) (inj₁ o) = inj₁ (occ-≈′→ e o)
occ-≈′→ (∥′-cong₁ e) (inj₂ o) = inj₂ o
occ-≈′→ (∥′-dup U) o = inj₁ o
occ-≈′→ (∥′-tm-; U) o = o

occ-≈′← : ∀ {x α β} → Γbody ∶ α ≈′ β → occ x β → occ x α
occ-≈′← ;′-assoc (inj₁ o) = inj₁ (inj₁ o)
occ-≈′← ;′-assoc (inj₂ (inj₁ o)) = inj₁ (inj₂ o)
occ-≈′← ;′-assoc (inj₂ (inj₂ o)) = inj₂ o
occ-≈′← (;′-cong₁ e) (inj₁ o) = inj₁ (occ-≈′← e o)
occ-≈′← (;′-cong₁ e) (inj₂ o) = inj₂ o
occ-≈′← (;′-cong₂ e) (inj₁ o) = inj₁ o
occ-≈′← (;′-cong₂ e) (inj₂ o) = inj₂ (occ-≈′← e o)
occ-≈′← ∥′-unit o = inj₁ o
occ-≈′← ∥′-assoc (inj₁ o) = inj₁ (inj₁ o)
occ-≈′← ∥′-assoc (inj₂ (inj₁ o)) = inj₁ (inj₂ o)
occ-≈′← ∥′-assoc (inj₂ (inj₂ o)) = inj₂ o
occ-≈′← ∥′-comm (inj₁ o) = inj₂ o
occ-≈′← ∥′-comm (inj₂ o) = inj₁ o
occ-≈′← (∥′-cong₁ e) (inj₁ o) = inj₁ (occ-≈′← e o)
occ-≈′← (∥′-cong₁ e) (inj₂ o) = inj₂ o
occ-≈′← (∥′-dup U) (inj₁ o) = o
occ-≈′← (∥′-dup U) (inj₂ o) = o
occ-≈′← (∥′-tm-; U) o = o

-- Sep is preserved by ≈′ in both directions.  The only rule that could destroy a
-- separating ∥ is ∥′-tm-; (∥ → ;), but that needs an Unr side, impossible when 0F
-- (resp. 1F) occurs there.  Symmetrically for the reverse.
Sep-≈′→ : ∀ {α β} → Γbody ∶ α ≈′ β → Sep α → Sep β
Sep-≈′→ ;′-assoc (sepSl (sepSl s)) = sepSl s
Sep-≈′→ ;′-assoc (sepSl (sepSr s)) = sepSr (sepSl s)
Sep-≈′→ ;′-assoc (sepSr s) = sepSr (sepSr s)
Sep-≈′→ (;′-cong₁ e) (sepSl s) = sepSl (Sep-≈′→ e s)
Sep-≈′→ (;′-cong₁ e) (sepSr s) = sepSr s
Sep-≈′→ (;′-cong₂ e) (sepSl s) = sepSl s
Sep-≈′→ (;′-cong₂ e) (sepSr s) = sepSr (Sep-≈′→ e s)
Sep-≈′→ ∥′-unit (parLR o ())
Sep-≈′→ ∥′-unit (parRL o ())
Sep-≈′→ ∥′-unit (sepPl s) = s
Sep-≈′→ ∥′-unit (sepPr ())
Sep-≈′→ ∥′-assoc (parLR (inj₁ o1) o2) = parLR o1 (inj₂ o2)
Sep-≈′→ ∥′-assoc (parLR (inj₂ o1) o2) = sepPr (parLR o1 o2)
Sep-≈′→ ∥′-assoc (parRL (inj₁ o1) o2) = parRL o1 (inj₂ o2)
Sep-≈′→ ∥′-assoc (parRL (inj₂ o1) o2) = sepPr (parRL o1 o2)
Sep-≈′→ ∥′-assoc (sepPl (parLR o1 o2)) = parLR o1 (inj₁ o2)
Sep-≈′→ ∥′-assoc (sepPl (parRL o1 o2)) = parRL o1 (inj₁ o2)
Sep-≈′→ ∥′-assoc (sepPl (sepPl s)) = sepPl s
Sep-≈′→ ∥′-assoc (sepPl (sepPr s)) = sepPr (sepPl s)
Sep-≈′→ ∥′-assoc (sepPr s) = sepPr (sepPr s)
Sep-≈′→ ∥′-comm (parLR o1 o2) = parRL o2 o1
Sep-≈′→ ∥′-comm (parRL o1 o2) = parLR o2 o1
Sep-≈′→ ∥′-comm (sepPl s) = sepPr s
Sep-≈′→ ∥′-comm (sepPr s) = sepPl s
Sep-≈′→ (∥′-cong₁ e) (parLR o1 o2) = parLR (occ-≈′→ e o1) o2
Sep-≈′→ (∥′-cong₁ e) (parRL o1 o2) = parRL (occ-≈′→ e o1) o2
Sep-≈′→ (∥′-cong₁ e) (sepPl s) = sepPl (Sep-≈′→ e s)
Sep-≈′→ (∥′-cong₁ e) (sepPr s) = sepPr s
Sep-≈′→ (∥′-dup U) s = sepPl s
Sep-≈′→ (∥′-tm-; (inj₁ Uα)) (parLR o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr0 o1 Uα)
Sep-≈′→ (∥′-tm-; (inj₂ Uβ)) (parLR o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr1 o2 Uβ)
Sep-≈′→ (∥′-tm-; (inj₁ Uα)) (parRL o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr1 o1 Uα)
Sep-≈′→ (∥′-tm-; (inj₂ Uβ)) (parRL o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr0 o2 Uβ)
Sep-≈′→ (∥′-tm-; U) (sepPl s) = sepSl s
Sep-≈′→ (∥′-tm-; U) (sepPr s) = sepSr s

Sep-≈′← : ∀ {α β} → Γbody ∶ α ≈′ β → Sep β → Sep α
Sep-≈′← ;′-assoc (sepSl s) = sepSl (sepSl s)
Sep-≈′← ;′-assoc (sepSr (sepSl s)) = sepSl (sepSr s)
Sep-≈′← ;′-assoc (sepSr (sepSr s)) = sepSr s
Sep-≈′← (;′-cong₁ e) (sepSl s) = sepSl (Sep-≈′← e s)
Sep-≈′← (;′-cong₁ e) (sepSr s) = sepSr s
Sep-≈′← (;′-cong₂ e) (sepSl s) = sepSl s
Sep-≈′← (;′-cong₂ e) (sepSr s) = sepSr (Sep-≈′← e s)
Sep-≈′← ∥′-unit s = sepPl s
Sep-≈′← ∥′-assoc (parLR o1 (inj₁ o2)) = sepPl (parLR o1 o2)
Sep-≈′← ∥′-assoc (parLR o1 (inj₂ o2)) = parLR (inj₁ o1) o2
Sep-≈′← ∥′-assoc (parRL o1 (inj₁ o2)) = sepPl (parRL o1 o2)
Sep-≈′← ∥′-assoc (parRL o1 (inj₂ o2)) = parRL (inj₁ o1) o2
Sep-≈′← ∥′-assoc (sepPl s) = sepPl (sepPl s)
Sep-≈′← ∥′-assoc (sepPr (parLR o1 o2)) = parLR (inj₂ o1) o2
Sep-≈′← ∥′-assoc (sepPr (parRL o1 o2)) = parRL (inj₂ o1) o2
Sep-≈′← ∥′-assoc (sepPr (sepPl s)) = sepPl (sepPr s)
Sep-≈′← ∥′-assoc (sepPr (sepPr s)) = sepPr s
Sep-≈′← ∥′-comm (parLR o1 o2) = parRL o2 o1
Sep-≈′← ∥′-comm (parRL o1 o2) = parLR o2 o1
Sep-≈′← ∥′-comm (sepPl s) = sepPr s
Sep-≈′← ∥′-comm (sepPr s) = sepPl s
Sep-≈′← (∥′-cong₁ e) (parLR o1 o2) = parLR (occ-≈′← e o1) o2
Sep-≈′← (∥′-cong₁ e) (parRL o1 o2) = parRL (occ-≈′← e o1) o2
Sep-≈′← (∥′-cong₁ e) (sepPl s) = sepPl (Sep-≈′← e s)
Sep-≈′← (∥′-cong₁ e) (sepPr s) = sepPr s
Sep-≈′← (∥′-dup U) (parLR o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr0 o1 U)
Sep-≈′← (∥′-dup U) (parRL o1 o2) = ⊥-elim (occ⇒¬unrCx ¬unr1 o1 U)
Sep-≈′← (∥′-dup U) (sepPl s) = s
Sep-≈′← (∥′-dup U) (sepPr s) = s
Sep-≈′← (∥′-tm-; U) (sepSl s) = sepPl s
Sep-≈′← (∥′-tm-; U) (sepSr s) = sepPr s

-- Lift to the equivalence closure.
Sep-≈ : ∀ {α β} → Γbody ∶ α ≈ β → Sep α → Sep β
Sep-≈ refl⋆ sp = sp
Sep-≈ (fwd e ◅ rest) sp = Sep-≈ rest (Sep-≈′→ e sp)
Sep-≈ (bwd e ◅ rest) sp = Sep-≈ rest (Sep-≈′← e sp)

-- occ → count > 0 and back, so we can route occ-monotonicity through ≼⇒count≤.
occ⇒count : ∀ {x γ} → occ x γ → 0 Nat.< count x γ
occ⇒count {x} {` y} o with x Fin.≟ y
... | yes _ = Nat.s≤s Nat.z≤n
... | no ¬p = ⊥-elim (¬p o)
occ⇒count {x} {α ∥ β} (inj₁ o) = Nat.<-≤-trans (occ⇒count o) (Nat.m≤m+n _ _)
occ⇒count {x} {α ∥ β} (inj₂ o) = Nat.<-≤-trans (occ⇒count o) (Nat.m≤n+m _ _)
occ⇒count {x} {α ; β} (inj₁ o) = Nat.<-≤-trans (occ⇒count o) (Nat.m≤m+n _ _)
occ⇒count {x} {α ; β} (inj₂ o) = Nat.<-≤-trans (occ⇒count o) (Nat.m≤n+m _ _)

pos-+ : ∀ a b → 0 Nat.< a Nat.+ b → 0 Nat.< a ⊎ 0 Nat.< b
pos-+ zero b lt = inj₂ lt
pos-+ (suc a) b lt = inj₁ (Nat.s≤s Nat.z≤n)

count⇒occ : ∀ {x γ} → 0 Nat.< count x γ → occ x γ
count⇒occ {x} {` y} c with x Fin.≟ y
... | yes p = p
... | no ¬p = ⊥-elim (Nat.n≮n 0 c)
count⇒occ {x} {[]} c = ⊥-elim (Nat.n≮n 0 c)
count⇒occ {x} {α ∥ β} c = Sum.map count⇒occ count⇒occ (pos-+ (count x α) (count x β) c)
count⇒occ {x} {α ; β} c = Sum.map count⇒occ count⇒occ (pos-+ (count x α) (count x β) c)

-- occ of a NON-Unr var is preserved upward by ≼ (≼ never decreases its count).
occ-≼0 : ∀ {α β} → Γbody ∶ α ≼ β → occ 0F α → occ 0F β
occ-≼0 le o = count⇒occ (Nat.<-≤-trans (occ⇒count o) (≼⇒cnt le))
  where ≼⇒cnt : ∀ {α β} → Γbody ∶ α ≼ β → count 0F α Nat.≤ count 0F β
        ≼⇒cnt = ≼⇒count≤ ¬unr0
occ-≼1 : ∀ {α β} → Γbody ∶ α ≼ β → occ 1F α → occ 1F β
occ-≼1 le o = count⇒occ (Nat.<-≤-trans (occ⇒count o) (≼⇒cnt le))
  where ≼⇒cnt : ∀ {α β} → Γbody ∶ α ≼ β → count 1F α Nat.≤ count 1F β
        ≼⇒cnt = ≼⇒count≤ ¬unr1

-- Sep is preserved by ≼ (from α to β).
Sep-≼ : ∀ {α β} → Γbody ∶ α ≼ β → Sep α → Sep β
Sep-≼ (≼-refl eq) sp = Sep-≈ eq sp
Sep-≼ (≼-∅ U) ()
Sep-≼ ≼-wk sp = sep-wk sp
  where
    sep-wk : ∀ {α₁ α₂ β₁ β₂} → Sep ((α₁ ∥ α₂) ; (β₁ ∥ β₂)) → Sep ((α₁ ; β₁) ∥ (α₂ ; β₂))
    sep-wk (sepSl (parLR o1 o2)) = parLR (inj₁ o1) (inj₁ o2)
    sep-wk (sepSl (parRL o1 o2)) = parRL (inj₁ o1) (inj₁ o2)
    sep-wk (sepSl (sepPl s)) = sepPl (sepSl s)
    sep-wk (sepSl (sepPr s)) = sepPr (sepSl s)
    sep-wk (sepSr (parLR o1 o2)) = parLR (inj₂ o1) (inj₂ o2)
    sep-wk (sepSr (parRL o1 o2)) = parRL (inj₂ o1) (inj₂ o2)
    sep-wk (sepSr (sepPl s)) = sepPl (sepSr s)
    sep-wk (sepSr (sepPr s)) = sepPr (sepSr s)
Sep-≼ (≼-trans p q) sp = Sep-≼ q (Sep-≼ p sp)
Sep-≼ (≼-cong-; p q) (sepSl s) = sepSl (Sep-≼ p s)
Sep-≼ (≼-cong-; p q) (sepSr s) = sepSr (Sep-≼ q s)
Sep-≼ (≼-cong-∥ p q) (parLR o1 o2) = parLR (occ-≼0 p o1) (occ-≼1 q o2)
Sep-≼ (≼-cong-∥ p q) (parRL o1 o2) = parRL (occ-≼1 p o1) (occ-≼0 q o2)
Sep-≼ (≼-cong-∥ p q) (sepPl s) = sepPl (Sep-≼ p s)
Sep-≼ (≼-cong-∥ p q) (sepPr s) = sepPr (Sep-≼ q s)

-- The TP-Res body struct has NO separation of 0F and 1F: they sit under `;`.
¬Sep-target : ¬ Sep ((((` 0F) ; (` 1F)) ∥ (` 2F)))
¬Sep-target (parLR o1 ())
¬Sep-target (parRL o1 ())
¬Sep-target (sepPl (sepSl ()))
¬Sep-target (sepPl (sepSr ()))
¬Sep-target (sepPr ())

-- The clean body struct DOES separate 0F and 1F.
Sep-source : Sep (((` 0F) ∥ (` 1F)) ∥ (` 2F))
Sep-source = sepPl (parLR refl refl)

-- THE WALL, machine-checked: no ≼ from the parallel split up to the `;`-target.
wall : ¬ (Γbody ∶ (((` 0F) ∥ (` 1F)) ∥ (` 2F)) ≼ (((` 0F) ; (` 1F)) ∥ (` 2F)))
wall le = ¬Sep-target (Sep-≼ le Sep-source)

-- General form: ANY body struct that separates 0F and 1F across a `∥` (which is
-- forced whenever the handle 0F and the off-handle 1F are owned by two parallel
-- sibling threads) is NOT ≼ the TP-Res body struct.  This is the complete
-- obstruction: no TP-Par split routing 0F and 1F to parallel peers can be
-- weakened into bodyStruct.
wall-general : ∀ {γ} → Sep γ → ¬ (Γbody ∶ γ ≼ (((` 0F) ; (` 1F)) ∥ (` 2F)))
wall-general sp le = ¬Sep-target (Sep-≼ le sp)


-- ============================================================================
-- SUMMARY of what this module establishes (all machine-checked, hole/postulate-free):
--
-- (1) ⊢rsplitBody : a NON-EMPTY evaluation frame E DOES exist that consumes the
--     rsplit result pair  ⟨ msg‼⊤;ret ⟩ ⊗¹ ⟨ acq;skip ⟩  down to ⊤ ∣ 𝕀.  So an
--     rsplit thread CAN be well-typed (unlike the empty-frame case refuted in
--     BorrowedCF.Simulation2.RedexTypingProbe).  The thread reads ONLY the handle slot 0F.
--
-- (2) ⊢offThread, ⊢backThread : the off-handle borrow (front slot 1F) and the
--     back-chain borrow are each independently consumable to ⊤ by sibling threads.
--
-- (3) ⊢bodyClean : the full body  (⟪rsplitBody⟫ ∥ ⟪offThread⟫) ∥ ⟪backThread⟫
--     IS well-typed at the CLEAN struct  ((` 0F) ∥ (` 1F)) ∥ (` 2F)  — i.e. with
--     the handle and the off-handle owned by two PARALLEL sibling threads.
--
-- (4) wall : but there is NO  ≼  from that parallel struct up to the TP-Res body
--     struct  bodyStruct ≈ (` 0F ; ` 1F) ∥ ` 2F.  TP-Res forces the two borrows of
--     ONE chain to sit under `;` (structBinder), and ∥ ≼ ; is unavailable for the
--     two NON-Unr borrows (only ; ≼ ∥ holds, via ≼-wk).
--
-- CONCLUSION.  A well-typed rsplit redex CANNOT have a sibling owning an
-- off-handle borrow of the SAME chain being split as a PARALLEL peer: the borrows
-- of one chain are sequentially ordered (`;`), and TP-Par (`∥`) cannot split that
-- ordering across parallel threads.  Hence the source process the translation-flip
-- worry was about is VACUOUS — the flip is not exercised by any well-typed redex.
-- (The literal  ν (2 ∷ []) [] (…)  is additionally untypeable: B₂ = [] admits no
--  BindCtx, and with B₁ = 2 ∷ [] the off-handle is forced to ⟨ end ⁇ ⟩, not ⟨ msg ⁇ ⊤ ⟩.)
-- ============================================================================
