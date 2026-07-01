{-# OPTIONS --rewriting #-}
-- ============================================================================
--  IS THE FixBreaksDrop COUNTEREXAMPLE VACUOUS?
--
--  FixBreaksDrop builds  src = ν (1 ∷ 1 ∷ []) [] (⟪ drop · ` 0F ⟫ ∥ …)  and
--  shows its translation cannot RU-Drop-step.  But it NEVER proves src is
--  WELL-TYPED.  This module decides, machine-checked, whether a GENUINELY
--  well-typed R-Drop redex exists whose front bind group is MULTI-chain
--  (B₁ nonempty in  ν (suc b₁ ∷ B₁) B₂ …), so the distributing Ub leaf gives
--  the drop-target head a  *  right-sync (not the flag ` 0F) and RU-Drop cannot
--  fire.
-- ============================================================================
module BorrowedCF.Simulation2.FixBreaksDropTyped where

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
open import BorrowedCF.Simulation2.Base using (funext)
open import BorrowedCF.Simulation2.Base using (U[_])
import BorrowedCF.Processes.Untyped as U


open Fin.Patterns
open Nat.Variables

-- ── The new-session parameter.  s = msg ‼ ⊤ (New).
sParam : 𝕊 0
sParam = msg ‼ `⊤

Ns : New sParam
Ns = New.msg

-- ── Front group  B₁ = 1 ∷ 1 ∷ []  (MULTI-chain: first chain width 1 = the drop
--    handle ⟨ ret ⟩; second chain width 1 carries the real session).
--    Back group  B₂ = 1 ∷ [].

-- Front context: slot0 = ⟨ ret ⟩ (drop handle, empty first chain skip;ret),
-- slot1 = ⟨ acq ; msg ‼ ⊤ ; end ⁇ ⟩ (second chain, the real session).
Γfront : Ctx 2
Γfront = ⟨ ret ⟩ F.∷ ⟨ acq ; (msg ‼ `⊤ ; end ⁇) ⟩ F.∷ (λ ())

-- First chain (width 1):  BindCtx′ (skip ; ret) 1  with head ⟨ ret ⟩.
c1 : BindCtx′ (skip ; ret) 1 (λ _ → ⟨ ret ⟩)
c1 = cons {s₁ = ret} {s₂ = skip} {Γ′ = λ ()} (λ { (_ ; ()) }) (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (λ { 0F → refl }) (nil skip)

-- Second chain (width 1):  BindCtx (acq ; (msg ‼ ⊤ ; end ⁇)) (1 ∷ []).
c2 : BindCtx (acq ; (msg ‼ `⊤ ; end ⁇)) (1 ∷ []) (λ _ → ⟨ acq ; (msg ‼ `⊤ ; end ⁇) ⟩)
c2 = last (cons {s₁ = acq ; (msg ‼ `⊤ ; end ⁇)} {s₂ = skip} {Γ′ = λ ()} (λ { (() ; _) }) ≃-skipʳ (λ { 0F → refl }) (nil skip))

Cfront : BindCtx (sParam ; end ⁇) (1 ∷ 1 ∷ []) Γfront
Cfront = cons-ret/acq {s₁ = skip} {s₂ = msg ‼ `⊤ ; end ⁇} ≃-skipˡ (λ { 0F → refl ; 1F → refl }) c1 c2

-- ── Back group  B₂ = 1 ∷ [].  Back session  dual sParam ; end ‼ = msg ⁇ ⊤ ; end ‼.
Γback : Ctx 1
Γback = (λ _ → ⟨ (msg ⁇ `⊤) ; end ‼ ⟩)

Cback : BindCtx ((dual sParam) ; end ‼) (1 ∷ []) Γback
Cback = last (cons {s₁ = (dual sParam) ; end ‼} {s₂ = skip} {Γ′ = λ ()} (λ { (() ; _) }) ≃-skipʳ (λ { 0F → refl }) (nil skip))

⊢B₁ : ⊢ᴮ (1 ∷ 1 ∷ [])
⊢B₁ = (record { nonZero = _ }) All.∷ All.[]

⊢B₂ : ⊢ᴮ (1 ∷ [])
⊢B₂ = All.[]

-- ── The body context at scope 3:  slots 0F,1F = front borrows, 2F = back borrow.
Γbody : Ctx 3
Γbody = (Γfront ⸴* Γback) ⸴* (λ ())

-- ── Probe: the TP-Res body struct for  ν (1 ∷ 1 ∷ []) (1 ∷ []) …  at outer scope 0.
resBodyStruct : Struct 3
resBodyStruct = (structBinder (1 ∷ 1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ (structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 3)

-- Component reductions (each holds by refl: a single structBinder ⋯ᵣ-composition
-- reduces, though the full 3-way ≡ does not because of ∥-nesting).
frontRed : (structBinder (1 ∷ 1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0) ≡ (((` 0F) ; []) ∥ ((((` 1F) ; []) ∥ [])))
frontRed = refl

backRed : (structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0) ≡ ((((` 2F) ; []) ∥ []))
backRed = refl

outerRed : ([] 𝐂.⋯ᵣ 𝐂.weaken* 3) ≡ ([] {n = 3})
outerRed = refl

resBodyLit : Struct 3
resBodyLit = (((((` 0F) ; []) ∥ ((((` 1F) ; []) ∥ []))) ∥ ((((` 2F) ; []) ∥ []))) ∥ [])

resBodyStructEq : resBodyStruct ≡ resBodyLit
resBodyStructEq = cong₂ _∥_ (cong₂ _∥_ frontRed backRed) outerRed


-- ============================================================================
-- KEY OBSERVATION.  resBodyStruct normalises to
--    (` 0F ; []) ∥ ((` 1F ; []) ∥ []) ∥ ((` 2F ; []) ∥ []) ∥ []
-- i.e. the three borrows sit in PARALLEL (front chains are ∥-separated because
-- B₁ = 1 ∷ 1 ∷ [] has TWO width-1 chains).  So — UNLIKE the rsplit case — there
-- is NO Sep wall: the drop head 0F, the second-chain borrow 1F and the back
-- borrow 2F can be routed to three parallel threads by TP-Par.
-- ============================================================================

-- ── DROP thread: owns the head borrow 0F : ⟨ ret ⟩, consumed by `drop`.
dropThread : Tm 3
dropThread = K `drop · (` 0F)

⊢dropThread : Γbody ; (` 0F) ⊢ₚ ⟪ dropThread ⟫
⊢dropThread = TP-Expr (T-Weaken (≼-refl ∥-unit₁)
  (T-AppLin refl ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Const `drop)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))

-- ============================================================================
-- THE SIBLING  P : Proc 2  at the reduct scope (2 borrows: P's 0F = second
-- front chain ⟨ acq ; msg ‼ ⊤ ; end ⁇ ⟩, P's 1F = back ⟨ msg ⁇ ⊤ ; end ‼ ⟩).
-- After  ⋯ₚ weakenᵣ  these become slots 1F, 2F of Γbody.
-- ============================================================================

-- Reduct-scope context for P.
ΓP : Ctx 2
ΓP = ⟨ acq ; (msg ‼ `⊤ ; end ⁇) ⟩ F.∷ ⟨ (msg ⁇ `⊤) ; end ‼ ⟩ F.∷ (λ ())

-- Thread B (P's 1F, the back chain): lsplit off the msg, recv it, close ‼.
threadB : Tm 2
threadB =
  `let⊗ (K (`lsplit (msg ⁇ `⊤)) · (` 1F))
   `in ((K `recv · (` 0F)) ; (K (`end ‼) · (` 1F)))

⊢threadB : ΓP ; (` 1F) ⊢ₚ ⟪ threadB ⟫
⊢threadB = TP-Expr (T-Weaken (≼-refl (≈-trans ∥-unit₂ ∥-unit₁)) (T-LetPair par ⊢Blsplit ⊢Bbody))
  where
    ⊢Blsplit : ΓP ; ([] ∥ (` 1F)) ⊢ K (`lsplit (msg ⁇ `⊤)) · (` 1F) ∶ ⟨ msg ⁇ `⊤ ⟩ ⊗ᴸ ⟨ end ‼ ⟩ ∣ 𝕀
    ⊢Blsplit = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ
      (T-AppLin refl ℙ≤ϵ (T-Const (`lsplit (λ ()) (end ‼))) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))
    ΓBk : Ctx 4
    ΓBk = ⟨ msg ⁇ `⊤ ⟩ ⸴ ⟨ end ‼ ⟩ ⸴ ΓP
    ⊢Brecv : ΓBk ; (` 0F) ⊢ K `recv · (` 0F) ∶ `⊤ ∣ 𝕀
    ⊢Brecv = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`recv `⊤))) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))
    ⊢Bend : ΓBk ; (` 1F) ⊢ K (`end ‼) · (` 1F) ∶ `⊤ ∣ 𝕀
    ⊢Bend = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))
    ⊢Bbody : ΓBk ; (((` 0F) ; (` 1F)) ∥ []) ⊢ (K `recv · (` 0F)) ; (K (`end ‼) · (` 1F)) ∶ `⊤ ∣ 𝕀
    ⊢Bbody = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢Brecv ⊢Bend)

-- Thread A (P's 0F = second front chain ⟨ acq ; msg ‼ ⊤ ; end ⁇ ⟩):
--   acquire → ⟨ msg ‼ ⊤ ; end ⁇ ⟩, lsplit, send the msg, close ⁇.
threadA : Tm 2
threadA =
  `let (K `acq · (` 0F))
   `in (`let⊗ (K (`lsplit (msg ‼ `⊤)) · (` 0F))
        `in ((K `send · (* ⊗ (` 0F))) ; (K (`end ⁇) · (` 1F))))

⊢threadA : ΓP ; (` 0F) ⊢ₚ ⟪ threadA ⟫
⊢threadA = TP-Expr (T-Weaken (≼-refl ;-unit₂) (T-Let seq ⊢Aacq ⊢Abody))
  where
    ⊢Aacq : ΓP ; (` 0F) ⊢ K `acq · (` 0F) ∶ ⟨ msg ‼ `⊤ ; end ⁇ ⟩ ∣ 𝕀
    ⊢Aacq = T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl ℙ≤ϵ (T-Const (`acq {s = msg ‼ `⊤ ; end ⁇})) (T-Var 0F refl)))
    ΓA1 : Ctx 3
    ΓA1 = ⟨ msg ‼ `⊤ ; end ⁇ ⟩ ⸴ ΓP
    ⊢Abody : ΓA1 ; join seq (` 0F) (𝐂.wk []) ⊢ (`let⊗ (K (`lsplit (msg ‼ `⊤)) · (` 0F)) `in ((K `send · (* ⊗ (` 0F))) ; (K (`end ⁇) · (` 1F)))) ∶ `⊤ ∣ 𝕀
    ⊢Abody = T-Weaken (≼-refl (≈-trans ∥-unit₂ (≈-trans ∥-unit₁ (≈-sym ;-unit₂)))) (T-LetPair par ⊢Alsplit ⊢Abody2)
      where
        ⊢Alsplit : ΓA1 ; ([] ∥ (` 0F)) ⊢ K (`lsplit (msg ‼ `⊤)) · (` 0F) ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩ ∣ 𝕀
        ⊢Alsplit = T-Conv (⟨ ≃-refl ⟩ ⊗ ⟨ ≃-refl ⟩) ℙ≤ϵ
          (T-AppLin refl ℙ≤ϵ (T-Const (`lsplit (λ ()) (end ⁇))) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl)))
        ΓA2 : Ctx 5
        ΓA2 = ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ end ⁇ ⟩ ⸴ ΓA1
        ⊢Asend : ΓA2 ; (` 0F) ⊢ K `send · (* ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
        ⊢Asend = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁)) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
                   (T-Pair par par (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))
        ⊢Aclose : ΓA2 ; (` 1F) ⊢ K (`end ⁇) · (` 1F) ∶ `⊤ ∣ 𝕀
        ⊢Aclose = T-Weaken (≼-refl ∥-unit₁) (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))
        ⊢Abody2 : ΓA2 ; (((` 0F) ; (` 1F)) ∥ []) ⊢ (K `send · (* ⊗ (` 0F))) ; (K (`end ⁇) · (` 1F)) ∶ `⊤ ∣ 𝕀
        ⊢Abody2 = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢Asend ⊢Aclose)



-- ============================================================================
-- ASSEMBLE the sibling  P =  threadA  ∥  threadB   and weaken by weakenᵣ.
-- ============================================================================
Psib : Proc 2
Psib = ⟪ threadA ⟫ ∥ ⟪ threadB ⟫

⊢P : ΓP ; ((` 0F) ∥ (` 1F)) ⊢ₚ Psib
⊢P = TP-Par ⊢threadA ⊢threadB

-- weakenᵣ inserts ⟨ ret ⟩ at slot 0F:  ⟨ ret ⟩ ⸴ ΓP ≡ Γbody.
Γbody-eq : (⟨ ret ⟩ ⸴ ΓP) ≡ Γbody
Γbody-eq = funext (λ { 0F → refl ; 1F → refl ; (suc (suc 0F)) → refl })

⊢Pwk0 : (⟨ ret ⟩ ⸴ ΓP) ; ((` 1F) ∥ (` 2F)) ⊢ₚ (Psib ⋯ₚ weakenᵣ)
⊢Pwk0 = ⊢P ⊢⋯ₚ ⊢weakenᵣ {T = ⟨ ret ⟩} ΓP

⊢Pwk : Γbody ; ((` 1F) ∥ (` 2F)) ⊢ₚ (Psib ⋯ₚ weakenᵣ)
⊢Pwk = subst (λ Γ → Γ ; ((` 1F) ∥ (` 2F)) ⊢ₚ (Psib ⋯ₚ weakenᵣ)) Γbody-eq ⊢Pwk0

-- ============================================================================
-- THE FULL R-Drop REDEX BODY and its TP-Res derivation.
-- ============================================================================
srcBody : Proc 3
srcBody = ⟪ dropThread ⟫ ∥ (Psib ⋯ₚ weakenᵣ)

-- body typed at the clean parallel struct (` 0F) ∥ ((` 1F) ∥ (` 2F)).
⊢srcBodyClean : Γbody ; ((` 0F) ∥ ((` 1F) ∥ (` 2F))) ⊢ₚ srcBody
⊢srcBodyClean = TP-Par ⊢dropThread ⊢Pwk

-- weaken up to the TP-Res body struct.
⊢srcBody : Γbody ; resBodyStruct ⊢ₚ srcBody
⊢srcBody = TP-Weaken bodyLE ⊢srcBodyClean
  where
    bodyLE : Γbody ∶ ((` 0F) ∥ ((` 1F) ∥ (` 2F))) ≼ resBodyStruct
    bodyLE = ≼-refl (≈-sym chain)
      where
        open ≈-Reasoning
        chain : Γbody ∶ resBodyStruct ≈ ((` 0F) ∥ ((` 1F) ∥ (` 2F)))
        chain =
          ≈-trans (≈-reflexive resBodyStructEq)
            (≈-trans
              (≈-trans ∥-unit₂
                (CE.∥-cong
                  (CE.∥-cong ;-unit₂ (≈-trans ∥-unit₂ ;-unit₂))
                  (≈-trans ∥-unit₂ ;-unit₂)))
              CE.∥-assoc)





-- ============================================================================
-- THE WELL-TYPED MULTI-CHAIN-HEAD R-Drop REDEX.
--   src = ν (1 ∷ 1 ∷ []) (1 ∷ []) (⟪ drop · ` 0F ⟫ ∥ (Psib ⋯ₚ weakenᵣ))
-- Front group 1 ∷ 1 ∷ [] is MULTI-chain (two width-1 chains): its head borrow
-- ⟨ ret ⟩ (slot 0F) is a MULTI-chain-group head, so the distributing Ub leaf
-- gives that handle a  *  right-sync and RU-Drop cannot fire.
-- ============================================================================
src : Proc 0
src = ν (1 ∷ 1 ∷ []) (1 ∷ []) srcBody

⊢src : (λ ()) ; [] ⊢ₚ src
⊢src = TP-Res Ns ⊢B₁ ⊢B₂ Cfront Cback ⊢srcBody

-- ── src IS a genuine R-Drop redex (drops the front-chain head borrow ` 0F). ──
open RR using (_─→ₚ_)

src─→ : src ─→ₚ ν (0 ∷ 1 ∷ []) (1 ∷ []) (⟪ ([] [ K `unit ]*) ⟫ ∥ Psib)
src─→ = RR.R-Drop {b₁ = 0} {B₁ = 1 ∷ []} {B₂ = 1 ∷ []} {P = Psib} {E = []}



-- ============================================================================
-- THE BREAKAGE, on this WELL-TYPED source (real U[_]).
--   U[ src ] has the drop thread  ⟪ drop · ((* ⊗ ` 1F) ⊗ *) ⟫ : the drop-target
--   handle triple's RIGHT-sync slot is  *  (a unit constant), NOT the flag var
--   ` 0F that RU-Drop requires.  So NO RU-Drop step fires on U[ src ] — the
--   R-Drop forward-simulation step  U[ src ] ─→ U[ reduct ]  is unconstructible,
--   even though src is well-typed and R-Drop-reduces.
-- ============================================================================

Usrc : U.Proc 0
Usrc = U[ src ] (λ ())

-- The drop-thread handle triple in Usrc has right-sync  *  (machine-checked).
Usrc-drophandle :
  Usrc ≡ U.Proc.ν (U.Proc.φ U.drop
    ( U.Proc.⟪ K `drop · ((* ⊗ (` 1F)) ⊗ *) ⟫
    U.Proc.∥
      ( U.Proc.⟪ `let (K `acq · (((` 0F) ⊗ (` 1F)) ⊗ *))
                  `in (`let⊗ (K (`lsplit (msg ‼ `⊤)) · (` 0F))
                       `in ((K `send · (* ⊗ (` 0F))) ; (K (`end ⁇) · (` 1F)))) ⟫
      U.Proc.∥
        U.Proc.⟪ `let⊗ (K (`lsplit (msg ⁇ `⊤)) · ((* ⊗ (` 2F)) ⊗ *))
                  `in ((K `recv · (` 0F)) ; (K (`end ‼) · (` 1F))) ⟫ )))
Usrc-drophandle = refl

-- The right-sync slot is  *  (unit), not a flag variable.  Hence RU-Drop's read
-- shape  ((e ⊗ ` (suc x)) ⊗ ` 0F)  cannot match the drop handle: no (e , x) fits.
dropTriple : Tm 3
dropTriple = (* ⊗ (` 1F)) ⊗ *

no-RU-Drop-match :
  ¬ (Σ[ e ∈ Tm 3 ] Σ[ x ∈ 𝔽 2 ] dropTriple ≡ ((e ⊗ (` suc x)) ⊗ (` 0F)))
no-RU-Drop-match (e , x , ())
