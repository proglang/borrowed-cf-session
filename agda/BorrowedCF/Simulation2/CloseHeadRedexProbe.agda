module BorrowedCF.Simulation2.CloseHeadRedexProbe where

-- FULL TP-Res witness: is  ν [2] [1] (closeFirstThread ∥ back)  well-typed,
-- where closeFirstThread closes the LATER block-1 borrow (1F) FIRST (head redex)
-- and only THEN uses the earlier borrow (0F)?  If yes, the reverse RU-Close ?4
-- inner-handle case with a LIVE earlier borrow is genuinely reachable AS A HEAD
-- REDEX, and neither R-Discard (0F live) nor R-Close (block width 2) fires.

open import Data.Vec.Functional as F using ()
open import Data.List.Relation.Unary.All as All using (All)
import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Equivalence as CE

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed

open Fin.Patterns
open Nat.Variables

sParam : 𝕊 0
sParam = msg ‼ `⊤

-- Front chain (msg ‼ ⊤ ; end ⁇) split into 2 borrows:
--   slot0 = ⟨ msg ‼ ⊤ ⟩  (earlier), slot1 = ⟨ end ⁇ ⟩ (close handle)
Γfront : Ctx 2
Γfront = ⟨ msg ‼ `⊤ ⟩ F.∷ ⟨ end ⁇ ⟩ F.∷ (λ ())

↑ˡ0-2 : (x : 𝔽 2) → x ↑ˡ 0 ≡ x
↑ˡ0-2 0F = refl
↑ˡ0-2 1F = refl

bc-front′ : BindCtx′ (sParam ; end ⁇) 2 (Γfront ∘ wkʳ 0)
bc-front′ =
  cons (λ { (() ; _) }) ≃-refl (λ x → sym (cong Γfront (↑ˡ0-2 x)))
    (cons (λ ()) ≃-skipʳ (λ _ → refl)
      (nil skip))

Cfront : BindCtx (sParam ; end ⁇) (2 ∷ []) Γfront
Cfront = last bc-front′

Γback : Ctx 1
Γback = (λ _ → ⟨ (msg ⁇ `⊤) ; end ‼ ⟩)

bc-back′ : BindCtx′ ((dual sParam) ; end ‼) 1 (Γback ∘ wkʳ 0)
bc-back′ = cons (λ { (() ; _) }) ≃-skipʳ (λ { 0F → refl }) (nil skip)

Cback : BindCtx ((dual sParam) ; end ‼) (1 ∷ []) Γback
Cback = last bc-back′

⊢B₁ : ⊢ᴮ (2 ∷ [])
⊢B₁ = All.[]
⊢B₂ : ⊢ᴮ (1 ∷ [])
⊢B₂ = All.[]

Γbody : Ctx 3
Γbody = (Γfront ⸴* Γback) ⸴* (λ ())

-- FRONT thread: close 1F FIRST, THEN send on 0F.   REVERSE order.
frontThread : Tm 3
frontThread = (K (`end ⁇) · (` 1F)) ; (K `send · (* ⊗ (` 0F)))

⊢fclose : Γbody ; (` 1F) ⊢ K (`end ⁇) · (` 1F) ∶ `⊤ ∣ 𝕀
⊢fclose = T-Weaken (≼-refl ∥-unit₁)
  (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const `end)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 1F refl)))

⊢fsend : Γbody ; (` 0F) ⊢ K `send · (* ⊗ (` 0F)) ∶ `⊤ ∣ 𝕀
⊢fsend = T-Weaken (≼-refl (≈-trans ∥-unit₁ ∥-unit₁))
  (T-AppLin refl 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Const (`send `⊤)))
    (T-Pair par par (T-Conv `⊤ ℙ≤ϵ (T-Const `unit)) (T-Conv ⟨ ≃-refl ⟩ ℙ≤ϵ (T-Var 0F refl))))

⊢frontBody : Γbody ; (((` 1F) ; (` 0F)) ∥ []) ⊢ frontThread ∶ `⊤ ∣ 𝕀
⊢frontBody = T-Weaken (≼-refl (≈-sym ∥-unit₂)) (T-Seq `⊤ ⊢fclose ⊢fsend)

⊢frontThread : Γbody ; ((` 1F) ; (` 0F)) ⊢ₚ ⟪ frontThread ⟫
⊢frontThread = TP-Expr (T-Weaken (≼-refl ∥-unit₂) ⊢frontBody)

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

bodyProc : Proc 3
bodyProc = ⟪ frontThread ⟫ ∥ ⟪ backThread ⟫

-- CLEAN struct: front thread's struct is (` 1F) ; (` 0F)  [reverse order!]
⊢bodyClean : Γbody ; (((` 1F) ; (` 0F)) ∥ (` 2F)) ⊢ₚ bodyProc
⊢bodyClean = TP-Par ⊢frontThread ⊢backThread

resBodyStruct : Struct 3
resBodyStruct = (structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 1 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ (structBinder (1 ∷ []) 𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
              ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 3)

-- The KEY question: does the reverse-order clean struct  (` 1F) ; (` 0F)
-- weaken UP to resBodyStruct (whose block-1 is  0F ; (1F ; []),  FORWARD order)?
-- If body≼ typechecks, the inner-handle close head-redex is well-typed ⇒ ?4 blocked.
body≼ : Γbody ∶ (((` 1F) ; (` 0F)) ∥ (` 2F)) ≼ resBodyStruct
body≼ = ≼-refl (CE.∥-cong (≈-sym (CE.;-cong ≈-refl ;-unit₂)) ;-unit₂ ◅◅ CE.∥-cong CE.∥-comm CE.∥-comm)

⊢resBody : Γbody ; resBodyStruct ⊢ₚ bodyProc
⊢resBody = TP-Weaken body≼ ⊢bodyClean

theProc : Proc 0
theProc = ν (2 ∷ []) (1 ∷ []) bodyProc

⊢theProc : (λ ()) ; [] ⊢ₚ theProc
⊢theProc = TP-Res New.msg ⊢B₁ ⊢B₂ Cfront Cback ⊢resBody
