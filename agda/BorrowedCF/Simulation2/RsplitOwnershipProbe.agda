module BorrowedCF.Simulation2.RsplitOwnershipProbe where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as RR

open Fin.Patterns
open Nat.Variables

-- ============================================================================
-- Probe: in the WELL-TYPED R-RSplit redex, can the sibling P own an OFF-HANDLE
-- chain slot?  Minimal instance  B1 = [], b1 = 1, B2 = [], B = [].
-- The split group is  suc b1 ∷ [] = 2 ∷ []  (a TWO-borrow chain).
-- The handle is slot 0F; the off-handle borrow is slot 1F.
-- ============================================================================

-- A New session whose  s ; end‼  expansion gives a TWO-borrow chain.
-- s = msg ‼ `⊤ ; msg ‼ `⊤  is New (each msg New, ; New).
sP : 𝕊 0
sP = msg ‼ `⊤ ; (msg ⁇ `⊤ ; skip)

NsP : New sP
NsP = New.msg New.; (New.msg New.; New.skip)

-- The two-slot channel context for the front chain  2 ∷ [] :
-- slot 0 : ⟨ msg ‼ `⊤ ⟩   (handle, rsplit domain head)
-- slot 1 : ⟨ msg ‼ `⊤ ⟩   (off-handle borrow)
g2 : Ctx 2
g2 = ⟨ msg ‼ `⊤ ⟩ F.∷ ⟨ msg ⁇ `⊤ ⟩ F.∷ (λ ())

-- A 2-borrow BindCtx′ over  sP  (msg ; (msg ; skip)), terminating in Skips skip.
-- This realises the TWO ordered borrows (slots 0F, 1F) of the front chain.
bc2 : BindCtx′ sP 2 g2
bc2 = cons (\ { (() ; _) }) ≃-refl (\ _ -> refl)
        (cons (\ { (() ; _) }) ≃-refl (\ _ -> refl)
          (nil skip))

-- ============================================================================
-- DECISIVE COUNT FACT (Outcome B): the OFF-HANDLE slot inj 1F is a genuine
-- linear resource of the TP-Res body context, appearing EXACTLY ONCE -- just
-- like the handle inj 0F.  The R-RSplit redex consumes only the handle, so
-- nothing forces inj 1F into E; conf-Proc only LOWER-bounds counts, hence the
-- single occurrence of inj 1F is free to be placed in the sibling P.
-- ============================================================================

module S = RR.SplitRenamings [] [] []   -- B1 = B2 = B' = []

open import BorrowedCF.Simulation2.Confine using (count)
import BorrowedCF.Context.Substitution as 𝐂

-- The TP-Res body context for  ν [2] [] ( ... )  at outer scope m = 0.
-- C1 = [] ++ suc 1 ∷ [] = 2 ∷ [].   B = [].   m = 0.
bodyStruct : Struct 2
bodyStruct =
    (structBinder (2 ∷ []) 𝐂.⋯ᵣ 𝐂.wkʳ 0 𝐂.⋯ᵣ 𝐂.wkʳ 0)
  ∥ (structBinder []      𝐂.⋯ᵣ 𝐂.wkˡ 2 𝐂.⋯ᵣ 𝐂.wkʳ 0)
  ∥ ([] 𝐂.⋯ᵣ 𝐂.weaken* 2)

-- handle = inj 0F  occurs exactly once (matches count-handle-⊓inner).
handle-count-1 : count (S.inj {2 ∷ []} {0} 0F) bodyStruct ≡ 1
handle-count-1 = refl

-- off-handle borrow = inj 1F  ALSO occurs exactly once.  It is NOT the handle,
-- NOT consumed by the rsplit redex, yet a full linear resource.
offhandle-count-1 : count (S.inj {2 ∷ []} {0} 1F) bodyStruct ≡ 1
offhandle-count-1 = refl

-- ============================================================================
-- The OFF-HANDLE slot 1F is genuinely OWNABLE BY A SIBLING P: a thread that
-- consumes  ` 1F : ⟨ msg ⁇ `⊤ ⟩  typechecks in the Struct  (` 1F)  alone.
-- This is the slot the rsplit redex does NOT touch -- so in the body's TP-Par
-- split  bodyStruct ⊑ γE ∥ γP, the unit  (` 1F)  may sit entirely in γP.
-- ============================================================================

-- P consumes the off-handle borrow via recv (message `⊤ is Mobile).
Poff : g2 ; ([] ∥ (` 1F)) ⊢ₚ ⟪ K `recv · (` 1F) ⟫
Poff = TP-Expr (T-AppLin refl 𝕀≤𝕀
  (T-Conv ≃-refl ℙ≤ϵ (T-Const (`recv `⊤)))
  (T-Conv ≃-refl ℙ≤ϵ (T-Var 1F refl)))
