module BorrowedCF.Simulation.LSplitRevProbe where

open import Data.Vec.Functional as F using ()
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Terms
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed

open Fin.Patterns

-- A REAL nu-bindable block:  msg S msg S end  =  New(msg S msg) ; end.
-- slot0 = < msg > (used); slot1 = < msg S end > (lsplit-able).  Unlike gA's
-- < acq S end > (acq is not in New, so cannot be a block slot), THIS block is
-- BindCtx'-inhabited, hence nu-bindable.
gL : Ctx 2
gL = ⟨ msg ‼ `⊤ ⟩ F.∷ (⟨ (msg ‼ `⊤) ; (end ⁇) ⟩ F.∷ (λ ()))

gL-block : BindCtx′ ((msg ‼ `⊤) ; ((msg ‼ `⊤) ; (end ⁇))) 2 gL
gL-block = cons (λ { (() ; _) }) ≃-refl (λ _ → refl)
             (cons (λ { (() ; _) }) ≃-skipʳ (λ _ → refl) (nil skip))

-- A PURE lsplit operates the NON-front slot 1F while used borrow 0F is held,
-- typed at the honest block order (` 0F)S(` 1F).  Typed R-LSplit fires only at
-- block-front 0F ==> no typed rule matches this lsplit at 1F.
posL : gL ; ((` 0F) ; (` 1F)) ⊢ (` 0F) ⊗ (K (`lsplit (msg ‼ `⊤)) ·¹ (` 1F))
         ∶ ⟨ msg ‼ `⊤ ⟩ ⊗ᴸ (⟨ msg ‼ `⊤ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩) ∣ ℙ
posL = T-Weaken (≼-refl (;-cong ≈-refl ∥-unit₁))
         (T-Pair seq seq (T-Var 0F refl)
           (T-AppUnr refl ℙ≤ϵ (T-Const (`lsplit (λ ()) (end ⁇))) (T-Var 1F refl)))
