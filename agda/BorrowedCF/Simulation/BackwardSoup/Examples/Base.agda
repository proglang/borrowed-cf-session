-- Shared vocabulary for the backward-simulation example suite.
--
-- The suite tests the *naive* backward proposition of
-- `Simulation/BackwardSoup/PLAN.md` §1: for a closed `P : Typed.Proc 0`,
-- every soup step out of `flatten P` is matched by a typed step of `P`
-- whose reduct flattens exactly to the soup reduct.
module BorrowedCF.Simulation.BackwardSoup.Examples.Base where

open import Data.Maybe using (Maybe; just; nothing) public

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open Fin.Patterns public

-- The soup image of a closed typed process: the second projection of `U[_]`.
𝑪 : (P : 𝐓.Proc 0) →
    𝐒.Config (proj₁ 𝐔.U[ P ]) (proj₁ (proj₂ 𝐔.U[ P ]))
𝑪 P = proj₂ (proj₂ 𝐔.U[ P ])

-- The handle pattern shared by translation and soup reduction.
pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ 𝐒Tm.⊗ (𝐒Tm.` x)) 𝐒Tm.⊗ e₂
