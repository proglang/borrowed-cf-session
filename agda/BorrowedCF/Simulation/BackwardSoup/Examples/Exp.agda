-- Backward simulation, rule `RUS-Exp` (failure mode F5 of PLAN.md §2).
--
-- Finding: the naive proposition HOLDS.  A soup expression step on the
-- translation of a source expression is the translation of a source step,
-- and `flatten` of the typed reduct is the soup reduct on the nose.
module BorrowedCF.Simulation.BackwardSoup.Examples.Exp where

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (skip)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Reduction.Base as 𝐓E
import BorrowedCF.Reduction.Expressions as 𝐓Red
import BorrowedCF.Reduction.ExpressionsSoup as 𝐒Red
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

------------------------------------------------------------------------
-- A beta redex whose argument is a channel handle.

-- ν ⟨s⟩ ⟨dual s⟩ . ⟪ (λx. x) x₀ ⟫  --  the argument translates to a triple.
P : 𝐓.Proc 0
P = 𝐓.ν (1 ∷ []) (1 ∷ [])
      𝐓.⟪ (𝐓Tm.ƛ (𝐓Tm.` 0F)) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫

C : 𝐒.Config 1 1
C = 𝑪 P

C≡ :
  C ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    (((𝐒Tm.ƛ (𝐒Tm.` 0F)) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷ [])
C≡ = refl

C′ : 𝐒.Config 1 1
C′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    (𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷ [])

-- The soup step: beta with a value argument (the handle triple is a value).
step : C 𝐑.─→ₚ C′
step =
  𝐑.RUS-Exp 0F
    (𝐒Red.E-□ (𝐒Red.E-App (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K)))

P′ : 𝐓.Proc 0
P′ = 𝐓.ν (1 ∷ []) (1 ∷ []) 𝐓.⟪ 𝐓Tm.` 0F ⟫

-- The typed step: the same beta redex, one `R-Bind` deep.
red : P 𝐓𝐑.─→ₚ P′
red = 𝐓𝐑.R-Bind (𝐓𝐑.R-Exp (𝐓Red.E-□ (𝐓Red.E-App 𝐓E.V-`)))

-- F5: exact flattening.  No generalisation needed.
exp-exact-flatten : 𝑪 P′ ≡ C′
exp-exact-flatten = refl

------------------------------------------------------------------------
-- The same phenomenon one frame deep: the soup frame is the translation
-- of the source frame, so `E-Ctx` transports verbatim.

Q : 𝐓.Proc 0
Q = 𝐓.ν (1 ∷ []) (1 ∷ [])
      𝐓.⟪ ((𝐓Tm.ƛ (𝐓Tm.` 0F)) 𝐓Tm.·¹ (𝐓Tm.` 0F)) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫

QC : 𝐒.Config 1 1
QC = 𝑪 Q

QC≡ :
  QC ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ((((𝐒Tm.ƛ (𝐒Tm.` 0F)) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])
      𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷ [])
QC≡ = refl

QC′ : 𝐒.Config 1 1
QC′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ((𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷ [])

step-ctx : QC 𝐑.─→ₚ QC′
step-ctx =
  𝐑.RUS-Exp 0F
    (𝐒Red.E-Ctx (𝐒Red.□⊗ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ])
      (𝐒Red.E-□
        (𝐒Red.E-App (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K))))

Q′ : 𝐓.Proc 0
Q′ = 𝐓.ν (1 ∷ []) (1 ∷ []) 𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫

red-ctx : Q 𝐓𝐑.─→ₚ Q′
red-ctx =
  𝐓𝐑.R-Bind
    (𝐓𝐑.R-Exp
      (𝐓Red.E-Ctx (𝐓E.□⊗ (𝐓Tm.` 1F))
        (𝐓Red.E-□ (𝐓Red.E-App 𝐓E.V-`))))

exp-ctx-exact-flatten : 𝑪 Q′ ≡ QC′
exp-ctx-exact-flatten = refl
