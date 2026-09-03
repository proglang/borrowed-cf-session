-- Backward simulation, the three rules that consume a handle:
-- `RUS-Drop`, `RUS-Discard` and `RUS-Acquire`.
--
-- Findings (positive examples only; the F4 probes live in `Probes.agda`):
-- when the consumed handle sits where the typed rules demand it -- the
-- variable `0F`, i.e. the first handle of the first group of the LEFT
-- binder list, with width-0 first group for `R-Acq` -- the naive
-- proposition HOLDS for all three rules, on the nose.
module BorrowedCF.Simulation.BackwardSoup.Examples.Handles where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Reduction.ExpressionsSoup as 𝐒Red
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

------------------------------------------------------------------------
-- 1. Drop.
--
-- The left binder list is `1 ∷ 1 ∷ []`: a width-1 group carrying the
-- `ret` half, then a sync boundary (`drop`), then the live remainder.
-- The dropping thread holds handle 0F, the other thread holds handle 1F.

Pd : 𝐓.Proc 0
Pd =
  𝐓.ν (1 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K 𝐓Tm.`drop 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.` 1F ⟫)

Cd : 𝐒.Config 1 2
Cd = 𝑪 Pd

Cd≡ :
  Cd ≡
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`drop 𝐒Tm.·¹
        𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ]) ∷
      𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ] ∷
      [])
Cd≡ = refl

-- Dropping turns the boundary from `drop` into `acq`: the partner may now
-- acquire what the dropper gave back.
Cd′ : 𝐒.Config 1 2
Cd′ =
  𝐒.config
    ((true , 𝐒.acq ∷ [] , []) ∷ [])
    ( 𝐒Tm.* ∷
      𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ] ∷
      [])

step-drop : Cd 𝐑.─→ₚ Cd′
step-drop = 𝐑.RUS-Drop 0F 0F 0F [] [] [] refl refl refl

Pd′ : 𝐓.Proc 0
Pd′ =
  𝐓.ν (0 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.` 0F ⟫)

red-drop : Pd 𝐓𝐑.─→ₚ Pd′
red-drop =
  𝐓𝐑.R-Drop
    {b₁ = 0} {B₁ = 1 ∷ []} {B₂ = 1 ∷ []}
    {P = 𝐓.⟪ 𝐓Tm.` 0F ⟫} {E = []}

drop-exact-flatten : 𝑪 Pd′ ≡ Cd′
drop-exact-flatten = refl

------------------------------------------------------------------------
-- 2. Discard.

Pdi : 𝐓.Proc 0
Pdi =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K 𝐓Tm.`discard 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cdi : 𝐒.Config 1 2
Cdi = 𝑪 Pdi

Cdi≡ :
  Cdi ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`discard 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Cdi≡ = refl

Cdi′ : 𝐒.Config 1 2
Cdi′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    (𝐒Tm.* ∷ 𝐒Tm.* ∷ [])

step-discard : Cdi 𝐑.─→ₚ Cdi′
step-discard =
  𝐑.RUS-Discard 0F [] (𝐒Red.V-⊗ (𝐒Red.V-⊗ 𝐒Red.V-K 𝐒Red.V-`) 𝐒Red.V-K) refl

Pdi′ : 𝐓.Proc 0
Pdi′ = 𝐓.ν (0 ∷ []) (1 ∷ []) (𝐓.⟪ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-discard : Pdi 𝐓𝐑.─→ₚ Pdi′
red-discard =
  𝐓𝐑.R-Discard
    {b₁ = 0} {B₁ = []} {B₂ = 1 ∷ []}
    {P = 𝐓.⟪ 𝐓Tm.* ⟫} {E = []}

discard-exact-flatten : 𝑪 Pdi′ ≡ Cdi′
discard-exact-flatten = refl

------------------------------------------------------------------------
-- 3. Acquire.
--
-- `R-Acq` needs a width-0 first group, i.e. an endpoint whose first
-- boundary is already `acq` -- exactly the state `RUS-Drop` leaves behind.

Pa : 𝐓.Proc 0
Pa =
  𝐓.ν (0 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K 𝐓Tm.`acq 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Ca : 𝐒.Config 1 2
Ca = 𝑪 Pa

Ca≡ :
  Ca ≡
  𝐒.config
    ((true , 𝐒.acq ∷ [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`acq 𝐒Tm.·¹
        𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Ca≡ = refl

-- Acquiring REMOVES the boundary: the endpoint's flag list shrinks and
-- every remaining reference to a later slot is renumbered by `consumePhi`.
Ca′ : 𝐒.Config 1 2
Ca′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    (𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷ 𝐒Tm.* ∷ [])

step-acq : Ca 𝐑.─→ₚ Ca′
step-acq = 𝐑.RUS-Acquire 0F 0F 0F [] [] [] refl refl refl

Pa′ : 𝐓.Proc 0
Pa′ = 𝐓.ν (1 ∷ []) (1 ∷ []) (𝐓.⟪ 𝐓Tm.` 0F ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-acq : Pa 𝐓𝐑.─→ₚ Pa′
red-acq =
  𝐓𝐑.R-Acq
    {b₁ = 0} {B₁ = []} {B₂ = 1 ∷ []}
    {P = 𝐓.⟪ 𝐓Tm.* ⟫} {E = []}

acq-exact-flatten : 𝑪 Pa′ ≡ Ca′
acq-exact-flatten = refl
