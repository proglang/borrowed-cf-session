-- Backward simulation, the three two-party rules: `RUS-Com`, `RUS-Choice`
-- and `RUS-Close` (failure mode F1 of PLAN.md §2).
--
-- Findings:
--   * Com and Choice: the naive proposition HOLDS, and it keeps holding
--     when the two partner threads sit in the "wrong" order, because
--     `replaceTwo` writes back in place and `R-Struct ∥-comm` re-orders
--     the typed side without moving anything in the soup.
--   * Close: the naive proposition FAILS (F1).  `RUS-Close` retains the
--     channel as a dead cell `(false , [] , [])` while `R-Close` erases
--     the `ν` outright, so the two configurations do not even have the
--     same channel count.  What holds is `GlobalImage P′ C′` with the
--     dead channel accounted for by `garbage-channel`.
module BorrowedCF.Simulation.BackwardSoup.Examples.Sync where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (‼; ⁇)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Reduction.Base as 𝐓E
import BorrowedCF.Reduction.ExpressionsSoup as 𝐒Red
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.World

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

------------------------------------------------------------------------
-- 1. Com, partners in the canonical (send, recv) order.
--
-- ν ⟨msg ‼ T⟩ ⟨msg ⁇ T⟩ ((⟪ send (λx.() ⊗ x₀) ⟫ ∥ ⟪ recv x₁ ⟫) ∥ ⟪ () ⟫)

payload : 𝐓Tm.Tm 2
payload = 𝐓Tm.ƛ 𝐓Tm.*

Pc : 𝐓.Proc 0
Pc =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (payload 𝐓Tm.⊗ (𝐓Tm.` 0F)) ⟫
      𝐓.∥ 𝐓.⟪ 𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cc : 𝐒.Config 1 3
Cc = 𝑪 Pc

Cc≡ :
  Cc ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K 𝐒Tm.`send 𝐒Tm.·¹
        ((𝐒Tm.ƛ 𝐒Tm.*) 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ])) ∷
      (𝐒Tm.K 𝐒Tm.`recv 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Cc≡ = refl

Cc′ : 𝐒.Config 1 3
Cc′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    (𝐒Tm.* ∷ (𝐒Tm.ƛ 𝐒Tm.*) ∷ 𝐒Tm.* ∷ [])

step-com : Cc 𝐑.─→ₚ Cc′
step-com =
  𝐑.RUS-Com 0F 1F 0F 0F 1F [] []
    (λ ()) 𝐑.left-right refl 𝐒Red.V-λ refl refl

Pc′ : 𝐓.Proc 0
Pc′ =
  𝐓.ν (0 ∷ []) (0 ∷ [])
    ((𝐓.⟪ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.ƛ 𝐓Tm.* ⟫) 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-com : Pc 𝐓𝐑.─→ₚ Pc′
red-com = 𝐓𝐑.R-Com {e = 𝐓Tm.ƛ 𝐓Tm.*} {E₁ = []} {E₂ = []} 𝐓E.V-λ

com-exact-flatten : 𝑪 Pc′ ≡ Cc′
com-exact-flatten = refl

------------------------------------------------------------------------
-- 2. Com with the partners in the swapped order (⟪ recv ⟫ ∥ ⟪ send ⟫).
--
-- The soup step just addresses the two threads by their indices, and
-- `replaceTwo` leaves them where they are.  On the typed side `R-Struct`
-- with `∥-comm` on both ends recovers the same layout, so the exact
-- match survives -- thread order is NOT a failure mode.

Pc2 : 𝐓.Proc 0
Pc2 =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.K 𝐓Tm.`recv 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫
      𝐓.∥ 𝐓.⟪ 𝐓Tm.K 𝐓Tm.`send 𝐓Tm.·¹ (payload 𝐓Tm.⊗ (𝐓Tm.` 0F)) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cc2 : 𝐒.Config 1 3
Cc2 = 𝑪 Pc2

Cc2′ : 𝐒.Config 1 3
Cc2′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ((𝐒Tm.ƛ 𝐒Tm.*) ∷ 𝐒Tm.* ∷ 𝐒Tm.* ∷ [])

-- The sender is now thread 1, the receiver thread 0.
step-com-swapped : Cc2 𝐑.─→ₚ Cc2′
step-com-swapped =
  𝐑.RUS-Com 1F 0F 0F 0F 1F [] []
    (λ ()) 𝐑.left-right refl 𝐒Red.V-λ refl refl

Pc2′ : 𝐓.Proc 0
Pc2′ =
  𝐓.ν (0 ∷ []) (0 ∷ [])
    ((𝐓.⟪ 𝐓Tm.ƛ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫) 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-com-swapped : Pc2 𝐓𝐑.─→ₚ Pc2′
red-com-swapped =
  𝐓𝐑.R-Struct
    (𝐓.ν-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl))
    (𝐓𝐑.R-Com {e = 𝐓Tm.ƛ 𝐓Tm.*} {E₁ = []} {E₂ = []} 𝐓E.V-λ)
    (𝐓.ν-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl))

com-swapped-exact-flatten : 𝑪 Pc2′ ≡ Cc2′
com-swapped-exact-flatten = refl

------------------------------------------------------------------------
-- 3. Choice.

Pch : 𝐓.Proc 0
Pch =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.K (𝐓Tm.`select 𝐓Tm.L) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫
      𝐓.∥ 𝐓.⟪ 𝐓Tm.K 𝐓Tm.`branch 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cch : 𝐒.Config 1 3
Cch = 𝑪 Pch

Cch≡ :
  Cch ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`select 𝐓Tm.L) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      (𝐒Tm.K 𝐒Tm.`branch 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Cch≡ = refl

Cch′ : 𝐒.Config 1 3
Cch′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷
      𝐒Tm.`inj 𝐓Tm.L 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ] ∷
      𝐒Tm.* ∷
      [])

step-choice : Cch 𝐑.─→ₚ Cch′
step-choice =
  𝐑.RUS-Choice 0F 1F 0F 0F 1F [] [] 𝐓Tm.L
    (λ ()) 𝐑.left-right refl refl refl

Pch′ : 𝐓.Proc 0
Pch′ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.` 0F ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.`inj 𝐓Tm.L (𝐓Tm.` 1F) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-choice : Pch 𝐓𝐑.─→ₚ Pch′
red-choice = 𝐓𝐑.R-Choice [] [] 𝐓Tm.L

choice-exact-flatten : 𝑪 Pch′ ≡ Cch′
choice-exact-flatten = refl

------------------------------------------------------------------------
-- 4. Choice with the partners in the swapped order.

Pch2 : 𝐓.Proc 0
Pch2 =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.K 𝐓Tm.`branch 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫
      𝐓.∥ 𝐓.⟪ 𝐓Tm.K (𝐓Tm.`select 𝐓Tm.R) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cch2 : 𝐒.Config 1 3
Cch2 = 𝑪 Pch2

Cch2′ : 𝐒.Config 1 3
Cch2′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( 𝐒Tm.`inj 𝐓Tm.R 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ] ∷
      𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷
      𝐒Tm.* ∷
      [])

step-choice-swapped : Cch2 𝐑.─→ₚ Cch2′
step-choice-swapped =
  𝐑.RUS-Choice 1F 0F 0F 0F 1F [] [] 𝐓Tm.R
    (λ ()) 𝐑.left-right refl refl refl

Pch2′ : 𝐓.Proc 0
Pch2′ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    ((𝐓.⟪ 𝐓Tm.`inj 𝐓Tm.R (𝐓Tm.` 1F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.` 0F ⟫)
     𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-choice-swapped : Pch2 𝐓𝐑.─→ₚ Pch2′
red-choice-swapped =
  𝐓𝐑.R-Struct
    (𝐓.ν-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl))
    (𝐓𝐑.R-Choice [] [] 𝐓Tm.R)
    (𝐓.ν-cong (𝐓.∥-cong 𝐓.∥-comm ≋-refl))

choice-swapped-exact-flatten : 𝑪 Pch2′ ≡ Cch2′
choice-swapped-exact-flatten = refl

------------------------------------------------------------------------
-- 5. Close: F1.

Pcl : 𝐓.Proc 0
Pcl =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ‼) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫
     𝐓.∥ 𝐓.⟪ 𝐓Tm.K (𝐓Tm.`end ⁇) 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫)

Ccl : 𝐒.Config 1 2
Ccl = 𝑪 Pcl

Ccl≡ :
  Ccl ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`end ‼) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      (𝐒Tm.K (𝐒Tm.`end ⁇) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 1F × 𝐒Tm.* ]) ∷
      [])
Ccl≡ = refl

-- The closed channel survives in the soup as a dead cell.
Ccl′ : 𝐒.Config 1 2
Ccl′ = 𝐒.config ((false , [] , []) ∷ []) (𝐒Tm.* ∷ 𝐒Tm.* ∷ [])

step-close : Ccl 𝐑.─→ₚ Ccl′
step-close =
  𝐑.RUS-Close 0F 1F 0F 0F 1F [] []
    (λ ()) 𝐑.left-right refl refl refl

Pcl′ : 𝐓.Proc 0
Pcl′ = 𝐓.⟪ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫

red-close : Pcl 𝐓𝐑.─→ₚ Pcl′
red-close = 𝐓𝐑.R-Close {E₁ = []} {E₂ = []}

-- F1: `𝑪 Pcl′ ≡ Ccl′` is not even well typed -- the channel counts differ.
-- Stated on the ℕ component of `U[_]`:
close-exact-flatten-fails : proj₁ 𝐔.U[ Pcl′ ] ≢ 1
close-exact-flatten-fails ()

close-channel-count : proj₁ 𝐔.U[ Pcl′ ] ≡ 0
close-channel-count = refl

-- What holds instead: the image relation, with the dead channel garbage.
close-channels : Vec (OrientedChannel 1) 0
close-channels = []

close-inj :
  ∀ {i j : 𝔽 0} →
  physicalChannel (lookup close-channels i) ≡
  physicalChannel (lookup close-channels j) →
  i ≡ j
close-inj {()}

close-image-holds : GlobalImage Pcl′ Ccl′
close-image-holds = record
  { logicalChannels = close-channels
  ; localImage = record
      { channelEmbedding-injective = close-inj
      ; threadEmbedding = just
      ; threadEmbedding-injective = λ { refl refl → refl }
      ; channel-not-ambient = λ ()
      ; thread-not-ambient = λ _ ()
      ; live-channel = λ ()
      ; live-thread = λ { 0F → present 0F refl refl
                        ; 1F → present 1F refl refl }
      ; garbage-channel = λ { 0F _ _ → refl }
      ; garbage-thread = λ j outside _ → ⊥-elim (outside j refl)
      }
  }
