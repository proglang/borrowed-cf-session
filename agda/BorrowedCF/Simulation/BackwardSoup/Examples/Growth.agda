-- Backward simulation, the two rules that GROW the soup: `RUS-Fork` and
-- `RUS-New` (failure mode F2 of PLAN.md §2).
--
-- Findings:
--   * Fork: the naive proposition HOLDS.  `insertAfter` puts the child
--     immediately behind the parent, which is exactly where `flatten`
--     of `⟪ E [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫` puts it.
--   * New at the canonical index (the position the `ν` nesting dictates,
--     i.e. behind all channels already owned by the enclosing binders):
--     the naive proposition HOLDS.
--   * New at any other index: the naive proposition FAILS -- the channel
--     vectors are permutations of one another -- but `GlobalImage P′ C′`
--     holds, with the permutation absorbed by `logicalChannels`.  This is
--     F2, and no `≋`-rearrangement of `P′` is needed.
module BorrowedCF.Simulation.BackwardSoup.Examples.Growth where

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (skip)

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
-- 1. Fork.

-- ⟪ fork (λx. unit) ⟫
Pf : 𝐓.Proc 0
Pf = 𝐓.⟪ 𝐓Tm.K 𝐓Tm.`fork 𝐓Tm.·¹ (𝐓Tm.ƛ 𝐓Tm.*) ⟫

Cf : 𝐒.Config 0 1
Cf = 𝑪 Pf

Cf≡ :
  Cf ≡
  𝐒.config [] ((𝐒Tm.K 𝐒Tm.`fork 𝐒Tm.·¹ (𝐒Tm.ƛ 𝐒Tm.*)) ∷ [])
Cf≡ = refl

Cf′ : 𝐒.Config 0 2
Cf′ = 𝐒.config [] (𝐒Tm.* ∷ ((𝐒Tm.ƛ 𝐒Tm.*) 𝐒Tm.·¹ 𝐒Tm.*) ∷ [])

step-fork : Cf 𝐑.─→ₚ Cf′
step-fork = 𝐑.RUS-Fork 0F [] 𝐒Red.V-λ refl

Pf′ : 𝐓.Proc 0
Pf′ = 𝐓.⟪ 𝐓Tm.* ⟫ 𝐓.∥ 𝐓.⟪ (𝐓Tm.ƛ 𝐓Tm.*) 𝐓Tm.·¹ 𝐓Tm.* ⟫

red-fork : Pf 𝐓𝐑.─→ₚ Pf′
red-fork = 𝐓𝐑.R-Fork [] 𝐓E.V-λ

fork-exact-flatten : 𝑪 Pf′ ≡ Cf′
fork-exact-flatten = refl

------------------------------------------------------------------------
-- 2. New, no other channel around: the index is forced, match is exact.

Pn : 𝐓.Proc 0
Pn = 𝐓.⟪ 𝐓Tm.K (𝐓Tm.`new skip) 𝐓Tm.·¹ 𝐓Tm.* ⟫

Cn : 𝐒.Config 0 1
Cn = 𝑪 Pn

Cn≡ : Cn ≡ 𝐒.config [] ((𝐒Tm.K (𝐒Tm.`new skip) 𝐒Tm.·¹ 𝐒Tm.*) ∷ [])
Cn≡ = refl

Cn′ : 𝐒.Config 1 1
Cn′ =
  𝐒.config
    ((true , 𝐒.acq ∷ [] , 𝐒.acq ∷ []) ∷ [])
    ((𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ] 𝐒Tm.⊗
      𝓒[ 𝐒Tm.`phi (1F , 0) × 1F × 𝐒Tm.* ]) ∷ [])

step-new : Cn 𝐑.─→ₚ Cn′
step-new = 𝐑.RUS-New 0F 0F [] refl

Pn′ : 𝐓.Proc 0
Pn′ =
  𝐓.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
    𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫

red-new : Pn 𝐓𝐑.─→ₚ Pn′
red-new = 𝐓𝐑.R-New []

new-exact-flatten : 𝑪 Pn′ ≡ Cn′
new-exact-flatten = refl

------------------------------------------------------------------------
-- 3. New with one channel already present.
--
-- P = ν ⟨s⟩ ⟨s̄⟩ ( ⟪ x₀ ⟫ ∥ ⟪ new skip () ⟫ )

Pn2 : 𝐓.Proc 0
Pn2 =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.` 0F ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.K (𝐓Tm.`new skip) 𝐓Tm.·¹ 𝐓Tm.* ⟫)

Cn2 : 𝐒.Config 1 2
Cn2 = 𝑪 Pn2

Cn2≡ :
  Cn2 ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷
      (𝐒Tm.K (𝐒Tm.`new skip) 𝐒Tm.·¹ 𝐒Tm.*) ∷
      [])
Cn2≡ = refl

-- The typed reduct: `R-New` puts the new `ν` where the redex was, i.e.
-- INSIDE the existing binder and to the right of the surviving thread.
Pn2′ : 𝐓.Proc 0
Pn2′ =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.` 0F ⟫ 𝐓.∥
     𝐓.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
       𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫)

red-new2 : Pn2 𝐓𝐑.─→ₚ Pn2′
red-new2 =
  𝐓𝐑.R-Bind
    (𝐓𝐑.R-Struct 𝐓.∥-comm (𝐓𝐑.R-Par (𝐓𝐑.R-New [])) 𝐓.∥-comm)

Cn2′-flat : 𝐒.Config 2 2
Cn2′-flat = 𝑪 Pn2′

Cn2′-flat≡ :
  Cn2′-flat ≡
  𝐒.config
    ((true , [] , []) ∷ (true , 𝐒.acq ∷ [] , 𝐒.acq ∷ []) ∷ [])
    ( 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷
      (𝓒[ 𝐒Tm.`phi (2F , 0) × 2F × 𝐒Tm.* ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (3F , 0) × 3F × 𝐒Tm.* ]) ∷
      [])
Cn2′-flat≡ = refl

-- 3a. The soup may append the channel: this index IS the canonical one and
--     the naive proposition holds on the nose.
Cn2′ : 𝐒.Config 2 2
Cn2′ =
  𝐒.config
    ((true , [] , []) ∷ (true , 𝐒.acq ∷ [] , 𝐒.acq ∷ []) ∷ [])
    ( 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] ∷
      (𝓒[ 𝐒Tm.`phi (2F , 0) × 2F × 𝐒Tm.* ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (3F , 0) × 3F × 𝐒Tm.* ]) ∷
      [])

step-new-canonical : Cn2 𝐑.─→ₚ Cn2′
step-new-canonical = 𝐑.RUS-New 1F 1F [] refl

new-canonical-exact-flatten : 𝑪 Pn2′ ≡ Cn2′
new-canonical-exact-flatten = refl

-- 3b. F2 probe: the soup may instead PREPEND the channel (index 0F).
Cn2″ : 𝐒.Config 2 2
Cn2″ =
  𝐒.config
    ((true , 𝐒.acq ∷ [] , 𝐒.acq ∷ []) ∷ (true , [] , []) ∷ [])
    ( 𝓒[ 𝐒Tm.* × 2F × 𝐒Tm.* ] ∷
      (𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (1F , 0) × 1F × 𝐒Tm.* ]) ∷
      [])

step-new-front : Cn2 𝐑.─→ₚ Cn2″
step-new-front = 𝐑.RUS-New 1F 0F [] refl

-- The exact-flattening claim fails: the two channel vectors differ.
new-front-exact-flatten-fails : ¬ (𝑪 Pn2′ ≡ Cn2″)
new-front-exact-flatten-fails ()

-- What holds instead (F2): the image relation of the forward proof, with
-- the permutation absorbed by `logicalChannels`.
--
-- logical channel 0 (the `ν` of `P`)         lives at physical channel 1
-- logical channel 1 (the freshly created one) lives at physical channel 0
front-channels : Vec (OrientedChannel 2) 2
front-channels = (1F , forward) ∷ (0F , forward) ∷ []

front-injective :
  ∀ {i j : 𝔽 2} →
  physicalChannel (lookup front-channels i) ≡
  physicalChannel (lookup front-channels j) →
  i ≡ j
front-injective {0F} {0F} _ = refl
front-injective {0F} {1F} ()
front-injective {1F} {0F} ()
front-injective {1F} {1F} _ = refl

front-garbage-channel :
  (i : 𝔽 2) →
  LocalOutside (physicalChannel ∘ lookup front-channels) i →
  ¬ ⊥ →
  lookup (𝐒.channels Cn2″) i ≡ (false , [] , [])
front-garbage-channel 0F outside _ = ⊥-elim (outside 1F refl)
front-garbage-channel 1F outside _ = ⊥-elim (outside 0F refl)

new-front-image : GlobalImage Pn2′ Cn2″
new-front-image = record
  { logicalChannels = front-channels
  ; localImage = record
      { channelEmbedding-injective = front-injective
      ; threadEmbedding = just
      ; threadEmbedding-injective = λ { refl refl → refl }
      ; channel-not-ambient = λ _ ()
      ; thread-not-ambient = λ _ ()
      ; live-channel = λ { 0F → refl ; 1F → refl }
      ; live-thread = λ { 0F → present 0F refl refl
                        ; 1F → present 1F refl refl }
      ; garbage-channel = front-garbage-channel
      ; garbage-thread = λ j outside _ → ⊥-elim (outside j refl)
      }
  }
