-- Backward simulation, the two split rules `RUS-LSplit` and `RUS-RSplit`
-- (failure mode F3 of PLAN.md §2).
--
-- Findings:
--   * LSplit: the naive proposition HOLDS.  The rule touches no flags and
--     no phi slots, so there is nothing for the soup to guess.
--   * RSplit at the canonical position `k` (the number of binder groups
--     that precede the split one on that endpoint): the naive proposition
--     HOLDS -- both for a head group (k = 0) and for an interior group
--     (k = 1).
--   * RSplit at a non-canonical `k`: the naive proposition FAILS (F3).
--     The soup side condition `endpointFlags … ≡ before ++ after` admits
--     every splitting of the flag list, and the resulting configuration
--     is not the flattening of the typed reduct: the CHANNELS agree (the
--     new `drop` lands in the same multiset) but the threads disagree in
--     the phi slots.  The two configurations differ only by WHICH slot is
--     the freshly inserted boundary, which `consumePhi` makes precise.
module BorrowedCF.Simulation.BackwardSoup.Examples.Splits where

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (skip)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as 𝐔
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.Typed as 𝐓𝐑
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑
import BorrowedCF.Terms.Base as 𝐓Tm
import BorrowedCF.Terms.BaseSoup as 𝐒Tm

open import BorrowedCF.Simulation.BackwardSoup.Examples.Base

------------------------------------------------------------------------
-- 1. LSplit.
--
-- ν ⟨s ; s′⟩ ⟨…⟩ ( ⟪ lsplit x₀ ⟫ ∥ ⟪ () ⟫ )

Pl : 𝐓.Proc 0
Pl =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`lsplit skip) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cl : 𝐒.Config 1 2
Cl = 𝑪 Pl

Cl≡ :
  Cl ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`lsplit skip) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Cl≡ = refl

Cl′ : 𝐒.Config 1 2
Cl′ =
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ] 𝐒Tm.⊗ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])

step-lsplit : Cl 𝐑.─→ₚ Cl′
step-lsplit = 𝐑.RUS-LSplit 0F 0F 0F [] refl refl

-- The typed rule widens the split group from 1 to 2 handles.
Pl′ : 𝐓.Proc 0
Pl′ =
  𝐓.ν (2 ∷ []) (1 ∷ [])
    (𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-lsplit : Pl 𝐓𝐑.─→ₚ Pl′
red-lsplit =
  𝐓𝐑.R-LSplit {B₁ = []} {B₂ = []} {B = 1 ∷ []} {q = 0} {b₁ = 0} {E = []}

lsplit-exact-flatten : 𝑪 Pl′ ≡ Cl′
lsplit-exact-flatten = refl

------------------------------------------------------------------------
-- 2. RSplit on a head group: the canonical `k` is 0, and it is the only
--    one available (the endpoint carries no flags yet).

Pr : 𝐓.Proc 0
Pr =
  𝐓.ν (1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`rsplit skip) 𝐓Tm.·¹ (𝐓Tm.` 0F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Cr : 𝐒.Config 1 2
Cr = 𝑪 Pr

Cr≡ :
  Cr ≡
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`rsplit skip) 𝐒Tm.·¹ 𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Cr≡ = refl

Cr′ : 𝐒.Config 1 2
Cr′ =
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.`phi (0F , 0) ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])

step-rsplit : Cr 𝐑.─→ₚ Cr′
step-rsplit = 𝐑.RUS-RSplit 0F 0F 0F [] [] [] refl refl refl

-- The typed rule splits the group `1` into `1 ∷ 1`, i.e. it introduces a
-- new sync boundary; the translation turns that boundary into `drop`.
Pr′ : 𝐓.Proc 0
Pr′ =
  𝐓.ν (1 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ (𝐓Tm.` 0F) 𝐓Tm.⊗ (𝐓Tm.` 1F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-rsplit : Pr 𝐓𝐑.─→ₚ Pr′
red-rsplit =
  𝐓𝐑.R-RSplit {B₁ = []} {B₂ = []} {B = 1 ∷ []} {q = 0} {b₁ = 0} {E = []}

rsplit-head-exact-flatten : 𝑪 Pr′ ≡ Cr′
rsplit-head-exact-flatten = refl

------------------------------------------------------------------------
-- 3. RSplit on an INTERIOR group.  The left endpoint already owns one
--    boundary (`drop`), so the soup has two admissible `before`/`after`
--    splittings: k = 1 (canonical) and k = 0 (wrong).

Prs : 𝐓.Proc 0
Prs =
  𝐓.ν (1 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ 𝐓Tm.K (𝐓Tm.`rsplit skip) 𝐓Tm.·¹ (𝐓Tm.` 1F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

Crs : 𝐒.Config 1 2
Crs = 𝑪 Prs

Crs≡ :
  Crs ≡
  𝐒.config
    ((true , 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝐒Tm.K (𝐒Tm.`rsplit skip) 𝐒Tm.·¹
        𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])
Crs≡ = refl

-- 3a. The canonical splitting: `before = drop ∷ []`, so k = 1.
Crs′ : 𝐒.Config 1 2
Crs′ =
  𝐒.config
    ((true , 𝐒.drop ∷ 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.`phi (0F , 1) ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (0F , 1) × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])

step-rsplit-canonical : Crs 𝐑.─→ₚ Crs′
step-rsplit-canonical =
  𝐑.RUS-RSplit 0F 0F 0F [] (𝐒.drop ∷ []) [] refl refl refl

Prs′ : 𝐓.Proc 0
Prs′ =
  𝐓.ν (1 ∷ 1 ∷ 1 ∷ []) (1 ∷ [])
    (𝐓.⟪ (𝐓Tm.` 1F) 𝐓Tm.⊗ (𝐓Tm.` 2F) ⟫ 𝐓.∥ 𝐓.⟪ 𝐓Tm.* ⟫)

red-rsplit-interior : Prs 𝐓𝐑.─→ₚ Prs′
red-rsplit-interior =
  𝐓𝐑.R-RSplit {B₁ = 1 ∷ []} {B₂ = []} {B = 1 ∷ []} {q = 0} {b₁ = 0} {E = []}

rsplit-interior-exact-flatten : 𝑪 Prs′ ≡ Crs′
rsplit-interior-exact-flatten = refl

-- 3b. F3 probe: the non-canonical splitting `before = []`, `after = drop ∷ []`,
--     i.e. k = 0.  The side condition is satisfied, so the soup step exists.
Crs″ : 𝐒.Config 1 2
Crs″ =
  𝐒.config
    ((true , 𝐒.drop ∷ 𝐒.drop ∷ [] , []) ∷ [])
    ( (𝓒[ 𝐒Tm.`phi (0F , 1) × 0F × 𝐒Tm.`phi (0F , 0) ] 𝐒Tm.⊗
       𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ]) ∷
      𝐒Tm.* ∷
      [])

step-rsplit-wrong-k : Crs 𝐑.─→ₚ Crs″
step-rsplit-wrong-k =
  𝐑.RUS-RSplit 0F 0F 0F [] [] (𝐒.drop ∷ []) refl refl refl

-- The channel components agree ...
rsplit-wrong-k-channels-agree :
  𝐒.channels Crs″ ≡ 𝐒.channels Crs′
rsplit-wrong-k-channels-agree = refl

-- ... but the thread components do not, so the naive proposition fails.
rsplit-wrong-k-exact-flatten-fails : ¬ (𝑪 Prs′ ≡ Crs″)
rsplit-wrong-k-exact-flatten-fails ()

-- No typed reduct of `Prs` flattens to `Crs″` either: the handle
-- `𝓒[ phi (0F , 1) × 0F × phi (0F , 0) ]` occurring in it is not in the
-- image of `UB[_]` for ANY binder group, because `UBFrom` hands out slot
-- numbers in increasing order along the group list.
--
-- What the two configurations DO share: they differ only in which slot
-- carries the freshly inserted boundary.  Deleting that slot from each
-- (slot 1 from the canonical result, slot 0 from the wrong-k result)
-- yields the very same configuration.
rsplit-wrong-k-is-a-slot-renumbering :
  V.map (𝐑.consumePhi 0F 1) (𝐒.threads (𝑪 Prs′)) ≡
  V.map (𝐑.consumePhi 0F 0) (𝐒.threads Crs″)
rsplit-wrong-k-is-a-slot-renumbering = refl

-- Concretely, both collapse to the pre-split handle plus a dead cell.
rsplit-wrong-k-common-residual :
  V.map (𝐑.consumePhi 0F 0) (𝐒.threads Crs″) ≡
  ( (𝓒[ 𝐒Tm.`phi (0F , 0) × 0F × 𝐒Tm.* ] 𝐒Tm.⊗
     𝓒[ 𝐒Tm.* × 0F × 𝐒Tm.* ]) ∷
    𝐒Tm.* ∷
    [])
rsplit-wrong-k-common-residual = refl
