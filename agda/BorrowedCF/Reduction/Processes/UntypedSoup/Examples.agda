module BorrowedCF.Reduction.Processes.UntypedSoup.Examples where

open import BorrowedCF.Prelude
open import BorrowedCF.Types using (Pol; ‼; ⁇; skip)
open import BorrowedCF.Terms.BaseSoup
open import BorrowedCF.Reduction.ExpressionsSoup using (Value; V-K)
import BorrowedCF.Processes.UntypedSoup as 𝐒
import BorrowedCF.Reduction.Processes.UntypedSoup as 𝐑

open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

fork-inserts-child-next :
  𝐒.config
    []
    ( * ∷
      (K `fork ·¹ *) ∷
      K `discard ∷
      K `branch ∷
      []
    )
  𝐑.─→ₚ
  𝐒.config
    []
    ( * ∷
      * ∷
      (* ·¹ *) ∷
      K `discard ∷
      K `branch ∷
      []
    )
fork-inserts-child-next = 𝐑.RUS-Fork 1F [] V-K refl

new-prepends-channel-and-weakens-endpoints :
  𝐒.config
    ((true , 𝐒.drop ∷ [] , 𝐒.acq ∷ []) ∷ [])
    ( ((` 0F) ⊗ `phi (1F , 0)) ∷
      (K (`new skip) ·¹ *) ∷
      []
    )
  𝐑.─→ₚ
  𝐒.config
    ( (true , 𝐒.acq ∷ [] , 𝐒.acq ∷ []) ∷
      (true , 𝐒.drop ∷ [] , 𝐒.acq ∷ []) ∷
      []
    )
    ( ((` 2F) ⊗ `phi (3F , 0)) ∷
      (𝓒[ `phi (0F , 0) × 0F × * ] ⊗
       𝓒[ `phi (1F , 0) × 1F × * ]) ∷
      []
    )
new-prepends-channel-and-weakens-endpoints =
  𝐑.RUS-New 1F 0F []
    refl

-- The new boundary goes to position `L.length before`.  Taking all existing
-- flags as `before` reproduces the old append-at-the-end behaviour.
rsplit-appends-drop-and-uses-old-slot :
  𝐒.config
    ((true , [] , 𝐒.acq ∷ 𝐒.drop ∷ []) ∷ [])
    ((K (`rsplit skip) ·¹ 𝓒[ * × 1F × * ]) ∷ [])
  𝐑.─→ₚ
  𝐒.config
    ((true , [] , 𝐒.acq ∷ 𝐒.drop ∷ 𝐒.drop ∷ []) ∷ [])
    ((𝓒[ * × 1F × `phi (1F , 2) ] ⊗
      𝓒[ `phi (1F , 2) × 1F × * ]) ∷ [])
rsplit-appends-drop-and-uses-old-slot =
  𝐑.RUS-RSplit 0F 0F 1F [] (𝐒.acq ∷ 𝐒.drop ∷ []) []
    refl
    refl
    refl

-- An interior split: the new boundary takes slot `1`, so the sibling
-- thread's reference to slot `1` is renumbered to slot `2` by `insertPhi`
-- while its reference to slot `0` stays put.
rsplit-interior-renumbers-later-slots :
  𝐒.config
    ((true , [] , 𝐒.acq ∷ 𝐒.drop ∷ []) ∷ [])
    ( (K (`rsplit skip) ·¹ 𝓒[ * × 1F × `phi (1F , 1) ]) ∷
      𝓒[ `phi (1F , 0) × 1F × `phi (1F , 1) ] ∷
      []
    )
  𝐑.─→ₚ
  𝐒.config
    ((true , [] , 𝐒.acq ∷ 𝐒.drop ∷ 𝐒.drop ∷ []) ∷ [])
    ( (𝓒[ * × 1F × `phi (1F , 1) ] ⊗
       𝓒[ `phi (1F , 1) × 1F × `phi (1F , 2) ]) ∷
      𝓒[ `phi (1F , 0) × 1F × `phi (1F , 2) ] ∷
      []
    )
rsplit-interior-renumbers-later-slots =
  𝐑.RUS-RSplit 0F 0F 1F [] (𝐒.acq ∷ []) (𝐒.drop ∷ [])
    refl
    refl
    refl

close-uses-distinct-threads-and-opposite-ends :
  𝐒.config
    ((true , [] , []) ∷ [])
    ( (K (`end ‼) ·¹ 𝓒[ * × 0F × * ]) ∷
      K `discard ∷
      (K (`end ⁇) ·¹ 𝓒[ * × 1F × * ]) ∷
      []
    )
  𝐑.─→ₚ
  𝐒.config
    ((false , [] , []) ∷ [])
    (* ∷ K `discard ∷ * ∷ [])
close-uses-distinct-threads-and-opposite-ends =
  𝐑.RUS-Close 0F 2F 0F 0F 1F [] []
    (λ ())
    𝐑.left-right
    refl
    refl
    refl
