-- | Completeness of the normal form: `~` is a `≋`.
--
--   The converse of Normal.Sound, and the direction that makes `~` USABLE
--   downstream: a normal-form manipulation can be pushed back into the calculus.
--
--   Every generator of `~₁` is one ≋′ generator applied under the prefix
--   telescope it carries — which is exactly why Normal.Equiv's generators were
--   given that prefix.  The transpositions rename the body by an ENDOmorphism,
--   so `plug-⋯ₚ-endo` relates them to `liftId` with no scope transport, unlike
--   Normal.Rename's `plug-⋯ₚ`.
module BorrowedCF.Simulation.Support.Normal.Complete where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; plug-⋯ₚ)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Prenex using (≡→≋; ≋-sym; plug-cong)
open import BorrowedCF.Simulation.Support.Normal.Flat using (pars-↭)

open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Plugging under a scope ENDOmorphism.
------------------------------------------------------------------------

-- The shape every transposition case has: a ≋′ generator whose right-hand side
-- renames the body — which under linked-φ RENAMES the telescope's channels
-- (`renTel t ξ`), exactly as the ~-generator's RHS records.
transp : ∀ {n k} (t : Tel n k) (ξ : n →ᵣ n) (es : List (Tm k)) →
         plug t (pars es) ⋯ₚ ξ ≡ plug (renTel t ξ) (pars (map (_⋯ liftRen t ξ) es))
transp t ξ es =
  plug-⋯ₚ t ξ (pars es) ■ cong (plug (renTel t ξ)) (pars-⋯ₚ es (liftRen t ξ))

------------------------------------------------------------------------
-- Completeness.
------------------------------------------------------------------------

~₁⇒≋ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉

~₁⇒≋ (perm-ν1 s t es) =
  ≡→≋ (plug-++ᵗ s (tν t) (pars es))
    ◅◅ plug-cong s ν-cong-swap
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tν (renTel t (swapᵣ 1 1)))
                   (pars (map (_⋯ liftRen t (swapᵣ 1 1)) es))))
  where
    ν-cong-swap : ν (plug t (pars es))
                    ≋ ν (plug (renTel t (swapᵣ 1 1)) (pars (map (_⋯ liftRen t (swapᵣ 1 1)) es)))
    ν-cong-swap = Eq*.return ν-swap′ ◅◅ ≡→≋ (cong ν (transp t (swapᵣ 1 1) es))

~₁⇒≋ (perm-νν s t es) =
  ≡→≋ (plug-++ᵗ s (tν (tν t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tν (tν (renTel t (assocSwapᵣ 2 2))))
                   (pars (map (_⋯ liftRen t (assocSwapᵣ 2 2)) es))))
  where
    step : ν (ν (plug t (pars es)))
             ≋ ν (ν (plug (renTel t (assocSwapᵣ 2 2)) (pars (map (_⋯ liftRen t (assocSwapᵣ 2 2)) es))))
    step = Eq*.return ν-comm′ ◅◅ ≡→≋ (cong (λ z → ν (ν z)) (transp t (assocSwapᵣ 2 2) es))

~₁⇒≋ (perm-φφ s x y c d t es) =
  ≡→≋ (plug-++ᵗ s (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t (assocSwapᵣ 1 1))))
                   (pars (map (_⋯ liftRen t (assocSwapᵣ 1 1)) es))))
  where
    step : φ x c (φ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (plug t (pars es)))
             ≋ φ y d (φ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                        (plug (renTel t (assocSwapᵣ 1 1)) (pars (map (_⋯ liftRen t (assocSwapᵣ 1 1)) es))))
    step = Eq*.return φ-comm′
             ◅◅ ≡→≋ (cong (λ z → φ y d (φ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) z)) (transp t (assocSwapᵣ 1 1) es))

~₁⇒≋ (perm-νφ s x c t es) =
  ≡→≋ (plug-++ᵗ s (tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tφ x c (tν (renTel t (assocSwapᵣ 1 2))))
                   (pars (map (_⋯ liftRen t (assocSwapᵣ 1 2)) es))))
  where
    step : ν (φ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) (plug t (pars es)))
             ≋ φ x c (ν (plug (renTel t (assocSwapᵣ 1 2)) (pars (map (_⋯ liftRen t (assocSwapᵣ 1 2)) es))))
    step = Eq*.return νφ-comm′
             ◅◅ ≡→≋ (cong (λ z → φ x c (ν z)) (transp t (assocSwapᵣ 1 2) es))

~₁⇒≋ (perm-thr t p)  = plug-cong t (pars-↭ p)
~₁⇒≋ (unit-del t es) = plug-cong t (Eq*.return ∥-unit′)

~⇒≋ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉
~⇒≋ ε           = ε
~⇒≋ (fwd g ◅ c) = ~₁⇒≋ g          ◅◅ ~⇒≋ c
~⇒≋ (bwd g ◅ c) = ≋-sym (~₁⇒≋ g) ◅◅ ~⇒≋ c
