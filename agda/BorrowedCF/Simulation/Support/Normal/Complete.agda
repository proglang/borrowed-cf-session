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

plug-⋯ₚ-endo : ∀ {n k} (t : Tel n k) (ξ : n →ᵣ n) (X : Proc k) →
               plug t X ⋯ₚ ξ ≡ plug t (X ⋯ₚ liftId t ξ)
plug-⋯ₚ-endo []       ξ X = refl
plug-⋯ₚ-endo (tν t)   ξ X = cong ν     (plug-⋯ₚ-endo t (ξ ↑* 2) X)
plug-⋯ₚ-endo (tφ f t) ξ X = cong (φ f) (plug-⋯ₚ-endo t (ξ ↑)   X)

-- The shape every transposition case has: a ≋′ generator whose right-hand side
-- renames the body, re-expressed on the thread list.
transp : ∀ {n k} (t : Tel n k) (ξ : n →ᵣ n) (es : List (Tm k)) →
         plug t (pars es) ⋯ₚ ξ ≡ plug t (pars (map (_⋯ liftId t ξ) es))
transp t ξ es =
  plug-⋯ₚ-endo t ξ (pars es) ■ cong (plug t) (pars-⋯ₚ es (liftId t ξ))

------------------------------------------------------------------------
-- Completeness.
------------------------------------------------------------------------

~₁⇒≋ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉

~₁⇒≋ (perm-ν1 s t es) =
  ≡→≋ (plug-++ᵗ s (tν t) (pars es))
    ◅◅ plug-cong s (ν-cong-swap)
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tν t) (pars (map (_⋯ liftId t (swapᵣ 1 1)) es))))
  where
    ν-cong-swap : ν (plug t (pars es))
                    ≋ ν (plug t (pars (map (_⋯ liftId t (swapᵣ 1 1)) es)))
    ν-cong-swap = Eq*.return ν-swap′ ◅◅ ≡→≋ (cong ν (transp t (swapᵣ 1 1) es))

~₁⇒≋ (perm-νν s t es) =
  ≡→≋ (plug-++ᵗ s (tν (tν t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tν (tν t)) (pars (map (_⋯ liftId t (assocSwapᵣ 2 2)) es))))
  where
    step : ν (ν (plug t (pars es)))
             ≋ ν (ν (plug t (pars (map (_⋯ liftId t (assocSwapᵣ 2 2)) es))))
    step = Eq*.return ν-comm′ ◅◅ ≡→≋ (cong (λ z → ν (ν z)) (transp t (assocSwapᵣ 2 2) es))

~₁⇒≋ (perm-φφ s x y t es) =
  ≡→≋ (plug-++ᵗ s (tφ x (tφ y t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tφ y (tφ x t))
                   (pars (map (_⋯ liftId t (assocSwapᵣ 1 1)) es))))
  where
    step : φ x (φ y (plug t (pars es)))
             ≋ φ y (φ x (plug t (pars (map (_⋯ liftId t (assocSwapᵣ 1 1)) es))))
    step = Eq*.return φ-comm′
             ◅◅ ≡→≋ (cong (λ z → φ y (φ x z)) (transp t (assocSwapᵣ 1 1) es))

~₁⇒≋ (perm-νφ s x t es) =
  ≡→≋ (plug-++ᵗ s (tν (tφ x t)) (pars es))
    ◅◅ plug-cong s step
    ◅◅ ≡→≋ (sym (plug-++ᵗ s (tφ x (tν t))
                   (pars (map (_⋯ liftId t (assocSwapᵣ 1 2)) es))))
  where
    step : ν (φ x (plug t (pars es)))
             ≋ φ x (ν (plug t (pars (map (_⋯ liftId t (assocSwapᵣ 1 2)) es))))
    step = Eq*.return νφ-comm′
             ◅◅ ≡→≋ (cong (λ z → φ x (ν z)) (transp t (assocSwapᵣ 1 2) es))

~₁⇒≋ (perm-thr t p)  = plug-cong t (pars-↭ p)
~₁⇒≋ (unit-del t es) = plug-cong t (Eq*.return ∥-unit′)

~⇒≋ : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉
~⇒≋ ε           = ε
~⇒≋ (fwd g ◅ c) = ~₁⇒≋ g          ◅◅ ~⇒≋ c
~⇒≋ (bwd g ◅ c) = ≋-sym (~₁⇒≋ g) ◅◅ ~⇒≋ c
