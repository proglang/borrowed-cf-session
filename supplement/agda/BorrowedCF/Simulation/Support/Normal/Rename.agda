-- | Renaming a prenex normal form.
--
--   Needed by Normal.Complete: three of the twelve ≋′ generators (ν-swap′,
--   ν-comm′, φ-comm′, νφ-comm′) permute binders by RENAMING the body, so
--   relating the two sides' normal forms needs `prenex` to commute with
--   renaming.  The `Tel n k` indexing (Normal.Form) again keeps this
--   transport-free: a telescope's SHAPE is independent of its base scope, so
--   re-basing it at n′ is a plain structural recursion.
module BorrowedCF.Simulation.Support.Normal.Rename where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form

open import Data.List using (List; []; _∷_; map)

open Nat.Variables

------------------------------------------------------------------------
-- Re-basing a telescope.
------------------------------------------------------------------------

-- The inner scope the shape of `t` produces over a new base `n′`.
innerOf : ∀ {n k} → Tel n k → ℕ → ℕ
innerOf []         n′ = n′
innerOf (tν t)     n′ = innerOf t (2 + n′)
innerOf (tφ _ _ t) n′ = innerOf t (1 + n′)

-- Same shape, new base — the channels are RENAMED by ρ (linked-φ: a `tφ`
-- carries a term, so re-basing is no longer scope-only; it needs the renaming).
renTel : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) → Tel n′ (innerOf t n′)
renTel []         ρ = []
renTel (tν t)     ρ = tν   (renTel t (ρ ↑* 2))
renTel (tφ f c t) ρ = tφ f (c ⋯ ρ) (renTel t (ρ ↑))

-- A base renaming lifted under the whole telescope.
liftRen : ∀ {n k n′} (t : Tel n k) → n →ᵣ n′ → k →ᵣ innerOf t n′
liftRen []         ρ = ρ
liftRen (tν t)     ρ = liftRen t (ρ ↑* 2)
liftRen (tφ _ _ t) ρ = liftRen t (ρ ↑)

-- Renaming commutes with plugging.
plug-⋯ₚ : ∀ {n k n′} (t : Tel n k) (ρ : n →ᵣ n′) (X : Proc k) →
          plug t X ⋯ₚ ρ ≡ plug (renTel t ρ) (X ⋯ₚ liftRen t ρ)
plug-⋯ₚ []         ρ X = refl
plug-⋯ₚ (tν t)     ρ X = cong ν             (plug-⋯ₚ t (ρ ↑* 2) X)
plug-⋯ₚ (tφ f c t) ρ X = cong (φ f (c ⋯ ρ)) (plug-⋯ₚ t (ρ ↑)   X)

-- Re-basing at the same scope by the identity is the identity.
renTel-id : ∀ {n k} (t : Tel n k) → innerOf t n ≡ k
renTel-id []         = refl
renTel-id (tν t)     = renTel-id t
renTel-id (tφ _ _ t) = renTel-id t

------------------------------------------------------------------------
-- Renaming a normal form.
------------------------------------------------------------------------

renNF : ∀ {n} → NF n → (n′ : ℕ) → (n →ᵣ n′) → NF n′
renNF (mkNF t es) n′ ρ = mkNF (renTel t ρ) (map (_⋯ liftRen t ρ) es)

⌈⌉-⋯ₚ : ∀ {n n′} (N : NF n) (ρ : n →ᵣ n′) → ⌈ N ⌉ ⋯ₚ ρ ≡ ⌈ renNF N n′ ρ ⌉
⌈⌉-⋯ₚ (mkNF t es) ρ =
  plug-⋯ₚ t ρ (pars es) ■ cong (plug (renTel t ρ)) (pars-⋯ₚ es (liftRen t ρ))
