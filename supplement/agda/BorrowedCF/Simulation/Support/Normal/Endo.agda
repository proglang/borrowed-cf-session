-- | Re-basing a telescope at its OWN scope is the identity.
--
--   Normal.Equiv's four transposition generators use `liftId`, which keeps the
--   inner scope fixed; `nf` composed with `nf-nat` produces `renTel`/`liftRen`,
--   which re-base it.  On an ENDOmorphism the two agree, but only up to the
--   transport `renTel-id t : innerOf t n ≡ k`.  This module discharges that
--   transport once, for the telescope, the lifted renaming, and the weakening.
module BorrowedCF.Simulation.Support.Normal.Endo where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (subst-tν; subst-tφ; subst-wkTel; NF-≡; map-⋯-subst; nf-nat; renTel-cong)

open import Data.List using (List; map)

open Nat.Variables

------------------------------------------------------------------------
-- The empty telescope is a unit for concatenation.
------------------------------------------------------------------------

++ᵗ-idʳ : ∀ {n k} (t : Tel n k) → t ++ᵗ [] ≡ t
++ᵗ-idʳ []         = refl
++ᵗ-idʳ (tν t)     = cong tν       (++ᵗ-idʳ t)
++ᵗ-idʳ (tφ f c t) = cong (tφ f c) (++ᵗ-idʳ t)

++ᵗ-assoc : ∀ {n k j i} (t : Tel n k) (s : Tel k j) (u : Tel j i) →
            (t ++ᵗ s) ++ᵗ u ≡ t ++ᵗ (s ++ᵗ u)
++ᵗ-assoc []         s u = refl
++ᵗ-assoc (tν t)     s u = cong tν       (++ᵗ-assoc t s u)
++ᵗ-assoc (tφ f c t) s u = cong (tφ f c) (++ᵗ-assoc t s u)

-- Weakening through a concatenation is weakening twice.
wkTel-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (x : 𝔽 n) →
            wkTel (t ++ᵗ s) x ≡ wkTel s (wkTel t x)
wkTel-++ᵗ []         s x = refl
wkTel-++ᵗ (tν t)     s x = wkTel-++ᵗ t s (weaken* ⦃ Kᵣ ⦄ 2 x)
wkTel-++ᵗ (tφ f c t) s x = wkTel-++ᵗ t s (weaken* ⦃ Kᵣ ⦄ 1 x)

------------------------------------------------------------------------
-- Re-basing at the telescope's own scope.
------------------------------------------------------------------------

renTel-idᵗ : ∀ {n k} (t : Tel n k) → subst (Tel n) (renTel-id t) (renTel t (idₖ ⦃ Kᵣ ⦄)) ≡ t
renTel-idᵗ []         = refl
renTel-idᵗ (tν t)     =
  subst-tν (renTel-id t) _
    ■ cong tν ( cong (subst (Tel _) (renTel-id t)) (renTel-cong t (id↑* 2 (λ _ → refl)))
              ■ renTel-idᵗ t )
renTel-idᵗ (tφ f c t) =
  subst-tφ (renTel-id t) f (c ⋯ idₖ ⦃ Kᵣ ⦄) _
    ■ cong₂ (tφ f) (⋯-id c (λ _ → refl))
                   ( cong (subst (Tel _) (renTel-id t)) (renTel-cong t (id↑ (λ _ → refl)))
                   ■ renTel-idᵗ t )

-- `liftId` IS `liftRen` on an endomorphism: both recurse the same way, so the
-- transport is the only difference.
liftId-liftRen : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ n) (x : 𝔽 k) →
                 subst 𝔽 (renTel-id t) (liftRen t ρ x) ≡ liftId t ρ x
liftId-liftRen []         ρ x = refl
liftId-liftRen (tν t)     ρ x = liftId-liftRen t (ρ ↑* 2) x
liftId-liftRen (tφ f c t) ρ x = liftId-liftRen t (ρ ↑)    x

wkTel-idᵗ : ∀ {n k} (t : Tel n k) (x : 𝔽 n) →
            subst 𝔽 (renTel-id t) (wkTel (renTel t (idₖ ⦃ Kᵣ ⦄)) x) ≡ wkTel t x
wkTel-idᵗ t x =
  subst-wkTel (renTel-id t) (renTel t _) x ■ cong (λ T → wkTel T x) (renTel-idᵗ t)

------------------------------------------------------------------------
-- `liftId` of the identity is the identity.
------------------------------------------------------------------------

liftId-id : ∀ {n k} (t : Tel n k) {ρ : n →ᵣ n} → ρ ≗ idₖ ⦃ Kᵣ ⦄ → liftId t ρ ≗ idₖ ⦃ Kᵣ ⦄
liftId-id []         eq = eq
liftId-id (tν t)     eq = liftId-id t (id↑* 2 eq)
liftId-id (tφ f c t) eq = liftId-id t (id↑ eq)

------------------------------------------------------------------------
-- Renaming a normal form by a scope ENDOmorphism.
------------------------------------------------------------------------

-- This is the bridge the four ≋′ transpositions cross: they rename the body by
-- an endo, `nf-nat` turns that into `renNF`, and `renNF` at the same scope is
-- exactly what Normal.Equiv's generators produce.
-- LINKED-φ: under linked φ a `tφ` carries a channel term, so renaming a normal
-- form by an endo ξ RENAMES the telescope's channels — the old "telescope
-- unchanged" statement (renNF (mkNF t es) n ξ ≡ mkNF t …) is FALSE.  The honest
-- statement is just `nf-nat` specialised to the same scope: the telescope becomes
-- `renTel t ξ`.
nf-endo : ∀ {n} (P : Proc n) (ξ : n →ᵣ n) →
          nf (P ⋯ₚ ξ) ≡ mkNF (renTel (tel (nf P)) ξ) (map (_⋯ liftRen (tel (nf P)) ξ) (thr (nf P)))
nf-endo P ξ = nf-nat P ξ
