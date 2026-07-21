-- | Naturality of the structural normaliser under renaming.
--
--   `nf-nat : nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ` is what the four binder-permuting
--   ≋′ generators need: each of them renames the body, so relating the two
--   sides' normal forms means relating `nf` to `renNF`.
--
--   This is the one place the two-index `Tel n k` representation does NOT pay
--   for itself.  `plug-++ᵗ` is definitional there, but `renTel` composition is
--   not: `combine` builds `t₂ ++ᵗ renTel t₁ j₂`, and re-basing that is only
--   PROPOSITIONALLY the same shape as re-basing the parts.  The index lemmas
--   below isolate exactly that gap, and `NF-≡` is the interface that lets a
--   proof discharge it once, at the level of the packed normal form, instead of
--   threading transports through every component.
module BorrowedCF.Simulation.Support.Normal.Nat where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (νNF; φNF)

open import Data.List using (List; []; _∷_; _++_; map)

open Nat.Variables

------------------------------------------------------------------------
-- Shape arithmetic: `innerOf` sees only the SHAPE of a telescope.
------------------------------------------------------------------------

-- Re-basing does not change the shape, hence does not change `innerOf`.
innerOf-renTel : ∀ {n k} (t : Tel n k) (a b : ℕ) →
                 innerOf (renTel t a) b ≡ innerOf t b
innerOf-renTel []       a b = refl
innerOf-renTel (tν t)   a b = innerOf-renTel t (2 + a) (2 + b)
innerOf-renTel (tφ f t) a b = innerOf-renTel t (1 + a) (1 + b)

-- Concatenation of telescopes composes `innerOf`.
innerOf-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) (b : ℕ) →
              innerOf (t ++ᵗ s) b ≡ innerOf s (innerOf t b)
innerOf-++ᵗ []       s b = refl
innerOf-++ᵗ (tν t)   s b = innerOf-++ᵗ t s (2 + b)
innerOf-++ᵗ (tφ f t) s b = innerOf-++ᵗ t s (1 + b)

-- A telescope re-based at its own outer scope keeps its inner scope.
innerOf-id : ∀ {n k} (t : Tel n k) → innerOf t n ≡ k
innerOf-id = renTel-id

------------------------------------------------------------------------
-- Equality of packed normal forms.
------------------------------------------------------------------------

-- `NF n` packs the inner scope existentially, so two normal forms are equal as
-- soon as the inner scopes agree and the transported components do.  This is
-- the interface that keeps the transports out of the naturality proof proper.
NF-≡ : ∀ {n k k′} (eq : k ≡ k′)
       {t : Tel n k} {t′ : Tel n k′}
       {es : List (Tm k)} {es′ : List (Tm k′)} →
       subst (Tel n) eq t ≡ t′ →
       subst (λ j → List (Tm j)) eq es ≡ es′ →
       mkNF t es ≡ mkNF t′ es′
NF-≡ refl refl refl = refl

------------------------------------------------------------------------
-- Naturality, modulo ONE lemma about `combine`.
------------------------------------------------------------------------

-- The leaf, ν and φ cases of naturality are DEFINITIONAL: `renNF` pushes
-- `renTel`/`liftRen` under a head binder exactly the way `nf` does, so they are
-- `refl` and two `cong`s.  Everything that is left is the ∥ case, i.e. that
-- `combine` commutes with re-basing.  Isolating it as a hypothesis (rather than
-- a hole) records that the reduction is COMPLETE: naturality is `Combine-nat`
-- and nothing else.
Combine-nat : Set
Combine-nat = ∀ {n n′} (N₁ N₂ : NF n) (ρ : n →ᵣ n′) →
              combine (renNF N₁ n′ ρ) (renNF N₂ n′ ρ) ≡ renNF (combine N₁ N₂) n′ ρ

module _ (combine-nat : Combine-nat) where

  nf-nat : ∀ {n n′} (P : Proc n) (ρ : n →ᵣ n′) → nf (P ⋯ₚ ρ) ≡ renNF (nf P) n′ ρ
  nf-nat ⟪ e ⟫   ρ = refl
  nf-nat (ν P)   ρ = cong νNF     (nf-nat P (ρ ↑* 2))
  nf-nat (φ f P) ρ = cong (φNF f) (nf-nat P (ρ ↑))
  nf-nat (P ∥ Q) ρ =
    cong₂ combine (nf-nat P ρ) (nf-nat Q ρ) ■ combine-nat (nf P) (nf Q) ρ

------------------------------------------------------------------------
-- What `Combine-nat` needs, and why it is the awkward one.
------------------------------------------------------------------------
--
--   Writing N₁ = mkNF t₁ es₁ (t₁ : Tel n j₁) and N₂ = mkNF t₂ es₂ (t₂ : Tel n j₂),
--   the two sides carry inner scopes
--
--       LHS : innerOf (renTel t₁ n′) (innerOf t₂ n′)
--       RHS : innerOf (t₂ ++ᵗ renTel t₁ j₂) n′
--
--   which the lemmas above reconcile — both equal `innerOf t₁ (innerOf t₂ n′)`
--   — but only PROPOSITIONALLY.  A proof therefore needs, besides `NF-≡`:
--
--     A.  subst (Tel b) (innerOf-renTel t a b) (renTel (renTel t a) b) ≡ renTel t b
--     B.  subst (Tel b) (innerOf-++ᵗ t s b) (renTel (t ++ᵗ s) b)
--           ≡ renTel t b ++ᵗ renTel s (innerOf t b)
--
--   plus the matching `liftRen`/`wkTel` composition facts for the thread lists.
--   Both A and B go through by induction on the telescope with a `subst`-pushing
--   helper (`subst (Tel n) eq (tν X) ≡ tν (subst (Tel _) eq X)`, by J).
--
--   This is the one place the two-index `Tel n k` representation stops paying
--   for itself.  The alternative — indexing normal forms by a scope-free
--   `Shape` with `inner : Shape → ℕ → ℕ`, so that re-basing is the IDENTITY —
--   makes A and B vanish and the telescope half of `Combine-nat` `refl`, at the
--   cost of making `plug-++` (currently definitional) carry the transport
--   instead.  Which representation to settle on is the open design call.
