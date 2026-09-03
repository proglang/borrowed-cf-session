{-# OPTIONS --allow-unsolved-metas #-}

-- | Phase 4b, the PAIR corollary (`R-Com` / `R-Choice` / `R-Close`).
--
--   `Canonical.agda` canonicalises ONE located thread.  The synchronising
--   rules need TWO threads brought under the SAME binder, side by side and
--   in the right order:
--
--     ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
--       ((⟪ E₁ [ K c₁ ·¹ (` 0F) ]* ⟫ ∥ ⟪ E₂ [ K c₂ ·¹ (` y) ]* ⟫) ∥ Q)
--
--   with `y = wkʳ mid (wkˡ (suc b₁ + sum B₁) 0F)`, i.e. the head of the
--   first group of the SECOND endpoint.
--
--   This module supplies the two-hole process context that the construction
--   walks (`ProcessContext₂`, `plug₂`) and the statement `CanonPair`.  The
--   construction itself is the ONE piece of Phase 4b that is not yet built;
--   `canon-pair` is stated with a hole, which is why this file (and only
--   this file) carries `--allow-unsolved-metas`.
--
--   Plan for the missing proof (two passes over `Canonical.agda`'s
--   machinery):
--
--     1. `bubble₂`, the two-hole analogue of `bubble`: walk `ProcessContext₂`
--        and produce a bind stack `bs`, two renamings `ρ₁`/`ρ₂` and a
--        residual with
--            plug₂ c R₁ R₂ ≋ plugL bs (((R₁ ⋯ₚ ρ₁) ∥ (R₂ ⋯ₚ ρ₂)) ∥ resid).
--        The `par₂`/`par₂ˢ` leaves are where the two holes meet; the
--        `par-left`/`par-right`/`bind` nodes are handled exactly as in
--        `bubble` (`foldPar` for the siblings, `∥-assoc`/`∥-comm` to keep the
--        two threads leftmost and in order -- `par₂ˢ` needs one `∥-comm`).
--     2. `push` (unchanged) moves the binding `ν B₁ B₂` inside `bs`, and its
--        handle lemma gives both `ρ₁ x₁` and `ρ₂ x₂` in the binder's local
--        scope; `HeadShape` on each side then pins them to `0F` and
--        `sum C₁ ↑ʳ 0F`.
--     3. For `R-Com` / `R-Close` the two frames and the residual are
--        additionally strengthened w.r.t. BOTH head handles
--        (`Support/RevComConfine.agda`'s `wkₚ` form).
module BorrowedCF.Simulation.BackwardSoup.CanonicalPair where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.BackwardSoup.Locate
open import BorrowedCF.Simulation.BackwardSoup.Position
open import BorrowedCF.Simulation.BackwardSoup.Canonical

open 𝐓 using (BindGroup; _;_⊢ₚ_)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  Two-hole process contexts.

data ProcessContext₂ : ℕ → ℕ → ℕ → Set where
  par₂  : ProcessContext k₁ n → ProcessContext k₂ n → ProcessContext₂ k₁ k₂ n
  par₂ˢ : ProcessContext k₂ n → ProcessContext k₁ n → ProcessContext₂ k₁ k₂ n
  left₂ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc n → ProcessContext₂ k₁ k₂ n
  right₂ : 𝐓.Proc n → ProcessContext₂ k₁ k₂ n → ProcessContext₂ k₁ k₂ n
  bind₂ : (B₁ B₂ : BindGroup) →
          ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n) →
          ProcessContext₂ k₁ k₂ n

plug₂ :
  ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₁ → 𝐓.Proc k₂ → 𝐓.Proc n
plug₂ (par₂ c₁ c₂) R₁ R₂ = plug c₁ R₁ 𝐓.∥ plug c₂ R₂
plug₂ (par₂ˢ c₂ c₁) R₁ R₂ = plug c₂ R₂ 𝐓.∥ plug c₁ R₁
plug₂ (left₂ c Q) R₁ R₂ = plug₂ c R₁ R₂ 𝐓.∥ Q
plug₂ (right₂ Q c) R₁ R₂ = Q 𝐓.∥ plug₂ c R₁ R₂
plug₂ (bind₂ B₁ B₂ c) R₁ R₂ = 𝐓.ν B₁ B₂ (plug₂ c R₁ R₂)

-- The one-hole context obtained by filling the second hole.
fill₂ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₂ → ProcessContext k₁ n
fill₂ (par₂ c₁ c₂) R₂ = par-left c₁ (plug c₂ R₂)
fill₂ (par₂ˢ c₂ c₁) R₂ = par-right (plug c₂ R₂) c₁
fill₂ (left₂ c Q) R₂ = par-left (fill₂ c R₂) Q
fill₂ (right₂ Q c) R₂ = par-right Q (fill₂ c R₂)
fill₂ (bind₂ B₁ B₂ c) R₂ = bind B₁ B₂ (fill₂ c R₂)

plug-fill₂ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  plug (fill₂ c R₂) R₁ ≡ plug₂ c R₁ R₂
plug-fill₂ (par₂ c₁ c₂) R₁ R₂ = refl
plug-fill₂ (par₂ˢ c₂ c₁) R₁ R₂ = refl
plug-fill₂ (left₂ c Q) R₁ R₂ = cong (𝐓._∥ Q) (plug-fill₂ c R₁ R₂)
plug-fill₂ (right₂ Q c) R₁ R₂ = cong (Q 𝐓.∥_) (plug-fill₂ c R₁ R₂)
plug-fill₂ (bind₂ B₁ B₂ c) R₁ R₂ =
  cong (𝐓.ν B₁ B₂) (plug-fill₂ c R₁ R₂)

-- ... and the one-hole context of the SECOND thread.
fill₁ : ProcessContext₂ k₁ k₂ n → 𝐓.Proc k₁ → ProcessContext k₂ n
fill₁ (par₂ c₁ c₂) R₁ = par-right (plug c₁ R₁) c₂
fill₁ (par₂ˢ c₂ c₁) R₁ = par-left c₂ (plug c₁ R₁)
fill₁ (left₂ c Q) R₁ = par-left (fill₁ c R₁) Q
fill₁ (right₂ Q c) R₁ = par-right Q (fill₁ c R₁)
fill₁ (bind₂ B₁ B₂ c) R₁ = bind B₁ B₂ (fill₁ c R₁)

plug-fill₁ :
  (c : ProcessContext₂ k₁ k₂ n) (R₁ : 𝐓.Proc k₁) (R₂ : 𝐓.Proc k₂) →
  plug (fill₁ c R₁) R₂ ≡ plug₂ c R₁ R₂
plug-fill₁ (par₂ c₁ c₂) R₁ R₂ = refl
plug-fill₁ (par₂ˢ c₂ c₁) R₁ R₂ = refl
plug-fill₁ (left₂ c Q) R₁ R₂ = cong (𝐓._∥ Q) (plug-fill₁ c R₁ R₂)
plug-fill₁ (right₂ Q c) R₁ R₂ = cong (Q 𝐓.∥_) (plug-fill₁ c R₁ R₂)
plug-fill₁ (bind₂ B₁ B₂ c) R₁ R₂ =
  cong (𝐓.ν B₁ B₂) (plug-fill₁ c R₁ R₂)

------------------------------------------------------------------------
-- 2.  The statement.
--
-- Shaped exactly like the left-hand side of `R-Choice`; `R-Com` and
-- `R-Close` add the strengthening of the frames and the residual.

record CanonPair
  {k₁ k₂ : ℕ} (P : 𝐓.Proc 0) (e₁ : Tm k₁) (e₂ : Tm k₂)
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) : Set where
  constructor canonPair
  field
    {midᵖ}  : ℕ
    b₁ b₂   : ℕ
    B₁ B₂   : BindGroup
    above′  : ProcessContext midᵖ 0
    ρ₁      : k₁ →ᵣ
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    ρ₂      : k₂ →ᵣ
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    resid   : 𝐓.Proc
              (sum (suc b₁ L.∷ B₁) + sum (suc b₂ L.∷ B₂) + midᵖ)
    ≋-canon : P 𝐓.≋
      plug above′
        (𝐓.ν (suc b₁ L.∷ B₁) (suc b₂ L.∷ B₂)
          ((𝐓.⟪ e₁ ⋯ ρ₁ ⟫ 𝐓.∥ 𝐓.⟪ e₂ ⋯ ρ₂ ⟫) 𝐓.∥ resid))
    x₁-eq   : ρ₁ x₁ ≡ 0F
    x₂-eq   : ρ₂ x₂ ≡
              wkʳ ⦃ Kᵣ ⦄ midᵖ
                (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

-- The two threads must resolve to the SAME binder, on OPPOSITE sides, each
-- at the head of its first group.  `bnd₁`/`bnd₂` are the resolutions of the
-- two handles in the ONE-hole contexts obtained by filling the other hole.
-- (That the two `Binder`s name the SAME `ν` node and OPPOSITE endpoints is
-- what the missing construction has to read off `c`; the soup step supplies
-- the two thread indices, and `Position/Crux.agda`'s `PairArgRedexHead`
-- supplies the two `HeadShape`s.)
canon-pair :
  {c : ProcessContext₂ k₁ k₂ 0} (e₁ : Tm k₁) (e₂ : Tm k₂)
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd₁ : Binder (fill₂ c 𝐓.⟪ e₂ ⟫) x₁)
  (bnd₂ : Binder (fill₁ c 𝐓.⟪ e₁ ⟫) x₂) →
  HeadShape (Binder.B₁ bnd₁) (Binder.B₂ bnd₁) (Binder.local bnd₁) →
  HeadShape (Binder.B₁ bnd₂) (Binder.B₂ bnd₂) (Binder.local bnd₂) →
  CanonPair (plug₂ c 𝐓.⟪ e₁ ⟫ 𝐓.⟪ e₂ ⟫) e₁ e₂ x₁ x₂
canon-pair e₁ e₂ bnd₁ bnd₂ hs₁ hs₂ = {!!}
