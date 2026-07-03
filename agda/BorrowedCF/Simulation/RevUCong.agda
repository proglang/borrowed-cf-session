module BorrowedCF.Simulation.RevUCong where

-- | Image-reflection for the reverse simulation: DETERMINATION.
--
--   GOAL (parent task).  Build `reverse-U-≋`, reflecting an untyped ≋ between a
--   process R and a translation image  U[ P ] σ  to R being ITSELF an image
--   U[ P′ ] σ  of a typed-≋-related source P′, so that sim← (Reverse.agda l.362)
--   can recurse on the strictly-smaller SUB-derivation instead of transporting
--   the reduction across the ≋-chain (the RevCongStrong replay that fails to
--   terminate).
--
--   FINDING.  The STRICT-image form of `reverse-U-≋` is FALSE, and this module
--   proves it hole-free / postulate-free.  The obstruction is the UNTYPED-ONLY
--   structural generator `νφ-comm′` (Untyped.agda), which pulls a sync cell OUT
--   of the dual-pair binder:
--
--       ν (φ x P) ≋′ φ x (ν (P ⋯ₚ assocSwapᵣ 1 2)).
--
--   Two facts collide:
--     (1) φ-freeness of the HEAD is a translation invariant: every image
--         U[ P′ ] σ  has head constructor ⟪⟫ / ∥ / ν and NEVER φ  (U-not-φ).
--     (2) for any source whose FIRST bind group has length ≥ 2 (syncs ≥ 1) — the
--         canonical `src`-shape  ν (1 ∷ 1 ∷ []) …  — the image is  ν (φ drop …)
--         (Bisim.UB[_] emits one φ per non-last bind-group element, flag ϕ[b]).
--   So a SINGLE νφ-comm step sends the image to the φ-headed
--         φ drop (ν …)
--   which by (1) is NOT  U[ P′ ] σ  for ANY P′.  Hence  R ≋ U[ P ] σ  does not
--   force R to be an image: the reflection fails at the φ-telescope.  Such
--   φ-bearing sources ARE typeable — the R-New forward image is exactly this
--   ν (1 ∷ 1 ∷ …) shape (Theorems.agda:103 builds the length-≥2 BindCtx via
--   cons-ret/acq), so this escape is genuinely reachable in sim←.
--
--   Since the sim← input is  R ≈ U[ P ] σ  with  ≈ ⊇ ≋ ⊇ {νφ-comm′}, NO
--   codomain weakening rescues the STRICT  R ≡ U[ P′ ] σ  that sim←ᵍ's inversions
--   (inv-U-∥ / inv-U-ν / …) require, because the escaping R is provably not a
--   strict image AT ALL.  So the sim← non-ε case genuinely needs a
--   calculus/statement design change (a φ-telescope-aware reverse inversion
--   engine, or dropping sim←ᵍ's strict-image demand) — the determination the
--   parent asked to bring back either way.
--
--   Deliverables (all hole-free, postulate-free):
--     • U-not-φ       : a translation image never has head φ.
--     • U-≋-escapes   : the concrete witness  Σ R. (R ≋ U[ Pesc ] σ₀) ×
--                       (∀ P′. R ≢ U[ P′ ] σ₀)  — exactly the requested
--                       refutation data (concrete R, P = Pesc, generator νφ-comm).
--     • Reverse-U-≋   : the exact requested lemma type, and
--       reverse-U-≋-⊥ : Reverse-U-≋ → ChanCx Γ → (Γ ; g ⊢ₚ Pesc) → ⊥,
--                       reducing the typed lemma to a contradiction.  The typing
--                       of the concrete φ-bearing source is the ONE remaining
--                       input; the calculus admits it (see above), so the typed
--                       lemma is refuted, not merely the untyped skeleton.

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Context using (Ctx; Struct)
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open TP using (_;_⊢ₚ_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Variables
open Fin.Patterns

------------------------------------------------------------------------
-- (1) A translation image never has head constructor φ.
--     U[ ⟪e⟫ ]σ = ⟪ e⋯σ ⟫,  U[ P∥Q ]σ = U[P]σ ∥ U[Q]σ,  U[ ν… ]σ = ν …
--     — the head is always ⟪⟫ / ∥ / ν, so it can never equal  φ f Q.
------------------------------------------------------------------------

U-not-φ : ∀ {m n} (P′ : TP.Proc m) (σ : m →ₛ n) {f : UP.Flag} {Q : UP.Proc (suc n)}
        → U[ P′ ] σ ≢ UP.φ f Q
U-not-φ TP.⟪ e ⟫       σ ()
U-not-φ (P TP.∥ Q)     σ ()
U-not-φ (TP.ν B₁ B₂ P) σ ()

------------------------------------------------------------------------
-- (2) The concrete escaping source and its φ-headed non-image reduct.
--     First bind group (1 ∷ 1 ∷ []) has syncs 1, so the image is  ν (φ drop …);
--     a single νφ-comm step lands on the φ-headed  φ drop (ν …).
------------------------------------------------------------------------

Pesc : TP.Proc 0
Pesc = TP.ν (1 ∷ 1 ∷ []) [] (TP.⟪ K `drop ·¹ (` 0F) ⟫)

σ₀ : 0 →ₛ 0
σ₀ ()

Vσ₀ : VSub σ₀
Vσ₀ ()

U-≋-escapes :
  Σ[ R ∈ UP.Proc 0 ] (R UP.≋ U[ Pesc ] σ₀) × (∀ (P′ : TP.Proc 0) → R ≢ U[ P′ ] σ₀)
U-≋-escapes =
  _ , Eq*.symmetric UP._≋′_ (Eq*.return UP.νφ-comm′)
    , λ P′ eq → U-not-φ P′ σ₀ (sym eq)

------------------------------------------------------------------------
-- (3) The exact requested lemma type, and its refutation.
------------------------------------------------------------------------

Reverse-U-≋ : Set
Reverse-U-≋ = ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
            → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
            → {R : UP.Proc n} → R UP.≋ U[ P ] σ
            → Σ[ P′ ∈ TP.Proc m ] (R ≡ U[ P′ ] σ) × (P TP.≋ P′)

reverse-U-≋-⊥ : Reverse-U-≋ → {Γ : Ctx 0} → ChanCx Γ → {g : Struct 0}
              → Γ ; g ⊢ₚ Pesc → ⊥
reverse-U-≋-⊥ rev {Γ} cc {g} ⊢P
  with rev σ₀ Vσ₀ {Γ} cc {g} ⊢P (Eq*.symmetric UP._≋′_ (Eq*.return UP.νφ-comm′))
... | P′ , R≡ , _ = U-not-φ P′ σ₀ (sym R≡)
