-- | The residual administrative-reflection obligation `AdminStep`
--   (BorrowedCF.Simulation2.Backward.PhiChainBase), analysed to its exact
--   content.
--
--   PhiChainBase.base-from-strict reflects a direct untyped step  red : R ─→ₚ Q
--   against a process  R ≈ U[ P ] σ  by structural recursion on the ≈-chain.
--   At a ≋ link it re-wraps (reduct unchanged) and RECURSES; at an administrative
--   (─→ᵃ, discard-GC) link it delegates the WHOLE remaining tail to the
--   hypothesis `admin : AdminStep` WITHOUT recursing:
--
--     base-from-strict … (fwd (inj₂ a) ◅ rest) red = admin (inj₁ a) rest red
--
--   So `admin` must, on its own, reflect an ARBITRARY direct step across ONE
--   leading admin link WITH the tail  Y ≈ U[ P ] σ  in scope, and return a fully
--   reflected  Res Q.
--
--   THE EXACT CONTENT OF AdminStep IS `Base`.  Because an ─→ᵃ link is itself a ≈
--   link (─→ᵃ⇒≈), the leading admin link composes with the tail into a single
--   relatedness  R ≈ U[ P ] σ, and reflecting  red : R ─→ₚ Q  against THAT is
--   precisely  UpToPhiEngineWF.Base.  This module machine-checks the reduction
--
--       adminStep-from-base : Base → AdminStep          (hole/postulate-free)
--
--   which is a two-line absorption — establishing that base-from-strict's
--   admin-link factoring makes NO progress on Base: `admin` carries the entire
--   remaining reflection content, and that content is `Base` itself.
--
--   That AdminStep genuinely needs the full reflector (and cannot be discharged
--   standalone from its stated interface, which supplies neither `Strict` nor
--   `Base`) is machine-witnessed: for a disjoint genuine φ-drop the reduct's
--   #acq strictly increments, so the step is NOT absorbable up-to-≈ with zero
--   typed steps (BorrowedCF.Simulation2.Backward.DropNotAdmin.
--   ε-reflection-unavailable, re-exported below as `disjoint-drop-needs-reflector`).
--   Hence the disjoint-observable case forces a genuine typed step, i.e. requires
--   the strict image reflector — exactly what `Base` provides and what
--   AdminStep's interface withholds.
module BorrowedCF.Simulation2.Backward.AdminStepProof where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin
  using (_≈_; _─→ᵃ_; ≈-sym; ─→ᵃ⇒≈)
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_)

import Data.Sum as Sum
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅◅_)

-- The machine witness that a disjoint genuine φ-drop cannot be absorbed
-- up-to-≈ with zero typed steps (so a real reflector is unavoidable).
open import BorrowedCF.Simulation2.Backward.DropNotAdmin
  using (ε-reflection-unavailable) public

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
         {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P) where

  -- Identical to PhiChainBase.Res / .AdminStep and UpToPhiEngineWF.Base,
  -- restated here so this module does not depend on the off-limits Backward*.
  Res : UP.Proc n → Set
  Res Q = Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

  Base : Set
  Base = ∀ {R Q : UP.Proc n} → R ≈ U[ P ] σ → R UR.─→ₚ Q → Res Q

  AdminStep : Set
  AdminStep = ∀ {R Y Q : UP.Proc n}
            → (R ─→ᵃ Y) Sum.⊎ (Y ─→ᵃ R)
            → Y ≈ U[ P ] σ
            → R UR.─→ₚ Q
            → Res Q

  -- The reduction: AdminStep is exactly Base.  A leading admin link (either
  -- direction) is a ≈ link, so it composes with the tail  Y ≈ U[ P ] σ  into
  -- R ≈ U[ P ] σ, and the residual is the full reflector on R.
  adminStep-from-base : Base → AdminStep
  adminStep-from-base base (Sum.inj₁ a) tail red =
    base (─→ᵃ⇒≈ a ◅◅ tail) red
  adminStep-from-base base (Sum.inj₂ a) tail red =
    base (≈-sym (─→ᵃ⇒≈ a) ◅◅ tail) red
