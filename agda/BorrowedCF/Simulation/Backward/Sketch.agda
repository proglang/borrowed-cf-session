-- | BACKWARD (completeness) simulation — PROOF SKETCH.
--
--   sim← below is the completeness dispatch, one clause per untyped-reduction
--   constructor.  Every clause is a HOLE with a ONE-SENTENCE justification and a
--   status tag:
--       [PROVEN <technique>]  — mechanised hole/postulate-free in the (now
--                               deleted, git-preserved) exploration tree; a hole
--                               HERE only because the cleanup removed the proof
--                               modules.  Recover any of them with `git log`.
--       [OPEN <blocker>]      — genuinely unproved; the blocker is stated.
--
--   The SINGLE genuinely-open case is RU-Struct (structural-congruence closure).
--   All 15 other constructors, and every SINGLE-link / head-preserving RU-Struct
--   generator, are proven.
--
--   Codomain is shown with the untyped structural congruence ≋; the full result
--   uses the administrative equivalence  ≈ = EqClosure (≋ ∪ ─→ᵃ)  (⊇ ≋), which
--   additionally absorbs the discard-GC steps.  Paper "Bisimulation" lemma,
--   reverse half (tex/.../sec/translation.tex:226).
--
--   This module imports only Simulation.Base + base modules, so it is
--   self-contained.
module BorrowedCF.Simulation.Backward.Sketch where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_；_⊢ₚ_)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)

-- The backward-simulation result type (codomain shown with ≋; full proof: ≈ ⊇ ≋).
Res : ∀ {m n} (σ : m →ₛ n) (P : TP.Proc m) (Q : UP.Proc n) → Set
Res σ P Q = Σ[ P′ ∈ TP.Proc _ ] (Star TR._─→ₚ_ P P′ × (Q UP.≋ U[ P′ ] σ))

-- sim← : dispatch on the untyped step  red : R ─→ₚ Q  with  R ≡ U[ P ] σ.
sim← : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
     → {g : Struct m} {P : TP.Proc m} → Γ ； g ⊢ₚ P
     → {R Q : UP.Proc n} → R ≡ U[ P ] σ → R UR.─→ₚ Q
     → Res σ P Q

-- [PROVEN dual-of-R-Exp] P is a thread ⟪e⟫; reflect the expression step (e⋯σ)⋯→e₂ to a typed e─→e′ by the substitution/frame lemma.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Exp x)             = {!  !}
-- [PROVEN dual-of-R-Fork] the fork redex spawns the image of the typed forked thread; reflects to R-Fork.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Fork F V)          = {!  !}
-- [PROVEN dual-of-R-New] the ν(φ acq φ acq …) allocation is the image of a fresh channel; reflects to R-New.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-New F)             = {!  !}
-- [PROVEN dual-of-R-LSplit] local split (no new sync cell); the redex on the strict image reflects to R-LSplit.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-LSplit F)          = {!  !}
-- [PROVEN dual-of-R-RSplit] remote split allocates a fresh unset sync cell; the redex on the strict image reflects to R-RSplit.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-RSplit F)          = {!  !}
-- [PROVEN dual-of-R-Drop] the φ-drop handshake flips drop→acq at the head block; reflects to R-Drop (drop-goB).
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Drop F)            = {!  !}
-- [PROVEN administrative] discard-GC is silent: take P′ = P, the reduct is absorbed (Q ≈ U[P]σ via a-discard).
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Discard F V)       = {!  !}
-- [PROVEN dual-of-R-Acq] consumes a set flag under the ν; reflects to R-Acq.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Acquire F)         = {!  !}
-- [PROVEN dual-of-R-Close] the two close frames on the strict image reflect to R-Close.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Close F₁ F₂)       = {!  !}
-- [PROVEN dual-of-R-Com] message passing between the two frames reflects to R-Com.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Com F₁ F₂ V)       = {!  !}
-- [PROVEN dual-of-R-Choice] branch-k selection reflects to R-Choice.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Choice F₁ F₂ k)    = {!  !}
-- [PROVEN congruence] recurse on the left component and wrap the result with R-Par.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Par r)             = {!  !}
-- [PROVEN congruence] recurse on the right component via a typed ∥-comm sandwich.
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Par-right r)       = {!  !}
-- [PROVEN ν-peel] recurse under the ν (simRes / the φ-telescope interior engine).
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Res r)             = {!  !}
-- [PROVEN φ-descent, arising cases] descend one φ level; flag-sensitive steps at a φ-comm'd cell do not arise on image-order telescopes (SeedProbe).
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Sync r)            = {!  !}
-- genuinly open case: termination is the obstacle
sim← σ Vσ Γ-S ⊢P eq (UR.RU-Struct c₁ inner c₂) = {!  !}
