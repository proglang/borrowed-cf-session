{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.Theorems where

-- | Main results of the simulation development (goal: the paper's Bisimulation
--   lemma, tex/20250826-compositional/sec/translation.tex:226 — for well-typed P,
--   P ─→ₚ P′  (typed)  ⇔  U[P] ─→ₚ U[P′]  (untyped)).
--
--     • U[_]    (Bisim.agda)              — the translation, DONE, hole-free.
--     • U-cong / U-⋯ₚ / U-σ⋯ / UB-nat     (TranslationProperties)  — DONE.
--     • U-≋ / U-≋′  — translation respects structural congruence  — DONE except the
--       two ν-reordering rules dispatch to U-ν-swap (DONE) and U-ν-comm (1 hole, below).
--     • U-ν-swap    — COMPLETE, hole-free, postulate-free (see below; the φ-block
--       permutation engine: flattening + φ^-swap + canonₛ-nat + swap-++ₛ + renId*).
--     • U-ν-comm    — postulate ELIMINATED; now a structured proof with ONE hole.  The
--       binder-permutation ENGINE is COMPLETE & verified (φ-ν-comm / φ^-ν-comm / ν-φ^-comm
--       / φ^-⋯ₚ / νφφ-ext / Uν-flat / telescope-transpose).  The single remaining hole is
--       PHASE 3 = the body data-permutation reconciliation; see the comment at the hole.
--     • U-ν-ext     — DONE.
--     • sim→        — forward simulation; R-Exp/Par/Struct/Fork/New/Close DONE.
--
--   REMAINING TO CLOSE THE FORWARD DIRECTION (postulate-free):
--     1. U-ν-comm  — ONE hole (phase-3 body reconcile).  See the comment at the hole
--        (~the `{!   !}` just after `telescope-transpose …` in U-ν-comm).
--     2. The 5 sim→ channel-op holes (R-Com/LSplit/RSplit/Drop/Acq). NOTE: R-Acq/Drop/Com
--        etc. need a TYPING hypothesis on sim→ (a not-yet-landed weakening constructor on
--        process typing) — see the block before them and memory `simulation-progress.md`.
--
--   THE OTHER HALF OF THE Bisimulation lemma — the REFLECTION direction
--   (untyped ⇒ typed: U[P] ─→ₚ Q  ⇒  ∃P′. P ─→ₚ P′ ∧ Q = U[P′], UNDER well-typedness
--   of P) — is NOT STARTED.  It needs: (i) an untyped TYPING judgement (undefined —
--   the forward direction never needed Γ⊢ₚP, only VSub σ, but reflection does); (ii)
--   the converse simulation (inversion: every untyped step came from a typed one).
--   This is the long pole — plausibly as large as everything above combined; it may
--   admit a determinism/inversion shortcut on top of sim→ + well-typedness, but that
--   is unproven.  Scope it before committing.
--
--   This module has OPEN HOLES (the 5 sim→ ops) so it CANNOT be re-exported from the
--   barrel (BorrowedCF/Simulation.agda re-exports only the 7 hole-free foundation
--   modules).  Check it standalone:  ./agda-check.sh check BorrowedCF/Simulation/Theorems.agda

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.TypedMW as 𝐓R
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Frames
open import BorrowedCF.Simulation.TranslationProperties
open import BorrowedCF.Simulation.Flatten
open import BorrowedCF.Simulation.BlockPermutation
open import BorrowedCF.Simulation.NuExtrusion
open import Data.Nat.Solver using (module +-*-Solver)
open import BorrowedCF.Simulation.Theorems.Toolkit
open import BorrowedCF.Simulation.Theorems.NuSwap
open import BorrowedCF.Simulation.Theorems.NuComm


U-≋′ : (σ : m →ₛ n) {P Q : 𝐓.Proc m} → P 𝐓.≋′ Q → U[ P ] σ 𝐔.≋ U[ Q ] σ
U-≋′ σ 𝐓.∥-comm′       = 𝐔.∥-comm
U-≋′ σ 𝐓.∥-assoc′      = 𝐔.∥-assoc
U-≋′ σ 𝐓.∥-unit′       = 𝐔.∥-unitˡ
U-≋′ σ (𝐓.∥-cong′ x)   = 𝐔.∥-cong (U-≋′ σ x) ε
U-≋′ σ (𝐓.ν-cong′ {B₁} {B₂} x) =
  𝐔.ν-cong (UB-cong B₁ _ (λ σ₁ → UB-cong B₂ _ (λ σ₂ → U-≋′ _ x)))
U-≋′ σ (𝐓.ν-swap′ {B₁} {B₂} {P}) = U-ν-swap σ {B₁} {B₂} {P}
U-≋′ σ (𝐓.ν-comm′ {B₁} {B₂} {A₁} {A₂} {P}) = U-ν-comm σ {B₁} {B₂} {A₁} {A₂} {P}
U-≋′ σ (𝐓.ν-ext′ {P} {B₁} {B₂} {Q}) = U-ν-ext σ P B₁ B₂ Q

U-≋ : (σ : m →ₛ n) {P Q : 𝐓.Proc m} → P 𝐓.≋ Q → U[ P ] σ 𝐔.≋ U[ Q ] σ
U-≋ σ = kleisliStar (λ P → U[ P ] σ)
          λ { (fwd s) → U-≋′ σ s ; (bwd s) → Eq*.symmetric _ (U-≋′ σ s) }

-- Value-carrying frame congruences (the Value witnesses are irrelevant).

sim→ : (σ : m →ₛ n) → VSub σ → {P P′ : 𝐓.Proc m} → P 𝐓R.─→ₚ P′ → U[ P ] σ 𝐔R.─→ₚ U[ P′ ] σ
sim→ σ Vσ (𝐓R.R-Exp x)         = 𝐔R.RU-Exp (⋯→-⋯ₛ σ Vσ x)
sim→ σ Vσ (𝐓R.R-Par red)       = 𝐔R.RU-Par (sim→ σ Vσ red)
sim→ σ Vσ (𝐓R.R-Struct e r e′) = 𝐔R.RU-Struct (U-≋ σ e) (sim→ σ Vσ r) (U-≋ σ e′)
sim→ {m = m} {n = n} σ Vσ (𝐓R.R-New E) =
  𝐔R.RU-Struct (≡→≋ (cong 𝐔.⟪_⟫ (frame-plug* E σ Vσ)))
               (𝐔R.RU-New (frame*-⋯ E σ Vσ))
               (Eq*.symmetric _
                 (𝐔.ν-cong ( 𝐔.φ-cong (Eq*.return 𝐔.φ-ext′)
                           ◅◅ 𝐔.φ-cong (𝐔.φ-cong 𝐔.∥-assoc)
                           ◅◅ ≡→≋ (cong (λ z → 𝐔.φ (𝐔.φ (((1F 𝐔.↦ 𝐔.set) 𝐔.∥ (0F 𝐔.↦ 𝐔.set)) 𝐔.∥ z)))
                                        leafEq))))
  where
    e∅ : ∀ {N} → 0 →ₛ N
    e∅ = λ ()
    Ve∅ : ∀ {N} → VSub (e∅ {N})
    Ve∅ = λ ()
    t₁ : Tm (1 + (2 + n))
    t₁ = ((` 0F) ⊗ (` 1F)) ⊗ (K `unit ⋯ weakenᵣ)
    t₂ : Tm (1 + (1 + (2 + n)))
    t₂ = ((` 0F) ⊗ (` suc (weaken* ⦃ Kᵣ ⦄ 1 1F))) ⊗ (K `unit ⋯ weakenᵣ)
    in1 : 1 →ₛ (1 + (2 + n))
    in1 = (t₁ ∷ₛ e∅) ++ₛ e∅
    in2 : 1 →ₛ (1 + (1 + (2 + n)))
    in2 = (t₂ ∷ₛ e∅) ++ₛ e∅
    part1 : 1 →ₛ (1 + (1 + (2 + n)))
    part1 = λ i → in1 i ⋯ weaken* ⦃ Kᵣ ⦄ 1
    Bσ : m →ₛ (1 + (1 + (2 + n)))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 1
    σ′ : (1 + 1 + m) →ₛ (1 + (1 + (2 + n)))
    σ′ = (part1 ++ₛ in2) ++ₛ Bσ
    Vin1 : VSub in1
    Vin1 = ++ₛ-VSub {σ₁ = t₁ ∷ₛ e∅} (∷ₛ-VSub {t = t₁} (V-⊗ (V-⊗ V-` V-`) V-K) Ve∅) Ve∅
    Vin2 : VSub in2
    Vin2 = ++ₛ-VSub {σ₁ = t₂ ∷ₛ e∅} (∷ₛ-VSub {t = t₂} (V-⊗ (V-⊗ V-` V-`) V-K) Ve∅) Ve∅
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = part1 ++ₛ in2}
            (++ₛ-VSub {σ₁ = part1} (weaken-VSub 1 Vin1) Vin2)
            (weaken-VSub 1 (weaken-VSub 1 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 4)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 1)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1)
    perF : (F : Frame m) → frame-⋯ (F ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame-⋯ F σ Vσ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 4
    perF F = frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
           ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)) weakenEq
           ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)))
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_ (perF F) (frameEqA E*)
    leafEq = cong 𝐔.⟪_⟫ (frame-plug* (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                        ■ cong (_[ ((` 0F) ⊗ (` 1F)) ⋯ σ′ ]*) (frameEqA E))
sim→ σ Vσ (𝐓R.R-Fork E V) =
  subst₂ 𝐔R._─→ₚ_ (sym (cong 𝐔.⟪_⟫ (frame-plug* E σ Vσ)))
                  (cong₂ 𝐔._∥_ (sym (cong 𝐔.⟪_⟫ (frame-plug* E σ Vσ))) refl)
                  (𝐔R.RU-Fork (frame*-⋯ E σ Vσ) (value-⋯ V σ Vσ))
-- ════════════════════════════════════════════════════════════════════════════
-- OPEN OBLIGATION 2/2: the 5 channel-operation cases of the forward simulation.
-- sim→ relates typed reduction 𝐓R (= Reduction.Processes.TypedMW) to untyped 𝐔R
-- (= Reduction.Processes.Untyped) through the translation U[_].  R-Exp/Par/Struct/
-- Fork/New/Close are DONE (above) and are the TEMPLATE; copy their shape.
--
-- ⚠ DESIGN BLOCKER (found 2026-06-08): these 5 ops are FALSE under the current
-- `(σ : m →ₛ n) → VSub σ` signature — they need WELL-TYPEDNESS.  E.g. RU-Acquire's
-- parallel proc is `P⋯ₚweakenᵣ` (it must avoid the consumed sync channel); with an
-- ill-typed P that references the acquired channel, U[P]σ uses that sync var and the
-- rule cannot fire (counterexample: P = ⟪acq·(`0F)⟫).  Confirmed vs the paper (Acquire
-- rule writes the SAME named Proc both sides ⇒ Proc avoids the consumed channel; the
-- headline Bisimulation is stated "for well-typed P").  The historical "forward doesn't
-- need Γ⊢ₚP" note was only validated on the easy ops.  DECISION (user): add a typing
-- hypothesis `Γ;γ⊢ₚP` to sim→ (postulate-clean: ⊢ₚ is built from Context ops, not wkₚ).
-- GATED on a not-yet-landed WEAKENING CONSTRUCTOR on `_;_⊢ₚ_` (Processes/Typed.agda) whose
-- STRENGTHENING/inversion gives `P ≡ P′⋯ₚweakenᵣ`.  Full recipe in simulation-progress.md.
--
-- ⚠ REFINEMENT (2026-06-09): the "needs typing" obstruction is SPECIFIC to the CONSUMING
-- ops (R-Acq / R-Drop / R-Com): their untyped rule shape forces the parallel `P` to avoid a
-- channel that is removed, which only well-typedness guarantees.  The SPLIT ops ADD a channel
-- and consume nothing, so they are provable NOW under VSub-only:
--   • R-LSplit — untyped RU-LSplit leaves P AND the binder depth UNCHANGED (syncs preserved,
--     no new φ); the typed rule grows one borrow (P⋯lwk).  Reconciliation is pure
--     translation+renaming algebra (no strengthening).  ← THE case to do next.
--   • R-RSplit — also non-consuming, but INTRODUCES a φ (syncs +1) ⇒ harder; do after LSplit.
--
-- THE TEMPLATE (see R-New ~line 300 and R-Close ~line 503, both fully proven):
--   sim→ σ Vσ (𝐓R.R-Foo …) =
--     𝐔R.RU-Struct  (≡→≋  <LHS leaf reconcile>)        -- ≋ : U[lhs]σ ≋ <RU-redex shape>
--                   (𝐔R.RU-Foo (frame*-⋯ E σ Vσ) …)    -- the matching untyped rule
--                   (≡→≋  <RHS leaf reconcile>)         -- ≋ : <RU-result> ≋ U[rhs]σ
--   where the leaf reconciles use `frame-plug*` (subst commutes with Frame* plugging)
--   and `frameEqA` (per-frame `frame-fusion-gen` ■ `frame-cong` ■ sym; needs a
--   weaken-composition `weakenEq`).  Build any concrete leaf substitution σ′ with the
--   `e∅`/`Ve∅` empty-sub trick (see R-New) so VSub metas solve.
--
-- REUSABLE MACHINERY (all proven; in this file or the foundation modules):
--   frame-plug* / frame*-⋯ / frame-fusion-gen / frame-cong / value-⋯  (frames)
--   ≡→≋ / subst-∥ / ⋯ₚ-id / 𝐓⋯ₚ-id                                   (SubstLemmas/Frames)
--   U-σ⋯ : U[P]σ ⋯ₚ ρ ≡ U[P](σ·ₖρ)   U-⋯ₚ : U[P⋯ₚρ]σ ≡ U[P](ρ·ₖσ)   U-cong  (TranslationProperties)
--   UB-cong / UB-cong-─→ / UB-ext (push ∥ through the φ-nest) / UB-nat  (TranslationProperties/NuExtrusion)
--   UB-flat / UBflat-assoc / Flags / canonₛ / canonₛ-nat / φ-ext* / φ^-swap  (Flatten/BlockPermutation/this file)
--   the untyped reduction congruences RU-Res/RU-Sync/RU-Par/RU-Struct  (Untyped reduction)
--
-- KEY STRUCTURAL FACTS (from studying Bisim.agda):
--   • syncs B = (#chains − 1), LENGTH-based (Bisim.agda:56-59) — INDEPENDENT of the
--     head borrow-count.  So syncs(suc b₁∷B₁) ≡ syncs(b₁∷B₁) DEFINITIONALLY:
--     drop/lsplit/rsplit preserve the φ-nest DEPTH; only the front Ub-chain / a flag
--     changes.  cc₂ and the leaf substitutions in those goals are then defeq across
--     LHS/RHS (only the head bind-group and U[P]/U[P⋯ρ] differ).
--   • UB[ c ∷ B@(_∷_) ] = φ ((0F ↦ ϕ[c]) ∥ UB[B] … (leaf does Ub[c] …))   (Bisim:69-76):
--     ONE φ + flag ϕ[c] per chain-junction; the chain's Ub[c] (c sequenced triples)
--     lives in the *innermost* leaf.  ϕ[zero]=set, ϕ[suc _]=unset (Bisim:32-34).
--   • UB[ c ∷ [] ] = Ub[c] …  — a single chain has NO φ (syncs=0).
--
-- PER-OP GUIDANCE (typed rule = TypedMW, untyped = Untyped reduction):
--
-- R-Drop  (𝐓R.R-Drop, ν (suc b₁∷B₁) B₂ (⟪E⋯weakenᵣ[drop·(`0F)]⟫ ∥ P⋯weakenᵣ)
--          ─→ ν (b₁∷B₁) B₂ (⟪E[unit]⟫ ∥ P)) ↦ 𝐔R.RU-Drop
--   (φ((0F↦unset) ∥ (⟪F[drop·((unit⊗x)⊗0F)]⟫ ∥ P)) ─→ φ((0F↦set) ∥ (⟪F[unit]⟫ ∥ P))).
--   ⚠ HARDER THAN IT LOOKS — needs THREE things:
--   (a) ≋-RECONCILE so the dropped channel's flag and the drop-redex sit under ONE φ.
--       The first chain's flag is the OUTERMOST φ but the drop-thread is in the
--       INNERMOST leaf → use φ-ext*/∥-comm/∥-assoc (UB-ext-style) to co-locate them.
--   (b) CASE ON b₁: RU-Drop flips unset→set unconditionally, but the RHS front flag is
--       ϕ[b₁] = set ONLY if b₁=0, else still unset.  So RU-Drop matches the b₁=0 case
--       (dropping the LAST borrow) directly; for b₁≥1 the flag must STAY unset — verify
--       in the paper (sec/translation.tex, rules/translated-system.tex) what drop means
--       with borrows remaining; it likely shortens the front Ub-chain WITHOUT a flag
--       flip, which may need a different reconciliation (or the typed R-Drop is only
--       ever applied at the last borrow — check TypedMW typing).  DO NOT GUESS the
--       paper semantics — confirm first.
--   (c) CASE ON B₁ empty/non-empty (B₁=[] ⇒ no φ ⇒ no flag ⇒ separate handling).
--
-- R-Acq  (𝐓R.R-Acq, ν (zero∷suc b₁∷B₁) B₂ (⟪E[acq·(`0F)]⟫ ∥ P)
--          ─→ ν (suc b₁∷B₁) B₂ (⟪E[`zero]⟫ ∥ P)) ↦ 𝐔R.RU-Acquire
--   (ν(φ((0F↦set) ∥ (⟪F[acq·((0F⊗suc x)⊗e)]⟫ ∥ P))) ─→ ν(⟪F[(unit⊗x)⊗e]⟫ ∥ P)).
--   Dual to drop: consumes a `set` sync (the `zero∷` front = ϕ[zero]=set).  The
--   `zero∷suc b₁∷B₁ → suc b₁∷B₁` removes the leading zero-chain; acq returns a channel
--   (so a ν is needed, hence RU-Acquire has the ν+φ).  Same ≋-co-location as drop,
--   but the flag is concretely `set` (ϕ[zero]) so NO b₁ case-split mismatch — likely
--   the most tractable of the five.  START HERE to validate the co-location pattern.
--
-- R-LSplit (𝐓R.R-LSplit, ν (B₁++suc b₁∷B₂) B (⟪E[lsplit·(`𝐒.inj 0F)]⟫ ∥ P)
--           ─→ ν (B₁++suc(suc b₁)∷B₂) B (⟪E⋯𝐒.lwk[(`𝐒.inj 0F)⊗(`𝐒.inj 1F)]⟫ ∥ P⋯𝐒.lwk))
--   ↦ 𝐔R.RU-LSplit (NOW has its ν binder restored: ν(⟪F[lsplit·((e₁⊗x)⊗e₂)]⟫ ∥ P)
--   ─→ ν(⟪F[((e₁⊗x)⊗unit)⊗((unit⊗x)⊗e₂)]⟫ ∥ P)).  syncs preserved (chain count same,
--   borrow grows).  Work: the SplitRenamings 𝐒.inj/𝐒.lwk are Fin.cast-heavy (TypedMW
--   SplitRenamings module); reconcile the φ-nest locally (the split chain) + the cast
--   bookkeeping.  Medium-high effort.
--
-- R-RSplit (𝐓R.R-RSplit, … ν (B₁++1∷suc b₁∷B₂) B … with 𝐒.rwk) ↦ 𝐔R.RU-RSplit
--   (adds a fresh φ : ν(⟪F[rsplit·…]⟫ ∥ P) ─→ ν(φ((0F↦unset) ∥ (⟪F⋯weakenᵣ[…]⟫ ∥ P⋯weakenᵣ)))).
--   Like LSplit but adds a chain ⇒ syncs +1 ⇒ a new φ to introduce (matches the fresh
--   unset sync).  Higher effort than LSplit.
--
-- R-Com  (𝐓R.R-Com, ν (suc b₁∷B₁)(suc b₂∷B₂) ((⟪E₁⋯wkρ[send·((`0F)⊗(e⋯wkρ))]⟫
--          ∥ ⟪E₂⋯wkρ[recv·(`recv-idx)]⟫) ∥ P⋯wkρ) ─→ ν (b₁∷B₁)(b₂∷B₂) ((⟪E₁[unit]⟫
--          ∥ ⟪E₂[e]⟫) ∥ P)) ↦ 𝐔R.RU-Com.  HARDEST: two communicating threads, the
--   recv-side index is the cast `Fin.cast (sym (+-assoc …)) (sum (suc b₁∷B₁) ↑ʳ 0F)`
--   (the dual endpoint), value e transferred across the ν.  Both endpoints' front
--   borrows decrease.  Do this LAST.
-- ════════════════════════════════════════════════════════════════════════════
sim→ σ Vσ (𝐓R.R-Com _)       = {!   !}
sim→ σ Vσ 𝐓R.R-LSplit        = {!   !}
sim→ σ Vσ 𝐓R.R-RSplit        = {!   !}
sim→ σ Vσ 𝐓R.R-Drop          = {!    !}
sim→ σ Vσ 𝐓R.R-Acq           = {!   !}
sim→ {m = m} {n = n} σ Vσ (𝐓R.R-Close {E₁ = E₁} {E₂ = E₂}) =
  𝐔R.RU-Struct
    (≡→≋ (cong 𝐔.ν (cong₂ 𝐔._∥_ (thr ‼ E₁ 0F t₁ (⋯-id t₁ {ϕ = weaken* ⦃ Kᵣ ⦄ 0} (λ _ → refl))) (thr ⁇ E₂ 1F t₂ refl))))
    (𝐔R.RU-Close (frame*-⋯ E₁ σ Vσ) (frame*-⋯ E₂ σ Vσ))
    (≡→≋ (sym (cong₂ 𝐔._∥_ (cong 𝐔.⟪_⟫ (frame-plug* E₁ σ Vσ)) (cong 𝐔.⟪_⟫ (frame-plug* E₂ σ Vσ)))))
  where
    e∅ : ∀ {N} → 0 →ₛ N
    e∅ = λ ()
    Ve∅ : ∀ {N} → VSub (e∅ {N})
    Ve∅ = λ ()
    t₁ : Tm (2 + n)
    t₁ = (K `unit ⊗ (` 0F)) ⊗ K `unit
    t₂ : Tm (2 + n)
    t₂ = (K `unit ⊗ (` 1F)) ⊗ K `unit
    σ₁ : 1 →ₛ (2 + n)
    σ₁ = (t₁ ∷ₛ e∅) ++ₛ e∅
    σ₂ : 1 →ₛ (2 + n)
    σ₂ = (t₂ ∷ₛ e∅) ++ₛ e∅
    Bσ : m →ₛ (2 + n)
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    σ′ : (1 + 1 + m) →ₛ (2 + n)
    σ′ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂) ++ₛ Bσ
    Vσ₁ : VSub σ₁
    Vσ₁ = ++ₛ-VSub {σ₁ = t₁ ∷ₛ e∅} (∷ₛ-VSub {t = t₁} (V-⊗ (V-⊗ V-K V-`) V-K) Ve∅) Ve∅
    Vσ₂ : VSub σ₂
    Vσ₂ = ++ₛ-VSub {σ₁ = t₂ ∷ₛ e∅} (∷ₛ-VSub {t = t₂} (V-⊗ (V-⊗ V-K V-`) V-K) Ve∅) Ve∅
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = (λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ σ₂}
            (++ₛ-VSub {σ₁ = λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ 0} (weaken-VSub 0 Vσ₁) Vσ₂)
            (weaken-VSub 0 (weaken-VSub 0 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0) (weaken* ⦃ Kᵣ ⦄ 0)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 0 ·ₖ weaken* ⦃ Kᵣ ⦄ 0)
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_
      ( frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
      ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)) weakenEq
      ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))) )
      (frameEqA E*)
    thr : (pol : Pol) (E* : Frame* m) (x : 𝔽 (1 + 1 + m)) (t : Tm (2 + n)) → σ′ x ≡ t →
          𝐔.⟪ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2 [ K (`end pol) · (` x) ]*) ⋯ σ′ ⟫
          ≡ 𝐔.⟪ (frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end pol) · t ]* ⟫
    thr pol E* x t eq =
      cong 𝐔.⟪_⟫ (frame-plug* (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E*) (cong (K (`end pol) ·_) eq))
sim→ σ Vσ (𝐓R.R-Bind {B₁} {B₂} red) =
  𝐔R.RU-Res (UB-cong-─→ B₁ (K `unit , 0F , K `unit) (V-K , V-K)
    (λ σ₁ Vσ₁ → UB-cong-─→ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) (V-K , V-K)
      (λ σ₂ Vσ₂ → sim→ _
        (++ₛ-VSub (++ₛ-VSub (weaken-VSub (syncs B₂) Vσ₁) Vσ₂)
                  (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ))))
        red)))
