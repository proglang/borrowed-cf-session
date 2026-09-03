{-# OPTIONS --allow-unsolved-metas #-}

-- | Phase 3, THE CRUX (`BackwardSoup/PLAN.md` §9, P3).
--
--   `Position.agda` STATES the metatheorem (`ImpureRedexHead`,
--   `PairArgRedexHead`, `DropFirstGroupSingleton`, `AcqSecondGroupHead`) and
--   proves all its combinatorial ingredients; it loads with 0 goals.  This
--   module is the proof attempt.  It carries FOUR CLEARLY MARKED HOLES -- the
--   four statements themselves -- and it is the only module of Phase 3 that
--   needs `--allow-unsolved-metas`.
--
--   What is missing is not any of the ingredients but the GLUE, which needs
--   Phase 4 (`Canonical.agda`): the derived structure of the located thread
--   has to be read off the `ProcessContext` (`TP-Par` on every `par-left` /
--   `par-right`, `TP-Res` on every `bind`) and compared, through
--   `before-mono-≼`, with the structure `TP-Res` prescribes for the binder
--   that owns the handle.  Each of the four holes is one instance of that
--   comparison.
--
--   PROVED HERE, as the (iv)-ingredient: for the impure constants whose
--   domain session carries no `acq` -- `discard : ⟨ skip ⟩`,
--   `drop : ⟨ ret ⟩`, `recv : ⟨ msg ⁇ T ⟩`, `end p : ⟨ end p ⟩` -- the
--   consumed handle is NOT MOBILE, hence `∥′-tm-;` can never reorder it and
--   `before-mono-≼` applies to it directly.  (`select`/`branch` consume a
--   `⟨ brn p s₁ s₂ ⟩` whose branches are arbitrary, so `NoAcq` is not
--   available for them; `send` consumes a PAIR, and `Position.pair-arg-not-var`
--   is what handles that case.)
module BorrowedCF.Simulation.BackwardSoup.Position.Crux where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Simulation.BackwardSoup.Position

open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The impure constants with an `acq`-free domain session.

data NoAcqDomain : Const → Set where
  `discard : NoAcqDomain `discard
  `drop    : NoAcqDomain `drop
  `recv    : NoAcqDomain `recv
  `end     : ∀ {p} → NoAcqDomain (`end p)

private
  fn-dom-noAcq :
    ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
    NoAcqDomain c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] (⟨ s ⟩ ≃ Tᵈ) × NoAcq s
  fn-dom-noAcq `discard (T-Const `discard) = skip , ≃-refl , skip
  fn-dom-noAcq `drop (T-Const `drop) = ret , ≃-refl , ret
  fn-dom-noAcq `recv (T-Const (`recv {T = T} _)) = msg ⁇ T , ≃-refl , msg
  fn-dom-noAcq `end (T-Const `end) = end _ , ≃-refl , end
  fn-dom-noAcq nd (T-Conv (dom≃ `→ _) _ d) =
    let s , eq , na = fn-dom-noAcq nd d in s , ≃-trans eq dom≃ , na
  fn-dom-noAcq nd (T-Weaken _ d) = fn-dom-noAcq nd d

  handle-noAcq-app :
    ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {d} {T ϵ} →
    NoAcqDomain c → Γ ; γ ⊢ K c ·⟨ d ⟩ (` x) ∶ T ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ s ⟩) × NoAcq s
  handle-noAcq-app nd (T-AppUnr _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppLin _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppLeft _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-AppRight _ _ ⊢fn ⊢arg) =
    let s , eq , na = fn-dom-noAcq nd ⊢fn in
    s , ≃-trans (arg-type ⊢arg) (≃-sym eq) , na
  handle-noAcq-app nd (T-Conv _ _ d) = handle-noAcq-app nd d
  handle-noAcq-app nd (T-Weaken _ d) = handle-noAcq-app nd d

-- PROVED.  The handle such a constant consumes is not mobile, so
-- `before-mono-≼` may be applied to it (ingredient (iii)/(iv) of the sketch).
impure-handle-noAcq :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {T ϵ} →
  NoAcqDomain c → Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ →
  Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ s ⟩) × NoAcq s
impure-handle-noAcq = handle-noAcq-app

impure-handle-¬mobile :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {T ϵ} →
  NoAcqDomain c → Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ → ¬ Mobile (Γ ﹫ x)
impure-handle-¬mobile nd ⊢app mob
  with impure-handle-noAcq nd ⊢app
... | s , eq , na = ¬mobile-noAcq na (mobile-≃ eq mob)

------------------------------------------------------------------------
-- 2.  THE FOUR HOLES.
--
-- Each is exactly the statement of the corresponding `Position.*` type.
-- Everything they need is available:
--
--   * `Position.resolve` / `Binder`             -- which `ν` binds the handle;
--   * `Position.structBinder-before`,
--     `Position.group-head-before`              -- the order the binder
--                                                  PRESCRIBES inside a group;
--   * `Position.first-group-¬mobile`,
--     `impure-handle-¬mobile` above             -- immobility of the handles
--                                                  the comparison mentions;
--   * `Position.before-mono-≼`, `count-≼-eq`,
--     `¬unr-handle`                             -- `≼` neither creates a `;`
--                                                  nor changes multiplicities;
--   * `Position.focusTyping-binders`            -- the `TP-Res` payload of the
--                                                  owning binder.
--
-- What is NOT yet available is the DERIVED structure of the located thread as
-- a function of the `ProcessContext` -- `TP-Par`/`TP-Res` inversion along the
-- whole path, plus `Reduction/Base.⊢[]*⁻¹` at the hole -- together with the
-- `Probes2` §7(e) observation that the only frames placing resources
-- `;`-before the hole (`app₁ v L`, `v ⊗□`) force the hole to be PURE, which
-- contradicts `ImpureHandleConst`.  That is Phase 4's job.

impure-redex-head : ImpureRedexHead
impure-redex-head = {!!}   -- HOLE 1

pair-arg-redex-head : PairArgRedexHead
pair-arg-redex-head = {!!} -- HOLE 2

drop-first-group-singleton : DropFirstGroupSingleton
drop-first-group-singleton = {!!}  -- HOLE 3

acq-second-group-head : AcqSecondGroupHead
acq-second-group-head = {!!}       -- HOLE 4
