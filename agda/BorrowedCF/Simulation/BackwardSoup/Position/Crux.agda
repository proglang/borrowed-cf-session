{-# OPTIONS --allow-unsolved-metas #-}

-- | Phase 3, THE CRUX (`BackwardSoup/PLAN.md` §9, P3).
--
--   `Position.agda` STATES the metatheorem (`ImpureRedexHead`,
--   `PairArgRedexHead`, `DropFirstGroupSingleton`, `AcqNonFirstGroupHead` --
--   RENAMED from `AcqSecondGroupHead`, see its own doc comment) and proves
--   all its combinatorial ingredients; it loads with 0 goals.  This module
--   is the proof attempt.
--
--   CURRENT STATE (this pass).  `acq-non-first-group-head` (`?3`/`?4`) and
--   `drop-first-group-singleton` (`?2`) are FULLY PROVED -- the latter
--   reduces cleanly to `impure-redex-head` (`?0`), no further gap of its
--   own.  `impure-redex-head` (`?0`) and `pair-arg-redex-head` (`?1`)
--   remain OPEN.  Exactly ONE piece of genuinely NEW theory is missing and
--   is isolated as a single hole, `nonFirstGroup-interior-noAcq` (§1a): a
--   front-atom-peel fact for `acq`, dual to what `Types/AtomUnsnoc.agda`
--   built for the LAST atom of a `;`-chain, needed by BOTH the "different
--   group" branch of `?0`/`?1`'s case (iv) (Position.agda's proof sketch)
--   and (in its easier, NoAcq-only direction) `acq-non-first-group-head`
--   below.  `?0`/`?1` ADDITIONALLY need, for their "same group, but not
--   first" branch, that the group's own head is not known `¬ Mobile` (it is
--   expected TO carry the acq), so `before-mono-≼` cannot be invoked
--   against it the way `Position.first-group-¬mobile` lets it be invoked
--   for the first group -- a second, related gap, not yet isolated as its
--   own lemma.  The "same group, first group" case of `?0`/`?1` (case iii
--   proper) is NOT attempted here: it needs the `Δ`-structure `TP-Res`
--   prescribes for the binder's body threaded through `before-⋯ᵣ` and
--   `Position.ContextOrder.ctx-¬before-direct`/`-pair`, all doable with
--   already-proved ingredients (§1b's `TypeWalk` is the template for the
--   `Binder.below`-walk this needs), but it was not reached in this pass.
--
--   §1a-§1d below are NEW, general-purpose, PROVED infrastructure (no
--   holes except the one named above): `first-group-noAcq` (a witness-
--   exposing generalisation of `Position.first-group-¬mobile`), `TypeWalk`
--   (a generic walker propagating a `≃`-fact about a fixed global variable
--   from its own thread's typing up through a resolved `Binder`'s
--   `below`), `acq-handle-≃acq`/`Q-acq-type`/`Q-drop-type` (domain
--   extraction for `acq`/`drop`, mirroring `Support.Theorems.DropShape`'s
--   `drop-handle-≃ret`), and `dropGroupShape` (`Support.Theorems.
--   DropShape`'s `drop-b₁-zero`/`drop-B₁-cons` argument, generalised off
--   its canonical `0F` position to work at any `BindCtx`-resolved index).
--
--   PROVED HERE ORIGINALLY, as the (iv)-ingredient: for the impure
--   constants whose domain session carries no `acq` -- `discard : ⟨ skip ⟩`,
--   `drop : ⟨ ret ⟩`, `recv : ⟨ msg ⁇ T ⟩`, `end p : ⟨ end p ⟩` -- the
--   consumed handle is NOT MOBILE, hence `∥′-tm-;` can never reorder it and
--   `before-mono-≼` applies to it directly.  (`select`/`branch` consume a
--   `⟨ brn p s₁ s₂ ⟩` whose branches are arbitrary, so `NoAcq` is not
--   available for them; `send` consumes a PAIR, and `Position.pair-arg-not-var`
--   is what handles that case.)
module BorrowedCF.Simulation.BackwardSoup.Position.Crux where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base

import BorrowedCF.Processes.Typed as 𝐓

open import BorrowedCF.Simulation.Support.InvFrame using (arg-type)
open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; ¬noRet-ret; noRet-;-fst
        ; RetTip; noRet-front-cons; retTip-Sc-skips; retTip-≃ )
open import BorrowedCF.Simulation.Support.Theorems.DropShape
  using (drop-handle-≃ret)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug)
open import BorrowedCF.Simulation.BackwardSoup.Position

open 𝐓 using
  ( BindGroup; BindCtx; BindCtx′; AcqHeadCtx; structBinder; structNSeq
  ; last; cons-ret/acq; cons-acq; nil; cons
  ; _;_⊢ₚ_; inv-ν; inv-∥; inv-⟪⟫ )

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
-- 1a.  NoAcq witnesses.  `first-group-noAcq` generalises
--      `Position.first-group-¬mobile` to expose the WITNESS session,
--      needed to contradict `Γ ﹫ x ≃ ⟨ acq ; s ⟩` directly (via
--      `noAcq-;-fst` / `¬noAcq-acq`) without going through
--      `Mobile`'s `Bounded` side condition at all.
--      `nonFirstGroup-interior-noAcq` is THE GAP: see its documentation
--      below.

private
  bindCtx′-noAcq : ∀ {n} {Γ : Ctx n} {s : 𝕊 0} → NoAcq s → BindCtx′ s Γ →
    (z : 𝔽 n) → Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ z) ≃ ⟨ s′ ⟩) × NoAcq s′
  bindCtx′-noAcq NAs (cons s₁ s₂ _ s-split C) zero =
    s₁ , ≃-refl , noAcq-;-fst (noAcq-≃ (≃-sym s-split) NAs)
  bindCtx′-noAcq NAs (cons s₁ s₂ _ s-split C) (suc z) =
    bindCtx′-noAcq (noAcq-;-snd (noAcq-≃ (≃-sym s-split) NAs)) C z

  first-group-noAcq :
    ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
    New s → BindCtx (s ; end p) B Γ →
    ∀ {i} (g : GroupOf B i) → groupIndex g ≡ 0 →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
  first-group-noAcq N (last C) {i} g idx = bindCtx′-noAcq (new-end⇒noAcq N) C i
  first-group-noAcq {Γ = Γ} N (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front _ _)
    (head-group B′ q) idx =
    let s′ , eq , na = bindCtx′-noAcq (noAcq-front (new-end⇒noAcq N) s≃) front q
    in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ˡ Γ₁ Γ₂ q)) eq , na
  first-group-noAcq N (cons-acq C _) (head-group B′ ()) idx

-- ★ THE GAP ★ (Position.agda's proof sketch (iv); the module-level comment
-- at the top of this file cites the tools this needs: `atom-;-unsnoc` /
-- `atomKind≢⇒≄-;ʳ` of `Types/AtomUnsnoc.agda` / `Types/AtomSnoc.agda`.
--
-- Precisely what is missing.  `BindCtx (acq ; g) B Γ` (`g` NoAcq) is what
-- a `cons-ret/acq`/`cons-acq` node hands to the group list AFTER crossing
-- exactly one `acq` boundary (`cons-ret/acq`'s own recursive premise is
-- literally `BindCtx (acq ; s₂) B Γ₂`; `cons-acq`'s is
-- `BindCtx (acq ; s) B Γ`).  For a handle NOT at offset 0 of its
-- group (`grp`), we want `Γ ﹫ i` NoAcq.  A `BindCtx′`-chain argument
-- (`bindCtx′-noAcq` above) gets this INSTANTLY from `NoAcq` of the group's
-- own governing session `s₁ᶜ ; ret` -- but here the governing session
-- is `acq ; g`, NOT NoAcq, and splitting it (`cons-ret/acq`'s own
-- `s≃ : s₁ᶜ ; s₂ᶜ ≃ acq ; g`) does not by itself pin the acq to
-- `s₁ᶜ`'s own front: nothing rules out `s₁ᶜ` being entirely `Skips` (or more
-- generally NoAcq) with the acq "leaking" into `s₂ᶜ` instead, UNLESS one
-- shows that a chain equivalent to `acq ; g` (`g` NoAcq) can only be
-- re-split with the acq landing ENTIRELY inside one factor, at THAT
-- factor's own front -- exactly the front-peel dual of what
-- `Types/AtomUnsnoc.agda` builds for the LAST atom of a chain
-- (`Snoc`/`atom-;-unsnoc`), which this attempt did not have time to
-- build symmetrically for the FIRST atom.  (`AcqHeadCtx`, the OTHER
-- premise `cons-ret/acq`/`cons-acq` carry, states only `¬ Skips` of the
-- head channel -- enough to rule out `discard`'s `⟨ skip ⟩` domain
-- directly via `Skips`-≃-invariance, but NOT enough for `recv`/`end`/
-- `send`'s domains, real non-skip non-acq atoms.)
--
-- What IS available and used below: `NoAcq` is exactly conjunctive over
-- `_;_` (both directions -- the constructor and
-- `noAcq-;-fst`/`-snd`), and ≃-invariant (`noAcq-≃`), so the missing
-- piece is precisely a chain-recombination lemma, not a new predicate.
nonFirstGroup-interior-noAcq :
  ∀ {B} {Γ : Ctx (sum B)} {g : 𝕊 0} → NoAcq g → BindCtx (acq ; g) B Γ →
  ∀ {i} (grp : GroupOf B i) → 0 Nat.< groupOffset grp →
  Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
nonFirstGroup-interior-noAcq = {!!}

-- The composite for a LATER group's interior (offset > 0): descend past
-- however many groups precede `grp`'s own group (`⊢ᴮ` forbids more than the
-- very first group being empty, so at most one real `acq`-crossing sits
-- between the top and any given group), landing on `nonFirstGroup-
-- interior-noAcq` once `groupIndex grp` is confirmed `> 0`.  Only the
-- "index > 0, offset ≡ 0" case (the group HEAD itself) is left unaddressed
-- -- `impure-redex-head`/`pair-arg-redex-head` need it too (Position.agda's
-- case (iv), "if x IS that head"); `acq-non-first-group-head` below does
-- not, since it already KNOWS (from `acq`'s own typing rule) that ITS
-- target carries the acq.
private
  laterGroup-interior-noAcq :
    ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} → New s →
    BindCtx (s ; end p) B Γ →
    ∀ {i} (grp : GroupOf B i) →
    0 Nat.< groupIndex grp → 0 Nat.< groupOffset grp →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
  laterGroup-interior-noAcq N (last C) (head-group B′ j) () 0<off
  laterGroup-interior-noAcq {Γ = Γ} N
    (cons-ret/acq s₁ {s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest _)
    (next-group n g′) 0<gi 0<off =
    let s′ , eq , na =
          nonFirstGroup-interior-noAcq
            (noAcq-;-snd (noAcq-≃ (≃-sym s≃) (new-end⇒noAcq N))) rest g′ 0<off
    in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) eq , na
  laterGroup-interior-noAcq N (cons-acq C _) (next-group .0 g′) 0<gi 0<off =
    nonFirstGroup-interior-noAcq (new-end⇒noAcq N) C g′ 0<off

------------------------------------------------------------------------
-- 1b.  A generic walker: propagate a `≃`-fact about the fixed global
--      variable `x` from the deepest typing of `Q` (the thread it sits in)
--      up through a `ProcessContext`.  The channel context `Γ` is untouched
--      by `TP-Par`/`TP-Weaken` (only the struct changes) and only GROWS, by
--      prefixing, at `TP-Res`; `weakenThrough` tracks exactly which
--      position in the growing vector is `x`, so the fact transports
--      unconditionally -- no linearity/`Mobile` side condition needed,
--      unlike `Position.ContextOrder`'s `count`/`before` walk.

private
  module TypeWalk {k : ℕ} (Q : 𝐓.Proc k) (x : 𝔽 k) (wrap : 𝕊 0 → 𝕊 0)
    (Q-type : ∀ {Γ : Ctx k} {γ : Struct k} →
              Γ ; γ ⊢ₚ Q → Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ wrap s′ ⟩))
    where

    ctx-type :
      ∀ {n} (below : ProcessContext k n) {Γ : Ctx n} {γ : Struct n} →
      Γ ; γ ⊢ₚ plug below Q →
      (y : 𝔽 n) → weakenThrough below y ≡ x →
      Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ y) ≃ ⟨ wrap s′ ⟩)
    ctx-type hole ⊢P y refl = Q-type ⊢P
    ctx-type (par-left ctx P₂) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , ⊢left , _ = ctx-type ctx ⊢left y eq
    ctx-type (par-right P₁ ctx) ⊢P y eq with inv-∥ ⊢P
    ... | _ , _ , _ , _ , ⊢right = ctx-type ctx ⊢right y eq
    ctx-type (bind B₁ B₂ ctx) {Γ} ⊢P y eq with inv-ν ⊢P
    ... | Γ₁ , Γ₂ , _ , _ , _ , _ , _ , _ , _ , ⊢body =
      let s′ , eq′ = ctx-type ctx ⊢body ((sum B₁ + sum B₂) ↑ʳ y) eq
      in s′ , subst (_≃ ⟨ wrap s′ ⟩) (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ y) eq′

------------------------------------------------------------------------
-- 1c.  `acq`'s domain, extracted (mirrors `DropShape.drop-handle-≃ret`),
--      and the small arithmetic/type glue `acq-non-first-group-head` needs.

private
  fn-acq-dom : ∀ {n} {Γ : Ctx n} {β : Struct n} {Tᵈ U a ϵ} →
    Γ ; β ⊢ K `acq ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] (⟨ acq ; s ⟩ ≃ Tᵈ)
  fn-acq-dom (T-Const `acq) = _ , ≃-refl
  fn-acq-dom (T-Conv (dom≃ `→ _) _ d) = let s , eq = fn-acq-dom d in s , ≃-trans eq dom≃
  fn-acq-dom (T-Weaken _ d) = fn-acq-dom d

  acq-handle-≃acq : ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {U ϵ} →
    Γ ; γ ⊢ K `acq ·¹ (` x) ∶ U ∣ ϵ →
    Σ[ s ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; s ⟩)
  acq-handle-≃acq (T-AppUnr _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in s , ≃-trans (arg-type ⊢arg) (≃-sym eq)
  acq-handle-≃acq (T-AppLin _ _ ⊢fn ⊢arg) =
    let s , eq = fn-acq-dom ⊢fn in s , ≃-trans (arg-type ⊢arg) (≃-sym eq)
  acq-handle-≃acq (T-Conv _ _ d) = acq-handle-≃acq d
  acq-handle-≃acq (T-Weaken _ d) = acq-handle-≃acq d

  Q-acq-type : ∀ {k} (E : Frame* k) (x : 𝔽 k) →
    ∀ {Γ : Ctx k} {γ : Struct k} →
    Γ ; γ ⊢ₚ 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ acq ; s′ ⟩)
  Q-acq-type E x ⊢Q =
    let ⊢e = inv-⟪⟫ ⊢Q
        _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole = ⊢[]*⁻¹ E (K `acq ·¹ (` x)) ⊢e
    in acq-handle-≃acq ⊢hole

  Q-drop-type : ∀ {k} (E : Frame* k) (x : 𝔽 k) →
    ∀ {Γ : Ctx k} {γ : Struct k} →
    Γ ; γ ⊢ₚ 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
    Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ x) ≃ ⟨ ret ⟩)
  Q-drop-type E x ⊢Q =
    let ⊢e = inv-⟪⟫ ⊢Q
        _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢hole = ⊢[]*⁻¹ E (K `drop ·¹ (` x)) ⊢e
    in ret , drop-handle-≃ret ⊢hole

  ⟨⟩≃′ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃′ ⟨ eq ⟩ = eq

  -- `x`'s ACTUAL session, `≃ ⟨ acq ; s ⟩`, cannot ALSO be NoAcq.
  acq-vs-noAcq : ∀ {s a : 𝕊 0} → NoAcq a → a ≃ acq ; s → ⊥
  acq-vs-noAcq NAa eq = ¬noAcq-acq (noAcq-;-fst (noAcq-≃ eq NAa))

  0≢⇒0< : ∀ {n : ℕ} → n ≢ 0 → 0 Nat.< n
  0≢⇒0< {zero} ne = ⊥-elim (ne refl)
  0≢⇒0< {suc n} ne = Nat.s≤s Nat.z≤n

------------------------------------------------------------------------
-- 1d.  `drop`'s group shape, generalised off `Support.Theorems.DropShape`'s
--      canonical `0F` position.  This is PURELY `BindCtx`-level (no term
--      syntax at all): the ORIGINAL `drop-b₁-zero`/`drop-B₁-cons` interleave
--      this argument with `strengthen-frame`/`inv-⟪⟫`/`inv-∥` purely to dig
--      the hole's typing (`Γ ﹫ 0F ≃ ⟨ ret ⟩`) out of the canonical term
--      shape `ν (suc b₁ ∷ B₁) B₂ (⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫
--      ∥ (P ⋯ₚ weakenᵣ))`; once that fact is available some OTHER way (here:
--      `Position.binderTyping` + §1b's `TypeWalk`, at whatever index `resolve`
--      names, not literally `0F`), the REST of the argument is identical.
--      Ready to discharge `?2` once `?0` supplies `HeadOfFirstGroup`.

private
  dropGroupShape :
    ∀ {b₁ B′} {Δ₁ : Ctx (sum (suc b₁ ∷ B′))} {s p} → New s →
    BindCtx (s ; end p) (suc b₁ ∷ B′) Δ₁ →
    (Δ₁ ﹫ (zero ↑ˡ sum B′)) ≃ ⟨ ret ⟩ →
    (b₁ ≡ 0) × (B′ ≢ [])
  dropGroupShape {b₁} {[]} N (last (cons s₁ s₂ ¬sk s-split rest)) head≃ret =
    ⊥-elim (¬noRet-ret (noRet-≃ (⟨⟩≃′ head≃ret)
      (noRet-;-fst (noRet-≃ (≃-sym s-split) (NoRet._;_ (new⇒noRet N) NoRet.end)))))
  dropGroupShape {zero} {c₀ ∷ B″} N C head≃ret = refl , (λ ())
  dropGroupShape {suc b₁} {c₀ ∷ B″} N
    (cons-ret/acq sh {s₂} frontSplit _ (cons s₁ʰ s₂ʰ ¬sk₁ s≃₁ (cons _ _ ¬skTail _ _)) _ _)
    head≃ret =
    ⊥-elim (¬skTail (retTip-Sc-skips retTipBorrow (⟨⟩≃′ head≃ret)))
    where
    noRet-sh : NoRet sh
    noRet-sh = noRet-;-fst (noRet-≃ (≃-sym frontSplit) (NoRet._;_ (new⇒noRet N) NoRet.end))
    retTipBorrow : RetTip (s₁ʰ ; s₂ʰ)
    retTipBorrow = retTip-≃ (≃-sym s≃₁) (noRet-front-cons noRet-sh)

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
--     `¬unr-handle`                             -- `≼` neither creates a `;`
--                                                  nor changes multiplicities;
--   * `Position.focusTyping-binders`/
--     `Position.binderTyping`                   -- the `TP-Res` payload of the
--                                                  owning binder;
--   * `ThreadOrder.thread-¬before`/
--     `thread-pair-¬before`, `ContextOrder.ctx-¬before-direct`/
--     `-pair`                                   -- Phase 4a: the ACTUAL
--                                                  structure the derivation
--                                                  forces, walked down to the
--                                                  redex thread.
--
-- `acq-non-first-group-head` (`?3`, restated -- see `Position.agda`'s
-- `AcqNonFirstGroupHead`) is PROVED below, modulo the one isolated gap
-- `nonFirstGroup-interior-noAcq` (§1a): it needs only the "offset > 0 ⟹
-- NoAcq" half of Position.agda's case (iv), because `x`'s OWN acq-typing
-- comes directly from `acq`'s typing rule (§1c/§1b), not from a forward
-- "group head ⟹ acq-typed" derivation the OTHER three holes still need.
--
-- `impure-redex-head` / `pair-arg-redex-head` / `drop-first-group-singleton`
-- remain OPEN.  Besides `nonFirstGroup-interior-noAcq`, they additionally
-- need, for the "x IS the head of a later group" branch of case (iv), the
-- FORWARD direction ("later-group head ⟹ acq-typed") that
-- `acq-non-first-group-head` sidesteps; AND, for case (iii) (same group)
-- when the group is NOT the first, `Position.group-head-before`'s partner
-- handle -- the group's own head -- is not known `¬ Mobile` (it is, in
-- fact, expected TO carry the acq), so `before-mono-≼` cannot be invoked
-- against it the way `first-group-¬mobile` lets it be invoked for the
-- first group.  Both gaps trace back to the same missing front-atom-peel
-- fact recorded in `nonFirstGroup-interior-noAcq`'s documentation.  Beyond
-- that, wiring `Position.binderTyping`'s payload down to
-- `E [ K c ;¹ (` x) ]*`'s own typing needs a walk of `Binder.below`
-- exactly like §1b's `TypeWalk` (for `?0`/`?1`, this time tracking `count`/
-- `before` as `Position.ContextOrder`'s own `Walk` already does -- it is
-- the RIGHT tool, just not yet driven from a resolved `Binder`), or
-- `Support.Theorems.DropShape`'s `NoRet`/`RetTip` machinery generalised off
-- its canonical `0F` position (for `?2`, which otherwise needs nothing
-- beyond `?0`).

impure-redex-head : ImpureRedexHead
impure-redex-head = {!!}   -- HOLE 1

pair-arg-redex-head : PairArgRedexHead
pair-arg-redex-head = {!!} -- HOLE 2

drop-first-group-singleton : DropFirstGroupSingleton
drop-first-group-singleton {ctx = ctx} {E = E} {x = x} ⊢plug
  with resolve ctx x
... | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  with impure-redex-head ⊢plug `drop
... | gi≡0 , off≡0
  with binderTyping bnd 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with TypeWalk.ctx-type 𝐓.⟪ E [ K `drop ·¹ (` x) ]* ⟫ x (λ _ → ret) (Q-drop-type E x)
         below ⊢body (local ↑ˡ mid) index-eq
... | _ , eqRet
  with sideOf B₁ B₂ local
... | inl i
  with groupOf B₁ i | gi≡0 | off≡0
... | head-group B′ zero | _ | _ =
  let localEq = V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ ((zero ↑ˡ sum B′) ↑ˡ sum B₂) ■ V.lookup-++ˡ Γ₁ Γ₂ (zero ↑ˡ sum B′)
      b₁≡0 , B′≢[] = dropGroupShape N C (subst (_≃ ⟨ ret ⟩) localEq eqRet)
  in cong suc b₁≡0 , B′≢[]
... | head-group B′ (suc q) | _ | ()
... | next-group b g′ | () | _
drop-first-group-singleton {ctx = ctx} {E = E} {x = x} ⊢plug
  | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  | gi≡0 , off≡0
  | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  | _ , eqRet
  | inr i
  with groupOf B₂ i | gi≡0 | off≡0
... | head-group B″ zero | _ | _ =
  let localEq = V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (sum B₁ ↑ʳ (zero ↑ˡ sum B″)) ■ V.lookup-++ʳ Γ₁ Γ₂ (zero ↑ˡ sum B″)
      b₁≡0 , B″≢[] = dropGroupShape (new-dual N) C′ (subst (_≃ ⟨ ret ⟩) localEq eqRet)
  in cong suc b₁≡0 , B″≢[]
... | head-group B″ (suc q) | _ | ()
... | next-group b g′ | () | _

-- `?4` (restated from `AcqSecondGroupHead`, see `Position.agda`), PROVED
-- modulo `nonFirstGroup-interior-noAcq` (§1a) -- see the header comment
-- above for why this one hole does not also block on the "later-group
-- head ⟹ acq-typed" direction the other three still need.
acq-non-first-group-head : AcqNonFirstGroupHead
acq-non-first-group-head {ctx = ctx} {E = E} {x = x} ⊢plug
  with resolve ctx x
... | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  with binderTyping bnd 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ ⊢plug
... | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with TypeWalk.ctx-type 𝐓.⟪ E [ K `acq ·¹ (` x) ]* ⟫ x (λ s → acq ; s) (Q-acq-type E x)
         below ⊢body (local ↑ˡ mid) index-eq
... | sAcq , eqAcq
  with sideOf B₁ B₂ local
... | inl i
  with groupOf B₁ i
... | g
  with V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (i ↑ˡ sum B₂) ■ V.lookup-++ˡ Γ₁ Γ₂ i
... | localEq
  with subst (_≃ ⟨ acq ; sAcq ⟩) localEq eqAcq
... | eqAcq₁
  with groupIndex g Nat.≟ 0
... | yes gi≡0 =
  let s′ , eq′ , na′ = first-group-noAcq N C g gi≡0
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₁)))
... | no gi≢0
  with groupOffset g Nat.≟ 0
... | yes off≡0 = 0≢⇒0< gi≢0 , off≡0
... | no off≢0 =
  let s′ , eq′ , na′ = laterGroup-interior-noAcq N C g (0≢⇒0< gi≢0) (0≢⇒0< off≢0)
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₁)))
acq-non-first-group-head {ctx = ctx} {E = E} {x = x} ⊢plug
  | bnd@(binder {mid} B₁ B₂ above below dec local index-eq)
  | Γ′ , γ′ , Γ₁ , Γ₂ , s , p , Γ′-S , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  | sAcq , eqAcq
  | inr i
  with groupOf B₂ i
... | g
  with V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ′ (sum B₁ ↑ʳ i) ■ V.lookup-++ʳ Γ₁ Γ₂ i
... | localEq
  with subst (_≃ ⟨ acq ; sAcq ⟩) localEq eqAcq
... | eqAcq₂
  with groupIndex g Nat.≟ 0
... | yes gi≡0 =
  let s′ , eq′ , na′ = first-group-noAcq (new-dual N) C′ g gi≡0
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₂)))
... | no gi≢0
  with groupOffset g Nat.≟ 0
... | yes off≡0 = 0≢⇒0< gi≢0 , off≡0
... | no off≢0 =
  let s′ , eq′ , na′ = laterGroup-interior-noAcq (new-dual N) C′ g (0≢⇒0< gi≢0) (0≢⇒0< off≢0)
  in ⊥-elim (acq-vs-noAcq na′ (⟨⟩≃′ (≃-trans (≃-sym eq′) eqAcq₂)))
