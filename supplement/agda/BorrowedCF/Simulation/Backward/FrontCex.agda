-- | DECISIVE TEST for the backward front-firing obligation.
--
--   Question: for a well-typed com/close redex `ν B₁ B₂ P₀` (B₁ multi-block),
--   is the consumed handle FORCED by the global ordered+linear typing to be at
--   the FRONT of its bind group (`toℕ xS ≡ 0`, requiring `¬ Mobile (lookup 0F)`)?
--
--   ANSWER: NO — case (A).  The ν body is typed against the ;-chain binder
--   `structBinder B₁ ∥ … = (block-0) ; (block-1) ; …`.  The typing rule `∥′-tm-;`
--   makes `α ∥ β ≈ α ; β` WHENEVER `α` (the front) is `MobCx` (all-Mobile), and
--   `TP-Weaken` lifts a body along `≼-refl`.  So a body that uses a LATER channel
--   `β` in one thread and the MOBILE front `α` in a PARALLEL thread types against
--   the `;`-binder — the active com/close handle need NOT be at the front.
--
--   Hence `¬ Mobile (lookup Γ₁ 0F)` is GENUINELY FALSE for a well-typed com/close
--   redex whose front block is a Mobile (acq-headed, i.e. dropped-then-pending)
--   handle.  This is the SAME `∥′-tm-;` mechanism that blocks the `¬Unr`
--   weakening of `com-xS-min` — self-consistent.  The `front-block-nonzero′` fact
--   (front ≠ cons-acq FROM a msg-typed front) does not help, because the front is
--   NOT the msg handle here (the msg handle is the later `β` channel).
--
--   Below is the machine-checked pivotal typing derivation.  It is abstract in
--   `α`/`β`/`Q`/`P`, so it holds for ANY concrete instance; a Mobile front `α`
--   (an acq-headed channel `⟨ acq ; bounded ⟩`) is well-typed (cf. the BindCtx
--   `cons-acq` counterexamples), so a concrete `ν`-headed com/close redex with a
--   non-front handle and a Mobile front exists.
module BorrowedCF.Simulation.Backward.FrontCex where

open import BorrowedCF.Prelude
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Context using (Ctx; Struct; MobCx; _∶_≼_; ≼-refl; _∶_≈_; _;_; _∥_)
open import BorrowedCF.Context.Equivalence using (∥′-tm-;)
open import BorrowedCF.Processes.Translation using (ϕ[_])
import BorrowedCF.Processes.Untyped as U
open import BorrowedCF.Processes.Typed using (_;_⊢ₚ_; TP-Par; TP-Weaken; _∥_)

-- A Mobile FRONT block is orderable in PARALLEL with the rest: `α ∥ β ≼ α ; β`.
-- (`∥′-tm-;` lifted to `≈` by `Eq*.return`, then `≼-refl`.)
front-mobile-≼ : ∀ {n} {Γ : Ctx n} {α β : Struct n}
  → MobCx Γ α → Γ ∶ (α ∥ β) ≼ (α ; β)
front-mobile-≼ M = ≼-refl (Eq*.return (∥′-tm-; (inj₁ M)))

-- THE COUNTEREXAMPLE MECHANISM (machine-checked): a body `Q ∥ P` in which the
-- MOBILE front block `α` is used by thread `Q` while a LATER channel `β` (the
-- com/close handle) is used by the PARALLEL thread `P`, types against the ν's
-- `;`-chain binder `α ; β`.  So the active handle sits in `β` (not the front),
-- with `α` (front) Mobile — witnessing that the ordered+linear ⊢ₚ does NOT force
-- the handle to `0F`, i.e. `¬ Mobile (lookup 0F)` is not derivable.
front-mobile-bypass : ∀ {n} {Γ : Ctx n} {α β : Struct n} {P Q}
  → MobCx Γ α → Γ ; β ⊢ₚ P → Γ ; α ⊢ₚ Q → Γ ; (α ; β) ⊢ₚ (Q ∥ P)
front-mobile-bypass M ⊢P ⊢Q = TP-Weaken (front-mobile-≼ M) (TP-Par ⊢Q ⊢P)


-- ── REDUCTION-SEMANTICS SUBTLETY, RESOLVED ──────────────────────────────────
-- Does the ¬Mobile(0F)-obligation-failure make the SIMULATION genuinely fail,
-- or is it rescuable by an admin-prefixed reflection (R-Acq α, then R-Com β)?
--
-- A Mobile (acq-headed) front `α` is a `cons-acq` (0-count) block.  Its untyped
-- acquire-flag is `acq` = ACQUIRE-READY (below), NOT a blocked `drop` flag.
-- `RU-Acquire` fires on `φ acq _` (Reduction/Processes/Untyped.agda:82); typed
-- `R-Acq` fires UNCONDITIONALLY on `zero ∷ suc b₁ ∷ B₁` (no flag side-condition).
-- A `drop`-flag block is a NONZERO active block (ϕ[suc _] = drop) whose front is
-- New-derived — hence NOT Mobile.  So a "Mobile front with a BLOCKED acquire" is
-- inconsistent: Mobile front ⟹ flag `acq` ⟹ R-Acq/RU-Acquire FIREABLE.
mobile-front-flag-acquire-ready : (ϕ[ 0 ]) ≡ U.acq
mobile-front-flag-acquire-ready = refl

-- CONCLUSION — SECOND OUTCOME (rescuable, NO design change):
--   The Mobile front's acquire is always fireable, so the com handle `β` behind
--   `α` is brought to `0F` by `R-Acq`, after which `R-Com` fires.  P is NOT stuck
--   for producing the com.  Backward HOLDS via an ADMIN-PREFIXED reflection
--   (R-Acq then R-Com), provided a-acq is absorbed by `≈` (the up-to-φ machinery).
--   The `¬Mobile(0F)` obligation is still FALSE (front-mobile-bypass), so the flat
--   confinement `com-reflect` cannot close it — but the fix is a SMARTER
--   (admin-prefixed) `com-reflect`, NOT a calculus/statement design change.
