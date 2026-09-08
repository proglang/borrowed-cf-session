# Redex lemmas (agent G1, wave 2)

Files owned: `Safety/Progress/Redex.agda`, `Safety/Progress/Redex/*.agda`, this file.
No postulates, no pragmas, no holes anywhere below.

## Safety/Progress/Redex/Context.agda -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `red-in-ctx` | `(ctx : ProcessContext k n) → Q ─→ₚ Q′ → plug ctx Q ─→ₚ plug ctx Q′` | proved |
| `step-in-ctx` | `(ctx : ProcessContext k n) → e ⋯→ e′ → plug ctx ⟪ e ⟫ ─→ₚ plug ctx ⟪ e′ ⟫` | proved |

Reused: `Locate.{ProcessContext,plug}`, `Reduction.Processes.Typed.{R-Exp,R-Par,R-Bind,R-Struct}`,
`Processes.Typed.∥-comm` (needed for `par-right`: there is no right-hand `R-Par`).

## Safety/Progress/Redex/Located.agda -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `∈BCe⇒shape` | `x ∈BCe e → ∃ E c d w. e ≡ E [ K c ·⟨ d ⟩ w ]* × BCRedex x (K c ·⟨ d ⟩ w)` | proved |
| `∈ACe⇒shape` | same for `∈ACe` / `ACRedex` | proved |
| `∈BC⇒located` | `x ∈BC P → ∃ k ctx E c d w. P ≡ plug ctx ⟪ E [ K c ·⟨ d ⟩ w ]* ⟫ × BCRedex (weakenThrough ctx x) (K c ·⟨ d ⟩ w)` | proved |
| `∈AC⇒located` | same for `∈AC` / `ACRedex` | proved |
| `∈AC⇒located-acq` | `x ∈AC P → ∃ k ctx E d. P ≡ plug ctx ⟪ E [ K `acq ·⟨ d ⟩ (` weakenThrough ctx x) ]* ⟫` | proved |

Reused: `Blocked.{_∈BC_,_∈AC_,_∈BCe_,_∈ACe_,BCRedex,ACRedex}` (agent F),
`Locate.{ProcessContext,plug}`, `Position.weakenThrough`.
The `res` case is definitional: `weakenThrough (bind B₁ B₂ ctx) x` reduces to
`weakenThrough ctx ((sum B₁ + sum B₂) ↑ʳ x)`, the index `_∈BC_`'s `res` uses.

## Safety/Progress/Redex/SplitShape.agda -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `split-shape` | `(bnd : Binder ctx x) → SplitShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd)` | proved |

Re-proof (not import): `Leaves/RSplit.agda` has the identical `split-shape` but inside a
`private` block. The helpers copied are `fin-split`, `splitIx-toℕ`, `transportSplitShape{ˡ,ʳ}`,
`{left,right}PrefixIx(-toℕ)`, `head-split-{left,right}-prefix`, `group-split-{left,right}(-prefix)`.
Reused from `Canonical.agda`: `SplitShape`, `split-l`, `split-r`, `splitIx`;
from `Position.agda`: `Binder`, `sideOf`, `GroupOf`, `groupOf`.

## Safety/Progress/Redex/Handles.agda -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `redex-drop` | `(ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) → [] ; [] ⊢ₚ plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ → ∃ P′. plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ ─→ₚ P′` | proved |
| `redex-discard` | same with `` `discard `` | proved |
| `drop-first-group` | `(ctx) (E) (x) → [] ; [] ⊢ₚ … → (binderWidth (resolve ctx x) ≡ 1) × (binderRest (resolve ctx x) ≢ [])` | proved |

Reused: `Canonical.{CanonRedex,canonRedex,canon-drop,canon-discard,headOfFirstGroup⇒shape}`,
`Position/Crux.{impure-redex-head,drop-first-group-singleton}`,
`Position.{resolve,binderWidth,binderRest,ImpureHandleConst}`, `Locate.{ProcessContext,plug}`,
`Redex/Context.red-in-ctx`.

## Safety/Progress/Redex/Acq.agda -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `redex-acq` | `(E : Frame* k) (bnd : Binder ctx x) → AcqShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) → ∃ P′. plug ctx ⟪ E [ K `acq ·¹ (` x) ]* ⟫ ─→ₚ P′` | proved |
| `acqBinderˡ` | `(ctx₀ : ProcessContext m 0) (ctx₁ : ProcessContext k (sum (0 ∷ suc b ∷ B₁) + sum B₂ + m)) → Binder (compose ctx₀ (bind (0 ∷ suc b ∷ B₁) B₂ ctx₁)) (weakenThrough ctx₁ 0F)` | proved |
| `acqBinderʳ` | same for side 2, at `weakenThrough ctx₁ (head₂ B₁ b B₂)` | proved |
| `redex-acq-exposedˡ` | `(ctx₀) (ctx₁) (E) → ∃ P′. plug ctx₀ (ν (0 ∷ suc b ∷ B₁) B₂ (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ 0F) ]* ⟫)) ─→ₚ P′` | proved |
| `redex-acq-exposedʳ` | same for side 2, handle `head₂ B₁ b B₂` | proved |
| `acq-position` | `(ctx) (E) (x) → [] ; [] ⊢ₚ … → (0 < binderGroup (resolve ctx x)) × (binderPos (resolve ctx x) ≡ 0)` | proved |

Reused: `Canonical.{CanonAcq,canonAcq,canon-acq,AcqShape,acq-l,acq-r}`,
`Position/Crux.acq-non-first-group-head`, `Position.{Binder,binder,weakenThrough,resolve,
binderGroup,binderPos}`, `Locate.{bind,compose,plug,plug-compose}`, `Blocked.head₂`,
`Redex/Context.red-in-ctx`.
Both `index-eq`s hold by `refl`: `0F ↑ˡ m` reduces to `0F`, and `head₂ B₁ b B₂` unfolds to
`(sum B₁ ↑ʳ 0F) ↑ˡ m` because `wkˡ`/`wkʳ` of the renaming kit are `_↑ʳ_`/`_↑ˡ_`.

## Safety/Progress/Redex.agda (hub) -- DONE (0 goals)

| lemma | statement | status |
|---|---|---|
| `redex-new` | `(ctx : ProcessContext k n) (E : Frame* k) (s : 𝕊 0) → ∃ P′. plug ctx ⟪ E [ K (`new s) ·¹ * ]* ⟫ ─→ₚ P′` | proved |
| `redex-fork` | `(ctx : ProcessContext k n) (E : Frame* k) → Value e → ∃ P′. plug ctx ⟪ E [ K `fork ·¹ e ]* ⟫ ─→ₚ P′` | proved |
| `redex-lsplit` | `(ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) → ∃ P′. plug ctx ⟪ E [ K (`lsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′` | proved |
| `redex-rsplit` | same with `` `rsplit `` | proved |

Re-exports `Redex/{Context,Located,Handles,Acq}`, so one import of
`BorrowedCF.Safety.Progress.Redex` gives every lemma above.

## Memory footprint

Every module below completes inside a 6 GB heap (`agda-check … +RTS -M6G -RTS`);
the hub was verified at 8 GB. Two rewrites were needed to get there, both
recorded under "Notes" -- the naive versions grew past 22 GB and were killed by
the machine watchdog.

## Notes / discrepancies

* PERFORMANCE GOTCHA 1 (cost me two watchdog kills): do NOT `with`-abstract a
  `Canonical.agda` record and then match its CONSTRUCTOR
  (`with canon-drop … | canonRedex bh D₁ D₂ ab E₀ Q₀ ≋r trk`). The
  with-abstraction has to generalise the `src` index
  `threadInContext ctx ⟪ E [ K c ·¹ (` x) ]* ⟫ 0F` as well, and Agda then grows
  without bound (>20 GB) even when the body is the constant `bh`. Consume the
  record in a separate top-level function whose argument is the record
  (`fromCanonDrop`, `fromCanonDiscard`, `fromCanonAcq` here), stated for an
  ARBITRARY closed process, and apply that function. A `with` that binds a plain
  VARIABLE and uses projections (as `redex-lsplit` does) is fine.
* PERFORMANCE GOTCHA 2: `R-Drop` / `R-Discard` weaken the residual and the frame
  (`P ⋯ₚ weakenᵣ`, `E ⋯ᶠ* weakenᵣ`). Applying them with the indices implicit
  makes Agda try to solve `sum (?b ∷ ?B) + sum ?C + ?n ≡ …`, which is not a
  pattern. `dropStep` / `discardStep` / `acqStep` give every index explicitly, so
  the application is a syntactic conversion check.
* GOTCHA for callers: the frame stack `E` is NOT inferable from a type of the form
  `… ⊢ₚ plug ctx ⟪ E [ K c ·¹ (` x) ]* ⟫`, because `_[_]*` is a fold over the frame
  list. `Crux.{impure-redex-head,drop-first-group-singleton,acq-non-first-group-head}`
  therefore have to be applied with `{E = E}` given; left implicit, Agda blocks on the
  constraint and its memory grows without bound. `drop-first-group` and `acq-position`
  take `ctx`, `E`, `x` explicitly for that reason.

* `redex-new`, `redex-fork`, `redex-lsplit`, `redex-rsplit` need NO typing derivation:
  `R-New` / `R-Fork` fire on a bare thread, and `canon-lsplit` / `canon-rsplit` are purely
  structural (any group position is a split position). Only `drop` / `discard` need one,
  because the crux of `Position/Crux.agda` is what puts the handle at `0F`.
* `Reduction/Processes/Typed.agda` has no right-hand parallel congruence; `∥-comm` twice
  through `R-Struct` supplies it. Worth noting in the paper's rule figure.
