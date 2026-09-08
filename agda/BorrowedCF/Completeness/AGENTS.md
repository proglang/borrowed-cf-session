# Working rules for proof agents (read fully before touching anything)

## Scope and isolation
- You may create and edit files ONLY inside `agda/BorrowedCF/Completeness/` (module prefix
  `BorrowedCF.Completeness.`). Never edit any other file of the repository. If an existing
  lemma outside is missing or too weak, re-prove what you need inside Safety/.
- Do not run git commands that change state (no commit, no checkout, no stash).
- No `postulate`, no `{-# TERMINATING #-}`, no `--allow-unsolved-metas`, no
  `trustMe` in files you deliver. A file counts as done only when it loads with zero
  goals and zero unsolved metas. If you must leave holes, say exactly which ones and why.
- Files you own are listed in your task. Do not edit files owned by another agent; if
  you need something from them, write it yourself in your own module.

## Toolchain (mandatory settings)
- Agda 2.8.0 with stdlib 2.4. Every agda invocation needs
  `AGDA_DIR=$HOME/.config/agda-mcp/agda-dir`
  (private config; the global ~/.agda still points at stdlib 2.3, which fails).
- Command-line check: ALWAYS use the wrapper `agda-check BorrowedCF/Completeness/X.agda` (in PATH). It sets
  AGDA_DIR, runs from `agda/`, and takes one of 2 machine-wide slots and caps the heap at 11 GB (a check that exceeds it fails with "heap overflow" instead of taking the machine down) (the system went OOM on
  2026-09-08 with 6 unthrottled agda processes). Never call `agda` directly.
- Old form (do not use):
  `cd agda && AGDA_DIR=$HOME/.config/agda-mcp/agda-dir agda BorrowedCF/Safety/X.agda`
- Interactive development through the Agda MCP server (preferred for goals, case
  splits, refine, normalisation). It runs on http://localhost:3000/mcp and is called with
  `agda-mcp-call <tool> '<json-args>'` (in PATH), e.g.
  `AGDA_MCP_SESSION=<your-agent-name> agda-mcp-call agda_load '{"file":"/abs/path/File.agda"}'`
  then `agda_get_goals '{}'`, `agda_get_goal_type_context '{"goalId":0}'`,
  `agda_refine '{"goalId":0,"expression":"..."}'`, `agda_case_split '{"goalId":0,"variable":"x"}'`,
  `agda_give`, `agda_auto`, `agda_infer_type`, `agda_compute`, `agda_search_about`,
  `agda_show_module`, `agda_why_in_scope`, `agda_goto_definition`. Always pass your own
  AGDA_MCP_SESSION so sessions do not interfere. Commands that edit (give/refine/case
  split) write the file on disk; re-read the file afterwards. Absolute file paths only.
- Interface files of the core modules and of Simulation/BackwardSoup/Canonical (+deps) are cached in agda/_build.
- Import only the core modules (Prelude, Types, Context, Terms, Processes.Typed,
  Processes.Congruence, Processes.Renamings, Reduction.Base, Reduction.Expressions,
  Reduction.Processes.Typed, Context.*, Types.*). Modules under `Simulation/` are
  expensive and partly hole-ridden; import one only if it is cheap and complete, and say
  so in your report (`Simulation.Support.Strengthen` is a candidate).

## Editing discipline
- Make targeted edits (Edit tool or MCP give/refine); do not rewrite whole files to
  change a part. Re-read a region right before you replace it.
- Keep each module under ~600 lines; split helper lemmas into submodules under your
  own directory.

## Reporting
- Keep `agda/BorrowedCF/Completeness/DASHBOARD.md` untouched; the orchestrator updates it.
- Update your STATUS.md the MOMENT a single lemma or definition type-checks with zero goals
  (one line each: name, one-line statement, proved / in progress / stuck: reason, file). Not
  only at the end. The orchestrator reads it continuously.
  Instead, put your own progress log in `agda/BorrowedCF/Completeness/<YourDir>/STATUS.md`
  (lemma list with todo/done, blockers, and any issue with the paper or the
  definitions you discovered), and update it whenever you finish or get stuck on a lemma.
- Your final report must list: files delivered, every top-level lemma with its
  statement in one line and its status, remaining holes (if any) with the goal type,
  and every discrepancy you found between the tex rules and the Agda definitions.

## Reuse before you prove (added 2026-09-08 17:45)
The `Simulation/` tree is COMPLETE (170 modules, no --allow-unsolved-metas, no holes except
Simulation/Backward.agda and Backward/Sketch.agda; one sanctioned postulate `funext` in
Simulation/Support/Base.agda). Before proving any lemma, search for it: `grep -rn` under
agda/BorrowedCF and `agda-mcp-call agda_search_about`. Known reusable results:
- Simulation/Support/Theorems/DropShape.agda: `drop-handle-≃ret`, `discard-handle-≃skip`,
  `fn-drop-dom`, `fn-discard-dom`, `drop-shape` (typing of the R-Drop LHS forces b₁ ≡ 0 and a
  following group), `discard-b0-vacuous`.
- Simulation/Support/AcqInv.agda: `fn-acq-dom`, `acq-app-nonUnr`.
- Simulation/Support/PairConfine.agda: `fn-end-dom`, `close-handle-end`, `close-group-width`,
  `strengthen-frame*`, `Inverter*` machinery.
- Simulation/Support/HeadConfine.agda: `¬unr-handle`, `discard-app-nonUnr`, `drop-app-nonUnr`.
- Simulation/Support/InvFrame.agda: `inv-app`, `inv-pair`, `inv-seq`, `inv-let`, `inv-letpair`,
  `inv-inj`, `inv-case`, `strengthen-frame`, `value-reflect`.
- Simulation/Support/Strengthen.agda: `strengthen-Tm(-gen)`, `strengthen-Proc(-gen)` (a typed
  term/process not using handle h factors through any renaming missing h), `Inverter`.
- Simulation/Support/Confine.agda: `count`, `≼⇒count≤`, `count-≈`, dom lemmas.
- Simulation/Support/HandleLinear.agda: `¬Skips⇒¬Unr-seq`, `¬Unr-seq`.
- Simulation/Support/Frames.agda: frame substitution lemmas, `⋯→-⋯ₛ`.
- Simulation/BackwardSoup/Inversion.agda: `T-app-inv`, `T-seq-inv`, `T-let-inv`, `T-letpair-inv`,
  `T-case-inv`, `T-value-inv`, `value-irreducible`, `plug-value-inv`.
- Simulation/Support/Theorems/{Com,Splits,Acq,Drop}.agda: the forward-simulation cases for the
  typed rules; they invert the typing of exactly the R-Com / R-RSplit / R-Acq / R-Drop LHS
  (`U-com-step`, `U-rsplit-step`, ...). Mine them for the inversion sequences.
- Simulation/Support/Theorems/SplitsLQ.agda: arithmetic and renaming facts about the lsplit
  position q (`dlwkq`, `sum-lwkq`, `𝐒lwkq-lo/hi`, `P1q..P3q`).
- Processes/Congruence.agda: `_/_⊢-≋_` (congruence preserves typing).
Importing these modules costs type-checking time the first time only (interface files are
cached in agda/_build). Duplicating a lemma that exists is a failure; cite the module you reuse.

## Performance gotchas (MANDATORY reading, added 18:45 after two agents lost >1h each)
- NEVER `with`-abstract a record or a Σ-package that contains an EQUATION about the process
  (e.g. `with locate₂ … | loc₂ c f₁ f₂ refl …`, `with canon-drop … | canonRedex … `, or any
  `refl` that rewrites `plug ctx …` / `threadInContext …`). The `refl` rewrites the whole goal
  including the typing hypothesis, and every later `with` re-elaborates a huge term: checks
  reached 12–23 GB and 15+ minutes (Sync.agda, Redex/Handles.agda, Main/TmpCheck.agda).
  Instead: bind the package to a variable and use projections, or move the continuation into a
  separate top-level function that takes the package as an ARGUMENT and is stated for an
  arbitrary process; use `rewrite`/`subst` only on small goals; avoid chains of more than two
  `with`s on goals mentioning `plug`.
- Apply R-Drop/R-Discard/R-Acq/R-Com/R-Choice/R-Close with all implicit indices given
  (`sum (?b ∷ ?B) + … ≡ …` is not a pattern for the unifier).
- A frame list `E` is never inferable through `_[_]*` (it folds over the list): pass `{E = E}`.
- Every `;` in identifiers and operators is U+037E, not ASCII `;` (bare `[ParseError]`).
- Import Simulation modules with explicit `using` lists; never `open import` an umbrella.
- Watch the RSS of your own `agda-check` (`ps -o rss,args -C agda`); anything above 6 GB or
  longer than 5 minutes on a file whose imports are cached means one of the patterns above.
- (G2, 19:10) A second trap: `subst (λ z → z ─→ₚ _) eq red` or a pattern-`let` projection over an
  equation between PLUGGED processes (`plug ctx …`, `plug₂ …`, `compose₂ …`) makes Agda unfold
  the plugging functions under the equation: >10 GB, never finishes. Fix: transport lemmas that
  match the equation with `refl` while both processes are still VARIABLES (`transport-red`,
  `transport-⊢` in Safety/Progress/Sync/Dispatch.agda (in the finished Safety tree)), applied before anything is unfolded.

## This task: algorithmic completeness
Reuse everything in `agda/BorrowedCF/Safety/` (finished, verified: process preservation and
progress) in addition to `Simulation/`; in particular the Safety tree shows how to work with
`≼`/`≈` (Handles/Acq.agda: `≼-tr`, `zap`, `pat-hole-≼`), with `count` (Confine), and with
`before`/`GroupOrder`. Read `Safety/AGENTS.md`'s performance gotchas: they apply verbatim.

## Development quirks (MANDATORY, collected from 15 agent runs — read before writing Agda)
- SEMICOLON: every `;` in this development is U+037E GREEK QUESTION MARK, never ASCII `;`:
  the session/structure/term operators `_;_`, the judgments `Γ ; γ ⊢ e ∶ T ∣ ϵ` and
  `Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n`, and identifiers such as `;-≼-∥`, `;-≼-join`, `;-commMob`,
  `atom-;-unsnoc`, `𝐂.;-unit₁`. An ASCII `;` yields a bare `[ParseError]` with no hint. Copy the
  character from an existing file when in doubt.
- Names: `Lin` is taken (Types/Syntax), the completeness predicate is `LinStruct` (Base.agda);
  `Solved` is renamed `SolvedTy` wherever Algorithmic modules are open; `Ctx n = Vec 𝕋 n` with
  cons `_⸴_`, append `_⸴*_`, lookup `_﹫_`; index 0F is the innermost binder; `0F`/`1F` need
  `open Fin.Patterns` (or `let open Fin.Patterns in`); `n m` etc. come from `open Nat.Variables`.
- Structures: `Γ ∶ γ₁ ≼ γ₂` reads "typable under γ₁ ⇒ typable under γ₂" (T-Weaken). Rules:
  `≼-refl` from `≈`, `≼-∅ : UnrCx Γ α → [] ≼ α` (unrestricted structure may be ADDED, never
  dropped), `≼-wk : (α₁ ∥ α₂) ; (β₁ ∥ β₂) ≼ (α₁ ; β₁) ∥ (α₂ ; β₂)`, `;-≼-∥ : α ; β ≼ α ∥ β`,
  congruences, transitivity. `≈` has assoc/comm/unit, `∥′-dup` (UnrCx) and `∥′-tm-;` (MobCx one
  side); Unr ⊆ Mobile (`unr⇒mobile`), so unrestricted variables commute (`;-commMob`) and
  duplicate. `≼` never creates a `;`-order between immobile variables (`before-mono-≼`).
- `join 𝟙 α β = α ∥ β`, `join L α β = α ; β`, `join R α β = β ; α` (`join-flip`); for ParSeq,
  `join par = ∥`, `join seq = ;` definitionally (`parOrSeq? ≤γ = seq , ≤γ` now type-checks),
  `biasedDir par = 𝟙`, `biasedDir seq = L`, `;-≼-join p/s : α ; β ≼ join p/s α β`.
- Restriction `γ ↓ X` keeps the SHAPE of γ and replaces excluded variables by `[]`; use `≈` to
  clean up (`↓-empty`, `dom-empty⇒≈[]`). `dom`, `count` (Confine), `_∈ₘ_` (GroupOrder) are the
  three views of "which variables occur".
- `Mobile` is NOT decidable (∃ over sessions modulo ≃); `Unr` is (`unr?`). Case-split on syntax,
  not on `Mobile`.
- Unification: `UV.Sub` carries `ap-¬skips` and `ap-dual/dual` (the ⁇-twin of a variable must be
  mapped to the dual); build substitutions like `UV.subAll`/`UV.weaken`. `subTy` is the identity
  on solved types (`subTy-id`); `Solving σ` = every image solved.
- Algorithmic judgment `_;_/_⊢[_]_∶_∣_↑_/_` with `Mode = chk | inf`; `⇒`/`⇐` are abbreviations;
  A-Check (⇒→⇐, adds `C-Eq T U`) and A-Ann (⇐→⇒, no annotation) switch modes; `m` is the next
  fresh uvar index on entry, `n` on exit.
- The base now has A-Let and admits `select`/`branch` in A-Const (agent C6, 2026-09-08).
- (C4/orchestrator, 21:55) A third trap: destructuring a large Σ-package (an induction result
  with 10+ components) by an irrefutable `let 〈tuple〉 = r` and then using the components to build
  the next package. Agda desugars each component into nested projections of the whole term, so
  the elaborated term grows combinatorially (Main/Bind/Case.agda: 11.5 GB, killed twice). Bind
  such packages with `with a , b , … ← r` (tuple patterns only, no refl), or split the steps
  into top-level helpers taking the previous components as explicit arguments.
