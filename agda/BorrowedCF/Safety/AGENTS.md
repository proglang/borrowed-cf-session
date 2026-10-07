# Working rules for proof agents (read fully before touching anything)

## Scope and isolation
- You may create and edit files ONLY inside `agda/BorrowedCF/Safety/` (module prefix
  `BorrowedCF.Safety.`). Never edit any other file of the repository. If an existing
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
- Command-line check: ALWAYS use the wrapper `agda-check BorrowedCF/Safety/X.agda` (in PATH). It sets
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
- Keep `agda/BorrowedCF/Safety/DASHBOARD.md` untouched; the orchestrator updates it.
- Update your STATUS.md the MOMENT a single lemma or definition type-checks with zero goals
  (one line each: name, one-line statement, proved / in progress / stuck: reason, file). Not
  only at the end. The orchestrator reads it continuously.
  Instead, put your own progress log in `agda/BorrowedCF/Safety/<YourDir>/STATUS.md`
  (lemma list with todo/done, blockers, and any issue with the paper or the
  definitions you discovered), and update it whenever you finish or get stuck on a lemma.
- Your final report must list: files delivered, every top-level lemma with its
  statement in one line and its status, remaining holes (if any) with the goal type,
  and every discrepancy you found between the tex rules and the Agda definitions.

## Reuse before you prove (added 2026-09-08 17:45)
The maintained strict-soup simulation trees are COMPLETE (no --allow-unsolved-metas and no holes;
one sanctioned postulate `funext` is in Simulation/Support/Base.agda). Before proving any lemma, search for it: `grep -rn` under
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
  `transport-⊢` in Safety/Progress/Sync/Dispatch.agda), applied before anything is unfolded.

## Portability (added 2026-09-08 late)

The development is also checked on a second machine with a different Agda build. There, `s ⋯ ρ` in a type signature with `ρ : m →ᵣ n` and a generalized `s` failed instance search (`No instance of type Kit (λ _ → 𝔽 n)`), although it passes here. In every new signature fix the kit by using the aliases `s ⋯ᵣ ρ` and `s ⋯ₛ ϕ` (both are `_⋯_` with the kit fixed, exported by BorrowedCF.Types.Substitution), or `_⋯_ ⦃ Kᵣ ⦄ s ρ`. Do the same for other instance arguments a reader cannot infer from the renaming alone.

## rsplit relaxation campaign (added 2026-10-07)

Upstream (Janek, commits 469f079 + 85720a8) relaxed the splits:
- `lsplit : (s s′ : 𝕊 0) → ¬ Skips s → Local s′ → ¬ Skips s′ → …` (one NEW argument `Local s′`).
- `rsplit : (s s′ : 𝕊 0) → Local s′ → ¬ Skips s′ → …` (`¬ Skips s` REMOVED, `Local s′` added; Skip is
  now allowed as the first type of an rsplit).
- New predicates in `BorrowedCF.Types.Predicates`: `NonLocal` (starts with acq: `acq`, `_;₁-`,
  `Skips s₁ ;₂ NonLocal s₂`) and `Local s = ¬ NonLocal s`, with lemmas `nonLocal-dual⁺/⁻`,
  `nonLocal-⋯`, `nonLocal-⋯ᵣ⁻¹`, `local-⋯ᵣ`, `local-⋯ᵣ⁻¹`, `local-dual⁺`, `skips⇒local`.
- `Wf` for `s₁ ; s₂` now takes `Skips s₁ ⊎ Local s₂`.
Proof sites that relied on the removed `¬ Skips s` evidence of rsplit are broken; the `Local s′`
evidence is what replaces it. Typical repair: where `¬Sm₁ Sk` refuted the `Skips t₁` branch, that
branch now really happens, and the danger it used to signal (a second `acq` appearing behind the
fresh `acq` of the right part, `acq ; t₂` with `t₂ ≃ acq ; …`) is refuted by `Local t₂` instead,
via a lemma of the shape `s ≃ acq ; u → NonLocal s` (check `Types/AtomCons`/head machinery before
proving one).

All earlier sections of this file still apply: U+037E semicolons, `agda-check`, no `with` on
packages whose refl rewrites the plug index, STATUS file updates after every proved piece.

### Campaign findings (broadcast 2026-10-07, from agent R1)

- RESOLVED 2026-10-07 (agent R3): `NonLocal` now HAS a `mu` constructor, so
  `Local t₂` really does refute `t₂ ≃ acq ; u`; `local⇒¬acqHead` in
  Splits/Group.agda is fully proved, Group.agda has zero holes and no pragma.
  A `λ ()` proof of `Local (mu …)` no longer type-checks — add a `mu` clause
  instead. History: Splits/DECISION-local-mu.md, Probe/LocalMuGap.agda.
- Group.agda's public `bindCtx-rsplit` now takes `Local t₂ → ¬ Skips t₂ → …`
  (the old `¬ Skips t₁` is gone). Redex.agda:92 still passes the old
  arguments.
- In `using (…)` lists of import statements the separator is ASCII `;`; a
  blanket replace to U+037E breaks the import with a ParseError.
- Do not name a bound variable `L`; a constructor `L` is in scope and pattern
  matching then fails with "Cannot split on argument of non-datatype".

### Decision (2026-10-07, MW): Local gets a `mu` constructor

Option 1 of Splits/DECISION-local-mu.md is being applied by agent R3:
`NonLocal` gains `mu : NonLocal s → NonLocal (mu s)` (Types/Predicates.agda),
with `mu` clauses in the transport lemmas and the decider, Group.agda's hole
closes and its temporary pragma goes away. Consequences for everyone else:
a `λ ()` proof of `Local (mu …)` no longer type-checks (by design); `Local`
proofs for non-μ head constructors are unaffected.

## Annotation campaign, Phase A landed (2026-10-07)

Both term languages now have `_⦂_ : (e : Tm n) (T : 𝕋) → Tm n` (U+2982, `infixl 5`,
same level as `_⋯_`, so `e ⋯ ϕ ⦂ T` parses as `(e ⋯ ϕ) ⦂ T`). Facts for all later phases:
- Declarative rule `T-Ann : Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ⊢ e ⦂ T ∶ T ∣ ϵ` (Terms/Base.agda);
  inversion `inv-⦂ : Γ ; γ ⊢ e ⦂ T ∶ U ∣ ϵ → T ≃ U × Γ ; γ ⊢ e ∶ T ∣ ϵ` provided there.
- Step `E-Ann : (e ⦂ T) ─→ e` in Reduction/Expressions.agda AND Reduction/ExpressionsSoup.agda.
  `(e ⦂ T)` is NOT a Value; there is NO annotation Frame; an annotated term steps at the root.
- `strip : Tm n → Tm n` (Terms/Base.agda) removes all annotations.
- Translations are homomorphic BY DEFINITION: `T[ e ⦂ T ] σ = T[ e ] σ ⦂ T` (soup) and the tree
  translation goes through `⋯`. Do not erase annotations anywhere.
- Typed and soup `_⦂_` are distinct overloaded constructors; a module opening both unqualified
  may need qualification.
- Any function deciding value/plug/blocked over Tm needs an `e ⦂ T` clause: not a value, not a
  plug, root-steps by E-Ann. First known sites: Safety/Progress/Expr/Plug.agda `value?`, `plug?`,
  `plug-⋯ᵣ⁻¹` (CoverageIssue).
- `fv` lives in Algorithmic.agda and still lacks the `⦂` clause (Phase B3 adds `fv (e ⦂ T) = fv e`).

### Annotation campaign, D1 landed (ForwardSoup green)

Lock-step confirmed: the source E-Ann maps to the soup E-Ann with no `subst`
(`T[ e ⦂ T ] σ = T[ e ] σ ⦂ T` is definitional). Pattern for structural
lemmas over terms: copy the `` `inj `` clause and wrap with `cong (_⦂ ty)`.
Soup-side `consumePhi`/`insertPhi` already carry their ⦂ clauses
(Reduction/Processes/UntypedSoup.agda ~71/~102). Annotation-constructor
injectivity helper: `ann-inj` (local in ForwardSoup/Local/InsertSupport.agda);
make a local copy where needed.

### C2 gotcha (broadcast): `where` and `with`

`where` definitions are not in scope inside `with` expressions, only in the
final clause. For a function that needs helpers across `with` steps, split it:
a `*-go` with the small structural `let`s and a `*-go′` taking the `with`
results (template: Completeness/Main/Bind/Let.agda, LetPair.agda).
