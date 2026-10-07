# Annotation campaign, agent B1 status

Scope: Safety/Blocked.agda, Safety/Progress.agda, Safety/Progress/**.

## Plan
1. agda-check Safety/Blocked.agda, add `e ⦂ T` clauses until exit 0.
2. agda-check Safety/Progress.agda, fix own files until exit 0.
Semantics: `e ⦂ T` is not a value, not a blocked plug, root-steps by `E-Ann`.

## Error log
- Progress/Expr/Plug.agda: CoverageIssue `value?`, `plug?`, `plug-⋯ᵣ⁻¹` for `e ⦂ T`. FIXED
  (`no λ()`; `plug?` only via `here`, like `μ`; `plug-⋯ᵣ⁻¹` `here` clause).
- Blocked.agda: CoverageIssue `constApp?` (`e ⦂ T` and `(e ⦂ T) ·⟨ d ⟩ e₂`), `isVar?`,
  `sendArg?`. FIXED (all `no` by constructor disjointness). Nothing else in Blocked.agda
  needed a case: `_∈BCe_`, `_∈ACe_`, `Stuck` are defined via `Frame*` plugging, so an
  annotated root has none of them for free.
- Progress/Expr.agda: CoverageIssue `progress⁺` for `T-Ann`. FIXED
  (`progress⁺ (T-Ann e) = inj₂ (inj₂ (_ , E-□ E-Ann))`).
- Progress.agda: blocked by out-of-scope error (below).

## Per-file ticks
- [x] Progress/Expr/Plug.agda (via Blocked check)
- [x] Blocked.agda: exit 0, 46 s
- [x] Progress/Expr.agda: exit 0, 227 s (first run 395 s while Simulation.Support deps rebuilt)
- [x] Progress/Sync/Front.agda, Sync/Unique.agda, Sync/Heads.agda, Main/Shapes.agda,
      Sync/CloseShape.agda: exit 0 each (6 to 10 s)
- [ ] Progress.agda and every module importing Simulation.BackwardSoup.Locate (Main, Redex,
      Redex/*, Sync, Sync/{Binder,Choice,Close,Com,Dispatch,Locate}): NOT CHECKABLE, blocked.
      grep shows none of them cases on Tm, `_─→_`, `_⋯→_`, Value or typing constructors
      (they use `progress⁺`, `_∈BCe_`/`_∈ACe_` abstractly), so no annotation clause is expected.

## Out-of-scope errors
- Simulation/BackwardSoup/Inversion.agda:651 `head-inversion`: CoverageIssue, missing
  `head-inversion e σ Vσ Pσ {t SoupTerm.⦂ T} x x₁`. Imported by Simulation.BackwardSoup.Locate,
  which nearly all of Safety/Progress/** and Progress.agda import. Phase D (Simulation) owns it.

## Final
- Blocked.agda: exit 0 (46 s).
- Progress.agda: exit 42 (26 s), only error is the out-of-scope Inversion.agda one above.
