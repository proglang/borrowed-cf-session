# Annotation campaign, agent D1: ForwardSoup

Goal: `agda-check BorrowedCF/Simulation/ForwardSoup/Local.agda` exits 0 after Phase A
added `_⦂_` and `E-Ann` to both term languages.

## Plan
Add homomorphic `⦂` clauses to every structural recursion over `Src.Tm` / `Soup.Tm` in
the ForwardSoup tree, and the `E-Ann ↦ E-Ann` case to `T[_]-─→`.

## Errors found and fixed (all CoverageIssue, all mechanical)
- [x] Expressions.agda: `sub-cong`, `sub-id`, `ren-cong`, `ren-ren`, `ren-sub`, `sub-ren`,
      `T[_]-Env-cong`, `T[_]-renEnv`, `T[_]-⋯ᵣ`, `T[_]-envAt`, `T[_]-⋯ₛ` get
      `cong (_⦂ T) (IH)`; `T[_]-─→` gets `... | e₁ Src.⦂ T | SrcRed.E-Ann = SoupRed.E-Ann`
      (no subst, the translation equation is definitional).
- [x] Local/Step.agda: `ren-id`.
- [x] Local/InsertSupport.agda: `insertPhi-ren`, `insertPhi-T`, new injectivity helper
      `ann-inj`, `consumePhi-fixed⇒insertPhi-fixed`.
- [x] LocalImage/Separation.agda: `consumePhi-ren`, `consumePhi-T`.

No `Value`, `Frame`, or `⋯→` case analysis needed changes (no new Value/Frame constructors).
No live-thread condition broke.

## Out-of-scope errors
None encountered.

## Result
`agda-check BorrowedCF/Simulation/ForwardSoup/Local.agda`: exit 0.
Full run (after Expressions fixes, all leaf modules re-checked): 2m38s wall, no warnings.
No holes, no pragmas, no postulates added.
