# Annotation campaign, agent C2: main completeness induction

Owner: C2. Files: Completeness/Main.agda, Completeness/Main/**, Completeness.agda.

## Plan
- Interface.agda: `Conclusion Γ̂ γ e …` becomes `Σ[ ê ∈ Tm n ] e ⊑ ê × Infers Γ̂ γ ê …`
  (`Infers` = the old Σ-chain over ê). Case-module signatures stay unchanged (they mention
  only `Conclusion`/`IHAt`).
- Transfer.agda: transport helpers `re-⊢` / `re-≼` (match `refl` on `X′ ≡ X` with both
  sets variables), fed with `fv-⊑ p`.
- Every case outputs `ê` + the `_⊑_` proof; former `A-Ann cf …` sites wrap with `ann … T`.
- Main.agda: new `e ⦂ T` case (`inv-⦂`, `solvedTm-⦂`, `A-Ann (A-Check …)`, `⊑-⦂`),
  new impossible `μ (e ⦂ T)` clause; `complete⇒`/`complete⇐` thread ê.

## Ticks
- [x] Interface.agda (agda-check exit 0)
- [x] Transfer.agda (helpers) (agda-check exit 0)
- [x] Simple.agda (var, const) (agda-check exit 0)
- [x] Abs.agda (abs, absrec: A-Ann sites) (agda-check exit 0)
- [x] Struct.agda (seq, pair ×2 A-Ann, inj A-Ann) (agda-check exit 0)
- [x] App.agda (agda-check exit 0)
- [x] Bind/Let.agda (agda-check exit 0)
- [x] Bind/LetPair.agda (agda-check exit 0)
- [x] Bind/Case.agda (agda-check exit 0)
- [x] Main.agda (+ ann case: `ann-case` lives in Main/Struct.agda; impossible `μ (e ⦂ T)` clause)
- [x] Completeness.agda (unchanged; both statement witnesses check against the new Base statements)

## Verification
- `agda-check BorrowedCF/Completeness.agda`: exit 0, 20.7 s wall with every Main/* interface
  and Completeness.agdai deleted first (15 modules re-checked). No holes, pragmas, postulates.
- Each Main/* module checked individually on landing (each ~10 s; Bind/Case 11 s).

## Notes for later phases
- `Conclusion` = `Σ[ ê ∈ Tm n ] e ⊑ ê × Infers Γ̂ γ ê …` (Interface.agda); `Infers` is the old chain.
- Transport: `re-⊢ F eq d` and `re-≼ F eqX eqY d` (Transfer.agda) match `refl` on `X′ ≡ X`
  with both sets variables; `F` names the position, e.g.
  `re-≼ (λ X Y → join (Arr.dir a) (γ ↓ X) (γ ↓ Y)) (fv-⊑ p₂) (fv-⊑ p₁) (der Lft)`.
  Case uses `caseY-⊑ p₁ p₂ : caseY ê₁ ê₂ ≡ caseY e₁ e₂` (Bind/Case.agda).
- The `let`-tuple destructurings in App.go, Let and LetPair were replaced by `with … ←`.
  A `where` block is NOT in scope in the `with` expressions (only in the last clause), so
  Let/LetPair are split into `*-go` (small structural `let`s) and `*-go′` (the `with`s).
- `mk` continuations in Bind/* are now quantified over the annotated subterms.
