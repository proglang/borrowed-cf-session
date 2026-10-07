# Phase B3 status: Algorithmic + Solved + sound (annotation campaign)

Owner: agent B3. Files: BorrowedCF/Algorithmic.agda, BorrowedCF/Algorithmic/Solved.agda.

## Plan
- [x] Solved.agda: SolvedTm `_⦂_` case (+ `infixl 5 _⦂_`, same as the Tm constructor),
      subTm / subTm-solved / subTm-id clauses
- [x] Algorithmic.agda: `fv (e ⦂ T) = fv e`, `fv-subTm (e ⦂ T) = fv-subTm e`
- [x] Algorithmic.agda: A-Ann syntactic (ChkForm premise dropped, `data ChkForm` kept, comment updated)
- [x] Algorithmic.agda: `sound (A-Ann x) = T-Ann (sound x …)`; `⊢-sub σ (T-Ann d) = T-Ann (⊢-sub σ d)`
- [x] agda-check BorrowedCF/Algorithmic/Solved.agda: exit 0
- [x] agda-check BorrowedCF/Algorithmic.agda: exit 0 (includes sound, ⊢-sub)
- [x] Completeness.agda reconnaissance (expected failure, not fixed)

No holes, pragmas or postulates added.

## Final A-Ann (verbatim)

```agda
  A-Ann :
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n →
    -------------------------------------
    Γ ; γ / m ⊢ (e ⦂ T) ⇒ T ∣ ϵ ↑ Δ / n
```

## New SolvedTm case (verbatim)

```agda
  _⦂_ : {e : Tm n} {T : 𝕋} → SolvedTm e → SolvedTy T → SolvedTm (e ⦂ T)
```

## Completeness reconnaissance (first error, exit 42)

```
BorrowedCF/Completeness/Scope.agda:145.37-38: error: [WrongNumberOfConstructorArguments]
The constructor A-Ann expects 6 arguments (including hidden ones),
but has been given 7 (including hidden ones)
when checking that the pattern A-Ann cf d has type
Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n
```

Other `A-Ann cf …` sites (grep): Completeness/Scope.agda:145,258; Weaken.agda:309,311;
Main/Struct.agda:104,129,154; Main/Abs.agda:77,114. Probes (CaseUnr, MobUvarWF, LinNeeded,
LetPairPar) already used one-argument A-Ann and now type `e ⦂ T` instead of `e`.
Any function casing on SolvedTm (Completeness/Decl/Solved.agda, Main/*) needs a `_⦂_` clause.
