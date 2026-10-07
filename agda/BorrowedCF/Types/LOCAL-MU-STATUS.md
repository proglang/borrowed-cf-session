# R3: `NonLocal.mu` (option 1 of Safety/Preservation/Splits/DECISION-local-mu.md)

## Plan / progress
1. [done] Types/Predicates.agda: `mu : NonLocal s → NonLocal (mu s)`; `mu` clauses in
   nonLocal-dual⁺, nonLocal-dual⁻, nonLocal-⋯, nonLocal-⋯ᵣ⁻¹, skips⇒local. Nothing else in
   the file cases on NonLocal (Wf only uses Local abstractly).
2. [done] Types/Unification.agda: no edit needed (no NonLocal case split; the `λ α ()`
   proofs are for `` α and end, unaffected). No decider (`nonLocal?`/`local?`) exists.
3. [done] Splits/Group.agda: `cons-acq⇒nonLocal (AC.mu c) = mu (cons-acq⇒nonLocal c)`
   (direct; `acq ⋯ weakenᵣ` reduces to `acq`). Pragma + TODO removed, comment updated.
4. [done] Probe/LocalMuGap.agda: `NL₂ : NonLocal t₂ = mu (acq ;₁-)`, `¬L₂ : ¬ Local t₂`,
   left-not-acqHead kept, header says the gap is closed.
5. [done] Grep: only hit outside my scope that breaks is below.

## Recorded, NOT fixed (outside scope)
- BorrowedCF/Algorithmic/Solved.agda:190-194 `subTy-local` — CoverageIssue, missing
  `subTy-local {s = mu s} x x₁`. Proposed one-line fix (unverified, file not edited):
  `subTy-local {s = mu _}     Ls (mu ¬Lσs) = subTy-local (Ls ∘ mu) ¬Lσs`
  This blocks Algorithmic.agda and Completeness.agda (which imports it).
- Completeness/Scope/Merge.agda:50-55, Completeness/Main/Interface.agda:51-64 use Local
  only abstractly; not reached by the checker yet because of the error above.

## Verification (agda-check exit codes)
| file | exit | wall |
|---|---|---|
| Types/Predicates.agda | 0 | 29s (incl. slot wait) |
| Types/Unification.agda | 0 | 6s |
| Safety/Preservation/Splits/Group.agda (no pragma, 0 holes) | 0 | 55s |
| Safety/Probe/LocalMuGap.agda | 0 | 6s |
| Algorithmic.agda | 42 | 8s |
| Completeness.agda | 42 | 9s |

First error (both):
```
BorrowedCF/Algorithmic/Solved.agda:191.1-194.43: error: [CoverageIssue]
Incomplete pattern matching for subTy-local. Missing cases:
  subTy-local {s = mu s} x x₁
when checking the definition of subTy-local
```
