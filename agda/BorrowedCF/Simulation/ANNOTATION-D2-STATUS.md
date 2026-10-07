# Annotation campaign, Phase D2 status (agent D2)

Targets: Simulation/Support/Theorems/DropShape.agda, Simulation/Forward.agda,
Simulation/BackwardSoup/Simulation.agda. Scope: Simulation/ minus ForwardSoup/.

## Plan
Iterate agda-check, cheapest first (DropShape, Forward, BackwardSoup/Simulation),
adding `⦂` / `T-Ann` / `E-Ann` cases in the style of the neighbouring cases.

## Fixes (ticks)
- [x] Support/Strengthen.agda: T-Ann cases for strengthen-Tm-gen, strengthen-Tm, strengthen-Tm-gen*.
- [x] Support/Frames.agda: `─→-⋯ₛ σ Vσ E-Ann = E-Ann`.
- [x] BackwardSoup/Inversion.agda: new `T-ann-inv` (T[ e ] σ ≡ u ⦂ T gives e ≡ e₀ ⦂ T with
      T[ e₀ ] σ ≡ u; the variable case is refuted because σ x is a value), and the
      `head-inversion … SoupRed.E-Ann` clause reflecting to `E-□ E-Ann` (lock-step).
      Imports `𝕋` from BorrowedCF.Types.
- [x] BackwardSoup/Statement.agda: `_⦂_` clauses of swapPhi, swapPhi-involutive.
- [x] BackwardSoup/SlotInsert.agda: `_⦂_` clause of swapPhi-insertPhi.
- [x] BackwardSoup/SlotBisim.agda: `_⦂_` clauses of swapPhi-ren, swapPhi-as-sub, sub-sub,
      consumePhi-swapPhi, swapPhi-consumePhi-miss, swapPhi-insertPhi-miss,
      swapPhi-insertPhi-past; `swapPhi-─→ x k E-Ann = E-Ann`.

All cases were mechanical (cong under `_⦂ T`, or the root E-Ann step). No new
mathematics, no holes, no pragmas. Locate, Leaves/*, Canonical, Unique,
GroupOrder/Position/Crux needed no change.

## Out-of-scope errors
None encountered.

## Final results (2026-10-07)
| target | exit | wall time (last fresh run / cached rerun) |
|---|---|---|
| Simulation/Support/Theorems/DropShape.agda | 0 | 25 s / 9 s |
| Simulation/Forward.agda | 0 | 584 s incl. slot wait / 12 s |
| Simulation/BackwardSoup/Simulation.agda | 0 | 144 s / 15 s |
