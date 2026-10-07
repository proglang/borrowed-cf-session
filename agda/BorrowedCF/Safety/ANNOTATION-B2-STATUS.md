# Annotation campaign, Phase B2: Safety preservation (agent B2)

Plan: iterate `agda-check BorrowedCF/Safety/Preservation.agda`, fix sites in
Safety/Preservation{.agda,/**} only (T-Ann pass-through, E-Ann via inv-⦂).

## Running error list
- Check 1 (11.6 s, exit 42): OUT OF SCOPE. Simulation/Support/Strengthen.agda
  coverage: `strengthen-Tm-gen`, `strengthen-Tm`, `strengthen-Tm-gen*` miss the
  `T-Ann` case. Imported by Splits/Confine.agda and Handles/Acq.agda. Not patched
  by B2; a sibling added the three `T-Ann` clauses while B2 was checking.
- `pres-Exp` (Preservation/Basic.agda) delegates to `preservation` of
  Reduction/Expressions.agda (Phase A, E-Ann case there), so no Exp-path work
  lives in B2's files.

## Per-file ticks (checked individually, exit 0, no edits)
- [x] Basic, Com, Choice/Session, Handles/Frames, Handles/AcqProbe,
      Splits/Redex, Splits/LocalHead, LSplit/Struct
- Simulation modules imported by B2 files, all exit 0: Support/{Base, Confine,
  FrameRename, InvFrame, HandleCount, AcqInv, AcqHandle},
  Support/Theorems/{SplitsLQ, SplitsRQ, DropShape, B1VacProbe},
  BackwardSoup/{GroupOrder, Position}
- Check 2 (119 s incl. queueing, exit 42): Choice/Retype.agda `Tm-re` missing
  `T-Ann`. Fixed: `Tm-re Rt x∉ y∉ (T-Ann ⊢e) = T-Ann (Tm-re Rt x∉ y∉ ⊢e)`.
- Check 3: `agda-check BorrowedCF/Safety/Preservation.agda` EXIT 0, 38 s wall
  (all other submodules cached from check 2), no warnings, no holes, no pragmas.

## Result
- [x] Choice/Retype.agda (one clause added). All other B2 files unchanged.
- DONE: Preservation.agda exit 0.
