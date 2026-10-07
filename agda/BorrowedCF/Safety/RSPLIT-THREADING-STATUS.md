# R2: thread rsplit/lsplit evidence through Preservation and Progress

## Plan
- Iterate `agda-check BorrowedCF/Safety/Preservation.agda` and `.../Progress.agda`.
- Fix each reported site: lsplit pattern arity (5 args), rsplit evidence
  (`Local s′` replaces `¬ Skips s`), calls to Group's `bindCtx-rsplit`.
- No edits to Splits/Group.agda or outside Safety/. No holes, no pragmas.

## Errors found / fixed
- Progress/Expr.agda:116 `lsplit pattern 4 -> 5 args. FIXED (edit).
- Preservation/LSplit/Immobile.agda:110, LSplit/Mobile.agda:232: `lsplit
  inversion pattern gets `L₂`. FIXED (edit, found by grep).
- Preservation/RSplit.agda:94/316 + rsplit-bindCtx calls: evidence is now
  `L₂ ¬S₂`. FIXED.
- Splits/Redex.agda rsplit-bindCtx body: binds `L₂`, passes it to
  bindCtx-rsplit. FIXED.
- RSplit.agda `mob-rsplit` (and `θR-⇒`) used `¬ Skips t₁` to refute the
  Skips-t₁ branch. Now take `Local t₂`; branch refuted by
  `local⇒¬acqHead′` from NEW Splits/LocalHead.agda, which derives
  `Local t₂ → ¬ Skips t₂ → ∀ u → ¬ (t₂ ≃ acq ; u)` by running Group's public
  `bindCtx-rsplit` on a [0, 1] binder context (no new hole; it inherits
  Group's single `mu` hole). LocalHead.agda checks green.

## Final
- `agda-check BorrowedCF/Safety/Progress.agda`: exit 0, 1m41s wall.
- `agda-check BorrowedCF/Safety/Preservation.agda`: exit 0, 5m42s wall
  (clean re-run after all edits).
- No new holes or pragmas. LocalHead.agda goes through Group's public
  `bindCtx-rsplit`, so it stays valid when R3 closes the `mu` hole. If Group
  later exports `local⇒¬acqHead`, LocalHead can shrink to a re-export.
