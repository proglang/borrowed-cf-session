# Group.agda rsplit repair (agent R1, 2026-10-07)

Plan: replace `¬ Skips t₁` in `acqHead-rsplit` by evidence about `t₂`, refute the
`Skips t₁` branch of `acq-;-split` by "t₂ does not start with acq", fill the two
holes in `bindCtx-rsplit`.

## Log
- BLOCKER found: `Local t₂ → t₂ ≃ acq ; u → ⊥` is FALSE. `NonLocal` has no `mu`
  constructor, so `t₂ = mu (acq ; ` zero)` is `Local`, `¬ Skips`, and `≃ acq ; t₂`.
  With `t₁ = skip`, `t = skip ; t₂ ≃ acq ; t₂` may head a non-first group, but the
  left part `skip ; ret` is not acq-headed, so `acqHead-rsplit` (and the recursive
  cases of `bindCtx-rsplit`) are false as stated. Checked counterexample in the
  scratchpad (`RsplitCex.agda`, loads with exit 0).
- done: `acqHead-rsplit` now takes `∀ u → ¬ (t₂ ≃ acq ; u)` (≃-stable) instead of
  `¬ Skips t₁`; proved, no holes.
- done: both former holes of `bindCtx-rsplit` filled with
  `acqHead-rsplit (local⇒¬acqHead L₂) teq I Sm′ ah`.
- private `local⇒¬acqHead : Local t₂ → ∀ u → ¬ (t₂ ≃ acq ; u)` via `AC.≃-cons` and
  private `cons-acq⇒nonLocal : Cons acq w z → NonLocal w`. Proved except the `mu`
  clause, which is a hole with goal `NonLocal (mu s)` (uninhabited; FALSE as stated).
  Closes with `mu c = mu (cons-acq⇒nonLocal c)` once upstream adds
  `mu : NonLocal s → NonLocal (mu s)` to `NonLocal`.

## Final check
`agda-check BorrowedCF/Safety/Preservation/Splits/Group.agda`: exit 42, ~9 s wall,
single error `UnsolvedInteractionMetas` at 158.36-40 (the `mu` hole). Nothing else fails.
