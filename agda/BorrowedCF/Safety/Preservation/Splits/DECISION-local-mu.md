# DECISION (resolved 2026-10-07, MW): `Local` misses recursive types

Status: option 1 applied 2026-10-07 and verified: Types/Predicates.agda has NonLocal.mu,
Group.agda is hole- and pragma-free, subTy-local (Algorithmic/Solved.agda) gained the mu
clause, and Algorithmic.agda + Completeness.agda check clean (exit 0).

## Counterexample (mechanised: `BorrowedCF/Safety/Probe/LocalMuGap.agda`, checks green)

Let `t₂ = mu (acq ; ` zero)`.

- `Local t₂` holds: no `NonLocal` constructor matches a `mu`.
- `¬ Skips t₂` holds.
- So the relaxed `rsplit` accepts `t = skip ; t₂` with `t₁ = skip`, `s′ = t₂`.
- But `skip ; t₂ ≃ acq ; t₂` (unfold the μ): the handle is acq-headed and may
  legally head a non-first binder group.
- After the split, the left group is headed by `⟨ skip ; ret ⟩ ≃ ⟨ ret ⟩`,
  which is NOT acq-headed: the `AcqHeadCtx` invariant of `BindCtx` is broken,
  so `acqHead-rsplit`/`bindCtx-rsplit` (Splits/Group.agda) are false as
  stated. The right part is `⟨ acq ; mu (acq ; …) ⟩`, the very `acq ; acq ; …`
  the relaxation wanted to exclude.

The point: `Local` is syntactic and not closed under `≃`, while the guarantee
it must give ("does not start with acq") is a property up to `≃`. `Skips`
has a `mu` constructor (Types/Syntax.agda:235); `NonLocal` does not.

## Fix options

1. **Minimal (recommended): add `mu : NonLocal s → NonLocal (mu s)`** in
   Types/Predicates.agda, mirroring `Skips.mu`. Then `mu (acq ; _)` is
   NonLocal and the counterexample dies. Collateral: `mu` clauses in
   `nonLocal-⋯`, `nonLocal-⋯ᵣ⁻¹`, `nonLocal-dual⁺/⁻`, a `mu` case in
   `skips⇒local`, and the decision procedure (Types/Unification.agda) gets a
   structural `mu` case. Group.agda's one remaining hole
   (`cons-acq⇒nonLocal`, the `mu` clause) then closes.
2. Semantic: `Local s = ∀ u → ¬ (s ≃ acq ; u)`. Cleaner specification,
   heavier to decide and to thread.

Nothing in Safety/ can close the gap locally; the choice belongs to the team
(predicate is Janek's, commit 469f079).
