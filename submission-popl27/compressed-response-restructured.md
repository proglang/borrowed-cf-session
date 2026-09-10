We thank the reviewers. We summarize revisions and requested answers below; full replies to remaining comments follow the marked boundary.

## Proposed revisions

We will sharpen the paper's central contribution: CFST borrowing requires residual inference modulo type equivalence, while distinguishing local from remote borrowing reveals that synchronization is needed only across process boundaries. We will add running examples, explain purity and boundedness, clarify the scope of the shared-memory target, simplify the synchronization notation, redraw Figures 2c and 3, and correct the reported omissions and errors. Since submission, we have mechanized expression and process preservation and progress, algorithmic soundness and completeness, forward simulation, and backward simulation for a revised process-soup target. We will state precisely how that target corresponds to the submitted calculus. The artifact will include the Agda development, Rust typechecker, and examples.

## Review A: specific questions

### Why synchronization variables?

We chose synchronization cells because RTSB is intended as a low-level **shared-memory** target: a remote borrow needs a one-shot handoff, and a two-state cell directly represents the runtime flag that `drop` sets and `acquire` waits for, without introducing target-level message passing solely to encode that flag. We did not intend to claim that cells are intrinsic to borrowing or suitable for every session runtime. The reviewer is right that a one-shot asynchronous channel is the natural realization in a distributed setting; replacing cells with such channels would preserve CSTB, its direct semantics, and the local/remote distinction, but require a different target translation and simulation proof. We will make this design rationale and scope explicit, present channels as the distributed alternative, and rewrite Section 2.4's currently opaque presentation.

### Why the purity constraints?

They prevent call-by-value evaluation from violating the temporal use order recorded by an ordered context. If `c1` is a borrowed prefix and `c2` its residual, evaluating `c1 ⊗_l recv c2` evaluates `recv c2` before the packaged `c1` is consumed. Requiring the second component of `T-PairOrd` to be pure prevents this premature residual use. Directed application imposes the analogous condition on the subexpression whose evaluation order conflicts with the arrow's ordering. This conservative restriction could be relaxed by a phase-sensitive effect system.

### Is the Section 7.2 heuristic incomplete?

Yes. Constraint generation now has a mechanized completeness theorem for the annotated algorithmic judgment. The implementation's candidate-selection heuristic is separately sound but incomplete: it considers candidates exposed by simplification and validates them using decidable CFST equivalence and mobility, so it may reject a typable program. It succeeds on our current 16 positive and 6 negative examples; we will report this as limited experience, not completeness evidence.

## Review B: specific questions

### New insights over BGV

First, a CFST residual cannot be found by syntactic prefix removal: splitting must be solved modulo associativity, `Skip`, choice distributivity, and recursion. Second, separating local and remote borrows shows that synchronization is not intrinsic to borrowing: ordered typing and evaluation make local splitting synchronization-free, while cross-process borrowing requires handoff. The direct semantics specifies this distinction independently of implementation, and the simulations validate the optimized target realization.

### Formalization

The main obstacle was backward inversion through target structural congruence: parallel composition, scope movement, and reordered restrictions expose a redex in many equivalent forms. A process-soup target gives processes and restricted resources explicit positions, enabling stable inversion. All claimed metatheoretic results are now mechanized.

### `T-Weaken`

`T-Weaken` is purely static. It adds unused unrestricted assumptions or strengthens independent context composition to sequential composition; it neither rewrites runtime binder groups nor induces a reduction. Its role is admissible context adjustment in typing and therefore in preservation/progress proofs. The binder groups in the reviewer's example cannot be transformed into one another by this rule.

## Review C: specific questions

Backward simulation is addressed by the process-soup reformulation above; we will not claim the new theorem literally for the submitted syntax. Constraint-generation completeness is now mechanized, while solver heuristic completeness remains open. Omitting polymorphism is deliberate: borrowing removes continuation polymorphism from our examples, not the general need for data or protocol polymorphism; quantified session variables interact nontrivially with residual inference, mobility, and CFST equivalence. Local borrows cannot leak into a fork: capture or transmission requires mobility, which locally borrowed endpoints lack; cross-process use must elaborate to `rsplit`. Finally, CSTB follows the original CFST calculus in providing equivalence but not subtyping. Subtyping would accept additional programs, but CFST subtyping is undecidable and would require an incomplete procedure or explicit coercions; we will qualify our expressiveness claim accordingly.

---

# END OF 750-WORD CORE RESPONSE

# Responses to remaining comments (included in full)

## Review A: detailed comments

### Polymorphic recursion

We agree that polymorphic recursion is a legitimate language feature; our wording incorrectly presented it as a defect. The issue is the programming and inference burden: the CFST version must expose a continuation-polymorphic type and instantiate it differently at recursive calls, which requires annotations in an HM-style setting. CSTB removes this continuation plumbing in the example. We will replace “amends these problems” with wording that describes this as an ergonomic and inference advantage, not a soundness or expressiveness problem.

### `wait`/`close` in the example

`\nu[B_1][B_2]P` binds the two endpoint groups of one channel; `close` and `wait` can match only when they occur at opposite ends of the same restriction. They cannot accidentally synchronize with operations belonging to another restriction. We agree this is not evident in Figure 2b and will state it directly in the caption and immediately before the trace.

### Figure 2c

We agree that `[drop c1]` is indistinguishable from process state in the current trace. We will replace the annotated multi-step transition with an explicit intermediate configuration showing the forked process executing `drop c1`, followed by the separate `acquire c2` step. We will also adapt the notation to avoid confusing `[drop c1]` with a binder group.

### The passage from lines 376–391

We agree that the notation obscures a simple one-shot protocol. We will first explain it without binders: an optional component is either `*` (no handoff) or the name of a handoff cell; `drop` changes that cell from `pending` to `ready`; `acquire` waits for `ready` and then removes the cell. We will use visibly distinct notation for the binder, name, and state, and defer the formal binder syntax to Section 6. The `done` label in Figure 3 denotes removal of the cell, not a third stored state; we will redraw it accordingly.

### Boundedness and `Te-Seq2`

Here “bounded” does not mean that the protocol cannot run forever. It means that every finite completion reaches an explicit boundary—`Close`, `Wait`, or `Drop`—so a movable endpoint cannot finish silently while leaving an inaccessible residual obligation. For `S1;S2`, if `S1` continues forever, control never reaches `S2` and no handoff is stranded; if `S1` finishes, the boundary behavior is determined by `S2`. This is why `Te-Seq2` requires only `bnd S2`. We will revise the terminology and explanation to prevent the natural “finite protocol” reading.

### Why can `S2` not be `Skip` in `CT-LSplit`?

The restriction excludes a degenerate split. Because `S1;Skip` is equivalent to `S1`, splitting off a `Skip` residual adds no expressive power: the second result can only be discarded. Operationally, however, `R-LSplit` would introduce a fresh binder for that residual, while binder-group typing represents `Skip` by the empty binder group. The side condition preserves this canonical representation and the associated preservation invariant. We will explain this explicitly; programmers lose no useful split because the operation can be elided.

We will also correct “und” to “and” and add the requested comma after “juxtaposition.”

## Review B: remaining comments

### Tree-shaped contexts and BI

We agree. Our contexts are tree-shaped like BI contexts, but their two connectives distinguish ordered from unordered multiplicative composition rather than additive from multiplicative composition. We will use “tree-shaped context” throughout and mention BI only as a structural analogy, with this distinction stated explicitly.

### Running examples

We will carry a version of the rendering example into Sections 3 and 4, using it to introduce mobility, direction and effect annotations, ordered versus unordered context composition, and the types of `lsplit` and `rsplit` before presenting the general rules.

### Minor comments

**Listing 1 reference.** Correct: line 290 should refer to lines 6–9.

**The domain of `\varphi` and `done`.** The domain of `\varphi` is `{drop, acq}`. `done` is meant to indicate removal of the synchronization flag. We will revise Figure 3b to make this explicit.

**Missing `discard`.** Correct: `discard` is accidentally omitted from Figure 4 and will be added.

**Context equality.** Correct: the equality axioms in Figure 6 apply within arbitrary context positions. We will state the congruence closure explicitly.

**Effects in `T-AppUnr`.** The premises use the same `epsilon` because the declarative rules may raise either inferred effect to a common upper bound using `T-Conv` and `p <= i`. The shared annotation therefore denotes the join of the two evaluation effects. The separate condition `epsilon' <= epsilon` ensures that the function body's latent effect is also covered by the conclusion. The algorithmic rule computes these upper bounds explicitly using a least upper bound. We will explain this near Figure 8.

**`F` in `RU-Discard`.** `F` is a process-local evaluation context obtained by lifting an expression evaluation context into a process. It is the same metavariable used in the source reduction rules. We will add its grammar or an explicit cross-reference before Figure 12.

## Review C: remaining comments

We thank the reviewer for pointing us to Mordido and Perez's work on deadlock-free CFSTs. We will discuss its relationship to CSTB in the Related Work section. We will also correct “und” to “and.”

## References

[1] Gil Silva, Andreia Mordido, Vasco T. Vasconcelos. “Subtyping context-free session types.” *Theoretical Computer Science* 1069: 115705 (2026).

[2] Jules Jacobs, Stephanie Balzer, Robbert Krebbers. “Connectivity graphs: a method for proving deadlock freedom based on separation logic.” *PACMPL* 6 (POPL): 1–33 (2022).
