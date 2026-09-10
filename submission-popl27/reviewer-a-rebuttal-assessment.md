# Reviewer A Rebuttal Assessment

## Scope

This assessment reviews `popl27.pdf`, Reviewer A's comments in `reviews.md`, and the current author response in `reponse.md`. It focuses on changes most likely to move Reviewer A's Overall Merit rating from B to A. No submission files were edited.

## Overall Assessment

Reviewer A is unusually movable: they explicitly say they are between A and B and would advocate for the paper after writing improvements. The current response contains most of the necessary technical substance, but it is unlikely to maximize that opportunity because it sometimes sounds defensive, leaves two questions with weak answers, and makes several claims that are inaccurate or stronger than the submitted paper supports.

The best strategy is:

1. Concede that synchronization cells are a target-specific choice.
2. Separate that choice from the paper's real contribution.
3. Explain purity with a concrete counterexample.
4. State the heuristic's incompleteness unambiguously.
5. Respond to every presentation complaint with an exact revision.

## Highest-Priority Problems

| Issue | Current problem | Recommended change |
|---|---|---|
| Synchronization cells | Introduces an SMP assumption absent from the paper and argues partly by precedent. | Present cells as one shared-memory realization of an abstract one-shot handoff; explicitly endorse the reviewer's channel implementation for distributed runtimes. |
| Purity | "There seems to be a misunderstanding" is defensive, and the final description of application is technically wrong. | Explain that the extra restriction controls effects during construction/evaluation, separately from latent function-body effects. |
| Completeness | Claims the algorithmic system is sound and complete, but the submitted PDF states only Theorem 8.7, soundness. | Either cite the exact new completeness theorem and hypotheses or retract the claim. Clearly distinguish constraint generation from the incomplete solver. |
| `CT-LSplit` | "For technical reasons" is exactly the kind of answer likely to keep A at B. | Explain the binder-group invariant and why a `Skip` residual is redundant. |
| Boundedness | The current definition is nearly tautological and does not explain `Te-Seq2`. | Explain that the predicate is about safe finite completion, not absence of infinite behavior. |
| Presentation objections | Existing paper text is quoted back to the reviewer. | Agree that the explanation occurs too late and promise concrete caption/figure changes. |
| Credibility | "All metatheoretical results" conflicts with the later qualification that backward simulation uses a different target presentation. | Enumerate exactly what is mechanized and for which calculus. |

## Synchronization Cells

The current answer should be substantially rewritten.

Problems:

- The paper begins with "processes, cores, or machines," so retroactively declaring RTSB to be an SMP-only design looks like moving the goalposts.
- "SMP" normally means symmetric multiprocessing, not "shared memory multi-processing."
- Go channels do not support the argument for using something other than channels.
- The important optimization is that **local borrows require no synchronization at all**. Whether remote handoff uses a cell or a one-place channel is secondary.
- "All higher-level results remain intact" is too broad: the source language and its metatheory may remain unchanged, but the target translation and simulation proof must be adapted.

Suggested replacement:

> RTSB should be understood as one shared-memory implementation of the abstract handoff in CSTB, not as the only possible implementation. A remote borrow needs a one-shot event: `drop` signals that the prefix is finished, and `acquire` waits for that signal. We represented this event by a two-state synchronization cell because it is the minimal primitive needed by a shared-memory runtime.
>
> We agree that a one-place asynchronous channel carrying `Unit` gives an equally natural realization, and would be the appropriate choice in a distributed runtime. The principal optimization claimed by the paper is independent of this choice: local borrows require neither a cell nor a channel, whereas remote borrows require one handoff mechanism. Replacing cells by channels would leave the CSTB source calculus, declarative typing, and direct semantics unchanged, while requiring a corresponding target translation and simulation argument.
>
> We will revise Section 2.4 to scope RTSB explicitly as a shared-memory target and add the channel-based realization as an alternative.

This response concedes the reviewer's practical point without surrendering the local/remote distinction--the actual novelty.

## Purity Constraints

The current explanation starts defensively and ends with an incorrect generalization:

> The first subexpression to execute may have an effect, but the second must not.

That is not what Figure 8 says. `T-AppLeft` requires the function expression--the first call-by-value subexpression--to be pure; `T-AppRight` requires the argument--the second--to be pure.

The missing conceptual distinction is between:

- the latent effect of the function body, already stored on the arrow; and
- effects performed immediately while constructing a pair or evaluating the function and argument before entering the body.

Suggested replacement:

> The reviewer is right that latent function-body effects can ordinarily be tracked separately from effects incurred while evaluating the function expression. Our arrow effect already performs that role. The additional purity premises serve a different purpose: they prevent eager evaluation from violating the temporal order represented by an ordered context.
>
> For example, suppose `c1` is a borrowed prefix and `c2` its residual. In an ordered pair such as `c1 ⊗l recv c2`, evaluating the left component merely packages `c1`; it does not consume the prefix. If the right component were allowed to communicate, pair construction could use the residual before the packaged prefix is later consumed. Requiring the second component of `T-PairOrd` to be pure rules this out.
>
> Directed application has the analogous issue. The purity premise is imposed on whichever expression would otherwise perform effects in an order inconsistent with the arrow's placement of its argument and captured context: the function expression in `T-AppLeft`, and the argument in `T-AppRight`. This is a conservative approximation; a more refined effect system distinguishing phases of resource use could relax it. We will add this explanation and example.

This directly answers the reviewer's effect-system comparison and makes the restriction look principled rather than arbitrary.

## Heuristic Incompleteness

The current answer contains the most serious factual risk.

The submitted PDF:

- announces "soundness and completeness" in the contributions and Section 8.3;
- explains both concepts;
- but states only Theorem 8.7, algorithmic soundness;
- explicitly says the implemented solver is a heuristic that may reject when no candidate is exposed.

Therefore, "the algorithmic system is sound and complete" is unsupported by the submitted paper unless a new theorem is now present in the attachment.

Suggested replacement:

> You are right that the implemented solver is incomplete. There are two separate questions here. Constraint generation produces equations whose solutions yield declarative typings; the implementation must then find such a solution. Our solver only considers candidates exposed by simplification, validates every candidate using decidable CFST equivalence and mobility, and is therefore sound, but it may reject a typable program when no suitable candidate is syntactically exposed.
>
> The submitted manuscript is also unclear about completeness: Section 8.3 announces completeness, but only the soundness theorem is actually stated. We will correct this inconsistency. If the revised artifact contains a mechanized completeness theorem for the annotated algorithmic judgment, we will state its precise hypotheses in the paper. This theorem does not make the implementation's candidate-selection heuristic complete.
>
> Our current experience is limited to the implementation's test suite and the examples in the paper; we have not encountered a failure on those programs, but this is evidence of practical coverage rather than a completeness result. We will report the scope of that evaluation explicitly.

The completeness sentence should be strengthened only if the exact theorem genuinely exists and corresponds to the revised paper algorithm.

## Detailed Comments

### Polymorphic Recursion

"We never say polymorphic recursion is a problem" is contradicted by the paper's phrase "CSTB amends these problems." It also dismisses a reasonable inference by the reviewer.

Suggested replacement:

> We agree that polymorphic recursion is a legitimate language feature; our wording incorrectly presented it as a defect. The issue is the programming and inference burden: the CFST version must expose a continuation-polymorphic type and instantiate it differently at recursive calls, which requires annotations in an HM-style setting. CSTB removes this continuation plumbing in the example. We will replace "amends these problems" with wording that describes this as an ergonomic and inference advantage, not a soundness or expressiveness problem.

### Figure 2b and Channel Matching

The current answer quotes an explanation the reviewer already read. Instead, answer the semantic question immediately:

> `nu[B1][B2]P` binds the two endpoint groups of one channel; `close` and `wait` can match only when they occur at opposite ends of that same restriction. They cannot accidentally synchronize with operations belonging to another restriction. We agree this is not evident in Figure 2b and will state it directly in the caption and immediately before the trace.

### Figure 2c

Accept the reviewer's proposed repair:

> We agree that `[drop c1]` is indistinguishable from process state in the current trace. We will replace the annotated multi-step transition with an explicit intermediate configuration showing the forked process executing `drop c1`, followed by the separate `acquire c2` step.

### Section 2.4 Notation

The response should not defend line 379. The visual presentation really is confusing, and Figure 3 adds an apparent third state, `done`.

Suggested replacement:

> We agree that the notation obscures a simple one-shot protocol. We will first explain it without binders: an optional component is either `*` (no handoff) or the name of a handoff cell; `drop` changes that cell from `pending` to `ready`; `acquire` waits for `ready` and then removes the cell. We will use visibly distinct notation for the binder, name, and state, and defer the formal binder syntax to Section 6. The `done` label in Figure 3 denotes removal of the cell, not a third stored state; we will redraw it accordingly.

### Boundedness and `Te-Seq2`

The current answer does not explain the rule.

Suggested replacement:

> Here "bounded" does not mean that the protocol cannot run forever. It means that every finite completion reaches an explicit boundary--`Close`, `Wait`, or `Drop`--so a movable endpoint cannot finish silently while leaving an inaccessible residual obligation. For `S1;S2`, if `S1` continues forever, control never reaches `S2` and no handoff is stranded; if `S1` finishes, the boundary behavior is determined by `S2`. This is why `Te-Seq2` requires only `bnd S2`. We will revise the terminology and explanation to prevent the natural "finite protocol" reading.

### `CT-LSplit` with `S2` Equivalent to `Skip`

"For technical reasons" should be removed.

Suggested replacement:

> The restriction excludes a degenerate split. Because `S1;Skip` is equivalent to `S1`, splitting off a `Skip` residual adds no expressive power: the second result can only be discarded. Operationally, however, `R-LSplit` would introduce a fresh binder for that residual, while the binder-group typing represents `Skip` by the empty binder group. The side condition preserves this canonical representation and the associated preservation invariant. We will explain this explicitly; programmers lose no useful split because the operation can be elided.

## Structural and Tone Changes

- Replace the vague proposed-revisions list with exact commitments: rewrite Section 2.4, redraw Figures 2c and 3, add the ordered-pair counterexample, clarify boundedness, and state the solver limitation.
- Delete "These changes can implemented in a week's work"; it contains a writing error and adds no persuasive value.
- Avoid "There seems to be a misunderstanding," "We never say," "See above," "for technical reasons," and "BTW."
- Acknowledge both minor edits explicitly: `und` to `and`, and the comma after "juxtaposition."
- Add a two-sentence significance statement before the reviewer-specific answers:

> The representation-independent contribution is the combination of splitting CFSTs modulo their equational theory with a static distinction between local and remote borrowing. This distinction turns local borrowing into ordered aliasing with no run-time synchronization, while isolating the unavoidable handoff mechanism to borrows that cross process boundaries.

- Reconcile the global artifact claim with the later backward-simulation qualification. State exactly which theorems are mechanized and whether they apply to the paper's target calculus or the revised process-soup presentation.

## Recommended Positioning

The response should communicate the following overall message:

> The reviewer identified real presentation defects; we understand them precisely; the synchronization representation is replaceable; and the core contribution survives unchanged.

That is the strongest route from Reviewer A's stated borderline B/A position to an A.
