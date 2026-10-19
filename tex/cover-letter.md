# CHANGES

Thanks to the reviewers for conditionally accepting our paper.
We detail the changes of the revision by commenting on our author response below.
Please review the changes in the accompanying latex diff.


> ## Proposed revisions
> 
> We will sharpen the paper's central contribution: CFST borrowing requires residual inference modulo type equivalence, while distinguishing local from remote borrowing reveals that synchronization is needed only across process boundaries.

Minor rewordings in the introduction.

> We will add running examples, explain purity and boundedness,

[Janek]

> clarify the scope of the shared-memory target, simplify the synchronization notation,

Section 2.4 has been rewritten.

> redraw Figures 2c and 3,

Figure 2c is now 2b (prior 2b is now 2a). Both have been redesigned and the explanation updated.
Elaboration examples now in Listing 2.

Figure 3 has been redrawn and updated to the new target calculus.

> and correct the reported omissions and errors. 

All reported problems corrected; see below for comments on specific reviewer questions.

> Since submission, we have mechanized expression and process preservation and progress, algorithmic soundness and completeness, forward simulation, and backward simulation

See updates in section 8. We submitted the mechanization for artifact evaluation.
It is also included in the supplement to this revision.

> for a revised process-soup target. We will state precisely how that target corresponds to the submitted calculus.

[Peter]

The main obstacle was backward inversion through target structural congruence: parallel composition, scope movement, and reordered restrictions expose a redex in many equivalent forms. A process-soup target gives processes and restricted resources explicit positions, enabling stable inversion. All claimed metatheoretic results are now mechanized.

Cf. ref [1]

> The artifact will include the Agda development, Rust typechecker, and examples.

Cf. artifact submission and supplement.

> 
> ## Review A: specific questions
> 
> ### Why synchronization variables?

[Peter]

> We chose synchronization cells because RTSB is intended as a low-level **shared-memory** target: a remote borrow needs a one-shot handoff, and a two-state cell directly represents the runtime flag that `drop` sets and `acquire` waits for, without introducing target-level message passing solely to encode that flag. We did not intend to claim that cells are intrinsic to borrowing or suitable for every session runtime. The reviewer is right that a one-shot asynchronous channel is the natural realization in a distributed setting; replacing cells with such channels would preserve CSTB, its direct semantics, and the local/remote distinction, but require a different target translation and simulation proof. We will make this design rationale and scope explicit, present channels as the distributed alternative, and rewrite Section 2.4's currently opaque presentation.
> 
> ### Why the purity constraints?

[Janek]

> They prevent call-by-value evaluation from violating the temporal use order recorded by an ordered context. If `c1` is a borrowed prefix and `c2` its residual, evaluating `c1 ⊗_l recv c2` evaluates `recv c2` before the packaged `c1` is consumed. Requiring the second component of `T-PairOrd` to be pure prevents this premature residual use. Directed application imposes the analogous condition on the subexpression whose evaluation order conflicts with the arrow's ordering. This conservative restriction could be relaxed by a phase-sensitive effect system.
> 
> ### Is the Section 7.2 heuristic incomplete?

[Janek]

> Yes. Constraint generation now has a mechanized completeness theorem for the annotated algorithmic judgment. The implementation's candidate-selection heuristic is separately sound but incomplete: it considers candidates exposed by simplification and validates them using decidable CFST equivalence and mobility, so it may reject a typable program. It succeeds on our current 16 positive and 6 negative examples; we will report this as limited experience, not completeness evidence.
> 
> ## Review B: specific questions
> 
> ### New insights over BGV

[Peter]

> First, a CFST residual cannot be found by syntactic prefix removal: splitting must be solved modulo associativity, `Skip`, choice distributivity, and recursion. Second, separating local and remote borrows shows that synchronization is not intrinsic to borrowing: ordered typing and evaluation make local splitting synchronization-free, while cross-process borrowing requires handoff. The direct semantics specifies this distinction independently of implementation, and the simulations validate the optimized target realization.
> 
> ### Formalization

See above.

> 
> ## Review C: specific questions

[Peter]

> Backward simulation is addressed by the process-soup reformulation above; we will not claim the new theorem literally for the submitted syntax. Constraint-generation completeness is now mechanized, while solver heuristic completeness remains open. Omitting polymorphism is deliberate: borrowing removes continuation polymorphism from our examples, not the general need for data or protocol polymorphism; quantified session variables interact nontrivially with residual inference, mobility, and CFST equivalence. Local borrows cannot leak into a fork: capture or transmission requires mobility, which locally borrowed endpoints lack; cross-process use must elaborate to `rsplit`. Finally, CSTB follows the original CFST calculus in providing equivalence but not subtyping. Subtyping would accept additional programs, but CFST subtyping is undecidable and would require an incomplete procedure or explicit coercions; we will qualify our expressiveness claim accordingly.
> 
> ---
> 
> # END OF 750-WORD CORE RESPONSE
> 
> # Responses to remaining comments (included in full)
> 
> ## Review A: detailed comments
> 
> ### Polymorphic recursion

Has been deemphasized. See introduction and motivation.

> ### `wait`/`close` in the example

See update of section 2.3 / 2.4.

> ### Figure 2c

Revamped.


> ### The passage from lines 376–391

*Optional synchronization flag* clarified in the rewrite of section 2.3/2.4.

> ### Boundedness and `Te-Seq2`

[Janek]

> Here “bounded” does not mean that the protocol cannot run forever. It means that every finite completion reaches an explicit boundary—`Close`, `Wait`, or `Drop`—so a movable endpoint cannot finish silently while leaving an inaccessible residual obligation. For `S1;S2`, if `S1` continues forever, control never reaches `S2` and no handoff is stranded; if `S1` finishes, the boundary behavior is determined by `S2`. This is why `Te-Seq2` requires only `bnd S2`. We will revise the terminology and explanation to prevent the natural “finite protocol” reading.
> 
> ### Why can `S2` not be `Skip` in `CT-LSplit`?

[Janek]

> 
> The restriction excludes a degenerate split. Because `S1;Skip` is equivalent to `S1`, splitting off a `Skip` residual adds no expressive power: the second result can only be discarded. Operationally, however, `R-LSplit` would introduce a fresh binder for that residual, while binder-group typing represents `Skip` by the empty binder group. The side condition preserves this canonical representation and the associated preservation invariant. We will explain this explicitly; programmers lose no useful split because the operation can be elided.
> 
> ## Review B: remaining comments
> 
> ### Tree-shaped contexts and BI

[Peter]

> We agree. Our contexts are tree-shaped like BI contexts, but their two connectives distinguish ordered from unordered multiplicative composition rather than additive from multiplicative composition. We will use “tree-shaped context” throughout and mention BI only as a structural analogy, with this distinction stated explicitly.
> 
> ### Running examples

[Janek]

> We will carry a version of the rendering example into Sections 3 and 4, using it to introduce mobility, direction and effect annotations, ordered versus unordered context composition, and the types of `lsplit` and `rsplit` before presenting the general rules.
> 
> ### Minor comments
> 

All addressed.

> 
> ## Review C: remaining comments

[Peter]

> We thank the reviewer for pointing us to Mordido and Perez's work on deadlock-free CFSTs. We will discuss its relationship to CSTB in the Related Work section. 


## References

[1] Jules Jacobs, Stephanie Balzer, Robbert Krebbers. “Connectivity graphs: a method for proving deadlock freedom based on separation logic.” *PACMPL* 6 (POPL): 1–33 (2022).

