We thank the reviewers for their thoughtful comments. We will revise the paper to clarify the conceptual contribution, operational presentation, implementation scope, and metatheory. In particular, we will: (1) distinguish local borrowing, which needs no runtime synchronization, from remote borrowing, which requires a one-shot handoff; (2) redraw Figures 2c and 3 and simplify the synchronization notation; (3) add a running example to Sections 3–4; (4) explain purity, boundedness, `CT-LSplit`, and `T-Weaken`; (5) distinguish completeness of constraint generation from incompleteness of the implemented solver heuristic; and (6) correct the noted omissions and typographical errors.

Since submission, we have mechanized expression and process preservation and progress, algorithmic soundness and completeness, and forward simulation. We have also proved backward simulation for a revised process-soup presentation of the target calculus. The revision will state the correspondence with the submitted target precisely. The artifact will include the Agda development, Rust typechecker, and positive and negative examples.

## Review A

### Synchronization cells

RTSB is one shared-memory implementation of CSTB's abstract remote-borrow handoff. A remote borrow needs a one-shot event: `drop` signals completion of the borrowed prefix, and `acquire` enables the residual. A two-state cell realizes this directly in shared memory; a one-shot asynchronous channel would be equally natural in a distributed runtime. This choice does not affect the central optimization: local borrows need no synchronization, while remote borrows need a handoff. We will scope RTSB accordingly and discuss the channel-based alternative.

### Purity constraints

The purity premises prevent call-by-value evaluation from violating the temporal order represented by an ordered context. For example, in `c1 ⊗_l recv c2`, where `c1` is a borrowed prefix and `c2` its residual, evaluating the right component could use `c2` before the packaged `c1` is consumed. `T-PairOrd` therefore requires the second component to be pure. Directed application imposes purity on whichever subexpression would otherwise perform effects contrary to the arrow's ordering. This is a conservative approximation; a phase-sensitive effect system could be more permissive. We will add this example.

### Completeness and implementation

Constraint generation and solving are distinct. The revised artifact contains a mechanized completeness theorem for the annotated algorithmic judgment; we will state its hypotheses precisely. The Rust solver, however, considers only candidates exposed by simplification, then validates them with decidable CFST equivalence and mobility. It is sound but incomplete and may reject a typable program when no candidate is syntactically exposed. It succeeds on our current suite of 16 positive and 6 negative examples, but this is evidence of coverage, not completeness.

### Detailed comments

Polymorphic recursion is not a defect: the CFST encoding exposes continuation polymorphism that requires annotations in an HM-style setting, whereas CSTB removes this continuation plumbing. We will present this as an ergonomic and inference advantage.

In Figure 2b, `\nu[B_1][B_2]P` binds opposite endpoint groups of one channel, so `close` and `wait` cannot interact across restrictions. We will state this in the text and caption. Figure 2c will show `drop` and `acquire` as separate reductions and distinguish operations from binder groups. Figure 3 will define an optional handoff component as either `*` or a cell name; `drop` changes `pending` to `ready`, and `acquire` consumes the ready cell. `done` denotes removal, not a third state.

“Bounded” does not exclude infinite protocols. It requires every finite completion to reach `Close`, `Wait`, or `Drop`, preventing a movable endpoint from finishing while stranding an inaccessible residual. For `S1;S2`, if `S1` diverges, `S2` is never reached; if `S1` finishes, the boundary is determined by `S2`. Hence `Te-Seq2` requires only `bnd S2`.

`CT-LSplit` excludes `S2 = Skip` because `S1;Skip` is equivalent to `S1`; such a split adds no useful behavior but would create a fresh binder for a residual represented canonically by an empty binder group, complicating preservation.

## Review B

### Contribution beyond BGV

CSTB adds two insights. First, unlike syntactic prefix borrowing in BGV, splitting a CFST must be discovered modulo associativity, `Skip`, choice distributivity, and recursion; residual inference therefore requires solving constraints over CFST equivalence rather than structural traversal. Second, CSTB separates local from remote borrowing: ordered typing and evaluation let local aliases share an endpoint safely, whereas only cross-process borrows require runtime handoff. BGV's uniform translation obscures this distinction and introduces synchronization in both cases. The direct semantics specifies this distinction independently of implementation, while simulation connects it to the optimized target.

### Formalization and dynamics

Backward simulation was difficult because structural congruence allowed binders and redexes to appear in many equivalent target forms. The revised process-soup target gives processes and restricted resources explicit positions, enabling stable inversion; all claimed metatheoretic results are now mechanized.

`T-Weaken` is purely static: it adds unused unrestricted assumptions or replaces independence with stronger sequential ordering. It neither rewrites binder groups nor induces a runtime reduction; binder groups change only through operational rules. We will also call our contexts “tree-shaped,” noting that, unlike BI, their connectives distinguish ordered from unordered multiplicative composition.

We will carry the rendering example through Sections 3–4 to introduce mobility, direction, effects, context composition, and `lsplit`/`rsplit`. We will also correct the Listing 1 reference to lines 6–9; add missing `discard` syntax; state that context equality is closed under context formation; define `F` as a process-local lifted evaluation context; and clarify that the shared effect in `T-AppUnr` is a common upper bound, with the algorithm computing the least upper bound.

## Review C

The process-soup reformulation resolves backward-simulation inversion while preserving the operational primitives and translation idea; we will not claim that the theorem applies literally to the submitted syntax.

General polymorphism remains useful. We deliberately leave it to future work because quantified session variables interact nontrivially with residual inference, mobility, and CFST equivalence; borrowing removes continuation polymorphism from our examples, not the general need for polymorphism.

Local borrows cannot leak across process boundaries: capture by `fork` or transmission requires mobility, which local borrowed endpoints lack. Cross-process use must elaborate to `rsplit`, introducing `Drop` and `Acq`.

CSTB follows the original CFST calculus in providing equivalence but not subtyping. A system with subtyping would accept additional programs, but CFST subtyping is undecidable and would require an incomplete procedure or explicit coercions. We will qualify the expressiveness claim and discuss Silva et al.'s semi-decision approach. We will also discuss Mordido and Perez's deadlock-free CFST work.

## References

[1] Gil Silva, Andreia Mordido, Vasco T. Vasconcelos. “Subtyping context-free session types.” TCS 1069, 2026.

[2] Jules Jacobs, Stephanie Balzer, Robbert Krebbers. “Connectivity graphs: a method for proving deadlock freedom based on separation logic.” PACMPL 6 (POPL), 2022.
