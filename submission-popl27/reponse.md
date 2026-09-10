Thanks to the reviewers for their thoughtful comments.

We first list the proposed revisions, then, for each reviewer, we
first answer the specific questions of each reviewer and then comment
on their remaining remarks. 

## Proposed revisions

We will revise the paper as follows:

- Rewrite Section 2.4 to present synchronization cells as one shared-memory
  implementation of the remote-borrow handoff, and explain how a one-place
  asynchronous channel provides an alternative implementation for distributed
  runtimes.

- Redraw Figure 2c to show `drop` as an explicit reduction step, and clarify
  near Figure 2b that the two binder-groups of a restriction denote opposite
  endpoints of the same channel.

- Simplify the synchronization notation, define optional flag components
  explicitly, and clarify that `done` in Figure 3 denotes removal of the flag
  rather than a third stored state.

- Expand the explanation of the purity side conditions with a concrete example
  showing how an effectful subexpression could use a residual endpoint before a
  packaged borrowed prefix has been consumed.

- Clarify that boundedness concerns safe finite completion rather than
  excluding infinite protocols, and explain directly why `Te-Seq2` requires
  only its second component to be bounded.

- Explain that the side condition on `CT-LSplit` excludes a redundant split
  with a `Skip` residual and preserves the canonical binder-group
  representation used by preservation.

- State explicitly that the implemented constraint solver is sound but
  incomplete, distinguish this from completeness of constraint generation, and
  report the scope of our implementation experience.

- Add a running example to Sections 3 and 4, clarify `F` in `RU-Discard`, and
  correct the noted typographical and punctuation errors.

Meanwhile, all metatheoretical results (preservation, progress;
forward and backward simulation; soundness and completeness of
algorithmic typing) come with mechanized proofs. The revised
artifact will include the mechanization and Rust typechecker, together
with its positive and negative examples.

## Review A

### Why synchronization variables?

RTSB should be understood as one shared-memory implementation of the
abstract handoff in CSTB, not as the only possible implementation. A
remote borrow needs a one-shot event: either a `drop`/`acquire`
synchronization cell or a one-shot channel. We chose a synchronization
cell because it is the minimal primitive needed by a shared-memory
runtime.

We agree that a one-shot asynchronous channel gives an equally
natural realization, and that would be the appropriate choice in a
distributed runtime (cf. the BST work by Saffrich et al). The
principal optimization claimed by the paper is independent of this choice: local borrows
require no synchronization, whereas remote borrows require a handoff
mechanism. Replacing cells by channels would leave the CSTB source
calculus, declarative typing, and direct semantics unchanged, while
requiring a different target translation and simulation argument.

We will revise Section 2.4 to scope RTSB explicitly as a shared-memory
target and comment on the channel-based realization as an alternative.

### Explain the purity constraints discussed in 654-633

The effect system works exactly like any other effect system: some operations
are classified as effect-producing and effects are propagated in the expected
way with latent effects ending up on function arrows. The additional purity
premises serve a different purpose: they prevent call-by-value evaluation from
violating the temporal order imposed by an ordered context.

For example, suppose `c1` is a borrowed prefix and `c2` its residual. Take the
ordered pair expression `e = c1 ⊗l recv c2`, for example. Evaluating `e` will
first evaluate `c1` and then move on to evaluate `recv c2` before packaging the
result into a pair. An evaluation of `c1` is different from consuming it. If
the right component were allowed to communicate, pair construction could use
the residual before the packaged prefix is later consumed. Requiring the second
component of `T-PairOrd` to be pure rules this out. The expression `e` is not
typable in CTSB.

Directed application has a similar issue. The purity premise is imposed on
whichever expression would otherwise perform effects in an order inconsistent
with the way the arrow places its argument with respect to the captured context
(cf. T-AbsLeft vs T-AbsRight): the function expression in `T-AppLeft`, and the
argument in `T-AppRight`.

This is a purity requirements are a conservative approximation; a more refined
effect system distinguishing phases of resource use could relax it. We will add
this explanation and example.

### 7.2 heuristic incompleteness

You are right that the implemented solver is incomplete. There are two
separate questions here. Constraint generation produces equations
whose solutions yield declarative typings; the implementation must
then find such a solution. Our solver only considers candidates
exposed by simplification, validates every candidate using decidable
CFST equivalence and mobility, and is therefore sound, but it may
reject a typable program when no suitable candidate is syntactically
exposed.

The submitted manuscript is a bit unclear about completeness: Section
8.3 announces completeness, but only the soundness theorem is
actually stated because the proof of the completeness theorem was not quite
finished at submission time. The revised artifact will contain a mechanized
completeness theorem for the annotated algorithmic judgment, and we will state
its precise hypotheses in the revised paper. This theorem is independent of the
implementation's candidate-selection heuristic, which remains incomplete.

Our current experience is limited to the implementation's test suite
and the examples in the paper; we have not encountered a failure on
those programs, but this is evidence of practical coverage rather than
a completeness result. We will report the scope of that evaluation
explicitly.

## Review A - detailed comments

### Polymorphic recursion

We agree that polymorphic recursion is a legitimate language feature;
our wording incorrectly presented it as a defect. The issue is the programming
and inference burden: the CFST version must expose a continuation-polymorphic
type and instantiate it differently at recursive calls, which requires
annotations in an HM-style setting. CSTB removes this continuation plumbing in
the example. We will replace "amends these problems" with wording that
describes this as an ergonomic and inference advantage, not a soundness or
expressiveness problem.

### wait/close in example

`nu[B1][B2]P` binds the two endpoint groups of one channel; `close`
and `wait` can match only when they occur at opposite ends of the same
restriction. They cannot accidentally synchronize with operations
belonging to another restriction. We agree this is not evident in
Figure 2b and will state it directly in the caption and immediately
before the trace.

### Figure 2c

We agree that `[drop c1]` is indistinguishable from process state in
the current trace. We will replace the annotated multi-step transition
with an explicit intermediate configuration showing the forked process
executing `drop c1`, followed by the separate `acquire c2` step. We will also
adapt the notation to avoid confusing `[drop c1]` with a binder-group. 

### The passage from 376-391 is inscrutable.

We agree that the notation obscures a simple one-shot protocol. We
will first explain it without binders: an optional component is either
`*` (no handoff) or the name of a handoff cell; `drop` changes that
cell from `pending` to `ready`; `acquire` waits for `ready` and then
removes the cell. We will use visibly distinct notation for the
binder, name, and state, and defer the formal binder syntax to
Section 6. The `done` label in Figure 3 denotes removal of the cell,
not a third stored state; we will redraw it accordingly.

We agree that the different phis may be confusing and will change
the notation.
  
### Boundedness and `Te-Seq2`

> "without consuming an unbounded residual owned elsewhere" why do we
> care? servers exist, they are supposed to run forever. Lots of
> channels are unbounded, they send streams of things. Maybe just a
> few more words on this. 

Here "bounded" does not mean that the protocol cannot run forever. It
means that every finite completion reaches an explicit
boundary--`Close`, `Wait`, or `Drop`--so a movable endpoint cannot
finish silently while leaving an inaccessible residual obligation. For
`S1;S2`, if `S1` continues forever, control never reaches `S2` and no
handoff is stranded; if `S1` finishes, the boundary behavior is
determined by `S2`. This is why `Te-Seq2` requires only `bnd S2`. We
will revise the terminology and explanation to prevent the natural
"finite protocol" reading.


> fig 7 rule CT-LSplit why can't S2 be Skip?

The restriction excludes a degenerate split. Because `S1;Skip` is equivalent to
`S1`, splitting off a `Skip` residual adds no expressive power: the second
result can only be discarded. Operationally, however, `R-LSplit` would
introduce a fresh binder for that residual, while the binder-group typing
represents `Skip` by the empty binder-group. The side condition preserves this
canonical representation and the associated preservation invariant. We will
explain this explicitly; programmers lose no useful split because the operation
can be elided.


## Review B

### 1) New insights over BGV

The overarching insight with CSTB is the connection of a high-level calculus
with borrowing with a low-level target calculus operating directly on the
resources.

In BGV, every borrow creates a new channel over which the shared resource, the
actual communication channel, is passed. The frequent creation of new channels
introduces unnecessary allocation and synchronization machinery. CSTB
demonstrates that local borrows can be handled without any overhead, while
remote borrows can share the underlying resource using an explicit one-shot
handoff.

The design of the direct semantics as well as arranging the low-level
calculus with tight simulation results was challenging.

### 2) Formalization

At submission time, the missing mechanized results were due to ongoing proof
work. The main difficulties was due to a higher degree of freedom in how
binders could move in the target calculus and thus relating target calculus
terms to source terms. By now, we have completed the mechanized proofs of all
results and will include these in the updated artifact. The results include
progress and preservation for processes.

### 3) Manifestation of T-Weaken in the dynamics

The T-Weaken rule is not reflected in the semantics. In the
preservation proof it appears mainly in the inversion lemmas because
this rule is not syntax-driven (module Terms.Base). The progress proof
by itself just skips over it (module Reduction/Expressions).

> consider a program of the form \nu x[c][d]\ldots, where c = ((x
> \parallel y)(z \parallel d)). Can the program be rewritten as \nu
> x[c'][d]\ldots where c' = (xz \parallel yd), or vice versa? 

No, it cannot be rewritten. Changes in the binding compartment can
only happen by reduction (cf. sections 2.3 / 2.4).

> If so, which rule allows this rewriting? If not, what role does the
> T-Weaken rule play in the dynamics, and how does it contribute to
> the progress and preservation theorems?

T-Weaken only rearranges bindings in the environment. It also enables
adding sequentiality constraints: if `x : T || y : U` were independent before, 
then they could be required to be used in sequence after T-Weaken:
`x : T ; y : U`.

### 4) BI contexts

Will adopt your suggestion to use *tree-shaped contexts* instead of
*BI-contexts*. (In one place 446, we write more accurately 
*in the style of BI-contexts*.)

### 5) running examples

Good suggestion.

### Minor comments

> Line 290. lines 5-7 → 6-9 in Listing 1?

Correct. Line 290 should refer to lines 6-9.

> Section 2.4 states \phi:drop or acq but in Figure 3(b), we also have z
> \mapsto done. Also, what is the domain of \varphi? Is it just a label?

The domain of \varphi is {drop,acq}. `done` is meant to indicate removal of the
synchronization flag. We will revise Figure 3b to clarify.

> Is discard missing from the syntax of Figure 4?

Correct. `discard` is accidentally omitted and will be added.

> Can the equality rules of Figure 6 be applied anywhere in the context? i.e.,
> is \Gamma[\Gamma_1]=\Gamma[\Gamma_2], if \Gamma_1=\Gamma_2?

Correct, as stated in the figure "Equality of typing contexts is the
equivalence closure of the following axioms."

> Figure 8, e.g., rule T-AppUnr. Are the two premises required to have the same
> \epsilon? Why?

The two premises use the same \epsilon because the declarative rules may raise
either effect to a common upper bound using T-Conv. Thus the shared annotation
denotes the join of the two evaluation effects. The separate condition
$\epsilon' \le epsilon$ ensures that the function body's latent effect is also
covered by the conclusion. The algorithmic rule computes these upper bounds
explicitly with a least upper bound.

> Figure 12, RU-discard: what is F?

The same context F as in the un-translated reductions: a process-local
context lifting an expression into the process level in some expression
evaluation context. We will add an explicit reference before Figure 12.


## Review C

### Backward simulation

The obstacle was inversion through structural congruence in the low-level
target calculus. The structural congruence of translated process terms resulted
in too many degrees of freedom. A backward proof must locate the redex in the
translated source configuration and reconstruct either a matching source step
or an administrative step; the submitted presentation did not provide a
sufficiently canonical decomposition for this inversion.

We resolved the problem by presenting the target as a soup of processes and
restricted resources. The soup representation gives each process and
synchronization resource an explicit position, making redex location and
reconstruction stable under reordering. We now have a complete mechanized
backward-simulation proof for this revised target presentation. The operational
primitives and translation idea are unchanged, but the theorem is not literally
a proof for the submitted syntax; we will revise Section 6 and state the
correspondence precisely. The presentation is inspired by the paper [2].

### 7.2 heuristic incompleteness

As explained in our response to Reviewer A, constraint generation now has a
mechanized completeness theorem for the annotated judgment, whereas the
implementation's candidate-selection heuristic remains sound but incomplete.

### Polymorphism

The omission is a deliberate choice, not a claim that borrowing subsumes
polymorphism. Borrowing removes the continuation polymorphism and polymorphic
recursion needed by the resource-passing versions of our examples, but ordinary
data and protocol polymorphism remain useful. Adding them to CSTB requires
studying the interaction between quantified session variables, the unification
variables introduced for residual inference, mobility constraints, and CFST
equivalence.

### Leaking local borrows

The distinction is not ambiguous after elaboration. A borrow used entirely
within one process elaborates to `lsplit`. If either component is captured by
`fork` or sent over a channel, the relevant typing rule requires it to be
mobile; a locally borrowed endpoint is not mobile, so an attempted escape is
rejected. A borrow that is intended to cross the boundary must instead
elaborate to `rsplit`, which adds `Drop` and `Acq` and produces the mobile
residual needed for handoff.

### Subtyping

The original CFST work has no subtyping and CSTB is on par with that
system (i.e., same expressiveness). As the reviewer writes, CFST
subtyping is undecidable, but nevertheless there is a paper that
describes a semi-algorithm to check subtyping of CFST [1]. The same
approach, along with the incomplete procedure from [1] could be applied to
CSTB, though we have not investigated the ramifications. 

### Related work

We thank the reviewer for pointing us to Mordido and Perez's work on
deadlock-free CFSTs. We will discuss its relationship to CSTB in the Related
Work section.


## References

[1] Gil Silva, Andreia Mordido, Vasco T. Vasconcelos: Subtyping context-free
session types. Theor. Comput. Sci. 1069: 115705 (2026)

[2] Jules Jacobs, Stephanie Balzer, Robbert Krebbers:
Connectivity graphs: a method for proving deadlock freedom based on
separation logic.
Proc. ACM Program. Lang. 6(POPL): 1-33 (2022)

