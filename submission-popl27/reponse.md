We thank the reviewers for their thoughful comments. The reviews
identified several places where the presentation obscured the design,
as well as questions about the scope of the implementation and
metatheory. We first summarize the concrete revisions and then address
each reviewer's questions.

## Proposed revisions

We will revise the paper as follows:

- Rewrite Section 2.4 to present synchronization cells as one shared-memory
  implementation of the remote-borrow handoff, and explain how a one-shot
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
  excluding infinite protocols, and explain why `Te-Seq2` requires
  only its second component to be bounded.

- Explain why the side condition on `CT-LSplit` excludes a redundant split
  with a `Skip` residual and that it preserves the canonical binder-group
  representation used by preservation.

- State explicitly that the implemented constraint solver is sound but
  incomplete, distinguish this from completeness of constraint generation, and
  report the scope of our implementation experience.

- Add a running example to Sections 3 and 4, clarify `F` in `RU-Discard`, and
  correct the noted typographical and punctuation errors.

Since submission, we have completed mechanized proofs of expression
and process preservation and progress, algorithmic soundness and
completeness, and forward simulation. We have also completed backward
simulation for a revised, process-soup presentation of the low-level
calculus. The revision will explain the correspondence between the submitted
and revised target calculus. The artifact will include the Agda
development, the Rust typechecker, and its positive and negative
examples.

## Review A

### Why synchronization cells?

RTSB provides one shared-memory implementation of the abstract handoff
in CSTB, but other implementations are possible. A remote borrow needs
a one-shot event: `drop` signals completion of the borrowed prefix,
and `acquire` waits for that signal before enabling the residual. We
chose a two-state synchronization cell because it represents this
handoff directly in a shared-memory runtime. 

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

The reviewer is right that ordinary effect systems just collect
effects that occur while evaluating an expression and put latent
effects on the function arrow. The additional purity premises address
a separate issue: they prevent call-by-value evaluation from violating
the temporal use order represented by an ordered context.

For example, suppose `c1` is a borrowed prefix and `c2` its residual. Take the
ordered pair expression `e = c1 ⊗_l recv c2`, for example. Evaluating `e` will
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

The submitted manuscript is inconsistent about completeness: Section
8.3 announces a completeness result, but only algorithmic soundness is
stated as Theorem 8.7 because the completeness proof was unfinished at
submission. The revised artifact contains a mechanized completeness
theorem for the annotated algorithmic judgment, and we will add its
exact statement and hypotheses to the paper. This result concerns
constraint generation; it does not make the implementation's
candidate-selection heuristic complete.

Our current experience is limited to the implementation's test suite
(16 positive and 6 negative example programs) and the examples in the
paper; we have not encountered a failure on those programs, but this
is evidence of practical coverage rather than a completeness
result. We will report the scope of that evaluation explicitly.

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

`\nu[B_1][B_2]P` binds the two endpoint groups of one channel; `close`
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

The move from BGV to CSTB exposes two new issues. 

First, borrowing a regular session prefix is a syntactic operation in
BGV, whereas a CFST split must be discovered modulo associativity,
`Skip`, distributivity through choices, and recursion.  We obtain the
residual by solving constraints over CFST equivalence because it
cannot be obtained by a structural traversal. This is a technical
consequence of combining borrowing with CFSTs. 

Second, separating local from remote borrows reveals that
synchronization is not intrinsic to borrowing. A local split can
return two aliases to the same endpoint because ordered typing and
evaluation ensure that the prefix is consumed before the
residual. Only a borrow that crosses a process boundary requires a
run-time handoff. BGV's uniform translation obscures this distinction
and allocates synchronization machinery for both cases. 

The direct semantics serves as a representation-independent
specification of this distinction. Binder groups record the ordering
and handoff boundaries abstractly, while the low-level translation
realizes them using shared endpoint representations and
synchronization cells. The simulation results show that this optimized
realization implements the direct semantics. We will revise the
introduction and related-work section to present these as the main
conceptual and technical insights, rather than listing only
differences from BGV. 

### 2) Formalization

At submission time, the missing mechanized results were due to ongoing proof
work. The main difficulty regarding the backward simulation was due to
a higher degree of freedom in how binders could move in the target
calculus and thus relating target calculus terms to source terms. To
overcome this issue we revised the target calculus to use a
process-soup presentation, discussed in the response to reviewer C. By
now, we have completed the mechanized proofs of all results and will
include these in the updated artifact. The results include progress
and preservation for processes. 

### 3) Manifestation of T-Weaken in the dynamics

`T-Weaken` is purely static and has no corresponding reduction
rule. It changes the context under which an unchanged expression is
typed. The order permits two operations: adding unused unrestricted
assumptions, and replacing independence by a stronger sequential
ordering. For example, an expression typable under `x:T, y:U` may also
be typed under `x:T || y:U`, thereby promising to use the two
resources in that order even though they were independent before. 

 This static rule does not rewrite a run-time binder group. In
 particular, the two binder groups in the reviewer's example cannot be
 transformed into one another by `T-Weaken`; binder groups change only
 through the reduction rules for communication, splitting, dropping,
 acquiring, and discarding. 

### 4) BI contexts

We agree. Our contexts are tree-shaped like BI contexts, but their two
connectives distinguish ordered from unordered multiplicative
composition rather than additive from multiplicative composition. We
will use "tree-shaped context" throughout and mention BI only as a
structural analogy, with this distinction stated explicitly. 

### 5) running examples

We will carry a version of the rendering example into
Sections 3 and 4, using it to introduce mobility, direction and effect
annotations, ordered versus unordered context composition, and the
types of `lsplit` and `rsplit` before presenting the general rules.

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

The two premises use the same `epsilon` because the declarative rules
may raise either inferred effect to a common upper bound using
`T-Conv` and `p <= i`. Thus the shared annotation denotes the join of
the two evaluation effects. The separate condition `epsilon' <=
epsilon` ensures that the function body's latent effect is also
covered by the conclusion. The algorithmic rule computes these upper
bounds explicitly with a least upper bound. We will explain this near
Figure 8.

> Figure 12, RU-discard: what is F?

`F` is a process-local evaluation context obtained by lifting an
expression evaluation context into a process. It is the same
metavariable used in the source reduction rules. We will add its
grammar or an explicit cross-reference before Figure 12. 

## Review C

### Backward simulation

The obstacle was inversion through structural congruence in the target
calculus. With explicit process terms, associativity and
commutativity of parallel composition, scope movement, and reordering
of independent restrictions a target redex may be exposed in many
syntactically different ways. A backward proof must locate that redex
in the translated source configuration and reconstruct either a
matching source step or an administrative step; the submitted
presentation did not provide a sufficiently canonical decomposition
for this inversion. 

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

The omission is a deliberate choice. Borrowing removes the
continuation polymorphism and polymorphic 
recursion needed by the resource-passing versions of our examples, but ordinary
data and protocol polymorphism remain useful. Adding them to CSTB requires
studying the interaction between quantified session variables, the unification
variables introduced for residual inference, mobility constraints, and CFST
equivalence. We therefore leave polymorphism to future work and will
revise the paper to avoid suggesting that borrowing eliminates the
general need for it. 

### Leaking local borrows

The distinction is not ambiguous after elaboration. A borrow used entirely
within one process elaborates to `lsplit`. If either component is captured by
`fork` or sent over a channel, the relevant typing rule requires it to be
mobile; a locally borrowed endpoint is not mobile, so an attempted escape is
rejected. A borrow that is intended to cross the boundary must instead
elaborate to `rsplit`, which adds `Drop` and `Acq` and produces the mobile
residual needed for handoff.

### Subtyping

CSTB is aligned with the original CFST calculus, which also has type
equivalence but no subtyping, so borrowing does not remove a feature
present in CFST. Nevertheless, more
programs would be typable in a CFST system with
subtyping, particularly programs relying on width or protocol
refinements. Since CFST subtyping is undecidable, incorporating it
would require an incomplete procedure or explicit coercions. The
semi-decision approach of Silva et al. [1] may provide a starting point,
but we have not yet studied how it interacts with borrowing and
residual inference. We will qualify the expressiveness claim
accordingly.

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

