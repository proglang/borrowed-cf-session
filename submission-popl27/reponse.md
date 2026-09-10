Thanks to the reviewers for their thoughtful comments.

We first list the proposed revisions, then, for each reviewer, we
first answer the specific questions of each reviewer and then comment
on their remaining remarks. 

## Proposed revisions

We will revise the paper as follows:

- Rewrite Section 2.4 to present synchronization cells as one shared-memory implementation of the remote-borrow handoff, and explain how a one-place asynchronous channel provides an alternative implementation for distributed runtimes.
- Redraw Figure 2c to show `drop` as an explicit reduction step, and clarify near Figure 2b that the two binder groups of a restriction denote opposite endpoints of the same channel.
- Simplify the synchronization notation, define optional flag components explicitly, and clarify that `done` in Figure 3 denotes removal of the flag rather than a third stored state.
- Expand the explanation of the purity side conditions with a concrete example showing how an effectful subexpression could use a residual endpoint before a packaged borrowed prefix has been consumed.
- Clarify that boundedness concerns safe finite completion rather than excluding infinite protocols, and explain directly why `Te-Seq2` requires only its second component to be bounded.
- Explain that the side condition on `CT-LSplit` excludes a redundant split with a `Skip` residual and preserves the canonical binder-group representation used by preservation.
- State explicitly that the implemented constraint solver is sound but incomplete, distinguish this from completeness of constraint generation, and report the scope of our implementation experience.
- Add running a example to Sections 3 and 4, clarify `F` in `RU-Discard`, and correct the noted typographical and punctuation errors.

Meanwhile, all metatheoretical results (preservation, progress;
forward and backward simulation; soundness and completeness of
algorithmic typing) come with mechanized proofs. The revised
artifact will include the mechanization and Rust typechecker, together
with its positive and negative examples. 

## Review A

### why synchronization variables?

RTSB should be understood as one shared-memory implementation of the
abstract handoff in CSTB, not as the only possible implementation. A
remote borrow needs a one-shot event: either a `drop`/`acquire`
synchronization cell or a one-shot channel. We chose a synchronization
cell because it is the minimal primitive needed by a shared-memory
runtime. 

We agree that a one-shot asynchronous channel` gives an equally
natural realization, and that would be the appropriate choice in a
distributed runtime (cf. the BST work by Saffrich et al). The
principal optimization claimed by the paper is independent of this choice: local borrows
require no synchronization, whereas remote borrows require a handoff
mechanism. Replacing cells by channels would leave the CSTB source
calculus, declarative typing, and direct semantics unchanged, while
requiring a different target translation and simulation argument. 

We will revise Section 2.4 to scope RTSB explicitly as a shared-memory
target and comment on the channel-based realization as an alternative.

### explain the purity constraints discussed in 654-633

The effect system works exactly like any other effect system: some
operations are classified as effect-producing, they are propagated in
the expected way with latent effects ending up on function arrows.
The additional purity premises serve a different purpose: they prevent
call-by-value evaluation from violating the temporal order imposed by
an ordered context. 

For example, suppose `c1` is a borrowed prefix and `c2` its
residual. In an ordered pair such as `c1 ⊗l recv c2`, evaluating the
left component merely packages `c1`; it does not consume the
prefix. If the right component were allowed to communicate, pair
construction could use the residual before the packaged prefix is
later consumed. Requiring the second component of `T-PairOrd` to be
pure rules this out. 

Directed application has a similar issue. The purity premise is
imposed on whichever expression would otherwise perform effects in an
order inconsistent with the way the arrow places its argument with
respect to the captured context (cf. T-AbsLeft vs T-AbsRight): the
function expression in `T-AppLeft`, and the argument in
`T-AppRight`. This is a conservative approximation; a more refined
effect system distinguishing phases of resource use could relax it. We
will add this explanation and example. 

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
actually stated because the proof of the completeness theorem was not
quite finished at submission time. In the revision, we can resolve
this inconsistency: The revised artifact contains a mechanized
completeness theorem for the annotated algorithmic judgment, and we
will state its precise hypotheses in the revised paper. This theorem
is independent of the implementation's candidate-selection heuristic,
which remains incomplete. 

Our current experience is limited to the implementation's test suite
and the examples in the paper; we have not encountered a failure on
those programs, but this is evidence of practical coverage rather than
a completeness result. We will report the scope of that evaluation
explicitly. 

## Review A - detailed comments

### Polymorphic recursion

We agree that polymorphic recursion is a legitimate language feature;
our wording incorrectly presented it as a defect. The issue is the
extra overhead on programming and inference: the CFST version must expose a
continuation-polymorphic type and instantiate it differently at
recursive calls, which requires annotations in an HM-style
setting. CSTB removes this continuation plumbing in the example. We
will replace "amends these problems" with wording that describes this
as an ergonomic and inference advantage, not a soundness or
expressiveness problem. 

### wait/close in example

`nu[B1][B2]P` binds the two endpoint groups of one channel; `close`
and `wait` can match only when they occur at opposite ends of the same
restriction. They cannot accidentally synchronize with operations
belonging to another restriction. We agree this is not evident in
Figure 2b and will state it directly in the caption and immediately
before the trace. (cf. explanation in 271-276)

### Figure 2c

We agree that `[drop c1]` is indistinguishable from process state in
the current trace. We will replace the annotated multi-step transition
with an explicit intermediate configuration showing the forked process
executing `drop c1`, followed by the separate `acquire c2` step. We
will also adapt the notation to avoid confusing `[drop c1]` with a
bindgroup. 

### the passage from 376-391 is inscrutable.

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

The restriction excludes a degenerate split. Because `S1;Skip` is
equivalent to `S1`, splitting off a `Skip` residual adds no expressive
power: the second result can only be discarded. Operationally,
however, `R-LSplit` would introduce a fresh binder for that residual,
while the binder-group typing represents `Skip` by the empty binder
group. The side condition preserves this canonical representation and
the associated preservation invariant. We will explain this
explicitly; programmers lose no useful split because the operation can
be elided. 


## Review B

### 1) New insights over BGV

The overarching insight with CSTB is the connection of a high-level calculus
with borrowing with a low-level target calculus operating directly on the
resources.

In BGV, every borrow creates a new channel over which the shared
resource, the actual communication channel, is passed. The frequent
creation of new channels pose an unnecessary inefficiency. CSTB
demonstrates that local borrows can be handled without any overhead, while
remote borrows can share the underlying resource with some form of
synchronization primitives.

The design of the direct semantics as well as arranging the low-level
calculus with tight simulation results was challenging.

### 2) Formalization

By the time of the submission, the mechanized proofs of some
metatheoretical results were still ongoing. There were significant
difficulties to get the details of the translation and the low-level
calculus in provable shape. By now, we have completed fully mechanized
proofs of all results. (see attachment)

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

> Can the equality rules of Figure 6 be applied anywhere in the context? i.e.,
> is \Gamma[\Gamma_1]=\Gamma[\Gamma_2], if \Gamma_1=\Gamma_2?

Correct, as stated in the figure "Equality of typing contexts is the
equivalence closure of the following axioms."

> Figure 8, e.g., rule T-AppUnr. Are the two premises required to have the same
> \epsilon? Why?

The rule T-Conv on the premises enables us to assume they have the
same $\epsilon$ (in the algorithmic system, we use least upper bound).
As CSTB has no subtyping, we cannot make the same assumption about
$\epsilon'$ on the arrow; hence the $\epsilon'\le\epsilon$.

> Figure 12, RU-discard: what is F?

The same context F as in the un-translated reductions: a process-local
context lifting an expression into the process level in some
expression evaluation context. 

## Review C

### Backward simulation

The specific difficulty of the backwards simulation proof was the
process congruence in the low-level target calculus, which had too
many degrees of freedom. We have a complete mechanized backwards
simulation proof, but for a slightly different presentation of the
low-level calculus as a soup of processes in place of explicit process
terms. The presentation is inspired by the paper [2]


### 7.2 heuristic incompleteness (see comments to A)

### Polymorphism

The choice to exclude polymorphism is deliberate because the situation is more
complex than in CFST. Constraints that track information about mobility and
equivalence are necessary, and the interplay of polymorphic variables with the
unification variables of CSTB and the heuristic for solving them has to be
investigated. We regard the addition of polymorphism as future work.

### Leaking local borrows

The type system statically enforces that a local borrow can never leak
across process boundaries. The type of a local borrow is never mobile
(`mbl`).  There are two ways a borrow could escape the local context but
either way the type system statically requires the borrow to be
mobile: a) it is sent over a channel, or b) it is used in an
expression that is evaluated in a forked thread.

### Subtyping

The original CFST work has no subtyping and CSTB is on par with that
system (i.e., same expressiveness). As the reviewer writes, CFST
subtyping is undecible, but nevertheless there is a paper that
describes a semi-algorithm to check subtyping of CFST [1]. The same
approach, along with the incomplete procedure from [1] could be
applied to CSTB, though we haven't investigated the ramifications. 

[1] Gil Silva, Andreia Mordido, Vasco T. Vasconcelos:
Subtyping context-free session types.
Theor. Comput. Sci. 1069: 115705 (2026)

[2] Jules Jacobs, Stephanie Balzer, Robbert Krebbers:
Connectivity graphs: a method for proving deadlock freedom based on
separation logic.
Proc. ACM Program. Lang. 6(POPL): 1-33 (2022)

