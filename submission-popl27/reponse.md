Thanks to the reviewers for their thoughtful comments.

We first list the proposed revisions, then, for each reviewer, we
first answer the specific questions of each reviewer and then comment
on their remaining remarks. 

## Proposed revisions

* clarify choice of SMP
* clarify the discussion of effects
* revise the writing in 2.4 as explained below, in particular change the notation of 
  `(𝜑𝑧 ↦ 𝜙)𝑃` and expand the explanation 
* clarify F in RU-Discard
* add a running example to section 3 and 4

These changes can implemented in a week's work.
We plan to submit the mechanization of all metatheoretical results and
the typechecker implementation as an artifact.

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

We never say polymorphic recursion is a problem. 
We just state that it is needed for resource-passing
style. In the context of a Hindley-Milner type system,
it would require type annotations as it would be rejected by
the standard algorithms.
In the System-F context, as in CFST, it does not matter because 
typing must be explicit.

### wait/close in example

The $\nu$ restriction is explained in 271-276:

> Execution proceeds by repeatedly exposing the next local prefix of the channel sequence. Figure 2b
> shows a suffix of its reduction sequence. The 𝜈[c][d] in ... operator is a channel restriction as
> known from session calculi [Gay and Vasconcelos 2025]. It introduces a communication channel
> with endpoint names c and d. We generalize channel restriction so that each compartment [c] and
> [d] contains a binder group: a list of channel names and separator markers. Its working is best
> illustrated with the example trace.

The occurrence of the || is in 289-290:

> For remote borrowing, we incorporate the acquire primitive and indicate a remote split with the
> symbol “∥” in the compartment. As an example, we consider the
> translation of lines 5–7:

Regarding `[drop c1]` in 2c, see 339-341 (admittedly the notation,
which overloads the brackets may be confusing; we'll change that):

> Executing this code takes the steps shown in fig. 2c (ignoring the activity at the other
> end of the channel). The bracketed step abbreviates the forked process running renderProf until
> its final drop c1.

### the passage from 376-391 is inscrutable.

* optional means that the flag compartments have an option type like
  `Maybe Flag`
* Line 379 says "A synchronization binder (𝜑𝑧 ↦ 𝜙)𝑃 binds a flag name
  𝑧 in 𝑃 and stores one of two states in 𝜙: drop or acq. "
  So $\varphi z$ introduces the binding for $z$ and $\phi$ is its
  initial value, which can be drop or acq.

  We agree that the different phis may be confusing and will change
  the notation.
  
### discussion of rules
  
> "without consuming an unbounded residual owned elsewhere" why do we
> care? servers exist, they are supposed to run forever. Lots of
> channels are unbounded, they send streams of things. Maybe just a
> few more words on this. 

We'll improve the wording. Bounded means the session either comes to
an end in Close, Wait, or Drop; or it does not terminate. Technically,
we need to make sure that *if* the session comes to an end, then
either the channel gets closed (Close, Wait) or it was a borrow and
gets handed off (Drop). 
  
> Fig 6 rule Te-Seq2 - why don't you require S1 to be bounded? It
> seems if S1 is not bounded then the whole thing is not bounded? 

See above.

> fig 7 rule CT-LSplit why can't S2 be Skip?

For technical reasons. The restriction arose in a proof.
BTW, an lsplit with S2=Skip can be elided.


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

