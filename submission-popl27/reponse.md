Thanks to the reviewers for their thoughtful comments.

We first list the suggested revisions, then answer the specific
questions of each reviewer, and finally comment on the remaining remarks.

## Proposed revisions

* clarify choice of SMP
* clarify the discussion of effects
* change notation of `(𝜑𝑧 ↦ 𝜙)𝑃` and expand the explanation


## Review A

### why synchronization variables?

The low-level calculus of the present work is geared towards shared
memory multi-processing (SMP) where processes communicate via session-typed
channels. This is exactly the scenario targeted by channels in Go. The
same assumption also underlies some work that derives session types
from separation logic, for example:

Jules Jacobs, Jonas Kastberg Hinrichsen, Robbert Krebbers:
Dependent Session Protocols in Separation Logic from First Principles
(Functional Pearl). Proc. ACM Program. Lang. 7(ICFP): 768-795 (2023) 

One goal was to see if it was possible to avoid the overhead of
channel creation in the SMP setting.

The channel-based encoding suggested by the reviewer was investigated
in BST [Saffrich et al. 2025b]. We believe that one could swap the
low-level calculus with the BST solution just by changing the
translation. All higher level results remain intact.

### explain the purity constraints discussed in 654-633

There seems to be a misunderstanding. The effect system works exactly
like any other effect system: some operations are classified as
effect-producing, they are propagated in the expected way with latent
effects ending up on function arrows.

The difference is that some constructions, notably pair construction
and function application, require that one subexpression must be
effect-free, i.e., pure. Taking the example of pairs:

* unordered pairs (T-PairUnOrd): we know by construction that the contexts of the
  components are independent `Γ_1 ∥ Γ_2`, so we can just collect the
  effects.
* ordered pairs (T-PairOrd): `Γ_1,Γ_2` here the left context may contain a borrow
  and the right context its residual. If the left component does *not*
  fully consume the borrow, then it is unsafe for the right component
  to perfom an operation on the residual. Hence, the rule requires the
  right component to be pure. This is a crude, but safe approximation.
  
Function application is similar, but we have two kinds with different
evaluation orders, so the purity requirement flips. The first
subexpression to execute may have an effect, but the second must not.

### 7.2 heuristic incompleteness

To avoid confusion: the algorithmic system is sound and complete wrt
the declarative system. In 7.2 we are talking about the implementation
of constraint solving in the implementation of the algorithmic
system. The issue is that we are not aware of a unification algorithm
for the problem as described in 7.2. We designed and implemented the
heuristic approach explained in 7.2 and, so far, we did not run into
examples where it failed. Nevertheless, this step in the
implementation is most likely incomplete.

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
