# Revised Author Response: Improvement Report

## Executive Summary

The revised response is substantially stronger for Reviewer A. It now accepts the reviewer's central implementation concern, explains the purity restrictions with a useful example, distinguishes constraint generation from heuristic solving, and gives concrete revision commitments.

The main remaining problem is imbalance: the Reviewer A section is now careful and persuasive, while much of the Reviewer B and C material remains terse, vague, or defensive. Since all three reviewers currently assign B, the response should aim to move all three, even if Reviewer A remains the primary target.

The highest-priority improvements are:

1. Reconcile the global claim that all results are mechanized with the later statement that backward simulation is proved for a different presentation of the target calculus.
2. Replace the Reviewer B novelty answer; it currently asserts that the development was challenging without explaining the new insights or challenges.
3. Give a more precise account of `T-Weaken`, including its role in preservation and progress.
4. Answer every Reviewer B minor comment, especially the missing `discard` syntax and incorrect Listing 1 line reference.
5. Strengthen the Reviewer C answers on backward simulation, polymorphism, local-borrow escape, and subtyping.
6. Remove remaining defensive, tentative, and informal phrasing.
7. Correct several typographical and notation errors in the response itself.

## Global Issues

### 1. Opening Paragraph

The opening repeats "first" and describes the document's organization rather than framing the contribution.

Current text:

> We first list the proposed revisions, then, for each reviewer, we first answer the specific questions of each reviewer and then comment on their remaining remarks.

Suggested replacement:

> We thank the reviewers for their careful and constructive comments. The reviews identified several places where the presentation obscured the design, as well as questions about the scope of the implementation and metatheory. We first summarize the concrete revisions and then address each reviewer's questions.

This immediately communicates that the authors understood the reviews and are taking action.

### 2. Proposed Revisions

The revised list is good and specific. Correct this typo:

> Add running a example

to:

> Add a running example

The mechanization paragraph should not begin with "Meanwhile," and its current universal claim conflicts with the Reviewer C answer. If backward simulation is mechanized only after replacing explicit process terms with a process-soup presentation, then it is misleading to say without qualification that all results for the submitted system have mechanized proofs.

Suggested replacement:

> Since submission, we have completed mechanized proofs of expression and process preservation and progress, algorithmic soundness and completeness, and forward simulation. We have also completed backward simulation for a revised, process-soup presentation of the low-level calculus. The revision will state precisely which presentation each theorem concerns and explain the correspondence between the submitted and revised target calculi. The artifact will include the Agda development, the Rust typechecker, and its positive and negative examples.

Use this wording only if each listed result has actually been checked in the artifact. Otherwise enumerate the smaller verified set.

### 3. Contribution Framing

The response should state the representation-independent contribution before discussing implementation choices. This helps both Reviewer A and Reviewer B.

Suggested paragraph after the proposed revisions:

> The central contribution is not the particular synchronization primitive used by RTSB. It is the combination of session-type splitting modulo CFST equivalence with a static distinction between local and remote borrows. Local borrows become ordered aliases requiring no run-time handoff, while remote borrows expose the handoff explicitly. This distinction is reflected consistently in the type system, direct semantics, and implementation translation.

## Reviewer A

The Reviewer A section is now persuasive overall. The following refinements would improve precision and tone.

### 1. Synchronization Cells

Correct the stray backtick in:

> a one-shot asynchronous channel`

Rename the heading from "why synchronization variables?" to "Why synchronization cells?" to match the terminology used in the paper and revised answer.

The phrase "minimal primitive" is stronger than necessary and invites another implementation debate. A synchronization cell may be a direct primitive, but the paper provides no cost model proving minimality.

Suggested replacement for the first paragraph:

> RTSB should be understood as one shared-memory implementation of the abstract handoff in CSTB, not as the only possible implementation. A remote borrow needs a one-shot event: `drop` signals completion of the borrowed prefix, and `acquire` waits for that signal before enabling the residual. We used a two-state synchronization cell because it represents this handoff directly in a shared-memory runtime.

Change "one-shot asynchronous channel" to "one-place asynchronous channel carrying `Unit`," which mirrors the reviewer's concrete proposal.

### 2. Purity

The explanation is technically much better, but its opening still risks sounding dismissive:

> The effect system works exactly like any other effect system

It is also too broad: the unusual purity restrictions are precisely what the reviewer is asking about.

Suggested replacement:

> The reviewer is right that ordinary effect systems distinguish effects incurred while evaluating a function expression from the latent effects of its body. CSTB's arrow annotation already records the latent effect. The additional purity premises address a separate issue: they prevent call-by-value evaluation from violating the temporal use order represented by an ordered context.

Use typographically unambiguous notation such as `c1 \otimes_l recv c2` or the paper's exact rendered symbol instead of `c1 ⊗l recv c2`.

### 3. Heuristic Incompleteness

This section is strong but contains unnecessarily tentative language:

- "a bit unclear" understates a real inconsistency.
- "we can resolve" should be "we will resolve."
- "not quite finished" is informal.

Suggested replacement for the middle paragraph:

> The submitted manuscript is inconsistent about completeness: Section 8.3 announces a completeness result, but only algorithmic soundness is stated as Theorem 8.7 because the completeness proof was unfinished at submission. The revised artifact contains a mechanized completeness theorem for the annotated algorithmic judgment, and we will add its exact statement and hypotheses to the paper. This result concerns constraint generation; it does not make the implementation's candidate-selection heuristic complete.

The empirical statement should be quantified if space permits. The artifact currently contains 16 positive and 6 negative example programs, in addition to unit tests. Reporting those numbers is more informative than "the test suite."

### 4. Polymorphic Recursion

Replace "extra overhead on programming and inference" with "programming and inference burden." The issue is not run-time overhead.

Suggested sentence:

> The issue is the programming and inference burden: the CFST version must expose a continuation-polymorphic type and instantiate it differently at recursive calls.

### 5. Figures and Notation

Use mathematical notation consistently:

> `nu[B1][B2]P`

should be rendered as `\nu[B_1][B_2]P` or with the exact notation from the paper.

Delete the parenthetical:

> (cf. explanation in 271-276)

It partially revives the earlier defensive response that the explanation was already present. The key point is that it appeared too late.

Change "bindgroup" to "binder group."

Delete the duplicate final sentence in the Section 2.4 answer:

> We agree that the different phis may be confusing and will change the notation.

The preceding paragraph already makes this commitment more precisely.

### 6. Minor Comments

Reviewer A explicitly identified `und` and the punctuation around "juxtaposition." Add a one-sentence response rather than mentioning these only in the revision list:

> We will correct `und` to `and` and add the requested comma after "juxtaposition."

## Reviewer B

This section now needs the most work.

### 1. New Insights over BGV

The current answer is too generic. It says the overarching insight is a connection between two calculi, repeats the efficiency claim, and concludes that the work was "challenging." Reviewer B explicitly asks what new insights and technical challenges arise. Merely asserting difficulty is unlikely to change the score.

Suggested complete replacement:

> The move from BGV to CSTB is not a direct substitution of context-free for regular session types. It exposes two new issues.
>
> First, borrowing a regular session prefix is syntactic after unfolding, whereas a CFST split must be discovered modulo associativity, `Skip`, distributivity through choices, and recursion. The residual is therefore not obtained by a structural traversal; it becomes a constraint-solving problem over CFST equivalence. This is the principal technical consequence of combining borrowing with CFSTs.
>
> Second, separating local from remote borrows reveals that synchronization is not intrinsic to borrowing. A local split can return two aliases to the same endpoint because ordered typing and evaluation ensure that the prefix is consumed before the residual. Only a borrow that crosses a process boundary requires a run-time handoff. BGV's uniform translation obscures this distinction and allocates synchronization machinery for both cases.
>
> The direct semantics then serves as a representation-independent specification of this distinction. Binder groups record the ordering and handoff boundaries abstractly, while the low-level translation realizes them using shared endpoint representations and synchronization cells. The simulation results show that this optimized realization implements the direct semantics. We will revise the introduction and related-work section to present these as the main conceptual and technical insights, rather than listing only differences from BGV.

This answer uses the strongest points already recognized by Reviewer C and applies them directly to Reviewer B's concern.

Avoid "without any overhead" unless the paper has a formal cost model or measurements. Prefer:

> without allocation or synchronization machinery beyond sharing the existing endpoint representation

### 2. Formalization

The current response does not identify the requested technical difficulties. It should explain what made the proofs hard and avoid an unqualified "all results" claim.

Suggested replacement:

> At submission time, the missing mechanized results were due to ongoing proof work rather than a known counterexample. The main difficulty was relating source binder groups, whose structural congruence exposes redexes in many equivalent forms, to the explicit channel and synchronization-cell structure of the target calculus. Preservation and progress also require inversion lemmas showing that the head names in dual binder groups correspond to compatible actions after splitting and weakening.
>
> Since submission, we have completed [enumerate the exact checked results]. Backward simulation required a revised process-soup presentation of the target calculus, discussed in our response to Reviewer C. We will state this qualification explicitly and include the complete checked development in the artifact.

### 3. `T-Weaken`

The current answer is incomplete and slightly misleading:

- `T-Weaken` does more than rearrange bindings: the subcontext preorder can weaken independence into sequentiality and add unused unrestricted assumptions.
- Context sequencing uses a comma, not a semicolon.
- The answer does not clearly explain preservation or progress.

Suggested replacement:

> `T-Weaken` is purely static and therefore has no corresponding reduction rule. It changes the context under which an unchanged expression is typed. The preorder permits two operations: adding unused unrestricted assumptions, and replacing available independence by a stronger sequential ordering. For example, an expression typable under `x:T || y:U` may also be typed under `x:T, y:U`, thereby promising to use the two resources in that order even though the expression did not require that order.
>
> This does not rewrite a run-time binder group. In particular, the two binder groups in the reviewer's example cannot be transformed into one another by `T-Weaken`; binder groups change only through the operational rules for communication, splitting, dropping, acquiring, and discarding.
>
> In preservation, inversion may expose a final `T-Weaken`; the proof removes it, applies the induction argument to the underlying syntax-directed derivation, and then re-establishes the larger context using monotonicity of the subcontext relation. In progress, `T-Weaken` adds no term constructor or run-time behavior, so progress follows from the underlying derivation.

Confirm that this description matches the actual mechanized proof before using the final paragraph verbatim.

### 4. BI Contexts

Replace the terse answer and defensive parenthetical with:

> We agree. Our contexts are tree-shaped like BI contexts, but their two connectives distinguish ordered from unordered multiplicative composition rather than additive from multiplicative composition. We will use "tree-shaped context" throughout and mention BI only as a structural analogy, with this distinction stated explicitly.

### 5. Running Examples

"Good suggestion" is not enough. State what will be added:

> We will carry the rendering example into Sections 3 and 4, using it to introduce mobility, direction and effect annotations, ordered versus unordered context composition, and the types of `lsplit` and `rsplit` before presenting the general rules.

### 6. Missing Minor Answers

Add explicit answers for all omitted comments:

> **Listing 1 reference.** Correct: line 290 should refer to lines 6-9, not lines 5-7.
>
> **Flag states.** The synchronization state ranges over `drop` and `acq`; `done` in Figure 3 denotes that `acquire` has consumed and removed the cell. We will redraw the figure and define the flag-name and state domains separately.
>
> **Missing `discard`.** Correct: `discard` is accidentally omitted from the constant syntax in Figure 4 and will be added.
>
> **Context equality.** Yes. "Equivalence closure" includes congruence, so an equality may be applied inside any context. We will state this explicitly rather than relying on the caption.

### 7. Effect Premises in `T-AppUnr`

The current explanation invokes the absence of subtyping, which obscures the simpler answer.

Suggested replacement:

> The two premises use the same `epsilon` because the declarative rules may raise either inferred effect to a common upper bound using `T-Conv` and `p <= i`. Thus the shared annotation denotes the join of the two evaluation effects. The separate condition `epsilon' <= epsilon` ensures that the function body's latent effect is also covered by the conclusion. The algorithmic rule computes these upper bounds explicitly with a least upper bound. We will explain this near Figure 8.

### 8. `F` in `RU-Discard`

Suggested replacement:

> `F` is a process-local evaluation context obtained by lifting an expression evaluation context into a process. It is the same metavariable used in the source reduction rules. We will add its grammar or an explicit cross-reference before Figure 12.

## Reviewer C

### 1. Backward Simulation

The current answer names "too many degrees of freedom" but does not explain the obstacle. It should identify why process congruence obstructed inversion and how the process-soup presentation fixes it.

Suggested replacement:

> The obstacle was inversion through structural congruence in the target calculus. With explicit binary process terms, associativity and commutativity of parallel composition, scope movement, and reordering of independent restrictions allow a target redex to be exposed in many syntactically different ways. A backward proof must locate that redex in the translated source configuration and reconstruct either a matching source step or an administrative step; the submitted presentation did not provide a sufficiently canonical decomposition for this inversion.
>
> We resolved the problem by presenting the target as a soup of processes and restricted resources. The soup representation removes irrelevant binary-tree structure and gives each process and synchronization resource an explicit position, making redex location and reconstruction stable under reordering. We now have a complete mechanized backward-simulation proof for this revised target presentation. The operational primitives and translation idea are unchanged, but the theorem is not literally a proof for the submitted syntax; we will revise Section 6 and state the correspondence precisely.

This is much more credible than saying only that congruence had too many degrees of freedom.

### 2. Heuristic Completeness

A cross-reference to Reviewer A is acceptable under a strict word limit, but include the conclusion directly:

> As explained in our response to Reviewer A, constraint generation now has a mechanized completeness theorem for the annotated judgment, whereas the implementation's candidate-selection heuristic remains sound but incomplete and may reject typable programs.

### 3. Polymorphism

The current answer should explicitly answer the reviewer's either/or question. Borrowing removes the need for continuation polymorphism in the examples, but does not replace general polymorphism.

Suggested replacement:

> The omission is a deliberate scope choice, not a claim that borrowing subsumes polymorphism. Borrowing removes the continuation polymorphism and polymorphic recursion needed by the resource-passing versions of our examples, but ordinary data and protocol polymorphism remain useful. Adding them to CSTB requires studying the interaction between quantified session variables, the unification variables introduced for residual inference, mobility constraints, and CFST equivalence. We therefore leave polymorphism to future work and will revise the paper to avoid suggesting that borrowing eliminates the general need for it.

### 4. Local-Borrow Escape

The current response states the static property but does not fully answer whether classification is ambiguous.

Suggested replacement:

> The distinction is not ambiguous after elaboration. A borrow used entirely within one process elaborates to `lsplit`. If either component is captured by `fork` or sent over a channel, the relevant typing rule requires it to be mobile; a locally borrowed endpoint is not mobile, so an attempted escape is rejected. A borrow that is intended to cross the boundary must instead elaborate to `rsplit`, which adds `Drop` and `Acq` and produces the mobile residual needed for handoff. We will make this static classification and failure mode explicit.

### 5. Subtyping

The current claim that CSTB has the "same expressiveness" as CFST is too broad. It is safer to distinguish the baseline CFST calculus from hypothetical systems with subtyping.

Suggested replacement:

> CSTB is aligned with the original CFST calculus, which also has type equivalence but no subtyping, so borrowing does not remove a feature present in that baseline. Nevertheless, lack of subtyping can reject programs that would be typable in a CFST system equipped with subtyping, particularly programs relying on width or protocol refinements. Since CFST subtyping is undecidable, incorporating it would require an incomplete procedure or explicit coercions. The semi-decision approach of Silva et al. may provide a starting point, but we have not yet studied how it interacts with borrowing and residual inference. We will qualify the expressiveness claim accordingly.

Correct `undecible` to `undecidable`.

### 6. Omitted Acknowledgements

Add responses to Reviewer C's related-work suggestion and typo:

> We thank the reviewer for pointing us to Mordido and Perez's work on deadlock-free CFSTs. We will discuss its relationship to CSTB's deliberately weaker, blocked-process progress result in related work.
>
> We will correct `und` to `and`.

## Response-Wide Style Corrections

Apply the following edits throughout:

- Capitalize headings consistently: "Why Synchronization Cells?", "Purity Constraints", and "The Passage in Lines 376-391."
- Prefer "backward simulation" to "backwards simulation."
- Prefer "binder group" to "bindgroup."
- Replace "pose an unnecessary inefficiency" with "introduces unnecessary allocation and synchronization machinery."
- Replace "with some form of synchronization primitives" with "using an explicit one-shot handoff."
- Replace "The design ... was challenging" with a description of the actual invariant or proof obstacle.
- Avoid contractions such as "haven't" in the formal response.
- Add the missing period after the sentence citing reference [2].
- Use `undecidable`, not `undecible`.
- Use context commas consistently; reserve semicolons for session-type sequencing.
- Remove redundant quotations of reviewer text when a heading already identifies the question.

## Recommended Final Structure

1. Opening acknowledgment and two-sentence contribution framing.
2. Concrete proposed revisions.
3. Reviewer A's three priority questions.
4. Reviewer A's remaining comments, each answered in one concise paragraph.
5. Reviewer B's three required questions with a substantially expanded novelty answer.
6. Reviewer B's remaining comments, including every omitted minor point.
7. Reviewer C's questions, with an explicit distinction between submitted and revised target calculi.
8. References.

The revised response should consistently follow this pattern for every issue:

1. Direct answer.
2. Technical reason.
3. Concrete revision.

Reviewer A's revised section mostly follows this pattern already. Bringing the Reviewer B and C sections to the same standard would materially improve the response's persuasiveness and credibility.
