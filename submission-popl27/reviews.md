POPL 2027 Paper #1159 Reviews and Comments
===========================================================================
Paper #1159 Context-Free Session Types with Borrowing


Review #1159A
===========================================================================

Overall merit
-------------
B. OK paper, but I will not champion it

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper defines a system of borrowing for session types.  It builds on prior work
in the area, but extends the idea by supporting context-free session types, which are
more expressive, by avoiding the need to use resource-passing style in some cases,
and by supporting a lightweight and optimized local form of borrowing in addition to
cross-process borrowing.  The paper illustrates the idea by example; defines a
source-level language, its type system, and its dynamics; gives a translation to an
untyped core; defines algorithmic typing; and proves that it all fits together.  An
implementaiton in Rust is claimed.

Strengths
---------
+ borrowing adds substantial convenience to session types
+ this paper supports a simpler and more powerful form of borrowing than the prior work
+ the paper describes several layers of theory and semantics, all of which seems basically correct (though I have one question and also did not check the proofs in the appendix)

Weaknesses
----------
- some problematic writing (see below), probably fixable though
- design decision to use synchronization variables seems questionable

Comments for authors
--------------------
Overall, I'm reasonably positive on the paper, between and A and a B.  With some improvements to the writing I would advocate for it.  As an extension of prior work it is a "brick in the wall" kind of paper not a "new wall" paper, but it's a very solid brick and we need those.

I think the choice to "implement" drop/acquire with synchronization variables is very questionable, probably just a bad decision.  First of all the writing in section 2.4 (specifically lines 376-391) is totally inscrutable, due in part to what I think is unnecessary complexity.  Second of all you are working with session types, so you have channels, therefore why not use channels for synchronization?  What you need is exactly a channel where the drop process sends and the acquire process receives.  Ok, the channel is asynchronous, but a single cell buffer suffices to handle that.  Third, this paper is focused on theory, but session types are motivated mainly by distributed systems, and in a distributed system all you have is messages--not synchronization variables.  So as soon as anyone tries to put this in common session type settings they will have to do it differently.

I realize the reviewer of paper should not design it for the authors, so I am not going to reject the paper for this reason or demand it all be redone.  But I think the paper should explain why this modeling choice was made, and I suggest the authors think long and hard about whether this choice actually makes sense.


DETAILED COMMENTS

page 4: Why is polymorphic recursion a "problem"?  It seems like a reasonable language feature & works fine e.g. in Java, so please explain the issue.  Are you implicitly assuming a setting like ML and/or Hindley-Milner?

Fig 2b: should the reader be worried that wait/close is not specific to a channel?  what if we are waiting for one channel and another channel is closed, could that mess things up if the semantics allows them to match?  [UPDATE on reading the semantics - it would be helpful to state around here in the paper that v[c4][d3] (with c4 and d4 alone in the brackets) indicates that c4 and d3 are different ends of the same channel, not two arbitrary channel endpoints, which addresses my question. This was not obvious to me because in the paper there can be whole strings of variables and || inside the square brakets.]

Same question in Fig 2c, but for matching the drop and the acquire.  When I read this example I thought [ drop c1 ] was part of the state after ~>* but now after reading the rest of the paper I think it is an annotation about what happened in the ~>*.  This is extremely confusing and you must change that line to indicate this in some other way.  I personally think the best way would be to show one more step where the drop is executed.

As mentioned above, the passage from 376-391 is inscrutable.  What does "optional" mean? You explain \varphi but not \phi, I think \phi is the binder?  BTW by using both \varphi and \phi in the same form becomes impossible to read the form out loud, this is really variable choice malpractice.  "loopy phi z arrow straight phi P" ugh.  I am not toally sure how to fix it, but maybe just take it out and discuss it at a higher level of abstraction?  The explanations that come later are much easier to follow, including both 425-433 and section 6.

458: und -> and

also "juxtaposition with unit e" would be more readable with a comma after juxtaposition (I read it as "juxtaposition with unit e" as in putting e right after something to show concatenation).

"without consuming an unbounded residual owned elsewhere" why do we care?  servers exist, they are supposed to run forever.  Lots of channels are unbounded, they send streams of things.  Maybe just a few more words on this.

Fig 6 rule Te-Seq2 - why don't you require S1 to be bounded?  It seems if S1 is not bounded then the whole thing is not bounded?

fig 7 rule CT-LSplit why can't S2 be Skip?

paragraph 654-633 a lot of discussion about requiring things to be pure.  why?  For example it is routine in effect systems to account for effects in evaluating an expression to a function separately from the effects of a function body, and we don't expect that to be pure.

7.2 should we be worried that the heuristic is (I think) incomplete?  Do you have any experience with this?

Specific questions to be addressed in the author response
---------------------------------------------------------
Please answer the questions above.  Especially important:
 * why synchronization variables?
 * explain the purity constraints discussed in 654-633
 * 7.2 heuristic incompleteness



Review #1159B
===========================================================================

Overall merit
-------------
B. OK paper, but I will not champion it

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
The paper introduces CSTB, a context-free session types calculus with borrowing. It supports two forms of borrowing: local borrowing, which stays within the process and is a form of sequencing by order typing, and remote borrowing, where the borrowed prefix can cross process boundaries and requires a synchronous acquire/done. The paper provides a declarative (and algorithmic) type system, based on the idea that the channels in the context form a tree rather than a sequent with two different separators, an operational semantics, and a translation to a low-level session calculus. The paper presents metatheoretical results, partially mechanized in Lean, including preservation and a limited form of progress.

Strengths
---------
* The theory appears sound and well-developed.
* Context-free session types appear to be a natural fit for modeling borrowing, as demonstrated by the paper.

Weaknesses
----------
* The theoretical significance relative to prior work is not clear.
* The Agda formalization is incomplete.

Comments for authors
--------------------
1) The results in the paper are closely related to BGV, a calculus derived from GV that supports borrowing. I think the results in this paper when compared to GV, indeed show that context-free session types are a better match for borrowing. On the other hand, I  worry that the theoretical and technical contributions are not significant enough compared to BGV for a POPL paper. As stated in the paper, the main technical differences compared to BGV are fourfold: (a) instead of defining the semantics of borrowing by translation,  CSTB has a direct operational semantics; (b) CSTB distinguishes remote borrows from local borrows; (c)  CSTB requires constraint generation modulo type equivalence; (d) the paper defines a low-level target calculus. Do any of these provide any new insights? Interesting theoretical challenges? 

2) Only some of the main theorems are formalized in Agda, and the formalization does not include progress and preservation for the processes. I found this somewhat concerning. Could the authors provide more insight into why the remaining theorems have not been formalized? In particular, are there any technical challenges or limitations that make these results difficult to formalize?

3) I would like to better understand how the T-Weaken rule manifests in the dynamics and how it is reflected in the progress and preservation theorems. In particular, consider a program of the form \nu x[c][d]\ldots, where c = ((x \parallel y)(z \parallel d)). Can the program be rewritten as \nu x[c'][d]\ldots where c' = (xz \parallel yd), or vice versa? If so, which rule allows this rewriting? If not, what role does the T-Weaken rule play in the dynamics, and how does it contribute to the progress and preservation theorems?

4) I don't think the repeated reference to the context as one similar to BI is accurate. In particular, in BI the separators distinguish additive from multiplicative conjunction, whereas here the two separators distinguish ordered from unordered (I believe both multiplicative) conjunction. These are two different distinctions, with different algebraic properties, and conflating them risks confusing the reader. I'd suggest instead referring to it as a tree-shaped context versus a linear context, and noting that BI also has such a tree-shaped context, but structured around a different distinction.

5) I think the presentation, particularly in Sections 3 and 4, would benefit from running examples. Many notations are difficult to understand without familiarity with the prior work, and some only become clear much later in the paper (e.g., the superscripts on function type).


------------
Minor:

- Line 290. lines 5-7 → 6-9 in Listing 1?

- Section 2.4 states \phi:drop or acq but in Figure 3(b), we also have z \mapsto done. Also, what is the domain of \varphi? Is it just a label?

- Is discard missing from the syntax of Figure 4?

- Can the equality rules of Figure 6 be applied anywhere in the context? i.e., is \Gamma[\Gamma_1]=\Gamma[\Gamma_2], if \Gamma_1=\Gamma_2?

- Figure 8, e.g., rule T-AppUnr. Are the two premises required to have the same \epsilon? Why?

-Figure 12, RU-discard: what is F?

Specific questions to be addressed in the author response
---------------------------------------------------------
Please address comments 1-3 above.



Review #1159C
===========================================================================

Overall merit
-------------
B. OK paper, but I will not champion it

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
The paper extends prior work on borrowing for session types (BST) (Saffrich et al. 2025) to context-free session types (CFSTs), proposing a new calculus CSTB. In CFSTs, sequential composition is a symmetric operator and not restricted to tail recursion, so a borrowed prefix of a protocol can only be identified modulo an equational theory. This makes splitting a CFST into borrowed prefix and residual suffix nontrivial, unlike in regular session types (ST) where the prefix is syntactically evident. This a central technical problem dealt with in this paper. The key conceptual move is to distinguish local borrows, which basically stay in one process, from remote borrows which cross a process boundary via fork.

Strengths
---------
- The paper identifies a genuinely open problem. Prior borrowing work (BST, Saffrich et al. 2025) only handles regular (tail recursive) session types. On the other hand, context-free session types need borrowing more, since their resource passing and polymorphic recursion burden is worse. The tree serialization and streaming HTML examples in Section 2 are effective,  they make the point, and they motivate borrowing before any formalism appears.

- Local vs remote borrow distinction is the paper key idea. Recognizing that local borrows can be sequenced for free via evaluation order plus ordered typing, whereas only remote (cross-process) borrows need synchronization machinery, is a genuine efficiency insight. This is reflected consistently across all three layers (declarative types, direct operational semantics, and the low-level translation), which gives the paper structural coherence.

- The paper has a very clear technical development. Going from 
(1) a declarative type system with ordered and unordered contexts, in the style of Bunched Implication, to 
(2) a direct operational semantics, rather than defining the source language purely by translation as is BST, to 
(3) an algorithmic bidirectional type system with constraint solving, to 
(4) a low-level runtime calculus with an explicit simulation theorem.

- Mechanization in Agda of the fundamental properties of type safety (preservation, progress) and algorithmic soundness, strengthens confidence in the results.

Weaknesses
----------
The weakness are related to the specific questions, as follows.

Comments for authors
--------------------
Recent work on deadlock free CFSTs could be of interest
Andreia Mordido, Jorge A. Pérez. Deadlock-Free Context-Free Session Types, FORTE 2026.

Typo
- line 458 "und" --> "and"

Specific questions to be addressed in the author response
---------------------------------------------------------
- Backward simulation: Theorem 8.6 (backward simulation) is stated as a conjecture. What is the specific obstacle to completing this proof?

- Section 7.2 heuristic is described as sound but the completeness argument is informal. Is there a formal completeness theorem, or is completeness open? 

- CSTB drops the polymorphism present in FreeST and CFST. Borrowing removes the need for polymorphism in the examples shown. Can this omission be principled in the sense that borrowing genuinely removes the need for polymorphism in CSTB? Or, is it a deliberate choice in the design of CSTB?

- The distinction between local and remote borrows is determined by whether a borrow crosses a fork. Is this distinction ever ambiguous in practice — e.g., could a local borrow accidentally leak into a forked process? If so, is that caught statically? 

- Subtyping in CFST as undecidable, as shown by Padovani 2019. Subtyping in this new setting CSTB is not present.  How does the lack of subtyping in the new CSTB affect expressiveness?
