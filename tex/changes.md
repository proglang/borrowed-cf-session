# Changes by MW (2026-10-06/07)

Line numbers are the review-mode margin numbers of the current builds of
popl2027.pdf and popl2027-supplement.pdf.

## popl2027.pdf

| p. | lines | change |
|---|---|---|
| 2 | 86–95 | Contributions: algorithmic typing is now "proved sound and complete"; the obligations bullet is replaced by proved type soundness and forward and backward simulation; mechanization claim added. |
| 19 | 920–929 | §7.1 prose: type-normalisation intro dropped; A-Const covers every constant except the splits (select and branch included); A-Annot checks against the annotation; two sentences on normalised types dropped. |
| 20 | Fig. 14 | A-Select and A-Branch removed (typed via A-Const); every NormaliseType premise removed (A-Var, A-App, A-Annot, A-Abs, A-AbsRec, A-Pair, A-Inj); A-Const side condition is now c ∉ {lsplit, rsplit}; A-Inj checks the k-th summand. The figure now matches the Agda rules. |
| 22 | 1031–1037 | §8 intro: every theorem of the section is proved in Agda; the supplement names the Agda module per theorem. |
| 22 | 1039 | Process preservation: Agda bird added. |
| 22 | 1044–1053 | Process progress: stated for closed processes (empty context); Blocked is the predicate of Fig. S-12; Agda bird added. |
| 22 | 1055–1072 | §8.2 rewritten for the process-soup target: image relation ▷ introduced (macro \ImageRel), theorems use the letters P, Q, R; forward simulation is lock-step; backward simulation is now a theorem (was a conjecture), up to the slot-renumbering equivalence ≈. The symbol ≈ is re-purposed; weak bisimilarity is gone. |
| 22 | 1073–1079 | Soundness: σ is applied to Γ and e as well as the type; the effect is kept. |
| 23 | 1081–1100 | Completeness theorems added (checking and inference), matching the Agda complete⇐ and complete⇒: hypotheses (no unification variables, linear variables occur at most once) stated once in the preceding paragraph; both theorems produce an annotated variant of e (type annotations inserted at checking forms in inference position — the annotation is now syntactic in the mechanisation too); effect bound ε′ ≤ ε; inference result type up to ≃. |

## popl2027-supplement.pdf

| p. | lines | change |
|---|---|---|
| 9 | 398–417 | Blocked-processes figure: B-NuBlockedAcq replaced by B-NuBlockedAcqLeft/Right/Both, the precise rules mechanised as Blocked⁺ (process progress is proved for both). In tex/rules/blocked.tex the imprecise rule is kept as a comment. |
| 10 | 444 | Paper proof of process progress commented out; the mechanised proof supersedes it. |
| 5 | §S-D | Type-normalisation figure commented out; no algorithmic rule normalises any more. |

## Source-only

- tex/symbols.tex: new macro \ImageRel (▷).
- tex/rules/typing-algorithmic.tex and tex/rules/blocked.tex carry the rule edits above.
- introduction and appendix edits were made in the literate sources sec/introduction.lhs.tex and sec/appendix.lhs.tex; the .tex files are generated.
