# Algorithmic completeness dashboard

Generated from `dashboard/state.json` (2026-09-08 final: complete⇒/complete⇐ verified from empty cache, pushed as 3f3c4b3). Open `dashboard/dashboard.html` for the live view (`dashboard/serve.sh`).

## Theorems

| name | module | status | note |
|---|---|---|---|
| complete⇐ : Complete⇐ | Completeness.agda / Completeness/Main.agda | DONE (verified): complete⇐ : Complete⇐ in Completeness.agda, zero goals, no postulates, no assumptions | SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ → Γ ; γ ⊢ e ∶ T ∣ ϵ → ∀ m → ∃ ϵ′ Δ k σ. Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / k |
| complete⇒ : Complete⇒ | Completeness.agda | DONE (verified): complete⇒ : Complete⇒ in Completeness.agda | same with an inferred T̂ and subTy T̂ σ ≃ T |

## Lemmas

| name | module | status | agent |
|---|---|---|---|
| LinStruct lemmas (lin-≼, lin-↓, lin-join⁻, lin-bind) | Completeness/Split.agda | done | C1 |
| ↓-mono-⊆, unr-absorb | Completeness/Split.agda | done | C1 |
| canon-split (canonical restriction split of an admissible split) | Completeness/Split.agda | done | C1 |
| canon-core (construction half of the canonical split, from Sep predicates) | Completeness/Split/Construct.agda | done | C9 |
| UVarsIn, scope (uvars of outputs lie in [m,n)) | Completeness/Scope.agda | done | C2 |
| merge / single substitutions, solvedΔ-merge, subTy-agree | Completeness/Scope.agda | done | C2 |
| alg-weaken (algorithmic typing closed under ≼ on linear structures) | Completeness/Weaken.agda | done | C3 |
| fv⊆dom, fv-cover, restrict, restrict-≼ | Completeness/Decl.agda | done | C5 |
| effect / Seq⇒Pure / EffCompat bridges, Solved inversions | Completeness/Decl.agda | done | C5 |
| main induction (parametrised) + instantiation | Completeness/Main.agda, Completeness.agda | done | C4 |
| red-team probes (counterexample search) | Completeness/Probe/ | done | C7 |
| ≼↑ (constraint-generating subcontext): ≼↑-sound, ≼↑-complete, ≼⇒≼↑/≼↑-erase, base-change probe | Completeness/Sub.agda, Sub/Probe.agda | done | C8 |

## Agents

| id | model | task | files | state |
|---|---|---|---|---|
| C1 | opus | structure algebra: LinStruct, restriction monotonicity, unrestricted absorption, canonical split lemma | Completeness/Split.agda, Split/ | finished (canon-split proved, toolkit verified) |
| C2 | opus | unification-variable scope invariant, substitution merge/single/agreement | Completeness/Scope.agda, Scope/ | finished (re-verified after the ≼↑ base change) |
| C3 | opus | algorithmic weakening (parametrised over C1) | Completeness/Weaken.agda, Weaken/ | finished (alg-weaken restated over Γ̂ with Approx, verified) |
| C4 | opus | main completeness induction (parametrised over C1/C2/C3/C5), instantiation | Completeness/Main.agda, Completeness.agda, Main/ | finished (complete⇒/complete⇐ proved, no assumptions; verified) |
| C5 | opus | declarative facts: fv⊆dom, fv-cover, restrict, effects, inversions | Completeness/Decl.agda, Decl/ | finished |
| C6 | opus | base edit (user-approved): select/branch via A-Const, new A-Let + soundness case in Algorithmic.agda; parOrSeq? postulate replaced by proof | Algorithmic.agda, Context/Join.agda (base), BaseRules-STATUS.md | finished (A-Let + soundness, select/branch in A-Const, parOrSeq? proved; Safety theorems re-checked OK) |
| C7 | opus | red team: search for counterexamples to Complete⇐/⇒, canon-split, alg-weaken, and confirm the LinStruct necessity, on concrete Agda-checked examples | Completeness/Probe/, Probe-STATUS.md | finished (WF mobility instance mechanised; A-Ann escape found; probes now regression tests) |
| C8 | opus | design+validate in isolation the principled fix for Finding 1: constraint-generating subcontext relation ≼↑Δ with soundness and the transfer lemma; write the base-change spec | Completeness/Sub.agda, Sub/ | finished (≼↑ with soundness, transfer, round trip; base-change spec validated by probe) |
| C9 | opus | helper of C1: canon-core (construction half of the canonical split lemma) against C1's Sep predicates | Completeness/Split/Construct.agda | finished (canon-core proved, verified) |
| C6b | opus | base repair (Finding 2): A-Case restricts branches to their own free variables; soundness case adapted; then add the missing let constructor to SolvedTm (+ subTm-solved/subTm-id cases) | Algorithmic.agda (base) | finished (A-Case per-branch restriction + SolvedTm let, verified) |
| C6c | opus | base repair (Finding 3): p/s choice in A-LetPair and A-Let mirroring T-LetPair/T-Let; soundness adapted | Algorithmic.agda (base) | finished (p/s in A-LetPair/A-Let, soundness adapted, verified) |
| C10 | opus | base change (user-approved): constraint-generating subcontext premises in the nine A-rules, definitions moved to Context/SubConstraint.agda, soundness adapted; plus A-Ann restricted to checking forms (ChkForm) | Algorithmic.agda, Context/SubConstraint.agda (base), Completeness/Sub*.agda | finished (≼↑ premises in nine rules, A-Ann restricted, SubConstraint.agda, soundness adapted; verified) |
| C11 | opus | base edit: SolvedC gains `discard/`select/`branch (+ subConst cases) so the theorem's SolvedTm hypothesis covers those constants | Algorithmic/Solved.agda (base) | finished |

## Issues found

- Completeness needs a linearity hypothesis on the structure (LinStruct): under γ = x ∥ x with linear x the declarative T-AppUnr types f x · g x but A-Var cannot derive ` x ≼ x ∥ x. Stated in Base.agda.
- Agda A-Ann switches from checking to inference without an annotation (the paper's A-Annot needs e : T), so the mechanised 'algorithmic' relation guesses types at that rule.
- GAP (being closed, user approved): select/branch had no algorithmic rule and let had no A-Let; C6 adds them to Algorithmic.agda with the soundness case. A full check of the whole development follows.
- FINDING 2 (C4 + C7 independently): A-Case drops every scrutinee variable from the branch structure (∁ (fv e)), so an unrestricted variable shared by scrutinee and branch is untypable algorithmically (witness Probe/CaseUnr.agda). Repair: per-branch restriction like every other rule; C6 implements it in the base (reversible).
- parOrSeq? in Context/Join.agda was a postulate; it is now a one-line proof (join seq is definitionally ;). No postulates remain outside Simulation/Support/Base.funext.
- C2: the scope invariant needs a GuessIn side condition (A-Const's instance type and A-Ann's guessed type are not determined by premises), and SolvedTm cannot be a hypothesis of scope because it has no constructor for let.
- C3: canon-split's Unr side conditions are not derivable for raw X = fv e; call it with X ∩ dom γ₂ (↓-∩). LinStruct as a Π-type blocks unification (Γ under lookup, γ under count): thread a record LinBox instead. Only A-Abs's mobility constraints move under weakening, direction γ₁ ⇒ γ₂.
- Decision memo for the team: Completeness/DECISION-mobility.md (counterexample, proposed constraint-generating subcontext judgment, alternatives, other paper-relevant changes).
- C1: the canonical split lemma is TRUE as stated; the ;-node case needs a mobility witness, obtained by strengthening before-mono-≼ to return `before u v α ⊎ (Mobile u ⊎ Mobile v)`. Signature deviation: X, Y explicit; LinStruct arguments explicit (Π-type blocks inference).
- C5: `_≤ϵ_` has no fixity in Types/Syntax.agda (defaults tighter than `_⊔ϵ_`), so `ϵ₁ ⊔ϵ ϵ₂ ≤ϵ ϵ` misparses; parenthesise or add `infix 4 _≤ϵ_`. `restrict` for T-Abs needs fv-cover because an unused bound variable must be unrestricted.
- Full-development check: the 13 modules of the OLD Simulation/Backward tree (untyped-target development, on hold since July, still has holes) fail at HEAD already: ReverseInv.agda imports chanCx-⸴* from Reduction.Base, which never defined it (the lemma is private to ForwardSoup/Local.agda). Unrelated to today's edits (ReverseInv imports neither Join nor Algorithmic). Everything else green so far.
- FINDING 3 (C7, genuine, Agda and paper): A-LetPair hard-wires `;` between the pair components and the rest of the context; T-LetPair allows par. Witness Probe/LetPairPar.agda (¬ Complete⇐ against the current base). Repair: p/s in A-LetPair and A-Let (C6c). C7 could not break the canonical split lemma, restriction monotonicity, or C8's ≼↑ fix.
- FINDING 1 resolved by decision (user + supervisor, 2026-09-08): the subcontext premises of the algorithmic rules become constraint-generating (Mobile ⟨Acq ; α⟩ = Bounded α emitted as a constraint, validated after solving). The first memo instance was malformed (Acq in the middle; the paper's formation rules never admit Acq/Drop); the well-formed rsplit instance (Probe/MobUvarWF.agda, C7) is the deciding witness. Agda's ⊢ allows acq/ret anywhere and typing never checks annotations: recorded as a discrepancy, not changed (would ripple through T-Abs into every preservation/simulation proof).
- C7: Agda's A-Ann (⇐→⇒ with no annotation) lets the mechanised relation re-type any subterm at a solved type, an escape the paper's A-Annot does not have; the mechanised relation was strictly more permissive than the paper's algorithm. Fix (in C10's base change): A-Ann only on checking forms ƛ/μ/⊗/inj, the positions where the paper needs an annotation.
- C4 design notes: induction on the TERM (T-Conv/T-Weaken absorbed by inversion), inference proved and checking derived via A-Check, algorithmic context only APPROXIMATES the declarative one (subTy (Γ̂ ﹫ x) σ₀ ≃ Γ ﹫ x), substitution threaded not merged (C2's merge and C3's alg-weaken ended up unused by the final proof), scope facts are outputs of the induction. SolvedC lacked `discard/`select/`branch (C11 fixes).
