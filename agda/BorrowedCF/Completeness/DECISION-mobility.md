# Algorithmic completeness: one counterexample and the proposed change

Status 2026-09-08. Agda: `agda/BorrowedCF/Completeness/`. Findings verified by two independent
agents (C4 main proof, C7 red team); the Agda witness for the second finding is
`Completeness/Probe/CaseUnr.agda`.

## 1. The counterexample (mobility of unification-variable types)

Paper notation; `Term` is close, `Acq ; S` is an acquirable session, `!Unit` sends a unit.

    f  =  λ(x : ⟨!Unit ; Acq ; Term⟩).
            let (x₁ , x₂) = lsplit_{!Unit} x in
              close (acquire x₂) ;            -- uses x₂ first
              send (unit , x₁)                -- then x₁

Closed, no free variables.  After the split, x₁ : ⟨!Unit⟩ and x₂ : ⟨Acq ; Term⟩.

Declaratively well typed.  T-LetPair gives the body the ordered structure x₁ ; x₂ (lsplit
returns an ordered pair).  The body itself uses x₂ before x₁, so T-Seq types it under
x₂ ; x₁.  The subcontext relation bridges the two, x₂ ; x₁ ⊑ x₁ ; x₂, through the context
equalities

    Mobile Γ₁ ⇒ Γ₁ ∥ Γ₂ = Γ₁ ; Γ₂        (types.tex, context equality, and Agda ∥′-tm-;)

because x₂ : ⟨Acq ; Term⟩ is mobile (Te-Acq, Term is bounded): x₁ ; x₂ = x₁ ∥ x₂ = x₂ ∥ x₁ = x₂ ; x₁.

Algorithmically rejected.  A-LSplit gives lsplit_{!Unit} the type ⟨!Unit ; α⟩ → ⟨!Unit⟩ ⊗ᴸ ⟨α⟩
with a fresh unification variable α.  Checking x against ⟨!Unit ; α⟩ emits the constraint
⟨!Unit ; Acq ; Term⟩ ≐ ⟨!Unit ; α⟩ (solvable, α ↦ Acq ; Term).  A-LetPair then binds
x₁ : ⟨!Unit⟩ and x₂ : ⟨α⟩ with structure x₁ ; x₂, and A-Seq needs x₂ ; x₁ ⊑ x₁ ; x₂.  That
requires Mobile ⟨α⟩ or Mobile ⟨!Unit⟩.  ⟨!Unit⟩ is not mobile, and ⟨α⟩ is a bare unification
variable, so no mobility rule applies.  The algorithm has no way to record "α must be mobile"
as a constraint: mobility constraints are generated only by A-Abs.  No other algorithmic
derivation exists, because A-LSplit and A-LetPair fix the shapes.

Root cause.  The algorithmic rules check the subcontext relation ⊑ inside contexts whose
types contain unification variables, and ⊑ decides mobility syntactically.  Unr is harmless
(no session type is unrestricted, so Unr is preserved and reflected by substitution);
Mobile is not: Mobile (T[σ]) does not imply Mobile T.

This affects the paper's algorithm and the Agda one alike.

## 1b. Status after the supervisor's objection (2026-09-08, evening)

The instance above uses `⟨!Unit ; Acq ; Term⟩`, which violates the intended formation rule
"nothing before Acq, nothing after Drop" (the paper's formation rules never admit Acq/Drop;
Agda's `⊢` does, and typing never checks annotations: recorded as a discrepancy). The gap
survives well-formed types: `rsplit` itself yields a component `⟨Acq ; α⟩` whose mobility is
`Bounded α`, unknown until `α` is solved. Well-formed, Agda-checked instance
(`Completeness/Probe/MobUvarWF.agda`, every type proved to satisfy the formalised rule):

    λ(q : ⟨!Unit ; Term⟩ ⊗ᴸ ⟨Wait⟩).
      let (x , z)   = q in                     -- ordered pair: x before z
      let (x₁ , x₂) = rsplit_{!Unit} x in      -- x₁ : ⟨!Unit ; Drop⟩,  x₂ : ⟨Acq ; Term⟩  (algorithm: ⟨Acq ; α⟩)
      let (y₁ , y₂) = lsplit_{!Unit} x₁ in     -- y₁ : ⟨!Unit⟩,  y₂ : ⟨Drop⟩
      send (unit , y₁) ; drop y₂ ; wait z ; close (acquire x₂)      -- z before x₂

Declaratively typable (one use of the mobile commutation for x₂). For the PAPER's algorithm
there is no derivation: mobility of ⟨Acq ; α⟩ is unknown and the parallel split would need x
mobile. For the MECHANISED relation as it stood, there was an escape: the rule A-Ann (⇐ to ⇒
without a source annotation) lets the algorithm re-type `rsplit x` at the solved pair type
with a solvable constraint. That escape does not exist in the paper (A-Annot needs `e : T`),
so the mechanised relation was strictly more permissive than the paper's algorithm.

Decision taken (user + supervisor): (i) apply the constraint-generating subcontext judgment
of Section 2 (the emitted constraint for ⟨Acq ; α⟩ is exactly `Bounded α`, validated after
solving); (ii) restrict Agda's A-Ann to checking forms (λ, μ, pair, injection), which are
precisely the positions where the paper's algorithm requires an annotation, so that the
mechanised completeness theorem is the paper's theorem with annotations at those positions.

## 2. Proposed change (minimal, mirrors how A-Abs already treats mobility)

Make the subcontext relation used by the algorithmic rules constraint generating:

    Γ ⊢ Ctx₁ ⊑ Ctx₂ ↑ C            (Agda: Γ ∶ γ₁ ≼ γ₂ ↑ Δ)

with the same rules as ⊑ and context equality, except that the two mobility rules no longer
check Mobile but emit it:

    Γ₁ ∥ Γ₂ = Γ₁ ; Γ₂ ↑ Mob(Γ₁)          Γ₁ ∥ Γ₂ = Γ₁ ; Γ₂ ↑ Mob(Γ₂)
    where Mob(Γ) = { Mobile T | x : T ∈ Γ }

The Unr rule (Γ ∥ Γ = Γ for unrestricted Γ) keeps its side condition; transitivity and
congruences take the union of the constraint sets.  Every algorithmic rule with a premise
Ctx′ ⊑ Ctx (A-Var, A-Const, A-LSplit, A-RSplit, A-App, A-Seq, A-LetPair, A-Case, A-Pair,
and the Agda-only A-Let) reads Ctx′ ⊑ Ctx ↑ C₀ and adds C₀ to its output constraints.

Two lemmas make this the right fix. BOTH ARE NOW PROVED in isolation (agent C8,
`Completeness/Sub.agda`, zero goals, no postulates; no base file touched):

    soundness     σ ⊨ C  and  Ctx₁ ⊑ Ctx₂ ↑ C     ⇒  Ctx₁[σ] ⊑ Ctx₂[σ]
    completeness  Ctx₁ ⊑ Ctx₂ (solved contexts)  ⇒  for every Γ̂ with Γ̂[σ] ≃ Γ there is C
                                                    with Γ̂ ⊢ Ctx₁ ⊑ Ctx₂ ↑ C and σ ⊨ C

The soundness theorem of the paper keeps its statement (its proof replaces one lemma per
rule).  The completeness statement is unchanged:

    Complete⇐ : SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ → Γ ; γ ⊢ e : T | ε →
      ∀ m → ∃ ε′ C k σ. σ ⊨ C × ε′ ≤ ε × Γ ; γ / m ⊢ e ⇐ T | ε′ ↑ C / k
    Complete⇒ : … ∃ T̂ … × T̂[σ] ≃ T × Γ ; γ / m ⊢ e ⇒ T̂ | ε′ ↑ C / k

Also proved: the new judgment is a conservative refinement of the old one (every old ⊑
derivation lifts with constraints that hold, and a lifted derivation whose constraints hold
erases back), and `Completeness/Sub/Probe.agda` discharges verbatim the four proof
obligations the base change creates in the soundness proof.

Cost: one new judgment (a copy of ⊑ with a constraint index), nine premises get a
constraint index prepended to the rule's output (A-Var, A-Const, A-LSplit, A-RSplit, A-App,
A-Seq, A-LetPair, A-Let, A-Pair; A-Case's join premise likewise), A-Abs/A-AbsRec untouched,
mechanical changes in the soundness proof (spec with line references in
`Completeness/Sub-STATUS.md`). Paper side: `\SubCtx` premises in typing-algorithmic.tex
lines 8, 16, 27, 65 and via \CtxAlgJoinCheck/\CtxAlgSeqCheck at 75, 141, 166, 190 become
`Γ ⊑ Γ′ ↑ C`; A-Case's metafunction \CaseJoinDir must return a constraint set as well.  Benefit: the counterexample and every variant of
it are accepted, and constraint solving stays as described in Section 7.2 (mobility
constraints are validated after solving, as today).

## 3. Alternatives considered

(B) Annotate both components of lsplit and rsplit (as the implementation apparently does:
    "the split operators carry type parameters in the actual code").  Then no unification
    variable ever enters a context, the constraint machinery collapses to equivalence
    checks, and completeness is routine.  Simplest, but it removes the remainder-inference
    heuristic that Section 7 presents.
(C) Keep the rules and weaken the theorem to derivations that never use the mobility of a
    variable bound at an inferred type.  Not a clean statement; we do not recommend it.

## 4. Other changes already made to the mechanised system (need the same edit in the paper)

- A-Case: the branches were typed under Ctx|_{fv(e)^C}, the complement of the scrutinee's
  variables, so an unrestricted variable used by both scrutinee and branch was lost
  (counterexample: case u of {inl _ → u ; inr _ → u} with u : Unit ⊕ Unit).  Now the
  branches are typed under Ctx restricted to the branches' own free variables, like every
  other rule.  Soundness re-proved.
- A-LetPair (and the paper's rule, typing-algorithmic.tex line ~190, `(x:T₁ ⋈ y:T₂) ; Ctx|e₂`)
  hard-wires a sequential link between the pair components and the rest of the context,
  while T-LetPair admits the parallel one. Counterexample (Probe/LetPairPar.agda): under
  z : ⟨Wait⟩ and a pair p : ⟨Term⟩ ⊗ Unit, the body `let (c, _) = p in (z , c)` uses z before
  the component c. Declaratively typable with p/s = par, algorithmically not. Repair: give
  A-LetPair (and A-Let) the same p/s choice as the declarative rule. Applied in Agda.
- Completeness needs the hypothesis that the structure is linear (each non-unrestricted
  variable occurs at most once).  Under x ∥ x with a linear x the declarative system types
  f x · g x while the algorithmic variable rule cannot derive x ⊑ x ∥ x.  Paper contexts are
  linear by construction; the Agda structures are not, hence the explicit hypothesis.
- Agda only: A-Let added (the paper has no let), select/branch admitted in A-Const (the
  paper's A-Select/A-Branch had not been transcribed), the postulate parOrSeq? replaced by
  a proof, the missing let constructor added to SolvedTm.
