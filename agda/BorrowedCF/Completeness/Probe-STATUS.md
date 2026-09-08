# C7 (red team) — probe status

# DECIDING ITEM (2026-09-08): the well-formed mobility instance

**File `Probe/MobUvarWF.agda`, type-checks, zero goals, zero metas.**

**Verdict in one line: the instance is well formed and declaratively typable, and
`⟨ acq ; `` α ⟩` is indeed not Mobile — but it is NOT a counterexample to the Agda
`Complete⇐`, because A-Ann/A-Check let the algorithm trade the inferred type
`⟨ !Unit ; ret ⟩ ⊗¹ ⟨ acq ; `` α ⟩` for the SOLVED `⟨ !Unit ; ret ⟩ ⊗¹ ⟨ acq ; end ‼ ⟩`
at the cost of one solvable `C-Eq`. The same escape kills the original
DECISION-mobility instance. The mobility gap is real for the PAPER's algorithm
(whose A-Annot needs a source annotation) and is not expressible against the
mechanised one.**

### (1) Well-formedness, formalised

`Probe/MobUvarWF.agda` §1 defines, by mutual induction,

    Core s   -- s mentions neither acq nor ret, anywhere (msg payloads and brn
             -- branches included); constructors `_ end msg brn mu _;_ skip ``_
    CoreTy T -- lifted to 𝕋 through ⟨_⟩, `⊤, ⟨a⟩→, ⊗⟨d⟩, ⊕
    WF s     -- core (Core s) | ret | acq-head (Core s) | ret-tail (Core s)
             --               | acq-ret (Core s)
    WFTy T   -- lifted to 𝕋

i.e. exactly "acq only as the first atom of the top-level `;`-spine, ret only as the
last, never inside a payload". Proved there:

| type | role | WF proof |
|---|---|---|
| `⟨ msg ‼ `⊤ ; end ‼ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩` | the λ annotation | `wf-Tq  = ⟨ core (msg `⊤ ; end) ⟩ ⊗⟨ L ⟩ ⟨ core end ⟩` |
| `⟨ msg ‼ `⊤ ; ret ⟩` | rsplit, 1st component | `wf-Tx₁ = ⟨ ret-tail (msg `⊤) ⟩` |
| `⟨ acq ; end ‼ ⟩` | rsplit, 2nd component | `wf-Tx₂ = ⟨ acq-head end ⟩` |
| `⟨ msg ‼ `⊤ ⟩` | lsplit, 1st component | `wf-Ty₁ = ⟨ core (msg `⊤) ⟩` |
| `⟨ ret ⟩` | lsplit, 2nd component | `wf-Ty₂ = ⟨ ret ⟩` |
| `⟨ acq ; `` α ⟩` | what A-RSplit gives x₂ | `wf-Tx₂-alg = ⟨ acq-head (`` α) ⟩` |

Every type in the instance is WF; no type has anything before `acq` or after `ret`.
(For comparison: the type of the OLD instance, `⟨ msg ‼ `⊤ ; (acq ; end ‼) ⟩`, is
NOT WF — `acq` is not the first atom — although the Agda predicate `⊢_`
(Types/Syntax.agda:296) accepts it, since `⊢_` is purely structural and has
`acq : ⊢ acq`. The paper's session-type-formation.tex has no rule for Acq/Drop at
all, so neither source enforces the supervisor's condition today.)

### (2) Declarative derivation — Agda-checked

    a₀ = ⟨lin 𝟙, dir 𝟙, mob S, eff 𝕀⟩
    fWF = ƛ (let⊗ q in let⊗ (rsplit_{!Unit} x) in let⊗ (lsplit_{!Unit} x₁) in
              ((send (unit ⊗ y₁) ; drop y₂) ; (end⁇ z ; end‼ (acq x₂))))
    decl : [] ; [] ⊢ fWF ∶ (⟨ msg ‼ `⊤ ; end ‼ ⟩ ⊗ᴸ ⟨ end ⁇ ⟩) ⟨ a₀ ⟩→ `⊤ ∣ ℙ

The three `let⊗` all use `p/s = seq`. The body's own structure is
`(y₁ ; y₂) ; (z ; x₂)`; T-LetPair prescribes `(y₁ ; y₂) ; (x₂ ; z)`; the single
bridging step is `;-commMob (inj₂ (` mobile-x₂))`, i.e. one use of `∥′-tm-;` on
x₂ : `⟨ acq ; end ‼ ⟩`. Nothing else in the derivation touches mobility.
`p/s = par` for the outer `let⊗` is not needed (and would need `Mobile ⟨ sQ ⟩`,
which is false) — the instance is genuinely about `;-commMob`, not about `par`.

### (3) The mobility facts — Agda-checked

* `mobile-x₂ : Mobile ⟨ acq ; end ‼ ⟩` = `⟨ end ‼ , end , ≃-refl ⟩` (Te-Acq, `Bounded end`).
* `mobile⇒bounded : Mobile ⟨ s ⟩ → Bounded s` — new; `≃-bounded` (Types/Predicates.agda)
  transports `Bounded (acq ; s′) = -;₂ B` back along `s ≃ acq ; s′`.
* `¬mobile-acq-uvar : ¬ Mobile ⟨ acq ; `` α ⟩` — new, from the above plus
  `¬ Bounded (acq ; `` α)` (neither `;₁` nor `-;₂` applies). So the type A-RSplit
  hands x₂ really is not mobile, as DECISION-mobility.md says.

### (4) Why the algorithmic refutation does NOT go through

    αᵣ = UV.fresh 0
    Uᵣ = ⟨ msg ‼ `⊤ ; ret ⟩ ⊗¹ ⟨ acq ; `` αᵣ ⟩          -- what A-App infers
    Δᵣ = C-Eq (Tx₁ ⊗¹ Tx₂) Uᵣ ∷ C-Eq ⟨ msg ‼ `⊤ ; `` αᵣ ⟩ ⟨ msg ‼ `⊤ ; end ‼ ⟩ ∷ []

    alg-rsplit : Cx3 ; (` 0F) / 0 ⊢ rsplit_{!Unit} x ⇒ (Tx₁ ⊗¹ Tx₂) ∣ ℙ ↑ Δᵣ / 1
    alg-rsplit = A-Ann (A-Check (A-App _ … (A-RSplit …) (A-Check (A-Var …))))
    solvedΔᵣ : SolvedΔ Δᵣ UV.someSub          -- σ = (α ↦ end ‼); Solving σ is someSub-solving

Both constraints hold by `≃-refl` after `subTy … UV.someSub`. A-LetPair therefore
binds x₂ at the SOLVED, MOBILE `⟨ acq ; end ‼ ⟩`, and the mobility obstruction is gone.

The escape is general, not ad hoc — also in the file:

    retype : Γ ; γ / m ⊢ e ⇒ U ∣ ϵ ↑ Δ / k → Γ ; γ / m ⊢ e ⇒ G ∣ ϵ ↑ C-Eq G U ∷ Δ / k
    retype d = A-Ann (A-Check d)
    retype-solved : subTy G σ ≃ subTy U σ → SolvedΔ Δ σ → SolvedΔ (C-Eq G U ∷ Δ) σ

**No binder of the mechanised algorithm is ever stuck at an unsolved type**: every
inferred type can be traded for any σ-equivalent one, in particular for a solved one.
Any counterexample whose obstruction is "the algorithm only knows a unification
variable here" therefore fails against the Agda system. (Consequence for the memo:
DECISION-mobility.md §1's sentence "No other algorithmic derivation exists, because
A-LSplit and A-LetPair fix the shapes" is false for the Agda rules as they stand.)

**What I did NOT mechanise:** the full algorithmic derivation of `fWF`. I certified the
step the memo's argument rests on. Strictly, "not a counterexample" would need that
full derivation; what is proved is that the stated obstruction is removable.

### (5) Recommendation

Two coherent options, and they must be taken together:

1. Keep C8's constraint-generating `≼ ↑ Δ` **for the paper**, where A-Annot needs a
   source annotation and the instance above genuinely has no derivation. Then also
   fix the Agda A-Ann (add an annotation to `Tm`, or drop A-Ann) — otherwise the Agda
   `Complete⇐` is proved about a *different, more permissive* algorithm than the one
   in the paper, and the mechanisation does not support the paper's claim.
2. Or annotate both components of lsplit/rsplit (DECISION-mobility.md alternative B),
   which removes unification variables from contexts entirely and makes the question
   moot in both systems.

Adopting C8's fix in Agda alone changes nothing that is provable there.

---

## Files

| file | what it is | status |
|---|---|---|
| `Probe/MobUvarWF.agda` | WF predicate, the well-formed mobility instance, `¬mobile-acq-uvar`, the A-Ann escape | **deciding item, above** |
| `Probe/MobUvar.agda` | the original DECISION-mobility instance, declarative side + `¬mobile-uvar` | witness (its type is NOT WF) |
| `Probe/CaseUnr.agda` | was COUNTEREXAMPLE 1 (A-Case `∁ (fv e)`), now a POSITIVE regression test | fixed in base |
| `Probe/LetPairPar.agda` | was COUNTEREXAMPLE 2 (A-LetPair's `;`-body), now a POSITIVE regression test | fixed by C6c |
| `Probe/LinNeeded.agda` | `LinStruct` is necessary; the invariant is `count-≼-eq`, not `≼⇒count≤` | confirmed |
| `Probe/UnrReflect.agda` | `subTy-unr⁻¹` / `unrCx-reflect`: `Unr` is REFLECTED by σ (C8 needs this) | support |

## FIXED — was COUNTEREXAMPLE 2 (A-LetPair hard-wired a sequential body)

`let⊗ p in (z ⊗ c₀)` with `p : ⟨ end ‼ ⟩ ⊗¹ `⊤`, `z : ⟨ end ⁇ ⟩`, `γ = ` p ∥ ` z`:
declaratively typable with T-LetPair `p/s = par`, algorithmically impossible while
A-LetPair fixed the body structure to `join d (` 0F) (` 1F) ; wk (wk γ₂)` — every
component was `before` every outer variable and `before-mono-≼` forbade the body's
`before z c₀`. C6c has landed the `p/s` repair for A-LetPair and A-Let;
`Probe/LetPairPar.agda` now carries the algorithmic derivation (`alg`, `p/s = par`,
`Δ₀` = three reflexive `C-Eq`s, `solvedΔ₀`) next to the declarative one and fails to
compile if the body join regresses to `;`.

## FIXED — was COUNTEREXAMPLE 1 (A-Case restricted the branches by `∁ (fv e)`)

`case (inj_L u) of { _ → u ; _ → u }` with `u : `⊤`. A-Case now restricts the branches
to `fvClose (fv e₁) ∪ fvClose (fv e₂)`. `Probe/CaseUnr.agda` is a positive regression
test (declarative derivation, algorithmic `alg`, `solvedΔ₀`).

## `LinStruct` is necessary — and Base.agda's comment cites the wrong invariant

`Probe/LinNeeded.agda`: with `h : ⟨ end ‼ ⟩` and `γ = ` 0F ∥ ` 0F`, the declarative
system types `h ⊗ h` (T-Pair par) and no algorithmic derivation exists, so
`Complete⇐` without `LinStruct` is refuted (`refute-noLin`).
`` ` x ≼ ` x ∥ ` x `` is underivable NOT by `≼⇒count≤` (Confine.agda) — `1 ≤ 2` holds —
but by `count-≼-eq` (Simulation/Support/BeforeOrder.agda:114), which says `≼`
*preserves* the count of a non-unrestricted variable: `1 ≢ 2`.

## Attack on C8's fix (constraint-generating `≼ ↑ Δ`)

Beyond the deciding item above:

* *Mobility only up to `≃`*: no problem, `mobile-≃` already exists.
* *`∥′-dup` / `≼-∅` keep an `Unr` side condition*: sound only because `Unr` is
  reflected by σ. Now proved in `Probe/UnrReflect.agda` (`subTy-unr⁻¹`,
  `unrCx-reflect`, `unrCx-sub`); C8 should import or copy these.
* *The emitted `Mob(Γ)` covers a whole `∥′-tm-;` side*: matches the declarative
  `MobCx Γ α ⊎ MobCx Γ β`, so the step-for-step mirroring works (structures carry no
  types).
* **Independent of the fix**: `Complete⇐`/`Complete⇒` use ONE context for both
  judgments and hypothesise `SolvedCtx Γ`, but A-LetPair extends the context with
  *inferred* types (after A-RSplit the second is `⟨ acq ; `` α ⟩`). The induction
  hypothesis is not applicable to the body. The statement must be generalised to an
  algorithmic `Γ̂` with `∀ x → subTy (Γ̂ ﹫ x) σ₀ ≃ Γ ﹫ x`, with the produced σ
  extending σ₀. Same at A-Let, A-Case and A-Abs. (`retype` does not repair this: it
  changes the type, not the statement.)

## Smaller findings

* `SolvedTm` had no constructor for `` `let e₁ `in e₂ ``; recorded as fixed in
  DECISION-mobility.md §4.
* **`alg-weaken` (C3) cannot preserve `Δ`.** A-Abs emits one `C-Mob (Γ ﹫ x)` per
  variable of the ambient γ; weakening `γ₁ ≼ γ₂` adds variables, hence constraints.
  State it as `∃ Δ₂. alg under γ₂ ↑ Δ₂ × SolvedΔ Δ₂ σ`. The extra constraints are always
  satisfiable: `≼` adds structure only through `≼-∅`, whose side condition is `UnrCx`,
  and `Unr ⊆ Mobile`.
* Restriction monotonicity (`γ₁ ≼ γ₂ → γ₁ ↓ X ≼ γ₂ ↓ X`) and C1's canonical split
  lemma resisted attack; `count-≼-eq` and `before-mono-≼` are both consistent with the
  split lemma (cases `γ = x ; y`, `x ∥ y`, `(x ∥ y) ; z`, `x ; u ; y` with `u`
  unrestricted, X/Y overlapping on `u`, `d ∈ {𝟙, L, R}`).
* A-App's effect discipline is fine: `Arr.ω⇒𝟙` forces `dir a = 𝟙` when `Arr.Unr a`, and
  `EffCompat L/R` matches T-AppLeft's pure function / T-AppRight's pure argument.
