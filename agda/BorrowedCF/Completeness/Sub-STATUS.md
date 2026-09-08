# C8 — constraint-generating subcontext relation (`Completeness/Sub.agda`)

Owner: agent C8.  Files: `Completeness/Sub.agda`, `Completeness/Sub/Base.agda`,
`Completeness/Sub/Probe.agda`.  All three type-check with `agda-check`, **zero goals,
zero unsolved metas, no postulates**.  Nothing outside `Completeness/` was touched.

NOTE for whoever copies code out of this file: every `;` in an Agda snippet below is
U+037E, not ASCII `;` (see `Completeness/AGENTS.md`).  Copy the character from
`Completeness/Sub.agda`, do not retype it.

## What this fixes

C4's BLOCKING FINDING 1 (`Completeness/Main-STATUS.md`): the A-rules check
`Γ ∶ γ₁ ≼ γ₂` in a context whose types still contain unification variables, and the
rule `∥′-tm-;` of `_∶_≈′_` (Context/Equivalence.agda) — hence `;-commMob`, `;-unit₁`,
`;-unit₂`, `∥/;-transmute` — needs `MobCx`.  `Mobile` is not reflected along `subTy`
(`Mobile ⟨ s ⟩` is `∃ s′. Bounded s′ × s ≃ acq ; s′`, and a uvar leaf `` `` α `` is a
leaf of `≃𝕊`), so completeness is false.  `Unr` *is* reflected (`Unr` is `⊥` on every
session type), so `∥′-dup` and `≼-∅` are unaffected.

`Completeness/Sub.agda` defines the repaired judgment and proves that it is sound,
complete for the transfer step, and a conservative refinement of `≼`.

## Delivered definitions

| name | statement | file |
|---|---|---|
| `_∶_≈′_↑_` | one-step context equivalence with emitted constraints; 10 rules mirroring `_∶_≈′_` | Sub.agda:52 |
| `_∶_≈_↑_` | its reflexive/symmetric/transitive closure (`ε↑`, `_◅ᶠ_`, `_◅ᵇ_`), constraint lists concatenated | Sub.agda:67 |
| `_∶_≼_↑_` | subcontext with emitted constraints; 6 rules mirroring `_∶_≼_` | Sub.agda:72 |
| `JoinParSeq↑` | the A-Case premise, indexed by its constraint set | Sub.agda:223 |
| `MobHolds` | `MobHolds (C-Mob T) = Mobile T`, `MobHolds (C-Eq _ _) = ⊤` | Sub.agda:330 |
| `Approx Γ̂ Γ σ` | `∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x` | Sub/Base.agda |

The single design decision: `∥′-tm-;`'s premise `MobCx Γ α ⊎ MobCx Γ β` becomes two
constructors, `∥′-tmˡ↑ : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ α` and
`∥′-tmʳ↑ : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ β`.  Every other rule emits `[]` or
concatenates the constraint sets of its premises.  `∥′-dup↑` keeps `UnrCx Γ α`,
`≼-∅↑` keeps `UnrCx Γ α`.

Because `allMobile Γ [] = []`, the units `sq-unit₁↑ : Γ ∶ [] ; α ≈ α ↑ []` and
`sq-unit₂↑ : Γ ∶ α ; [] ≈ α ↑ []` are constraint-FREE, and so is `sq-≼-par↑`
(`; ≼ ∥`) and `sq-≼-join↑`.  Only a genuine `;`-commutation or a genuine
`∥ ⇝ ;` transmutation costs constraints.

## Lemma status (all `proved`)

| lemma | statement | status |
|---|---|---|
| `subTy-unr⁻¹` | `Unr (subTy T σ) → Unr T` | proved (Sub/Base.agda) |
| `approx-⸴` | `subTy T̂ σ ≃ T → Approx Γ̂ Γ σ → Approx (T̂ ⸴ Γ̂) (T ⸴ Γ) σ` | proved (Sub/Base.agda) |
| `approx-id` | `SolvedΓ Γ σ → Approx Γ (subCtx Γ σ) σ` | proved (Sub/Base.agda) |
| `unrCx-approx` | `Approx Γ̂ Γ σ → UnrCx Γ α → UnrCx Γ̂ α` | proved (Sub/Base.agda) |
| `mobCx⇒solvedΔ` | `Approx Γ̂ Γ σ → MobCx Γ α → SolvedΔ (allMobile Γ̂ α) σ` | proved (Sub/Base.agda) |
| `unrCx-sub` | `UnrCx Γ α → UnrCx (subCtx Γ σ) α` | proved (Sub/Base.agda) |
| `≈↑-cast` / `≼↑-cast` | re-index along `Δ ≡ Δ′` | proved |
| `≈↑-trans` | `α ≈ β ↑ Δ₁ → β ≈ γ ↑ Δ₂ → α ≈ γ ↑ (Δ₁ ++ Δ₂)` | proved |
| `≈↑-sym` | `α ≈ β ↑ Δ → Σ[ Δ′ ] (β ≈ α ↑ Δ′) × (∀ {σ} → SolvedΔ Δ σ → SolvedΔ Δ′ σ)` | proved |
| `≈↑-par-cong₁`, `≈↑-sq-cong₁`, `≈↑-sq-cong₂` | congruences preserving Δ | proved |
| `∥-assoc↑ ∥-comm↑ ∥-unit₁↑ ∥-unit₂↑ ∥-dup↑ sq-assoc↑` (+ the `⁻¹` reverses) | the derived equivalences of Context/Equivalence.agda, all at `↑ []` | proved |
| `∥-cong↑`, `sq-cong↑` | congruences at `↑ (Δ₁ ++ Δ₂)` | proved |
| `transmuteˡ↑` / `transmuteʳ↑` | `α ∥ β ≈ α ; β ↑ allMobile Γ α` / `↑ allMobile Γ β` | proved |
| `sq-unit₁↑`, `sq-unit₂↑` (+ `⁻¹`) | `[] ; α ≈ α ↑ []`, `α ; [] ≈ α ↑ []` | proved |
| `sq-commMobˡ↑` / `sq-commMobʳ↑` | `α ; β ≈ β ; α ↑ (allMobile Γ α ++ allMobile Γ α)` (resp. β) | proved |
| `sq-≼-par↑` | `Γ ∶ α ; β ≼ α ∥ β ↑ []` | proved |
| `sq-≼-join↑`, `join-≼-par↑` | `α ; β ≼ join p/s α β ↑ []`, `join p/s α β ≼ α ∥ β ↑ []` | proved |
| `≼-join↑` | `≼ ↑ Δ₁ → ≼ ↑ Δ₂ → join p/s … ≼ join p/s … ↑ (Δ₁ ++ Δ₂)` | proved |
| `parOrSeq?↑` | `Γ ∶ α ; β ≼ γ ↑ Δ → Σ[ p/s ] Γ ∶ join p/s α β ≼ γ ↑ Δ` | proved |
| `join-joinParSeq↑` | `JoinParSeq↑ Γ γ X p/s Δ → Γ ∶ join p/s (γ ↓ X) (γ ↓ ∁ X) ≼ γ ↑ Δ` | proved |
| **`≈′↑-sound`** | `Solving σ → SolvedΔ Δ σ → Γ ∶ α ≈′ β ↑ Δ → subCtx Γ σ ∶ α ≈′ β` | proved |
| **`≈↑-sound`** | `Solving σ → SolvedΔ Δ σ → Γ ∶ α ≈ β ↑ Δ → subCtx Γ σ ∶ α ≈ β` | proved |
| **`≼↑-sound`** | `Solving σ → SolvedΔ Δ σ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → subCtx Γ σ ∶ γ₁ ≼ γ₂` | proved |
| `≼↑-sound-++` | same, splitting `SolvedΔ (Δ ++ Δ′) σ` — the form the A-rules use | proved |
| **`≈′↑-complete`** | `Solving σ → Approx Γ̂ Γ σ → Γ ∶ α ≈′ β → Σ[ Δ ] (Γ̂ ∶ α ≈′ β ↑ Δ) × SolvedΔ Δ σ` | proved |
| **`≈↑-complete`** | same for `≈` | proved |
| **`≼↑-complete`** | `Solving σ → (∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x) → Γ ∶ γ₁ ≼ γ₂ → Σ[ Δ ] (Γ̂ ∶ γ₁ ≼ γ₂ ↑ Δ) × SolvedΔ Δ σ` | proved |
| `≼↑-complete-solved` | the `Γ̂ := Γ` instance via `approx-id` | proved |
| `allMobile-holds` / `allMobile-holds⁻¹` | `MobCx Γ α ↔ All MobHolds (allMobile Γ α)` | proved |
| **`≼⇒≼↑`** | `Γ ∶ γ₁ ≼ γ₂ → Σ[ Δ ] (Γ ∶ γ₁ ≼ γ₂ ↑ Δ) × All MobHolds Δ` (+ `≈⇒≈↑`, `≈′⇒≈′↑`) | proved |
| **`≼↑-erase`** | `All MobHolds Δ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → Γ ∶ γ₁ ≼ γ₂` (+ `≈↑-erase`, `≈′↑-erase`) | proved |

### On `≼↑-weaken-Δ`

Weakening the index (`Γ ∶ γ₁ ≼ γ₂ ↑ Δ → Γ ∶ γ₁ ≼ γ₂ ↑ (Δ ++ Δ′)`) is **not derivable**:
the constraint set of a derivation is determined by the rules it uses, and no rule can
emit spurious constraints.  It is also **not needed**.  The A-rule carries the literal
index `Δ₀` of its own `≼↑` premise into its own output constraints; at the use site the
`SolvedΔ` is split with `All.++⁻ˡ / ++⁻ʳ`, exactly as the existing `sound` already does
for `Δ₁ ++ Δ₂`.  The two forms that *are* delivered are `≼↑-cast` (re-index along a
propositional equality, used to normalise `Δ ++ []`) and `≼↑-sound-++`.

The requested `≼ → ≼ ↑ []` embedding is false whenever the derivation takes a mobility
step; `≼⇒≼↑` + `≼↑-erase` is the honest replacement (a round trip: `≼` and `≼↑` with
outright-valid constraints are interderivable).  The fragment that *does* embed at
`↑ []` is everything below `sq-≼-par↑` / `sq-≼-join↑` / `≼-wk↑` / `≼-∅↑` /
`≼-refl↑ ε↑` plus the six constraint-free equivalences, listed above.

## PROPOSED BASE CHANGE (for the base-editing agent, after user approval)

### 0. Placement

`allMobile` currently lives in `Algorithmic.agda`, but the relation must be available to
`Algorithmic.agda`'s own rules.  Move the 5-line `allMobile` into a new module
`BorrowedCF/Context/Constraints.agda` (imports `Context.Base` + `Types.Unification`),
then put the three data types of `Completeness/Sub.agda` into
`BorrowedCF/Context/SubcontextC.agda`, and let `Algorithmic.agda` import both.
`Algorithmic.mobConstraints` keeps its definition in terms of the moved `allMobile`.
The proofs in `Completeness/Sub.agda` move with them unchanged (they use nothing from
`Completeness/`).

### 1. Rules of `Algorithmic.agda` whose `≼` premise becomes `≼ ↑ Δ₀`

Every occurrence of the named premise gets an extra implicit `Δ₀ : CSet`, and `Δ₀` is
prepended to the rule's output constraint set.

| rule | premise now | premise after | output constraints now | after |
|---|---|---|---|---|
| `A-Var` | `≤γ : Γ ∶ ` x ≼ γ` | `≤γ : Γ ∶ ` x ≼ γ ↑ Δ₀` | `[]` | `Δ₀` |
| `A-Const` | `≤γ : Γ ∶ [] ≼ γ` | `… ↑ Δ₀` | `[]` | `Δ₀` |
| `A-LSplit` | `≤γ : Γ ∶ [] ≼ γ` | `… ↑ Δ₀` | `[]` | `Δ₀` |
| `A-RSplit` | `≤γ : Γ ∶ [] ≼ γ` | `… ↑ Δ₀` | `[]` | `Δ₀` |
| `A-App` | `≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ` | `… ↑ Δ₀` | `Δ₁ ++ Δ₂` | `Δ₀ ++ Δ₁ ++ Δ₂` |
| `A-Seq` | `≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ` | `… ↑ Δ₀` | `Δ₁ ++ Δ₂` | `Δ₀ ++ Δ₁ ++ Δ₂` |
| `A-LetPair` | `≤γ : Γ ∶ γ₁ ; γ₂ ≼ γ` | `… ↑ Δ₀` | `Δ₁ ++ Δ₂` | `Δ₀ ++ Δ₁ ++ Δ₂` |
| `A-Let` | `≤γ : Γ ∶ γ₁ ; γ₂ ≼ γ` | `… ↑ Δ₀` | `Δ₁ ++ Δ₂` | `Δ₀ ++ Δ₁ ++ Δ₂` |
| `A-Pair` | `≤γ : Γ ∶ join p/s (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ` | `… ↑ Δ₀` | `Δ₁ ++ Δ₂` | `Δ₀ ++ Δ₁ ++ Δ₂` |
| `A-Case` | `JoinParSeq Γ γ (fv e) p/s` | `JoinParSeq↑ Γ γ (fv e) p/s Δ₀` | `C-Eq U₁ U₂ ∷ Δ ++ Δ₁ ++ Δ₂` | `C-Eq U₁ U₂ ∷ Δ₀ ++ Δ ++ Δ₁ ++ Δ₂` |

`A-Abs`, `A-AbsRec`, `A-Inj`, `A-Check`, `A-Ann` are unchanged.  `A-Abs`/`A-AbsRec`
carry `UnrCx Γ γ` premises, and `Unr` *is* reflected (`subTy-unr⁻¹`), so they stay as
they are.  `A-Abs` already turns its `Mobile` side condition into `mobConstraints`; the
change above applies the same treatment to the subcontext premises.

### 2. `sound` in `Algorithmic.agda`

In each of the nine `≼`-premise cases replace

    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ) …

by

    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ) …

and shift every existing split by one: `All.++⁻ˡ Δ₁ SΔ` becomes
`All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ)`, and likewise for `++⁻ʳ`.  (`≼↑-sound-++ Sσ Δ₀ ≤γ SΔ`
packages the first step.)  Concretely:

* `A-Var`, `A-Const`, `A-LSplit`, `A-RSplit`: `SΔ : SolvedΔ Δ₀ σ`, so the replacement is
  just `≼↑-sound Sσ SΔ ≤γ`.
* `A-App`, `A-Seq`, `A-Pair`: `≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ`, then feed
  `All.++⁻ʳ Δ₀ SΔ` to the existing `Δ₁ / Δ₂` splits.
* `A-LetPair`, `A-Let`: `let p/s , join≼ = parOrSeq? (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)`
  and drop the surrounding `≼-map⁺` (`≼↑-sound` already lands in `subCtx Γ σ`).
* `A-Case`: `≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ′) (join-joinParSeq↑ j-p/s)` where `SΔ′` is the
  tail after the leading `C-Eq U₁ U₂`.

No other proof in `Algorithmic.agda` changes; `⊢-sub` and the `sound-app` helper are
untouched.

`Completeness/Sub/Probe.agda` states and proves these four obligations verbatim
(`probe-nullary`, `probe-binary`, `probe-letpair`, `probe-case`), so the rule shapes in
the table above are mechanically checked, not guessed.

### 3. Decidability

`Context/Subcontext.agda` postulates `_∶_≼?_`.  The constraint version must *produce* a
constraint set, so the postulate becomes something of the shape

    _∶_≼?_↑ : (Γ : Ctx n) (γ₁ γ₂ : Struct n) → Dec (Σ[ Δ ∈ CSet ] Γ ∶ γ₁ ≼ γ₂ ↑ Δ)

(“no derivation at all” on the negative side).  The algorithm should return the set with
`Mobile` demanded of as few variables as possible; the search space is the same as
before, only the mobility checks are recorded instead of performed.

### 4. Consequence for the paper

Concretely, in `tex/rules/typing-algorithmic.tex` (macro `\SubCtx = \preccurlyeq`,
`symbols.tex:164`):

| rule | line | premise | becomes |
|---|---|---|---|
| A-Const | 8 | `\CtxEmpty \SubCtx \Ctx` | `… \SubCtx \Ctx \csred \CSet[0]`, output `\CSet[0]` |
| A-LSplit | 16 | same | same |
| A-RSplit | 27 | same | same |
| A-Var | 65 | `\CtxVar \EVar \T \SubCtx \Ctx` | same |
| A-App | 75 | `\CtxAlgJoinCheck{\E[1]}{\E[2]}` | `\CSet[0]` added to the conclusion's set |
| A-Pair | 141 | `\CtxAlgJoinCheck{\E[1]}{\E[2]}` | idem |
| A-Seq | 166 | `\CtxAlgSeqCheck{\E[1]}{\E[2]}` | idem |
| A-LetPair | 190 | `\CtxAlgSeqCheck{\E[1]}{\E[2]}` | idem |
| A-Case | 238 | `\Dir = \CaseJoinDir(\Ctx, \Fv(\E))` | the metafunction hides the same `\SubCtx` check, so it must return a constraint set as well |

The two macros `\CtxAlgJoinCheck` / `\CtxAlgSeqCheck` (`symbols.tex:170,173`) expand to a
`\SubCtx`, so changing the judgment changes them in one place.  A-Abs (line 115) already
emits `\CMobile{\T*}` constraints for the mobility of its captured context, which is the
pattern the subcontext premises have to follow.


The paper's algorithmic rules carry the same defect: their subcontext premise
`Γ ⊑ Γ′` is checked on contexts whose types contain unification variables, and the
context-equality rules behind it have `Mobile` side conditions.  The rules must be
restated with a constraint-generating subcontext judgment

    Γ ⊑ Γ′ ↑ C

where the `Mobile` side condition of the equality rule that turns `∥` into `;` (and of
everything derived from it — commutation of `;` for mobile parts) emits a mobility
constraint `Mob(Γ(x))` for each variable x of the affected part, and the generated `C`
is added to the constraints of the rule that uses the premise.  The `Unr` side
conditions (duplication, and adding an unrestricted part) stay side conditions: `Unr` is
decided syntactically and is preserved *and reflected* by type substitution, whereas
`Mobile` is only preserved.  Soundness of the algorithm is unaffected (`≼↑-sound`), and
completeness needs exactly this change (`≼↑-complete`).

### 5. The counterexample of BLOCKING FINDING 1 goes through

With the change, A-Seq's premise in C4's counterexample becomes
`` Γ̂ ∶ (` 1F) ; (` 0F) ≼ (` 0F) ; (` 1F) ↑ allMobile Γ̂ (` 1F) ``, i.e. the single
constraint `` C-Mob ⟨ `` α ⟩ ``, produced by `sq-commMobˡ↑`.  `SolvedCst` for it is
`` Mobile (subTy ⟨ `` α ⟩ σ) ``, which the substitution `σ α = acq ; end ‼` of the
example satisfies.  `≼↑-complete` is exactly the general statement of this step: the
declarative `;-commMob`, justified by `Mobile ⟨ acq ; end ‼ ⟩`, is transported to the
uvar context as a solvable constraint by `mobCx⇒solvedΔ` (via `mobile-≃`).

## Notes for other agents

* C4: `≼-ctx` becomes `≼↑-complete Sσ ap` where `ap : Approx Γ̂ Γ σ` is built from the
  IH's `∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x` and extended over binders with `approx-⸴`.
  The `mob-reflect` module parameter (marked `GAP (false in general)`) can go.
* The `Δ` produced by `≼↑-complete` is the one that must be appended to the A-rule's
  constraint output, so the ordering in the table above (`Δ₀` first) is what the
  completeness proof wants: it builds `Δ₀` before the subderivations.
