# Mechanised metatheory: where things are

## Main theorems

| Theorem | Statement | Location |
|---|---|---|
| Process preservation | `preservationₚ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q` | [BorrowedCF/Safety/Preservation.agda:39](BorrowedCF/Safety/Preservation.agda#L39) |
| Process progress (paper's Blocked) | `progressₚ : [] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)` | [BorrowedCF/Safety/Progress.agda:142](BorrowedCF/Safety/Progress.agda#L142) |
| Process progress (precise Blocked⁺) | `progress⁺ₚ : [] ; γ ⊢ₚ P → Blocked⁺ P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)` | [BorrowedCF/Safety/Progress.agda:148](BorrowedCF/Safety/Progress.agda#L148) |
| Algorithmic completeness, checking | `complete⇐ : Complete⇐` | [BorrowedCF/Completeness/Main.agda:119](BorrowedCF/Completeness/Main.agda#L119), exported by [BorrowedCF/Completeness.agda:19](BorrowedCF/Completeness.agda#L19) |
| Algorithmic completeness, inference | `complete⇒ : Complete⇒` | [BorrowedCF/Completeness/Main.agda:112](BorrowedCF/Completeness/Main.agda#L112), exported by [BorrowedCF/Completeness.agda:19](BorrowedCF/Completeness.agda#L19) |

Statement types of completeness ([BorrowedCF/Completeness/Base.agda](BorrowedCF/Completeness/Base.agda)):
```agda
Complete⇐ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ → Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
    Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / k)          -- line 35
Complete⇒ = … Σ[ T̂ ∈ 𝕋 ] … × (subTy T̂ σ ≃ T) × (Γ ; γ / m ⊢ e ⇒ T̂ ∣ ϵ′ ↑ Δ / k)   -- line 44
```

## Relevant definitions (new)

| Definition | Location |
|---|---|
| `Blocked` (tex rules B-*, one constructor each; `B-NuBlockedAcq` as `B-NuAcqˡ`/`B-NuAcqʳ`) | [BorrowedCF/Safety/Blocked.agda:345](BorrowedCF/Safety/Blocked.agda#L345) |
| `Blocked⁺` (B-NuBlockedAcq split into ˡ / ʳ / ˡʳ) | [BorrowedCF/Safety/Blocked.agda:374](BorrowedCF/Safety/Blocked.agda#L374) |
| `Stuck` (B-ExpConstBlocked shape), `_∈BCe_`, `_∈BC_`, `_∈AC_` | [Blocked.agda:73](BorrowedCF/Safety/Blocked.agda#L73), [:97](BorrowedCF/Safety/Blocked.agda#L97), [:291](BorrowedCF/Safety/Blocked.agda#L291), [:298](BorrowedCF/Safety/Blocked.agda#L298) |
| `LinStruct Γ γ = ∀ x → ¬ Unr (Γ ﹫ x) → count x γ ≤ 1` | [BorrowedCF/Completeness/Base.agda:25](BorrowedCF/Completeness/Base.agda#L25) |
| `SolvedCtx Γ = ∀ x → SolvedTy (Γ ﹫ x)` | [BorrowedCF/Completeness/Base.agda:29](BorrowedCF/Completeness/Base.agda#L29) |
| `_∶_≼_↑_`, `_∶_≈′_↑_`, `allMobile` (constraint-generating subcontext) | [BorrowedCF/Context/SubConstraint.agda:78](BorrowedCF/Context/SubConstraint.agda#L78), [:58](BorrowedCF/Context/SubConstraint.agda#L58), [:45](BorrowedCF/Context/SubConstraint.agda#L45) |
| `≼↑-sound` | [BorrowedCF/Context/SubConstraint.agda:135](BorrowedCF/Context/SubConstraint.agda#L135) |
| `≼↑-complete` | [BorrowedCF/Completeness/Sub.agda:229](BorrowedCF/Completeness/Sub.agda#L229) |
| canonical split `canon-split` | [BorrowedCF/Completeness/Split.agda](BorrowedCF/Completeness/Split.agda) |
| algorithmic weakening `alg-weaken` | [BorrowedCF/Completeness/Weaken/Instance.agda](BorrowedCF/Completeness/Weaken/Instance.agda) |
| unification-variable scope `scope` | [BorrowedCF/Completeness/Scope.agda](BorrowedCF/Completeness/Scope.agda) |
| restriction of declarative derivations `restrict` | [BorrowedCF/Completeness/Decl.agda](BorrowedCF/Completeness/Decl.agda) |

## Definitions changed (base files)

The algorithmic typing relation gained the rules the paper has but the mechanisation lacked (A-Let, `select`/`branch` through A-Const), its structural premises now mirror the declarative rules exactly (a `p/s` choice in A-LetPair and A-Let, per-branch restriction in A-Case), every subcontext premise emits mobility constraints instead of checking mobility (`… ≼ γ ↑ Δ₀`), and A-Ann is limited to checking forms. Three definitional gaps were closed alongside (the `let` constructor of `SolvedTm`, the `discard`/`select`/`branch` constructors of `SolvedC`, the postulate `parOrSeq?` proved); no declarative rule, process rule, session-type definition or simulation module changed.


[BorrowedCF/Algorithmic.agda](BorrowedCF/Algorithmic.agda)
```agda
-- ¬AlgConst: select/branch removed (now typed by A-Const)              -- line 102
data ¬AlgConst : Const → Set where
  `lsplit : ¬AlgConst (`lsplit s)
  `rsplit : ¬AlgConst (`rsplit s)

-- A-Let: new                                                            -- line 199
A-Let : (p/s : ParSeq) → let γ₁ = γ ∣fv[ e₁ ]; γ₂ = γ ↓ fvClose (fv e₂) in
  (≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ) →
  Γ ; γ₁ / m ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
  T ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ₂) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
  Γ ; γ / m ⊢ `let e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

-- A-LetPair: premise γ₁ ; γ₂ ≼ γ  ↦  join p/s γ₁ γ₂ ≼ γ;               -- line 189
--            body  (join d (` 0F) (` 1F)) ; wk (wk γ₂)  ↦  join p/s (join d (` 0F) (` 1F)) (wk (wk γ₂))

-- A-Case: branch structure  γ ↓ ∁ (fv e)  ↦  γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂));   -- line 209
--         premise JoinParSeq Γ γ (fv e) p/s  ↦  Γ ∶ join p/s (γ ∣fv[ e ]) γ₂ ≼ γ

-- A-Ann: premise ChkForm e added; data ChkForm has chk-ƛ, chk-μ, chk-⊗, chk-inj   -- lines 266, 141
A-Ann : ChkForm e → Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n → Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n

-- every subcontext premise of A-Var, A-Const, A-LSplit, A-RSplit, A-App, A-Seq, A-LetPair,
-- A-Let, A-Pair, A-Case:  Γ ∶ … ≼ γ  ↦  Γ ∶ … ≼ γ ↑ Δ₀, with Δ₀ prepended to the output, e.g.   -- line 158
A-Var : (≤γ : Γ ∶ ` x ≼ γ ↑ Δ₀) → Γ ; γ / m ⊢ ` x ⇒ Γ ﹫ x ∣ ℙ ↑ Δ₀ / m
```

[BorrowedCF/Context/SubConstraint.agda](BorrowedCF/Context/SubConstraint.agda) (new): `_∶_≈′_↑_` is `_∶_≈′_` with the two mobility rules
```agda
∥′-tmˡ↑ : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ α        ∥′-tmʳ↑ : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ β
```
(emitting `C-Mob (Γ ﹫ x)` per variable instead of requiring `MobCx`); `_∶_≼_↑_` is `_∶_≼_` over it, constraint lists concatenated.

[BorrowedCF/Algorithmic/Solved.agda:214](BorrowedCF/Algorithmic/Solved.agda#L214)
```agda
`let_`in_ : {e₁ : Tm n} {e₂ : Tm (1 + n)} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (`let e₁ `in e₂)   -- new
```
[BorrowedCF/Algorithmic/Solved.agda:202](BorrowedCF/Algorithmic/Solved.agda#L202)
```agda
`discard : SolvedC `discard            -- new; SolvedC now covers every constant
`select : ∀ {k} → SolvedC (`select k)
`branch : SolvedC `branch
```

[BorrowedCF/Context/Join.agda:162](BorrowedCF/Context/Join.agda#L162)
```agda
parOrSeq? : Γ ∶ α ; β ≼ γ → Σ[ p/s ∈ ParSeq ] Γ ∶ join p/s α β ≼ γ     -- was a postulate
parOrSeq? ≤γ = seq , ≤γ
```

[tex/rules/blocked.tex:60](../tex/rules/blocked.tex#L60) — commented block with the precise rules B-NuBlockedAcqLeft / Right / Both.

## Not changed
Declarative typing (Terms/Base.agda), process typing and reduction, Types/*, all of Simulation/.

## Discrepancies with the paper (recorded 2026-10-06)

| Paper | Agda |
|---|---|
| Algorithmic rules normalise types (`\NormaliseType` in A-Var, A-App, A-Annot, A-Abs, A-AbsRec, A-Select, A-Pair, A-Inj) | No rule normalises. The constant types of `select`/`branch` ([Terms/Base.agda:159](BorrowedCF/Terms/Base.agda#L159)) take arbitrary branch types, and A-Check emits `C-Eq T U`, solved modulo `≃` ([Solved.agda:328](BorrowedCF/Algorithmic/Solved.agda#L328)). Design of the original algorithmic system (Janek Spaderna, June 2026), never changed. Proven: this normalisation-free system is sound and complete. Every paper derivation with normalisation maps to an Agda derivation up to `≃`; the converse fails when `select`/`branch` act on a channel whose type is a unification variable (continuation of a split). The paper was aligned on 2026-10-06: A-Select, A-Branch and all normalisation premises removed, `select`/`branch` typed by A-Const. |
| Labelled choice `⊕{ℓ : S_ℓ}_{ℓ∈L}` | Binary choice `brn p s₁ s₂`, `select : Bool → Const`. |
| A-Annot reads an annotation `e : T` | No annotation syntax. `A-Ann : ChkForm e → … ⇐ T … → … ⇒ T …` receives `T` directly ([Algorithmic.agda:266](BorrowedCF/Algorithmic.agda#L266)). Inference completeness therefore reads, on paper, "every checking form in inference position is annotated with its declarative type". |
| Process progress for any session context | `progressₚ`/`progress⁺ₚ` are for closed processes (`[] ; γ ⊢ₚ P`, `γ : Struct 0`). |
| Blocked with B-NuBlockedAcq | Figure now shows B-NuBlockedAcqLeft/Right/Both, i.e. `Blocked⁺` ([Safety/Blocked.agda:374](BorrowedCF/Safety/Blocked.agda#L374)), proved by `progress⁺ₚ`. |
| Weak simulation up to administrative steps, tree-shaped target | Lock-step forward and backward simulation for the process soup, backward up to slot renumbering `_≈ˢ_` ([BackwardSoup/Statement.agda:222](BorrowedCF/Simulation/BackwardSoup/Statement.agda#L222)). |

## 2026-10-07: repair of the relaxed splits

Upstream relaxed the splits (commits 469f079, 85720a8): `rsplit` accepts `skip` as first type, both
splits require `Local s′` ([Types/Predicates.agda](BorrowedCF/Types/Predicates.agda): `NonLocal`, `Local = ¬ NonLocal`).

| Change | Location |
|---|---|
| Counterexample: `mu (acq ; ` 0)` was `Local` yet `≃ acq ; …`; breaks the acq-head invariant under the relaxed `rsplit` | [BorrowedCF/Safety/Probe/LocalMuGap.agda](BorrowedCF/Safety/Probe/LocalMuGap.agda), memo [Splits/DECISION-local-mu.md](BorrowedCF/Safety/Preservation/Splits/DECISION-local-mu.md) |
| Fix: `mu : NonLocal s → NonLocal (mu s)`; μ clauses in `nonLocal-⋯`, `nonLocal-⋯ᵣ⁻¹`, `nonLocal-dual⁺`, `nonLocal-dual⁻`, `skips⇒local` | [BorrowedCF/Types/Predicates.agda](BorrowedCF/Types/Predicates.agda) |
| μ clause of `subTy-local` | [BorrowedCF/Algorithmic/Solved.agda](BorrowedCF/Algorithmic/Solved.agda#L195) |
| `acqHead-rsplit` now takes `∀ u → ¬ (t₂ ≃ acq ; u)` (from `Local t₂` via `local⇒¬acqHead`); `bindCtx-rsplit` takes `Local t₂ → ¬ Skips t₂` | [Splits/Group.agda](BorrowedCF/Safety/Preservation/Splits/Group.agda) |
| `local⇒¬acqHead′ : Local t₂ → ¬ Skips t₂ → ∀ u → ¬ (t₂ ≃ acq ; u)` (new module) | [Splits/LocalHead.agda](BorrowedCF/Safety/Preservation/Splits/LocalHead.agda) |
| New split arities threaded (patterns `` `lsplit t₁ t₂ ¬S₁ L₂ ¬S₂ ``, `` `rsplit t₁ t₂ L₂ ¬S₂ ``); `mob-rsplit`, `θR-⇒` take `Local t₂` | Safety/Progress/Expr.agda, Safety/Preservation/{RSplit,LSplit/Immobile,LSplit/Mobile}.agda, Splits/Redex.agda |
| `chanCx-⸴*` exported (fixes `Simulation/Forward.agda` and dependents) | [BorrowedCF/Reduction/Base.agda](BorrowedCF/Reduction/Base.agda) |
| Deleted dead modules of the removed tree-shaped backward proof | `Simulation/Support/ReverseInv.agda`, `Simulation/Support/RevComImage.agda` |

`Completeness/Probe/MobUvar.agda` is deleted (2026-10-07): the relaxed `lsplit` requires `Local` on
the split continuation, which makes that probe's term untypable, so its counterexample claim is void;
[Probe/MobUvarWF.agda](BorrowedCF/Completeness/Probe/MobUvarWF.agda) supersedes it.

## 2026-10-07: syntactic type annotation

The term languages gained a type-annotation construct, so the algorithmic rule A-Ann is now
syntax-directed; the dynamics erase the annotation in one step and both simulations stay lock-step.

| Change | Location |
|---|---|
| `_⦂_ : (e : Tm n) (T : 𝕋) → Tm n` (infixl 5) in BOTH term languages; `strip` | [Terms/Base.agda](BorrowedCF/Terms/Base.agda), [Terms/BaseSoup.agda](BorrowedCF/Terms/BaseSoup.agda) |
| `T-Ann : Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ⊢ e ⦂ T ∶ T ∣ ϵ`; inversion `inv-⦂` | [Terms/Base.agda](BorrowedCF/Terms/Base.agda) |
| `E-Ann : (e ⦂ T) ─→ e` in both expression reductions; `(e ⦂ T)` is not a value, no new frame | [Reduction/Expressions.agda](BorrowedCF/Reduction/Expressions.agda), [Reduction/ExpressionsSoup.agda](BorrowedCF/Reduction/ExpressionsSoup.agda) |
| Translations homomorphic: `T[ e ⦂ T ] σ = T[ e ] σ ⦂ T` (definitional) | [Processes/TranslationSoup.agda](BorrowedCF/Processes/TranslationSoup.agda) |
| `A-Ann : Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n → Γ ; γ / m ⊢ (e ⦂ T) ⇒ T ∣ ϵ ↑ Δ / n` (ChkForm premise gone; ChkForm kept as the completeness insertion guide) | [Algorithmic.agda](BorrowedCF/Algorithmic.agda) |
| `SolvedTm` case `_⦂_`; `subTm (e ⦂ T) σ = subTm e σ ⦂ subTy T σ` | [Algorithmic/Solved.agda](BorrowedCF/Algorithmic/Solved.agda) |
| Annotation relation `_⊑_` (congruences + `ann : e ⊑ ê → ∀ T → e ⊑ (ê ⦂ T)`), `fv-⊑ : e ⊑ ê → fv ê ≡ fv e` | [Completeness/Base.agda](BorrowedCF/Completeness/Base.agda) |
| Completeness statements now conclude `Σ[ ê ∈ Tm n ] e ⊑ ê × (… ⊢ ê ⇐/⇒ …)` (annotations inserted at checking forms in inference position) | [Completeness/Base.agda](BorrowedCF/Completeness/Base.agda), proofs in [Completeness/Main.agda](BorrowedCF/Completeness/Main.agda) and Main/* |
| Safety: annotated terms are never values, plugs, or blocked; progress steps them by E-Ann; preservation passes T-Ann through | Safety/Progress/Expr/Plug.agda, Safety/Blocked.agda, Safety/Preservation/Choice/Retype.agda |
| Simulations: E-Ann maps to E-Ann (forward) and reflects (backward, `T-ann-inv`, `head-inversion`); lock-step statements unchanged | Simulation/ForwardSoup/Expressions.agda, Simulation/BackwardSoup/Inversion.agda, SlotBisim.agda, Support/{Strengthen,Frames}.agda |

## Verification
Every module under `Safety/` and `Completeness/` re-checked from an empty interface cache with Agda 2.8.0 and stdlib 2.4: zero goals, no `postulate`, no pragmas. The only axiom reachable is `funext` in `Simulation/Support/Base.agda` (pre-existing). `chanCx-⸴*` is now defined in `Reduction.Base`; `Simulation/Forward.agda` checks, and the two dead support modules that also used it are deleted (2026-10-07). `Simulation/BackwardSoup` and `ForwardSoup` pass. The incomplete legacy `Simulation/Backward` namespace referenced above was subsequently removed; the strict-soup backward proof is the maintained result.
