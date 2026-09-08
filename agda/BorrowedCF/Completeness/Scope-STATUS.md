# Scope (agent C2) — unification-variable bookkeeping  [COMPLETE]

Files delivered (all check with `agda-check`, zero goals, zero unsolved metas, no postulates,
no `{-# TERMINATING #-}`):

- `Completeness/Scope/Base.agda`   (159 lines) — the predicate and substitution agreement
- `Completeness/Scope/Merge.agda`  (139 lines) — merging and singleton substitutions
- `Completeness/Scope.agda`        (~270 lines) — `GuessIn`, `scope`, context/term facts
  (re-exports Base and Merge, so `open import BorrowedCF.Completeness.Scope` is enough)
- `Completeness/Scope/Smoke.agda`  — three usage examples (merge, single, scope⇒); kept as a
  regression check that the API is usable with the implicits it has.

## Exported statements

### Scope/Base.agda
- `InRange lo hi α = lo ≤ UV.var α × UV.var α < hi` (polarity irrelevant). proved
- `inRange-mono : (α : UVar) → m′ ≤ m → n ≤ n′ → InRange m n α → InRange m′ n′ α`. proved
- `data UVarsIn (lo hi : ℕ) : ∀ {κ x} → Ty κ x → Set` — one constructor per `Ty` constructor
  (names mirror `SolvedTy`), `` ``_ : InRange lo hi α → UVarsIn lo hi (`` α) ``. proved
- `uvarsIn-mono : m′ ≤ m → n ≤ n′ → UVarsIn m n t → UVarsIn m′ n′ t`. proved
- `solved⇒uvarsIn : SolvedTy t → UVarsIn m n t`. proved
- `data UVarsInC (lo hi : ℕ) : Constraint → Set` with `C-Eq`, `C-Mob`. proved
- `UVarsInΔ m n Δ = All (UVarsInC m n) Δ`; `uvarsInC-mono`, `uvarsInΔ-mono`, `uvarsInΔ-++`. proved
- `record Agree (m n : ℕ) (σ₁ σ₂ : UV.Sub)` — constructor `agree`, field
  `ap≡ : ∀ α → m ≤ UV.var α → UV.var α < n → UV.ap σ₁ α ≡ UV.ap σ₂ α`. proved
- `agree-sym`, `agree-empty : Agree n n σ₁ σ₂`. proved
- `subTy-agree : Agree m n σ₁ σ₂ → UVarsIn m n t → subTy t σ₁ ≡ subTy t σ₂`. proved
- `solvedCst-agree : Agree m n σ₁ σ₂ → UVarsInC m n C → SolvedCst C σ₁ → SolvedCst C σ₂`. proved
- `solvedΔ-agree : Agree m n σ₁ σ₂ → UVarsInΔ m n Δ → SolvedΔ Δ σ₁ → SolvedΔ Δ σ₂`. proved
- `solvedΔ-indep : UVarsInΔ n n Δ → SolvedΔ Δ σ₁ → SolvedΔ Δ σ₂`. proved

### Scope/Merge.agda
- `merge : ℕ → UV.Sub → UV.Sub → UV.Sub` — σ₁ on `var α < k`, σ₂ otherwise; `ap-¬skips` and
  `ap-dual/dual` inherited (the ⁇-twin has the same index, so it takes the same branch). proved
- `merge-below : ∀ k σ₁ σ₂ α → UV.var α < k → UV.ap (merge k σ₁ σ₂) α ≡ UV.ap σ₁ α`. proved
- `merge-above : ∀ k σ₁ σ₂ α → k ≤ UV.var α → UV.ap (merge k σ₁ σ₂) α ≡ UV.ap σ₂ α`. proved
- `merge-solving : ∀ k σ₁ σ₂ → Solving σ₁ → Solving σ₂ → Solving (merge k σ₁ σ₂)`. proved
- `merge-agree-below : ∀ k σ₁ σ₂ → Agree m k σ₁ (merge k σ₁ σ₂)`,
  `merge-agree-above : ∀ k σ₁ σ₂ → Agree k n σ₂ (merge k σ₁ σ₂)`. proved
- `solvedΔ-∷`, `solvedΔ-++`. proved
- `solvedΔ-merge : ∀ k σ₁ σ₂ → UVarsInΔ m k Δ₁ → UVarsInΔ k n Δ₂ → SolvedΔ Δ₁ σ₁ →
   SolvedΔ Δ₂ σ₂ → SolvedΔ (Δ₁ ++ Δ₂) (merge k σ₁ σ₂)`. proved
- `merge₃ k₁ k₂ σ σ₁ σ₂ = merge k₁ σ (merge k₂ σ₁ σ₂)` and
  `solvedΔ-merge₃ : ∀ k₁ k₂ σ σ₁ σ₂ → k₁ ≤ k₂ → k₂ ≤ n → UVarsInΔ m k₁ Δ → UVarsInΔ k₁ k₂ Δ₁ →
   UVarsInΔ k₂ n Δ₂ → SolvedΔ Δ σ → SolvedΔ Δ₁ σ₁ → SolvedΔ Δ₂ σ₂ →
   SolvedΔ (Δ ++ Δ₁ ++ Δ₂) (merge₃ k₁ k₂ σ σ₁ σ₂)` (A-Case; cons the `C-Eq U₁ U₂` in front with
  `solvedΔ-∷`). proved
- `single α s ¬Ss = UV.subAll {s = UV.dual/id α s} …` with `single-ap : UV.ap (single α s ¬Ss) α ≡ s`,
  `single-ap-dual : UV.ap (single α s ¬Ss) (UV.dual α) ≡ dual s`,
  `single-solving : SolvedTy s → Solving (single α s ¬Ss)`, `solved-dual/id`. proved

### Scope.agda
- `uvarsIn-→₁/→₂/⊗₁/⊗₂/⊕₁/⊕₂` — inversions of `UVarsIn` at →, ⊗, ⊕. proved
- `record UVarsInΓ (lo hi : ℕ) {N} (Γ : Ctx N)` — constructor `ctx`, field
  `lookupΓ : ∀ x → UVarsIn lo hi (Γ ﹫ x)`; `uvarsInΓ-mono`, `uvarsInΓ-⸴`,
  `solvedCtx⇒uvarsInΓ`. proved
- `uvarsInΔ-allMobile`, `uvarsInΔ-mobConstraints`. proved
- `GuessIn k d : Set` — recursion over the derivation collecting the scope obligation of the
  two rules whose type is GUESSED: `A-Const` (`UVarsIn k m T`) and `A-Ann` (`UVarsIn k m T`),
  plus `A-LSplit`/`A-RSplit` (`UVarsIn k m s`, i.e. the split type of the constant); every other
  rule is the conjunction over its premises (`⊤` for A-Var). proved
- `ScopeIn : Mode → ℕ → ℕ → 𝕋 → Set`; `ScopeIn inf k m T = ⊤`, `ScopeIn chk k m T = UVarsIn k m T`. proved
- `scope-gen : (d : Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n) → GuessIn k d → UVarsInΓ k m Γ →
   k ≤ m → ScopeIn ξ k m T → m ≤ n × UVarsIn k n T × UVarsInΔ k n Δ`. proved
- `scope : SolvedCtx Γ → (d : …) → GuessIn m d → ScopeIn ξ m m T →
   m ≤ n × UVarsIn m n T × UVarsInΔ m n Δ`. proved
- `scope⇒ : SolvedCtx Γ → (d : … ⇒ …) → GuessIn m d → m ≤ n × UVarsIn m n T × UVarsInΔ m n Δ`. proved
- `scope⇐ : SolvedCtx Γ → SolvedTy T → (d : … ⇐ …) → GuessIn m d → m ≤ n × UVarsInΔ m n Δ`. proved
- `mobCx⇒solvedΔ : (γ : Struct N) → SolvedCtx Γ → MobCx Γ γ → SolvedΔ (allMobile Γ γ) σ`,
  `mobConstraints-solved : (𝓂 : Mob) (γ : Struct N) → SolvedCtx Γ → (𝓂 ≡ M → MobCx Γ γ) →
   SolvedΔ (mobConstraints 𝓂 Γ γ) σ` (A-Abs). proved
- `subTy-ctx-id : SolvedCtx Γ → subCtx Γ σ ≡ Γ`, `solvedΓ-of : SolvedCtx Γ → SolvedΓ Γ σ`,
  `solvedTm-K : SolvedTm (K c) → SolvedC c`, `solvedC-lsplit`, `solvedC-rsplit`,
  `subTm-id-solved = subTm-id`. proved

## Deviations from the task statement — READ BEFORE USING

1. **`scope` needs `GuessIn k d`, and the `SolvedTm e` argument is gone.**  The statement
   "`SolvedCtx Γ → SolvedTm e → d → m ≤ n × UVarsIn m n T × UVarsInΔ m n Δ`" is FALSE as written:
   two rules put a type into the conclusion that no premise determines.
   * `A-Const`: `⊢ c ∶ T` is a schema; `` `send ``/`` `recv `` carry an arbitrary `T`,
     `` `acq `` an arbitrary `s`, `` `select ``/`` `branch `` arbitrary `s₁ s₂`.  Nothing stops
     `T` from mentioning a variable that was never allocated.
   * `A-Ann` (⇐→⇒) makes the checked type an inferred one, and in checking mode the type is an
     input, so an inference can conclude any type at all.
   `GuessIn k d` is the (small) predicate that asks exactly these types to be in scope; it is a
   nested tuple of `UVarsIn` proofs, and for a derivation built from a SOLVED declarative
   derivation each component is `solved⇒uvarsIn _`.  Since `GuessIn` also carries the
   `A-LSplit`/`A-RSplit` obligation (the split type `s` of the constant), the `SolvedTm e`
   argument became unnecessary — and dropping it is what makes the A-Let case provable, because
   `SolvedTm` has no constructor for `` `let _ `in _ `` (`Algorithmic/Solved.agda`, outside this
   tree, has it commented out).
2. **Checking mode takes the input type's scope as a hypothesis** (`ScopeIn chk k m T =
   UVarsIn k m T`), and the conclusion is uniform: `UVarsIn k n T × UVarsInΔ k n Δ`.  This is the
   "`UVarsInΔ-with T`" of the task, in the form that composes: in `A-App` the checked type comes
   from the arrow inferred by the first premise, so its variables are in `[k, m′)`, and A-Check's
   `C-Eq T U` is then in `[k, n)`.  There is a window base `k ≤ m` so that the same statement
   serves the premises of a rule; `scope` instantiates `k := m`.
3. `UVarsIn`, `UVarsInC`, `UVarsInΓ` are DATA/RECORD types and `Agree` is a RECORD, never
   Set-valued functions.  With functions Agda cannot invert `UVarsIn m n ?t =?= UVarsIn m n T`
   (defined functions are not injective) and every use site leaves unsolved metas; this cost one
   rewrite of the module.  Consequence for callers: build `Agree` with `agree (λ α lo hi → …)`,
   read it with `ap≡`; build `UVarsInΓ` with `ctx (λ x → …)`, read it with `lookupΓ`.
4. `merge`, `merge₃` and their lemmas take `k` (and `k₁ k₂`) and the substitutions as EXPLICIT
   arguments, for the same inference reason (`UV.Sub` is a record with proof fields, so a σ that
   occurs only under `SolvedΔ`/`Solving` is not recoverable).

## Notes for other agents
- The three-way merge for A-Case is `merge₃ m₁ m₂ σ σ₁ σ₂` where `m₁`, `m₂` are the exit counters
  of the scrutinee and of the first branch; `solvedΔ-merge₃` wants `m₁ ≤ m₂ ≤ n`, all of which
  come out of `scope`.
- For A-LSplit/A-RSplit use `merge m (single (UV.fresh m) s′ ¬Ss′) σ-rest`: `single` puts `s′` on
  the freshly allocated `uvar ‼ m` (and `dual s′` on its ⁇-twin), `merge` at `suc m` keeps it.
- Nothing here imports anything from `Simulation/`; the only imports are core modules plus
  `BorrowedCF.Algorithmic` (for `subAll-solving`, reused rather than re-proved) and
  `Completeness/Base.agda` (for `SolvedCtx`).

## Discrepancies found between the tex rules and the Agda definitions
- None affecting this module.  The one modelling observation worth recording is the one above:
  the algorithmic system as mechanised has two rules (A-Const, A-Ann) whose conclusion type is
  not determined by the term and the premises, so "the algorithmic derivation only mentions
  variables it allocated" is a property of the derivations the completeness proof BUILDS, not of
  the judgment.

## Base-change log
- 2026-09-08, C6c: A-LetPair / A-Let gained an explicit first argument `(p/s : ParSeq)`.
  Adapted the four patterns (`GuessIn`, `scope-gen`); no statement changed — the scope
  invariant never inspects the structure `γ`.  All four modules re-checked, exit 0.
- 2026-09-08, C10: the ≼ premises now emit `Δ₀` (`Γ ∶ γ₁ ≼ γ₂ ↑ Δ₀`, `Context/SubConstraint.agda`),
  which is prepended to the output set of A-Var, A-Const, A-LSplit, A-RSplit, A-App, A-Seq,
  A-LetPair, A-Let, A-Case, A-Pair; A-Ann gained a first premise `ChkForm e`; A-Case takes
  `≤γ` instead of `JoinParSeq`.  Adapted, no exported statement changed.  NEW exported lemmas:
  * `uvarsInΔ-≈′↑ : UVarsInΓ m n Γ → Γ ∶ γ₁ ≈′ γ₂ ↑ Δ → UVarsInΔ m n Δ`. proved
  * `uvarsInΔ-≈↑ : UVarsInΓ m n Γ → Γ ∶ γ₁ ≈ γ₂ ↑ Δ → UVarsInΔ m n Δ`. proved
  * `uvarsInΔ-≼↑ : UVarsInΓ m n Γ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → UVarsInΔ m n Δ`. proved
    (only `∥′-tmˡ↑` / `∥′-tmʳ↑` emit anything, namely `allMobile Γ α`, so the scope of Δ₀ is
    the scope of the context; every other constructor emits `[]` or a concatenation.)
  `scope-gen` threads Δ₀ with `uvarsInΔ-++` in all ten rules.  All four modules re-checked, exit 0.
