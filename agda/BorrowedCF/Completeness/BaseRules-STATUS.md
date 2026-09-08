# C6 — base-rule extensions (Algorithmic.agda, Context/Join.agda)

Status: DONE (2026-09-08). Both base files type-check, with no new postulates and no holes.

## Task 1a — `select`/`branch` are algorithmic constants
`¬AlgConst` now has two constructors only:

    data ¬AlgConst : Const → Set where
      `lsplit : ¬AlgConst (`lsplit s)
      `rsplit : ¬AlgConst (`rsplit s)

`algConst?` returns `inj₁ λ()` for `` `select x `` and `` `branch ``.
`sound (A-Const ≤γ Ac ⊢c)` is unchanged (it only uses `subConst-⊢`), so
`K (`select i)` and `K `branch` are now inferred by A-Const from the declarative
constant typing. Justification: A-Const already covers `send`/`recv`/`acq`/`new`/`end`,
whose constant types are equally non-deterministic. Only `lsplit`/`rsplit` need the
dedicated A-LSplit/A-RSplit rules that invent a fresh unification variable for the
second component of the split. done

## Task 1b — A-Let (new rule, right after A-LetPair)

    A-Let :
      let open Fin.Patterns in
      let γ₁ = γ ∣fv[ e₁ ] in
      let γ₂ = γ ↓ fvClose (fv e₂) in
      (≤γ : Γ ∶ γ₁ ; γ₂ ≼ γ) →
      Γ ; γ₁ / m ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
      T ⸴ Γ ; ((` 0F) ; 𝐂.wk γ₂) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
      -----------------------------------------------------------
      Γ ; γ / m ⊢ `let e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

(all `;` in the rule are U+037E, not ASCII). done

## Task 1c — soundness case for A-Let

    sound (A-Let {T = T} {Δ₁ = Δ₁} ≤γ x y) SΓ SΔ =
      let p/s , join≼ = parOrSeq? ≤γ in
      T-Weaken (≼-map⁺ subTy-unr subTy-mobile join≼)
               (T-Let p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                          (T-Weaken (;-≼-join p/s) (T-Conv ≃-refl (x≤y⊔x _ _)
                            (sound y (solved-⸴ (subTy-solved T Sσ) SΓ) (All.++⁻ʳ Δ₁ SΔ)
                              ⊢≗ λ _ → refl))))

Went through exactly as given (the `;-≼-join p/s : Γ ∶ α ; β ≼ join p/s α β` bridges
`(` 0F) ; 𝐂.wk γ₂` to `join p/s (` zero) (𝐂.wk γ₂)`). done

## Task 2 — `parOrSeq?` is no longer a postulate (Context/Join.agda, end of file)

    parOrSeq? : Γ ∶ α ; β ≼ γ → Σ[ p/s ∈ ParSeq ] Γ ∶ join p/s α β ≼ γ
    parOrSeq? ≤γ = seq , ≤γ

`joinDir` for ParSeq is `biasedDir`, `biasedDir seq = L`, and `join` with `joinDir a = L`
is `_;_`, so `join seq α β` reduces to `α ; β` definitionally and the postulate was
trivially provable. done

## Checks run (agda-check, one at a time)
- BorrowedCF/Context/Join.agda — OK
- BorrowedCF/Algorithmic.agda — OK, zero goals, no postulate (the only `postulate` in the
  file is the commented-out `fv-wk` block, untouched)
- BorrowedCF/Completeness/Base.agda — OK
- BorrowedCF/Completeness/Weaken/Support.agda — OK (second importer of Algorithmic)
- BorrowedCF/Safety/Preservation.agda — OK (5m21s)
- BorrowedCF/Safety/Progress.agda — OK (6m12s)

Importers of `BorrowedCF.Algorithmic`: Completeness/Base.agda, Completeness/Weaken/Support.agda
(only these two). `Context.Join` is re-exported by `BorrowedCF.Context`, hence pulled in by
almost everything, so the two Safety top modules cover it.

---

# C6b — A-Case repair + `SolvedTm` let-constructor (Algorithmic.agda, Algorithmic/Solved.agda)

Status: DONE (2026-09-08). Both files type-check, zero goals, no new postulates.

## Task 1 — A-Case restricted the branches to the COMPLEMENT of the scrutinee

Old premise set (incomplete, refuted by `Completeness/Probe/CaseUnr.agda`): the branch
structure was `join p/s (` 0F) (𝐂.wk (γ ↓ ∁ (fv e)))`, so every variable of the scrutinee
was deleted from the branch structure. The declarative `T-Case` splits `γ` into `γ₁`
(scrutinee) and `γ₂` (both branches) and `T-Weaken` lets the two share an unrestricted
variable (`∥′-dup`), so a `u : `⊤` free in the scrutinee and in a branch had no algorithmic
derivation.

New rule (`;` and `⸴` are the U+037E / U+2E34 characters of the development):

    A-Case : (p/s : ParSeq) →
      let γ₂ = γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂)) in
      (≤γ : Γ ∶ join p/s (γ ∣fv[ e ]) γ₂ ≼ γ) →
      ∀ {ϵ ϵ₁ ϵ₂ T₁ T₂ Δ Δ₁ Δ₂} →
      Γ ; γ ∣fv[ e ] / m ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / m₁ →
      T₁ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) / m₁ ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
      T₂ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) / m₂ ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ / n  →
      ---------------------------------------------------------------------------------------
      Γ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ C-Eq U₁ U₂ ∷ Δ ++ Δ₁ ++ Δ₂ / n

The branch structure is now the restriction of `γ` to the branches' OWN free variables,
which is the same convention as A-App / A-Seq / A-LetPair / A-Let / A-Pair. The split
premise is the `≼` itself, not a `JoinParSeq`; this is `A-Case-gen` of Main-STATUS.md
FINDING 2 with `γ′` instantiated to `γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂))`. The old rule
is subsumed: the two sets `fv e` and `fvClose (fv e₁) ∪ fvClose (fv e₂)` may overlap, and
they need not cover `γ` (leftover variables are absorbed by `≼`). Arity and argument order
are unchanged (`A-Case p/s ≤γ x y₁ y₂`), so pattern matches keep working.

`JoinParSeq` and `join-joinParSeq` are LEFT IN PLACE (unused by the rule now, still exported
and used by `Completeness/Weaken.agda`). Nothing else in Algorithmic.agda changed.

## Task 1b — soundness case for A-Case

Only the binder name and the weakening argument changed; with the explicit premise the
T-Weaken step is direct:

    sound {Γ = Γ} {γ} (A-Case {e} {e₁} {e₂} p/s ≤γ {ϵ} {ϵ₁} {ϵ₂} {T₁} {T₂} {Δ} {Δ₁} {Δ₂} x y₁ y₂) SΓ (U≃ ∷ SΔ)
      using SΔ₁ , SΔ₂ ← All.++⁻ Δ₁ (All.++⁻ʳ Δ SΔ)
      using x′  ← sound x SΓ (All.++⁻ˡ Δ SΔ)
      using y₁′ ← sound y₁ (solved-⸴ (subTy-solved T₁ Sσ) SΓ) SΔ₁ ⊢≗ λ _ → refl
      using y₂′ ← sound y₂ (solved-⸴ (subTy-solved T₂ Sσ) SΓ) SΔ₂ ⊢≗ λ _ → refl
      =
      T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ) $
        T-Case p/s
          (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤x⊔y ϵ ϵ₁)) x′)
          (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤y⊔x ϵ ϵ₁)) y₁′)
          (T-Conv (≃-sym U≃) (x≤y⊔x _ ϵ₂) y₂′)

was `T-Weaken (≼-map⁺ subTy-unr subTy-mobile (join-joinParSeq j-p/s))`. The `T-Case` of
Terms/Base.agda concludes in `join p/s γ₁ γ₂`, which is exactly the left-hand side of the
new premise, so soundness needs no bridging lemma. done

## Task 2 — `SolvedTm` had no `let` constructor (Algorithmic/Solved.agda)

`data SolvedTm` covered every term former except `` `let_`in_ `` (a commented-out remnant
sat where the constructor belongs), so `SolvedTm e` was uninhabited for every let-term and
the completeness hypothesis silently excluded them. Added, in Tm-constructor order right
before the `let⊗` line:

    `let_`in_ : {e₁ : Tm n} {e₂ : Tm (1 + n)} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (`let e₁ `in e₂)

plus the two mirrored cases

    subTm-solved (`let e `in e₁) = `let subTm-solved e `in subTm-solved e₁
    subTm-id (`let e `in e₁) = cong₂ `let_`in_ (subTm-id e) (subTm-id e₁)

and deleted the stale comment `-- `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n`.
Nothing else in Solved.agda changed. done

## Checks run (agda-check, one at a time, all OK)
- BorrowedCF/Algorithmic.agda — OK (zero goals, only postulate is the commented-out `fv-wk`)
- BorrowedCF/Algorithmic/Solved.agda — OK
- BorrowedCF/Completeness/Base.agda — OK
- BorrowedCF/Completeness/Weaken/Support.agda — OK
- BorrowedCF/Completeness/Scope.agda — OK (pattern `A-Case p/s j d d₁ d₂` unaffected)
- BorrowedCF/Completeness/Weaken.agda — OK (its A-Case case now passes `≤γ` straight to
  `split-weaken-ps`; `mkJoinParSeq` is no longer needed there)

Importers of `BorrowedCF.Algorithmic` are more than the two recorded above: also
Completeness/Decl/Eff.agda, Completeness/Main/Base.agda, Completeness/Scope.agda,
Completeness/Scope/Merge.agda, Completeness/Scope/Smoke.agda, Completeness/Weaken.agda and
the two Probe modules. Probe/CaseUnr.agda is now STALE by construction: its `no-alg` matches
`A-Case par _ _ d₁ _` and derives `⊥` from the old branch structure, which the repair
removes. Checking it now fails with

    Probe/CaseUnr.agda:90.45-47: error: [UnequalTerms]
    (` 1F) != [] of type (Struct 2)
    when checking that the expression d₁ has type
    T₁ ⸴ Γ₀ ; (` 0F) ∥ [] / _ ⊢[ _ ] ` 1F ∶ _ ∣ _ ↑ _ / _

i.e. the branch structure is now `(` 0F) ∥ (` 1F)` and the shared unrestricted variable
survives, exactly as intended. The completeness agents C2/C3/C4 should target the new rule.

## C6c — A-LetPair and A-Let take a `p/s : ParSeq` (2026-09-08)

Fixes agent C7's open counterexample `Probe/LetPairPar.agda`. Both rules hard-wired a
sequential link between the bound components and the rest of the context, so a body that
uses an outer variable before a component had no algorithmic derivation while T-LetPair
with `p/s = par` typed it. Only `agda/BorrowedCF/Algorithmic.agda` changed, in six lines of
the rule block and in the two `sound` cases.

`p/s` is explicit and FIRST, like A-Case and A-Pair. The `≼` premise moved from
`γ₁ ; γ₂ ≼ γ` to `join p/s γ₁ γ₂ ≼ γ`, which is the exact left-hand side of the
declarative conclusion `Γ ; join p/s γ₁ γ₂ ⊢ ...`.

### Final rule texts (Algorithmic.agda, lines 194-212)

    A-LetPair : (p/s : ParSeq) →
      let open Fin.Patterns in
      let γ₁ = γ ∣fv[ e₁ ] in
      let γ₂ = γ ↓ fvClose* 2 (fv e₂) in
      (≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ) →
      Γ ; γ₁ / m ⊢ e₁ ⇒ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ₁ ↑ Δ₁ / m′ →
      T₁ ⸴ T₂ ⸴ Γ ; join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ₂)) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
      -----------------------------------------------------------------------------------
      Γ ; γ / m ⊢ `let⊗ e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

    A-Let : (p/s : ParSeq) →
      let open Fin.Patterns in
      let γ₁ = γ ∣fv[ e₁ ] in
      let γ₂ = γ ↓ fvClose (fv e₂) in
      (≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ) →
      Γ ; γ₁ / m ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
      T ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ₂) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
      -----------------------------------------------------------
      Γ ; γ / m ⊢ `let e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

(the `;` above stands for the U+037E semicolon of the judgment.)

### Changed soundness cases (Algorithmic.agda, lines 327-338)

Neither case needs `parOrSeq?` or `;-≼-join` any more. The rule's own `p/s` goes straight
into `T-LetPair` / `T-Let`, the premise `≤γ` is the T-Weaken witness, and the body
derivation keeps its `⊢≗ λ _ → refl` for the context mapping.

    sound (A-LetPair {T₁ = T₁} {T₂ = T₂} {Δ₁ = Δ₁} p/s ≤γ x y) SΓ SΔ =
      T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
               (T-LetPair p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                              (T-Conv ≃-refl (x≤y⊔x _ _)
                                (sound y (solved-⸴ (subTy-solved T₁ Sσ) (solved-⸴ (subTy-solved T₂ Sσ) SΓ)) (All.++⁻ʳ Δ₁ SΔ)
                                  ⊢≗ λ _ → refl)))
    sound (A-Let {T = T} {Δ₁ = Δ₁} p/s ≤γ x y) SΓ SΔ =
      T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
               (T-Let p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                          (T-Conv ≃-refl (x≤y⊔x _ _)
                            (sound y (solved-⸴ (subTy-solved T Sσ) SΓ) (All.++⁻ʳ Δ₁ SΔ)
                              ⊢≗ λ _ → refl)))

### Checks (agda-check, one at a time)

- BorrowedCF/Algorithmic.agda — OK, zero goals, no new postulate (the only `postulate`
  keyword in the file is inside the commented-out `fv-wk` block at line 75).
- BorrowedCF/Completeness/Base.agda — OK, unaffected.
- BorrowedCF/Completeness/Weaken.agda — OK. Its `alg-weaken-box` already matched
  `A-LetPair {d = d} p/s ≤γ x y` and `A-Let p/s ≤γ x y` and fed `split-weaken-ps p/s`, so
  it was written against the generalised rule and now agrees with it.
- BorrowedCF/Completeness/Weaken/Instance.agda — OK.
- BorrowedCF/Completeness/Split.agda, Sub.agda, Decl.agda — OK (mention the rules only in
  comments).
- BorrowedCF/Completeness/Scope.agda — BREAKS. Four patterns miss the new argument, at
  lines 106 and 107 (`GuessIn k (A-LetPair ≤γ d₁ d₂)`, `GuessIn k (A-Let ≤γ d₁ d₂)`) and
  154 and 161 (`scope-gen (A-LetPair ≤γ d₁ d₂) ...`, `scope-gen (A-Let ≤γ d₁ d₂) ...`).
  Error `[WrongNumberOfConstructorArguments] ... expects 16 arguments ... given 15`. Fix is
  `A-LetPair p/s ≤γ d₁ d₂` and `A-Let p/s ≤γ d₁ d₂`. Owner C2.
- BorrowedCF/Completeness/Probe/LetPairPar.agda — BREAKS at line 143 for the same reason.
  That is the counterexample this repair closes, so the module has to be retired or turned
  into a positive test the way Probe/CaseUnr.agda was. Owner C7.
- BorrowedCF/Completeness/Main/Interface.agda — breaks only through its import of
  Scope.agda. Its `Rules` fields `A-Let-gen` and `A-LetPair-gen` (lines 78-93) now state
  exactly the new constructors, so they can be discharged by `A-Let` and `A-LetPair`
  themselves. Everything else under Main/ and Scope/Smoke.agda inherits the Scope.agda
  failure.


# C10 — constraint-generating subcontext premises + restricted A-Ann (2026-09-08)

Status: DONE. `Context/SubConstraint.agda` (new), `Algorithmic.agda`,
`Completeness/Sub.agda`, `Completeness/Sub/Base.agda` all type-check with
`agda-check`, zero goals, zero unsolved metas, no new postulate. `Sub/Probe.agda`
type-checks UNCHANGED, so the four probe obligations pin down the rule shapes.

## 1. New base module `BorrowedCF/Context/SubConstraint.agda`

Imports `Prelude`, `Context`, `Context.Base` (Variables), `Context.Domain` (`_↓_`),
`Types`, `Types.Unification`, `Algorithmic.Solved`. It does NOT import `Algorithmic`
(dependency direction: `Algorithmic.Solved` only needs `Context.Base`), and
`Algorithmic.agda` now does `open import BorrowedCF.Context.SubConstraint public`,
so every consumer of `allMobile` / `mobConstraints⇒MobCx` through `Algorithmic`
(`Completeness/Scope.agda`, `Completeness/Weaken/Support.agda`,
`Completeness/Main/Base.agda`) keeps working unchanged.

Exports (all moved verbatim, names/constructors/fixities unchanged):

| name | origin |
|---|---|
| `allMobile : Ctx n → Struct n → List Constraint` | was `Algorithmic.agda` |
| `_∶_≈′_↑_` (10 constructors, incl. `∥′-tmˡ↑` / `∥′-tmʳ↑`) | was `Completeness/Sub.agda` |
| `_∶_≈_↑_` (`ε↑`, `_◅ᶠ_`, `_◅ᵇ_`) | was `Completeness/Sub.agda` |
| `_∶_≼_↑_` (`≼-refl↑`, `≼-∅↑`, `≼-wk↑`, `≼-trans↑`, `≼-cong-sq↑`, `≼-cong-par↑`) | was `Completeness/Sub.agda` |
| `JoinParSeq↑` (`par↑`, `seq↑`), `join-joinParSeq↑` | was `Completeness/Sub.agda` |
| `unrCx-sub : UnrCx Γ α → UnrCx (subCtx Γ σ) α` | was `Completeness/Sub/Base.agda` |
| `mobConstraints⇒MobCx` | was `Algorithmic.agda` (same argument order: `mobConstraints⇒MobCx Sσ Γ γ SΔ`) |
| `≈′↑-sound`, `≈↑-sound`, `≼↑-sound`, `≼↑-sound-++` | was `Completeness/Sub.agda` |
| fixities `infix 4 _∶_≈′_↑_ _∶_≈_↑_ _∶_≼_↑_`, `infixr 5 _◅ᶠ_ _◅ᵇ_` | unchanged |

Everything else stays in `Completeness/Sub.agda`, which now opens SubConstraint
`public`: the derived laws (`transmuteˡ↑`, `sq-commMobˡ↑`, `sq-≼-par↑`, `≼-join↑`,
`parOrSeq?↑`, …), `≈↑-cast` / `≼↑-cast`, `≼↑-complete`, `≼↑-complete-solved`,
`MobHolds`, `≼⇒≼↑`, `≼↑-erase`. `Completeness/Sub/Base.agda` now imports
`allMobile` from `Context.SubConstraint` and no longer defines `unrCx-sub`.

## 2. The nine changed rules of `Algorithmic.agda` (final text)

`private variable Δ₀ : CSet` was added next to the judgment.

```

data _;_/_⊢[_]_∶_∣_↑_/_ Γ γ m where
  A-Var : ∀ {x} →
    (≤γ : Γ ∶ ` x ≼ γ ↑ Δ₀) →
    ----------------------------------
    Γ ; γ / m ⊢ ` x ⇒ Γ ﹫ x ∣ ℙ ↑ Δ₀ / m

  A-Const : ∀ {c} →
    (≤γ : Γ ∶ [] ≼ γ ↑ Δ₀) →
    (Ac : AlgConst c) →
    ⊢ c ∶ T →
    --------------------------------
    Γ ; γ / m ⊢ K c ⇒ T ∣ ℙ ↑ Δ₀ / m

  A-LSplit :
    let α = UV.fresh m in
    (≤γ : Γ ∶ [] ≼ γ ↑ Δ₀) →
    (¬skips : ¬ Skips s) →      -- NEW: the first component of a split must do real work
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`lsplit s) ⇒ ⟨ s ; `` α ⟩ →*M ⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩ ∣ ℙ ∣ ℙ ↑ Δ₀ / suc m

  A-RSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ ↑ Δ₀) →
    (¬skips : ¬ Skips s) →      -- NEW: the first component of a split must do real work
    -----------------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`rsplit s) ⇒ ⟨ s ; `` α ⟩ →*M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; `` α ⟩ ∣ ℙ ∣ ℙ ↑ Δ₀ / suc m

  A-App :
    EffCompat (Arr.dir a) ϵ₂ ϵ₁ →
    (≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ ↑ Δ₀) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ / n →
    --------------------------------------------------------------
    Γ ; γ / m ⊢ e₁ ·⟨ Arr.dir a ⟩ e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a ↑ Δ₀ ++ Δ₁ ++ Δ₂ / n

  A-Seq :
    Unr T →
    (≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ ↑ Δ₀) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n  →
    -------------------------------------------------
    Γ ; γ / m ⊢ e₁ ; e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₀ ++ Δ₁ ++ Δ₂ / n

  A-LetPair : (p/s : ParSeq) →
    let open Fin.Patterns in
    let γ₁ = γ ∣fv[ e₁ ] in
    let γ₂ = γ ↓ fvClose* 2 (fv e₂) in
    (≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ ↑ Δ₀) →
    Γ ; γ₁ / m ⊢ e₁ ⇒ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ₁ ↑ Δ₁ / m′ →
    T₁ ⸴ T₂ ⸴ Γ ; join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ₂)) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ `let⊗ e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₀ ++ Δ₁ ++ Δ₂ / n

  A-Let : (p/s : ParSeq) →
    let open Fin.Patterns in
    let γ₁ = γ ∣fv[ e₁ ] in
    let γ₂ = γ ↓ fvClose (fv e₂) in
    (≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ ↑ Δ₀) →
    Γ ; γ₁ / m ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    T ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ₂) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
    -----------------------------------------------------------
    Γ ; γ / m ⊢ `let e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₀ ++ Δ₁ ++ Δ₂ / n

  A-Case : (p/s : ParSeq) →
    let γ₂ = γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂)) in
    (≤γ : Γ ∶ join p/s (γ ∣fv[ e ]) γ₂ ≼ γ ↑ Δ₀) →
    ∀ {ϵ ϵ₁ ϵ₂ T₁ T₂ Δ Δ₁ Δ₂} →
    Γ ; γ ∣fv[ e ] / m ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / m₁ →
    T₁ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) / m₁ ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
    T₂ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) / m₂ ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ / n  →
    ---------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ C-Eq U₁ U₂ ∷ Δ₀ ++ Δ ++ Δ₁ ++ Δ₂ / n

  A-Abs :
    (Arr.Unr a → UnrCx Γ γ) →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) / m ⊢ e ⇐ U ∣ ϵ ↑ Δ / n →
    Δ′ ≡ mobConstraints (Arr.mob a) Γ γ →
    --------------------------------------------------------------------
    Γ ; γ / m ⊢ ƛ e ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ′ ++ Δ / n

  A-AbsRec :
    let open Fin.Patterns in
    UnrCx Γ γ →
    Arr.Unr a →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) / m ⊢ e ⇐ U ∣ ϵ ↑ Δ / n →
    ------------------------------------------------------------------------------
    Γ ; γ / m ⊢ μ (ƛ e) ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ / n

  A-Pair :
    ∀ (p/s : ParSeq) {ϵ₁ ϵ₂} →
    (≤γ : Γ ∶ join p/s (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ ↑ Δ₀) →
    (seq⇒pure : p/s ≡ seq → ϵ₂ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇐ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ U ∣ ϵ₂ ↑ Δ₂ / n  →
    ----------------------------------------------------------------------
    Γ ; γ / m ⊢ e₁ ⊗ e₂ ⇐ T ⊗⟨ biasedDir p/s ⟩ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₀ ++ Δ₁ ++ Δ₂ / n

  A-Inj : ∀ {i} →
    Γ ; γ / m ⊢ e ⇐ if i then T₁ else T₂ ∣ ϵ ↑ Δ / n →
    --------------------------------------------------
    Γ ; γ / m ⊢ `inj i e ⇐ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / n

  A-Check :
    Γ ; γ / m ⊢ e ⇒ U ∣ ϵ ↑ Δ / n →
    ---------------------------------------
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ C-Eq T U ∷ Δ / n

  A-Ann :
    ChkForm e →
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n →
    -------------------------------
    Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n
```

## 3. `sound` (final text of the changed module body)

`≼-map⁺ subTy-unr subTy-mobile ≤γ` is gone from all nine cases; A-Var / A-Const /
A-LSplit / A-RSplit pass `SΔ` directly (their whole output set is `Δ₀`), the binary
rules split with `All.++⁻ˡ Δ₀ SΔ` / `All.++⁻ʳ Δ₀ SΔ`, A-Case first strips the leading
`C-Eq U₁ U₂` and then `Δ₀`.

```
  sound {Γ = Γ} (A-Var ≤γ) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ SΔ ≤γ)
             (T-Var _ (V.lookup-map _ (λ t → subTy t σ) Γ))
  sound (A-Const ≤γ Ac ⊢c) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ SΔ ≤γ)
             (T-Const (subConst-⊢ ⊢c))
  sound (A-LSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ SΔ ≤γ)
             (T-Const (`lsplit _ _ (¬skips ∘ subTy-skips⁻¹) (UV.ap-¬skips σ _ ∘ skips-⋯ᵣ⁻¹)))
  sound (A-RSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ SΔ ≤γ)
             (T-Const (`rsplit _ _ (¬skips ∘ subTy-skips⁻¹) (UV.ap-¬skips σ _ ∘ skips-⋯ᵣ⁻¹)))
  sound (A-App {Δ₀ = Δ₀} {Δ₁ = Δ₁} ec ≤γ x y) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)
             (sound-app ec x y SΓ (All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ)) (All.++⁻ʳ Δ₁ (All.++⁻ʳ Δ₀ SΔ)))
  sound (A-Seq {Δ₀ = Δ₀} {Δ₁ = Δ₁} unr-T ≤γ x y) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)
             (T-Seq (subTy-unr unr-T)
                    (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ))))
                    (T-Conv ≃-refl (x≤y⊔x _ _) (sound y SΓ (All.++⁻ʳ Δ₁ (All.++⁻ʳ Δ₀ SΔ)))))
  sound (A-LetPair {Δ₀ = Δ₀} {T₁ = T₁} {T₂ = T₂} {Δ₁ = Δ₁} p/s ≤γ x y) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)
             (T-LetPair p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ))))
                            (T-Conv ≃-refl (x≤y⊔x _ _)
                              (sound y (solved-⸴ (subTy-solved T₁ Sσ) (solved-⸴ (subTy-solved T₂ Sσ) SΓ)) (All.++⁻ʳ Δ₁ (All.++⁻ʳ Δ₀ SΔ))
                                ⊢≗ λ _ → refl)))
  sound (A-Let {Δ₀ = Δ₀} {T = T} {Δ₁ = Δ₁} p/s ≤γ x y) SΓ SΔ =
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)
             (T-Let p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ))))
                        (T-Conv ≃-refl (x≤y⊔x _ _)
                          (sound y (solved-⸴ (subTy-solved T Sσ) SΓ) (All.++⁻ʳ Δ₁ (All.++⁻ʳ Δ₀ SΔ))
                            ⊢≗ λ _ → refl)))
  sound {Γ = Γ} {γ} (A-Case {Δ₀ = Δ₀} p/s ≤γ {ϵ} {ϵ₁} {ϵ₂} {T₁} {T₂} {Δ} {Δ₁} {Δ₂} x y₁ y₂) SΓ (U≃ ∷ SΔ′)
    using SΔ ← All.++⁻ʳ Δ₀ SΔ′
    using SΔ₁ , SΔ₂ ← All.++⁻ Δ₁ (All.++⁻ʳ Δ SΔ)
    using x′  ← sound x SΓ (All.++⁻ˡ Δ SΔ)
    using y₁′ ← sound y₁ (solved-⸴ (subTy-solved T₁ Sσ) SΓ) SΔ₁ ⊢≗ λ _ → refl
    using y₂′ ← sound y₂ (solved-⸴ (subTy-solved T₂ Sσ) SΓ) SΔ₂ ⊢≗ λ _ → refl
    =
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ′) ≤γ) $
      T-Case p/s
        (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤x⊔y ϵ ϵ₁)) x′)
        (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤y⊔x ϵ ϵ₁)) y₁′)
        (T-Conv (≃-sym U≃) (x≤y⊔x _ ϵ₂) y₂′)
  sound {Γ = Γ} {γ = γ} (A-Abs {T = T}{Δ′ = Δ′} unr-Γ ϵ≤ x refl) SΓ SΔ =
    T-Abs (allCx-map⁺ subTy-unr ∘ unr-Γ) (λ{ refl → mobConstraints⇒MobCx Sσ Γ γ (All.++⁻ˡ Δ′ SΔ) })
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ (subTy-solved T Sσ) SΓ) (All.++⁻ʳ Δ′ SΔ) ⊢≗ λ _ → refl
  sound {Γ = Γ} (A-AbsRec {T = T} {U = U} unr-Γ unr-a ϵ≤ x) SΓ SΔ =
    let open Fin.Patterns in
    let T′  = subTy-solved T Sσ in
    let T→U = T′ ⟨ _ ⟩→ subTy-solved U Sσ in
    T-AbsRec (allCx-map⁺ subTy-unr unr-Γ) unr-a
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ T′ (solved-⸴ T→U SΓ)) SΔ ⊢≗ λ where
          0F → refl
          1F → refl
          (suc (suc k)) → refl
  sound (A-Pair {Δ₀ = Δ₀} {Δ₁ = Δ₁} p/s {ϵ₁} {ϵ₂} ≤γ seq⇒pure x y) SΓ SΔ =
    let _ , _ , ≤ϵ₁ , ≤ϵ₂ , ≤ϵ⊔ , S⇒P = mk-seq⇒pure seq⇒pure in
    T-Weaken (≼↑-sound Sσ (All.++⁻ˡ Δ₀ SΔ) ≤γ)
      $ T-Conv ≃-refl ≤ϵ⊔
      $ T-Pair p/s S⇒P
          (T-Conv ≃-refl ≤ϵ₁ (sound x SΓ (All.++⁻ˡ Δ₁ (All.++⁻ʳ Δ₀ SΔ))))
          (T-Conv ≃-refl ≤ϵ₂ (sound y SΓ (All.++⁻ʳ Δ₁ (All.++⁻ʳ Δ₀ SΔ))))
  sound (A-Inj {i = i} x) SΓ SΔ =
    T-Inj
      $ subst (_ ; _ ⊢ _ ∶_∣ _) (if-float (flip subTy σ) i)
      $ sound x SΓ SΔ
  sound (A-Ann _ x) SΓ SΔ =
    sound x SΓ SΔ
  sound (A-Check x) SΓ (eq ∷ SΔ) =
    T-Conv (≃-sym eq) ≤ϵ-refl
      $ sound x SΓ SΔ
```

Two notes on the patterns: `Δ₀` must be given as the FIRST named implicit
(`A-LetPair {Δ₀ = Δ₀} {T₁ = T₁} …`), because named implicit patterns have to follow
telescope order and `≤γ` precedes the premise that mentions `T₁`; and `A-Case` binds
its constraint sets as `SΓ (U≃ ∷ SΔ′)` with `SΔ ← All.++⁻ʳ Δ₀ SΔ′`.

## 4. A-Ann restricted to the checking forms (coordinator addendum)

New base predicate, right before the judgment:

```
data ChkForm {n} : Tm n → Set where
  chk-ƛ   : ∀ {e}     → ChkForm (ƛ e)
  chk-μ   : ∀ {e}     → ChkForm (μ e)
  chk-⊗   : ∀ {e₁ e₂} → ChkForm (e₁ ⊗ e₂)
  chk-inj : ∀ {i e}   → ChkForm (`inj i e)
```

and the rule

```
  A-Ann :
    ChkForm e →
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n →
    -------------------------------
    Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n
```

`sound (A-Ann _ x) SΓ SΔ = sound x SΓ SΔ` (the premise is ignored). With the
restriction every A-Ann step sits at a term the paper's algorithm annotates anyway
(λ, μ, pair, injection), so completeness against the mechanised relation is
completeness against the paper's algorithm with annotations inserted exactly there.
Before the change A-Ann could re-type ANY subterm at a guessed type, e.g. an
application `K (`rsplit s) ·⟨ d ⟩ e` at its fully solved pair type, which the paper's
A-Annot cannot do (agent C7).

## 5. Left alone

* `JoinParSeq` / `join-joinParSeq` (the un-indexed A-Case premise) are now DEAD in
  `Algorithmic.agda` — A-Case carries the `≼ ↑ Δ₀` premise directly, as instructed,
  and `JoinParSeq↑` is not used by the rules either. Both are KEPT, because
  `Completeness/Split.agda` still does `open import BorrowedCF.Algorithmic using
  (JoinParSeq; par; seq)`; deleting them would break a module owned by another agent.
* `Context/Subcontext.agda`'s `postulate _∶_≼?_ : Bin.Decidable (Γ ∶_≼_)` is
  untouched (out of scope). IT MUST BECOME A PROCEDURE THAT RETURNS THE CONSTRAINT
  SET, i.e. of the shape
  `_∶_≼?_↑ : (Γ : Ctx n) (γ₁ γ₂ : Struct n) → Dec (Σ[ Δ ∈ CSet ] Γ ∶ γ₁ ≼ γ₂ ↑ Δ)`,
  demanding `Mobile` of as few variables as possible; otherwise the decision
  procedure still performs the mobility checks the rules now only record.

## 6. Checks (agda-check, one at a time)

| module | result |
|---|---|
| `BorrowedCF/Context/SubConstraint.agda` | OK |
| `BorrowedCF/Algorithmic.agda` | OK, zero goals, no new postulate |
| `BorrowedCF/Completeness/Sub.agda` (+ `Sub/Base.agda`) | OK |
| `BorrowedCF/Completeness/Sub/Probe.agda` | OK, source unchanged |
| `BorrowedCF/Completeness/Base.agda` | OK |
| `BorrowedCF/Completeness/Split.agda`, `Decl.agda`, `Main/Base.agda` | OK (unaffected) |
| `BorrowedCF/Completeness/Scope.agda` | BREAKS: `Scope.agda:114` `GuessIn k (A-Ann d)` — "constructor A-Ann expects 7 arguments, given 6" (the new `ChkForm` premise). That is only the FIRST error; the scope lemmas over the output sets also have to account for the new `Δ₀` (`A-Var` now outputs `Δ₀`, the binary rules `Δ₀ ++ Δ₁ ++ Δ₂`). Fix: `A-Ann _ d`, and a `UVarsInΔ Δ₀` obligation carried by the `≼ ↑ Δ₀` premise. |
| `BorrowedCF/Completeness/Weaken.agda` | BREAKS: `Weaken.agda:154` `alg-weaken-box lin w (A-Var ≤γ) = _ , A-Var (≼-trans ≤γ w) , …` — `≼-trans` produces `Γ ∶ α ≼ γ`, the rule now wants `Γ ∶ ` x ≼ γ₂ ↑ Δ₀`. All nine cases need `≼-trans↑` (from `Context.SubConstraint`) and a `Transfer` that accounts for the extra `Δ₀ ++ Δ₀′`. |
| `BorrowedCF/Completeness/Weaken/Instance.agda` | BREAKS via `Weaken.agda` (same error). |
| `BorrowedCF/Completeness/Main.agda`, `Main/{Simple,Abs,App,Bin,Bind,Struct,Transfer,Interface}.agda` | BREAK via `Scope.agda:114` only; no error of their own was reached. |

Owners C2/C3/C4 to re-target (per orchestrator); C10 edited none of them.

# C11 — `SolvedC` was missing `discard`/`select`/`branch` (Algorithmic/Solved.agda, 2026-09-08)

Status: DONE. Only `agda/BorrowedCF/Algorithmic/Solved.agda` was edited; nothing under
`Completeness/` broke.

## The gap

`data SolvedC : Const → Set` had no constructor for `` `discard ``, `` `select k `` or
`` `branch ``, so `SolvedTm (K c)` was UNINHABITED for those three constants. Every
completeness theorem whose hypothesis is `SolvedTm e` therefore silently excluded each
term containing a discard, a selection or a branch, even though `algConst?` puts all
three in `inj₁` (C6) and `A-Const` infers them.

## Added constructors (Solved.agda, after `` `rsplit ``)

    `discard : SolvedC `discard
    `select : ∀ {k} → SolvedC (`select k)
    `branch : SolvedC `branch

`` `select ``'s index is a `Bool` (`` `select : Bool → Const ``, Terms/Base.agda:21;
`Side` is the same type, renamed from `Data.Bool`), and no `k`/`i` variable is in scope
in Solved.agda, so the index is bound by an explicit `∀ {k}`.

## Added function cases

`subConst` already had all three constants (lines 227-229), so only the two lemmas that
match on `SolvedC` needed cases:

    subConst-solved `discard = `discard
    subConst-solved `select  = `select
    subConst-solved `branch  = `branch

    subConst-id `discard = refl
    subConst-id `select  = refl
    subConst-id `branch  = refl

`subConst-⊢` already covered the three constants and matches on the typing derivation,
not on `SolvedC`, so it is untouched.

## Checks (agda-check, one at a time, all OK, zero goals, no new postulate)

| module | result |
|---|---|
| `BorrowedCF/Algorithmic/Solved.agda` | OK |
| `BorrowedCF/Algorithmic.agda` | OK |
| `BorrowedCF/Completeness/Base.agda` | OK |
| `BorrowedCF/Completeness/Scope.agda` | OK (`solvedTm-K`, `solvedC-lsplit`, `solvedC-rsplit` unaffected: they match on one constructor each, not exhaustively) |
| `BorrowedCF/Completeness/Decl.agda` | OK (the `solvedTm-*` inversions in `Decl/Solved.agda` all match a single constructor) |
| `BorrowedCF/Completeness.agda` | OK (full theorem, whole tree) |

## Coverage note

`const-case` (Main/Simple.agda:52) dispatches on `algConst? c`; the three constants fall
into the `inj₁ Ac` branch, which builds `A-Const (der Lft) Ac (… subConst-⊢ ⊢c)`. So the
new `SolvedC` constructors make the completeness theorem apply to those terms and the
existing proof discharges them with no further case.
