# Annotation campaign, agent C1: completeness foundations + periphery

Owner: C1. Files: everything under BorrowedCF/Completeness/ except Main/ and
Completeness.agda (agent C2). Completeness/Main.agda (the main induction, parametrised
over Main/App and Main/Bind) was NOT touched either; it belongs with Main/.

## Plan / ticks
- [x] Base.agda: `data _⊑_`, `⊑-refl`, `fv-⊑`; Complete⇐ / Complete⇒ restated; module comment
- [x] Scope.agda: `GuessIn` and `scope-gen` A-Ann clauses drop `cf`
- [x] Weaken.agda: `alg-weaken-box` A-Ann clause drops `cf`
- [x] Weaken.agda: A-RSplit clause drops `¬skips` (pre-existing breakage from rsplit commit 469f079)
- [x] Decl.agda: `T-Ann` clauses in `fv⊆dom`, `fv-cover′`, `restrict`
- [x] Decl/Solved.agda: new `solvedTm-⦂ : SolvedTm (e ⦂ T) → SolvedTm e × SolvedTy T`
- [x] Scope/Smoke.agda: removed `single-use` (upstream 469f079 deleted `single`/`single-solving`/`single-ap`)
- [x] Split*, Sub*, Weaken/*, Scope/*, Decl/*: swept, no further Tm / fv / subTm / SolvedTm case splits
- [x] Probes adjusted: CaseUnr, LetPairPar, LinNeeded, MobUvarWF
- [ ] Probe/MobUvar.agda: NOT adjusted, see below
- [x] Reconnaissance: Main/Interface.agda

No holes, pragmas or postulates added.

## `_⊑_` (verbatim, Base.agda)

```agda
infix 4 _⊑_

data _⊑_ {n : ℕ} : Tm n → Tm n → Set where
  ⊑-var  : ∀ {x} → ` x ⊑ ` x
  ⊑-K    : ∀ {c} → K c ⊑ K c
  ⊑-ƛ    : ∀ {e ê} → e ⊑ ê → ƛ e ⊑ ƛ ê
  ⊑-μ    : ∀ {e ê} → e ⊑ ê → μ e ⊑ μ ê
  ⊑-app  : ∀ {e₁ ê₁ e₂ ê₂} d → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → e₁ ·⟨ d ⟩ e₂ ⊑ ê₁ ·⟨ d ⟩ ê₂
  ⊑-seq  : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → (e₁ ; e₂) ⊑ (ê₁ ; ê₂)
  ⊑-⊗    : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → e₁ ⊗ e₂ ⊑ ê₁ ⊗ ê₂
  ⊑-let  : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → `let e₁ `in e₂ ⊑ `let ê₁ `in ê₂
  ⊑-let⊗ : ∀ {e₁ ê₁ e₂ ê₂} → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ → `let⊗ e₁ `in e₂ ⊑ `let⊗ ê₁ `in ê₂
  ⊑-inj  : ∀ {e ê} i → e ⊑ ê → `inj i e ⊑ `inj i ê
  ⊑-case : ∀ {e ê e₁ ê₁ e₂ ê₂} → e ⊑ ê → e₁ ⊑ ê₁ → e₂ ⊑ ê₂ →
           `case e `of⟨ e₁ ; e₂ ⟩ ⊑ `case ê `of⟨ ê₁ ; ê₂ ⟩
  ⊑-⦂    : ∀ {e ê} → e ⊑ ê → ∀ T → (e ⦂ T) ⊑ (ê ⦂ T)
  ann    : ∀ {e ê} → e ⊑ ê → ∀ T → e ⊑ (ê ⦂ T)

⊑-refl : ∀ {n} {e : Tm n} → e ⊑ e
fv-⊑ : ∀ {n} {e ê : Tm n} → e ⊑ ê → fv ê ≡ fv e
```

(All `;` in code are U+037E.) Base.agda now imports `Data.Fin.Subset using (_∪_)`.

## New statements (verbatim)

```agda
Complete⇐ : Set
Complete⇐ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê ×
    (Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
      Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ ê ⇐ T ∣ ϵ′ ↑ Δ / k))

Complete⇒ : Set
Complete⇒ = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê ×
    (Σ[ T̂ ∈ 𝕋 ] Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
      Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (subTy T̂ σ ≃ T) × (Γ ; γ / m ⊢ ê ⇒ T̂ ∣ ϵ′ ↑ Δ / k))
```

Tuple shape of a result: `ê , ê⊑ , ϵ′ , Δ , k , σ , Sσ , SΔ , ϵ′≤ , der` (⇐) and
`ê , ê⊑ , T̂ , ϵ′ , Δ , k , σ , Sσ , SΔ , ϵ′≤ , T≃ , der` (⇒).

## Probes

| probe | change | still proves its header? |
|---|---|---|
| CaseUnr | derivation types `ê₀ = case ((inj L u) ⦂ (⊤ ⊕ ⊤)) of …`, `e₀⊑ê₀` added; ≼ premises lifted to `≼↑` via `↑′ d = proj₁ (proj₂ (≼⇒≼↑ d))` (Δ computes to []) | yes, Δ₀ unchanged |
| LetPairPar | derivation types `ê₀ = let⊗ p in ((z ⊗ c₀) ⦂ T₀)`, `e₀⊑ê₀`; `↑′` lifting | yes, Δ₀ unchanged |
| LinNeeded | `count-≈′↑`, `count-≈↑`, `count-≼↑-eq` (count invariant for `≼↑`); `var-≼`/`no-alg` now quantify over every `ê` with `e₀ ⊑ ê` (`bad-⊑` transports `γ₀ ↓ fv ê` with `fv-⊑`); `Complete⇐-noLin` restated in the ⊑ form | yes, and stronger: no annotation placement rescues the term |
| MobUvarWF | `lsplit`/`rsplit` constant typings get the new `Local` arguments (`local-ret`, `local-end`); `alg-rsplit` types `eRsplit ⦂ (Tx₁ ⊗¹ Tx₂)`; `retype` now produces `(e ⦂ G)` | yes; the escape now needs a source annotation, which `Complete⇐` lets the proof insert, so the instance is still not a counterexample to the Agda statement |
| UnrReflect | none needed | yes |
| MobUvar | NOT changed, does not check | NO, see below |

Probe/MobUvar.agda is meaningless since the rsplit relaxation (commit 469f079), not because of
annotations: its instance splits `⟨ !Unit ; (acq ; end‼) ⟩` with `lsplit`, and `` `lsplit `` now
requires `Local s′` for `s′ = acq ; end ‼`, which is `NonLocal` (constructor `acq ;₁-`). The term
is no longer declaratively typable, so the counterexample is gone. The file fails at line 105
(`` `lsplit t₁ t₂ ¬skips-t₁ ¬skips-t₂ `` lacks the `Local` argument, which cannot be supplied).
MobUvarWF.agda is its well-formed replacement and checks. Left in place, not deleted.

## Verification (agda-check, exit codes)

| file | exit |
|---|---|
| Base | 0 |
| Decl, Decl/Eff, Decl/Solved, Decl/Subsets | 0 |
| Scope, Scope/Base, Scope/Merge, Scope/Smoke | 0 |
| Weaken, Weaken/Support, Weaken/Instance, Weaken/Smoke | 0 |
| Split, Split/Absorb, Split/Base, Split/Construct, Split/Extract, Split/Lin, Split/Order, Split/Smoke | 0 |
| Sub, Sub/Base, Sub/Probe | 0 |
| Probe/CaseUnr, Probe/LetPairPar, Probe/LinNeeded, Probe/MobUvarWF, Probe/UnrReflect | 0 |
| Probe/MobUvar | 42 (pre-existing, see above) |

## Reconnaissance for C2

`agda-check BorrowedCF/Completeness/Main/Interface.agda`: exit 0 (no error). Interface does not
depend on the A-Ann shape or the Complete⇐/⇒ statements as they stand. Known remaining
`A-Ann cf …` sites (two-argument form, must become `A-Ann …` and type `e ⦂ T`):
Main/Abs.agda:77,114; Main/Struct.agda:104,129,154.
