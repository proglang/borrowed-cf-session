# C3 — algorithmic weakening (`alg-weaken`) — STATUS

Owner: agent C3.  Files: `Completeness/Weaken.agda`, `Completeness/Weaken/{Support,Instance,Smoke}.agda`.
Checked with `agda-check` only (the Agda MCP server refused to connect this session:
protocol version 2025-11-25 vs the server's 2025-06-18).

**DONE (restated for C10).**  All delivered lemmas type-check with zero goals, zero
unsolved metas, zero postulates, and `Weaken/Instance.agda` is FULLY INSTANTIATED with
agent C1's `Completeness/Split.agda` — no module parameters and no assumptions are left.

C4 and anyone else: `open import BorrowedCF.Completeness.Weaken.Instance using (alg-weaken)`.

```agda
alg-weaken :
  ∀ {σ : UV.Sub} → Solving σ →
  ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {m k : ℕ} {ξ : Mode}
    {e : Tm n} {T : 𝕋} {ϵ : Eff} {Δ : CSet} →
  Approx Γ̂ Γ σ →                      -- ∀ x → subTy (Γ̂ ﹫ x) σ ≃ Γ ﹫ x
  LinStruct Γ γ₂ →
  Γ ∶ γ₁ ≼ γ₂ →
  Γ̂ ; γ₁ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k →
  SolvedΔ Δ σ →
  Σ[ Δ′ ∈ CSet ] (Γ̂ ; γ₂ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ′ / k) × SolvedΔ Δ′ σ
```

NOTE the shape of the last two lines.  `SolvedΔ Δ σ` is an INPUT, not the antecedent of
a `Transfer` inside the Σ.  Since C10 the new premise `Γ̂ ∶ α′ ≼ γ₂ ↑ Δ₀′` can only be
BUILT by first bringing the old premise down to the solved context, which needs
`SolvedΔ Δ₀ σ`; so Δ′ genuinely depends on the solvedness proof and
`Σ[ Δ′ ] … × (SolvedΔ Δ σ → SolvedΔ Δ′ σ)` is not inhabitable.  The form above is the
same statement with the arrow pulled out in front, and it is what the main induction
needs anyway (there one always has σ and the solvedness of what one just built).

## Lemma table

| lemma | statement | status | file |
|---|---|---|---|
| `csetOf` / `csetOf≼` | read the emitted constraint set off a derivation / a `≼↑` premise | defined | Weaken.agda |
| `LinBox` | record wrapper of `LinStruct` (makes Γ, γ inferable) | defined | Weaken.agda |
| `↓-∩` | `dom γ ⊆ Z → γ ↓ (X ∩ Z) ≡ γ ↓ X` | proved | Weaken/Support.agda |
| `∈-dom-↓` | `x ∈ dom γ → x ∈ X → x ∈ dom (γ ↓ X)` | proved | Weaken/Support.agda |
| `∉-dom-↓` | `x ∈ X → x ∉ dom (γ ↓ X) → x ∉ dom γ` | proved | Weaken/Support.agda |
| `allCx-dom` | `AllCx P Γ γ → x ∈ dom γ → P (Γ ﹫ x)` | proved | Weaken/Support.agda |
| `extra-unr` | `Γ ∶ γ₁ ≼ γ₂ → x ∈ dom γ₂ → x ∉ dom γ₁ → Unr (Γ ﹫ x)` (pointwise `≼⇒extra-Unr`) | proved | Weaken/Support.agda |
| `allMobile⇒AllCx` / `AllCx⇒allMobile` | `SolvedΔ (allMobile Γ γ) σ ↔ AllCx (λ T → Mobile (subTy T σ)) Γ γ` | proved | Weaken/Support.agda |
| `mobConstraints-weaken` | `Approx Γ̂ Γ σ → Γ ∶ γ₁ ≼ γ₂ → SolvedΔ (mobConstraints M Γ̂ γ₁) σ → SolvedΔ (mobConstraints M Γ̂ γ₂) σ` | proved | Weaken/Support.agda |
| `allCx-transfer` | one pointwise map moves an `AllCx` between two contexts and two predicates | proved | Weaken/Support.agda |
| `≈′-ctx-≃` / `≈-ctx-≃` / `≼-ctx-≃` | contexts equal up to `≃` prove the same `≈` / `≼` | proved | Weaken/Support.agda |
| `approx⇒ctxEq` | `Approx Γ̂ Γ σ → CtxEq (subCtx Γ̂ σ) Γ` | proved | Weaken/Support.agda |
| `unrCx-fwd` | `Approx Γ̂ Γ σ → UnrCx Γ̂ α → UnrCx Γ α` | proved | Weaken/Support.agda |
| `wk-≼` | `Γ ∶ α ≼ β → (T ⸴ Γ) ∶ 𝐂.wk α ≼ 𝐂.wk β` | proved | Weaken/Support.agda |
| `split-weaken` | `LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → Γ ∶ join d (γ₁ ↓ X) (γ₁ ↓ Y) ≼ γ₁ → Γ ∶ join d (γ₂ ↓ X) (γ₂ ↓ Y) ≼ γ₂` | proved | Weaken.agda |
| `split-weaken-ps` | same for `join p/s` (A-Pair, A-Case, A-Let, A-LetPair) | proved | Weaken.agda |
| `split-weaken-seq` | the `d = L` instance (`join L α β = α ; β`), used by A-Seq | proved | Weaken.agda |
| `≼↑⇒≼` | `Approx Γ̂ Γ σ → SolvedΔ Δ₀ σ → Γ̂ ∶ α ≼ β ↑ Δ₀ → Γ ∶ α ≼ β` (`≼↑-sound` + `≼-ctx-≃`) | proved | Weaken.agda |
| `lift-≼` | post-compose a solved premise with the weakening and lift back (A-Var/A-Const/A-LSplit/A-RSplit) | proved | Weaken.agda |
| `lift-split` / `-ps` / `-seq` | down to Γ, canonical split, back up to Γ̂ (the seven two-subterm rules) | proved | Weaken.agda |
| `unr-weaken` | `Approx Γ̂ Γ σ → Γ ∶ γ₁ ≼ γ₂ → UnrCx Γ̂ γ₁ → UnrCx Γ̂ γ₂` (A-Abs / A-AbsRec) | proved | Weaken.agda |
| `alg-weaken-box` | the induction (all 15 A-rules incl. A-Let) | proved | Weaken.agda |
| `alg-weaken` | **`LinStruct Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → Γ ; γ₁ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k → Σ[ Δ′ ∈ CSet ] (Γ ; γ₂ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ′ / k) × Transfer Δ Δ′`** | proved | Weaken.agda |
| `WithSplit` | split-agnostic view of `Weakening` (C1's `lin-*` already supplied) | proved | Weaken/Instance.agda |
| `c-split` / `c-split-ps` | C1's `canon-split` / `canon-split-ps` with X, Y turned implicit | proved | Weaken/Instance.agda |
| `alg-weaken` (exported) | the statement above, **no parameters** | proved | Weaken/Instance.agda |
| `alg-weaken-statement` | regression guard: re-ascribes the exported statement | proved | Weaken/Smoke.agda |

## Module parameters (all discharged)

```agda
canon-split : ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (d : Dir) →
  LinStruct Γ γ → Γ ∶ join d α β ≼ γ → dom α ⊆ X → dom β ⊆ Y →
  (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
  (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
canon-split-ps : the same with (p/s : ParSeq) in place of (d : Dir)
```

C1 states X and Y EXPLICITLY (they occur only under `_↓_` and `_∈_`), `Weakening`
wants them implicit; `c-split` / `c-split-ps` in `Weaken/Instance.agda` are the whole
adaptation (`c-split {X = X} {Y = Y} d = Split.canon-split d X Y`).  The `lin-*`
parameters come from C1's `Completeness/Split/Lin.agda` (`lin-↓`, `lin-bind`,
`lin-bind₂`, `lin-bind-rec`); `lin-bind` is generic in the `Join` instance, so it
serves the Dir, ParSeq and `join L` (= `_;_`) uses alike.

## Notes for the other agents

* `LinStruct Γ γ` is a Π-type in which Γ sits under `lookup` and γ under `count`,
  so Agda can never solve Γ or γ from a `LinStruct` argument (C1 hit the same wall).
  `Weaken.agda` therefore threads the record `LinBox Γ γ` through the induction and
  only unwraps at the leaves; `alg-weaken` itself takes a plain `LinStruct`.
* The Unr side conditions of `canon-split` are discharged by calling it with the
  subsets `X ∩ dom γ₂` and `Y ∩ dom γ₂` (which restrict γ₂ to the same structure,
  `↓-∩`).  That confines the side conditions to variables of γ₂, exactly the ones
  `≼⇒extra-Unr` speaks about.  Callers of `canon-split` that use raw `fv e` subsets
  would need `fv e ⊆ dom γ`, which is NOT available from the ≼ alone.

## Base changes tracked

* C6 (A-Let, `select`/`branch` in A-Const), C6 (A-Case premise `Γ ∶ join p/s (γ ∣fv[ e ])
  (γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂))) ≼ γ`, no more `JoinParSeq`), and C6c
  (A-LetPair / A-Let take `(p/s : ParSeq)`, premise `Γ ∶ join p/s γ₁ γ₂ ≼ γ`, bodies
  `join p/s (join d (` 0F) (` 1F)) (wk² γ₂)` resp. `join p/s (` 0F) (wk γ₂)`) are all
  absorbed.  After C6c, A-Let / A-LetPair are handled exactly like A-Case / A-Pair:
  `split-weaken-ps p/s` for the premise and `≼-join p/s` for the binder.
  The `lin-bind-let` parameter disappeared (A-Let's binder is now `lin-bind-ps p/s`)
  and `lin-bind₂` gained the outer `(p/s : ParSeq)`, matching C1's
  `lin-bind₂ : (a) (d) (T U) (Γ) (γ) → …` exactly.
* C10 (subcontext premises `… ≼ γ ↑ Δ₀` with Δ₀ prepended to the output constraints in
  the nine structural rules; `ChkForm e` premise on A-Ann) is absorbed.  The route per
  structural rule is: `All.++⁻ (csetOf≼ ≤γ)` to get `SolvedΔ Δ₀ σ`, `≼↑⇒≼` down to the
  solved context, `split-weaken*` there, `Sub.≼↑-complete` back up, which also hands
  back `SolvedΔ Δ₀′ σ`.  A-Abs's mobility constraints go through the two-context
  `mobConstraints-weaken`; A-Abs / A-AbsRec's `UnrCx` premises through `unr-weaken`
  (Unr is reflected along `subTy`, `Mobile` is not — hence the constraints).
  A-Ann just carries its `ChkForm` premise through.
* `csetOf` / `csetOf≼` exist so that no `All.++⁻` needs the constructor's implicit
  arguments by name; a future reordering of the generalised implicits of a rule
  cannot break this file.
