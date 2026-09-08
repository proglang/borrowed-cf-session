# C5 — declarative facts (Completeness/Decl.agda + Decl/)   [COMPLETE]

All four files check with `agda-check`, zero goals, zero unsolved metas, no postulates,
no `{-# TERMINATING #-}`. `open import BorrowedCF.Completeness.Decl` is enough: it
re-exports `Decl.Subsets`, `Decl.Eff`, `Decl.Solved`, C1's `Split.Lin` and
`Completeness.Base`'s `LinStruct` / `SolvedCtx`.

| file | lines | status |
|---|---|---|
| `Completeness/Decl/Subsets.agda` | 226 | done |
| `Completeness/Decl/Eff.agda` | 95 | done |
| `Completeness/Decl/Solved.agda` | 80 | done |
| `Completeness/Decl.agda` | 284 | done |

## Decl.agda — the three main statements

| lemma | statement | status |
|---|---|---|
| `fv⊆dom` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → fv e ⊆ dom γ` | proved |
| `fv-cover′` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → y ∈ dom γ → y ∉ fv e → Unr (Γ ﹫ y)` (pointwise) | proved |
| `fv-cover` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → AllCx Unr Γ (γ ↓ ∁ (fv e))` | proved |
| `restrict` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ↓ fv e ⊢ e ∶ T ∣ ϵ` | proved |
| `restrict-∣fv` | same, written `γ ∣fv[ e ]` | proved |
| `restrict-≼` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ∶ γ ↓ fv e ≼ γ` | proved |
| `restrict-bind` | `(a) (γ) (X) → fvClose (fv e) ⊆ X → Γ′ ; join a (` 0F) (𝐂.wk γ) ⊢ e ∶ U ∣ ϵ → Γ′ ; join a (` 0F) (𝐂.wk (γ ↓ X)) ⊢ e ∶ U ∣ ϵ` | proved |
| `restrict-bind²` | same for `join a (join b (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ))`, hypothesis `fvClose* 2 (fv e) ⊆ X` | proved |
| `restrict-absrec` | same for `(` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ)`, hypothesis `fvClose (fvClose (fv e)) ⊆ X` | proved |
| `lin-join⁻′`, `lin-bind′` | aliases of C1's `lin-join⁻` / `lin-bind` (Split/Lin.agda) | proved |

`restrict-bind` is the one-binder tool for T-Abs / T-Let / T-Case and for the new
A-Let / A-Case: for A-Case take `X := fvClose (fv e₁) ∪ fvClose (fv e₂)`, for A-Let
`X := fvClose (fv e₂)`, with the `⊆` premise `⊆-refl` resp. `p⊆p∪q _` / `q⊆p∪q _ _`.

## Decl/Subsets.agda — subset / dom / ↓ plumbing

| lemma | statement |
|---|---|
| `∈tail⁺`, `∈drop⁺` | `suc x ∈ X → x ∈ tail X`; `m ↑ʳ x ∈ X → x ∈ drop m X` (⁻ directions are in Context.Domain) |
| `suc∉⁅zero⁆`, `suc²∉⁅zero⁆`, `suc²∉⁅suc-zero⁆` | bound variables are not weakened variables |
| `∈dom-wk⁺/⁻`, `∈dom-wk²⁺/⁻` | `x ∈ dom γ ↔ suc x ∈ dom (𝐂.wk γ)` |
| `∈-join⁺/⁻` | `x ∈ dom (join a α β) ↔ x ∈ dom α ⊎ x ∈ dom β`, any `Join` instance |
| `allCx-↓⁺/⁻` | `AllCx P Γ (γ ↓ X) ↔ (∀ y ∈ dom γ, y ∈ X → P (Γ ﹫ y))` |
| `↓-≼-↓` | `Y ⊆ X → (z ∈ dom γ → z ∉ Y → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ Y ≼ γ ↓ X` |
| `↓-bind`, `↓-bind²`, `↓-absrec` | `join a (` 0F) (𝐂.wk γ) ↓ (inside ∷ X) ≡ join a (` 0F) (𝐂.wk (γ ↓ X))` and its two-binder analogues |
| `⊆-inside∷`, `⊆-inside²∷`, `⊆-inside²∷-tail` | `tail Z ⊆ X → Z ⊆ inside ∷ X` (resp. `drop 2`, `tail ∘ tail`) |
| `∈-bind⁺/⁻`, `∈-bind²⁺/⁻`, `∈-absrec⁺/⁻` | dom of a binder block vs dom of the body |

## Decl/Eff.agda — effects

Re-exports `x≤x⊔y`, `x≤y⊔x`, `x≤y⇒x≤y⊔z`, `⊔-mono-≤`, `⊔-monoˡ-≤`, `⊔-monoʳ-≤`,
`⊔-lub`, `⊔-comm`, `⊔-assoc`, `𝕀-maximum`, `ℙ-minimum` from `EffProperties`, plus

| lemma | statement |
|---|---|
| `≤ϵ-antisym` | `ϵ₁ ≤ϵ ϵ₂ → ϵ₂ ≤ϵ ϵ₁ → ϵ₁ ≡ ϵ₂` |
| `≤ϵ-reflexive` | `ϵ₁ ≡ ϵ₂ → ϵ₁ ≤ϵ ϵ₂` |
| `≤ℙ⇒≡ℙ` | `ϵ ≤ϵ ℙ → ϵ ≡ ℙ` |
| `⊔³-lub` | `ϵ₁ ≤ϵ ϵ → ϵ₂ ≤ϵ ϵ → ϵ₃ ≤ϵ ϵ → (ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ ϵ₃) ≤ϵ ϵ` (A-App's effect) |
| `⊔ϵ-idem`, `⊔ϵ-ℙ` | `ϵ ⊔ϵ ϵ ≡ ϵ`, `ϵ ⊔ϵ ℙ ≡ ϵ` |
| `seq⇒pure⇒alg` | `Seq⇒Pure p/s ϵ₁ ϵ₂ → (p/s ≡ seq → ϵ₂ ≡ ℙ)` (declarative ⇒ A-Pair) |
| `alg⇒seq⇒pure` | `= mk-seq⇒pure` (Context.agda), the other direction |
| `seq⇒pure-⊔`, `seq⇒pure-≤` | `Seq⇒Pure p/s ϵ₁ ϵ₂ → ϵ₁ ⊔ϵ ϵ₂ ≡ ϵ₁` (A-Pair reports the join, T-Pair reports ϵ₁) |
| `effCompat-𝟙/L/R` | `d ≡ 𝟙 / L / R → … → EffCompat d ϵ₂ ϵ₁` |
| `effCompat-L≤`, `effCompat-R≤` | same from `ϵ ≤ϵ ℙ` (what the induction has) |
| `effCompat-unr`, `effCompat-lin` | from `Arr.Unr a` (via `ω⇒𝟙`) resp. `Arr.Is𝟙 a` |

`EffCompat (Arr.dir a) ϵ₂ ϵ₁` with ϵ₁ the FUNCTION effect and ϵ₂ the ARGUMENT effect:
for `L` it demands `ϵ₁ ≡ ℙ` (matches T-AppLeft), for `R` it demands `ϵ₂ ≡ ℙ`
(T-AppRight), for `𝟙` it is `⊤` (T-AppUnr / T-AppLin).

## Decl/Solved.agda — inversions

`solvedTm-ƛ`, `solvedTm-μ`, `solvedTm-·`, `solvedTm-;`, `solvedTm-⊗`, `solvedTm-let`,
`solvedTm-let⊗`, `solvedTm-inj`, `solvedTm-case`; `solvedTy-→`, `solvedTy-⊗`,
`solvedTy-⊕`, `solvedTy-⟨⟩`, `solvedTy-if`; `solved-lookup`, `solved-ctx-⸴`.
`solvedTm-K` is NOT here — it is agent C2's, in `Completeness.Scope`.

## Coordination / duplication

- `LinStruct`: C1's `Completeness/Split/Lin.agda` landed while I worked and covers
  everything I needed, so I DELETED my `Decl/Lin.agda` and `Decl.agda` re-exports
  C1's module. `lin-join⁻′` and `lin-bind′` (the names my task fixed) are aliases.
- `solvedTm-K`, `subTy-ctx-id`, `solvedΓ-of` are C2's (Scope.agda), not duplicated.
- C3's `Completeness/Weaken/Lin.agda` duplicates C1's binder lemmas; not my file.

## Issues found

1. `_≤ϵ_` has NO fixity declaration (Types/Syntax.agda), so it defaults to `infixl 20`
   and binds TIGHTER than `_⊔ϵ_` (`infixl 5`). `ϵ₁ ⊔ϵ ϵ₂ ≤ϵ ϵ` therefore parses as
   `ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ (ϵ₃ ≤ϵ ϵ)` and fails with "Eff should be a sort". Always parenthesise:
   `(ϵ₁ ⊔ϵ ϵ₂) ≤ϵ ϵ`. Inside the judgments this never shows because they are `infix 4`.
   Suggested fix in the base: `infix 4 _≤ϵ_`.
2. `SolvedTm` had no `` `let `` constructor when I started; agent C6b added it, and
   `solvedTm-let` is now proved.
3. `count x (` y)` reduces definitionally (`Fin._≟_` pattern-matches), so the `count-self`
   / `∉dom⇒count0` rewrites that C1 and C3 use in the binder lemmas are not needed.
4. Rewriting with `count-join b …` under an ascribed structure `(Struct (2 + _) ∋ ` 0F)`
   silently fails to fire; state the composite equation as its own lemma instead
   (see `count-bind²` in the deleted `Decl/Lin.agda`, kept in the scratchpad).
