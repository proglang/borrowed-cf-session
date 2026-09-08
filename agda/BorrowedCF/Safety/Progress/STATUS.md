# Agent F (foundations) — status

Owner: agent F. Files owned: `Safety/Blocked.agda`, `Safety/Progress/Expr.agda`,
`Safety/Progress/Expr/**`, `Safety/Progress/STATUS.md`.

Toolchain: `AGDA_DIR=<scratchpad>/agda-dir agda BorrowedCF/Safety/<X>.agda` from `agda/`.
(The Agda MCP server was unreachable at session start; all checks were done from the CLI.)

## Files delivered so far

| File | Status |
|---|---|
| `Safety/Progress/Expr/Plug.agda` | **type-checks, zero goals** |
| `Safety/Blocked.agda` | **type-checks, zero goals** |
| `Safety/Progress/Expr.agda` | **type-checks, zero goals** |

## `Safety/Progress/Expr/Plug.agda` (helper; other agents may import, never edit)

Structural presentation of "some subterm at an evaluation position satisfies `Red`".
Needed because `E [ r ]*` (`Frame*` plugging) is a stuck application, so Agda cannot
case-split on it; `Plug` has one constructor per *term* former, so inversion,
decidability and renaming-inversion are plain structural recursions.

| Lemma | Statement | Status |
|---|---|---|
| `value?` | `(e : Tm n) → Dec (Value e)` | proved |
| `app₁-cond?` / `app₂-cond?` | decide the `Frame` value side conditions | proved |
| `Plug` | `data Plug (Red : Tm n → Set) : Tm n → Set` | defined |
| `plug-frame` / `plug-frame*` | `Plug Red e → Plug Red (F [ e ])` / `(E [ e ]*)` | proved |
| `plug⇒ctx` | `Plug Red e → ∃[ E ] ∃[ r ] Red r × e ≡ E [ r ]*` | proved |
| `plug?` | `(∀ e → Dec (Red e)) → ∀ e → Dec (Plug Red e)` | proved |
| `value-⋯ᵣ⁻¹` | `Value (e ⋯ ρ) → Value e` | proved (= `InvFrame.value-reflect`; see Reuse) |
| `⋯ᶠ-[]` / `⋯ᶠ*-[]*` | `(E [ e ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ e ⋯ ρ ]*` | proved |
| `plug-⋯ᵣ` / `plug-⋯ᵣ⁻¹` | Plug transported/reflected along a renaming | proved |

## `Safety/Blocked.agda`

| Item | Statement | Status |
|---|---|---|
| `BlockingConst` | constants outside `{new,fork,lsplit,rsplit,drop,discard,unit}` | defined |
| `blockingConst?` | decidable | proved |
| `Stuck` | `∃ E c d v. Value v × BlockingConst c × e ≡ E [ K c ·⟨ d ⟩ v ]*` (tex B-ExpConstBlocked) | defined |
| `StuckRedex`, `stuck⇒plug`, `plug⇒stuck` | `Stuck e ↔ Plug StuckRedex e` | proved |
| `BCRedex` / `ACRedex` | the BC/AC tables of the tex figure as redex shapes | defined |
| `_∈BCe_` | `send/recv/select i/branch/end p`, tex BC on threads | defined |
| `_∈ACe_` | single `acq` constructor, tex AC on threads | defined |
| `∈BCe⇒plug`,`plug⇒∈BCe`,`∈ACe⇒plug`,`plug⇒∈ACe` | equivalence with `Plug` | proved |
| `constApp?`,`isVar?`,`sendArg?` | shape decisions on `Tm` | proved |
| `bcRedex?`,`acRedex?`,`stuckRedex?` | decidable redex shapes | proved |
| `_∈BCe?_`,`_∈ACe?_`,`stuck?` | decidable at expression level | proved |
| `_∈BC_` / `_∈AC_` | lifted to `Proc` through `⟪_⟫`, both sides of `∥`, and `ν` | defined |
| `_∈BC?_` / `_∈AC?_` | `∀ x P → Dec (x ∈BC P)` etc. | proved |
| `head₂` | first variable of side 2 of a `ν`, spelled as in R-Com | defined |
| `Blocked` | B-Unit, B-Const, B-Par, B-Nu, B-NuAcqˡ, B-NuAcqʳ | defined |
| `Blocked⁺` | precise variant: B-NuAcqˡ⁺, B-NuAcqʳ⁺, B-NuAcqˡʳ⁺ | defined |
| `Blocked⁺⇒Blocked` | `Blocked⁺ P → Blocked P` | proved |
| `↑*-↑ʳ` / `↑*-↑ˡ` / `↑*-↑ʳ⁻¹` | `ρ ↑* k` acts as `ρ` above the k binders and as the identity on them | proved |
| `⋯ᵣ-K⁻¹`, `⋯ᵣ-var⁻¹`, `⋯ᵣ-pair⁻¹`, `⋯ᵣ-KApp⁻¹` | a renaming reflects the top term former | proved |
| `bcRedex-⋯ᵣ` / `acRedex-⋯ᵣ` / `stuckRedex-⋯ᵣ` and `…-⋯ᵣ⁻¹` | redex shapes transport/reflect | proved |
| `∈BCe-⋯ᵣ` / `∈ACe-⋯ᵣ` / `Stuck-⋯ᵣ` | `x ∈BCe e → ρ x ∈BCe (e ⋯ ρ)` etc. | proved |
| `∈BCe-⋯ᵣ⁻¹` / `∈ACe-⋯ᵣ⁻¹` / `Stuck-⋯ᵣ⁻¹` | `y ∈BCe (e ⋯ ρ) → ∃ x. ρ x ≡ y × x ∈BCe e` | proved |
| `∈BC-⋯ᵣ` / `∈AC-⋯ᵣ` | `x ∈BC P → ρ x ∈BC (P ⋯ₚ ρ)` | **proved** |
| `∈BC-⋯ᵣ⁻¹` / `∈AC-⋯ᵣ⁻¹` | `y ∈BC (P ⋯ₚ ρ) → ∃ x. ρ x ≡ y × x ∈BC P` (no injectivity needed) | **proved** |
| `⋯ₚ-⟪⟫⁻¹`, `⋯ₚ-∥⁻¹`, `⋯ₚ-ν⁻¹` | a renaming reflects the top process former | proved |
| `Blocked-⋯ᵣ` | `Inj ρ → Blocked P → Blocked (P ⋯ₚ ρ)` | **proved** |
| `Blocked-⋯ᵣ⁻¹` | `Blocked (P ⋯ₚ ρ) → Blocked P` (injectivity NOT needed) | **proved** |

## `Safety/Progress/Expr.agda`

All of the following type-check with zero goals.

| Lemma | Statement | Status |
|---|---|---|
| `ConstApp` | `∃ E c d v. Value v × e ≡ E [ K c ·⟨ d ⟩ v ]*` (middle case of the paper's theorem) | defined |
| `constApp-frame` | `ConstApp e → ConstApp (F [ e ])` | proved |
| `stuck⇒constApp` | `Stuck e → ConstApp e` | proved |
| `const-unr` | `Γ ; γ ⊢ K c ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.Unr a` | proved |
| `const-app-dir` | `Γ ; γ ⊢ K c ·⟨ d ⟩ v ∶ T ∣ ϵ → d ≡ 𝟙` | proved |
| `inv-app-fn/arg` | app inversion that KEEPS the arrow (`Γ;α ⊢ e₁ ∶ T ⟨a⟩→ U`, `Γ;β ⊢ e₂ ∶ T`) | proved |
| `fn-send-dom` | `⊢ K `send ∶ T ⟨a⟩→ U → ∃ T₀. (T₀ ⊗¹ ⟨ msg ‼ T₀ ⟩) ≃ T` | proved |
| `fn-recv-dom` | `… → ∃ T₀. ⟨ msg ⁇ T₀ ⟩ ≃ T` | proved |
| `fn-select-dom` | `… → ∃ (s₁,s₂). ⟨ brn ‼ s₁ s₂ ⟩ ≃ T` | proved |
| `fn-branch-dom` | `… → ∃ (s₁,s₂). ⟨ brn ⁇ s₁ s₂ ⟩ ≃ T` | proved |
| `fn-lsplit-dom` / `fn-rsplit-dom` | `… → ∃ s′. ⟨ s ; s′ ⟩ ≃ T` | proved |
| `fn-new-dom` | `… → `⊤ ≃ T` | proved |
| `fn-fork-dom` | `… → (`⊤ →1M `⊤ ∣ 𝕀) ≃ T` | proved |
| `progress⁺` | `Γ ; γ ⊢ e ∶ T ∣ ϵ → Value e ⊎ ConstApp e ⊎ ∃[ e′ ] e ⋯→ e′` | **proved** |
| `handle-arg` | generic: a value argument of a handle-domain constant is a variable with a `≃`-matching session | proved |
| `arg-send` | argument is `v₀ ⊗ ` x` with `Γ ﹫ x ≡ ⟨ s ⟩`, `s ≃ msg ‼ T₀` | proved |
| `arg-recv` | `` ` x``, `s ≃ msg ⁇ T₀` | proved |
| `arg-select` | `` ` x``, `s ≃ brn ‼ s₁ s₂` | proved |
| `arg-branch` | `` ` x``, `s ≃ brn ⁇ s₁ s₂` | proved |
| `arg-end` | `` ` x``, `s ≃ end p₀` | proved |
| `arg-acq` | `` ` x``, `s ≃ acq ; s₀` | proved |
| `arg-drop` | `` ` x``, `s ≃ ret` | proved |
| `arg-discard` | `` ` x``, `s ≃ skip` | proved |
| `arg-lsplit` / `arg-rsplit` | `` ` x``, `s ≃ s₀ ; s′` | proved |
| `arg-new` | argument is `K `unit` | proved |
| `stuck⇒∈BC/AC` | a stuck thread yields `∃ x. x ∈BCe e` (or `∃ x. x ∈ACe e` for `acq`) | **proved** |

`fork` needs no argument-shape lemma: its argument is an arbitrary value of function type,
`fn-fork-dom` records the domain.

Note: `Safety/Blocked.agda` is 751 lines, above the ~600-line guideline in AGENTS.md.
Splitting it would force downstream agents to import two modules for one predicate, so it is
left whole; the renaming section at the end is self-contained if a split becomes necessary.

## Reuse (modules imported, never edited)

- `Simulation/Support/InvFrame.agda`: `arg-type`, `value-reflect`.
- `Simulation/Support/AcqInv.agda`: `fn-acq-dom`.
- `Simulation/Support/PairConfine.agda`: `fn-end-dom`.
- `Simulation/Support/Theorems/DropShape.agda`: `fn-drop-dom`, `fn-discard-dom`.
- `Reduction/Expressions.agda`: `inv-arr`, `inv-session`, `value×⊗⇒⊗`, `value⇒pure`.
- `Terms/Base.agda`: `inv-·`, `inv-K`, `inv-⊗`, `inv-`_`, `constFnUnr′`.

Top-level `fn-send-dom`, `fn-recv-dom`, `fn-select-dom`, `fn-branch-dom`,
`fn-lsplit-dom`, `fn-rsplit-dom`, `fn-new-dom`, `fn-fork-dom` do NOT exist anywhere at
importable scope (`Position.agda`, `Leaves/Choice.agda` have them only inside `where`
blocks), so they are proved in `Safety/Progress/Expr.agda` in the same style and are
free for other agents to import.

## Notes / discrepancies with the tex

1. tex B-ExpConstBlocked excludes `c ∈ {new, fork, lsplit, rsplit, drop, discard}` but
   not `unit`; the Agda `Const` has `` `unit `` (the value `*`), so `BlockingConst`
   excludes it too. Otherwise `Blocked ⟪ * ⟫` would be derivable twice.
2. tex B-NuBlocked reads `{x,y} ∩ BC(P) ≠ {x,y}`. Mechanised as
   `¬ (x ∈BC P × y ∈BC P)`, which is the same statement for a two-element set.
3. tex B-NuBlockedAcq quantifies over `i ∈ {1,2}`; mechanised as the two rules
   `B-NuAcqˡ` / `B-NuAcqʳ`, and refined in `Blocked⁺` (see the comment now in
   `tex/rules/blocked.tex`).
