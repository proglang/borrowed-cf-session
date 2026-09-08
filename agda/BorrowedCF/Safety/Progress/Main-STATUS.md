# Process progress: main induction (agent G3, wave 2)

Files owned: `Safety/Progress.agda`, `Safety/Progress/Main.agda`,
`Safety/Progress/Main/*.agda`, this file.
No postulates, no pragmas, no holes.  ALL THREE FILES TYPE-CHECK (exit 0).

## Safety/Progress/Main/Shapes.agda -- DONE (0 goals)

VERIFIED: `.agdai` deleted, `agda-check` re-run to completion, exit 0, no errors
and no warnings.

| lemma | statement | status |
|---|---|---|
| `no-unit-app` | `Γ ; γ ⊢ K `unit ·⟨ d ⟩ w ∶ T ∣ ϵ → ⊥` | proved |
| `bindCtx-single-0` | `¬ BindCtx (s ; end p) (0 ∷ []) Γ` | proved |
| `bindGroup-0∷0` | `¬ ⊢ᴮ (0 ∷ 0 ∷ B)` | proved |
| `GroupShape` / `groupShape` | a typable binder group is `suc b ∷ B` or `0 ∷ suc b ∷ B` | proved |
| `closed-struct` | `(γ : Struct 0) → [] ∶ γ ≈ []` | proved |
| `close-γ` | `[] ; γ ⊢ₚ P → [] ; [] ⊢ₚ P` (closed processes) | proved |

## Safety/Progress/Main.agda -- DONE (0 goals, 0 metas)

VERIFIED, and the check COMPLETED: `_build/.../Main.agdai` deleted first,
`agda-check BorrowedCF/Safety/Progress/Main.agda` re-run twice to completion,
exit 0, no errors, no warnings, peak RSS 1.4 GB (well under the 11 GB cap).
Nothing below was concluded from a killed run.

Parametrised module; the parameters are the only assumptions.

| lemma | statement | status |
|---|---|---|
| `app-dir-in` | a constant application inside a process context has direction `𝟙` | proved |
| `acq-redexˡ` | `0F ∈AC Q` under `ν (0 ∷ suc b ∷ B₁) B₂` gives a reduction | proved |
| `acq-redexʳ` | `head₂ B₁ b B₂ ∈AC Q` under `ν B₁ (0 ∷ suc b ∷ B₂)` gives a reduction | proved |
| `leaf` | thread `⟪ E [ K c ·⟨ d ⟩ v ]* ⟫`: blocked or reduces (12 constants) | proved |
| `nu` | the four typable binder-group shape combinations | proved |
| `go` | `(ctx : ProcessContext k 0) (Q : Proc k) → [] ; [] ⊢ₚ plug ctx Q → Blocked⁺ Q ⊎ ∃ P′. plug ctx Q ─→ₚ P′` | proved |
| `progress⁺ₚ` | `[] ; γ ⊢ₚ P → Blocked⁺ P ⊎ ∃ P′. P ─→ₚ P′` | proved |
| `progressₚ` | `[] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ ∃ P′. P ─→ₚ P′` | proved |

### Module parameter list (exactly)

From G2.  `plug-typing` is VERIFIED: G2's `Sync/Locate.plug-typing⁺` (already
delivered, and more general -- arbitrary `Γ`, `γ`, plus a lookup-agreement
clause) specialises to it, and `Safety/Progress.agda` now derives it that way;
a throwaway module doing exactly that derivation type-checks (exit 0).

    plug-typing : ∀ {k} (ctx : ProcessContext k 0) (Q : Proc k) →
      [] ; [] ⊢ₚ plug ctx Q →
      Σ[ Δ ∈ Ctx k ] Σ[ σ ∈ Struct k ] ChanCx Δ × (Δ ; σ ⊢ₚ Q)

`sync-redex` is the ONLY parameter whose signature is still a guess (it lives in
`Safety/Progress/Sync.agda`, which does not exist yet):

    sync-redex : ∀ {k b₁ b₂} {B₁ B₂ : BindGroup}
      (ctx : ProcessContext k 0)
      (Q : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
      [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) →
      0F ∈BC Q → head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC Q →
      Σ[ P′ ∈ Proc 0 ] (plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) ─→ₚ P′)

From G1 (`Safety/Progress/Redex.agda`), COPIED VERBATIM from the delivered file:
`step-in-ctx`, `∈AC⇒located-acq`, `redex-new`, `redex-fork`, `redex-lsplit`,
`redex-rsplit`, `redex-drop`, `redex-discard`, `redex-acq-exposedˡ`,
`redex-acq-exposedʳ`.

## Safety/Progress.agda -- DONE (0 goals, 0 metas, no postulates)

VERIFIED, check COMPLETED: `_build/.../Progress.agdai` deleted, `agda-check
BorrowedCF/Safety/Progress.agda` re-run to completion, exit 0, no errors, no
warnings, peak RSS 1.4 GB.  The whole chain Shapes -> Main -> Progress is now
assumption-free: `Main`'s twelve module parameters are all discharged.

Final statements:

    progressₚ  : {γ : Struct 0} {P : Proc 0} →
      [] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)

    progress⁺ₚ : {γ : Struct 0} {P : Proc 0} →
      [] ; γ ⊢ₚ P → Blocked⁺ P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)

Ten of the twelve parameters are G1's lemmas verbatim.  The two G2 lemmas are
adapted by a one-line eta-wrapper each, because G2 states them slightly more
generally / with a different explicitness:

    plug-typing ctx Q ⊢P            = G2.plug-typing ctx Q []ᴬ ⊢P
    sync-redex ctx Q ⊢P mem₁ mem₂   = G2.sync-redex ctx ⊢P mem₁ mem₂

## Notes

* `close-γ` is what reconciles the paper statement `[] ; γ ⊢ₚ P` with the
  `[] ; []` that every `Safety/Progress/Redex.agda` lemma demands.
* `go` returns `Blocked⁺` (the precise variant of `Safety/Blocked.agda`), not
  `Blocked`: the case analysis on the two binder groups delivers it for free.
  `progressₚ` post-composes `Blocked⁺⇒Blocked`.
