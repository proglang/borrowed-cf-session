# Campaign: syntactic type annotation in the core term language (planned 2026-10-07)

Goal: the algorithmic rule A-Ann must read a syntactic annotation instead of
receiving the type out of thin air. Decision (MW): annotation goes into the
CORE term syntax, not a separate surface language.

## Design

1. `Terms/Base.agda`: new constructor `_⦂_ : (e : Tm n) (T : 𝕋) → Tm n`
   (U+2982, NOT the typing colon ∶). Kits: `(e ⦂ T) ⋯ ϕ = (e ⋯ ϕ) ⦂ T`.
   `fv (e ⦂ T) = fv e`. `strip : Tm n → Tm n` removes all annotations.
2. Declarative typing: `T-Ann : Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ⊢ e ⦂ T ∶ T ∣ ϵ`.
3. Dynamics: `E-Ann : (e ⦂ T) ─→ e` in `Reduction/Expressions.agda`.
   `(e ⦂ T)` is NOT a Value; no new Frame.
4. Soup runtime gets the SAME constructor and step (`Terms/BaseSoup.agda`,
   soup expression reduction), and the translation maps ⦂ to ⦂. This keeps
   both simulations LOCK-STEP: an E-Ann source step maps to an E-Ann soup
   step through the generic expression-step case. Do NOT erase annotations in
   the translation; erasure would break the one-step-to-one-step statements.
5. Algorithmic: `A-Ann : Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n → Γ ; γ / m ⊢ e ⦂ T ⇒ T ∣ ϵ ↑ Δ / n`.
   The `ChkForm` premise is deleted; the system is syntax-directed because
   only `_⦂_` terms match. `ChkForm` stays as the guide for where completeness
   inserts annotations.
6. `Algorithmic/Solved.agda`: `SolvedTm (e ⦂ T) = _⦂_ of SolvedTm e and SolvedTy T`;
   `subTm (e ⦂ T) σ = subTm e σ ⦂ subTy T σ` (annotation types may carry uvars).
   Wait: annotation types in CORE Tm are 𝕋 over uvars? Keep `𝕋` as is (it
   already embeds uvars via ``_); solved means no uvars, as for other types.
7. Soundness: A-Ann case = T-Ann after the IH.
8. Completeness statements (`Completeness/Base.agda`), REFINED 2026-10-07:
   a new relation `data _⊑_ : Tm n → Tm n → Set` ("ê annotates e"), with one
   homomorphic congruence rule per Tm constructor plus
   `ann : e ⊑ ê → ∀ T → e ⊑ (ê ⦂ T)`; lemma `fv-⊑ : e ⊑ ê → fv ê ≡ fv e`
   (and `⊑-refl`). Conclusions become `Σ[ ê ∈ Tm n ] e ⊑ ê × (… ⊢ ê ⇐/⇒ …)`.
   The proof inserts `_⦂ T` at checking forms in inference position, T the
   declarative type there; `fv-⊑` transports every `γ ∣fv[ _ ]` restriction
   from e-subterms to ê-subterms.
9. Expected new cases elsewhere: Blocked.agda ⋯ᵣ-inversion lemmas, plug/frame
   lemmas, DescendAbs/DescendK, Terms substitution lemmas, Progress expression
   trichotomy ((e ⦂ T) always steps), Safety pres-Exp via expression
   preservation, ForwardSoup/Expressions and BackwardSoup expression-step
   mappings, both translations.

## Phases (each phase = agents, 2 agda slots machine-wide)

- A (serial, one agent): syntax + kits + fv + strip + T-Ann + E-Ann in both
  term languages + translation case; goal: `Reduction/Expressions.agda` and
  `Processes/TranslationSoup.agda` check.
- B (parallel): B1 Safety/Blocked.agda + Progress plug/expr lemmas;
  B2 Safety preservation Exp path; B3 Algorithmic + Solved + sound;
  B4 remaining Terms/* lemma modules.
- C: Completeness (statement + per-case threading, split by Main/* module).
- D: Simulation expression-step mappings (ForwardSoup, BackwardSoup, legacy
  Forward.agda).
- E: full-development check, agda/CHANGES.md + tex/changes.md updates.

Precondition: the rsplit-relaxation campaign (Safety/AGENTS.md last section)
must be green first; do not run both on Safety files concurrently.
