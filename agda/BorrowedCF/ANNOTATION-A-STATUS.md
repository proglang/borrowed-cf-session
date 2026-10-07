# Annotation campaign, phase A status

## Plan
- [x] Terms/Base.agda: `_⦂_`, ⋯ / ⋯-id / ⋯-cong / fusion, `strip`, `T-Ann`, `_⊢⋯_`, new `inv-⦂`
- [x] Terms/BaseSoup.agda: `_⦂_`, ⋯ᵣ, ⋯ₛ, phiRefsFrom (BaseSoup/Properties.agda needs nothing)
- [x] Reduction/Expressions.agda: `E-Ann`, preservation′, progress (value⇒pure, inv-unr, ... need no case: Value has none)
- [x] Soup expression reduction (Reduction/ExpressionsSoup.agda): `E-Ann`
- [x] Reduction/Processes/UntypedSoup.agda: consumePhi, insertPhi cases
- [x] Translations: TranslationSoup.agda `T[_]` case; Processes/Translation.agda needs none (translates by `e ⋯ σ`)
- [x] Terms/SubstitutionInversion: two `⊢⋯⁻¹` cases. DescendAbs, DescendK: no Tm cases
- [x] Reduction/Base.agda, Reduction/Processes/Typed.agda: no change needed (both check)
- [x] Verification
- [x] Reconnaissance: Safety/Blocked.agda first error

## Declarations (verbatim)
Terms/Base.agda and Terms/BaseSoup.agda (inside `data Tm`), followed by `infixl 5 _⦂_`:

    _⦂_ : (e : Tm n) (T : 𝕋) → Tm n

Terms/Base.agda, declarative typing:

    T-Ann :
      Γ ; γ ⊢ e ∶ T ∣ ϵ →
      -----------------------
      Γ ; γ ⊢ e ⦂ T ∶ T ∣ ϵ

    inv-⦂ : Γ ; γ ⊢ e ⦂ T ∶ U ∣ ϵ → T ≃ U × Γ ; γ ⊢ e ∶ T ∣ ϵ

Reduction/Expressions.agda: `E-Ann : ∀ {T} → (e ⦂ T) ─→ e`
Reduction/ExpressionsSoup.agda: `E-Ann : ∀ {T : 𝕋} → (e ⦂ T) ─→ e`

Fixity: `infixl 5 _⦂_`, same level as `_⋯_`, so `e ⋯ ϕ ⦂ T` parses as `(e ⋯ ϕ) ⦂ T`.

## Constructor sites added (grep `⦂`)
- Terms/Base.agda: `data Tm` constructor; `_⋯_`, `⋯-id`, `⋯-cong`, `fusion` clauses; `strip` (new, all clauses); `T-Ann` in `_;_⊢_∶_∣_`; `_⊢⋯_` clause `T-Ann x ⊢⋯ ⊢ϕ = T-Ann (x ⊢⋯ ⊢ϕ)`; `inv-⦂` (new)
- Terms/BaseSoup.agda: `data Tm` constructor; `_⋯ᵣ_`, `_⋯ₛ_`, `phiRefsFrom` clauses
- Terms/SubstitutionInversion.agda: `⊢⋯⁻¹ {e = μ (e ⦂ T₀)}` (absurd via μ-ƛ), `⊢⋯⁻¹ {e = e ⦂ T₀}` (via inv-⦂ and T-Ann)
- Reduction/Expressions.agda: `E-Ann` in `_─→_`; `preservation′ (T-Ann e) E-Ann = e`; `progress (T-Ann e) = inj₂ (inj₂ (_ , E-□ E-Ann))`
- Reduction/ExpressionsSoup.agda: `E-Ann` in `_─→_` (and `𝕋` added to the Types import list)
- Reduction/Processes/UntypedSoup.agda: `consumePhi`, `insertPhi` clauses
- Processes/TranslationSoup.agda: `T[ e 𝐓Tm.⦂ T ] σ = (T[ e ] σ) 𝐒Tm.⦂ T`

## Verification (agda-check, exit codes, wall time with cached deps)
| module | exit | wall |
|---|---|---|
| Terms/Base.agda | 0 | 6s (12s cold) |
| Terms/BaseSoup.agda | 0 | 7s |
| Terms/SubstitutionInversion.agda | 0 | 6s |
| Reduction/Expressions.agda | 0 | 7s (34s cold) |
| Reduction/ExpressionsSoup.agda | 0 | 7s |
| Reduction/Processes/UntypedSoup.agda | 0 | 6s |
| Processes/TranslationSoup.agda | 0 | 8s |
| Processes/Translation.agda (tree) | 0 | 7s |
| also: TranslationSoup/{Properties,Examples}, UntypedSoup/{Properties,Examples}, Reduction/Processes/Typed, Processes/Congruence | 0 | 7-34s |

## Reconnaissance (Safety/Blocked.agda, exit 42)
First errors are in its import Safety/Progress/Expr/Plug.agda:

    Plug.agda:33.1-45.18: [CoverageIssue] Incomplete pattern matching for value?. Missing cases:
      value? (e ⦂ T)
    Plug.agda:130.1-178.34: [CoverageIssue] Incomplete pattern matching for plug?. Missing cases:
      plug? x (e ⦂ T)
    Plug.agda:227.1-248.49: [CoverageIssue] Incomplete pattern matching for plug-⋯ᵣ⁻¹. Missing cases:
      plug-⋯ᵣ⁻¹ ρ x (e ⦂ T) x₁

## Notes
- ⦂ (U+2982) was unused in the development before this phase (only in ANNOTATION-PLAN.md).
- `fv` exists only in BorrowedCF/Algorithmic.agda (out of scope for phase A). Phase B3 adds `fv (e ⦂ T) = fv e` there.
- The soup Tm has its own `_⦂_`. Terms/BaseSoup imports Terms/Base with a `using` list, so the names do not clash there. Modules opening both term languages unqualified must disambiguate (constructor overloading resolves by expected type).
- No git operations performed.
