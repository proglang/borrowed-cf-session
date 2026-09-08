# C4 — main completeness induction (`Completeness/Main.agda`, `Completeness.agda`)

Owner: agent C4.  Files: `Completeness/Main.agda`, `Completeness/Main/*`, `Completeness.agda`.

## FINDING 1 — CLOSED by C10's base change (was: the theorems are FALSE as stated)

The mechanised algorithmic system checks the structural premises `Γ ∶ … ≼ …` in the
context that A-LetPair / A-Case build from the **inferred** types of the scrutinee, and
those types contain unification variables.  `≼` is not a constraint-generating relation:
`∥′-tm-;` (turn `α ∥ β` into `α ; β`) and `;-commMob` need `MobCx`, and

    Mobile (subTy T̂ σ)  DOES NOT IMPLY  Mobile T̂

(`Mobile ⟨ s ⟩ = ∃ s′. Bounded s′ × s ≃ acq ; s′`; for `T̂ = ⟨ `` α ⟩` with `σ α = acq ; end ‼`
the instance is mobile, the uvar is not: `` `` α `` is a leaf of `≃𝕊`).  `Unr` *is* reflected
(`Unr` is `⊥` on all session types), only `Mobile` is not.

### Counterexample

    s  = msg ‼ `⊤            -- NOT mobile:  msg p T ≄ acq ; s′
    s′ = acq ; end ‼         -- mobile:      Bounded (end ‼)
    Γ  = ⟨ s ; s′ ⟩ ⸴ [],  γ = ` 0F           (SolvedCtx, LinStruct: count = 1)
    e  = `let⊗ (K (`lsplit s) ·¹ ` 0F) `in
            ((K `end ·¹ (K `acq ·¹ ` 1F)) ; (K `send ·¹ (K `unit ⊗ ` 0F)))
    T  = `⊤,  ϵ = 𝕀          (SolvedTm e, SolvedTy T)

*Declaratively derivable*: the body needs `Γ′ ∶ (` 1F) ; (` 0F) ≼ (` 0F) ; (` 1F)`, granted by
`;-commMob` because variable `1F : ⟨ acq ; end ‼ ⟩` is mobile.

*Algorithmically underivable*: A-LSplit forces the pair type `⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩`, so A-LetPair
types the body in `⟨ s ⟩ ⸴ ⟨ `` α ⟩ ⸴ Γ` with structure `(` 0F) ; (` 1F)`.  A-Seq then needs
`(` 1F) ; (` 0F) ≼ (` 0F) ; (` 1F)`, i.e. `Mobile ⟨ `` α ⟩` (variable `0F : ⟨ msg ‼ `⊤ ⟩` is not
mobile), which is underivable.  No other algorithmic derivation exists: `d = L` and the body
structure are forced by A-LSplit and A-LetPair.

**Repair options** (decision needed, outside `Completeness/`):
1. make the algorithmic subcontext premise constraint-generating,
   `Γ ∶ γ₁ ≼ γ₂ ↑ Δ`, emitting `C-Mob (Γ ﹫ x)` for every `∥′-tm-;` / `;-commMob` step
   (`∥′-dup` needs only `Unr`, which is reflected, so it stays); or
2. add a premise to `Complete⇒` / `Complete⇐` excluding declarative derivations that use the
   mobility of a variable bound by `let⊗` / `case` at an unsolved type.

RESOLVED: option 1 was taken (C8's design, C10's edit).  Every `≼` premise of the A-rules is
now `Γ ∶ γ₁ ≼ γ₂ ↑ Δ₀` and the Δ₀ joins the rule's constraints.  `Main/Transfer.agda` builds it
with C8's `≼↑-complete`; the `mob-reflect` parameter is GONE and `Completeness.agda` is
unconditional.  `Main/Transfer.agda` additionally proves `uvarsInΔ-≼↑` (the emitted constraints
are `C-Mob (Γ̂ ﹫ x)`, hence inside the context's scope window), which the induction needs to
carry them past later substitution extensions.

## ⚠ FINDING 2: A-Case is incomplete for variables shared by scrutinee and branches

`A-Case` types the branches in `join p/s (` 0F) (𝐂.wk (γ ↓ ∁ (fv e)))`: the branch context is the
**complement** of the scrutinee's free variables, unlike A-App/A-Seq/A-LetPair/A-Let which use
`γ ∣fv[ eᵢ ]` per subterm.  An *unrestricted* variable used by both the scrutinee and a branch is
therefore dropped:

    Γ = (`⊤ ⊕ `⊤) ⸴ [],  γ = ` 0F,  e = `case (` 0F) `of⟨ ` 1F ; ` 1F ⟩,  T = `⊤ ⊕ `⊤

is declaratively derivable (T-Case par with `γ₁ = γ₂ = ` 0F`, closed by `∥′-dup`), but
`γ ↓ ∁ ⁅ 0F ⁆ = []`, so the branch has to derive `` Γ′ ∶ ` 1F ≼ join p/s (` 0F) [] ``, refuted by
`dom⊈⇒⋠`.

**Repair** (sound generalisation, subsumes the present rule, for C6):

    A-Case-gen : (p/s : ParSeq) {γ′ : Struct n} →
      Γ ∶ join p/s (γ ∣fv[ e ]) γ′ ≼ γ →
      Γ ; γ ∣fv[ e ] / m ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / m₁ →
      T₁ ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ′) / m₁ ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
      T₂ ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ′) / m₂ ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ / n →
      Γ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ C-Eq U₁ U₂ ∷ Δ ++ Δ₁ ++ Δ₂ / n

(`soundness` for it is the present A-Case proof with `join-joinParSeq j-p/s` replaced by the new
premise.)  `Main.agda` takes it as a module parameter `A-Case-gen` until it lands; the proof
instantiates `γ′ := γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂))`.

## ⚠ FINDING 4: A-Let / A-LetPair force the SEQUENTIAL structure, T-Let / T-LetPair do not

`A-LetPair` types the body in `join d (` 0F) (` 1F) ; 𝐂.wk (𝐂.wk γ₂)` and `A-Let` in
`(` 0F) ; 𝐂.wk γ₂`, always with `;`.  The declarative rules use `join p/s A B` for a FREE
`p/s`, and `A ∥ B ≼ A ; B` needs `MobCx` of one side (`∥′-tm-;`), so a `par` derivation whose
body uses the outer context BEFORE the bound variables is lost:

    Γ = ⟨ (msg ‼ `⊤) ; (acq ; end ‼) ⟩ ⸴ ⟨ msg ‼ `⊤ ⟩ ⸴ [],   γ = (` 0F) ∥ (` 1F)
    e = `let⊗ (K (`lsplit (msg ‼ `⊤)) ·¹ ` 0F) `in ((use ` 2F) ; (use ` 0F , ` 1F))

is declaratively derivable with `p/s = par` (the body needs
`(` 2F) ; ((` 0F) ; (` 1F)) ≼ ((` 0F) ; (` 1F)) ∥ (` 2F)`, granted by `;-≼-∥` + `∥-comm`),
but A-LetPair demands `((` 0F) ; (` 1F)) ; (` 2F)`, and both `⟨ msg ‼ `⊤ ⟩` groups are immobile,
so the two `;`-groups cannot be swapped.

**Repair**: give `A-Let` / `A-LetPair` a `(p/s : ParSeq)` argument, exactly like `A-Case`, with
`≤γ : Γ ∶ join p/s γ₁ γ₂ ≼ γ` and body structure `join p/s …` (the current rules are the
`p/s = seq` instances, and `sound` already recovers the ParSeq with `parOrSeq?`).  `Main.agda`
takes `A-Let-gen` / `A-LetPair-gen` as parameters until they land.

## FINDING 3: `let`, `select`, `branch` are unreachable, not proved

`Algorithmic/Solved.agda` has no `SolvedTm` constructor for `` `let_`in_ `` and no `SolvedC`
constructor for `` `select i ``, `` `branch ``, `` `discard ``.  Under the theorem's `SolvedTm e`
hypothesis those cases are *vacuous* (absurd patterns), so C6's new `A-Let` and the admission of
`select`/`branch` into `A-Const` are not exercised.  `Main.agda` routes these three through the
one-line projections `sTm-let`, `sC-select`, `sC-branch` in `Main/Base.agda`, so that adding the
constructors to `Solved.agda` turns the cases on with a one-line change (the A-Let / A-Const
proofs are written out and independent of the projection).

## Design of the induction (fixed, 2026-09-08)

Structural induction on the TERM (not on the derivation): the declarative rules T-Conv / T-Weaken
are absorbed by the inversion lemmas `inv-`` `, `inv-K`, `inv-·`, `inv-⊗`, `inv-;`, `inv-`let`,
`inv-`let⊗`, `inv-inj`, `inv-`case` of `Terms/Base.agda` (plus `inv-ƛ`, `inv-μ`, which C4 adds in
`Main/Base.agda`).  Only INFERENCE is proved; checking is `A-Check` on top of it, so
`Complete⇐ = A-Check ∘ Complete⇒` and the "check e₂ at a type containing e₁'s uvars" problem
disappears (the `C-Eq` it generates is discharged at the merged substitution).

Generalised statement (`complete⇒ᵍ`), needed because A-LetPair / A-Case put INFERRED types into
the context, and because the fresh-variable counter has to be threaded:

    complete⇒ᵍ :
      (Γ̂ : Ctx n) (σ₀ : UV.Sub) → Solving σ₀ →
      (∀ x → UvTy m (Γ̂ ﹫ x)) →                    -- uvars of the context are < m
      (∀ x → subTy (Γ̂ ﹫ x) σ₀ ≃ Γ ﹫ x) →          -- Γ̂ approximates the declarative Γ
      SolvedTm e → SolvedTy T → LinStruct Γ γ →
      Γ ; γ ⊢ e ∶ T ∣ ϵ →
      Σ[ T̂ ] Σ[ ϵ′ ] Σ[ Δ ] Σ[ k ] Σ[ σ ]
        Solving σ × (σ ≈[ m ] σ₀) × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (subTy T̂ σ ≃ T)
        × (Γ̂ ; γ / m ⊢ e ⇒ T̂ ∣ ϵ′ ↑ Δ / k)

`σ ≈[ m ] σ₀ = ∀ α → UVar.var α < m → UV.ap σ α ≡ UV.ap σ₀ α`.  Substitutions are THREADED, not
merged: the right subderivation starts from the left one's σ, so C2's `merge` is not needed; what
is needed from C2 is `UvTy`/`UvΔ`, `scope⇒` and `subTy-agree` (to lift `SolvedΔ Δ₁ σ₁` to the
final σ), plus `single` for A-LSplit/A-RSplit.  C3's `alg-weaken` is NOT needed: every subterm's
declarative derivation is moved to the algorithmic structure on the DECLARATIVE side, by
`restrict` (C5) + `T-Weaken`, before the IH is applied.

`Complete⇒` = `complete⇒ᵍ` at `Γ̂ := Γ`, `σ₀ := UV.someSub`; `Complete⇐` = `A-Check` on it.

## HELPER SPLIT — yes, please spawn both (the types are FIXED and machine-checked)

Everything a helper needs is in `Completeness/Main/Interface.agda` (type-checks, zero goals):
`Approx`, `Conclusion`, `IH`, `AppCase`, `LetCase`, `LetPairCase`, `CaseCase`, `Rules`,
`extend`/`extend-agree`/`extend-solving`/`extend-ap`.  A helper module is

    open import BorrowedCF.Completeness.Main.Base        -- C4 preamble (below)
    open import BorrowedCF.Completeness.Main.Interface
    module BorrowedCF.Completeness.Main.App (RL : Rules) where
    open import BorrowedCF.Completeness.Main.Transfer RL -- ≼→ / unrCx→ / mobCx→ / unr→ / mob→
    app-case : IH → AppCase

and analogously `Main/Bind.agda` with `let-case : IH → LetCase`, `letpair-case : IH → LetPairCase`,
`case-case : IH → CaseCase`.  C1 (`Completeness.Split`), C2 (`Completeness.Scope`) and C5
(`Completeness.Decl`) are imported DIRECTLY, not assumed.  `Main/Base.agda` (C4, checks) has:
`absorbʳ`/`absorbˡ`, `allCx-of-dom`, `dom-↓⁺`, `dom⇒count`, `shared-unr`, `⊔ϵ-lub`, `≤ϵℙ⇒≡ℙ`,
`arrow-inv`/`pair-inv`/`sum-inv` (invert `subTy T̂ σ ≃ (T ⟨ a ⟩→ U)` etc., the `Arr`/`Dir`
annotation comes back too), `inv-ƛ`/`inv-μ`, `solve-ty`/`approx-sub`/`lin-sub` (apply
`⊢-sub UV.someSub` to a subderivation whose type the declarative rule invented, keeping the
approximation and the linearity), `uvar-subTy`, `allMobile-solved`, `subTy-unr⁻¹`,
`unr-approx`, `≼-ctx`/`allCx-ctx`.

Recipe for a BINARY node (declarative split `Γ ∶ join d α β ≼ γ`, subterms e₁ at α, e₂ at β):

1. `restrict` (C5) both premises to `α ↓ fv e₁`, `β ↓ fv e₂`.
2. `↓-strip≼ + fv-cover` (C5) gives `α ↓ fv e₁ ≼ α`, so the restricted split still lies under γ.
3. `Γ ∶ α ↓ fv e₁ ≼ γ ↓ fv e₁`: restrict the split with `↓-mono-≼` and drop the other side with
   `absorbʳ`/`absorbˡ` (Main/Base), whose `UnrCx` obligation is `allCx-of-dom` + `shared-unr`
   (a variable in both sides of a split of a LINEAR structure is unrestricted).  `T-Weaken`
   moves the declarative premise to the algorithmic structure — C3's `alg-weaken` is NOT needed
   and must not be used here, because it changes Δ and would break the scope bookkeeping.
4. IH on each side, THREADING the substitution: the right call takes the left call's σ as its
   σ₀ and its exit counter as its entry counter.  Lift the left `SolvedΔ Δ₁ σ₁` to the final σ
   with `solvedΔ-agree` (C2) and the left `UVarsInΔ 0 m′ Δ₁`; lift `subTy T̂₁ σ₂ ≡ subTy T̂₁ σ₁`
   with `subTy-agree` (C2).  `Agree` composes by `Agree 0 m σ₂ σ₁` + `Agree 0 m σ₁ σ₀`.
5. `canon-split` (C1) with `X := fv e₁`, `Y := fv e₂` gives the `≤γ` premise of the algorithmic
   rule; its two `Unr` side conditions are VACUOUS here because `fv e ⊆ dom (α ↓ fv e)`
   (`fv⊆dom` + `dom-↓⁺`), so no `X ∩ dom γ` trick is needed.
6. Effects: `⊔ϵ-lub`, `≤ϵℙ⇒≡ℙ` (for `EffCompat L/R`, where the declarative rule already forces
   the corresponding premise to be `ℙ`), and C5's `Decl.Eff` bridges.
7. Constraints: never merge — the checking premise's `C-Eq` is built at the END, at the final σ,
   from the two `≃` facts (`subTy T̂₁ σ ≃ subTy T s₀ ≃ subTy Û₂ σ`).

## Lemma status — COMPLETE (2026-09-08)

`agda-check BorrowedCF/Completeness.agda` succeeds: zero goals, zero unsolved metas, no
postulate, no `{-# TERMINATING #-}`, no assumption.  The two theorems of
`Completeness/Base.agda` are proved:

    complete⇒ : Complete⇒        complete⇐ : Complete⇐

| case | lemma | status | file |
|---|---|---|---|
| preamble | 20 helpers (see below) | PROVED | Main/Base.agda (281 l) |
| interface | `Conclusion`, `IHAt`/`IH`, the four case types | PROVED | Main/Interface.agda (134 l) |
| transfer | `≼→` (via C8's `≼↑-complete`), `scope-≼↑`, `unr→`, `unrCx→` | PROVED | Main/Transfer.agda (101 l) |
| binary splits | `canon`, `≼-left`, `≼-right`, `split-left/right/≤γ`, `agree-trans/narrow`, `approx-agree` | PROVED | Main/Bin.agda (131 l) |
| T-Var, T-Const | `var-case`, `const-case` (A-Const, A-LSplit, A-RSplit) | PROVED | Main/Simple.agda (122 l) |
| T-Abs, T-AbsRec | `abs-case`, `absrec-case` | PROVED | Main/Abs.agda (114 l) |
| T-Seq, T-Pair, T-Inj | `seq-case`, `pair-case`, `inj-case` | PROVED | Main/Struct.agda (154 l) |
| T-App ×4 | `app-case` | PROVED | Main/App.agda (105 l) |
| T-Let | `let-case` | PROVED | Main/Bind/Let.agda (108 l) |
| T-LetPair | `letpair-case` | PROVED | Main/Bind/LetPair.agda (119 l) |
| T-Case | `case-case` | PROVED | Main/Bind/Case.agda (196 l) |
| dispatch | `complete⇒ᵍ : IH` (11 term formers + 10 absurd `μ` shapes) | PROVED | Main.agda (124 l) |
| theorems | `complete⇒`, `complete⇐` | PROVED | Main.agda, exported by Completeness.agda |

External inputs, all imported directly (nothing assumed): C1 `Split.agda`, C2 `Scope.agda`,
C5 `Decl.agda`, C8 `Sub.agda`, and the repaired base (C6/C6b/C6c/C10).  C3's `alg-weaken` is
NOT used: every subterm's declarative premise is moved to the algorithmic structure on the
DECLARATIVE side (`restrict` + `T-Weaken`), which keeps the constraint set untouched.

### Performance notes (for the record)

* `Main/Bind.agda` as ONE module exhausted the 11 GB cap.  Split into
  `Bind/{Support,Let,LetPair,Case}.agda`; each checks in well under a minute.
* An irrefutable `let 〈14-tuple〉 = ih …` duplicates the whole right-hand side once per
  component.  Bind the call to a variable first (`r = ih …` then `a , b , … = r`), or use
  `with a , b , … ← ih …`.  The three-hypothesis `case-go` needed the `with` form.
* Never `with`-abstract the inversion package together with the `ParSeq` constructor
  (`with inv-`case dv … | par , …`): it generalises the induction hypotheses, the
  approximation and the linearity before the split.  `case-case` binds the package with a
  `let` and dispatches through a top-level `case-dispatch`.
* Shared structural facts (`covβ`, `≤L`, `≤R`, `≤γ′`, the confined branches) live in the
  top-level parametrised module `CS`, not in a `let`: Agda substitutes `let`s at every use.
