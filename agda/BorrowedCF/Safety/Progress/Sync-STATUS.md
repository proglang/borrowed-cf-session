# Sync lemmas (agent G2, wave 2)

Files owned: `Safety/Progress/Sync.agda`, `Safety/Progress/Sync/*.agda`, this file.
No postulates, no pragmas, no holes in anything marked DONE.

## Safety/Progress/Sync/Front.agda -- DONE (type-checks, 0 goals)

The front-kind theory that the dual-heads lemma needs.  `Types/AtomCons.agda`
peels a leading ATOM (`Cons`), but only for closed non-`msg` atoms, and
`Types/Atoms.agda` records that the `_≃_` transport for a leading `brn` was
abandoned.  Forgetting the payload and the branches makes the whole
development go through.

| lemma | statement | status |
|---|---|---|
| `HKind`, `dualKind` | head kinds `kmsg p` / `kbrn p` / `kend p` | defined |
| `ConsK hk w` | `w` starts with a head of kind `hk` (`hmsg`/`hbrn`/`hend`/`hd`/`tl`/`mu`) | defined |
| `skips⊥consK` | `Skips w → ConsK hk w → ⊥` | proved |
| `consK-unique` | `ConsK hk₁ w → ConsK hk₂ w → hk₁ ≡ hk₂` | proved |
| `consK-;⁻` | `ConsK hk (s₁ ; s₂) → ConsK hk s₁ ⊎ (Skips s₁ × ConsK hk s₂)` | proved |
| `consK-dual` | `ConsK hk w → ConsK (dualKind hk) (dual w)` | proved |
| `consK-⋯`, `consK-⋯ᵣ⁻¹`, `consK-⋯⁻¹` | substitution, both directions | proved |
| `consK-unfold`, `consK-unfold⁻¹` | `ConsK hk (mu s) ↔ ConsK hk (unfold s)` | proved |
| `≃-consK` | `w₁ ≃ w₂ → ConsK hk w₁ → ConsK hk w₂` | proved |
| `front-dual` | `ConsK hk₁ (s ; end p) → ConsK hk₂ (dual s ; end (dualPol p)) → hk₂ ≡ dualKind hk₁` | proved |

Reused: `Types.{Syntax,Substitution,Equivalence}` only (`skips-dual⁺`, `skips-⋯`,
`skips-⋯ᵣ⁻¹`, `skips-⋯⁻¹`, `≃-skips`, `dual-involutive`, `dualPol-involutive`).

## Safety/Progress/Sync/Heads.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `bindCtx′-head` | `BindCtx′ s Γ → Γ ﹫ 0F ≡ ⟨ t ⟩ → ConsK hk t → ConsK hk s` (Γ non-empty) | proved |
| `bindCtx-head` | same for `BindCtx s (suc b ∷ B) Γ` (the borrow's `ret` is peeled off) | proved |
| `head-kinds` | the two endpoints of a `TP-Res` present dual head kinds | proved |
| `BCShape x hk e` | `_∈BCe_` with the head kind as an INDEX and direction `𝟙` | defined |
| `shape⇒∈BCe` | back to `_∈BCe_` | proved |
| `bc-shape` | `ChanCx Γ → Γ ; γ ⊢ e ∶ T ∣ ϵ → x ∈BCe e → ∃ hk s. BCShape x hk e × Γ ﹫ x ≡ ⟨ s ⟩ × ConsK hk s` | proved |

Reused: agent F's `arg-send/recv/select/branch/end`, `const-app-dir` (Progress/Expr.agda),
`⊢[]*⁻¹` (Reduction/Base.agda), `Processes.Typed.{BindCtx,BindCtx′}`.

## Safety/Progress/Sync/Unique.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `bcRedex-fn` | a BC redex is `K c ·⟨ d ⟩ w` with `Value w` | proved |
| `bcRedex-unique`, `plug-value⊥`, `plug-K⊥`, `app-conflict` | auxiliaries | proved |
| `plug-det` | `Plug (BCRedex x) e → Plug (BCRedex y) e → x ≡ y` | proved |
| `∈BCe-unique` | `x ∈BCe e → y ∈BCe e → x ≡ y` (a thread blocks on one channel) | proved |

Reused: agent F's `Plug`, `∈BCe⇒plug` (Progress/Expr/Plug.agda, Blocked.agda).

## Safety/Progress/Sync/Locate.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `Loc₁`, `locate₁` | `x ∈BC P → ∃ ctx e. plug ctx ⟪ e ⟫ ≡ P × weakenThrough ctx x ∈BCe e` | proved |
| `Loc₂`, `locate₂` | `x ≢ y → x ∈BC P → y ∈BC P → ∃ (c : ProcessContext₂) e₁ e₂. plug₂ c ⟪e₁⟫ ⟪e₂⟫ ≡ P × wt₁ c x ∈BCe e₁ × wt₂ c y ∈BCe e₂` | proved |
| `swap₂`, `plug-swap₂`, `wt₁-swap₂`, `wt₂-swap₂`, `swapLoc₂` | exchanging the two holes | proved |
| `plug-typing⁺` | `ChanCx Γ → Γ ; γ ⊢ₚ plug ctx R → ∃ Γ′ γ′. ChanCx Γ′ × Γ′ ; γ′ ⊢ₚ R × (∀ z → Γ′ ﹫ weakenThrough ctx z ≡ Γ ﹫ z)` | proved |

Reused: G1's `∈BC⇒located` (Progress/Redex/Located.agda), `Locate.{ProcessContext,plug,compose}`,
`Position.weakenThrough`, `CanonicalPair.{ProcessContext₂,plug₂,wt₁,wt₂,fill₁,fill₂}`,
`Processes.Typed.{inv-∥,inv-ν,bindCtx⇒chanCtx}`.

## Safety/Progress/Sync/Choice.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `choice-step` | `(bnd : Binder₂ c x₁ x₂) → HeadShape₂ … → (E₁) (i) (E₂) → ∃ P′. plug₂ c ⟪ E₁ [ select i ·¹ ` x₁ ]* ⟫ ⟪ E₂ [ branch ·¹ ` x₂ ]* ⟫ ─→ₚ P′` | proved |

Reused: `CanonicalPair.canon-pair`, G1's `red-in-ctx`, F's `⋯ᶠ*-[]*`, `Locate.≡→≋`.

## Safety/Progress/Sync/Com.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `com-step` | as `choice-step`, for `send`/`recv`, with `[] ; [] ⊢ₚ …` as an extra premise | proved |

Reused: additionally `PairConfine.com-confine`, `Congruence._/_⊢-≋_`, `plug-typing⁺`,
F's `value-⋯ᵣ⁻¹`.

## Safety/Progress/Sync/CloseShape.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `new-¬end` | `New s → ¬ ConsK (kend q) s` | proved |
| `close-shape` | `New s → BindCtx (s ; end p) (suc b ∷ B) Γ → Γ ﹫ 0F ≡ ⟨ t ⟩ → t ≃ end q → b ≡ 0 × B ≡ []` | proved |

Reused: `PairConfine.close-group-width`, `Equivalence.atom-;⁻`, `≃-skipsˡ`.

## Safety/Progress/Sync/Close.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `wkₚ00` | `wkₚ 0 0 ≗ weaken* 2` (the renaming `ν-ext′` undoes) | proved |
| `close-groups` | both binder groups of a closing `ν` are `[ 1 ]` | proved |
| `close-go₂` | the residual-free canonical form reduces (`close-confine` + `R-Close`) | proved |
| `close-go` | pushes the residual out of the binder (`ν-ext′` backwards) and calls `close-go₂` | proved |
| `close-step` | as `com-step`, for `end ‼` / `end ⁇` | proved |

Reused: `PairConfine.{close-handle-end,close-pair-confine,close-confine}`,
`Processes.Typed.{ν-ext′,ν-cong,∥-comm,⋯ₚ-cong}`, `Locate.≋-plug`.

## Safety/Progress/Sync/Binder.agda -- DONE (type-checks, 0 goals)

| lemma | statement | status |
|---|---|---|
| `binderL` | `Binder₂ (compose₂ ctx (bind₂ C₁ C₂ c₀)) (wt₁ c₀ 0F) (wt₂ c₀ head₂)`, locals `0F` / `sum C₁ ↑ʳ 0F` | proved |
| `binderR` | the same with the two holes exchanged (`swap₂`), locals `sum C₁ ↑ʳ 0F` / `0F` | proved |
| `plugL` / `plugR` | `plug₂ (compose₂ ctx (bind₂ C₁ C₂ c₀)) R₁ R₂ ≡ plug ctx (ν C₁ C₂ (plug₂ c₀ R₁ R₂))` (and its swapped form) | proved |
| `0≢head₂` | `0F ≢ head₂ (suc b₁ ∷ B₁) b₂ B₂` | proved |

## Safety/Progress/Sync/Dispatch.agda -- DONE (type-checks, 0 goals, 12 s)

| lemma | statement | status |
|---|---|---|
| `transport-red`, `transport-⊢` | rewriting a reduction / a typing along a process equation, by matching `refl` | proved |
| `dispatch` | the six surviving constant pairs, each firing its rule in the right orientation | proved |

## Safety/Progress/Sync.agda -- DONE (type-checks, 0 goals, 16 s)

| lemma | statement | status |
|---|---|---|
| `plug-typing` | `ChanCx Γ → Γ ; γ ⊢ₚ plug ctx Q → ∃ Δ σ. ChanCx Δ × Δ ; σ ⊢ₚ Q` (= `Locate.focusTyping`) | proved |
| `lookup-fst` / `lookup-snd` | the two head handles of `(Γ₁ ⸴* Γ₂) ⸴* Δ` are `Γ₁ ﹫ 0F` and `Γ₂ ﹫ 0F` | proved |
| `sync-go` | reads both head kinds off the two threads and calls `dispatch` | proved |
| `sync-redex` | THE MAIN LEMMA (statement below) | **proved** |

```
sync-redex : {k : ℕ} (ctx : ProcessContext k 0) {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  {Q : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)} →
  [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) →
  0F ∈BC Q →
  head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC Q →
  Σ[ P′ ∈ Proc 0 ] plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) ─→ₚ P′
```

## PERFORMANCE (2026-09-08) -- read this before touching these files

The first version of the dispatch rewrote the two process equations with
`subst (λ z → z ─→ₚ _) eq red` and projected the rule worker's result with a
pattern-`let`.  Agda then unfolds `plug`, `plug₂`, `compose₂` and `fill₂` under
the equation: ONE such clause reached 10 GB RSS and did not finish; the whole
module was killed twice (once at 12 GB after 15 min).  Bisecting with a probe
module showed
  * importing `Sync/{Com,Choice,Close}` and applying `choice-step (binderL …)
    (heads-lr …) E₁ i E₂` bare: 11 s;
  * the same plus the `subst`/pattern-`let` transport: >10 GB, no end.
The fix is `transport-red` / `transport-⊢` in `Sync/Dispatch.agda`: they take the
equation and match it with `refl` while both processes are still VARIABLES.
With them the six clauses check in 12 s and `Sync.agda` in 16 s.
The same rule applies to the two `plug-fill₂` / `plug-fill₁` rewritings in
`sync-go` (`transport-⊢` there) -- with `subst` they are just as expensive.
The three rule workers keep a single `with` on the `CanonPair` record and check
in one to two minutes each; that pattern is fine as long as the record is
consumed inside the same clause.
## Discrepancies found (tex vs Agda)

1. `Types/Atoms.agda` states that the `_≃_` transport of a leading `brn` was
   abandoned, and `Types/AtomCons.agda` covers only closed non-`msg` atoms.  Both
   gaps are on the critical path of progress: without them nothing rules out a
   `select` facing a `select`.  `Sync/Front.agda` closes them by forgetting the
   payload and the branches -- the FRONT KIND is what the proof needs, and it is
   `≃`-invariant, unique, and flipped by `dual` (`front-dual`).
2. tex R-Com writes the frames, the sent value and the residual unchanged on both
   sides of the rule, leaving "x and y do not occur in them" to the nominal binder
   convention.  The Agda rule instead demands that all four factor through `wkₚ`.
   For a well-typed process this is not a restriction (`PairConfine.com-confine`),
   but a paper proof of progress must say so; it is the only reason `R-Com` fires.
3. tex R-Close has no parallel residual (`ν x y (F₁[term x] ∥ F₂[wait y])`), so the
   rule can only fire after `≡` has extruded the residual out of the binder.  The
   mechanised progress proof does exactly that (`ν-ext′` backwards), and it is
   sound only because the residual cannot mention the two closing handles
   (`close-pair-confine`).  Worth a sentence in the paper.
4. tex brackets the three components differently in R-Com (`(F₁ ∥ F₂) ∥ P`) and in
   R-Choice (`F₁ ∥ (F₂ ∥ P)`); the Agda rules both use `(F₁ ∥ F₂) ∥ P`.  Cosmetic.
5. B-NuBlocked's side condition is exactly right: `sync-redex` is its converse for
   the shape `ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)`, i.e. when both heads ARE in BC the
   process reduces.  Nothing else about the two groups is needed -- in particular
   the `end`/`end` case does NOT have to be assumed to sit at `ν [1] [1]`, that is
   derived (`Sync/CloseShape.close-shape`).
