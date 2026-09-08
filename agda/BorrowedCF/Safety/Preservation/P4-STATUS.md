# P4 status — R-Exp, R-New, R-Fork, R-Close, R-Discard, R-Drop, R-Acq, R-Par, R-Bind, R-Struct + assembly

Owner: agent P4.  Files owned: `Safety/Preservation.agda`,
`Safety/Preservation/Basic.agda`, `Safety/Preservation/Handles.agda`,
`Safety/Preservation/Basic/`, `Safety/Preservation/Handles/`, this file.

## Gotcha for everybody

Every `;` in this development is **U+037E GREEK QUESTION MARK**, not ASCII
`;` — that includes the operator *names* `atom-;-unsnoc`, `noRet-;-fst`,
`𝐂.;-unit₁`, `NoRet._;_`, …  An ASCII `;` gives a bare `[ParseError]`.

## Lemmas

| lemma | statement | status | file |
|---|---|---|---|
| `pres-Exp` | `ChanCx Γ → e₁ ⋯→ e₂ → Γ ; γ ⊢ₚ ⟪ e₁ ⟫ → Γ ; γ ⊢ₚ ⟪ e₂ ⟫` | **proved** | `Preservation/Basic.agda` |
| `pres-New` | `ChanCx Γ → ∀ {s} E → Γ ; γ ⊢ₚ ⟪ E [ K (`new s) ·¹ * ]* ⟫ → Γ ; γ ⊢ₚ ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) ⟪ … ⟫` | **proved** | `Preservation/Basic.agda` |
| `pres-Fork` | `ChanCx Γ → ∀ E (V : Value e) → Γ ; γ ⊢ₚ ⟪ E [ K `fork ·¹ e ]* ⟫ → Γ ; γ ⊢ₚ ⟪ E [ * ]* ⟫ ∥ ⟪ e ·¹ * ⟫` | **proved** | `Preservation/Basic.agda` |
| `⋯𝓅-wk-conv` | `𝒫 ⋯𝓅 weaken* ⦃Kₛ⦄ k ≡ 𝒫 ⋯𝓅 weaken* ⦃Kᵣ⦄ k` (closes the human's "TINY HOLE") | **proved** (private) | `Preservation/Basic.agda` |
| `er` / `er-⇒` / `er-wk` / `er-wkₛ` / `er-wk𝓅` | the erasing structure substitution `er k` (first `k` vars ↦ `[]`), its `⇒`-witness and its cancellation of `weaken* k` | **proved** | `Preservation/Handles/Erase.agda` |
| `app-var-[]≼` | `σ ∶ Γ ⇒ Γ′ → σ x ≡ [] → Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ → Γ′ ∶ [] ≼ γ ⋯ σ` (a consumed handle makes the whole redex structure droppable once erased) | **proved** | `Preservation/Handles/Erase.agda` |
| `plug-≼` | one consumed-handle thread: bounds the unit-plugged frame by the erased thread structure | **proved** | `Preservation/Handles/Erase.agda` |
| `er1-fuse`, `fuse2/3/4`, `nseq-er`, `tail-er`, `grp₂-er`, `amb-er` | the `TP-Res` body structure of `ν (suc b₁ ∷ B₁) B₂` erases under `er 1` to that of `ν (b₁ ∷ B₁) B₂` | **proved** | `Preservation/Handles/Frames.agda` |
| `bindCtx-discard` | `Γ ﹫ 0F ≃ ⟨ skip ⟩ → BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ → BindCtx (s ; end p) (b₁ ∷ B₁) (V.tail Γ)` | **proved** | `Preservation/Handles/BindCtx.agda` |
| `bindCtx-drop` | `New s → Γ ﹫ 0F ≃ ⟨ ret ⟩ → BindCtx (s ; end p) (suc b₁ ∷ B₁) Γ → BindCtx (s ; end p) (b₁ ∷ B₁) (V.tail Γ)` | **proved** | `Preservation/Handles/BindCtx.agda` |
| `skips-front` | `sh ; ret ≃ skip ; ret → Skips sh` (via `Types.AtomUnsnoc.atom-;-unsnoc`) | **proved** (private) | `Preservation/Handles/BindCtx.agda` |
| `pres-Close` | `ChanCx Γ → Γ ; γ ⊢ₚ ν [1] [1] (…end‼…∥…end⁇…) → Γ ; γ ⊢ₚ ⟪ E₁ [ * ]* ⟫ ∥ ⟪ E₂ [ * ]* ⟫` | **proved** | `Preservation/Handles.agda` |
| `pres-Discard` | `ChanCx Γ → Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂ (…discard…) → Γ ; γ ⊢ₚ ν (b₁ ∷ B₁) B₂ (⟪ E [ * ]* ⟫ ∥ P)` | **proved** | `Preservation/Handles.agda` |
| `pres-Drop` | same with `drop` | **proved** | `Preservation/Handles.agda` |
| `pres-Acq` | `ChanCx Γ → Γ ; γ ⊢ₚ ν (0 ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P) → Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` 0F ]* ⟫ ∥ P)` | **OPEN — currently a `postulate` in `Handles.agda`** | `Preservation/Handles.agda` |
| `preservationₚ` | `ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q` | assembled and type-checks; R-Exp/R-Struct/R-Par/R-Bind proved here, R-New/R-Fork from `Basic`, R-Close/R-Discard/R-Drop from `Handles`, R-Com from P2 | `Preservation.agda` |

## Postulates currently in delivered files (LOUDLY)

1. `Handles.agda`: `pres-Acq` (the only remaining case of mine).  See the
   obstacle below.
2. `Preservation.agda`, in a `private` block marked `TEMPORARY, replaced by
   P2/P3`: `pres-Choice`, `pres-LSplit`, `pres-RSplit`, stated as the full
   `ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q`.  Delete them and import
   `Preservation.{Choice,LSplit,RSplit}` as soon as P2/P3 deliver; the three
   call sites already pass `Γ-S`, the typing and the reduction.
   **P2's `Preservation.Com.pres-Com` is already wired in** (call site:
   `pres-Com {E₁ = E₁} {E₂ = E₂} {P = P₀} Γ-S V ⊢P`).

## The `pres-Acq` obstacle (for whoever picks it up)

R-Acq is the only rule whose two sides live in the *same* scope: the binder
list goes `0 ∷ suc b₁ ∷ B₁ ↝ suc b₁ ∷ B₁`, `sum` is unchanged (`sum (0 ∷ X) ≡
sum X` definitionally), `E` and `P` are literally the same terms, the two
`structBinder` frames are `≈` (`structNSeq 0 ≡ []`, `wkˡ 0 ≡ id`) and the
ambient `γ ⋯ᵣ weaken* _` is syntactically the same.  What changes is only the
*type* of `0F`: the `BindCtx` head `⟨ u ⟩` with `u ≃ acq ; t` (from
`AcqHeadCtx`) becomes `⟨ t ⟩`.

* The **`BindCtx` half** is routine: `C` must be `cons-acq C₁ ah` (a
  `cons-ret/acq` at width `0` would need `Skips (s₁ ; ret)`), and inverting
  `C₁ : BindCtx (acq ; (s ; end p)) (suc b₁ ∷ B₁) Γ₁` plus `ah : u ≃ acq ; t`
  and cancelling the leading `acq` (`Types.Atoms.atom-drop-front` at `acq`, or
  an `acq` analogue of P2's `msg-cancel`) gives `t ; v ≃ s ; end p`, hence the
  same block with head `⟨ t ⟩`.
* The **typing half** is routine: `Simulation/Support/SplitConfine.acq-confine`
  factors `E ≡ E₀ ⋯ᶠ* ρ⁻`, `P ≡ P₀ ⋯ₚ ρ⁻` through the thinning that misses
  `0F`, so `_⊢⋯ᶠ*⁻¹_/_` / `_⊢⋯ₚ⁻¹_/_` pull them back and `_⊢⋯ᶠ*_` / `_⊢⋯ₚ_`
  push them into `⟨ t ⟩ ⸴ R`; the plugged `` ` 0F `` is `T-Var 0F refl`.
* The **structure half is the blocker**, and it is a real one.  Both sides want
  the *same* `≼` derivation; only the context index changes, so one wants
  `Δ ∶ α ≼ β → Δ′ ∶ α ≼ β` for `Δ = ⟨ u ⟩ ⸴ R`, `Δ′ = ⟨ t ⟩ ⸴ R`.  Inspecting
  `Context/Equivalence._∶_≈′_` and `Context/Subcontext._∶_≼_`, exactly three
  rules read the context:
  - `∥′-dup (U : UnrCx Γ α)` and `≼-∅ (U : UnrCx Γ α)` — transportable: a
    `UnrCx` cannot mention `0F` at all, because `Unr ⟨ s ⟩` is empty
    (`Simulation/Support/HeadConfine.¬unr-handle`), and away from `0F` the two
    contexts agree.
  - `∥′-tm-; (U : MobCx Γ α ⊎ MobCx Γ β) : α ∥ β ≈′ α ; β` — **not**
    transportable.  `Mobile ⟨ s ⟩` unfolds (Types/Predicates:183) to
    `∃ s′. Bounded s′ × s ≃ acq ; s′`, so `Mobile ⟨ u ⟩ ⟺ Bounded t`, while
    `Mobile ⟨ t ⟩` needs `t ≃ acq ; s″`.  In the smallest R-Acq redex
    (`b₁ ≡ 0`, `B₁ ≡ []`) one gets `t ≃ s ; end p`, which *is* `Bounded`, so
    the acq'd handle really is mobile before the step and really is not after
    it.
  So the missing lemma is: *no `∥′-tm-;` step of the LHS derivation is needed
  at a structure mentioning the consumed handle.*  Note `;-≼-∥ : α ; β ≼ α ∥ β`
  (Context/Join) is unconditional, so only the `∥ ↝ ;` direction needs
  mobility, and the frame `structNSeq (suc b₁) = ` 0F ; wk (structNSeq b₁)`
  is exactly the place that wants a `;` at the handle.  This is the declarative
  counterpart of `Simulation/BackwardSoup/GroupOrder`'s `before-mono-≼`.

  **Open question for the paper:** if that lemma is false, R-Acq preservation
  needs a side condition (or `∥′-tm-;` needs to be restricted so that an
  acq-headed handle is not mobile), because a thread that consumes the group's
  later borrows *before* `acq x` typechecks on the left using `Mobile ⟨ acq ; t ⟩`
  and cannot be retyped on the right.  Worth a probe module of the
  `Simulation/BackwardSoup/Examples/` kind before more proof effort is spent.

## Reused (not re-proved)

* `Simulation/Support/Theorems/DropShape.agda`: `discard-handle-≃skip`,
  `drop-handle-≃ret`.
* `Simulation/Support/Theorems/B1VacProbe.agda`: `NoRet`, `new⇒noRet`,
  `noRet-≃`, `noRet-;-fst`, `¬noRet-ret`, `RetTip`, `noRet-front-cons`,
  `retTip-Sc-skips`, `retTip-≃`.
* `Simulation/Support/SplitConfine.agda`: `acq-confine` (for `pres-Acq`).
* `Simulation/Support/HeadConfine.agda`: `¬unr-handle`.
* `Types/AtomUnsnoc.agda`: `atom-;-unsnoc`.
* `Processes/Congruence.agda`: `_/_⊢-≋_`; `Reduction/Expressions.agda`:
  `preservation`; `Reduction/Base.agda`: `⊢[]*⁻¹`, `_⊢⋯ᶠ*⁻¹_/_`, `⊢⟨_[_]*⟩`;
  `Processes/Typed.agda`: `inv-ν`, `inv-∥`, `inv-⟪⟫`, `_⊢⋯ₚ⁻¹_/_`,
  `bindCtx′-≃`, `bindCtx-≃`, `bindCtx⇒chanCtx`; `Terms/Base.agda`: `inv-K`,
  `inv-\``, `inv-·-unr`, `constFnUnr′`, `⊢weakenᵣ`, `⊢weaken*`.
* `Safety/Preservation/Com.agda` (agent P2): `pres-Com`.

## Discrepancies tex vs Agda

1. tex `R-Drop` drops the whole first group `x ‖ B₁`; the Agda `R-Drop` drops
   the head of a first group of arbitrary width `suc b₁`.  The typing forces
   `b₁ ≡ 0` and `B₁ ≢ []` — `bindCtx-drop` derives exactly that: the `last`
   block is refuted (its session is `New`-derived, hence `NoRet`, so its first
   borrow cannot be `≃ ret`) and the two-borrow front block is refuted
   (`retTip-Sc-skips` makes the remainder skip, contradicting the `cons`
   `¬ Skips`).  So the two rules agree on typed processes, but only after that
   lemma.
2. tex `B-Seq` has no `¬ Skips s₂` premise and tex `B-Drop` has no
   `AcqHeadCtx` premise; the Agda `BindCtx.cons-ret/acq` carries both
   (`¬skips₂`, `acqHead`).  `acqHead` is what makes `bindCtx-drop`'s `cons-acq`
   reconstruction go through, and it is also what pins the head type in R-Acq.
3. tex `R-Discard` writes `ν (x B₁) B₂` on the left; the Agda rule works on the
   head of a group of width `suc b₁`, and `b₁ ≡ 0` is *not* forced here (a
   discarded `⟨ skip ⟩` head may be followed by further borrows), so the Agda
   rule is strictly more general than the tex one.  `bindCtx-discard`
   consequently needs no case analysis at all.
4. tex `R-Close` uses two named binders `x`, `y`; the Agda rule fixes both
   groups to `[1]` and weakens the frames by `weaken* 2`, so "the ν
   disappears" is realised by `structBinder [1] ⋯ er 2 ≈ []`.
5. tex `TP-Res` writes `Γ ∥ Γ₁ ∥ Γ₂ ⊢ P`; the Agda `TP-Res` orders the concrete
   context as `(Γ₁ ⸴* Γ₂) ⸴* Γ` and the structure as
   `structBinder B₁ ∥ structBinder B₂ ∥ (γ ⋯ weaken*)`, and `_∥_` is `infixl`,
   so it is really `(Fr₁ ∥ Fr₂) ∥ γwk`.
6. tex `R-Acquire` keeps the binder `x` and only deletes the group separator;
   the Agda rule does the same, but the *type* of `x` changes from
   `⟨ acq ; t ⟩` to `⟨ t ⟩`, which the tex rules do not make visible.  See the
   obstacle section above.
