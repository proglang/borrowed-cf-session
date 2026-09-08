# P3 — preservation cases R-LSplit / R-RSplit

Agent P3.  Files owned: `Preservation/LSplit.agda`, `Preservation/RSplit.agda`,
`Preservation/Splits/`, this file.

## Lemmas

| name | statement (one line) | status | file |
|---|---|---|---|
| `¬skips-seqˡ/ʳ`, `¬skips-ret`, `¬skips-acq` | `¬ Skips` propagates through `_;_`, `_ ; ret`, `acq ; _` | proved | Splits/Chain.agda |
| `Ins T T₁ T₂ Γ Γ′` | cast-free witness: Γ′ is Γ with one `T` entry replaced by `T₁ , T₂` | proved (data) | Splits/Chain.agda |
| `mkIns` | split a `Ctx (q + suc k)` at offset q and insert; returns the old entry | proved | Splits/Chain.agda |
| `ins-++ʳ`, `ins-head` | `Ins` is stable under appending a tail; head analysis | proved | Splits/Chain.agda |
| `chain-lsplit` | `¬ Skips t₂ → Ins ⟨t₁;t₂⟩ ⟨t₁⟩ ⟨t₂⟩ Γ Γ′ → BindCtx′ s Γ → BindCtx′ s Γ′` | proved | Splits/Chain.agda |
| `InsR T T₁ T₂ Γ Γ₁ Γ₂` | as `Ins`, but the chain is CUT between the two new entries | proved (data) | Splits/Chain.agda |
| `mkInsR`, `insR-++ʳ`, `insR-head`, `insR-flat` | builder and plumbing for `InsR` | proved | Splits/Chain.agda |
| `insR-acqHead` | the new group of an `InsR … ⟨acq ; t₂⟩ …` always has an acq head | proved | Splits/Chain.agda |
| `chain-rsplit` | `InsR ⟨t₁;t₂⟩ ⟨t₁;ret⟩ ⟨acq;t₂⟩ Γ Γ₁ Γ₂ → BindCtx′ s Γ → ∃ u v. u;v ≃ s ∧ ¬Skips v ∧ BindCtx′ (u;ret) Γ₁ ∧ BindCtx′ (acq;v) Γ₂` | proved | Splits/Chain.agda |
| `++-inj`, `vsplit`, `0<len`, `acqHead-cong` | vector/list plumbing | proved | Splits/Group.agda |
| `Same B₁ Γc Γc′ Γ Γ′` | Γ and Γ′ agree on the first `|B₁|` binder groups; cast-free | proved (data) | Splits/Group.agda |
| `same-nil⁻¹`, `same-cons⁻¹`, `mkSame` | inversion and construction of `Same` | proved | Splits/Group.agda |
| `acqHead-lsplit` / `acqHead-rsplit` | the `AcqHeadCtx` premise survives the split (via `acq-;-split` and `¬ Skips t₁`) | proved | Splits/Group.agda |
| **`bindCtx-lsplit`** (= paper's BindCtxLsplit) | `¬Skips t₁ → ¬Skips t₂ → Ins ⟨t₁;t₂⟩ ⟨t₁⟩ ⟨t₂⟩ Γg Γg′ → BindCtx s (B₁ ++ w ∷ B₂) Γ → Same B₁ … Γ Γ′ → BindCtx s (B₁ ++ w′ ∷ B₂) Γ′` | **proved** | Splits/Group.agda |
| **`bindCtx-rsplit`** (= paper's BindCtxRsplit) | as above with `InsR ⟨t₁;t₂⟩ ⟨t₁;ret⟩ ⟨acq;t₂⟩ Γg Γg₁ Γg₂` and result `BindCtx s (B₁ ++ w₁ ∷ w₂ ∷ B₂) Γ′` | **proved** | Splits/Group.agda |
| `lsplit-bindCtx` | applies BindCtxLsplit at the position `𝐒.atk (q ↑ʳ 0F)` names: from `Γ₁ ﹫ pos ≡ ⟨ t ⟩` and `t ≃ t₁ ; t₂` build `Γ₁′` with `BindCtx s₀ (B₁ ++ (q + suc (suc b₁)) ∷ B₂) Γ₁′` plus the two new lookups | proved | Splits/Redex.agda |
| `rsplit-bindCtx` | ditto for `B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂`, new lookups `⟨ t₁ ; ret ⟩` and `⟨ acq ; t₂ ⟩` | proved | Splits/Redex.agda |
| `atk-lookup` | `((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ 𝐒.atk (q ↑ʳ 0F) ≡ Γ₁ ﹫ (flat position sum B₁ + q)` | proved (twice, one per file) | LSplit.agda / RSplit.agda |
| `⊢ᴮ-lsplit′` / `⊢ᴮ-rsplit′` | `⊢ᴮ` for the exact width shapes `q + suc b ↦ q + suc (suc b)` resp. `q + suc b ↦ (q + 1), suc b` | proved | LSplit.agda / RSplit.agda |
| **`lsplit-binder`** | from `Γ ; γ ⊢ₚ` the R-LSplit LHS produce `s₀, pol, t₁, t₂, Γ₁′, New s₀, ⊢ᴮ (new list), BindCtx (s₀ ; end pol) (new list) Γ₁′` and the two handle lookups | **proved** | LSplit.agda |
| **`rsplit-binder`** | same for R-RSplit | **proved** | RSplit.agda |
| `pres-LSplit` | `ChanCx Γ → Γ ; γ ⊢ₚ LHS(R-LSplit) → Γ ; γ ⊢ₚ RHS(R-LSplit)` | NOT DONE — see "What is missing" | Preservation/LSplit.agda |
| `pres-RSplit` | `ChanCx Γ → Γ ; γ ⊢ₚ LHS(R-RSplit) → Γ ; γ ⊢ₚ RHS(R-RSplit)` | NOT DONE — see "What is missing" | Preservation/RSplit.agda |

All five delivered files (`Splits/Chain.agda`, `Splits/Group.agda`, `Splits/Redex.agda`,
`LSplit.agda`, `RSplit.agda`) load with **zero goals, zero unsolved metas, no postulates,
no TERMINATING pragmas**.

## What is missing for `pres-LSplit` / `pres-RSplit`

The binder-context side (the hard bookkeeping) is finished.  What remains is the
term/renaming side:

1. **Strengthening round trip.**  `E` and `P` must be re-typed in the NEW binder context,
   where the slot of the consumed handle has changed type (`⟨ t ⟩ ↦ ⟨ t₁ ⟩` resp.
   `⟨ t₁ ; ret ⟩`).  A plain typed renaming for `𝐒.lwk` / `𝐒.rwk` does NOT exist, because
   `_⊢⋯ₚ_` demands lookup agreement at *every* variable.  The route is
   `Simulation.Support.SplitConfine.lsplit-confine` / `rsplit-confine`, which give
   `k`, `ρ⁻ : k →ᵣ N` with `∀ y → ρ⁻ y ≢ handle`, and `E ≡ E₀ ⋯ᶠ* ρ⁻`, `P ≡ P₀ ⋯ₚ ρ⁻`.
   Then: type `E₀`/`P₀` in `Γsmall = tabulate (Γbig ﹫_ ∘ ρ⁻)` via `_⊢⋯ᶠ*⁻¹_/_` and
   `_⊢⋯ₚ⁻¹_/_` (needs `Inj ρ⁻`), and push them forward along `ρ⁺ = 𝐒.lwk ∘ ρ⁻`.
2. **The context lemma for `ρ⁺`:** `∀ z → z ≢ handle → Γbig′ ﹫ 𝐒.lwk z ≡ Γbig ﹫ z`
   (and the `rwk` analogue).  `Simulation.Support.Theorems.SplitsLQ` (`dlwkq`,
   `dlwkq-lo/hi`, `𝐒lwkq-lo/hi`, `P1q..P3q`) has the matching Fin arithmetic.
   `Splits/Group.agda` would then need the companion of `same-lookupˡ/ʳ` for the
   *prefix* positions (`y ↑ˡ _` instead of `sum B₁ ↑ʳ y`), which I did not prove.
3. **The structure inequality** for `TP-Res` on the new group list: relate
   `structBinder (B₁ ++ (q + suc (suc b₁)) ∷ B₂)` to `structBinder (B₁ ++ (q + suc b₁) ∷ B₂)`
   and discharge `TP-Weaken`.  This is the `𝒢[…] ∥ Γ_b ≼ Γ ∥ 𝒢′[…] ∥ Γ₂` step of the
   handwritten sketch; none of it is mechanised yet.
4. The final `TP-Res / TP-Par / TP-Expr` assembly, with `T-Pair par par (T-Var …) (T-Var …)`
   for `(` x₁) ⊗ (` x₂)` — the two `T-Var` premises are exactly the lookup equations that
   `lsplit-binder` / `rsplit-binder` already return.

## Reused (never edited)

- `BorrowedCF.Types.AtomCons.acq-;-split` — pins the group's `acq` to the front of one factor.
- `BorrowedCF.Types.AtomUnsnoc.atom-;-unsnoc` — pulls the trailing `ret` out of the second
  half of an r-split group.
- `BorrowedCF.Processes.Typed.bindCtx-inv-cons`, `bindCtx′-≃`.
- `BorrowedCF.Reduction.Base.chanCx-lookup`, `⊢[]*⁻¹`; `Terms.Base.{inv-K, inv-·-unr, inv-`,
  constFnUnr′}`; `Processes.Typed.{inv-ν, inv-∥, inv-⟪⟫, bindCtx⇒chanCtx, ⊢ᴮ-lsplit}`;
  `Terms.SplitRenamings.atk`.
- NOT imported (so nothing under `Simulation/` is type-checked by my files): the planned uses
  are `Simulation.Support.SplitConfine.{lsplit-confine,rsplit-confine}` (E and P factor
  through a renaming that misses the consumed handle) and
  `Simulation.Support.Theorems.SplitsLQ` (`dlwkq`, `𝐒lwkq-lo/hi`).  `Processes.Renamings.⊢wkRSplit`
  turned out NOT to be usable for R-RSplit as it stands: it keeps the consumed handle's OLD
  type at the shifted position (head of `Γb`) and puts a free `T` at the new position, whereas
  the rule needs `⟨ s ; ret ⟩` at the old position and `⟨ acq ; s′ ⟩` at the shifted one.

## Notes / discrepancies (tex vs Agda)

1. tex `CT-LSplit`/`CT-RSplit` require only `¬(S₂ ≃ Skip)`; Agda's `` `lsplit ``/`` `rsplit ``
   also require `¬ Skips s₁`.  The extra premise is *needed*: without `¬ Skips t₁` the
   `AcqHeadCtx` premise of `B-Seq`/`cons-ret/acq` cannot be re-established after the split
   (`acqHead-lsplit`/`acqHead-rsplit` use exactly `¬ Skips t₁`).
2. tex `B-Seq`/`B-Drop` lack Agda's `¬skips₂` and `acqHead` premises on
   `cons-ret/acq` / `cons-acq`.  Both are discharged here: `¬skips₂` from the split
   constant's `¬ Skips s′`, `acqHead` from `insR-acqHead` / `acq-;-split`.
3. The paper's BindCtxRsplit is stated with a context pattern `𝒢[·]`; the mechanised version
   replaces the pattern by the two inductive relations `Same` (prefix groups) and
   `Ins`/`InsR` (position inside the group).  This keeps every `sum-++`/`+-assoc` transport
   out of the proofs.

---

# P3b — continuation of P3 (assembling `pres-LSplit` / `pres-RSplit`)

## New files / lemmas

| name | statement (one line) | status | file |
|---|---|---|---|
| `lookup-toℕ` | lookup only depends on `Fin.toℕ` | proved | Splits/Chain.agda |
| `Agree p Γ Γ′` | Γ′ is Γ with one slot inserted after position `p`; entries at positions `≠ p` agree (below `p` at the same index, above `p` one further right) | proved (def) | Splits/Chain.agda |
| `agree-here`, `agree-suc`, `agree-++ˡ` | base / one-step / prefix lifting of `Agree` | proved | Splits/Chain.agda |
| `mkIns` / `mkInsR` (extended) | now also return `∀ Γr → Agree q (Γ ⸴* Γr) (Γ′ ⸴* Γr)` | proved | Splits/Chain.agda |
| `same-agree` | `Same B₁ … Γ Γ′ → Agree p Γc Γc′ → Agree (sum B₁ + p) Γ Γ′` | proved | Splits/Group.agda |
| `lsplit-bindCtx` / `rsplit-bindCtx` (extended) | now also return `Agree (sum B₁ + q) Γ₁ Γ₁′` | proved | Splits/Redex.agda |
| `split3` | structural three-way split of a ν-body variable | proved | Splits/Shift.agda |
| `toℕ-dh` | the consumed handle sits at flat position `sum B₁ + q` | proved | Splits/Shift.agda |
| **`lsplit-lookup`** | `Agree (sum B₁+q) Γ₁ Γ₁′ → z ≢ handle → ((Γ₁′ ⸴* Γ₂) ⸴* Γ) ﹫ 𝐒.lwk z ≡ ((Γ₁ ⸴* Γ₂) ⸴* Γ) ﹫ z` | **proved** | Splits/Shift.agda |
| **`rsplit-lookup`** | ditto for `𝐒.rwk` | **proved** | Splits/Shift.agda |
| `⋯ᵣᵣ`, `⋯ᵣₛ`, `⋯ᵣ⇒ₛ`, `⋯ₛ-cong` | Struct traversal plumbing | proved | Splits/Struct.agda |
| `seqOf`, `seqOf-cong`, `nseq-seqOf` | `structNSeq w ⋯ₛ θ` is the explicit `;`-chain of the `θ`-images | proved | Splits/Struct.agda |
| `seqOf-lsplit` | one chain entry expands into two sequential entries | proved | Splits/Struct.agda |
| `seqOf-rsplit` | the chain is cut, the entry becomes two parallel entries (≼ via `≼-wk`) | proved | Splits/Struct.agda |
| **`sb-lsplit`** | `structBinder (B₁ ++ (q+suc b)∷B₂) ⋯ₛ θ ≈ structBinder (B₁ ++ (q+suc(suc b))∷B₂) ⋯ₛ g` under the three positional clauses | **proved** | Splits/Struct.agda |
| **`sb-rsplit`** | `… ⋯ₛ θ ≼ structBinder (B₁ ++ (q+1)∷suc b∷B₂) ⋯ₛ g` | **proved** | Splits/Struct.agda |
| `mk-thin′` | `mk-thin` of `Simulation.Support.Strengthen` plus injectivity of the thinning | proved | Splits/Confine.agda |
| `lsplit-confine′` / `rsplit-confine′` | `Simulation.Support.SplitConfine.{lsplit,rsplit}-confine` plus `Inj ρ⁻` | proved | Splits/Confine.agda |

## Route actually taken (differs from P3's sketch on step 3)

P3's step 3 ("structure inequality via `structBinder` of the new list, then
`TP-Weaken`") is done through a **struct substitution** rather than a renaming.
Let `θ` send the consumed handle to `(` x₁) ; (` x₂)` (L-split) resp.
`(` x₁) ∥ (` x₂)` (R-split) and every other variable `z` to `` ` (lwk z) ``.
Then

  * `θ ∶ Γbig ⇒ Γbig′` holds for the *implication* reading of `⇒` — only `Unr`
    and `Mobile` have to be transported.  `Unr ⟨t⟩` is always false
    (`¬unr-handle`); `Mobile` transports for R-RSplit (`mob-rsplit`) and needs
    the extra premise for R-LSplit (see the finding below);
  * `≼-⋯` therefore transports the whole old inequality `δ ≼ γbig` to
    `δ ⋯ₛ θ ≼ γbig ⋯ₛ θ`;
  * `sb-lsplit` / `sb-rsplit` say `γbig ⋯ₛ θ ≼ γbig′`.

This avoids ever needing `𝒫`-level "pull out" lemmas, which would have relaxed
`;` to `∥` in the wrong direction.

## IMPORTANT FINDING — R-LSplit loses `Mobile`, R-RSplit does not

`Mobile ⟨ s ⟩` unfolds to `∃ s′. Bounded s′ × s ≃ acq ; s′` (Types/Predicates.agda:183),
and `MobCx` is **atom-wise** (`AllCx Mobile`).  The structure equivalence has

    ∥′-tm-; : MobCx Γ α ⊎ MobCx Γ β → Γ ∶ α ∥ β ≈′ α ; β

so a *mobile* handle may be used in parallel with a resource that the binder
offers only sequentially.  Transporting the ν-body inequality across a split
therefore needs the mobility of the consumed handle to survive.

* **R-RSplit: it survives.**  If `t ≃ acq ; v` with `Bounded v` and `t ≃ t₁ ; t₂`
  with `¬ Skips t₁`, `¬ Skips t₂`, then `acq-;-split` gives `t₁ ≃ acq ; h′` and
  `h′ ; t₂ ≃ v`; hence `Bounded t₂` and
  `Mobile ⟨ t₁ ; ret ⟩` (witness `h′ ; ret`, `Bounded` by `-;₂ ret`) and
  `Mobile ⟨ acq ; t₂ ⟩` (witness `t₂`).  Mechanised as `mob-rsplit` (RSplit.agda).
  `pres-RSplit` therefore needs no extra premise.

* **R-LSplit: it does NOT survive.**  The two halves are `⟨ t₁ ⟩` and `⟨ t₂ ⟩`.
  `Mobile ⟨ t₁ ⟩` would need `Bounded h′`, which is exactly the disjunct
  `bounded-;⁻` rules out (we only get `Bounded t₂`), and `Mobile ⟨ t₂ ⟩` would need
  `t₂` acq-headed.  Concretely `t = acq ; (msg ‼ T ; ret)`, `t₁ = acq ; msg ‼ T`,
  `t₂ = ret` satisfies every premise of `` `lsplit `` and has `Mobile ⟨ t ⟩` but
  neither `Mobile ⟨ t₁ ⟩` nor `Mobile ⟨ t₂ ⟩`.
  With such a handle the RHS is genuinely untypable: for a group `⟨t⟩,⟨c⟩` with a
  thread doing the lsplit and a parallel `P` using `c`, the LHS needs
  `` ` h ∥ ` c ≼ ` h ; ` c `` (fine, `h` mobile), while the RHS needs
  `` (` x₁ ; ` x₂) ∥ ` c ≼ ` x₁ ; ` x₂ ; ` c ``, and no ≼/≈ rule produces a `;`
  at the top from a `∥` without `MobCx` on one side.
  **`pres-LSplit` therefore carries one extra premise**
  `¬mob : ∀ u → ¬ Mobile ⟨ s ; u ⟩` (`s` is the rule's own parameter and the
  consumed handle has type `⟨ t ⟩` with `t ≃ s ; t₂`, so this is exactly
  "the consumed handle is not mobile").  This premise is a genuine restriction, not an artefact of
  the mechanisation; it points at either `MobCx` being too coarse (it cannot see
  that `` ` x₁ ; ` x₂ `` is jointly the mobile resource `` ` h `` was) or at a
  missing side condition on `CT-LSplit` in the paper.

## Delivered lemmas (P3b)

| name | statement (one line) | status | file |
|---|---|---|---|
| `θL` / `θL-h` / `θL-≢` | struct substitution sending the consumed handle to `(` x₁) ; (` x₂)` and every other variable along `lwk` | proved | LSplit.agda |
| `¬unr-handle` | `¬ Unr ⟨ s ⟩` | proved | LSplit.agda |
| `mob-lsplit-absurd` | `t ≃ t₁ ; t₂ → (∀ u → ¬ Mobile ⟨ t₁ ; u ⟩) → ¬ Mobile ⟨ t ⟩` | proved | LSplit.agda |
| `γbigL` | the ν-binder structure `structBinder Bl ⋯ ∥ structBinder B ⋯ ∥ γ ⋯` of `TP-Res` | definition | LSplit.agda |
| **`γbig-lsplit`** | `γbigL Bl B γ ⋯ₛ θL ≼ γbigL Bl′ B γ` | **proved** | LSplit.agda |
| **`θL-⇒`** | `θL ∶ Γbig ⇒ Γbig′` (needs the `¬mob` premise at the handle) | **proved** | LSplit.agda |
| **`pres-LSplit`** | `ChanCx Γ → (∀ u → ¬ Mobile ⟨ s ; u ⟩) → Γ ; γ ⊢ₚ LHS(R-LSplit) → Γ ; γ ⊢ₚ RHS(R-LSplit)` | **proved** | LSplit.agda |
| `θR` / `θR-h` / `θR-≢` | the R-RSplit struct substitution (handle ↦ `(` x₁) ∥ (` x₂)`) | proved | RSplit.agda |
| `toℕ-dhR₁` / `toℕ-dhR₂` | the two new r-split handles sit at flat positions `sum B₁ + q` and `suc (sum B₁ + q)` | proved | RSplit.agda |
| **`γbig-rsplit`** | `γbigL Bl B γ ⋯ₛ θR ≼ γbigL ((B₁ ++ (q+1) ∷ suc b₁ ∷ B₂)) B γ` | **proved** | RSplit.agda |
| **`mob-rsplit`** | `Mobile ⟨ t ⟩ → Mobile ⟨ t₁ ; ret ⟩ × Mobile ⟨ acq ; t₂ ⟩` | **proved** | RSplit.agda |
| **`θR-⇒`** | `θR ∶ Γbig ⇒ Γbig′` (no side condition) | **proved** | RSplit.agda |
| **`pres-RSplit`** | `ChanCx Γ → Γ ; γ ⊢ₚ LHS(R-RSplit) → Γ ; γ ⊢ₚ RHS(R-RSplit)` | **proved, no extra premise** | RSplit.agda |

## Files delivered (P3b), all loading with zero goals / zero unsolved metas / no postulates

- `Preservation/Splits/Chain.agda`   (extended: `Agree`, `agree-here/suc/++ˡ`, `mkIns`/`mkInsR` return `Agree`)
- `Preservation/Splits/Group.agda`   (extended: `same-agree`)
- `Preservation/Splits/Redex.agda`   (extended: both `*-bindCtx` return `Agree (sum B₁ + q) Γ₁ Γ₁′`)
- `Preservation/Splits/Shift.agda`   (NEW: `split3`, `toℕ-dh`, `lsplit-lookup`, `rsplit-lookup`)
- `Preservation/Splits/Struct.agda`  (NEW: `seqOf`, `seqOf-lsplit/rsplit`, `sb-lsplit/rsplit`, `σ∘`, `𝓅∘`, `join-unitʳ`)
- `Preservation/Splits/Confine.agda` (NEW: `mk-thin′`, `lsplit-confine′`, `rsplit-confine′` — `SplitConfine` + `Inj ρ⁻`)
- `Preservation/LSplit.agda`, `Preservation/RSplit.agda`

Imports from `Simulation/` (all with explicit `using` lists):
`Support.Theorems.SplitsLQ` (`dlwkq`,`dlwkq-lo/hi`,`P1q`,`P2q`,`P3q`),
`Support.Theorems.SplitsRQ` (`drwkq`,`drwkq-lo/hi`,`P1rq`,`P2rq`,`P3rq`),
`Support.FrameRename` (`⋯ᶠ*-fuse`), and (inside `Splits/Confine.agda`)
`Support.{Base,Confine,InvFrame,Strengthen,HandleCount}`.  This transitively pulls in the
sanctioned `funext` postulate of `Simulation/Support/Base.agda`; nothing else.

Performance: `LSplit.agda` and `RSplit.agda` each check in ~3 min at ≈4 GB RSS with the
interfaces cached.  They do use one `with … , refl , … ← *-confine′ …` that rewrites the frame
`E` and the parallel `P` in the goal — the pattern AGENTS.md warns about — but only ONE such
`refl`, and all implicit arguments of `*-confine′` are supplied explicitly
(`{γ = γ} {B₁ = B₁} … {E = E} {P = P}`), without which `E` is not inferable through `_[_]*`.

---

# P3c — removing the `¬mob` premise from `pres-LSplit`

Agent P3c.  Files owned: `Preservation/LSplit/*.agda` (new directory), this
section.  `LSplit.agda` is touched ONLY to rename P3b's lemma to
`pres-LSplit-immobile`; `Preservation.agda` only to drop the postulate.

## Corrections to the brief, found on reading the code (read these first)

1. **`Mobile` is NOT decidable.**  `Mobile ⟨ s ⟩ = ∃ s′. Bounded s′ × s ≃ acq ; s′`
   (`Types/Predicates.agda:183`) quantifies over sessions modulo `≃`;
   `Types/Predicates.tpred?` only lifts a decision procedure for the session
   part, and none exists.  So the final case split is NOT on `Mobile`.  It is
   a syntactic split on the two rule indices `q` and `b₁`:

   | clause | route |
   |---|---|
   | `q = suc _` | handle is INTERIOR to its group ⇒ immobile ⇒ P3b-style |
   | `q = 0`, `b₁ = suc _` | group width ≥ 2 at offset 0 ⇒ immobile ⇒ P3b-style |
   | `q = 0`, `b₁ = 0` | group width 1 ⇒ `zap` route, needs NO mobility fact |

   Pattern matching on `q`/`b₁` avoids every `subst` over the process: in the
   third clause `q + suc b₁` is literally `1` and `q + suc (suc b₁)` is `2`.

2. **P3b's premise is strictly stronger than `¬ Mobile` of the handle.**
   `∀ u → ¬ Mobile ⟨ s ; u ⟩` is *equivalent* to "`s` is not acq-headed":
   `Bounded (h ; ret)` holds for every `h`, so as soon as `s ≃ acq ; h` the
   instance `u := ret` gives `Mobile ⟨ s ; ret ⟩`.  The head of a NON-FIRST
   group IS acq-headed (`Crux.laterGroup-head-acq`), so P3b's lemma is NOT
   applicable in the clause `q = 0, b₁ = suc _`, even though the handle there
   is immobile.  Consequence: the immobile assembly has to be restated with
   the premise `¬ Mobile ⟨ t ⟩` (`t` the handle's own type), which cannot be
   phrased over the rule's `s`.  It is therefore restated in
   `LSplit/Immobile.agda` with the SHAPE premise (`0 < q ⊎ 0 < b₁`) and the
   `¬ Mobile ⟨ t ⟩` fact derived internally.  P3b's `pres-LSplit-immobile`
   stays in `LSplit.agda` unchanged but is no longer on the critical path.

3. **The shape lemma needs `Simulation/BackwardSoup/`** — `Position.agda`,
   `Position/Crux.agda`, `GroupOrder.agda`.  All three have CACHED interfaces
   in `agda/_build`, load with 0 goals and no pragma, so the import is cheap.
   Reused: `GroupOf`/`groupIndex`/`groupOffset`/`groupWidth`,
   `Position.first-group-¬mobile`, `Crux.mobile-head-alone`,
   `Crux.nonFirstGroup-interior-noAcq`, `GroupOrder.{NoAcq, ¬mobile-noAcq,
   new-end⇒noAcq, noAcq-;-snd, noAcq-≃}`.

4. **P3b's "counterexample" is refuted, but not by a single lemma.**  Its LHS
   (mobile handle sharing a group with a second handle `c`) needs group width
   ≥ 2 with a MOBILE handle in it.  `Crux.mobile-head-alone` (offset 0) and
   `Crux.nonFirstGroup-interior-noAcq` + `Position.first-group-¬mobile`
   (offset > 0) together say no such configuration is typable.

## Lemmas

| name | statement (one line) | status | file |
|---|---|---|---|
| `dpos` | flat position `sum B₁ + q` of the consumed handle in the first binder context | **proved** | LSplit/Shape.agda |
| `groupAt` | the `GroupOf (B₁ ++ (q+suc b₁) ∷ B₂) dpos` navigation, with `groupOffset ≡ q`, `groupWidth ≡ q + suc b₁`, `groupIndex ≡ length B₁` | **proved** | LSplit/Shape.agda |
| `laterInterior-noAcq` | re-derivation of `Crux`'s PRIVATE `laterGroup-interior-noAcq` from the public `nonFirstGroup-interior-noAcq` | **proved** | LSplit/Shape.agda |
| `handle-interior-¬mobile` | `0 < q → ¬ Mobile (Γ₁ ﹫ dpos …)` | **proved** | LSplit/Shape.agda |
| `handle-wide-¬mobile` | `q ≡ 0 → 0 < b₁ → ¬ Mobile (Γ₁ ﹫ dpos …)` | **proved** | LSplit/Shape.agda |
| `θL-⇒′` | `θL ∶ Γbig ⇒ Γbig′` from `¬ Mobile ⟨ t ⟩` instead of P3b's `∀ u → ¬ Mobile ⟨ s ; u ⟩` | **proved** | LSplit/Immobile.agda |
| `pres-LSplit-shape` | R-LSplit preservation under `0 < q ⊎ 0 < b₁` (no mobility premise) | **proved** | LSplit/Immobile.agda |
| `zapL` / `zapL-⇒` | `dh ↦ []`, `z ↦ ` (lwk z)`; a legal `⇒` with NO side condition | **proved** | LSplit/Mobile.agda |
| `sb-zap` | `d ∥ (structBinder (B₁ ++ 1 ∷ B₂) ⋯ₛ z) ≈ structBinder (B₁ ++ 2 ∷ B₂) ⋯ₛ g` | **proved** | LSplit/Struct.agda |
| `γbig-zap` | `((` x₁) ; (` x₂)) ∥ (γbigL Bl B γ ⋯ₛ zapL) ≈ γbigL Bl′ B γ` | **proved** | LSplit/Mobile.agda |
| `pres-LSplit-mobile` | R-LSplit preservation for `q ≡ 0`, `b₁ ≡ 0` (mobility irrelevant) | **proved** | LSplit/Mobile.agda |
| `pres-LSplit` | premise-free R-LSplit preservation | **proved** | LSplit/Total.agda |

`pres-LSplit` cannot live in `LSplit.agda` (it must call `LSplit/Shape.agda`
and `LSplit/Mobile.agda`, both of which import `LSplit.agda` for `θL`,
`γbigL`, `atk-lookup`, `lsplit-confine′`) — that would be an import cycle.  It
goes into `LSplit/Total.agda` and `Preservation.agda` imports it from there.

Status 2026-09-08: `LSplit/Shape.agda` (10 s) and `LSplit/Immobile.agda` (34 s) load with zero goals, zero unsolved metas, no postulates.

## Delivered (all load with zero goals, zero unsolved metas, no postulates, no pragmas)

| file | lines | check time (cached imports) |
|---|---|---|
| `Preservation/LSplit/Shape.agda` | 165 | 10 s |
| `Preservation/LSplit/Struct.agda` | 131 | 8 s |
| `Preservation/LSplit/Immobile.agda` | 172 | 34 s |
| `Preservation/LSplit/Mobile.agda` | 297 | 31 s |
| `Preservation/LSplit/Total.agda` | 69 | 12 s |

`LSplit.agda` was touched only to rename `pres-LSplit` to `pres-LSplit-immobile`
(and to fix the two doc comments that referred to the old name); it re-checks in
33 s.  `Safety/Preservation.agda` lost its last `postulate` block and now reads

```
open import BorrowedCF.Safety.Preservation.LSplit.Total using (pres-LSplit)
…
preservationₚ Γ-S ⊢P (R-LSplit {B₁ = B₁} … {E = E}) = pres-LSplit {B₁ = B₁} … Γ-S ⊢P
```

and checks in 52 s.  **`preservationₚ` is now postulate-free for every rule.**

Imports from `Simulation/` added by P3c (all cached in `agda/_build`, all with
explicit `using` lists): `BackwardSoup.GroupOrder`
(`NoAcq`, `¬mobile-noAcq`, `new-end⇒noAcq`, `noAcq-;-snd`, `noAcq-≃`),
`BackwardSoup.Position` (`GroupOf`, `head-group`, `next-group`, `groupIndex`,
`groupOffset`, `groupWidth`, `first-group-¬mobile`),
`BackwardSoup.Position.Crux` (`mobile-head-alone`,
`nonFirstGroup-interior-noAcq`).  Nothing else new.

## Duplication (declared)

`LSplit/Immobile.agda`'s `pres-LSplit-shape` and `LSplit/Mobile.agda`'s
`pres-LSplit-mobile` both repeat P3b's assembly (inversion chain, `lsplit-confine′`
round trip, `TP-Res`/`TP-Par`/`TP-Expr`).  They differ ONLY in the structure step
(`𝐂.≼-⋯` along `θL` vs along `zapL`, plus `pat-hole-≼`), which depends on
variables bound inside the `with` chain and therefore cannot be abstracted out
without threading a dozen local hypotheses.  `LSplit/Shape.agda`'s
`laterInterior-noAcq` repeats `Crux`'s PRIVATE `laterGroup-interior-noAcq`
(3 clauses, verbatim).
