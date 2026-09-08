# P2 — R-Com and R-Choice preservation (status: BOTH DONE)

Owner: agent P2.  Files owned: `Safety/Preservation/Com.agda`,
`Safety/Preservation/Choice.agda`, `Safety/Preservation/Support/`,
`Safety/Preservation/Choice/`, `Safety/Preservation/SelfTest.agda`,
this file.  (`Safety/Preservation/Com/` is empty — the R-Com helpers all
turned out to be reusable, so they live in `Support/`.)

Everything below type-checks with `agda-check`, **zero goals, zero unsolved
metas, no postulates, no `TERMINATING`, no `--allow-unsolved-metas`**.

## Two gotchas for everybody

1. Every `_;_` operator in this development (session types, `Struct`, `Tm`,
   `Skips`, the judgements `_;_⊢_∶_∣_` and `_;_⊢ₚ_`, `≃-;`, `;-unit₁`, …) is
   spelled with **U+037E GREEK QUESTION MARK**, not with an ASCII semicolon.
   An ASCII `;` in a pattern gives a bare `[ParseError]` with no useful text.
2. Calling `pres-Com` needs the two frames named:
   `preservationₚ Γ-S ⊢P (R-Com {E₁ = E₁} {E₂ = E₂} V) =
      pres-Com {E₁ = E₁} {E₂ = E₂} Γ-S V ⊢P`.
   The bare `pres-Com Γ-S V ⊢P` leaves `E₁`, `E₂` unsolved, because `E [ e ]*`
   is a stuck application and the unifier cannot invert it.  `pres-Choice`
   takes `E₁ E₂ i` explicitly, so `pres-Choice Γ-S E₁ E₂ i ⊢P` works as is.
   `Safety/Preservation/SelfTest.agda` contains a compiled `preservationₚ`
   clause for both rules, so it is the copy-paste source for the assembler.

## Deliverables

| lemma | statement | status | file |
|---|---|---|---|
| **`pres-Com`** | `ChanCx Γ → (V : Value e) → Γ ; γ ⊢ₚ LHS(R-Com V) → Γ ; γ ⊢ₚ RHS` | **proved** | `Com.agda` |
| **`pres-Choice`** | `ChanCx Γ → ∀ E₁ E₂ i → Γ ; γ ⊢ₚ LHS(R-Choice E₁ E₂ i) → Γ ; γ ⊢ₚ RHS` | **proved** | `Choice.agda` |
| `partial` | a compiled `preservationₚ` clause for `R-Com` and `R-Choice` | proved | `SelfTest.agda` |

## Reusable support (importable by P3/P4; do not edit)

`Safety/Preservation/Support/` — generic session-type and de Bruijn theory.

| lemma | statement | file |
|---|---|---|
| `dual-⋯ₛ` | `dual (s ⋯ ϕ) ≡ dual s ⋯ (dual ∘ ϕ)` for a session substitution | `Support/Dual.agda` |
| `dual-unfold` | `dual (unfold s) ≡ unfold (dual s)` | `Support/Dual.agda` |
| `≃-dual` | `s₁ ≃ s₂ → dual s₁ ≃ dual s₂` — **missing from `Types/*`** | `Support/Dual.agda` |
| `≃-consM` | `_≃_` transports `Cons (msg p T) w z`; the payload changes only up to `≃` (the `msg` case that `Types.AtomCons.≃-cons` excludes) | `Support/ConsMsg.agda` |
| `cons-atom-skip` | `Atom b → Cons a b z → b ≡ a × z ≡ skip` | `Support/ConsMsg.agda` |
| `msg-;-atom` | `Atom b → b ≃ msg p T ; t → ∃[ T′ ] b ≡ msg p T′` | `Support/ConsMsg.agda` |
| `msg-;-cons` | the `msg` companion of `Types.AtomCons.atom-;-cons` | `Support/ConsMsg.agda` |
| `msg-cancel` | `msg p T₁ ; s₁ ≃ msg p T₂ ; s₂ → T₁ ≃ T₂ × s₁ ≃ s₂` | `Support/ConsMsg.agda` |
| `com-split` | `New s → msg ‼ T₁ ; s₁ ≃ s ; end p → msg ⁇ T₂ ; s₂ ≃ dual s ; end (dualPol p) → ∃ s*. New s* × T₁ ≃ T₂ × s₁ ≃ s* ; end p × s₂ ≃ dual s* ; end (dualPol p)` | `Support/MsgSplit.agda` |
| `BrnV` / `≃-brnv` | branch-projection view: `BrnV p i w z` = "`w` starts with a `p`-choice whose `i`-th branch, continuation appended, is `z`"; `_≃_` transports it | `Support/BrnView.agda` |
| `brnv-unique` | the branch is determined up to `≃` | `Support/BrnView.agda` |
| `brnv-unfold(⁻¹)`, `brnv-⋯(ᵣ⁻¹)`, `brnv⋯⇒brnv`, `brnv-⋯⁻¹` | the μ-unfolding machinery, mirroring `Types.AtomCons` | `Support/BrnView.agda` |
| `brn-cancel`, `brn-cancel₀` | `brn p X₁ X₂ ; X ≃ brn p Y₁ Y₂ ; Y → Xᵢ ; X ≃ Yᵢ ; Y` — **new session-type theory, nothing comparable in `Types/*`** | `Support/BrnView.agda` |
| `brnv-dual`, `brnv-new` | `BrnV` commutes with `dual`, preserves `New` | `Support/BrnView.agda` |
| `⋯ᵣ∘`, `⋯ᵣ⋯ₛ`, `⋯ₛ≗ᵣ`, `⋯ᵣ-cong` | four `Struct` traversal lemmas by direct induction (no Kit instance search) | `Support/ComWeaken.agda` |
| `wkₚ-A/B/C` | where `wkₚ a c` sends first-block / second-block / ambient variables (transcribed from the private copies in `Simulation.ForwardSoup.Local.Com`) | `Support/ComWeaken.agda` |
| `split3` | three-way view of `𝔽 (a + c + k)` | `Support/ComWeaken.agda` |
| `del`, `del-A/B/C/x/y`, `del-wkₚ`, `⋯-wkₚ-del`, `⋯-cancel`, `⋯𝓅-cancel` | the structure substitution erasing the two communicated handles; it undoes `wkₚ` on variables, structures and context patterns | `Support/ComWeaken.agda` |
| `del-⇒` | `del a c ∶ ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) ⸴* Γ ⇒ (Γ₁ ⸴* Γ₂) ⸴* Γ` — legal because an erased slot is `[]` | `Support/ComWeaken.agda` |
| `structBinder-suc` | `structBinder (suc b ∷ B) ≡ ((` 0F) ; …) ∥ …` | `Support/ComWeaken.agda` |
| `Fr`, `Fr-del` | `Fr` is the `TP-Res` structure; `Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ ⋯ del ≈ Fr (b₁ ∷ B₁) (b₂ ∷ B₂) γ` | `Support/ComWeaken.agda` |

`Safety/Preservation/Choice/` — R-Choice-specific, but `Retype` and `Count`
are generic enough for anybody who has to change a context in place.

| lemma | statement | file |
|---|---|---|
| `bindCtx-brn` | a group whose first handle starts with a `p`-choice has a session that starts with the same choice, plus a rebuilder that re-types the group with the branch in place of the choice | `Choice/BindCtxBrn.agda` |
| `choice-split` | both endpoints resolve to dual continuations: produces `s*`, the two new head types, `New s*`, and both re-typed `BindCtx`s | `Choice/Session.agda` |
| `count-⋯ᵣ-∉`, `count-[-]𝓅`, `count-wkˡ` | multiplicity under renaming / through a context pattern / under `wkˡ` | `Choice/Count.agda` |
| `count-Fr-x`, `count-Fr-y` | each communicated handle occurs **exactly once** in the `TP-Res` structure | `Choice/Count.agda` |
| `∉-join-Dir⁻`, `∉-[-]𝓅⁻`, `∉-[-]𝓅-++`, `∉-block`, `∉-wk*` | `∉ dom` bookkeeping | `Choice/Count.agda` |
| `Retyping`, `↑Rt`, `↑Rt*` | the re-typing datum (contexts agreeing off two positions, both of which are neither `Unr` nor `Mobile`) and its lifts | `Choice/Retype.agda` |
| `unrCx-re`, `mobCx-re`, `≈-re`, `≼-re` | the structural side conditions transport unconditionally | `Choice/Retype.agda` |
| `Tm-re`, `F-re`, `F*-re`, `P-re` | a term / frame / frame stack / process that does not mention the two positions keeps its typing | `Choice/Retype.agda` |
| `agree-two` | the two doubly-blocked contexts of `R-Choice` agree off the two block heads | `Choice/Retype.agda` |

## Reused from elsewhere (nothing re-proved)

* `Types.AtomCons` (`Cons`, `cons-sound`, `cons-unfold(⁻¹)`, `cons-suffix-unique`,
  `skips⊥cons`, `¬cons-brn`, `cons-atom⁻`, `StartsVar`, `skips⊥startsVar`,
  `acq-;-¬brn`), `Types.AtomSnoc` (`ClosedAtom`), `Types.AtomUnsnoc`
  (`atom-;-unsnoc`), `Types.Predicates` (`New`, `new-≃`, `new-⋯`).
* `Processes.Typed` (`inv-ν`, `inv-∥`, `inv-⟪⟫`, `bindCtx-inv-msg`, `bindCtx-≃`,
  `bindCtx⇒chanCtx`, `_⊢⋯ₚ⁻¹_/_`), `Reduction.Base` (`⊢[]*⁻¹`, `_⊢⋯ᶠ*⁻¹_/_`),
  `Reduction.Expressions` (`value⇒pure`, `mobile×value⇒mobCx`),
  `Terms.Base`/`Terms.SubstitutionInversion` (`inv-K`, `inv-·-unr`, `inv-⊗`,
  `inv-`, `≃-⊗⁻¹`, `constFnUnr′`, `_⊢⋯⁻¹_/_`), `Processes.Renamings`
  (`⊢wkₚ`, `wkₚ-inj`), `Context.Pattern` (`pullOutMobile`, `[-]𝓅-≼`, `[-]-dist-⋯`).
* **`Simulation/Support/Confine.agda`** — imported (cheap: it only depends on
  `Prelude`, `Types`, `Context.*`): `count`, `count-self`, `≼⇒count≤`,
  `count0⇒∉dom`, `∉dom⇒count0`, `count-join-Dir/PS`, `∉∪⁻/⁺`,
  `∉-join-Dir⁺`, `∉-join-PS⁻`, `∉-join-biased⁻`, `∉-abs-ctx-Dir/PS`,
  `∉-absrec-ctx`, `∉-letpair-ctx`.  This is the only `Simulation/` import.
* `Simulation/ForwardSoup/Local/Com.agda`'s private `wkₚ-A/B/C` and
  `Simulation/ForwardSoup/Renaming.agda`'s `lift*-↑ˡ/↑ʳ` were **transcribed**
  (they are private / that tree is far too expensive to import for four lines
  of Fin arithmetic); the copies are in `Support/ComWeaken.agda` and are
  credited there.
* `Simulation/Support/Theorems/ComHelpers2.agda` was read but not imported:
  `send-handle-≃msg-app` / `recv-handle-≃msg-app` duplicate what the plain
  inversion cascade already gives, and importing that tree is expensive.

## Discrepancies between `tex/rules/*` and the Agda

1. **CT-New swaps the two endpoints.**  `tex/rules/constant-typing.tex` gives
   `new_s : 𝟙 → ⟨acq ; (s ; Term)⟩ ⊗ ⟨acq ; (dual s ; Wait)⟩` (Term on the
   *first* component); Agda's `` `new`` gives
   `` `⊤ →*M ⟨ acq ; (s ; end ⁇) ⟩ ⊗¹ ⟨ acq ; (dual s ; end ‼) ⟩ ``,
   i.e. `Wait` (`⁇`) on the first component.  The two are mirror images.
2. **R-Choice brackets the parallel composition differently from R-Com.**
   In `tex/rules/reduction.tex`, R-Com is `(E₁[…] ∥ E₂[…]) ∥ P` but R-Choice
   is `E₁[…] ∥ (E₂[…] ∥ P)`.  Agda uses the left-nested form for both, so the
   Agda `R-Choice` is not literally the paper's rule (they are related by
   `∥-assoc`, which `R-Struct` can absorb, but the paper should be made
   consistent).
3. **Binary vs indexed choice.**  CT-Select/CT-Branch are stated over an
   arbitrary label set `L`; Agda fixes `L = Bool` (`brn p s₁ s₂`,
   `` `select : Bool → Const ``, and `branch`'s result is `⟨s₁⟩ ⊕ ⟨s₂⟩`
   rather than a variant).
4. **The split constants are strictly stronger in Agda.**  CT-LSplit/CT-RSplit
   assume only `¬ (s₂ ≃ skip)`; Agda's `` `lsplit`` / `` `rsplit`` assume
   `¬ Skips s` **and** `¬ Skips s′`.  (Flagged for P3; the Agda source
   documents why.)
5. **TP-Res orders its premise the other way round.**  The paper writes
   `Γ ∥ Γ₁ ∥ Γ₂ ⊢ P`; Agda types the body in `(Γ₁ ⸴* Γ₂) ⸴* Γ` with structure
   `structBinder B₁ ∥ structBinder B₂ ∥ (γ ⋯ weaken*)`, i.e. binders first.
   Cosmetic, but the de Bruijn indices in the reduction rules depend on it.
6. **`⊢ᴮ B` is not in the paper.**  Agda's TP-Res carries
   `⊢ᴮ B = Allᴸ NonZero (drop 1 B)` (every sub-block after the first is
   non-empty).  The paper's B-Emp/B-Seq/B-Drop/B-Acq do not state it.
7. **`AcqHeadCtx` is not in the paper.**  Agda's `BindCtx.cons-ret/acq` and
   `cons-acq` additionally require the first handle of a non-first sub-block to
   *start* with `acq` (`s ≃ acq ; t`), not merely to be non-skipping.  The
   Agda source cites a counterexample that the weaker (paper) reading admits.
8. Minor: the paper's binder groups are sequences of variables with two kinds
   of separator; Agda's `BindGroup = List ℕ` records only the sub-block sizes,
   so `x·B₁` becomes `suc b₁ ∷ B₁`.  The correspondence is faithful but the
   paper never says which sub-block a bound variable belongs to.
