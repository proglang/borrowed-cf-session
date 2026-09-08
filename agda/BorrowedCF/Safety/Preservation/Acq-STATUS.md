# P4b status — R-Acq preservation (`pres-Acq`)

Owner: agent P4b.  Files owned: `Safety/Preservation/Handles/Acq.agda`,
`Safety/Preservation/Handles/AcqProbe.agda`, this file, and the `pres-Acq`
postulate block of `Safety/Preservation/Handles.agda`.

Gotcha: every `;` in this development is U+037E, including inside identifiers
(`acq-;-split`, `≃-;`, `;-unit₁`, the `AllCx` constructor `_;_`, …).

## 1. The probe: P4's counterexample does NOT exist

P4's obstacle was `∥′-tm-;  : MobCx Γ α ⊎ MobCx Γ β → Γ ∶ α ∥ β ≈′ α ; β`
(`Context/Equivalence.agda:35`).  It is the only rule that can split the
sequential frame `structNSeq (suc b₁) = ` 0F ; wk (structNSeq b₁)` of a binder
group into parallel components, and it needs the split point to be mobile.  If
the head `x₀ : ⟨ u ⟩`, `u ≃ acq ; t`, of the acquired group were mobile while
another thread held a later handle of the same group, the LHS would type and
the reduct (head `⟨ t ⟩`, no longer mobile) would not.

**That configuration is untypable.**  `Mobile ⟨ acq ; t ⟩` unfolds to
`∃ t′. Bounded t′ × (acq ; t ≃ acq ; t′)`, i.e. to `Bounded t`: the head's OWN
continuation already carries the group's terminator (`ret` inside a group
chain, `end p` for the last group).  `Types/NoTerm.bounded-tail-skips` then
forces everything after the head in the group to `Skip`, and `BindCtx′.cons`
demands `¬ Skips`.  So a mobile group head is ALONE in its group; equivalently
a group of width ≥ 2 has an immobile head.  Formalised as

* `AcqProbe.head-¬mobile` — `BindCtx c (suc (suc b) ∷ B) Γ → ¬ Mobile (Γ ﹫ 0F)`
  for any chain `c ≃ q ; τ` with `TermAtom τ`, `NoTerm q`;
* `AcqProbe.acq-head-¬mobile` — its R-Acq instance, `c = acq ; (s ; end p)`,
  `New s`.

This is the `BindCtx`-local half of `Simulation/BackwardSoup/Position/
Crux.agda`'s `mobile-head-alone` (line ~370) / `group-head-¬mobile` (~382);
their `block-mobile-head-width1` core is `private` and their statements are
phrased over the `GroupOf` navigation of a whole binder list, so the two
lemmas above re-derive exactly the instance R-Acq needs, without importing
`Simulation/BackwardSoup/`.

Concretely, the candidate configuration of the task (side 1 = `0 ∷ 2 ∷ []`,
`x₀ : ⟨ acq ; msg ‼ `⊤ ⟩`, `x₁ : ⟨ end ‼ ⟩`) fails at the first step:
`Mobile ⟨ acq ; (msg ‼ `⊤) ⟩` needs `Bounded (msg ‼ `⊤)`, and `Bounded`
(`Types/Predicates.agda:21`) has no `msg` constructor.  Any repair that makes
the head mobile (`t` bounded) makes `t` reach the terminator, which by
`bounded-tail-skips` empties the rest of the group.  `GroupOrder.
before-mono-≼` is the second, independent lever: with both handles immobile,
`≼` cannot turn the frame's `` ` 0F ; ` 1F `` into a `∥`, so the `TP-Par`
split of a width-2 group is underivable.  Not needed for the proof below.

**Consequence: process preservation for R-Acq is TRUE and `pres-Acq` is
provable.**  The simulation development never needed this: the forward case
(`Simulation/Support/Theorems/Acq.agda`, `U-acq-step`) consumes the typing of
the REDEX only and produces an untyped reduction of the translation; the
backward soup case (`Simulation/BackwardSoup/Leaves/Acq.agda`) likewise.  No
module in `Simulation/` types an R-Acq REDUCT.

## 2. Lemmas

| lemma | statement | status | file |
|---|---|---|---|
| `block-width1` | a mobile handle at the front of a `BindCtx′` block ends the block | **proved** (private) | `Handles/AcqProbe.agda` |
| `head-¬mobile` | the head of a binder group of width ≥ 2 is immobile | **proved** | `Handles/AcqProbe.agda` |
| `acq-head-¬mobile` | its `acq ; (s ; end p)` / `New s` instance | **proved** | `Handles/AcqProbe.agda` |
| `mobCx-tr`/`unrCx-tr`/`≈′-tr`/`≈-tr`/`≼-tr` | `¬ Mobile T → (T ⸴ Δ₀) ∶ α ≼ β → (T′ ⸴ Δ₀) ∶ α ≼ β` (and `≈`): a structure relation is replayed verbatim at a new head type as soon as the old head is immobile | **proved** | `Handles/Acq.agda` |
| `zap`, `zap-⇒`, `zap-fix`, `zap-fix𝓅`, `zap-wk`, `zap-wk𝓅` | the in-place erasing substitution `0F ↦ []`; it is a legal `⇒` between ANY two contexts differing only at `0F`, and fixes everything weakened past `0F` | **proved** | `Handles/Acq.agda` |
| `pat-hole-≼` | `Γ ∶ 𝒫 [ γ ]𝓅 ≼ γ ∥ 𝒫 [ [] ]𝓅` (uses `≼-wk` for the two `;` cases) | **proved** | `Handles/Acq.agda` |
| `app-var-≼` | `Γ ; γ ⊢ K c ·¹ (` x) → Γ ∶ ` x ≼ γ` | **proved** | `Handles/Acq.agda` |
| `acq-cancel` | `acq ; x ≃ acq ; y → x ≃ y` (via `AtomCons.≃-cons`/`cons-suffix-unique`) | **proved** (private) | `Handles/Acq.agda` |
| `bindCtx-acq` | `(Γ ﹫ 0F) ≃ ⟨ acq ; t ⟩ → BindCtx (acq ; (s ; end p)) (suc b ∷ B) Γ → BindCtx (s ; end p) (suc b ∷ B) (⟨ t ⟩ ⸴ V.tail Γ)` | **proved** | `Handles/Acq.agda` |
| `FrB`, `fr-0∷`, `fr-split` | the `TP-Res` frame; the leading zero-width group is `≈`-invisible; a width-1 group splits as `` ` 0F ∥ (Fr ⋯ zap) `` | **proved** | `Handles/Acq.agda` |
| `acq-confine-wk` | `acq-confine` with the thinning taken to be `weakenᵣ` (so `⊢weakenᵣ` can be attached) | **proved** (private) | `Handles/Acq.agda` |
| `mob-or-thin` | `¬ Mobile (Γ ﹫ 0F) ⊎ b ≡ 0` for the acquired group | **proved** | `Handles/Acq.agda` |
| `acq-final` | the structure step of R-Acq: the frame bound survives the head-type change, by `≼-tr` (wide group) or by `zap` + `pat-hole-≼` (width-1 group) | **proved** | `Handles/Acq.agda` |
| `bindCtx-0-inv` | a zero-width leading group is a `cons-acq` node | **proved** | `Handles/Acq.agda` |
| `pres-Acq′` | R-Acq with `E`, `P` already factored through `weakenᵣ` | **proved** (private) | `Handles/Acq.agda` |
| `pres-Acq` | `ChanCx Γ → Γ ; γ ⊢ₚ ν (0 ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ acq 0F ] ⟫ ∥ P) → Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` 0F ] ⟫ ∥ P)` | **proved**, zero holes, no postulates | `Handles/Acq.agda` |

## 2b. Wiring

`Handles.agda`'s `postulate pres-Acq` block is gone; the file now ends with

```
open import BorrowedCF.Safety.Preservation.Handles.Acq using (pres-Acq) public
```

`agda-check BorrowedCF/Safety/Preservation.agda` passes (it re-checks
`Handles.agda` and `Handles/Acq.agda` on the way), so `preservationₚ`'s R-Acq
case is now postulate-free.  The remaining postulates in `Preservation.agda`
are P4's `private` placeholders for `pres-LSplit`/`pres-RSplit`, owned by P3.

## 2c. Performance

The one `refl` that rewrites the process (`E ≡ E₀ ⋯ᶠ* weakenᵣ`, from
`acq-confine-wk`) is isolated in the two-line top-level `pres-Acq`, which does
nothing else and hands the already-factored process to `pres-Acq′`; `{E = E}`
and `{P = P}` are passed explicitly to `acq-confine-wk` (otherwise the
`Frame*` metavariable blocks the `refl` split, `SplitError.UnificationStuck`).
`pres-Acq′` then does its inversion `with`-chain on a process that is already
in `E₀`/`P₀` form.  A full `agda-check` of `Handles/Acq.agda` with cached
imports is ~10 s and stays well under 1 GB.

## 3. Reused (not re-proved)

* `Types/AtomCons.agda`: `≃-cons`, `cons-suffix-unique`, `acq-;-split`,
  `acq-;-≄ret`.  `Types/NoTerm.agda`: `bounded-tail-skips`, `noTerm-split`,
  `noTerm-acq`, `new⇒noTerm`, `TermAtom`.
* `Safety/Preservation/Handles/Erase.agda` (P4): `app-var-[]≼`;
  `Safety/Preservation/Handles/Frames.agda` (P4): `fuse2`, `fuse3`.
* `Simulation/Support/{Confine,InvFrame,Strengthen,AcqInv,AcqHandle}.agda`:
  the counting half of the confinement (`count`, `≼⇒count≤`,
  `strengthen-frame`, `strengthen-Proc-gen`, `inv-weakenᵣ`, `acq-app-nonUnr`,
  `count-handle-acq`).

## 4. Discrepancies tex vs Agda (R-Acq specific)

1. `Types/Predicates.agda:183` gives `Mobile ⟨ s ⟩ = ∃ s′. Bounded s′ ×
   s ≃ acq ; s′`, i.e. only `Te-Acq`
   (`tex/rules/bounded-session-types.tex:17`).  The paper ALSO has `Te-Skips`
   (`\S \SEq \SSkip ⇒ \Mobile\S`, same file line 21), which the Agda
   `Mobile` drops: a `⟨ skip ⟩` handle is mobile on paper and immobile in
   Agda.  R-Acq is unaffected — the acquired handle is `⟨ u ⟩` with
   `u ≃ acq ; t`, and `acq ; t ≃ skip` is impossible
   (`AtomCons.acq-;-¬skips`) — but under `Te-Skips` a `⟨ skip ⟩` head COULD
   be split off its group by `∥′-tm-;`, which is worth checking for R-Discard
   (there the head is exactly `≃ ⟨ skip ⟩`; `pres-Discard` is already proved
   for the Agda `Mobile`, and adding `Te-Skips` would not invalidate it, since
   `bindCtx-discard` and its structure step never use immobility).
2. The paper's context equality (`tex/sec/types.tex:84-86`,
   \cref{fig:syntax-types}) has EXACTLY the Agda rule, in both orientations:
   `Mobile Γ₁ ⇒ Γ₁ ∥ Γ₂ = Γ₁ ; Γ₂` and `Mobile Γ₂ ⇒ Γ₁ ∥ Γ₂ = Γ₁ ; Γ₂`,
   plus the CKA exchange law as the only non-`Unr` subcontext axiom.  So the
   paper has the same rule set and the same argument applies to it: a mobile
   group head has a `Bounded` continuation, hence ends its group.
3. tex `R-Acquire` keeps the binder `x` and only deletes the group separator;
   the Agda rule does the same, but the TYPE of `x` changes from
   `⟨ acq ; t ⟩` to `⟨ t ⟩`, which the tex rules do not make visible.

## 5. Do the rules need a fix?  No.

The coordinator asked, in case the counterexample were genuine, for the
minimal principled repair.  It is not genuine, so no rule changes; for the
record, here is what the audit found.

**Where `∥′-tm-;` is actually used.**  `grep` over `agda/BorrowedCF` for
`∥′-tm-;`, `∥/;-transmute`, `;-commMob` outside `Context/`: only comments (in
`Simulation/BackwardSoup/{GroupOrder,Position,Examples/*}`).  Inside
`Context/Equivalence.agda` the rule has exactly three consumers:

* `;-unit₁`/`;-unit₂` — witness `inj₁ []` / `inj₂ []`, i.e. `MobCx Γ []`,
  which holds for every context.  These two are used everywhere (every frame
  computation, `pres-Close`/`Discard`/`Drop`/`Acq`).
* `;-commMob` and the `∥`/`;` interchange at `Context/Equivalence.agda:196`
  — witnesses always `UnrCx⇒MobCx`, i.e. mobility of an UNRESTRICTED context.

So no proof in the development consumes `Te-Acq` mobility of a handle.  Its
role is in the TYPING OF PROGRAMS: `T-Abs`'s premise
`Γ-mob : Arr.Mobile a → MobCx Γ γ` (`Terms/Base.agda:196`) is what lets a
closure that captures a bounded acquired handle be given a mobile arrow, and
mobile arrows are what `fork`/`send` demand.  Deleting `Te-Acq` would not
break any proof here but would reject such programs, so it is not a repair
anyone should want.

**Why the rule is harmless at an acquired handle.**  `∥′-tm-;` can split a
group's `structNSeq` only at a mobile handle, and `Bounded` (the premise of
`Te-Acq`) says the handle's own continuation already reaches the group's
terminator.  `bounded-tail-skips` then empties the rest of the group.  Group
width one is exactly the case in which the frame contribution is
`` ` 0F ; [] ``, so the split is available but useless: `` ` 0F ∥ [] ≈ ` 0F ;
[] `` already follows from the trivial `MobCx []` witness.  That is why
`acq-final`'s width-one branch needs no mobility at all — it uses `zap`,
`pat-hole-≼` and `∥`-laws only.

**What WOULD break it.**  Two hypothetical changes, listed so they are not
made by accident:

1. Adding the paper's `Te-Skips` to `Mobile` (discrepancy 1 above) makes a
   `⟨ skip ⟩` handle mobile.  A `⟨ skip ⟩` head CAN sit in a group of width
   ≥ 2 (`BindCtx′.cons` only forbids the whole chain from skipping), so with
   `Te-Skips` a group really could be split across threads at a skip-typed
   head.  R-Acq is still safe (its head is acq-headed, never `≃ skip`), but
   `Simulation/BackwardSoup/Position/Crux.mobile-head-alone` and everything
   built on it would have to be restated.  If `Te-Skips` is wanted in the
   mechanisation, the minimal repair is to weaken it to
   `S ≃ Skip ⇒ Mobile S` only for handles whose group is already exhausted,
   or to keep the Agda `Mobile` and note the restriction in the paper.
2. Making `∥′-tm-;` unconditional (or conditioning it on the CONTINUATION
   rather than the head) would break R-Acq preservation for real, and would
   also invalidate `GroupOrder.before-mono-≼`, `Position/Crux`, and the whole
   `Simulation/BackwardSoup/Position` layer, which is the only place the
   development reasons about `;`-order.
