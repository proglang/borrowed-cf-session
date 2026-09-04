# Backward simulation UntypedSoup → Typed: statement, expected failures, example matrix

Date: 2026-09-02. Branch `codex/soup-of-processes`. The untyped-target development is on hold; this
directory concerns only the soup calculus `Processes.UntypedSoup` / `Reduction.Processes.UntypedSoup`.

## 1. The proposition to test

Naive form (as posed): for a well-typed closed `P : Typed.Proc 0` with `flatten P ≡ (cs , ts)`
(`Translation.flatten P (V.allFin _) (λ ())`, the `initialGlobalImage` configuration), if
`config cs ts ─→ₚ config cs′ ts′` then there is `P′` with `flatten P′ ≡ (cs′ , ts′)` and `P ─→ₚ P′`.

## 2. Failure modes predicted before running the examples

F1 **Dead channels (Close).** `RUS-Close` keeps the closed channel as `(false , [] , [])`; the typed
   `R-Close` removes the `ν`. `flatten P′` has one channel fewer than `cs′`, so no `P′` satisfies the
   naive equation. Generalisation: replace exact flattening by the image relation of the forward
   proof, `GlobalImage P′ C′` (`Simulation/ForwardSoup/World.agda`): live part = flattening up to an
   injective placement of channels/threads, the rest garbage (dead channels, `K unit` threads).
F2 **Channel placement (New).** `RUS-New` inserts the new channel at an arbitrary index `i`; the
   typed `ν` nesting fixes the index. Up to `≋` (`ν-ext′`, `ν-comm′`) any index is reachable, but
   with `GlobalImage` no `≋` is needed: `logicalChannels` absorbs the permutation. Same for thread
   order (`R-Par` only reduces the left component; `≋` `∥-comm` or the thread embedding absorbs it).
F3 **Slot choice (RSplit).** After the positional-insertion change (ForwardSoup PLAN §6.4, option 1)
   `RUS-RSplit` may insert the new boundary at ANY position `k = length before`; the typed rule
   determines `k` = number of groups before the split one. For interior handles the soup state
   carries no group information (`Ub` interior entries are `𝓒[ * × x × * ]`), so the soup cannot
   pick the right `k` locally. Predicted failing example: rsplit with a "wrong" `k`. Generalisation:
   images up to a per-endpoint renumbering of phi slots (consistently in the flag list and in all
   threads); the soup dynamics is invariant under it (`RUS-Drop`/`RUS-Acquire` address slots by
   name only). Alternative: make the soup record group membership.
F4 **Position of the consumed handle (Drop, Discard, Acq).** The soup fires on any thread holding
   the right term; the typed rules require the handle to be variable `0F` of the FIRST group
   (`R-Drop`, `R-Discard`; `R-Acq` additionally requires the first group to have width 0). Whether a
   well-typed process can hold a droppable/discardable handle elsewhere is a typing question (the
   borrowing discipline of `⊗ᴸ`/`⊗¹`, `Struct` joins, `BindCtx` chains). Probes: (a) `lsplit` a
   `⟨ s ; ret ⟩` handle and `drop` the second half while the first is live; (b) discard an interior
   handle; (c) acq on a group that is not the first. If typable ⇒ the typed rules are incomplete and
   the backward statement needs either extra typed rules or a reachability hypothesis.
F5 **Expression steps.** `RUS-Exp` needs the inverse of `T[_]-⋯→`: a soup step on `T[ e ] σ` comes
   from a source step of `e`. Expected to hold (compositional translation); one example.

## 3. Example matrix (`Examples.agda`, one section per soup rule)

Each example is a checked term: `P`, `C ≡ flatten P` (by `refl`), `step : C ─→ₚ C′`, `P′`,
`red : P ─→ₚ P′`, and either `flatten P′ ≡ C′` (by `refl`) or, where that fails, the weaker relation
that holds plus a note. Rules: Exp, Fork, New (canonical index and index `0F`), LSplit, RSplit
(canonical `k` and a wrong `k`), Drop, Discard, Acquire, Close, Com, Choice. Probes for F4 with a
typability attempt. Threads in swapped order for Com/Choice (needs `R-Struct`).

## 4. Findings from the example suite (`Examples.agda` and `Examples/*.agda`, all load with 0 goals)

Positive: Exp, Fork, LSplit, Drop/Discard/Acquire at the canonical position, Com and Choice (both
thread orders; `replaceTwo` writes in place so no `≋` is needed for the *image*), New at the
canonical index, RSplit at the canonical slot: `flatten P′ ≡ C′` by `refl`.

F1 confirmed (Close): counts differ; `GlobalImage P′ C′` holds with the dead channel as garbage.
F2 confirmed (New at index `0F`): exact flattening fails; `GlobalImage` holds with a permuted
   `logicalChannels`, no `≋` needed.
F3 confirmed (RSplit at a non-canonical slot): the reduct is NOT the flattening of any process
   (a decreasing phi-slot pair `𝓒[ phi (x,1) × x × phi (x,0) ]`); it is the canonical reduct up to a
   per-endpoint slot renumbering (`consumePhi 0F 1` vs `consumePhi 0F 0` agree).
F4 (a) Drop — GENUINE MISMATCH INSIDE THE CALCULUS. `Pf4 = ν (0 ∷ 2 ∷ 1 ∷ []) (1 ∷ []) ((⟪ end‼ (acq x₀) ⟫
   ∥ ⟪ drop x₁ ⟫) ∥ (⟪ discard (acq x₂) ⟫ ∥ ⟪ end⁇ x₃ ⟫))` is well typed (`f4-typing`): the binder
   structure `x₀ ; x₁` of the width-2 group is turned into `x₀ ∥ x₁` by `∥/;-transmute` because
   `x₀ : ⟨ acq ; end ‼ ⟩` is Mobile (`Types/Predicates.agda:183`). It is reachable (`new skip`, then
   `rsplit` presenting `acq ; end ‼` as `(acq ; end ‼) ; skip` via `≃`, then `lsplit`). The soup fires
   `RUS-Drop` on `x₁`; no typed rule applies (`R-Drop` wants `0F` of a nonempty first group) and the
   typed process deadlocks after `R-Acq` (`ν (2 ∷ 1 ∷ [])` with `x₀ : end ‼`, `x₁ : ret`). The soup's
   reduct has flags `acq ∷ acq`, i.e. group shape `0 ∷ 0 ∷ 1`, rejected by `⊢ᴮ`: it is the image of
   no well-typed process. Semantically the early `ret` releases the next group while `x₀`'s actions
   are still pending, i.e. `∥/;-transmute` lets a group's `ret` handle escape ahead of the group.
F4 (b) Discard — GENUINE MISMATCH. `Pf4b = ν (1 ∷ 2 ∷ []) (1 ∷ []) ((⟪ drop x₀ ⟫ ∥ ⟪ discard x₁ ;
   end‼ (acq x₂) ⟫) ∥ ⟪ end⁇ x₃ ⟫)` with `x₁ : ⟨ skip ⟩` at the head of the second group (from
   `lsplit` on `⟨ acq ; end ‼ ⟩ ≃ ⟨ skip ; (acq ; end ‼) ⟩`), well typed without mobility. The soup
   discards `x₁`, losing the group's boundary token (`x₂` keeps `𝓒[ * × x × * ]` and can never
   acquire); the typed calculus deadlocks too (`R-Discard` needs `0F`; after `R-Drop x₀` the first
   group is empty and only `R-Acq` removes it). The reduct is not a flattening.
F4 (c) Acquire — complete: `⊢ᴮ` forbids an empty group in non-first position, so a soup acquire on a
   typed image is always `R-Acq`.
F5 confirmed.

## 5. Proposed statement and the decisions it needs

Statement (fixes F1, F2, F3): for well-typed closed `P` and `C ─→ₚ C′` with `GlobalImage P C`
(initially `flatten P`), there is `P′` with `P ─→ₚ P′` and `GlobalImage P′ C′` **up to a per-endpoint
renumbering of phi slots** (`C′ ≡ᵖ flatten-image` where `≡ᵖ` relates configurations that differ by a
bijection on the slot names of each endpoint, applied consistently to the flag list and to every
thread). Equivalently, restrict `RUS-RSplit` to its canonical slot; but the soup cannot compute that
slot locally (interior handles carry no group information), so the quotient is the honest form.

F4 cannot be absorbed by any statement: on `Pf4`/`Pf4b` the soup steps and the typed calculus is
stuck, and the soup's continuation leaves the well-typed world. One of the following must change:
 (i) the type system: forbid `∥/;-transmute` from separating the handles of one binder group
     (mobility of an *earlier* handle must not reorder it past a later `ret` of the same group), and
     forbid `≃`-conversions that split off a leading `skip` into its own handle ahead of an `acq`;
 (ii) the typed rules: allow `R-Drop`/`R-Discard` at other positions, which also needs a group
     representation that can record a released boundary (`⊢ᴮ` change) — semantically dubious, since
     it lets the next group act before the current one is done;
 (iii) the soup: refuse `RUS-Drop`/`RUS-Discard` unless the handle is the last/first of the FIRST group
     — not expressible locally for Discard (a group head is `𝓒[ phi (x,k) × x × * ]` for k > 0, so it
     is expressible as `before ≡ []`; for Drop likewise `before ≡ []`), and it only makes both sides
     deadlock instead of restoring correspondence.
Recommendation: (i), then prove the statement of §5 with `≡ᵖ`.

## 6. Branch `codex/soup-strict-groups`: the strict rules (2026-09-02)

Validation round before the change:
* Paper comparison (`tex/rules/process-typing.tex`, `tex/sec/types.tex`): the Agda `BindCtx` is the paper's
  B-Seq/B-Drop/B-Acq and the split constants carry only `¬ Skips s′`; the proposal strengthens the paper.
* `¬ Skips s` on `rsplit` is NOT optional: splitting the head `⟨ acq ; t ⟩` of a non-first group as
  `⟨ skip ; (acq ; t) ⟩` would leave a head `⟨ ret ⟩` without its `acq` (moved to the new group): the
  soup cannot drop it (its left token is not `*`) and the typed side cannot acquire; both deadlock.
* Preservation of the new premises under every typed rule checked by hand: R-LSplit/R-RSplit keep the
  head's `acq` (the left part is non-skip), R-RSplit's new boundary has a non-skip continuation
  (`¬ Skips s′`), R-Discard/R-Drop empty only the first group, R-Acq removes the empty first group,
  New creates `0 ∷ 1 ∷ []` with an acq-headed second group.
* Mobility stays sound: a handle `⟨ acq ; s′ ⟩` with `Bounded s′` carries its group's terminator; `cons`
  forbids handles after a terminator, `AcqHeadCtx` forbids a skip handle before it, so a Mobile handle
  is the only handle of its group and `∥/;-transmute` only reorders across groups, which the tokens
  serialise.
Rules as implemented: `` `lsplit/`rsplit `` get `¬ Skips s`; `cons-ret/acq` gets `¬ Skips s₂` and
`AcqHeadCtx Γ₂`; `cons-acq` gets `AcqHeadCtx Γ` (`AcqHeadCtx (⟨ s ⟩ ∷ _) = ¬ Skips s`, else `⊥`).
BOTH claims of this section were later found too weak — see §10: `AcqHeadCtx` is now
`Σ[ t ] (s ≃ acq ; t)`, and the mobility argument runs on `NoTerm`, not `NoRet`.

## 7. Remedy (i), implemented (branch `codex/soup-strict-groups`)

Both F4 counterexamples are now ILL-TYPED; §4's "`is well typed (`f4-typing`)`" and the
corresponding claim for `Pf4b` are historical.  Two rules were tightened:

1. `Terms/Base.agda` — the split constants require `¬ Skips` of BOTH components:
   `` `lsplit : (s s′ : 𝕊 0) → ¬ Skips s → ¬ Skips s′ → … `` and likewise `` `rsplit ``.
   A split therefore never produces a bare `⟨ skip ⟩` handle, and the `¬ Skips s` premise of
   `` `rsplit `` is what stops `⟨ acq ; t ⟩ ≃ ⟨ skip ; (acq ; t) ⟩` from turning a group head
   into an unreleasable `⟨ ret ⟩` whose `acq` has moved into the new group.
2. `Processes/Typed.agda` — `BindCtx` gained two premises, stated via
   `AcqHeadCtx : Ctx n → Set` (`AcqHeadCtx (⟨ s ⟩ ∷ _) = ¬ Skips s`, `⊥` otherwise):
   `cons-ret/acq` now takes `¬skips₂ : ¬ Skips s₂` (a group boundary is only formed in front
   of real work) and `acqHead : AcqHeadCtx Γ₂`; `cons-acq` takes `acqHead : AcqHeadCtx Γ`
   (the first bound handle of a non-first group carries that group's `acq`).
   `AcqHeadCtx` was `¬ Skips s` here; §10 replaces it by `Σ[ t ] (s ≃ acq ; t)`.

`Examples/Probes.agda` keeps the soup steps and the "reduct is not a flattening" facts and
replaces the two typings by checked refutations of the exact blocked premise:
`f4-boundary-blocked : ¬ (¬ Skips {0} skip)` — the `cons-ret/acq` of `Pf4`'s width-2 group has
`s₂ ≡ skip` (witnessed by `f4-second-boundary` and `f4-tail-block`) — and
`f4b-acqHead-blocked : ¬ AcqHeadCtx (⟨ skip ⟩ ∷ ⟨ acq ; end ‼ ⟩ ∷ [])` — the second group of
`Pf4b` (witnessed by `f4b-second-group`) is headed by a bare `⟨ skip ⟩`.

F4 (c) is unaffected: `f4c-C1` still checks (with the new premises discharged by `λ ()`), and
`Pf4c` remains rejected by `⊢ᴮ` alone.

With F4 gone, the only remaining obstacle to the §5 statement is F3 (`RUS-RSplit` at a
non-canonical slot), i.e. the `≡ᵖ` slot-renumbering quotient.

## 8. `Statement.agda`: the refined statement, and the plan for proving it

`Statement.agda` (loads with 0 goals, no pragma) supplies the `≡ᵖ` of §5 concretely and states the
theorem.  The quotient is generated by an ADJACENT TRANSPOSITION of two slots of one endpoint:
`swapSlot k` exchanges the slot numbers `k`/`suc k`, `swapPhi x k` applies it to every `phi` of
endpoint `x` in a thread (structurally a copy of `insertPhi`), `swapFlags side k` to the endpoint's
flag list; all three are proved involutive.  `_≈¹_` performs one such transposition on a whole
configuration (flag list AND all threads, with `suc k < length (endpointFlags …)` so that both slots
exist); `_≈ˢ_` is its `EqClosure`, and since `≈¹-sym` is derivable the reflexive-transitive closure
would do just as well.  Statement:

    Backward-Sim = ∀ {P} {C C₀ : Config n m} {C′ : Config n′ m′} →
      [] ; [] ⊢ₚ P → GlobalImage P C₀ → C₀ ≈ˢ C → C ─→ₚ C′ →
      Σ[ P′ ] P ─→ₚ P′ × Σ[ C₀′ ] GlobalImage P′ C₀′ × C₀′ ≈ˢ C′

plus the auxiliary conjecture `Slot-Bisim : C ≈ˢ D → C ─→ₚ C′ → Σ[ D′ ] D ─→ₚ D′ × C′ ≈ˢ D′`, which
reduces `Backward-Sim` to the case `C₀ ≡ C` (the soup rules address slots only through `phi` names,
`consumePhi` and `insertPhi`, never through their order).  Validation: the F3 pair of
`Examples/Splits.agda` is a single `≈¹` step — `rsplit-wrong-k-is-a-swap : Crs′ ≈¹ Crs″`, holding by
`refl` on both components (the flag lists are `drop ∷ drop` on either side, so the flag half of the
swap is the identity; `swapPhi 0F 0` maps the canonical threads exactly onto the wrong-slot ones).

Plan, per ingredient:

(a) **Translation inversion**, the reverse of `T[_]-plugᶠ*` (`ForwardSoup/Expressions.agda:609`): for
    a value environment `σ`, `T[ e ] σ ≡ F [ K c ·¹ v ]*` implies `e ≡ E [ K c ·¹ w ]*` with
    `Tᶠ*[ E ] Vσ ≡ F` and `T[ w ] σ ≡ v`.  Induction on the frame stack after inverting `T[_]` on the
    head constructor; `ValueEnv σ` is what stops a variable from masquerading as a redex.  One
    instance per soup leaf, plus the `⋯→` inversion for `RUS-Exp`.
(b) **Image inversion**: a non-garbage thread of `C₀` is `lookup (proj₂ (flattenOriented P lc σ)) j`
    for a unique `j`, i.e. a subterm `⟪ e ⟫` of `P` under its `ν`-binders with the environment
    `bindEnv B₁ B₂ channel …` accumulated along the path.  The forward direction of each step is
    already available (`LocalImage/Bind.agda` `res-split-image`, `LocalImage/Parallel.agda`
    `par-split-left/right`); new is that the thread index determines the path, which follows from the
    injectivity of the thread embedding (`LocalImage/Embedding.agda`).
(c) **Typed position facts**, now guaranteed by the strict rules of §6/§7: for Drop/Discard the
    matched `phi` slot is `L.length before` with `before ≡ []`, and `drop-shape`
    (`Support/Theorems/DropShape.agda`) together with `BindCtx`'s `¬ Skips s₂` puts the handle at
    variable `0F` of a non-empty first group, i.e. exactly `R-Drop`/`R-Discard`; for Acq, `⊢ᴮ`
    (`Allᴸ NonZero (L.drop 1 B)`) forbids an empty non-first group, so the acquired slot forces an
    empty FIRST group, i.e. `R-Acq` (§4, F4(c)).  `AcqHeadCtx` supplies the extra premise when the
    group list is rebuilt after the step.  §7's `Examples/Probes.agda` refutations are the record
    that the old counterexamples are now excluded by precisely these premises.
(d) **Per-rule construction**: (a)+(b) give the source redex, (c) its typed position, `P′` is the
    typed reduct.  `R-Bind`/`R-Par` descend to the redex; `R-Struct` with `∥-comm` is needed only
    when the redex sits in the right component of a `_∥_` (and for Com/Choice, whose partners may
    appear in either order — both are checked in `Examples/Sync.agda`).  No `≋` is needed for the
    IMAGE: `GlobalImage` quantifies over `logicalChannels` and the thread embedding, absorbing F1 and
    F2.  `GlobalImage P′ C₀′` then follows by applying the FORWARD leaf lemma of
    `ForwardSoup/Local/*.agda` (`U-exp/fork/new/lsplit/rsplit/drop/discard/acq/close/com/choice-local`)
    to the constructed typed step: the forward leaves produce exactly the soup step's configuration
    at the canonical slot.  `_≈ˢ_` absorbs a non-canonical `RUS-RSplit` slot; `Slot-Bisim` absorbs
    the renumbering already carried by `C₀ ≈ˢ C`.
(e) **Size**: comparable to the forward proof.  (a) and (b) are the two genuinely new inversion
    lemmas and carry most of the weight; (c) is a handful of `BindCtx`/`⊢ᴮ` lemmas; (d) is a
    fourteen-case dispatcher that REUSES the forward leaves instead of reproving them.  `Slot-Bisim`
    is an independent induction over the eleven soup rules, needing `swapPhi`'s commutation with
    `consumePhi`, `insertPhi`, `_[_]*` and `_⋯ᵣ_` — the exact analogues of
    `ForwardSoup/Local/InsertSupport.agda` and `AcqSupport.agda`, which are the templates to copy.

## 9. Proof architecture for `Backward-Sim` (branch `codex/soup-strict-groups`)

Phases, each a module under `Simulation/BackwardSoup/`; one Opus run per phase, Fable reviews/commits.
P1 `Locate.agda` — thread paths: a process context (`hole`/`par`/`bind`, as the retired `Context.agda`
   had: `plug`, `threadInContext`, `focusEnv`), `locate : (P) (i : 𝔽 (processCount P)) → Σ ctx e. P ≡ plug ctx ⟪ e ⟫
   × threadInContext ctx i₀ ≡ i`, and `thread-content : lookup (proj₂ (flattenOriented P lc σ)) i ≡ T[ e ] (focusEnv ctx lc σ)`.
   With `GlobalImage`, a non-garbage soup thread `j` is `threadEmbedding i ≡ just j` for a unique `i`.
P2 `Inversion.agda` — translation inversion under `ValueEnv σ`: `T[ e ] σ ≡ F [ K c ·¹ v ]*` ⇒ `Σ E w. e ≡ E [ K c ·¹ w ]*
   × Tᶠ*[ E ] Vσ ≡ F × T[ w ] σ ≡ v` (values of handle type are variables: `σ x` is a chanTriple, never an application, and no
   frame decomposes it); expression-step inversion `T[ e ] σ ⋯→ t′ ⇒ Σ e′. e ⋯→ e′ × T[ e′ ] σ ≡ t′` (reverse of `T[_]-⋯→`).
P3 `Position.agda` — typing facts for the located redex: a handle-typed value is a variable; which `ν` on the path binds it,
   its group and position; with the strict rules: Drop/Discard ⇒ `0F` of a non-empty first group (`DropShape`), Acq ⇒ empty
   first group + acq head, Com/Choice/Close ⇒ heads of the first groups of both sides.
P4 `Canonical.agda` — `≋`-rearrangement: bring the redex thread(s) directly under their binder as the left component(s) of
   its body, with the remainder in `⋯ₚ weakenᵣ`/`⋯ᶠ* weakenᵣ` form (`ν-ext′`, `ν-comm′`, `∥-comm/assoc`, `Strengthen.agda`).
   Probe 6 of the second hunt checks the `≋` rules suffice.
P5 `Leaves/*.agda` — per soup rule: soup step data + canonical typed redex ⇒ `R-Struct (canon) (R-rule) refl` and
   `GlobalImage P′ C₀′ × C₀′ ≈ˢ C′`, obtained from the forward leaf `U-*-local` on the canonical step plus a transport of
   images along the soup step's free choices (New index, Fork position: `logicalChannels`/`threadEmbedding`; RSplit slot: `≈ˢ`).
P6 `Main.agda` — the dispatcher on the eleven soup rules; `SlotBisim.agda` — `≈¹` commutes with every soup rule.

## 10. P3 finding (2026-09-03): the strict rules were two premises short — and both are now in

`Position/Crux.agda`'s remaining gap was a FRONT-atom peel for `acq`, dual to `Types/AtomUnsnoc.agda`'s
last-atom `atom-;-unsnoc`.  That is built and hole-free in **`Types/AtomCons.agda`**: `Cons a w z`
witnesses `w ≃ a ; z`, `≃-cons` transports it along `_≃_`, and `atom-;-cons` splits `x ; y ≃ a ; t`
into "the atom is at the front of `x`" or "`x` skips and it is at the front of `y`".  `Cons` needs no
`brn` constructor (`_;_` distributes over `brn` only rightwards), so the module is a fifth the size of
`AtomUnsnoc` and needs neither `SnocA`/`SnocM` nor `snoc-⋯-sum`.  It also supplies the refutations the
crux spends on the impure domains: `acq-;-¬skips`, `acq-;-≄ret`, `acq-;-≄end`, `acq-;-≄msg`,
`acq-;-¬brn`.

With it the P3 metatheorem needed TWO further premises, both machine-refuted in
**`Examples/StrictGroupGap.agda`** against the rules as §7 left them, and both now ADOPTED.

* **`AcqHeadCtx` strengthened** (`Processes/Typed.agda:161-168`):

      AcqHeadCtx (⟨ s ⟩ ∷ _) = Σ[ t ∈ 𝕊 0 ] (s ≃ acq ; t)
      AcqHeadCtx _           = ⊥

  instead of the strictly weaker `¬ Skips s`.  Under the old reading `cons-ret/acq` still admitted
  `s₁ ≡ skip` — a group that does no work and passes its `acq` on — so the next group could govern
  `acq ; acq ; ⋯` and put an ACQ-HEADED handle at offset 1, refuting `nonFirstGroup-interior-noAcq`
  (`StrictGroupGap.refuted`, which still checks: the naked statement remains false, which is why
  `Crux.nonFirstGroup-interior-noAcq` carries the `AcqHeadCtx` premise).  What the strong reading
  kills is the step ABOVE such a group: `StrictGroupGap.blocked` refutes the `acqHead` argument that
  the former `top` needed, so a `⟨ ret ⟩`-headed group can no longer sit under a binder.
  Fallout, all reloaded hole-free: `Examples/Probes.agda` (`f4b-acqHead-blocked` now refutes
  `Σ[ t ] (skip ≃ acq ; t)`; `f4c-C1` supplies real witnesses), `Examples/Probes2.agda`
  (`f3d-acqHead-first-only` and three `cons-ret/acq` nodes), `Examples/StrictGroupGap.agda`.
  `Reduction/Processes/Typed.agda`, `Simulation/ForwardSoup/Local.agda`, `BackwardSoup/Examples.agda`
  and `BackwardSoup/Statement.agda` are unaffected.

* **`NoTerm` instead of `NoRet`** (`Types/NoTerm.agda`, NEW, hole-free).  §6's mobility argument
  ("a Mobile handle is the only handle of its group") does not follow from `NoRet`: `Bounded s′` in
  `Mobile ⟨ acq ; s′ ⟩` is satisfied by an `end` tip as well as a `ret` tip
  (`StrictGroupGap.mobile-head-alone-refuted`).  `NoTerm` — no `ret` AND no `end`, which is exactly
  what `New` gives — is the right premise, and `bounded-tail-skips` is the one-line consequence: in a
  chain `q ; τ` whose only terminator is the trailing atom `τ`, a BOUNDED handle already reaches it,
  so everything after it skips and the `BindCtx′` chain stops.  `Crux.mobile-head-alone` carries the
  invariant "`c ≃ q ; τ` with `NoTerm q`, `τ ∈ {ret, end p}`" through the `BindCtx` induction:

      mobile-head-alone :
        New s → BindCtx (s ; end p) B Γ →
        ∀ {i} (grp : GroupOf B i) → groupOffset grp ≡ 0 → Mobile (Γ ﹫ i) →
        groupWidth grp ≡ 1

  and `group-head-¬mobile` is its corollary: a handle at a POSITIVE offset has an IMMOBILE group head
  (a mobile head would make the group a singleton).  This subsumes `Position.first-group-¬mobile`
  for the comparison partner — no case distinction on the group index is needed.

## 11. P3 CLOSED (2026-09-03)

`Position/Crux.agda` loads with **0 goals and no pragma**.  All four statements of `Position.agda` §7
are proved: `ImpureRedexHead`, `PairArgRedexHead`, `DropFirstGroupSingleton`, `AcqNonFirstGroupHead`.
The proof of the first two is the sketch of `Position.agda` §7:

* case (iii), "same group, offset > 0" (`offset-zero-inl/inr`): `group-head-before` prescribes
  `head ; x`, `ctx-¬before-direct`/`-pair` refutes it.  Both immobility side conditions are now
  available — `x` by §1e (every impure domain: `NoAcq` for `discard`/`drop`/`recv`/`end`, `¬cons-brn`
  for `select`/`branch`, the `⟨ msg ‼ T ⟩` component for `send`), the head by `group-head-¬mobile`.
  Linearity (`count x γ ≤ 1`) is `count-body-inl/inr`, from `StructDom.count-structBinder-lt`.
* case (iv), "x IS the head of a later group" (`head-not-later`): `laterGroup-head-acq` reads the
  strengthened `AcqHeadCtx` off the chain, and no impure constant consumes an acq-headed handle (§1e).
* the plumbing: `before` and `count` lifted from `structBinder Bᵢ` into the body structure `TP-Res`
  prescribes (`before-body-inl/inr`, two `before-⋯ᵣ` steps), and `TypeWalkP`, a predicate-generic
  version of `TypeWalk`, carries the two thread-level facts up to the owning binder.

`impure-redex-head′` / `pair-arg-redex-head′` take the `Binder` EXPLICITLY (the unprimed versions
apply them to `resolve ctx x`); `drop-first-group-singleton` needs that, because
`HeadOfFirstGroup (resolve ctx x)` does not reduce once `resolve ctx x` has been `with`-abstracted.

Still stale for reasons predating this branch (context-as-function vs. `Vec`): `Algorithmic/Solved.agda`,
`Simulation/Support/{BeforeOrder,ReverseInv}.agda`, `Simulation/Support/Theorems/Drop.agda`,
`Simulation/Forward/{Drop,Discard}.agda`, `Simulation/Backward/DropGo.agda`,
`Simulation/Support/Rev{Com,Drop}Confine.agda`.

Next: P4 (`Canonical.agda`) and P5 (`Leaves/*.agda`) of §9.

## 12. P4b closed; P5 architecture revised (2026-09-04)

P4b is complete: `CanonicalPair.agda` loads hole-free and pragma-free (commit `build the two-hole
canonical form for synchronising redexes`): `compose₂`/`fill₁`/`fill₂` algebra, the two ambient
renamings `wt₁`/`wt₂`, TWO-LEVEL bind stacks (`wkL₂`, `foldPar₂`, `push₂`), `Bubble₂`/`bubble₂`,
`Binder₂` (one `bind₂` node on the common path; `binder₂⇒₁/₂` project the one-hole `Binder`s),
`Canon₂`/`canon₂`, `canon-swap₂`, `HeadShape₂`/`headShapes⇒₂`, and `canon-pair`.
`Support/PairConfine.agda` (`strengthen-frame*`, `com-confine`, `close-confine`) is being repaired.

### 12.1 Why the §9 plan for P5 does not work as written

§9 P5 said: apply the FORWARD leaf `U-*-local` to the image transported along `≋-canon` and read the
soup configuration off the result.  Two facts block this:

1. `≋-image` (`ForwardSoup/LocalImage/Struct.agda`) returns only `Σ lc′. LocalImage Q lc′ …`; it hides
   the thread map.  The backward leaf must know that the transported image sends the CANONICAL redex
   thread (`0F` of the `ν` body) to the soup slot `j` the soup step fired on.  Without that, nothing
   connects the soup step to the typed redex we chose: a well-typed process can contain several
   threads with identical soup content (two `⟪ discard x ⟫` on different channels, or `⟪ * ; * ⟫`
   twice), so no content-based or counting argument can recover `j` from a black-box transport.
2. `LocalStep` hides the soup step's DATA (slot, frame, channel, flag split).  The forward leaf's
   `C′` is a `RUS-*` result, but the leaf's slot and frame are computed inside `with`-blocks, so the
   backward proof cannot equate the forward `C′` with the soup step's reduct.

Consequences: (a) thread tracking through `≋` must be made SYNTACTIC and threaded through `Canonical`;
(b) each forward leaf must EXPOSE its step data.  CHANNEL tracking is NOT needed: once the slot is
known, `lookup ts j ≡ T[ E₀ [ K c ·¹ ` 0F ]* ] σ_c ≡ F [ K c ·¹ v ]*` and unique decomposition give
`v ≡ σ_c 0F`, whose endpoint is `endpoint (physicalChannel (lookup lc_c 0F)) side_c`, so the physical
channel and side of the soup step are forced (`endpoint` is injective).

### 12.2 Components (one module per step; one Opus run per module, Fable commits)

P5.0 **`BackwardSoup/Tracks.agda`** — syntactic thread tracking.  Inductive families
`Tracks′ : (s : P ≋′ Q) → 𝔽 (pc P) → 𝔽 (pc Q) → Set` (one constructor per axiom and position:
`comm-l/comm-r`, `assoc`, `unit` (`suc i ↦ i`; the unit thread is untracked), `swap`, `comm-ν`, `ext`
(identity up to `Fin.cast (processCount-rename …)`), `cong-l/cong-r`, `cong-ν`) and
`Tracks : (d : P ≋ Q) → 𝔽 (pc P) → 𝔽 (pc Q) → Set` (`ε`, `fwd`, `bwd`).  Algebra: `tracks-◅◅`,
`tracks-sym` (`Eq*.symmetric`), `tracks-gmap` for `ν-cong`/`∥-cong` (`𝐓.∥-cong ps qs` is
`gmap ∥-cong′ ps ◅◅ ∥-comm ◅◅ gmap ∥-cong′ qs ◅◅ ∥-comm`), `tracks-≡→≋`/`tracks-subst` (by `J`),
`tracks-≋-plug`/`tracks-≋-plugL` (`threadInContext` is preserved), and the instances used by
`Canonical` (`∥-comm`, `∥-assoc`, `∥-unitʳ`, `ν-ext′`, `ν-comm′`, `ν-swap′`).
P5.1 **`BackwardSoup/TracksImage.agda`** — `≋-image` respects `Tracks`:
`≋-image-tracks : Tracks d a b → threadEmbedding (proj₂ (≋-image d I)) b ≡ threadEmbedding I a`, via
`≋′-image-tracks`/`≋′-image⁻-tracks` (reindex cases reduce to `threadBackward` computations; unit and
congruence cases are definitional through `par-split-*`/`par-join`/`res-split-image`/`res-join`).
P5.2 **`Canonical.agda`/`CanonicalPair.agda` tracking fields** — `Bubble.tracks`
(`∀ Z₀ t → Tracks (≋-eq Z₀) (threadInContext c Z₀ t) (thread t of Z₀ in the target)`), a tracking
clause for `foldPar`, `push`, `foldPar₂`, `push₂`, `bubblePar`, `bubble₂`; `Canon.tracks :
Tracks ≋-canon (threadInContext ctx ⟪ e ⟫ 0F) (threadInContext above′ (ν C₁ C₂ (⟪ e ⋯ ρ ⟫ ∥ resid)) 0F)`
and the same for `CanonHead`, `CanonRedex`, `CanonAcq`, `CanonSplit`, `Canon₂` (two clauses, `0F`/`1F`
of `(⟪ e₁ ⟫ ∥ ⟪ e₂ ⟫) ∥ resid`), `CanonPair`; `canon-swap`/`canon-swap₂` keep the index (`ν-swap′`
tracks identically up to the `processCount-rename` cast).
P5.3 **`BackwardSoup/Unique.agda`** — unique decomposition of soup redexes:
`redex-unique : Value v → Value v′ → F [ K c ·¹ v ]* ≡ F′ [ K c′ ·¹ v′ ]* → (c ≡ c′) × (v ≡ v′) ×
(∀ t → F [ t ]* ≡ F′ [ t ]*)` (stated on plugged terms, as `Inversion.agda` does), plus the list
lemma `xs ++ a ∷ ys ≡ xs′ ++ a ∷ ys′ → length xs ≡ length xs′ → xs ≡ xs′ × ys ≡ ys′` for the flag
splits of Drop/Acq.
P5.4 **Exposure in the forward leaves** (`ForwardSoup/Local/Step.agda` + each `Local/<Rule>.agda`):
`ConfigStep P′ σ aC aT C C′` = `LocalStep` with the target configuration as an INDEX
(`step : C ─→ₚ C′`, `embedding`, `logicalChannels′`, `image′`), `identity-config-step`,
`configStep⇒localStep`.  Each leaf gains `<rule>-step : image → <Rule>Step image` whose record fixes
the slot(s) (`slot-eq : threadEmbedding image 0F ≡ just slot`), the frame(s) with the thread content
(`lookup ts slot ≡ frame [ K c ·¹ arg ]*`, `Value arg`), the rule's other data (channel, side,
`before`/`after` with the flag equation, sent value, choice) and `result : ConfigStep … (RUS-result)`;
`U-<rule>-local` becomes a corollary.  `U-new-local` is generalised over the insertion index
(`0F` is not forced anywhere; `V.insertAt-punchIn`/`insertAt-lookup` are index-generic).  RSplit exposes
the canonical `before` (`prefixFlags`).
P5.5 **`BackwardSoup/Lift.agda`** — `plug-red : (ctx) → P ─→ₚ P′ → plug ctx P ─→ₚ plug ctx P′`
(`R-Par`, `R-Struct ∥-comm` for `par-right`, `R-Bind`); image descent `focusImage` along a
`ProcessContext` (`par-split-left/right`, `res-split-image`; thread embedding
`threadEmbedding image ∘ threadInContext ctx P` definitionally) with `Separated`/`ValueEnv`/typing
descent; image ascent `liftConfigStep : ConfigStep P′ (focused) … C C′ → ConfigStep (plug ctx P′) σ aC aT C C′`
(the `R-Par`/`R-Bind` bodies of `ForwardSoup/Local.agda`'s `local-sim`, plus the mirrored `par-right`).
P5.6 **`BackwardSoup/Leaves/<Rule>.agda`** — per soup rule: `image-thread-term` (slot ↦ located
thread), `plug-inversion-K`, `handle-value-var`, `resolve` + `Position/Crux` shape, `canon-*`,
`≋-image` + `≋-image-tracks` (⇒ canonical redex ↦ `j`), `focusImage above′`, the exposed forward
leaf, `redex-unique` (⇒ the forward reduct IS the soup reduct), `liftConfigStep`, and the typed step
`R-Struct ≋-canon (plug-red above′ (R-<rule>)) ε`.  Two-thread rules build `Binder₂` from the two
`resolve`s (same physical channel ⇒ same logical channel by `channelEmbedding-injective` ⇒ same `bind`
node) and use `canon-pair`; Com/Close use `PairConfine`.  RSplit returns the forward configuration
`C″` and `C″ ≈ˢ C′` (slot renumbering between `prefixFlags B₁` and the soup's `before`).  New uses
the soup's insertion index.  Exp needs no canonicalisation (`step-inversion` + `plug-red`).
P5.7 **`BackwardSoup/Main.agda`** — `backward-core` (`C₀ ≡ C`) by cases on the eleven rules, and
`backward-sim : Backward-Sim` from `backward-core` and `Slot-Bisim`.
P5.8 **`BackwardSoup/SlotBisim.agda`** — `≈¹` commutes with every soup rule (`swapPhi` against
`consumePhi`/`insertPhi`/`_[_]*`/`_⋯ᵣ_`; templates `Local/AcqSupport.agda`, `Local/InsertSupport.agda`).
