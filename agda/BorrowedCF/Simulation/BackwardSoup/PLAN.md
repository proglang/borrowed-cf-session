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
