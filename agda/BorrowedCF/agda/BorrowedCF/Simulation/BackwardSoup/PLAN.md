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
