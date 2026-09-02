# Forward simulation Typed → UntypedSoup: status and completion plan

Date: 2026-09-02. Branch `codex/soup-of-processes`, HEAD `0d85b84`.

## 1. Where things stand

### 1.1 Files and typecheck status

| Module (under `Simulation/ForwardSoup/`) | Lines | Checks? | Holes | Image notion |
|---|---|---|---|---|
| `../ForwardSoup.agda` (dispatcher, untracked) | 49 | **no, scope error at line 20** (`;` not in scope) | 9 | `SoupImage` |
| `Base`, `Image`, `Image/ThreadPermutation`, `Expressions`, `Translation`, `Renaming` | — | yes | 0 | `SoupImage` |
| `Exp`, `Fork`, `New`, `Close`, `Choice`, `Com` | 80/202/298/382/352/1834 | yes | 0 | `SoupImage`, arity 0 |
| `LSplit` (untracked) | 1519 | loads, goals only | 3 | `SoupImage`, arity 0 |
| `RSplit` (untracked) | 1282 | loads, goals only | 7 | `SoupImage`, arity 0 |
| `LocalImage`, `LocalImage/{Properties,Congruence,Renaming,PhysicalRenaming,Restriction}` | 189/92/675/113/281/405 | yes | 0 | `LocalImage` |
| `World`, `World/Embedding` | 45/63 | yes | 0 | `GlobalImage` = `LocalImage` at arity 0 |
| `Context`, `Context/{Properties,Replacement}` | 225/406/336 | yes | 0 | `LocalImage` |

`PhysicalRenaming.agda` has 165 uncommitted lines (`UB-ren-coherent`, `flattenChannels-physical`,
`flattenThreads-physical`); they typecheck and are needed (see 4.2).

### 1.2 How to typecheck

* Batch `agda` on anything importing `Reduction/Processes/Typed.agda` fails: that module's
  `preservationₚ` has unsolved constraints (R-Com case, lines 276–281). The command-line flag
  `--allow-unsolved-metas` is rejected because the standard library is `--safe`. The project
  convention (see `Types/Predicates.agda:1`) is a per-file pragma. **Step 0: add
  `{-# OPTIONS --allow-unsolved-metas #-}` to `Reduction/Processes/Typed.agda`.** Verified: with
  that pragma, the interaction-protocol load of `LSplit.agda`/`RSplit.agda` succeeds.
* To load a file with holes from the shell (Emacs-equivalent, prints goals):

  ```bash
  F=$PWD/BorrowedCF/Simulation/ForwardSoup/LSplit.agda; printf 'IOTCM "%s" NonInteractive Indirect (Cmd_load "%s" [])\n' "$F" "$F" | agda --interaction | grep -o '(agda2-info-action "\*[A-Za-z ]*\*" "[^"]*' | sed 's/\\n/\n/g'
  ```

  Goal types: `Cmd_goal_type_context Normalised <id> noRange ""` in the same session.
* Note in passing: `Simulation/Forward.agda` (the untyped-target analogue) is stale — it imports
  the removed module `BorrowedCF.TypedEq`; `⊢-≋` now lives in `Processes/Congruence.agda:242` as
  `_/_⊢-≋_ : ChanCx Γ → Γ ; γ ⊢ₚ P → P ≋ Q → Γ ; γ ⊢ₚ Q`.

### 1.3 Two disjoint image worlds

* **`SoupImage P C`** (`Image.agda`): `P : Proc 0`, total function embeddings for channels and
  threads, an `endpointEmbedding`, forward orientation only, no frame. Used by the dispatcher and by
  every leaf case. `live-thread` states `lookup threads (emb j) ≡ canonicalThread j ⋯ᵣ ρ`.
* **`LocalImage P lc σ aC aT C`** (`LocalImage.agda`): `P : Proc k`, an environment
  `σ : Env k (2n)` for the free channel variables, a vector `lc` of *oriented* physical channels,
  partial thread embedding (`Maybe`, with `omitted` for unit threads), and two *ambient* predicates
  exempting context-owned resources from both the live and the garbage obligations.
  `GlobalImage` (`World.agda`) is `LocalImage` at arity 0 with empty env and empty frame.
* Nothing converts between them (only `flattenOriented-forward` relates the two flattenings), and
  no leaf lemma is stated for `LocalImage`.

What exists in the `LocalImage` world:

| Need | Exists | Missing |
|---|---|---|
| generic transport | `reindex-image` via `ImageReindex` (`LocalImage/Congruence.agda:110,159`) | inverse `ImageReindex` |
| `∥-comm′` | `parallel-swap-image` | — |
| `∥-assoc′` | `parallel-assoc-image` (one direction) | reverse (from inverse reindex) |
| `∥-unit′` | `unit-left-elim`, `unit-left-intro` | — |
| `ν-swap′` | `restriction-swap-image` (uses orientation flip) | reverse |
| `ν-comm′`, `ν-ext′` | — | both |
| `∥-cong′`, `ν-cong′`, `EqClosure` | — | all |
| descent into a context (R-Par/R-Bind) | `focus-image` (`Context/Properties.agda:309`) | ascent / plug-back |
| source-side renaming absorbed by env | `rename-image` (`LocalImage/Renaming.agda:98`) | — |
| physical renaming of flattened data | `flattenChannels-physical`, `flattenThreads-physical` (uncommitted) | image-level consequence |
| growing the soup (New/Fork) with a frame | `AmbientEmbedding` (`World/Embedding.agda`, imported by nothing) | transport of a `LocalImage` along it |

### 1.4 State of the leaf cases

* `Exp`, `Fork`, `New`, `Close`, `Choice`, `Com`: complete for closed processes (`SoupImage`).
  `Com` is not wired into the dispatcher. `U-com` is stated for head groups `suc (suc b) ∷ B`; this
  is the right shape (a send handle has type `⟨ msg ‼ T ⟩`, so it can never be the last binder of a
  group, whose type ends in `ret`/`end`), but the wiring needs the typed-side inversion lemmas
  `com-head≥1`/`com-head≥2` from `Support/Theorems/ComHelpers2.agda:330,263` and a `with … | refl`.
  `⊢P` is otherwise unused by `U-com`.
* `LSplit`: complete except `source-target-lwk` (env agreement across `lwk`, 2 holes) and
  `live-thread′ (suc l)` (residual threads across `P ⋯ₚ lwk`, 1 hole).
* `RSplit`: same three holes plus four more; **`parent` and `C′` are stale copies from LSplit**
  (the RSplit result must carry `` `phi (x , k) `` in the two new triples and
  `V.updateAt cs i (appendEndpointFlag side drop)`), which blocks the step witness (line 823),
  `live-channel′ zero` (1033), `target-body` (1099), and `bindFlags-rsplit` (392).
* Both split files: the `with Fin.splitAt … y` in `source-target-lwk` abstracts without `in eq`,
  so the two `inj` branches cannot be closed as written (must use `with … in split` +
  `Fin.join-splitAt`). About 800 lines are byte-identical between the two files.
* `Drop`, `Acq`, `Discard`: not started. `R-Par`, `R-Bind`, `R-Struct`: not started.

## 2. Diagnosis: the leaf lemmas must move to `LocalImage`

The frame cases force this. `R-Bind red : ν B₁ B₂ P ─→ ν B₁ B₂ Q` with `P : Proc (sum B₁ + sum B₂)`
requires simulating a step of an *open* process whose free variables are bound by the enclosing
ν, i.e. a leaf lemma at arity `k` with an environment `σ`. Closed-process leaf lemmas cannot be
lifted: the source calculus has no substitution of channel values, and the redex cannot be floated
to the top by `≋` because its evaluation frames may mention outer binders (a ν cannot be commuted
past threads that use its channel). The analogous untyped-target proof (`Forward.agda`) is stated
at arbitrary arity with a value substitution `σ` for exactly this reason.

`R-Struct` independently forces orientation (`ν-swap′` flips the polarity of a physical channel),
which `SoupImage` cannot express.

Consequences:

1. The final theorem is stated with `GlobalImage`, derived from a local simulation at arity `k`.
2. The six finished leaf cases are ported from `SoupImage` to `LocalImage`; `LSplit`/`RSplit` are
   finished directly in `LocalImage` form; `Drop`/`Acq`/`Discard` are written in that form.
   The port is mostly mechanical and *removes* work: in `LocalImage` the expected thread is
   `lookup (proj₂ (flattenOriented P lc σ)) j` on the nose (no `canonical … ⋯ᵣ ρ` detour), so the
   `translated-renamed`/`canonical-empty` plumbing and Com's `flatten-ren-threads`,
   `flatten-endpoint-thread` (≈330 lines) are replaced by `rename-image` plus an env-coherence
   fact of the form `σₛ (wkρ y) ≡ σₜ y`.
3. The `Context`/`ProcessContext` machinery is not needed for the recursion (the typed reduction is
   already inductive through `R-Par`/`R-Bind`); it can be retired once the two split/join lemmas
   of 4.1 exist, or kept to derive `∥-cong′`/`ν-cong′`.

## 3. Target statements

```agda
-- One local step, with the frame carried across.
record LocalStep {k n m} (P′ : Typed.Proc k) (σ : Env k (2 *ℕ n))
       (aC : 𝔽 n → Set) (aT : 𝔽 m → Set) (C : Soup.Config n m) : Set where
  field
    n′ m′       : ℕ
    C′          : Soup.Config n′ m′
    step        : C SoupReduction.─→ₚ C′
    emb         : AmbientEmbedding aC aT C C′          -- identity except New (channel) / Fork (thread)
    lc′         : Vec (OrientedChannel n′) (channelCount P′)
    image′      : LocalImage P′ lc′ (renameEnv (endpointEmbedding emb) σ)
                    (targetAmbientChannel emb) (targetAmbientThread emb) C′

Local-Sim : Set
Local-Sim = ∀ {k} {Γ : Ctx k} {g} {P P′ : Typed.Proc k} {n m}
  {lc} {σ : Env k (2 *ℕ n)} {aC aT} {C : Soup.Config n m} →
  ChanCx Γ → Γ ; g ⊢ₚ P → ValueEnv σ →
  Separated lc σ aT C →            -- only Acq needs it; see 4.5
  LocalImage P lc σ aC aT C → P ─→ₚ P′ → LocalStep P′ σ aC aT C

sim→ : [] ; [] ⊢ₚ P → GlobalImage P C → P ─→ₚ P′ → GlobalStepImage P′ C   -- Local-Sim at k = 0
```

`renameEnv` is in `LocalImage/PhysicalRenaming.agda:21`; `AmbientEmbedding`,
`targetAmbientChannel/Thread` in `World/Embedding.agda`. For the top-level instance the transported
frame `Transport emb (λ _ → ⊥)` is empty; a one-line `LocalImage` ambient-congruence lemma turns
it back into `λ _ → ⊥`.

Dispatcher shape (mirrors `Forward.agda`):

* `R-Par red`: `par-split` → recurse on the left → `ambient-transport` of the right half → `par-join`.
* `R-Bind red`: `res-split` (env extended by `UB[B₁] ++ₛ UB[B₂]`, head channel becomes ambient) →
  recurse (typing of the body from `inv-ν`) → `res-join` (head channel content preserved by
  `ambient-channel-content`).
* `R-Struct e₁ red e₂`: `≋-image e₁` → recurse (typing via `Γ-S / ⊢P ⊢-≋ e₁`) → `≋-image e₂`.
* leaves: the `LocalImage` leaf lemmas.

## 4. Work plan

Phases are ordered by dependency. Sizes are rough line counts of new Agda.

### Phase 0 — make the development checkable (small)

1. Add the `--allow-unsolved-metas` pragma to `Reduction/Processes/Typed.agda`.
2. Fix the dispatcher's scope error (`_;_⊢ₚ_` must be opened from `Processes.Typed`, as
   `Simulation/Base.agda` does) so `ForwardSoup.agda` loads with its holes.
3. Wire `U-com` (import `Com`, name `{E₁} {E₂}`, split on `com-head≥1`/`≥2`) so `R-Com` closes in
   the *current* `SoupImage` dispatcher. This is throwaway once Phase 2 lands but proves the
   typed-side inversion route works (ComHelpers2 is batch-importable: no holes, interface present).
4. Commit `LSplit.agda`, `RSplit.agda`, `ForwardSoup.agda`, and the `PhysicalRenaming.agda` diff.

### Phase 1 — `LocalImage` frame algebra and congruence closure (≈900 lines)

All in new modules under `LocalImage/` unless noted.

1. **Orientation kit** (`LocalImage.agda`, ≈40 lines): `Opposite (orientSide o 0F) (orientSide o 1F)`;
   `endpointFlags (orientChannel o (b , f₁ , f₂)) (orientSide o s) ≡ endpointFlags (b , f₁ , f₂) s`;
   `setEndpointFlags`/`appendEndpointFlag` commute with `orientChannel`. Lets every leaf lemma use
   `side = orientSide o zero` instead of `zero` and stay agnostic of polarity.
2. **`par-split` / `par-join`** (`LocalImage/Parallel.agda`, ≈250):
   ```agda
   LocalImage (P ∥ Q) lc σ aC aT C
     ⇔ LocalImage P (take lc) σ (aC ∪ chansOf (drop lc)) (aT ∪ threadsOf Q) C
     × LocalImage Q (drop lc) σ (aC ∪ chansOf (take lc)) (aT ∪ threadsOf P) C
   ```
   with the disjointness facts. Reuse `flatten-par-channels/threads` (`Congruence.agda:218,235`)
   and the `par hole Q` instance of `focus-channel`/`focus-thread`.
3. **`res-split` / `res-join`** (`LocalImage/Restriction.agda`, ≈200):
   ```agda
   LocalImage (ν B₁ B₂ P) (c ∷ lc) σ aC aT C
     ⇔ LocalImage P lc ((UB[B₁] r₁ … ++ₛ UB[B₂] r₂ …) ++ₛ σ) (aC ∪ {physicalChannel c}) aT C
     × lookup (channels C) (physicalChannel c) ≡ orientChannel (proj₂ c) (true , flags₁ , flags₂)
   ```
4. **`ambient-transport`** (`LocalImage/Embedding.agda`, ≈200): a `LocalImage Q` all of whose
   resources lie in the ambient of an `AmbientEmbedding emb : C ⇒ C′` is transported to `C′` with
   `lc ↦ map (renameOriented (channelEmbedding emb)) lc`, `σ ↦ renameEnv (endpointEmbedding emb) σ`.
   Uses `flattenChannels-physical`/`flattenThreads-physical`. Garbage clauses of the result come
   from the *stepped* image, so state this lemma for the live/ambient clauses only and let
   `par-join` take garbage from the other half.
5. **`reindex-sym`** (`Congruence.agda`, ≈60): invert an `ImageReindex` (both maps and round-trips
   are already fields). Gives the reverse directions of `∥-assoc′` and `ν-swap′` for free.
6. **`ν-comm′` and `ν-ext′` as `ImageReindex`es** (`Restriction.agda`, ≈250). `ν-ext′` is a
   rotation of the channel vector plus `rename-image` for `P ⋯ₚ weaken*` with coherence
   `++ₛ-lookupʳ`; `ν-comm′` swaps the two head channels plus an `assocSwapᵣ` coherence lemma in the
   style of `swap-prefix-coherent` (`Renaming.agda:210`).
7. **`≋-image`** (`LocalImage/Congruence.agda` or new `Struct.agda`, ≈120): induction over
   `EqClosure _≋′_`; `∥-cong′`/`ν-cong′` from items 2–3 with the identity embedding (or from
   `focus-image` + plug-back if the Context route is kept).

### Phase 2 — the skeleton (≈250 lines)

1. `LocalStep`, `Local-Sim`, `sim→` as in section 3 (`ForwardSoup/Base.agda` and `ForwardSoup.agda`).
2. Dispatcher with `R-Par`, `R-Bind`, `R-Struct` fully proved from Phase 1, and one `postulate`d
   (or holed) `LocalImage` leaf lemma per remaining rule, stated in final form. This fixes the
   leaf statements before the expensive ports start and lets the whole file typecheck.
3. Retire `SoupImage`-based `Forward-Sim`/`StepImage` or keep them as a corollary at arity 0.

### Phase 3 — leaf lemmas in `LocalImage` form

Common skeleton for every case: (i) the redex thread is `present` (its expected term is not
`K `unit`); (ii) `T[_]-plugᶠ*` exposes `F [ K c ·¹ arg ]*` and `UB-head`/env lookups give the
`chanTriple` with endpoint `physicalEndpoint (lookup lc 0F) side`; (iii) build `C′` and the `RUS-*`
step; (iv) `live-channel 0F` by the flag lemma of the rule, other channels unchanged;
`live-thread` for redex threads by the target env, for the residual `P ⋯ₚ ρ` by `rename-image`
with the env coherence `σₛ (ρ y) ≡ σₜ y`; garbage/ambient untouched (identity embedding).

Order (cheapest and most instructive first):

1. **Exp, Fork, New, Close** (port; ≈600 total). `New` and `Fork` are the two cases with a
   non-identity `AmbientEmbedding` (`punchIn` on channels resp. threads) and exercise
   `ambient-transport`. `Close` kills a channel: `garbage-channel` gains the closed channel.
2. **Choice** (port; ≈300). No typing needed.
3. **Com** (port; ≈1000). Keep `UB-flags-drop`, `Ub-drop`, `UB-env-drop`, `UB-head`,
   `UB-coherent`, `source-targetEnv` (Com.agda 171–780) after generalising `+ 0` to `+ k`; drop the
   flatten-renaming block (1008–1335). Wire with `com-head≥1/≥2`.
4. **Split common module + LSplit + RSplit** (≈1200 after dedup). Move the generic
   `T-ren-ren-coh`, `lift-ren-ren-coh`, `Tᶠ-plug-ren-ren-coh`, `Tᶠ*-plug-ren-ren-coh` to
   `Expressions.agda`; put `channelShape`, `bindFlags`, `UB-flags-shape`, the `group-*-shape`
   family, `blockAt`/`atk-blockAt` casts in `SplitCommon.agda`. Fix `RSplit`'s `parent`/`C′`;
   write `bindFlags-rsplit` (from `positive-flag`) and a `group-rsplit-shape` over `rightGroup`.
   The three shared holes become: `source-target-lwk`/`-rwk` (env agreement, prove by induction on
   `B₁` following `dlwkq-lo/hi`, LSplit 284–419) and the residual-thread clause, which in
   `LocalImage` form is exactly `rename-image` with that agreement.
   Typing enters only through `lsplit-confine`/`rsplit-confine` (`Support/SplitConfine.agda`),
   already used.
5. **Discard** (new; ≈300). Cases: `b₁ = suc _` (flags unchanged, env shift like `Ub-drop`);
   `b₁ = 0, B₁ = []` (last group, no flags); `b₁ = 0, B₁ ≠ []` impossible by typing
   (`disc-b0-vac`, `discard-handle-≃skip` in `Forward/Discard.agda:39–52`; lift them into a
   typed-only Support module).
6. **Drop** (new; ≈400). Typing forces `b₁ = 0` and `B₁ ≠ []` (`drop-handle-≃ret`,
   `head-noRet-last`, `noRet⇒≄ret`, `retTip-Sc-skips` in `Support/Theorems/Drop.agda:601–625` and
   `Theorems/B1VacProbe.agda`; lift likewise). Then the handle's triple is
   `Ub[ 1 ] (* , x , `phi (x , 0))`, `before = []`, and `RUS-Drop` flips `drop ↦ acq` matching
   `ϕ[ 1 ] ↦ ϕ[ 0 ]`; the env for `B₁` is `UBFrom 1 B₁ x (phi (x , 0) , x , *)` on both sides;
   residual via `rename-image` with `weakenᵣ` coherence.
7. **Acq** (new; ≈600). `RUS-Acquire` deletes flag `k` (= number of preceding groups, i.e. the
   `UBFrom k` index) and maps `consumePhi x k` over *all* threads. Needs:
   `consumePhi-T : consumePhi x k (T[ e ] σ) ≡ T[ e ] (consumePhi x k ∘ σ)`;
   `consumePhi` on `UBFrom (suc k) B x …` re-indexes to `UBFrom k B x …` (matches `shiftSlot`);
   `consumePhi x k (K `unit) ≡ K `unit` for garbage; typing via `acq-confine`
   (`Support/SplitConfine.agda:96`). For ambient threads see 4.5.

### Phase 4 — cleanup

Delete dead lemmas listed in the LSplit/RSplit survey (`ub-at`, `Ub-env-ren`, `UB-lookupʳ`,
`lsplit-flags`, `syncs-lsplit`, stale `targetSplitShape` in RSplit), the `SoupImage` copies of
lemmas now in `LocalImage` form, and `Context/*` if unused. One commit per leaf case.

### 4.5 The one genuinely new invariant: phi-separation for Acq

`RUS-Acquire` rewrites every thread with `consumePhi x k`. `AmbientEmbedding` demands that ambient
threads be preserved (up to endpoint renaming), so the Acq leaf lemma needs
`∀ j → aT j → consumePhi x k (lookup threads j) ≡ lookup threads j`, i.e. ambient threads carry
no `` `phi (x , _) `` for the acquired endpoint. From the local view this is unknowable, so
`Local-Sim` carries a hypothesis

```agda
Separated lc σ aT C = ∀ j → aT j → ∀ i side → PhiFree (physicalEndpoint (lookup lc i) side) (lookup (threads C) j)
```

(and the analogous fact for `σ`'s terms). It is trivial at the top level (`aT = ⊥`, `σ = λ ()`),
and `par-split`/`res-split` must re-establish it for the newly ambient threads. That needs a
scoping lemma about the translation (≈200 lines, new module `Translation/Scoping.agda`):
phi references in `proj₂ (flattenOriented P lc σ) j` point only to endpoints of channels in `lc`
or occur in `σ`; hence sibling/context threads never mention the hole's channels (injectivity of
`lc`). Decide in Phase 2 whether to put `Separated` into `Local-Sim` or into `LocalImage` itself;
the former keeps all existing `LocalImage` lemmas untouched.

## 5. Reusable typed-side material (no soup dependency)

`Support/SplitConfine.agda` (`lsplit-confine`, `rsplit-confine`, `acq-confine`),
`Support/InvFrame.agda` (`strengthen-frame`, `arg-type`, `fn-*-dom`), `Support/Strengthen.agda`,
`Support/Confine.agda`, `Support/AcqInv.agda`, `Support/Theorems/ComHelpers2.agda`
(`com-head≥1/≥2`), `Support/Theorems/Drop.agda:601–625` and `Theorems/B1VacProbe.agda` (drop
vacuity), `Forward/Discard.agda:32–52` (discard vacuity), `Processes/Typed.agda` (`inv-ν`, `inv-∥`,
`inv-⟪⟫`, `bindCtx⇒chanCtx`), `Processes/Congruence.agda:242` (`_/_⊢-≋_`). All have interfaces
and no holes; they only become importable after the Phase 0 pragma.

## 6. Phase 1/2 detailed design (2026-09-02, second session)

Decisions taken after re-reading `LocalImage`, `World/Embedding`, `Congruence`, `Restriction`:

* `Separated` is a **hypothesis of `Local-Sim`**, not a field of `LocalImage`; it never mentions
  `lc`, so it is invariant under `≋` and monotone in the ambient sets:
  ```agda
  PhiFreeFor : (𝔽 n → Set) → SoupTerm.Tm (2 *ℕ n) → Set
  PhiFreeFor aC t = ∀ (i : 𝔽 n) (side : 𝔽 2) (k : ℕ) → ¬ aC i →
    SoupReduction.consumePhi (Soup.endpoint i side) k t ≡ t
  record Separated (σ : Env k (2 *ℕ n)) (aC : 𝔽 n → Set) (aT : 𝔽 m → Set) (C : Config n m) where
    env-separated    : ∀ x → PhiFreeFor aC (σ x)
    thread-separated : ∀ j → aT j → PhiFreeFor aC (lookup (threads C) j)
  ```
  i.e. ambient threads and the environment mention `phi` only on ambient channels.
* `ambient-transport` produces an image whose ambient sets are the **complements of the
  transported resources**; garbage clauses are then vacuous and `par-join` does all bookkeeping.
* Frame-case helper statements (all in new modules under `LocalImage/`):

  `Frame.agda` (shared): `_∪ᵖ_`, `singletonᵖ`, `ownedChannels lc`, `ownedThreads te`,
  `ambient-resp` (pointwise-equivalent ambient predicates), `env-resp` (pointwise-equal envs,
  via `flattenOriented-env-cong`), `bindEnv B₁ B₂ c σ`, `bindChannel B₁ B₂ c`, `flatten-bind`.

  `Parallel.agda`: `par-split-left`, `par-split-right`, `par-join` (see agent brief in §6.1).

  `Bind.agda`: `res-split`, `res-join`.

  `Embedding.agda`: `ambient-transport` along an `AmbientEmbedding`.

  `Separation.agda`: `Separated`, `separated-mono`, `separated-bind`, `separated-par-left`
  (+ `consumePhi-ren`, `consumePhi-T`, `flatten-phi-free`).

  `Struct.agda`: `reindex-sym`, the `ImageReindex`es for `ν-comm′` and `ν-ext′`, `≋′-image`
  (both directions) and `≋-image : P ≋ Q → LocalImage P lc … → Σ lc′. LocalImage Q lc′ …`.

### 6.1 Statements

```agda
-- Frame.agda
_∪ᵖ_ : (𝔽 a → Set) → (𝔽 a → Set) → 𝔽 a → Set ;  (p ∪ᵖ q) i = p i ⊎ q i
singletonᵖ : 𝔽 a → 𝔽 a → Set ;  singletonᵖ c i = c ≡ i
ownedChannels : Vec (OrientedChannel n) k → 𝔽 n → Set
ownedChannels lc i = Σ[ j ∈ 𝔽 k ] physicalChannel (lookup lc j) ≡ i
ownedThreads : (𝔽 k → Maybe (𝔽 m)) → 𝔽 m → Set
ownedThreads te l = Σ[ j ∈ 𝔽 k ] te j ≡ just l
ambient-resp : (∀ i → aC i → aC′ i) → (∀ i → aC′ i → aC i) →
               (∀ l → aT l → aT′ l) → (∀ l → aT′ l → aT l) →
               LocalImage P lc σ aC aT C → LocalImage P lc σ aC′ aT′ C
flattenOriented-env-cong : (∀ x → σ x ≡ σ′ x) → flattenOriented P lc σ ≡ flattenOriented P lc σ′
env-resp : (∀ x → σ x ≡ σ′ x) → LocalImage P lc σ aC aT C → LocalImage P lc σ′ aC aT C
bindEnv : (B₁ B₂ : BindGroup) → OrientedChannel n → Env k (2 *ℕ n) → Env (sum B₁ + sum B₂ + k) (2 *ℕ n)
bindEnv B₁ B₂ c σ =
  (proj₁ (UB[ B₁ ] (physicalEndpoint c 0F) (* , physicalEndpoint c 0F , *)) ++ₛ
   proj₁ (UB[ B₂ ] (physicalEndpoint c 1F) (* , physicalEndpoint c 1F , *))) ++ₛ σ
bindChannel : (B₁ B₂ : BindGroup) → OrientedChannel n → Soup.Channel
bindChannel B₁ B₂ c = orientChannel (proj₂ c) (true , proj₂ (UB[ B₁ ] …) , proj₂ (UB[ B₂ ] …))
flatten-bind : flattenOriented (ν B₁ B₂ P) (c ∷ lc) σ ≡
  (bindChannel B₁ B₂ c ∷ proj₁ (flattenOriented P lc (bindEnv B₁ B₂ c σ)) ,
   proj₂ (flattenOriented P lc (bindEnv B₁ B₂ c σ)))

-- Parallel.agda
par-split-left : (image : LocalImage (P ∥ Q) lc σ aC aT C) →
  LocalImage P (V.take (channelCount P) lc) σ
    (aC ∪ᵖ ownedChannels (V.drop (channelCount P) lc))
    (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (processCount P ↑ʳ_))) C
par-split-right : (image : LocalImage (P ∥ Q) lc σ aC aT C) →
  LocalImage Q (V.drop (channelCount P) lc) σ
    (aC ∪ᵖ ownedChannels (V.take (channelCount P) lc))
    (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (_↑ˡ processCount Q))) C
par-join : (imageP : LocalImage P lc₁ σ aC₁ aT₁ C) (imageQ : LocalImage Q lc₂ σ aC₂ aT₂ C) →
  (∀ j → aC₁ (physicalChannel (lookup lc₂ j))) →
  (∀ {j l} → threadEmbedding imageQ j ≡ just l → aT₁ l) →
  (∀ i → aC i → aC₁ i) → (∀ i → aC i → aC₂ i) →
  (∀ l → aT l → aT₁ l) → (∀ l → aT l → aT₂ l) →
  (∀ i → aC₁ i → aC i ⊎ ownedChannels lc₂ i) →
  (∀ l → aT₁ l → aT l ⊎ ownedThreads (threadEmbedding imageQ) l) →
  LocalImage (P ∥ Q) (lc₁ V.++ lc₂) σ aC aT C
  -- thread embedding of the result: [ threadEmbedding imageP , threadEmbedding imageQ ]′ ∘ Fin.splitAt (processCount P)

-- Bind.agda
res-split : LocalImage (ν B₁ B₂ P) (c ∷ lc) σ aC aT C →
  LocalImage P lc (bindEnv B₁ B₂ c σ) (aC ∪ᵖ singletonᵖ (physicalChannel c)) aT C
  × lookup (channels C) (physicalChannel c) ≡ bindChannel B₁ B₂ c
res-join : LocalImage P lc (bindEnv B₁ B₂ c σ) (aC ∪ᵖ singletonᵖ (physicalChannel c)) aT C →
  lookup (channels C) (physicalChannel c) ≡ bindChannel B₁ B₂ c →
  LocalImage (ν B₁ B₂ P) (c ∷ lc) σ aC aT C

-- Embedding.agda
ambient-transport : (emb : AmbientEmbedding aC₁ aT₁ C C′) (image : LocalImage Q lc σ aC aT C) →
  (∀ i → aC₁ (physicalChannel (lookup lc i))) →
  (∀ {j l} → threadEmbedding image j ≡ just l → aT₁ l) →
  LocalImage Q (V.map (renameOriented (channelEmbedding emb)) lc) (renameEnv (endpointEmbedding emb) σ)
    (λ i → ¬ ownedChannels (V.map (renameOriented (channelEmbedding emb)) lc) i)
    (λ l → ¬ ownedThreads (Maybe.map (threadEmbedding emb) ∘ threadEmbedding image) l) C′

-- Separation.agda
separated-mono : (∀ i → aC i → aC′ i) → (∀ l → aT′ l → aT l) → Separated σ aC aT C → Separated σ aC′ aT′ C
separated-bind : Separated σ aC aT C → Separated (bindEnv B₁ B₂ c σ) (aC ∪ᵖ singletonᵖ (physicalChannel c)) aT C
consumePhi-ren : (ρ injective) → consumePhi (ρ x) k (t ⋯ᵣ ρ) ≡ consumePhi x k t ⋯ᵣ ρ
consumePhi-T : consumePhi x k (T[ e ] σ) ≡ T[ e ] (λ y → consumePhi x k (σ y))
flatten-phi-free : (∀ y → PhiFreeFor aC (σ y)) → (∀ i → aC (physicalChannel (lookup lc i))) →
  ∀ j → PhiFreeFor aC (lookup (proj₂ (flattenOriented Q lc σ)) j)
separated-par-left : Separated σ aC aT C → (image : LocalImage (P ∥ Q) lc σ aC aT C) →
  Separated σ (aC ∪ᵖ ownedChannels (V.drop (channelCount P) lc))
              (aT ∪ᵖ ownedThreads (threadEmbedding image ∘ (processCount P ↑ʳ_))) C

-- Struct.agda
reindex-sym : ImageReindex {P} {Q} lcP lcQ σP σQ → ImageReindex {Q} {P} lcQ lcP σQ σP
≋′-image  : P ≋′ Q → LocalImage P lc σ aC aT C → Σ[ lc′ ∈ _ ] LocalImage Q lc′ σ aC aT C
≋′-image⁻ : P ≋′ Q → LocalImage Q lc σ aC aT C → Σ[ lc′ ∈ _ ] LocalImage P lc′ σ aC aT C
≋-image   : P ≋ Q  → LocalImage P lc σ aC aT C → Σ[ lc′ ∈ _ ] LocalImage Q lc′ σ aC aT C
```

### 6.2 Skeleton (Phase 2)

```agda
record LocalStep (P′ : Proc k) (σ : Env k (2 *ℕ n)) (aC : 𝔽 n → Set) (aT : 𝔽 m → Set) (C : Config n m) : Set where
  field n′ m′ ; C′ : Config n′ m′ ; step : C ─→ₚ C′ ; emb : AmbientEmbedding aC aT C C′
        lc′ : Vec (OrientedChannel n′) (channelCount P′)
        image′ : LocalImage P′ lc′ (renameEnv (endpointEmbedding emb) σ) (targetAmbientChannel emb) (targetAmbientThread emb) C′
Local-Sim = ∀ {k Γ g P P′ n m lc σ aC aT C} → ChanCx Γ → Γ ; g ⊢ₚ P → ValueEnv σ →
  Separated σ aC aT C → LocalImage P lc σ aC aT C → P ─→ₚ P′ → LocalStep P′ σ aC aT C
```
R-Par: `par-split-left` → recurse (`separated-par-left`) → `ambient-transport` of `par-split-right`
along `emb` → `par-join` (hypotheses discharged by `Transport` algebra) → `LocalStep`.
R-Bind: `res-split` → recurse (`separated-bind`, `++ₛ-Value`/`UB-Value`, `inv-ν`) → `res-join` after
`ambient-resp` (`Transport ce (aC ∪ {c}) ⇔ Transport ce aC ∪ {ce c}`), `env-resp`
(`renameEnv ee (bindEnv c σ) ≐ bindEnv (renameOriented ce c) (renameEnv ee σ)` from `UB-ren-coherent`)
and `ambient-channel-content` + `UB-flags-ren` for the head channel.
R-Struct: `≋-image e₁` → recurse (`Γ-S / ⊢P ⊢-≋ e₁`, `separated` unchanged) → `≋-image e₂` on `image′`.

### 6.3 Status (2026-09-02, end of Phase 1)

Phase 0 done (`b26f164`, `51ca31e`; `ComHelpers2.agda` ported to vector contexts on the way).
Phase 1 done: `LocalImage/{Frame,Separation,SeparationFrame,Reindex,Parallel,Bind,Embedding,Commutation,Extrusion,Struct}.agda`,
all loading with 0 goals. Deviations from §6.1: `res-join` takes an extra `¬ aC (physicalChannel c)` (supplied by
`res-split-not-ambient`); `ambient-transport` exports `embedChannels`/`embedThreads`/`physicalChannel-embed`;
`Extrusion` names the renaming `extrusionRenaming B₁ B₂`; `≋-image` obtains the backward `ν-swap′` via
`Processes/Congruence.swapₚ-inv` and the backward `∥-assoc′` by a swap/assoc dance. Next: Phase 2 skeleton in
`ForwardSoup/Local.agda`.
Phase 2 done: `ForwardSoup/Local.agda` (`LocalStep`, `embedding-mono`, `Local-Sim : Set₁`, `local-sim` with R-Par/R-Bind/R-Struct
proved and 11 leaf holes, `sim-global`). Notes: `chanCx-⸴*` no longer exists in `Reduction/Base.agda` (`Forward.agda`
and `Backward/*` are stale); the typed context/struct types are `Context.Ctx`/`Context.Struct`; `_;_⊢ₚ_` uses U+037E.
Phase 3 layout: `Local/Step.agda` (record + identity embeddings + orientation kit), one `Local/<Rule>.agda` per leaf
exporting `U-<rule>-local : … → LocalStep …`, wired into `Local.agda`.
Phase 3 started (2026-09-02, third session). `Local/Step.agda` (307 lines, 0 goals) holds `LocalStep`,
`embedding-mono` and the shared leaf infrastructure: `ren-id` (identity renaming of soup terms),
`identity-embedding`/`identity-step` for the rules that keep both counts, the orientation kit
(`orientSide-opposite`, `open-orient`, `endpointFlags-orient`, `setEndpointFlags-orient`,
`appendEndpointFlag-orient`) and the redex-presence facts (`frame-not-K`, `K-head-irreducible`,
`K-irreducible`, `plug-not-K`).  `Local/Exp.agda` (102 lines, 0 goals) exports `U-exp-local`;
`Local.agda` is down to 449 lines and 10 goals.  Note: `Local/*.agda` may not define anything called
`image′`/`n′`/`m′`/`step`/`C′` — `Local/Step.agda` re-exports the `LocalStep` fields with `open … public`.
`Local/{Fork,New,Close}.agda` followed; `Local/Frames.agda` holds the frame/env coherence kit
(`T-ren-coh`, `Tᶠ*-plug-ren-coh`, `Tᶠ*-plug-renEnv`, `bindEnv-Value`, `renameEnv-Value`).
`Local/Step.agda` also exports `config-resp` (367 lines): an image only inspects *non-ambient*
positions, so it transports along any change of configuration confined to the ambient sets.  Every
leaf whose redex sits beside a residual process needs it for the sibling's image.
`Local/Choice.agda` (405 lines, 0 goals) exports `U-choice-local`; `Local.agda` is at 458 lines and
6 goals (R-Com, R-LSplit, R-RSplit, R-Drop, R-Acq, R-Discard).  The Choice shape —
`res-split` → `par-split-left`/`-right` → `UB-head` for both handles → `RUS-*` → rebuild with
`par-join`/`res-join` → `identity-step` — is the template for the R-Com port.
Staleness check (2026-09-02): `Support/Theorems/Drop.agda`, `Theorems/B1VacProbe.agda`, `Forward/Discard.agda` (and
`Forward.agda`, `Backward/*`) no longer load — contexts are vectors now (`lookup Γ x`, not `Γ x`). The Drop/Discard
vacuity lemmas must be re-established in a fresh typed-only module. `Support/SplitConfine.agda`, `Support/AcqInv.agda`
and (after the Phase 0 port) `Support/Theorems/ComHelpers2.agda` are current.
`Local/Discard.agda` (446 lines, 0 goals) exports `U-discard-local`; `Local.agda` is at 473 lines and
4 goals (R-LSplit, R-RSplit, R-Drop, R-Acq).  Two new shared modules came with it.
`Local/BindDrop.agda` (255 lines, 0 goals) holds everything the three *binder-shrinking* leaves
(`R-Com`, `R-Drop`, `R-Discard`) share: `lift*-↑ˡ`/`lift*-↑ʳ`, `split-left`/`-right`/`-ambient`,
`Ub-drop`/`UB-env-drop`/`UB-flags-drop` (lifted out of `Local/Com.agda`, now 735 lines), plus
`block-shift`, `UB-env-drop-last`, the three `weakenᵣ-bindEnv-coh`/`-last`/`-drop` environment
coherences and `bindChannel-drop`/`bindChannel-last`.
`Support/Theorems/DropShape.agda` (208 lines, 0 goals, no pragma) re-establishes the typed-side
vacuity arguments on vector contexts: `fn-discard-dom`, `discard-handle-≃skip`,
`discard-b0-vacuous`, `fn-drop-dom`, `drop-handle-≃ret`, `drop-b₁-zero`, `drop-B₁-cons`,
`drop-shape`.  It needs the `NoRet`/`RetTip` theory of `Support/Theorems/B1VacProbe.agda`, which
loads again after re-typing its two `BindCtx′` lemmas (`first-borrow-noRet`,
`last-first-borrow-≄ret`) for vector contexts; both were unused elsewhere.
For the `R-Drop` port: `drop-shape` gives `b₁ ≡ 0` and `B₁ ≡ c′ ∷ B′`, so the group shrinks
`1 ∷ c′ ∷ B′ ↦ 0 ∷ c′ ∷ B′`, the environment coherence is `weakenᵣ-bindEnv-coh-drop`, and the head
flag flips `ϕ[ 1 ] = drop ↦ ϕ[ 0 ] = acq` while the `UBFrom 1 (c′ ∷ B′) …` tail is shared — so
`RUS-Drop … before = []`, `after` = that tail's flag list, and the handle triple is
`𝓒[ * × end₁ × `phi (end₁ , 0) ]` (the `UB-head zero (c′ ∷ B′) …` clause).  The channel bookkeeping
needs `endpointFlags-orient` and `setEndpointFlags-orient` from `Local/Step.agda`.
