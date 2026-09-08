# C1 — Split.agda (structure-algebra toolkit) — STATUS

Owner: agent C1.  Files: `Completeness/Split.agda`, `Completeness/Split/*.agda`.
Wrapper: `agda-check BorrowedCF/Completeness/Split/X.agda`.  (The Agda MCP server
refused to connect for this session: protocol version mismatch, 2025-11-25 vs
2025-06-18.  Everything below was checked with `agda-check` only.)

## Lemma table

| lemma | statement | status | file |
|---|---|---|---|
| `count-↓-∈` | `x ∈ X → count x (γ ↓ X) ≡ count x γ` | proved | Split/Base.agda |
| `count-↓-∉` | `x ∉ X → count x (γ ↓ X) ≡ 0` | proved | Split/Base.agda |
| `count-↓` | `count x (γ ↓ X) ≡ (if does (x ∈? X) then count x γ else 0)` | proved | Split/Base.agda |
| `count-↓≤` | `count x (γ ↓ X) ≤ count x γ` | proved | Split/Base.agda |
| `mem⇒∈dom` / `∈dom⇒mem` / `mem-self` | `_∈ₘ_` ↔ `dom` | proved | Split/Base.agda |
| `mem-↓⁻` / `mem-↓⁺` | `x ∈ₘ (γ ↓ X) ↔ x ∈ X × x ∈ₘ γ` | proved | Split/Base.agda |
| `allCx-mem` | `AllCx P Γ α → x ∈ₘ α → P (Γ ﹫ x)` | proved | Split/Base.agda |
| `mem-allCx` | `(∀ z → z ∈ₘ α → P (Γ ﹫ z)) → AllCx P Γ α` | proved | Split/Base.agda |
| `allCx-↓-pointwise` | `(∀ z → z ∈ X → P (Γ ﹫ z)) → AllCx P Γ (γ ↓ X)` | proved | Split/Base.agda |
| `↓-∥` / `↓-;` / `↓-join` | restriction commutes with `∥` / `;` / `join a` (`↓-join` = `join-↓` of Context/Join.agda) | proved | Split/Base.agda |
| `↓-wk` | `wk γ ↓ (b ∷ X) ≡ wk (γ ↓ X)` | proved | Split/Base.agda |
| `↓-wk-tail` | `wk γ ↓ X ≡ wk (γ ↓ V.tail X)` (X : Subset (suc n); `fvClose = V.tail`) | proved | Split/Base.agda |
| `↓-wk²` | `wk (wk γ) ↓ X ≡ wk (wk (γ ↓ V.drop 2 X))` (`fvClose* 2 = V.drop 2`) | proved | Split/Base.agda |
| `↓-↓-⊆` | `X ⊆ Y → (γ ↓ Y) ↓ X ≡ γ ↓ X` | proved | Split/Base.agda |
| `↓-mono-⊆` | `X ⊆ Y → (∀ z → z ∈ Y → z ∉ X → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ X ≼ γ ↓ Y` | proved | Split/Base.agda |
| `↓-mono-⊆′` | same with `AllCx Unr Γ (γ ↓ Y ↓ ∁ X)` | proved | Split/Base.agda |
| `mob-dist` | `(∀ u v → u ∈ₘ P → v ∈ₘ Q → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)) → MobCx Γ P ⊎ MobCx Γ Q` | proved | Split/Base.agda |
| `SepXY` / `SepYX` / `Sep` | separation predicates (records, see below) | defined | Split/Base.agda |
| `sep-∥ˡ/ʳ`, `sep-;ˡ/ʳ` | `Sep` is inherited by substructures | proved | Split/Base.agda |
| `count-join` | `count x (join a α β) ≡ count x α + count x β`, generic in the `Join` instance | proved | Split/Lin.agda |
| `lin-≼` | `LinStruct Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → LinStruct Γ γ₁` | proved | Split/Lin.agda |
| `lin-↓` | `(Γ) (γ) (X) → LinStruct Γ γ → LinStruct Γ (γ ↓ X)` | proved | Split/Lin.agda |
| `lin-join⁻` | `(a) (Γ) (α β) → LinStruct Γ (join a α β) → LinStruct Γ α × LinStruct Γ β` | proved | Split/Lin.agda |
| `lin-;⁻` / `lin-∥⁻` | the `;` / `∥` instances of `lin-join⁻` | proved | Split/Lin.agda |
| `lin-wk` | `(T) (Γ) (γ) → LinStruct Γ γ → LinStruct (T ⸴ Γ) (wk γ)` | proved | Split/Lin.agda |
| `lin-bind` | `(a) (T) (Γ) (γ) → LinStruct Γ γ → LinStruct (T ⸴ Γ) (join a (` 0F) (wk γ))` | proved | Split/Lin.agda |
| `lin-bind₂` | `(a) (d) (T U) (Γ) (γ) → … → LinStruct (T ⸴ U ⸴ Γ) (join a (join d (` 0F) (` 1F)) (wk (wk γ)))` | proved | Split/Lin.agda |
| `lin-bind-rec` | `(T U) (Γ) (γ) → … → LinStruct (T ⸴ U ⸴ Γ) ((` 0F) ∥ (` 1F) ∥ wk (wk γ))` | proved | Split/Lin.agda |
| `unr-mob` | `Unr (Γ ﹫ x) → MobCx Γ (` x)` | proved | Split/Absorb.agda |
| `unr-extract` | `(γ) → Unr (Γ ﹫ x) → x ∈ₘ γ → Γ ∶ γ ≈ (` x) ∥ γ` | proved | Split/Absorb.agda |
| `unr-absorb` | `AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ γ ∥ β ≼ γ` | proved | Split/Absorb.agda |
| `unr-absorb-;` | same conclusion `Γ ∶ γ ; β ≼ γ` | proved | Split/Absorb.agda |
| `unr-absorb-;ˡ` | same conclusion `Γ ∶ β ; γ ≼ γ` | proved | Split/Absorb.agda |
| `unr-absorb-join` / `unr-absorb-joinˡ` | `Γ ∶ join a γ β ≼ γ` / `Γ ∶ join a β γ ≼ γ` | proved | Split/Absorb.agda |
| `Esc` | record wrapping `Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)` (field `getEsc`) | defined | Split/Order.agda |
| `before-fwd` | `¬Unr u → ¬Unr v → Γ ∶ α ≈′ β → before u v α → before u v β` | proved | Split/Order.agda |
| `before-bwd` | `… → Γ ∶ α ≈′ β → before u v β → before u v α ⊎ Esc Γ u v` | proved | Split/Order.agda |
| `before-≈ᵇ` | same along `≈` | proved | Split/Order.agda |
| `before-mob-≼` | `¬Unr u → ¬Unr v → Γ ∶ α ≼ β → before u v β → before u v α ⊎ Esc Γ u v` | proved | Split/Order.agda |
| `canon-disj` | `(a) (X Y) → LinStruct Γ γ → join a α β ≼ γ → dom α ⊆ X → dom β ⊆ Y → (leftovers Unr) → ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)` | proved | Split/Extract.agda |
| `canon-out` | `(a) (X Y) → join a α β ≼ γ → dom α ⊆ X → dom β ⊆ Y → AllCx Unr Γ (γ ↓ ∁ (X ∪ Y))` | proved | Split/Extract.agda |
| `canon-sep` | `(d) (X Y) → join d α β ≼ γ → dom α ⊆ X → dom β ⊆ Y → disj → Sep d Γ X Y γ` | proved | Split/Extract.agda |
| `mem⇒∈` | `(δ) → x ∈ₘ δ → dom δ ⊆ X → x ∈ X` | proved | Split/Extract.agda |
| `canon-core` | the induction on γ (delivered by agent C9, see its section below) | proved | Split/Construct.agda |
| `canon-split` | THE canonical split, see below | proved | Split.agda |
| `canon-split-ps` | ParSeq instance | proved | Split.agda |
| `canon-split-;` / `canon-split-∥` | the `;` / `∥` instances, spelled out | proved | Split.agda |
| `canon-joinParSeq` | packages the `Y = ∁ X` case as `JoinParSeq Γ γ X p/s` (A-Case) | proved | Split.agda |

### CALLING CONVENTION for the `lin-*` lemmas (important)

`LinStruct Γ γ` unfolds to `∀ x → ¬ Unr (Γ ﹫ x) → count x γ ≤ 1`, a Π-type in
which Γ sits under `lookup`.  Agda can therefore NEVER solve Γ, γ or a binder
type from a `LinStruct` argument or goal (the constraint `lookup ?Γ x = lookup Γ x`
is not invertible).  All those arguments are EXPLICIT in `Split/Lin.agda`, in the
order shown in the table.  Only `lin-≼` keeps them implicit, because its `≼`
argument pins them down.

## STATE: COMPLETE.  All eight files load with zero goals, zero unsolved metas,
no postulate, no TERMINATING, no holes:
`Split.agda`, `Split/{Base,Lin,Absorb,Order,Extract,Construct,Smoke}.agda`
(1021 lines + 143 from C9's `Construct.agda`).

`Split/Smoke.agda` is a usage example, not a proof obligation: it applies every
export in the shape the A-rules need (A-Seq, A-App at `R`, A-Pair, the binder
`LinStruct` lemmas, absorption, `↓-mono-⊆`).  Read it if an argument order is
unclear.  `Split.agda` also re-exports `count` (Confine), `_∈ₘ_` and `before`
(GroupOrder), because the `unr-absorb` premises are stated with `_∈ₘ_`.

## THE EXPORTS  (import `BorrowedCF.Completeness.Split`, it re-exports everything)

```agda
canon-split : (d : Dir) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ join d α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ

canon-split-ps    : (p/s : ParSeq) … → Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ
canon-split-;   : … → Γ ∶ α ; β ≼ γ → … → Γ ∶ (γ ↓ X) ; (γ ↓ Y) ≼ γ
canon-split-∥     : … → Γ ∶ α ∥ β ≼ γ → … → Γ ∶ (γ ↓ X) ∥ (γ ↓ Y) ≼ γ
canon-joinParSeq  : (p/s : ParSeq) (X : Subset n) → … → dom β ⊆ ∁ X → … → JoinParSeq Γ γ X p/s
```

X and Y are EXPLICIT (they occur only under `_↓_` and `_∈_`, so Agda cannot
solve them); Γ, α, β, γ are implicit and are pinned down by the `≼` argument.

HOW TO INSTANTIATE IT for the A-rules (the algorithmic side always restricts to
`fv e₂` FIRST in A-App):

* `T-AppLeft`  premise `γ₂ ; γ₁ ≼ γ`: `canon-split L (fv e₂) (fv e₁)`, giving
  `(γ ↓ fv e₂) ; (γ ↓ fv e₁) ≼ γ` = `join L (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ`.
* `T-AppRight` premise `γ₁ ; γ₂ ≼ γ`: `canon-split R (fv e₂) (fv e₁)` (α := γ₂,
  β := γ₁, and `join R α β = β ; α` definitionally).
* `T-AppUnr` / `T-AppLin` premise `γ₁ ∥ γ₂ ≼ γ`: commute with `∥-comm` first,
  then `canon-split 𝟙 (fv e₂) (fv e₁)`.
* `T-Seq` premise `γ₁ ; γ₂ ≼ γ`: `canon-split-; (fv e₁) (fv e₂)`.
* `T-Pair` / `T-Let` / `T-LetPair` premise `join p/s γ₁ γ₂ ≼ γ`:
  `canon-split-ps p/s X Y` with the two free-variable sets; for A-LetPair and
  A-Let, which demand a plain `;`, postcompose with `;-≼-join p/s`
  (`α ; β ≼ join p/s α β`) — or use `canon-split-;` directly when the
  declarative premise is already sequential.

The two `dom α ⊆ X` premises and the two "leftover is Unr" premises are what
the caller has to produce from the declarative derivation; C3/C4 own that
(`dom γᵢ ⊆ fv eᵢ ∪ {unrestricted junk}` comes from the typing of `eᵢ`).

## HELPER SPLIT  (answer to the coordinator: YES, it split cleanly — DONE, agent C9 delivered `canon-core`)

The canonical split factors into

  (a) EXTRACTION — from `Γ ∶ join d α β ≼ γ` + `LinStruct Γ γ` + the domain side
      conditions, derive the three inputs `disj`, `out`, `sep` below.  Needs a
      strengthened `before-mono-≼` (mine, `Split/Order.agda`).
  (b) CONSTRUCTION — from those three inputs, build the ≼ by induction on γ.

They share NOTHING except the three inputs, which are already type-checked
definitions in `Split/Base.agda`.  A helper agent can take (b) in
`BorrowedCF/Completeness/Split/Construct.agda` right now.

### What the helper must prove (exact statement, do not change it)

```agda
module BorrowedCF.Completeness.Split.Construct where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; _∪_; ∁)
open import Data.Fin.Subset.Properties using (_∈?_; x∈p∪q⁺; x∈p∪q⁻; x∉p⇒x∈∁p; x∈∁p⇒x∉p)
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Completeness.Split.Base

canon-core : ∀ (d : Dir) {Γ : Ctx n} {X Y : Subset n} (γ : Struct n) →
  (disj : ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)) →
  (out  : AllCx Unr Γ (γ ↓ ∁ (X ∪ Y))) →
  (sep  : Sep d Γ X Y γ) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
```

`Sep`, `SepXY`, `SepYX`, `mob-dist`, `mem-↓⁻`, `mem-allCx`, `allCx-mem`,
`sep-∥ˡ/ʳ`, `sep-;ˡ/ʳ` are all exported from `Split/Base.agda` (type-checked).
`SepXY`/`SepYX` are RECORDS (field `getXY` / `getYX`, constructor `mkSepXY` /
`mkSepYX`) so that Γ, X, Y stay inferable:

```agda
record SepXY (Γ : Ctx n) (X Y : Subset n) (γ : Struct n) : Set where
  field getXY : ∀ u v → u ∈ X → v ∈ Y → before u v γ → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
record SepYX (Γ : Ctx n) (X Y : Subset n) (γ : Struct n) : Set where
  field getYX : ∀ u v → u ∈ Y → v ∈ X → before u v γ → Mobile (Γ ﹫ u) ⊎ Mobile (Γ ﹫ v)
Sep 𝟙 Γ X Y γ = SepXY Γ X Y γ × SepYX Γ X Y γ
Sep L Γ X Y γ = SepYX Γ X Y γ
Sep R Γ X Y γ = SepXY Γ X Y γ
```

### Proof plan for (b) — worked out, no gaps known

Induction on γ.  Write `A₁ = γ₁ ↓ X`, `A₂ = γ₁ ↓ Y`, `B₁ = γ₂ ↓ X`, `B₂ = γ₂ ↓ Y`.

* `γ = []`: `join d [] [] ≈ []` by `join-[]₁ d`; `≼-refl`.
* `γ = ; z`: decide `z ∈? X` and `z ∈? Y` (`_∈?_` is decidable).
  - both: `Unr (Γ ﹫ z)` from `disj`, so `join d (; z) (; z) ≈ ; z`
    (`∥-dup` for 𝟙, `∥/;-transmute` + `∥-dup` for L/R — `unr⇒mobile`).
  - only X: `join-[]₂ d`.  Only Y: `join-[]₁ d`.
  - neither: `z ∈ ∁ (X ∪ Y)`, so `out` gives `Unr (Γ ﹫ z)`; then
    `join d [] [] ≈ [] ≼ ; z` by `≼-∅`.
* `γ = γ₁ ∥ γ₂`: `join-distr-∥ d A₁ A₂ B₁ B₂` (Context/Join.agda) gives
  `join d (A₁ ∥ B₁) (A₂ ∥ B₂) ≼ join d A₁ A₂ ∥ join d B₁ B₂`; finish with
  `≼-cong-∥ IH₁ IH₂`.  `out` splits by `allCx-∥⁻¹`, `sep` by `sep-∥ˡ/ʳ`.
* `γ = γ₁ ; γ₂`: THE case.  It suffices to prove
      `join d (A₁ ; B₁) (A₂ ; B₂) ≈ (join d A₁ A₂) ; (join d B₁ B₂)`
  and finish with `≼-cong-; IH₁ IH₂`.  Get two mobility disjunctions with
  `mob-dist` (u ∈ₘ A₁ gives u ∈ X and u ∈ₘ γ₁ by `mem-↓⁻`, so
  `before u v (γ₁ ; γ₂) = inj₁ (u∈ₘγ₁ , v∈ₘγ₂)` is available):
      H₁ : MobCx Γ A₁ ⊎ MobCx Γ B₂     (from `getXY sep`, needs d ∈ {𝟙, R})
      H₂ : MobCx Γ A₂ ⊎ MobCx Γ B₁     (from `getYX sep`, needs d ∈ {𝟙, L})
  Then
  - d = L: goal `(A₁ ; B₁) ; (A₂ ; B₂) ≈ (A₁ ; A₂) ; (B₁ ; B₂)`:
    reassociate with `;-assoc` and swap `B₁` past `A₂` with `;-commMob H₂`.
  - d = R: mirror image, `join R P Q = Q ; P`, swap `B₂` past `A₁` with
    `;-commMob H₁`.
  - d = 𝟙: goal `(A₁ ; B₁) ∥ (A₂ ; B₂) ≈ (A₁ ∥ A₂) ; (B₁ ∥ B₂)`.  Four
    cases from H₁ × H₂, two chains:
    * (MobA₁,MobA₂) and (MobB₂,MobB₁): `∥/;-transmute` backwards on both
      `;`s, `∥-comm₄`, then `∥/;-transmute` forwards using
      `MobCx (A₁ ∥ A₂)` resp. `MobCx (B₁ ∥ B₂)`.
    * (MobA₁,MobB₁) and (MobB₂,MobA₂): `∥/;-transmute` forwards on the top
      `∥` (witness `MobCx (A₁ ; B₁)` resp. `MobCx (A₂ ; B₂)`), then
      `;-assoc` + `;-commMob` to swap `B₁` past `A₂`, then transmute the two
      inner `;`s back to `∥`.
    All four are ≈, so the whole `;`-node is `≼-refl (…)` composed with
    `≼-cong-;`.

A convenient shape for the 𝟙 case (prove it first, it is context-free):

```agda
;-shuffle : ∀ {Γ : Ctx n} {A₁ A₂ B₁ B₂ : Struct n} →
  MobCx Γ A₁ ⊎ MobCx Γ B₂ → MobCx Γ A₂ ⊎ MobCx Γ B₁ →
  Γ ∶ (A₁ ; B₁) ∥ (A₂ ; B₂) ≈ (A₁ ∥ A₂) ; (B₁ ∥ B₂)
```

WHY the mobility disjunctions are unavoidable: `Γ = h : ⟨acq ; s⟩, y : ⟨…⟩`,
`γ = ; h ; ; y`, `X = ⁅y⁆`, `Y = ⁅h⁆`, `α = ; y`, `β = ; h`, `d = 𝟙`.
Then `α ∥ β ≼ γ` holds only through `∥′-tm-;` with the MOBILITY witness for `h`,
and the conclusion `(γ ↓ X) ∥ (γ ↓ Y) ≼ γ` needs that same witness.  `Mobile` is
NOT decidable, so the witness has to be threaded out of the ≼-derivation; that is
what part (a) (`before-mob-≼`) does, and `mob-dist` is the constructive
"(∀u∀v. P u ⊎ Q v) → (∀u. P u) ⊎ (∀v. Q v)" that turns the pointwise witnesses
into the two `MobCx` disjunctions.

## Notes / discrepancies found so far

* `A-Case` (Algorithmic.agda) types both branches at `γ ↓ ∁ (fv e)`.  That is
  INCOMPLETE for an unrestricted variable shared between the scrutinee and a
  branch: for `Γ = z : Int` (Unr) and `case e of ⟨ z ; z ⟩` with `z ∈ fv e`, the
  declarative `T-Case` types the branches at a `γ₂` containing `z` (duplication
  of an Unr variable is free, `∥′-dup`), while `γ ↓ ∁ (fv e)` deletes `z`, so
  `A-Var` cannot fire in the branch.  Every other two-subterm A-rule uses two
  restrictions of γ (never a complement) and is unaffected.  `canon-split` is
  stated with two independent sets X, Y and therefore does NOT cover the
  A-Case shape: `dom γ₂ ⊆ ∁ (fv e)` simply fails there.  Suggested fix for
  whoever owns Algorithmic.agda: use `γ ↓ (fvClose (fv e₁) ∪ fvClose (fv e₂))`
  for the branches instead of `γ ↓ ∁ (fv e)`.
* `join seq α β` and `join L α β` reduce to `α ; β` definitionally
  (`biasedDir seq = L`), so the `;`-shaped premises of A-Seq, A-Let and
  A-LetPair are literally `canon-split` at `d = L`.  I export an explicit
  `canon-split-;` anyway so nobody has to rely on that.

------------------------------------------------------------------------

## C9 — `Split/Construct.agda` (CONSTRUCTION half), owned by agent C9

File: `Completeness/Split/Construct.agda`.  Checked with
`agda-check BorrowedCF/Completeness/Split/Construct.agda`: exit 0, no output,
zero goals, zero unsolved metas, no postulate / TERMINATING / rewrite.
`Split/Base.agda` is the only Completeness import; nothing under `Simulation/`
is imported directly.

| lemma | statement | status |
|---|---|---|
| `;-interchange` | `(P₁ ; Q₁) ; (P₂ ; Q₂) ≈ (P₁ ; P₂) ; (Q₁ ; Q₂)` given `MobCx Γ P₂ ⊎ MobCx Γ Q₁` | proved |
| `;-shuffle` | `(A₁ ; B₁) ∥ (A₂ ; B₂) ≈ (A₁ ∥ A₂) ; (B₁ ∥ B₂)` given `MobCx A₁ ⊎ MobCx B₂` and `MobCx A₂ ⊎ MobCx B₁` | proved |
| `join-dup` | `(d) (Γ) (α) → UnrCx Γ α → Γ ∶ join d α α ≈ α` | proved |
| `mob-XY` | `SepXY Γ X Y (γ₁ ; γ₂) → MobCx Γ (γ₁ ↓ X) ⊎ MobCx Γ (γ₂ ↓ Y)` | proved |
| `mob-YX` | `SepYX Γ X Y (γ₁ ; γ₂) → MobCx Γ (γ₁ ↓ Y) ⊎ MobCx Γ (γ₂ ↓ X)` | proved |
| `canon-core` | `(d) (γ) → disj → out → Sep d Γ X Y γ → Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ` | **proved** |

`canon-core` is the EXACT statement of "HELPER SPLIT" above, unchanged, with the
module header and import list given there (`x∈p∪q⁺`, `_⊆_`, `x∈∁p⇒x∉p` end up
unused; I left them in so the header stays literally as specified).

All five auxiliaries are PUBLIC (not `private`), so C1 may reuse them; nothing in
`Split/Base.agda` was touched.

### Case breakdown of `canon-core` (all four done)

* `γ = []` — `≼-refl (join-[]₁ d)`.
* `γ = ` z` — `with z ∈? X | z ∈? Y`: both `join-dup d (` disj z _ _)`; only X
  `join-[]₂ d`; only Y `join-[]₁ d`; neither `≼-∅` on the `Unr` read out of `out`
  with `allCx-mem out (mem-↓⁺ (` z) (x∉p⇒x∈∁p …) (mem-self z))`.
* `γ = γ₁ ∥ γ₂` — `join-distr-∥ d (γ₁↓X) (γ₁↓Y) (γ₂↓X) (γ₂↓Y)` then
  `≼-cong-∥ IH₁ IH₂`; `out` splits by pattern `(o₁ ∥ o₂)`, `sep` by `sep-∥ˡ/ʳ d`.
* `γ = γ₁ ; γ₂` — split on `d`, each direction one `≼-refl` of a ≈-shuffle
  followed by `≼-cong-; IH₁ IH₂`.

### Deviations from C1's plan (three, all simplifications)

1. **`d = L` and `d = R` use `;-interchange`, not an ad-hoc chain.**  Both are the
   same lemma at different instances: `L` needs
   `;-interchange (γ₁↓X) (γ₂↓X) (γ₁↓Y) (γ₂↓Y) (mob-YX …)` and `R` needs
   `;-interchange (γ₁↓Y) (γ₂↓Y) (γ₁↓X) (γ₂↓X) (mob-XY …)`, because
   `join R α β = β ; α` reduces definitionally.  No `join-flip` and no
   `;-≼-join` were needed anywhere.

2. **`;-shuffle` has the argument order `A₁ B₁ A₂ B₂`** (row-major: the two
   factors of the first `;` first), not the `A₁ A₂ B₁ B₂` of the sketch in
   "HELPER SPLIT".  Its two hypotheses are exactly the sketch's `H₁`, `H₂`.
   Its Γ, A₁, B₁, A₂, B₂ are explicit for the same reason the `lin-*` lemmas
   are: `MobCx` hides them under `lookup`.

3. **`≼-wk` is never applied by hand.**  It only enters through
   `join-distr-∥` (Context/Join.agda), which already covers the `L`/`R` cases of
   the `∥`-node.  `∥′-dup` enters only through `∥-dup` inside `join-dup`.

Everything else follows the plan verbatim: `mob-dist` on `(γ₁ ↓ ·, γ₂ ↓ ·)` with
`before u v (γ₁ ; γ₂) = inj₁ (u∈ₘγ₁ , v∈ₘγ₂)` supplied through `mem-↓⁻`, and the
four `H₁ × H₂` cases of the `𝟙` shuffle in exactly the two chains described
(column-mobile → `∥-comm₄`; row-mobile → transmute the outer `∥` and reuse
`;-interchange`).

### No helper was missing from `Split/Base.agda`

`Base.agda` supplied `mob-dist`, `mem-↓⁻`, `mem-↓⁺`, `mem-self`, `allCx-mem`,
`Sep`/`SepXY`/`SepYX` and `sep-∥ˡ/ʳ`, `sepXY-;ˡ/ʳ`, `sepYX-;ˡ/ʳ` unchanged;
`mem-allCx`, `allCx-↓-pointwise` and `↓-mono-⊆` turned out not to be needed.
The three lemmas I added (`;-interchange`, `;-shuffle`, `join-dup`) are pure
structure algebra with no reference to `_↓_`, so they would sit equally well in
`Base.agda` if C1 wants them there — say the word and I will move them.

### Note for C1 / the extraction half

`canon-core` uses `sep` ONLY at `;`-nodes of γ, and only through
`before u v (γ₁ ; γ₂) = inj₁ (…)`, i.e. through the "u in the left factor, v in
the right factor" disjunct.  A weaker `Sep` that quantifies only over that
disjunct would still be enough for the construction; the recursive `sep-;ˡ/ʳ`
projections then have to be re-proved.  I kept the strong (recursive) `Sep`
because `Base.agda` already has the projections.
