-- | THE CANONICAL SPLIT, and the structure-algebra toolkit around it.
--
--   If SOME admissible split of γ along two variable sets exists, then the
--   RESTRICTION-based split along those sets is admissible too:
--
--     Γ ∶ join d α β ≼ γ   with dom α ⊆ X, dom β ⊆ Y and the leftovers of X, Y
--                          unrestricted, and γ linear
--     ⟹  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
--
--   That is exactly the gap between the declarative rules (which pick the two
--   structures γ₁, γ₂ out of thin air) and the algorithmic ones (which restrict
--   γ to the free variables of the two subterms).
--
--   The proof is in two halves: `Split/Extract.agda` turns the given split into
--   three syntactic facts about γ (`canon-disj`, `canon-out`, `canon-sep`, the
--   last one using `before-mob-≼` of `Split/Order.agda`), and `Split/Construct.agda`
--   rebuilds the restriction split from them by induction on γ (`canon-core`).
--
--   This module re-exports the whole toolkit; importing it is enough.
module BorrowedCF.Completeness.Split where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; _∪_; ∁)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Algorithmic using (JoinParSeq; par; seq)
open import BorrowedCF.Completeness.Base using (LinStruct)

-- The three views of "which variables occur", re-exported so that callers of
-- `unr-absorb` and friends do not have to chase them down.
open import BorrowedCF.Simulation.Support.Confine using (count) public
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder using (_∈ₘ_; before) public

open import BorrowedCF.Completeness.Split.Base      public
open import BorrowedCF.Completeness.Split.Lin       public
open import BorrowedCF.Completeness.Split.Absorb    public
open import BorrowedCF.Completeness.Split.Order     public
open import BorrowedCF.Completeness.Split.Extract   public
open import BorrowedCF.Completeness.Split.Construct public

open Nat.Variables
open Variables

------------------------------------------------------------------------
-- The canonical split.
--
-- X and Y are EXPLICIT: they occur only under `_↓_` and `_∈_`, so Agda cannot
-- solve them.  Γ, α, β and γ are implicit — the `≼` argument pins them down.

canon-split : (d : Dir) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ join d α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
canon-split d {Γ} X Y {γ = γ} lin ≤γ dα dβ uX uY =
  canon-core d γ disj (canon-out d X Y ≤γ dα dβ) (canon-sep d X Y ≤γ dα dβ disj)
  where
  disj : ∀ z → z ∈ X → z ∈ Y → Unr (Γ ﹫ z)
  disj = canon-disj d X Y lin ≤γ dα dβ uX uY

-- ParSeq instance (A-Pair, A-Case, T-Let, T-LetPair).  `join par = ∥` and
-- `join seq = ;` definitionally, so this is the same lemma at `𝟙` and `L`.
canon-split-ps : (p/s : ParSeq) {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ join p/s α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ
canon-split-ps par = canon-split 𝟙
canon-split-ps seq = canon-split L

-- The plain sequential instance, spelled out (A-Seq, A-Let, A-LetPair).
canon-split-; : {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ α ; β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  Γ ∶ (γ ↓ X) ; (γ ↓ Y) ≼ γ
canon-split-; = canon-split L

-- The parallel instance, spelled out (T-AppUnr / T-AppLin).
canon-split-∥ : {Γ : Ctx n} (X Y : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ α ∥ β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom β → Unr (Γ ﹫ z)) →
  Γ ∶ (γ ↓ X) ∥ (γ ↓ Y) ≼ γ
canon-split-∥ = canon-split 𝟙

-- A-Case wants the premise packaged as `JoinParSeq Γ γ X p/s`, i.e. with
-- Y = ∁ X.  NOTE that the side condition `dom β ⊆ ∁ X` is a real restriction:
-- see the discrepancy note in Split-STATUS.md about unrestricted variables
-- shared between the scrutinee and a branch.
canon-joinParSeq : (p/s : ParSeq) {Γ : Ctx n} (X : Subset n) {α β γ : Struct n} →
  LinStruct Γ γ →
  Γ ∶ join p/s α β ≼ γ →
  dom α ⊆ X → dom β ⊆ ∁ X →
  (∀ z → z ∈ X → z ∉ dom α → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ ∁ X → z ∉ dom β → Unr (Γ ﹫ z)) →
  JoinParSeq Γ γ X p/s
canon-joinParSeq par X lin ≤γ dα dβ uX uY = par (canon-split 𝟙 X (∁ X) lin ≤γ dα dβ uX uY)
canon-joinParSeq seq X lin ≤γ dα dβ uX uY = seq (canon-split L X (∁ X) lin ≤γ dα dβ uX uY)
