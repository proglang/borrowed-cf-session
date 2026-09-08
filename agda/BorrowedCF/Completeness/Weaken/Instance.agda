-- | Instantiation of `BorrowedCF.Completeness.Weaken.Weakening`.
--
--   Fully instantiated: the `lin-*` parameters and the two canonical-split lemmas
--   are all agent C1's (`Completeness/Split.agda`).  `alg-weaken` is exported here
--   with NO remaining module parameters and no assumptions; import this module.
--
--   `WithSplit` is kept as the split-agnostic view of the same proof.
module BorrowedCF.Completeness.Weaken.Instance where

open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Weaken
-- reused from agent C1 (Completeness/Split.agda), see Split-STATUS.md
open import BorrowedCF.Completeness.Split.Lin
  using (lin-↓; lin-bind; lin-bind₂; lin-bind-rec)
import BorrowedCF.Completeness.Split as Split

open Nat.Variables

import BorrowedCF.Context.Substitution as 𝐂

------------------------------------------------------------------------
-- `LinBox` adapters for C1's `lin-*` lemmas.  C1 states them with Γ, γ and the
-- binder types EXPLICIT (LinStruct is a Π-type, so they are never inferable);
-- boxing them makes the type former injective again, which is what `Weakening`
-- needs at its recursive calls.
------------------------------------------------------------------------

box-↓ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {X : Subset n} → LinBox Γ γ → LinBox Γ (γ ↓ X)
box-↓ {Γ = Γ} {γ} {X} l = box (lin-↓ Γ γ X (unbox l))

box-bind : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T} (d : Dir) →
  LinBox Γ γ → LinBox (T ⸴ Γ) (join d (` zero) (𝐂.wk γ))
box-bind {Γ = Γ} {γ} {T} d l = box (lin-bind d T Γ γ (unbox l))

box-bind-ps : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T} (p/s : ParSeq) →
  LinBox Γ γ → LinBox (T ⸴ Γ) (join p/s (` zero) (𝐂.wk γ))
box-bind-ps {Γ = Γ} {γ} {T} p/s l = box (lin-bind p/s T Γ γ (unbox l))

box-bind₂ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T₁ T₂} (p/s : ParSeq) (d : Dir) →
  LinBox Γ γ →
  LinBox (T₁ ⸴ T₂ ⸴ Γ) (join p/s (join d (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ)))
box-bind₂ {Γ = Γ} {γ} {T₁} {T₂} p/s d l = box (lin-bind₂ p/s d T₁ T₂ Γ γ (unbox l))

box-bind-rec : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T₁ T₂} →
  LinBox Γ γ →
  LinBox (T₁ ⸴ T₂ ⸴ Γ) ((` zero) ∥ (` suc zero) ∥ 𝐂.wk (𝐂.wk γ))
box-bind-rec {Γ = Γ} {γ} {T₁} {T₂} l = box (lin-bind-rec T₁ T₂ Γ γ (unbox l))


module WithSplit
  (canon-split :
     ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (d : Dir) →
     LinStruct Γ γ →
     Γ ∶ join d α β ≼ γ →
     dom α ⊆ X → dom β ⊆ Y →
     (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
     (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
     Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ)
  (canon-split-ps :
     ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (p/s : ParSeq) →
     LinStruct Γ γ →
     Γ ∶ join p/s α β ≼ γ →
     dom α ⊆ X → dom β ⊆ Y →
     (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
     (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
     Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ)
  where

  open Weakening canon-split canon-split-ps
                 box-↓ box-bind box-bind-ps box-bind₂ box-bind-rec
    public

------------------------------------------------------------------------
-- C1 states X and Y explicitly (they occur only under `_↓_` and `_∈_`);
-- `Weakening` wants them implicit.  These two wrappers are the whole adaptation.
------------------------------------------------------------------------

c-split : ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (d : Dir) →
  LinStruct Γ γ →
  Γ ∶ join d α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
  (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
  Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
c-split {X = X} {Y = Y} d = Split.canon-split d X Y

c-split-ps : ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (p/s : ParSeq) →
  LinStruct Γ γ →
  Γ ∶ join p/s α β ≼ γ →
  dom α ⊆ X → dom β ⊆ Y →
  (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
  (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
  Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ
c-split-ps {X = X} {Y = Y} p/s = Split.canon-split-ps p/s X Y

------------------------------------------------------------------------
-- The finished theorem.  `alg-weaken` below has no module parameters left.
------------------------------------------------------------------------

open WithSplit c-split c-split-ps public
