module BorrowedCF.Completeness.Split.Smoke where

open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; ∁)
open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution using (wk)
open import BorrowedCF.Completeness.Base using (LinStruct)
open import BorrowedCF.Completeness.Split

open Nat.Variables
open Variables
open Fin.Patterns

-- A-Seq shape.
smoke-; : {Γ : Ctx n} {γ γ₁ γ₂ : Struct n} (X Y : Subset n) →
  LinStruct Γ γ → Γ ∶ γ₁ ; γ₂ ≼ γ → dom γ₁ ⊆ X → dom γ₂ ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom γ₁ → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom γ₂ → Unr (Γ ﹫ z)) →
  Γ ∶ (γ ↓ X) ; (γ ↓ Y) ≼ γ
smoke-; X Y lin ≤γ a b c e = canon-split-; X Y lin ≤γ a b c e

-- A-App shape (dir R: the declarative premise is `γ₁ ; γ₂`, the algorithmic
-- conclusion `join R (γ ∣fv[e₂]) (γ ∣fv[e₁])`).
smoke-appR : {Γ : Ctx n} {γ γ₁ γ₂ : Struct n} (X Y : Subset n) →
  LinStruct Γ γ → Γ ∶ γ₁ ; γ₂ ≼ γ → dom γ₂ ⊆ X → dom γ₁ ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom γ₂ → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom γ₁ → Unr (Γ ﹫ z)) →
  Γ ∶ join R (γ ↓ X) (γ ↓ Y) ≼ γ
smoke-appR X Y lin ≤γ a b c e = canon-split R X Y lin ≤γ a b c e

-- A-Pair shape.
smoke-ps : (p/s : ParSeq) {Γ : Ctx n} {γ γ₁ γ₂ : Struct n} (X Y : Subset n) →
  LinStruct Γ γ → Γ ∶ join p/s γ₁ γ₂ ≼ γ → dom γ₁ ⊆ X → dom γ₂ ⊆ Y →
  (∀ z → z ∈ X → z ∉ dom γ₁ → Unr (Γ ﹫ z)) →
  (∀ z → z ∈ Y → z ∉ dom γ₂ → Unr (Γ ﹫ z)) →
  Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ
smoke-ps p/s X Y lin ≤γ a b c e = canon-split-ps p/s X Y lin ≤γ a b c e

-- LinStruct under a binder, and back down a join.
smoke-lin : (d : Dir) {Γ : Ctx n} {γ : Struct n} {T : 𝕋} →
  LinStruct Γ γ → LinStruct (T ⸴ Γ) (join d (` 0F) (wk γ))
smoke-lin d {Γ} {γ} {T} lin = lin-bind d T Γ γ lin

smoke-lin⁻ : {Γ : Ctx n} {α β : Struct n} → LinStruct Γ (α ; β) → LinStruct Γ α
smoke-lin⁻ {Γ = Γ} {α} {β} lin = proj₁ (lin-;⁻ Γ α β lin)

smoke-lin↓ : {Γ : Ctx n} {γ : Struct n} {X : Subset n} → LinStruct Γ γ → LinStruct Γ (γ ↓ X)
smoke-lin↓ {Γ = Γ} {γ} {X} lin = lin-↓ Γ γ X lin

-- Absorption and restriction monotonicity.
smoke-absorb : {Γ : Ctx n} {γ β : Struct n} →
  UnrCx Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ γ ; β ≼ γ
smoke-absorb U mem = unr-absorb-; U mem

smoke-mono : {Γ : Ctx n} (γ : Struct n) {X Y : Subset n} → X ⊆ Y →
  (∀ z → z ∈ Y → z ∉ X → Unr (Γ ﹫ z)) → Γ ∶ γ ↓ X ≼ γ ↓ Y
smoke-mono γ X⊆Y u = ↓-mono-⊆ γ X⊆Y u
