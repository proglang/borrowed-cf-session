-- | Transferring the structural premises of the declarative derivation into the
--   ALGORITHMIC context (agent C4).
--
--   `≼` sees the context only through `Unr` and `Mobile`.  `Unr` is reflected by
--   instantiation, `Mobile` is not — which is why the base now carries the
--   CONSTRAINT-GENERATING relation `Γ ∶ γ₁ ≼ γ₂ ↑ Δ₀` (C8's design, C10's edit): every
--   mobility use becomes a `C-Mob` constraint, and `≼↑-complete` turns a declarative `≼`
--   into one over the unification-variable context.  The gap parameter `mob-reflect` is
--   GONE (Main-STATUS.md, FINDING 1 is closed).
--
--   `≼→` packages `≼↑-complete` with the scope of the constraints it emits, which the
--   induction has to carry: they are all `C-Mob (Γ̂ ﹫ x)`, so `UVarsInΓ` bounds them.
--
--   Owner: agent C4.
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.SubConstraint
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Sub

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Interface

module BorrowedCF.Completeness.Main.Transfer where

open Nat.Variables

private variable
  α β : Struct n
  Γ̂ : Ctx n

------------------------------------------------------------------------
-- The constraints a `≼↑` derivation emits (C2 is adding the same lemma under the name
-- `uvarsInΔ-≼↑`; these are named `scope-*` so that both can be in scope) are mobility constraints on the variables of
-- the structure, so they live in the scope window of the context.

scope-≈′↑ : ∀ {n} {Γ̂ : Ctx n} {α β : Struct n} {Δ : CSet} {m} →
  UVarsInΓ 0 m Γ̂ → Γ̂ ∶ α ≈′ β ↑ Δ → UVarsInΔ 0 m Δ
scope-≈′↑ uΓ sq′-assoc↑ = []
scope-≈′↑ uΓ (sq′-cong₁↑ d) = scope-≈′↑ uΓ d
scope-≈′↑ uΓ (sq′-cong₂↑ d) = scope-≈′↑ uΓ d
scope-≈′↑ uΓ ∥′-unit↑ = []
scope-≈′↑ uΓ ∥′-assoc↑ = []
scope-≈′↑ uΓ ∥′-comm↑ = []
scope-≈′↑ uΓ (∥′-cong₁↑ d) = scope-≈′↑ uΓ d
scope-≈′↑ uΓ (∥′-dup↑ U) = []
scope-≈′↑ {Γ̂ = Γ̂} uΓ (∥′-tmˡ↑ {α = α}) = uvarsInΔ-allMobile Γ̂ α uΓ
scope-≈′↑ {Γ̂ = Γ̂} uΓ (∥′-tmʳ↑ {β = β}) = uvarsInΔ-allMobile Γ̂ β uΓ

scope-≈↑ : ∀ {n} {Γ̂ : Ctx n} {α β : Struct n} {Δ : CSet} {m} →
  UVarsInΓ 0 m Γ̂ → Γ̂ ∶ α ≈ β ↑ Δ → UVarsInΔ 0 m Δ
scope-≈↑ uΓ ε↑ = []
scope-≈↑ uΓ (d ◅ᶠ ds) = uvarsInΔ-++ (scope-≈′↑ uΓ d) (scope-≈↑ uΓ ds)
scope-≈↑ uΓ (d ◅ᵇ ds) = uvarsInΔ-++ (scope-≈′↑ uΓ d) (scope-≈↑ uΓ ds)

scope-≼↑ : ∀ {n} {Γ̂ : Ctx n} {α β : Struct n} {Δ : CSet} {m} →
  UVarsInΓ 0 m Γ̂ → Γ̂ ∶ α ≼ β ↑ Δ → UVarsInΔ 0 m Δ
scope-≼↑ uΓ (≼-refl↑ d) = scope-≈↑ uΓ d
scope-≼↑ uΓ (≼-∅↑ U) = []
scope-≼↑ uΓ ≼-wk↑ = []
scope-≼↑ uΓ (≼-trans↑ d e) = uvarsInΔ-++ (scope-≼↑ uΓ d) (scope-≼↑ uΓ e)
scope-≼↑ uΓ (≼-cong-sq↑ d e) = uvarsInΔ-++ (scope-≼↑ uΓ d) (scope-≼↑ uΓ e)
scope-≼↑ uΓ (≼-cong-par↑ d e) = uvarsInΔ-++ (scope-≼↑ uΓ d) (scope-≼↑ uΓ e)

------------------------------------------------------------------------
-- The transfer used by every case with a structural premise.

record Lift≼ {n : ℕ} (Γ̂ : Ctx n) (α β : Struct n) (m : ℕ) (σ₀ : UV.Sub) : Set where
  constructor lift≼
  field
    {cs}  : CSet
    der   : Γ̂ ∶ α ≼ β ↑ cs
    sol   : SolvedΔ cs σ₀
    csc   : UVarsInΔ 0 m cs

open Lift≼ public

≼→ : ∀ {n} {Γ Γ̂ : Ctx n} {α β : Struct n} {m : ℕ} {σ₀ : UV.Sub} →
  Solving σ₀ → Approx Γ̂ Γ σ₀ → UVarsInΓ 0 m Γ̂ →
  Γ ∶ α ≼ β → Lift≼ Γ̂ α β m σ₀
≼→ Sσ ap uΓ ≤γ =
  let Δ₀ , d , SΔ₀ = ≼↑-complete Sσ ap ≤γ in
  lift≼ d SΔ₀ (scope-≼↑ uΓ d)

------------------------------------------------------------------------
-- `Unr` transfers unconditionally (no session type is unrestricted).

unr→ : ∀ {n} {Γ Γ̂ : Ctx n} {σ₀ : UV.Sub} →
  Approx Γ̂ Γ σ₀ → ∀ x → Unr (Γ ﹫ x) → Unr (Γ̂ ﹫ x)
unr→ ap x = unr-approx (ap x)

unrCx→ : ∀ {n} {Γ Γ̂ : Ctx n} {α : Struct n} {σ₀ : UV.Sub} →
  Approx Γ̂ Γ σ₀ → UnrCx Γ α → UnrCx Γ̂ α
unrCx→ {Γ = Γ} {Γ̂ = Γ̂} ap U = allCx-ctx {Γ₁ = Γ} {Γ₂ = Γ̂} (unr→ {Γ = Γ} {Γ̂ = Γ̂} ap) U
