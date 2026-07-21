-- | Structural invariants of untyped ≋.
--
--   The uniqueness half of the normal-form theory (Normal.Complete, still open)
--   is proved by exhibiting quantities that every ≋′ generator preserves and
--   that a normal form determines.  This module establishes the technique and
--   the two simplest such quantities: the number of ν binders and the number of
--   φ cells.  Both are invariant because
--     • the ∥ generators only re-associate / commute / drop a `unit` thread,
--       which carries no binders;
--     • the four binder-permuting generators rename the body, and the counts
--       are renaming-invariant (νcount-⋯ₚ / φcount-⋯ₚ);
--     • the two extrusion generators move a binder ACROSS a ∥ without creating
--       or destroying one.
--
--   Corollary (≋-νcount / ≋-φcount): a process ≋-equal to a translation image
--   has exactly the image's binder counts — the first genuine constraint the
--   reverse simulation can put on the ≋-escaped R of `Base`.
module BorrowedCF.Simulation.Support.Normal.Invariant where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- The two counts.
------------------------------------------------------------------------

νcount : ∀ {n} → Proc n → ℕ
νcount ⟪ _ ⟫   = 0
νcount (P ∥ Q) = νcount P + νcount Q
νcount (ν P)   = suc (νcount P)
νcount (φ _ P) = νcount P

φcount : ∀ {n} → Proc n → ℕ
φcount ⟪ _ ⟫   = 0
φcount (P ∥ Q) = φcount P + φcount Q
φcount (ν P)   = φcount P
φcount (φ _ P) = suc (φcount P)

νcount-⋯ₚ : ∀ {n m} (P : Proc n) (ρ : n →ᵣ m) → νcount (P ⋯ₚ ρ) ≡ νcount P
νcount-⋯ₚ ⟪ _ ⟫   ρ = refl
νcount-⋯ₚ (P ∥ Q) ρ = cong₂ _+_ (νcount-⋯ₚ P ρ) (νcount-⋯ₚ Q ρ)
νcount-⋯ₚ (ν P)   ρ = cong suc (νcount-⋯ₚ P (ρ ↑* 2))
νcount-⋯ₚ (φ _ P) ρ = νcount-⋯ₚ P (ρ ↑)

φcount-⋯ₚ : ∀ {n m} (P : Proc n) (ρ : n →ᵣ m) → φcount (P ⋯ₚ ρ) ≡ φcount P
φcount-⋯ₚ ⟪ _ ⟫   ρ = refl
φcount-⋯ₚ (P ∥ Q) ρ = cong₂ _+_ (φcount-⋯ₚ P ρ) (φcount-⋯ₚ Q ρ)
φcount-⋯ₚ (ν P)   ρ = φcount-⋯ₚ P (ρ ↑* 2)
φcount-⋯ₚ (φ _ P) ρ = cong suc (φcount-⋯ₚ P (ρ ↑))

------------------------------------------------------------------------
-- Every generator preserves them.
------------------------------------------------------------------------

≋′-νcount : ∀ {n} {P Q : Proc n} → P ≋′ Q → νcount P ≡ νcount Q
≋′-νcount (∥-comm′ {P = P} {Q}) = Nat.+-comm (νcount P) (νcount Q)
≋′-νcount (∥-assoc′ {P₁ = P₁} {P₂} {P₃}) = sym (Nat.+-assoc (νcount P₁) (νcount P₂) (νcount P₃))
≋′-νcount ∥-unit′ = refl
≋′-νcount (ν-swap′ {P = P}) = cong suc (sym (νcount-⋯ₚ P _))
≋′-νcount (ν-comm′ {P = P}) = cong (λ z → suc (suc z)) (sym (νcount-⋯ₚ P _))
≋′-νcount (φ-comm′ {P = P}) = sym (νcount-⋯ₚ P _)
≋′-νcount (νφ-comm′ {P = P}) = cong suc (sym (νcount-⋯ₚ P _))
≋′-νcount (ν-ext′ {P = P} {Q}) =
  Nat.+-suc (νcount P) (νcount Q) ■ cong (λ z → suc (z + νcount Q)) (sym (νcount-⋯ₚ P _))
≋′-νcount (φ-ext′ {P = P} {Q}) = cong (_+ νcount Q) (sym (νcount-⋯ₚ P _))
≋′-νcount (∥-cong′ g) = cong (_+ _) (≋′-νcount g)
≋′-νcount (ν-cong′ g) = cong suc (≋′-νcount g)
≋′-νcount (φ-cong′ g) = ≋′-νcount g

≋′-φcount : ∀ {n} {P Q : Proc n} → P ≋′ Q → φcount P ≡ φcount Q
≋′-φcount (∥-comm′ {P = P} {Q}) = Nat.+-comm (φcount P) (φcount Q)
≋′-φcount (∥-assoc′ {P₁ = P₁} {P₂} {P₃}) = sym (Nat.+-assoc (φcount P₁) (φcount P₂) (φcount P₃))
≋′-φcount ∥-unit′ = refl
≋′-φcount (ν-swap′ {P = P}) = sym (φcount-⋯ₚ P _)
≋′-φcount (ν-comm′ {P = P}) = sym (φcount-⋯ₚ P _)
≋′-φcount (φ-comm′ {P = P}) = cong (λ z → suc (suc z)) (sym (φcount-⋯ₚ P _))
≋′-φcount (νφ-comm′ {P = P}) = cong suc (sym (φcount-⋯ₚ P _))
≋′-φcount (ν-ext′ {P = P} {Q}) = cong (_+ φcount Q) (sym (φcount-⋯ₚ P _))
≋′-φcount (φ-ext′ {P = P} {Q}) =
  Nat.+-suc (φcount P) (φcount Q) ■ cong (λ z → suc (z + φcount Q)) (sym (φcount-⋯ₚ P _))
≋′-φcount (∥-cong′ g) = cong (_+ _) (≋′-φcount g)
≋′-φcount (ν-cong′ g) = ≋′-φcount g
≋′-φcount (φ-cong′ g) = cong suc (≋′-φcount g)

------------------------------------------------------------------------
-- Lifted to the equivalence closure.
------------------------------------------------------------------------

≋-νcount : ∀ {n} {P Q : Proc n} → P ≋ Q → νcount P ≡ νcount Q
≋-νcount ε           = refl
≋-νcount (fwd g ◅ c) = ≋′-νcount g ■ ≋-νcount c
≋-νcount (bwd g ◅ c) = sym (≋′-νcount g) ■ ≋-νcount c

≋-φcount : ∀ {n} {P Q : Proc n} → P ≋ Q → φcount P ≡ φcount Q
≋-φcount ε           = refl
≋-φcount (fwd g ◅ c) = ≋′-φcount g ■ ≋-φcount c
≋-φcount (bwd g ◅ c) = sym (≋′-φcount g) ■ ≋-φcount c
