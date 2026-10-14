-- | The workhorse of every binary case: turn a declarative split into the CANONICAL one the
--   algorithmic rules demand (agent C4).
--
--   A declarative rule splits the structure into `α` and `β` with `join d α β ≼ γ`; the
--   algorithmic rule insists on `join d (γ ↓ X) (γ ↓ Y)` with X, Y the (closed) free variables
--   of the two subterms.  `binary-split` produces both the `≤γ` premise and the two `≼` facts
--   that move the declarative premises to `γ ↓ X` and `γ ↓ Y`.
--
--   Owner: agent C4.
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _⊆_; ∁)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Split
open import BorrowedCF.Completeness.Decl

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Interface

module BorrowedCF.Completeness.Main.Bin where

open Nat.Variables

private variable
  e e₁ e₂ : Tm n

------------------------------------------------------------------------
-- Agreement of substitutions: composition and narrowing of the window.
-- (C2 exports `agree-sym` and `agree-empty`; these two are the rest.)

agree-trans : ∀ {m k} {σ₁ σ₂ σ₃ : UV.Sub} →
  Agree m k σ₁ σ₂ → Agree m k σ₂ σ₃ → Agree m k σ₁ σ₃
agree-trans p q = agree λ α lo hi → ap≡ p α lo hi ■ ap≡ q α lo hi

agree-narrow : ∀ {m k k′} {σ₁ σ₂ : UV.Sub} →
  k Nat.≤ k′ → Agree m k′ σ₁ σ₂ → Agree m k σ₁ σ₂
agree-narrow le p = agree λ α lo hi → ap≡ p α lo (Nat.<-≤-trans hi le)

-- the context approximation survives moving to a substitution that agrees below the
-- entry counter (the right premise of a binary node runs under the left premise's σ)
approx-agree : ∀ {n} {Γ Γ̂ : Ctx n} {m : ℕ} {σ₁ σ₀ : UV.Sub} →
  UVarsInΓ 0 m Γ̂ → Agree 0 m σ₁ σ₀ → Approx Γ̂ Γ σ₀ → Approx Γ̂ Γ σ₁
approx-agree uΓ ag ap x = ≃-trans (≃-reflexive (subTy-agree ag (lookupΓ uΓ x))) (ap x)

------------------------------------------------------------------------
-- The canonical restriction of a declarative split.

module _ {n : ℕ} {Γ : Ctx n} {γ α β : Struct n} (d : Dir) (X Y : Subset n)
  (lin : LinStruct Γ γ) (≤γ : Γ ∶ join d α β ≼ γ)
  (covα : AllCx Unr Γ (α ↓ ∁ X)) (covβ : AllCx Unr Γ (β ↓ ∁ Y))
  (X⊆α : X ⊆ dom α) (Y⊆β : Y ⊆ dom β)
  where

  private
    ≼α : Γ ∶ α ↓ X ≼ α
    ≼α = ↓-strip≼ α covα

    ≼β : Γ ∶ β ↓ Y ≼ β
    ≼β = ↓-strip≼ β covβ

    split′ : Γ ∶ join d (α ↓ X) (β ↓ Y) ≼ γ
    split′ = ≼-trans (≼-join d ≼α ≼β) ≤γ

    -- a variable on both sides of a split of a LINEAR structure is unrestricted
    shared : ∀ z → z ∈ dom α → z ∈ dom β → Unr (Γ ﹫ z)
    shared = shared-unr d lin ≤γ

  -- the `≤γ` premise of the algorithmic rule
  canon : Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ
  canon = canon-split d X Y lin split′ (↓-dom α X) (↓-dom β Y)
            (λ z z∈X z∉ → ⊥-elim (z∉ (dom-↓⁺ α (X⊆α z∈X) z∈X)))
            (λ z z∈Y z∉ → ⊥-elim (z∉ (dom-↓⁺ β (Y⊆β z∈Y) z∈Y)))

  -- the two premises move from the declarative components to the canonical ones
  ≼-left : Γ ∶ α ↓ X ≼ γ ↓ X
  ≼-left =
    ≼-trans (absorbʳ d unrβX)
            (subst (λ z → Γ ∶ z ≼ γ ↓ X)
                   (join-↓ d (α ↓ X) (β ↓ Y) ■ cong (λ w → join d w ((β ↓ Y) ↓ X))
                                                    (↓-idempotent α X))
                   (↓-mono-≼ split′))
    where
      unrβX : UnrCx Γ ((β ↓ Y) ↓ X)
      unrβX = allCx-of-dom ((β ↓ Y) ↓ X) λ z z∈ →
        shared z (X⊆α (↓-dom (β ↓ Y) X z∈))
                 (↓-dom⊆dom β (↓-dom⊆dom (β ↓ Y) z∈))

  ≼-right : Γ ∶ β ↓ Y ≼ γ ↓ Y
  ≼-right =
    ≼-trans (absorbˡ d unrαY)
            (subst (λ z → Γ ∶ z ≼ γ ↓ Y)
                   (join-↓ d (α ↓ X) (β ↓ Y) ■ cong (join d ((α ↓ X) ↓ Y))
                                                    (↓-idempotent β Y))
                   (↓-mono-≼ split′))
    where
      unrαY : UnrCx Γ ((α ↓ X) ↓ Y)
      unrαY = allCx-of-dom ((α ↓ X) ↓ Y) λ z z∈ →
        shared z (↓-dom⊆dom α (↓-dom⊆dom (α ↓ X) z∈))
                 (Y⊆β (↓-dom (α ↓ X) Y z∈))

------------------------------------------------------------------------
-- The instance for two subterms of the same term: X = fv e₁, Y = fv e₂.

module _ {n : ℕ} {Γ : Ctx n} {γ α β : Struct n} {e₁ e₂ : Tm n} {T U : 𝕋} {ϵ₁ ϵ₂ : Eff}
  (d : Dir) (lin : LinStruct Γ γ) (≤γ : Γ ∶ join d α β ≼ γ)
  (d₁ : Γ ; α ⊢ e₁ ∶ T ∣ ϵ₁) (d₂ : Γ ; β ⊢ e₂ ∶ U ∣ ϵ₂)
  where

  split-left : Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ∶ T ∣ ϵ₁
  split-left =
    T-Weaken (≼-left d (fv e₁) (fv e₂) lin ≤γ (fv-cover d₁) (fv-cover d₂)
                     (fv⊆dom d₁) (fv⊆dom d₂))
             (restrict d₁)

  split-right : Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ∶ U ∣ ϵ₂
  split-right =
    T-Weaken (≼-right d (fv e₁) (fv e₂) lin ≤γ (fv-cover d₁) (fv-cover d₂)
                      (fv⊆dom d₁) (fv⊆dom d₂))
             (restrict d₂)

  split-≤γ : Γ ∶ join d (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ
  split-≤γ = canon d (fv e₁) (fv e₂) lin ≤γ (fv-cover d₁) (fv-cover d₂)
                   (fv⊆dom d₁) (fv⊆dom d₂)
