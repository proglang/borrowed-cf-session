-- | Unification-variable scope bookkeeping, part 2: combining substitutions.
--
--   `merge k σ₁ σ₂` uses σ₁ on the variables below k and σ₂ on the variables from
--   k on.  Both polarities are treated consistently, so the `ap-dual/dual` law of
--   `UV.Sub` is inherited from σ₁ and σ₂ (the twin `UV.dual α` has the same index,
--   hence lands in the same half).
--
--   `single α s ¬Ss` is the substitution used for A-LSplit / A-RSplit: it maps α to
--   s and the dual-polarity twin to `dual s`.  It is `UV.subAll` in disguise.
module BorrowedCF.Completeness.Scope.Merge where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Algorithmic using (subAll-solving)
open import BorrowedCF.Completeness.Scope.Base

open Nat.Variables

------------------------------------------------------------------------
-- Splitting a substitution at an index

-- Implementation detail: a `with` on the comparison would not reduce inside the
-- record fields, so the branch is taken by an explicitly applied helper.
choose : ∀ {a} {A : Set a} {P : Set} → Dec P → A → A → A
choose (yes _) x y = x
choose (no _) x y = y

mergeAp : ℕ → UV.Sub → UV.Sub → UVar → 𝕊 0
mergeAp k σ₁ σ₂ α = choose (UV.var α Nat.<? k) (UV.ap σ₁ α) (UV.ap σ₂ α)

merge : ℕ → UV.Sub → UV.Sub → UV.Sub
merge k σ₁ σ₂ = record
  { ap = mergeAp k σ₁ σ₂
  ; ap-¬skips = ¬sk
  ; ap-dual/dual = dd
  }
  where
    ¬sk : ∀ α → ¬ Skips (mergeAp k σ₁ σ₂ α)
    ¬sk α = go (UV.var α Nat.<? k)
      where
        go : (D : Dec (UV.var α Nat.< k)) → ¬ Skips (choose D (UV.ap σ₁ α) (UV.ap σ₂ α))
        go (yes _) = UV.ap-¬skips σ₁ α
        go (no _)  = UV.ap-¬skips σ₂ α

    dd : ∀ α → dual (mergeAp k σ₁ σ₂ α) ≡ mergeAp k σ₁ σ₂ (UV.dual α)
    dd α = go (UV.var α Nat.<? k)
      where
        go : (D : Dec (UV.var α Nat.< k)) →
             dual (choose D (UV.ap σ₁ α) (UV.ap σ₂ α)) ≡
             choose D (UV.ap σ₁ (UV.dual α)) (UV.ap σ₂ (UV.dual α))
        go (yes _) = UV.ap-dual/dual σ₁ α
        go (no _)  = UV.ap-dual/dual σ₂ α

merge-below : ∀ k (σ₁ σ₂ : UV.Sub) α → UV.var α Nat.< k →
  UV.ap (merge k σ₁ σ₂) α ≡ UV.ap σ₁ α
merge-below k σ₁ σ₂ α lt = go (UV.var α Nat.<? k)
  where
    go : (D : Dec (UV.var α Nat.< k)) → choose D (UV.ap σ₁ α) (UV.ap σ₂ α) ≡ UV.ap σ₁ α
    go (yes _) = refl
    go (no ¬p) = contradiction lt ¬p

merge-above : ∀ k (σ₁ σ₂ : UV.Sub) α → k Nat.≤ UV.var α →
  UV.ap (merge k σ₁ σ₂) α ≡ UV.ap σ₂ α
merge-above k σ₁ σ₂ α ge = go (UV.var α Nat.<? k)
  where
    go : (D : Dec (UV.var α Nat.< k)) → choose D (UV.ap σ₁ α) (UV.ap σ₂ α) ≡ UV.ap σ₂ α
    go (yes p) = contradiction p (Nat.≤⇒≯ ge)
    go (no _)  = refl

merge-solving : ∀ k (σ₁ σ₂ : UV.Sub) → Solving σ₁ → Solving σ₂ → Solving (merge k σ₁ σ₂)
merge-solving k σ₁ σ₂ S₁ S₂ α = go (UV.var α Nat.<? k)
  where
    go : (D : Dec (UV.var α Nat.< k)) → SolvedTy (choose D (UV.ap σ₁ α) (UV.ap σ₂ α))
    go (yes _) = S₁ α
    go (no _)  = S₂ α

merge-agree-below : ∀ k (σ₁ σ₂ : UV.Sub) → Agree m k σ₁ (merge k σ₁ σ₂)
merge-agree-below k σ₁ σ₂ = agree λ α lo hi → sym (merge-below k σ₁ σ₂ α hi)

merge-agree-above : ∀ k (σ₁ σ₂ : UV.Sub) → Agree k n σ₂ (merge k σ₁ σ₂)
merge-agree-above k σ₁ σ₂ = agree λ α lo hi → sym (merge-above k σ₁ σ₂ α lo)

------------------------------------------------------------------------
-- Solved constraint sets, combined

solvedΔ-∷ : ∀ {C} → SolvedCst C σ → SolvedΔ Δ σ → SolvedΔ (C ∷ Δ) σ
solvedΔ-∷ = _∷_

solvedΔ-++ : SolvedΔ Δ₁ σ → SolvedΔ Δ₂ σ → SolvedΔ (Δ₁ ++ Δ₂) σ
solvedΔ-++ [] q = q
solvedΔ-++ (p ∷ ps) q = p ∷ solvedΔ-++ ps q

-- Δ₁ lives in [m, k), Δ₂ in [k, n): one substitution solves both halves.
solvedΔ-merge : ∀ k (σ₁ σ₂ : UV.Sub) →
  UVarsInΔ m k Δ₁ → UVarsInΔ k n Δ₂ → SolvedΔ Δ₁ σ₁ → SolvedΔ Δ₂ σ₂ →
  SolvedΔ (Δ₁ ++ Δ₂) (merge k σ₁ σ₂)
solvedΔ-merge k σ₁ σ₂ u₁ u₂ s₁ s₂ =
  solvedΔ-++ (solvedΔ-agree (merge-agree-below k σ₁ σ₂) u₁ s₁)
             (solvedΔ-agree (merge-agree-above k σ₁ σ₂) u₂ s₂)

-- Three-way version (A-Case: Δ ++ Δ₁ ++ Δ₂ with split points k₁ ≤ k₂ ≤ n).
merge₃ : ℕ → ℕ → UV.Sub → UV.Sub → UV.Sub → UV.Sub
merge₃ k₁ k₂ σ σ₁ σ₂ = merge k₁ σ (merge k₂ σ₁ σ₂)

solvedΔ-merge₃ : ∀ k₁ k₂ (σ σ₁ σ₂ : UV.Sub) → k₁ Nat.≤ k₂ → k₂ Nat.≤ n →
  UVarsInΔ m k₁ Δ → UVarsInΔ k₁ k₂ Δ₁ → UVarsInΔ k₂ n Δ₂ →
  SolvedΔ Δ σ → SolvedΔ Δ₁ σ₁ → SolvedΔ Δ₂ σ₂ →
  SolvedΔ (Δ ++ Δ₁ ++ Δ₂) (merge₃ k₁ k₂ σ σ₁ σ₂)
solvedΔ-merge₃ k₁ k₂ σ σ₁ σ₂ k₁≤k₂ k₂≤n u u₁ u₂ s s₁ s₂ =
  solvedΔ-merge k₁ σ (merge k₂ σ₁ σ₂) u
    (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl k₂≤n u₁) (uvarsInΔ-mono k₁≤k₂ Nat.≤-refl u₂))
    s (solvedΔ-merge k₂ σ₁ σ₂ u₁ u₂ s₁ s₂)

------------------------------------------------------------------------
-- Singleton substitutions (A-LSplit / A-RSplit)

solved-dual/id : ∀ (α : UVar) {s : 𝕊 0} → SolvedTy s → SolvedTy (UV.dual/id α s)
solved-dual/id (uvar ‼ v) Ss = Ss
solved-dual/id (uvar ⁇ v) Ss = solved-dual Ss

single : (α : UVar) (s : 𝕊 0) → ¬ Skips s → UV.Sub
single α s ¬Ss = UV.subAll {s = UV.dual/id α s} (¬Ss ∘ UV.skips-dual/id⁻ α)

single-ap : ∀ (α : UVar) (s : 𝕊 0) (¬Ss : ¬ Skips s) → UV.ap (single α s ¬Ss) α ≡ s
single-ap (uvar ‼ v) s ¬Ss = refl
single-ap (uvar ⁇ v) s ¬Ss = dual-involutive s

single-ap-dual : ∀ (α : UVar) (s : 𝕊 0) (¬Ss : ¬ Skips s) →
  UV.ap (single α s ¬Ss) (UV.dual α) ≡ dual s
single-ap-dual (uvar ‼ v) s ¬Ss = refl
single-ap-dual (uvar ⁇ v) s ¬Ss = refl

single-solving : ∀ (α : UVar) (s : 𝕊 0) (¬Ss : ¬ Skips s) →
  SolvedTy s → Solving (single α s ¬Ss)
single-solving α s ¬Ss Ss = subAll-solving (¬Ss ∘ UV.skips-dual/id⁻ α) (solved-dual/id α Ss)
