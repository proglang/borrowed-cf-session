module BorrowedCF.Algorithmic.SoundSplit where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (_∈?_; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; ∉⊥; x∈p∪q⁻; x∈p∪q⁺)
import Data.Sum as Sum
open import Relation.Nullary using (yes; no)

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.DescendAbs using (↓-join)
open import BorrowedCF.Algorithmic.Split
open import BorrowedCF.Algorithmic.LinUnique
open import BorrowedCF.Algorithmic.SplitLemmas

open Nat.Variables

∈dom↓ : {n : ℕ} (γ : Struct n) {X : Subset n} {y : 𝔽 n} → y ∈ dom γ → y ∈ X → y ∈ dom (γ ↓ X)
∈dom↓ (` z) {X} {y} y∈ y∈X with x∈⁅y⁆⇒x≡y z y∈
... | refl with z ∈? X
...   | yes _  = x∈⁅x⁆ z
...   | no z∉  = ⊥-elim (z∉ y∈X)
∈dom↓ [] y∈ y∈X = ⊥-elim (∉⊥ y∈)
∈dom↓ (α ∥ β) {X} y∈ y∈X with x∈p∪q⁻ (dom α) (dom β) y∈
... | Sum.inj₁ y∈α = x∈p∪q⁺ (Sum.inj₁ (∈dom↓ α y∈α y∈X))
... | Sum.inj₂ y∈β = x∈p∪q⁺ (Sum.inj₂ (∈dom↓ β y∈β y∈X))
∈dom↓ (α ; β) {X} y∈ y∈X with x∈p∪q⁻ (dom α) (dom β) y∈
... | Sum.inj₁ y∈α = x∈p∪q⁺ (Sum.inj₁ (∈dom↓ α y∈α y∈X))
... | Sum.inj₂ y∈β = x∈p∪q⁺ (Sum.inj₂ (∈dom↓ β y∈β y∈X))

-- The SOUND core split fact: under LinUnique, the combined context restricted to
-- a subterm's free variables is a subcontext of that subterm's own context.
↓fv-≼-wf : {n : ℕ} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} (a : Dir) →
           LinUnique Γ (join a γ₁ γ₂) → (d : Γ ; γ₁ ⊢ e ∶ T ∣ ϵ) →
           Γ ∶ (join a γ₁ γ₂) ↓ fv e ≼ γ₁
↓fv-≼-wf {γ₁ = γ₁} {γ₂} {e} a lu d =
  subst (λ z → _ ∶ z ≼ γ₁) (sym (↓-join a γ₁ γ₂ (fv e)))
    (≼-trans (join-absorb a (γ₂ ↓ fv e) (sibling-Unr a lu d) dom⊆) (own-≼ d))
  where dom⊆ : dom (γ₂ ↓ fv e) ⊆ dom (γ₁ ↓ fv e)
        dom⊆ {y} y∈ = ∈dom↓ γ₁ (cnt⇒∈dom γ₁ (fv⇒cnt d (↓-dom γ₂ (fv e) y∈))) (↓-dom γ₂ (fv e) y∈)
