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

open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (+-comm)
open import BorrowedCF.Context.Join using (≼-join; join-flip; biasedDir)

linUnique-flip : {n : ℕ} {Γ : Ctx n} {γ₁ γ₂ : Struct n} (a : Dir) →
                 LinUnique Γ (join a γ₁ γ₂) → LinUnique Γ (join (flipDir a) γ₂ γ₁)
linUnique-flip {γ₁ = γ₁} {γ₂} a lu x ¬u =
  subst (_≤ 1) (cnt-join a γ₁ γ₂ x ■ +-comm (cnt γ₁ x) (cnt γ₂ x) ■ sym (cnt-join (flipDir a) γ₂ γ₁ x)) (lu x ¬u)

↓fv-≼ʳ-wf : {n : ℕ} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} (a : Dir) →
            LinUnique Γ (join a γ₁ γ₂) → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ → Γ ∶ (join a γ₁ γ₂) ↓ fv e ≼ γ₂
↓fv-≼ʳ-wf {γ₁ = γ₁} {γ₂} a lu d =
  ≼-trans (≼-refl (↓-mono-≈ (≈-sym (join-flip a))))
          (↓fv-≼-wf {γ₁ = γ₂} {γ₂ = γ₁} (flipDir a) (linUnique-flip a lu) d)

≤γ-par-wf : {n : ℕ} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e₁ e₂ : Tm n} {T₁ T₂ : 𝕋} {ϵ₁ ϵ₂ : Eff} (p/s : ParSeq) →
  LinUnique Γ (join (biasedDir p/s) γ₁ γ₂) → Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂ →
  Γ ∶ join (biasedDir p/s) ((join (biasedDir p/s) γ₁ γ₂) ↓ fv e₁) ((join (biasedDir p/s) γ₁ γ₂) ↓ fv e₂)
    ≼ join (biasedDir p/s) γ₁ γ₂
≤γ-par-wf {γ₁ = γ₁} {γ₂} p/s lu d₁ d₂ =
  ≼-join (biasedDir p/s) (↓fv-≼-wf {γ₂ = γ₂} (biasedDir p/s) lu d₁) (↓fv-≼ʳ-wf {γ₁ = γ₁} (biasedDir p/s) lu d₂)

≤γ-seq-wf : {n : ℕ} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e₁ e₂ : Tm n} {T₁ T₂ : 𝕋} {ϵ₁ ϵ₂ : Eff} →
  LinUnique Γ (γ₁ ; γ₂) → Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂ →
  Γ ∶ ((γ₁ ; γ₂) ↓ fv e₁) ; ((γ₁ ; γ₂) ↓ fv e₂) ≼ γ₁ ; γ₂
≤γ-seq-wf {γ₁ = γ₁} {γ₂} lu d₁ d₂ =
  ≼-join L (↓fv-≼-wf {γ₂ = γ₂} L lu d₁) (↓fv-≼ʳ-wf {γ₁ = γ₁} L lu d₂)


≤γ-app-wf : {n : ℕ} {Γ : Ctx n} {γ γ₁ γ₂ : Struct n} {e₁ e₂ : Tm n} {S₁ S₂ : 𝕋} {ϵ₁ ϵ₂ : Eff} (a : Dir) →
  LinUnique Γ γ → Γ ∶ γ ≈ join a γ₂ γ₁ → Γ ; γ₁ ⊢ e₁ ∶ S₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ S₂ ∣ ϵ₂ →
  Γ ∶ join a (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ
≤γ-app-wf a lu γ≈ d₁ d₂ =
  ≼-trans (≼-join a (≼-trans (≼-refl (↓-mono-≈ γ≈)) (↓fv-≼-wf a lu' d₂))
                    (≼-trans (≼-refl (↓-mono-≈ γ≈)) (↓fv-≼ʳ-wf a lu' d₁)))
          (≼-refl (≈-sym γ≈))
  where lu' = linUnique-≈ γ≈ lu
