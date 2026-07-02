module BorrowedCF.DescendK where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import BorrowedCF.DescendAbs
open import Data.Fin.Subset using (Subset; ∁; _∈_; _⊆_; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∉∁p⇒x∈p; x∈∁p⇒x∉p; x∉p⇒x∈∁p; _∈?_; x∈⁅x⁆; ⊆-trans; ⊆-refl; ∪-identityʳ; p⊆p∪q; q⊆p∪q; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; x∈p∪q⁺; ∉⊥)
import Data.Sum as Sum
import Data.Vec as Vec
open import Data.Vec using (_∷_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)

open Nat.Variables

-- k-fold weakening at Struct level
wk^ : (k : ℕ) → Struct n → Struct (k + n)
wk^ zero    γ = γ
wk^ (suc k) γ = 𝐂.wk (wk^ k γ)

-- bridge: k-fold wk ≡ ⋯ weaken* k
wkm≗·weaken : {ϕ : m →ᵣ n} → 𝐂.wkm ϕ ≗ (ϕ 𝐂.·ₖ 𝐂.weakenᵣ)
wkm≗·weaken x = refl

⋯-wkm : (γ : Struct m) {ϕ : m →ᵣ n} → γ 𝐂.⋯ᵣ 𝐂.wkm ϕ ≡ 𝐂.wk (γ 𝐂.⋯ᵣ ϕ)
⋯-wkm γ {ϕ} = 𝐂.⋯-cong γ wkm≗·weaken ■ sym (𝐂.fusion γ ϕ 𝐂.weakenᵣ)

weaken*-wk : (γ : Struct n) → γ 𝐂.⋯ᵣ 𝐂.weaken* (suc k) ≡ 𝐂.wk (γ 𝐂.⋯ᵣ 𝐂.weaken* k)
weaken*-wk {k = k} γ = ⋯-wkm γ {ϕ = 𝐂.weaken* k}

wk^≡weaken* : (k : ℕ) (γ : Struct n) → wk^ k γ ≡ γ 𝐂.⋯ᵣ 𝐂.weaken* k
wk^≡weaken* zero    γ = sym (𝐂.⋯-id γ (λ x → refl))
wk^≡weaken* (suc k) γ = cong 𝐂.wk (wk^≡weaken* k γ) ■ sym (weaken*-wk γ)
