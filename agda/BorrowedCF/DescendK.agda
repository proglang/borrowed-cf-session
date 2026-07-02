module BorrowedCF.DescendK where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import BorrowedCF.DescendAbs
open import Data.Fin.Subset using (Subset; ∁; _∈_; _∉_; _⊆_; ⁅_⁆; _∪_; inside) renaming (⊥ to ⁅⁆)
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

Inj-↑* : (k : ℕ) {ρ : m →ᵣ n} → 𝐂.Inj ρ → 𝐂.Inj (ρ 𝐂.↑* k)
Inj-↑* zero    inj = inj
Inj-↑* (suc k) inj = Inj-↑ (Inj-↑* k inj)

⋯ᵏ-↑-wk : (k : ℕ) (γ : Struct m) {ρ : m →ᵣ n} → (wk^ k γ) 𝐂.⋯ (ρ 𝐂.↑* k) ≡ wk^ k (γ 𝐂.⋯ᵣ ρ)
⋯ᵏ-↑-wk zero    γ = refl
⋯ᵏ-↑-wk (suc k) γ {ρ} = sym (𝐂.⋯-↑-wk (wk^ k γ) (ρ 𝐂.↑* k)) ■ cong 𝐂.wk (⋯ᵏ-↑-wk k γ)

dropᵏ : (k : ℕ) → Subset (k + n) → Subset n
dropᵏ zero    Z = Z
dropᵏ (suc k) Z = dropᵏ k (Vec.tail Z)

wk^↓ : (k : ℕ) (γ : Struct m) (Z : Subset (k + m)) → wk^ k γ ↓ Z ≡ wk^ k (γ ↓ dropᵏ k Z)
wk^↓ zero    γ Z = refl
wk^↓ (suc k) γ Z = wk↓' (wk^ k γ) Z ■ cong 𝐂.wk (wk^↓ k γ (Vec.tail Z))

dropᵏ-∁ : (k : ℕ) (Z : Subset (k + n)) → dropᵏ k (∁ Z) ≡ ∁ (dropᵏ k Z)
dropᵏ-∁ zero    Z = refl
dropᵏ-∁ (suc k) Z = cong (dropᵏ k) (tail-∁ Z) ■ dropᵏ-∁ k (Vec.tail Z)

fsuc^ : (k : ℕ) → 𝔽 n → 𝔽 (k + n)
fsuc^ zero    y = y
fsuc^ (suc k) y = fsuc (fsuc^ k y)

∈dropᵏ : (k : ℕ) {y : 𝔽 n} {Z : Subset (k + n)} → y ∈ dropᵏ k Z → fsuc^ k y ∈ Z
∈dropᵏ zero    p = p
∈dropᵏ (suc k) p = ∈tail (∈dropᵏ k p)

↑*-preimage : (k : ℕ) {ρ : m →ᵣ n} {z : 𝔽 (k + m)} {y : 𝔽 n} →
  (ρ 𝐂.↑* k) z ≡ fsuc^ k y → InImage ρ y
↑*-preimage zero    eq = _ , eq
↑*-preimage (suc k) {z = fzero}   ()
↑*-preimage (suc k) {z = fsuc z′} eq = ↑*-preimage k (suc-injective eq)

freshᵏ : (k : ℕ) → Subset (k + n)
freshᵏ zero    = ⁅⁆
freshᵏ (suc k) = inside ∷ freshᵏ k

fsuc^∉fresh : (k : ℕ) {y : 𝔽 n} → fsuc^ k y ∉ freshᵏ k
fsuc^∉fresh zero            = ∉⊥
fsuc^∉fresh (suc k) (Vec.there p) = fsuc^∉fresh k p
