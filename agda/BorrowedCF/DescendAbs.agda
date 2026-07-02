module BorrowedCF.DescendAbs where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import Data.Fin.Subset using (Subset; ∁; _∈_; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∉∁p⇒x∈p; x∈∁p⇒x∉p; _∈?_; x∈⁅x⁆; ⊆-trans; ∪-identityʳ; p⊆p∪q; q⊆p∪q; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; ∉⊥)
import Data.Vec as Vec
open import Data.Vec using (_∷_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (not)
open import Relation.Nullary using (yes; no)

open Nat.Variables

Inj-↑ : {ϕ : m →ᵣ n} → 𝐂.Inj ϕ → 𝐂.Inj (ϕ ↑)
Inj-↑ inj {fzero}  {fzero}  eq = refl
Inj-↑ inj {fzero}  {fsuc y} ()
Inj-↑ inj {fsuc x} {fzero}  ()
Inj-↑ inj {fsuc x} {fsuc y} eq = cong fsuc (inj (suc-injective eq))

tail-∁ : (Z : Subset (suc n)) → Vec.tail (∁ Z) ≡ ∁ (Vec.tail Z)
tail-∁ (b ∷ Z) = refl

wk↓' : (γ : Struct m) (Z : Subset (suc m)) → 𝐂.wk γ ↓ Z ≡ 𝐂.wk (γ ↓ Vec.tail Z)
wk↓' γ (b ∷ Z) = ↓-dist-wk γ

↓-join : (d : Dir) (α β : Struct n) (X : Subset n) → (join d α β) ↓ X ≡ join d (α ↓ X) (β ↓ X)
↓-join 𝟙 α β X = refl
↓-join L α β X = refl
↓-join R α β X = refl

tail-∪-⁅0⁆ : (Z : Subset (suc n)) → Vec.tail (Z ∪ ⁅ fzero ⁆) ≡ Vec.tail Z
tail-∪-⁅0⁆ (b ∷ Z) = ∪-identityʳ Z

↑ᵣ-preserves-⇐ : {ρ : m →ᵣ n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} →
  ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ → (ρ ↑) 𝐂.Preserves[ Unr ] (T₀ ⸴ Γ₁) ⇐ (T₀ ⸴ Γ₂)
↑ᵣ-preserves-⇐ pre {fzero}  (` u) = u
↑ᵣ-preserves-⇐ pre {fsuc y} (` u) = pre (` u)

allCx-join↓-proj₂ : ∀ {ℓ}{P : Pred 𝕋 ℓ}(d : Dir){α β}(X : Subset n) →
  AllCx P Γ ((join d α β) ↓ X) → AllCx P Γ (β ↓ X)
allCx-join↓-proj₂ 𝟙 X (u ∥ v) = v
allCx-join↓-proj₂ L X (u ; v) = v
allCx-join↓-proj₂ R X (u ; v) = u


un-wk-Unr : {δ : Struct n} → AllCx Unr (T ⸴ Γ) (𝐂.wk δ) → AllCx Unr Γ δ
un-wk-Unr = 𝐂.allCx-⋯⁻¹ (λ{ (` u) → u })

∈tail : {y : 𝔽 n} {X : Subset (suc n)} → y ∈ Vec.tail X → suc y ∈ X
∈tail {X = b ∷ X} y∈ = Vec.there y∈

descend-abs : ∀ {m n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ →
  (dd : Dir) (A : Struct (suc m)) (γa : Struct n) →
  (T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑)) ≼ join dd (CB.`_ fzero) (𝐂.wk γa) →
  ∃[ γr ] ((T₀ ⸴ Γ₁) ∶ A ≼ join dd (CB.`_ fzero) (𝐂.wk γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-abs {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} {ρ = ρ} inj-ρ pre dd A γa ≼b = γr , part1 , part2
  where
  Xd : Subset (suc n)
  Xd = dom (A 𝐂.⋯ (ρ ↑))
  Xd0 : Subset (suc n)
  Xd0 = Xd ∪ ⁅ fzero ⁆
  img : ∀ {y} → y ∈ dom (γa ↓ Vec.tail Xd0) → InImage ρ y
  img {y} y∈ with x∈p∪q⁻ Xd ⁅ fzero ⁆ (∈tail (↓-dom γa (Vec.tail Xd0) y∈))
  ... | inj₁ sy∈ with dom-⋯-InImage A sy∈
  ...   | fsuc w , eq = w , suc-injective eq
  img {y} y∈ | inj₂ (Vec.there sy∈) = contradiction sy∈ ∉⊥
  pim = preimage {ϕ = ρ} (γa ↓ Vec.tail Xd0) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ Vec.tail Xd0
  eqr = proj₂ pim
  0slot : (CB.`_ fzero) ↓ Xd0 ≡ ` fzero
  0slot = ↓-identity-⊆ (CB.`_ fzero) (q⊆p∪q Xd ⁅ fzero ⁆)
  rhs-img : (join dd (CB.`_ fzero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑) ≡ join dd (CB.`_ fzero) (𝐂.wk (γr 𝐂.⋯ ρ))
  rhs-img = join-⋯ {ϕ = ρ ↑} dd (CB.`_ fzero) (𝐂.wk γr) ■ cong₂ (join dd) refl (sym (𝐂.⋯-↑-wk γr ρ))
  rhs-eq : (join dd (CB.`_ fzero) (𝐂.wk γa)) ↓ Xd0 ≡ (join dd (CB.`_ fzero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑)
  rhs-eq = ↓-join dd (CB.`_ fzero) (𝐂.wk γa) Xd0
           ■ (cong₂ (join dd) 0slot (wk↓' γa Xd0 ■ cong 𝐂.wk (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ ↑)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ ↑)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ ↑)) (p⊆p∪q ⁅ fzero ⁆)
  part1 : (T₀ ⸴ Γ₁) ∶ A ≼ join dd (CB.`_ fzero) (𝐂.wk γr)
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd (CB.`_ fzero) (𝐂.wk γr)} {ϕ = ρ ↑}
            (Inj-↑ {ϕ = ρ} inj-ρ) (λ {x} → ↑ᵣ-preserves-⇐ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} pre {x})
            (subst₂ ((T₀ ⸴ Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk-eq : (𝐂.wk γa) ↓ ∁ Xd ≡ 𝐂.wk (γa ↓ ∁ (Vec.tail Xd0))
  wk-eq = wk↓' γa (∁ Xd)
          ■ cong (λ z → 𝐂.wk (γa ↓ z)) (tail-∁ Xd ■ cong ∁ (sym (tail-∪-⁅0⁆ Xd)))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (Vec.tail Xd0))
  unr-part = un-wk-Unr (subst (AllCx Unr (T₀ ⸴ Γ₂)) wk-eq
               (allCx-join↓-proj₂ dd (∁ Xd) (≼⇒extra-Unr ≼b)))
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

