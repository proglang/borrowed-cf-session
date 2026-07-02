module BorrowedCF.DescendAbs where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
import BorrowedCF.Context.Base as CB
open import Data.Fin.Subset using (Subset; ∁; _∈_; _⊆_; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∉∁p⇒x∈p; x∈∁p⇒x∉p; x∉p⇒x∈∁p; _∈?_; x∈⁅x⁆; ⊆-trans; ⊆-refl; ∪-identityʳ; p⊆p∪q; q⊆p∪q; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; x∈p∪q⁺; ∉⊥)
import Data.Sum as Sum
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

↓-join : ∀ {A} ⦃ _ : Join A ⦄ (d : A) (α β : Struct n) (X : Subset n) → (join d α β) ↓ X ≡ join d (α ↓ X) (β ↓ X)
↓-join d α β X with joinDir d
... | 𝟙 = refl
... | L = refl
... | R = refl

tail-∪-⁅0⁆ : (Z : Subset (suc n)) → Vec.tail (Z ∪ ⁅ fzero ⁆) ≡ Vec.tail Z
tail-∪-⁅0⁆ (b ∷ Z) = ∪-identityʳ Z

↑ᵣ-preserves-⇐ : {ρ : m →ᵣ n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} →
  ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ → (ρ ↑) 𝐂.Preserves[ Unr ] (T₀ ⸴ Γ₁) ⇐ (T₀ ⸴ Γ₂)
↑ᵣ-preserves-⇐ pre {fzero}  (` u) = u
↑ᵣ-preserves-⇐ pre {fsuc y} (` u) = pre (` u)

allCx-join↓-proj₂ : ∀ {ℓ}{P : Pred 𝕋 ℓ}{A} ⦃ _ : Join A ⦄ (d : A){α β}(X : Subset n) →
  AllCx P Γ ((join d α β) ↓ X) → AllCx P Γ (β ↓ X)
allCx-join↓-proj₂ d X u with joinDir d
allCx-join↓-proj₂ d X (u ∥ v) | 𝟙 = v
allCx-join↓-proj₂ d X (u ; v) | L = v
allCx-join↓-proj₂ d X (u ; v) | R = u


un-wk-Unr : {δ : Struct n} → AllCx Unr (T ⸴ Γ) (𝐂.wk δ) → AllCx Unr Γ δ
un-wk-Unr = 𝐂.allCx-⋯⁻¹ (λ{ (` u) → u })

∈tail : {y : 𝔽 n} {X : Subset (suc n)} → y ∈ Vec.tail X → suc y ∈ X
∈tail {X = b ∷ X} y∈ = Vec.there y∈

tail⊆ : ∀ {k} {A B : Subset (suc k)} → A ⊆ B → Vec.tail A ⊆ Vec.tail B
tail⊆ {A = a ∷ A} {b ∷ B} A⊆B {y} y∈ with A⊆B (Vec.there y∈)
... | Vec.there r = r

∁⊆ : ∀ {k} {A B : Subset k} → A ⊆ B → ∁ B ⊆ ∁ A
∁⊆ A⊆B x∈∁B = x∉p⇒x∈∁p (λ x∈A → x∈∁p⇒x∉p x∈∁B (A⊆B x∈A))

∪⊆ˡ : ∀ {k} {A B C : Subset k} → A ⊆ B → A ∪ C ⊆ B ∪ C
∪⊆ˡ A⊆B z∈ = x∈p∪q⁺ (Sum.map A⊆B (λ w → w) (x∈p∪q⁻ _ _ z∈))

descend-absX : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ →
  (dd : AD) (A : Struct (suc m)) (γa : Struct n) (X : Subset (suc n)) →
  (∀ {sy} → sy ∈ X → InImage (ρ ↑) sy) →
  dom (A 𝐂.⋯ (ρ ↑)) ⊆ X →
  (T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑)) ≼ join dd (CB.`_ fzero) (𝐂.wk γa) →
  ∃[ γr ] ((T₀ ⸴ Γ₁) ∶ A ≼ join dd (CB.`_ fzero) (𝐂.wk γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-absX {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} {ρ = ρ} inj-ρ pre dd A γa X Ximg A⊆X ≼b = γr , part1 , part2
  where
  Xtrue : Subset (suc n)
  Xtrue = dom (A 𝐂.⋯ (ρ ↑))
  Xd0 : Subset (suc n)
  Xd0 = X ∪ ⁅ fzero ⁆
  img : ∀ {y} → y ∈ dom (γa ↓ Vec.tail Xd0) → InImage ρ y
  img {y} y∈ with x∈p∪q⁻ X ⁅ fzero ⁆ (∈tail (↓-dom γa (Vec.tail Xd0) y∈))
  ... | inj₁ sy∈ with Ximg sy∈
  ...   | fsuc w , eq = w , suc-injective eq
  img {y} y∈ | inj₂ (Vec.there sy∈) = contradiction sy∈ ∉⊥
  pim = preimage {ϕ = ρ} (γa ↓ Vec.tail Xd0) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ Vec.tail Xd0
  eqr = proj₂ pim
  0slot : (CB.`_ fzero) ↓ Xd0 ≡ ` fzero
  0slot = ↓-identity-⊆ (CB.`_ fzero) (q⊆p∪q X ⁅ fzero ⁆)
  rhs-img : (join dd (CB.`_ fzero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑) ≡ join dd (CB.`_ fzero) (𝐂.wk (γr 𝐂.⋯ ρ))
  rhs-img = join-⋯ {ϕ = ρ ↑} dd (CB.`_ fzero) (𝐂.wk γr) ■ cong₂ (join dd) refl (sym (𝐂.⋯-↑-wk γr ρ))
  rhs-eq : (join dd (CB.`_ fzero) (𝐂.wk γa)) ↓ Xd0 ≡ (join dd (CB.`_ fzero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑)
  rhs-eq = ↓-join dd (CB.`_ fzero) (𝐂.wk γa) Xd0
           ■ (cong₂ (join dd) 0slot (wk↓' γa Xd0 ■ cong 𝐂.wk (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ ↑)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ ↑)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ ↑)) (⊆-trans A⊆X (p⊆p∪q ⁅ fzero ⁆))
  part1 : (T₀ ⸴ Γ₁) ∶ A ≼ join dd (CB.`_ fzero) (𝐂.wk γr)
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd (CB.`_ fzero) (𝐂.wk γr)} {ϕ = ρ ↑}
            (Inj-↑ {ϕ = ρ} inj-ρ) (λ {x} → ↑ᵣ-preserves-⇐ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} pre {x})
            (subst₂ ((T₀ ⸴ Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk-eq : (𝐂.wk γa) ↓ ∁ Xtrue ≡ 𝐂.wk (γa ↓ ∁ (Vec.tail (Xtrue ∪ ⁅ fzero ⁆)))
  wk-eq = wk↓' γa (∁ Xtrue)
          ■ cong (λ z → 𝐂.wk (γa ↓ z)) (tail-∁ Xtrue ■ cong ∁ (sym (tail-∪-⁅0⁆ Xtrue)))
  unr-true : AllCx Unr Γ₂ (γa ↓ ∁ (Vec.tail (Xtrue ∪ ⁅ fzero ⁆)))
  unr-true = un-wk-Unr (subst (AllCx Unr (T₀ ⸴ Γ₂)) wk-eq
               (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b)))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (Vec.tail Xd0))
  unr-part = ↓-⊆ γa (∁⊆ (tail⊆ (∪⊆ˡ A⊆X))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

descend-abs : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ →
  (dd : AD) (A : Struct (suc m)) (γa : Struct n) →
  (T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑)) ≼ join dd (CB.`_ fzero) (𝐂.wk γa) →
  ∃[ γr ] ((T₀ ⸴ Γ₁) ∶ A ≼ join dd (CB.`_ fzero) (𝐂.wk γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-abs {ρ = ρ} inj-ρ pre dd A γa ≼b =
  descend-absX inj-ρ pre dd A γa (dom (A 𝐂.⋯ (ρ ↑))) (dom-⋯-InImage A) ⊆-refl ≼b

Inj-↑↑ : {ϕ : m →ᵣ n} → 𝐂.Inj ϕ → 𝐂.Inj (ϕ ↑ ↑)
Inj-↑↑ inj = Inj-↑ (Inj-↑ inj)

wk²↓ : (γ : Struct m) (Z : Subset (suc (suc m))) →
  𝐂.wk (𝐂.wk γ) ↓ Z ≡ 𝐂.wk (𝐂.wk (γ ↓ Vec.tail (Vec.tail Z)))
wk²↓ γ Z = wk↓' (𝐂.wk γ) Z ■ cong 𝐂.wk (wk↓' γ (Vec.tail Z))

⋯²-↑-wk : (γ : Struct m) {ρ : m →ᵣ n} →
  𝐂.wk (𝐂.wk γ) 𝐂.⋯ (ρ ↑ ↑) ≡ 𝐂.wk (𝐂.wk (γ 𝐂.⋯ ρ))
⋯²-↑-wk γ {ρ} = sym (𝐂.⋯-↑-wk (𝐂.wk γ) (ρ ↑)) ■ cong 𝐂.wk (sym (𝐂.⋯-↑-wk γ ρ))

tail²-∁ : (Z : Subset (suc (suc n))) →
  Vec.tail (Vec.tail (∁ Z)) ≡ ∁ (Vec.tail (Vec.tail Z))
tail²-∁ Z = cong Vec.tail (tail-∁ Z) ■ tail-∁ (Vec.tail Z)

descend-abs2 : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ T₁ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ 𝐂.Preserves[ Unr ] Γ₁ ⇐ Γ₂ →
  (dd : AD) (Fr : Struct (suc (suc m))) (Fr′ : Struct (suc (suc n)))
  (A : Struct (suc (suc m))) (γa : Struct n) →
  Fr 𝐂.⋯ (ρ ↑ ↑) ≡ Fr′ →
  dom Fr′ ⊆ (⁅ fzero ⁆ ∪ ⁅ fsuc fzero ⁆) →
  (T₁ ⸴ T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑ ↑)) ≼ join dd Fr′ (𝐂.wk (𝐂.wk γa)) →
  ∃[ γr ] ((T₁ ⸴ T₀ ⸴ Γ₁) ∶ A ≼ join dd Fr (𝐂.wk (𝐂.wk γr))) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-abs2 {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} {T₁ = T₁} {ρ = ρ} inj-ρ pre dd Fr Fr′ A γa Frinv Frdom ≼b
  = γr , part1 , part2
  where
  Xtrue : Subset (suc (suc n))
  Xtrue = dom (A 𝐂.⋯ (ρ ↑ ↑))
  fr2 : Subset (suc (suc n))
  fr2 = ⁅ fzero ⁆ ∪ ⁅ fsuc fzero ⁆
  Xd0 : Subset (suc (suc n))
  Xd0 = Xtrue ∪ fr2
  img : ∀ {y} → y ∈ dom (γa ↓ Vec.tail (Vec.tail Xd0)) → InImage ρ y
  img {y} y∈ with x∈p∪q⁻ Xtrue fr2 (∈tail {X = Xd0} (∈tail {X = Vec.tail Xd0} (↓-dom γa (Vec.tail (Vec.tail Xd0)) y∈)))
  ... | inj₁ ssy∈ with dom-⋯-InImage A ssy∈
  ...   | fsuc (fsuc w) , eq = w , suc-injective (suc-injective eq)
  img {y} y∈ | inj₂ ssy∈fr with x∈p∪q⁻ ⁅ fzero ⁆ ⁅ fsuc fzero ⁆ ssy∈fr
  ...   | inj₁ e0 = contradiction (x∈⁅y⁆⇒x≡y fzero e0) λ ()
  ...   | inj₂ e1 = contradiction (suc-injective (x∈⁅y⁆⇒x≡y (fsuc fzero) e1)) λ ()
  pim = preimage {ϕ = ρ} (γa ↓ Vec.tail (Vec.tail Xd0)) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ Vec.tail (Vec.tail Xd0)
  eqr = proj₂ pim
  Fr-eq : Fr′ ↓ Xd0 ≡ Fr′
  Fr-eq = ↓-identity-⊆ Fr′ (⊆-trans Frdom (q⊆p∪q Xtrue fr2))
  rhs-img : (join dd Fr (𝐂.wk (𝐂.wk γr))) 𝐂.⋯ (ρ ↑ ↑) ≡ join dd Fr′ (𝐂.wk (𝐂.wk (γr 𝐂.⋯ ρ)))
  rhs-img = join-⋯ {ϕ = ρ ↑ ↑} dd Fr (𝐂.wk (𝐂.wk γr)) ■ cong₂ (join dd) Frinv (⋯²-↑-wk γr)
  rhs-eq : (join dd Fr′ (𝐂.wk (𝐂.wk γa))) ↓ Xd0 ≡ (join dd Fr (𝐂.wk (𝐂.wk γr))) 𝐂.⋯ (ρ ↑ ↑)
  rhs-eq = ↓-join dd Fr′ (𝐂.wk (𝐂.wk γa)) Xd0
           ■ (cong₂ (join dd) Fr-eq (wk²↓ γa Xd0 ■ cong (λ z → 𝐂.wk (𝐂.wk z)) (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ ↑ ↑)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ ↑ ↑)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ ↑ ↑)) (p⊆p∪q fr2)
  part1 : (T₁ ⸴ T₀ ⸴ Γ₁) ∶ A ≼ join dd Fr (𝐂.wk (𝐂.wk γr))
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd Fr (𝐂.wk (𝐂.wk γr))} {ϕ = ρ ↑ ↑}
            (Inj-↑↑ inj-ρ)
            (λ {x} → ↑ᵣ-preserves-⇐ {ρ = ρ ↑} {Γ₁ = T₀ ⸴ Γ₁} {Γ₂ = T₀ ⸴ Γ₂} {T₀ = T₁}
                       (λ {x'} → ↑ᵣ-preserves-⇐ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} pre {x'}) {x})
            (subst₂ ((T₁ ⸴ T₀ ⸴ Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk²-eq : (𝐂.wk (𝐂.wk γa)) ↓ ∁ Xtrue ≡ 𝐂.wk (𝐂.wk (γa ↓ ∁ (Vec.tail (Vec.tail Xtrue))))
  wk²-eq = wk²↓ γa (∁ Xtrue) ■ cong (λ z → 𝐂.wk (𝐂.wk (γa ↓ z))) (tail²-∁ Xtrue)
  unr-true : AllCx Unr Γ₂ (γa ↓ ∁ (Vec.tail (Vec.tail Xtrue)))
  unr-true = un-wk-Unr (un-wk-Unr (subst (AllCx Unr (T₁ ⸴ T₀ ⸴ Γ₂)) wk²-eq
               (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b))))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (Vec.tail (Vec.tail Xd0)))
  unr-part = ↓-⊆ γa (∁⊆ (tail⊆ (tail⊆ (p⊆p∪q {p = Xtrue} fr2)))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

