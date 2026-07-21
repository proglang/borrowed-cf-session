module BorrowedCF.Terms.DescendAbs where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
open import Function.Related.Propositional

open Nat.Variables
open Fin using (suc-injective)

allCx-join↓-proj₂ : ∀ {ℓ}{P : Pred 𝕋 ℓ}{A} ⦃ _ : Join A ⦄ (d : A){α β}(X : Subset n) →
  AllCx P Γ ((join d α β) ↓ X) → AllCx P Γ (β ↓ X)
allCx-join↓-proj₂ d {α} {β} X rewrite join-↓ d α β {X} = proj₂ ∘ allCx-join⁻ d

∪⊆ˡ : ∀ {k} {A B C : Subset k} → A ⊆ B → A ∪ C ⊆ B ∪ C
∪⊆ˡ A⊆B z∈ = x∈p∪q⁺ (Sum.map A⊆B (λ w → w) (x∈p∪q⁻ _ _ z∈))

descend-absX : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ →
  ρ ∶ Γ₁ ⇔ Γ₂ →
  (dd : AD) (A : Struct (suc m)) (γa : Struct n) (X : Subset (suc n)) →
  (∀ {sy} → sy ∈ X → sy ∈img ρ ↑) →
  dom (A 𝐂.⋯ (ρ ↑)) ⊆ X →
  (T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑)) ≼ join dd (` zero) (𝐂.wk γa) →
  ∃[ γr ] ((T₀ ⸴ Γ₁) ∶ A ≼ join dd (` zero) (𝐂.wk γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-absX {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} {ρ = ρ} inj-ρ ρ⇔ dd A γa X Ximg A⊆X ≼b = γr , part1 , part2
  where
  Xtrue : Subset (suc n)
  Xtrue = dom (A 𝐂.⋯ (ρ ↑))
  Xd0 : Subset (suc n)
  Xd0 = X ∪ ⁅ zero ⁆
  img : ∀ {y} → y ∈ dom (γa ↓ V.tail Xd0) → y ∈img ρ
  img {y} y∈ with x∈p∪q⁻ X ⁅ zero ⁆ (∈tail⁻ (↓-dom γa (V.tail Xd0) y∈))
  ... | inj₁ sy∈ with Ximg sy∈
  ...   | suc w , eq = w , suc-injective eq
  img {y} y∈ | inj₂ (there sy∈) = contradiction sy∈ ∉⊥
  pim = ⋯-preimage {ρ = ρ} (γa ↓ V.tail Xd0) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ V.tail Xd0
  eqr = proj₂ pim
  0slot : (` zero) ↓ Xd0 ≡ ` zero
  0slot = ↓-identity-⊆ (` zero) (q⊆p∪q X ⁅ zero ⁆)
  rhs-img : (join dd (` zero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑) ≡ join dd (` zero) (𝐂.wk (γr 𝐂.⋯ ρ))
  rhs-img = join-⋯ dd {ϕ = ρ ↑} (` zero) (𝐂.wk γr) ■ cong₂ (join dd) refl (sym (𝐂.⋯-↑-wk γr ρ))
  rhs-eq : (join dd (` zero) (𝐂.wk γa)) ↓ Xd0 ≡ (join dd (` zero) (𝐂.wk γr)) 𝐂.⋯ (ρ ↑)
  rhs-eq = join-↓ dd (` zero) (𝐂.wk γa)
             ■ (cong₂ (join dd) 0slot (↓-dist-wk-tail γa Xd0 ■ cong 𝐂.wk (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ ↑)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ ↑)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ ↑)) (⊆-trans A⊆X (p⊆p∪q ⁅ zero ⁆))
  part1 : (T₀ ⸴ Γ₁) ∶ A ≼ join dd (` zero) (𝐂.wk γr)
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd (` zero) (𝐂.wk γr)} {ϕ = ρ ↑}
            (↑-inj inj-ρ)
            (↑-⇔ ρ⇔)
            (subst₂ ((T₀ ⸴ Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk-eq : (𝐂.wk γa) ↓ ∁ Xtrue ≡ 𝐂.wk (γa ↓ ∁ (V.tail (Xtrue ∪ ⁅ zero ⁆)))
  wk-eq = ↓-dist-wk-tail γa (∁ Xtrue)
            ■ cong (λ z → 𝐂.wk (γa ↓ z)) (tail-∁ Xtrue ■ cong ∁ (sym (tail-∪⁅0⁆ Xtrue)))
  unr-true : UnrCx Γ₂ (γa ↓ ∁ (V.tail (Xtrue ∪ ⁅ zero ⁆)))
  unr-true = allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₂ (wk-⇔ ⦃ Kᵣ ⦄))
                       (subst (UnrCx (T₀ ⸴ Γ₂)) wk-eq (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b)))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (V.tail Xd0))
  unr-part = ↓-⊆ γa (⊆-∁⁺ (⊆-tail⁺ (∪⊆ˡ A⊆X))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

descend-abs : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ ∶ Γ₁ ⇔ Γ₂ →
  (dd : AD) (A : Struct (suc m)) (γa : Struct n) →
  (T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑)) ≼ join dd (` zero) (𝐂.wk γa) →
  ∃[ γr ] ((T₀ ⸴ Γ₁) ∶ A ≼ join dd (` zero) (𝐂.wk γr)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-abs {ρ = ρ} inj-ρ ρ⇔ dd A γa ≼b =
  descend-absX inj-ρ ρ⇔ dd A γa (dom (A 𝐂.⋯ (ρ ↑))) (∈dom⋯⇒∈img A) ⊆-refl ≼b

dom-join-⊆ : ∀ {n} (d : Dir) (α β : Struct n) → dom (join d α β) ⊆ dom α ∪ dom β
dom-join-⊆ d α β with joinDir d
... | 𝟙 = ⊆-refl
... | L = ⊆-refl
... | R = λ z∈ → x∈p∪q⁺ (Sum.swap (x∈p∪q⁻ _ _ z∈))

wk²↓ : (γ : Struct m) (Z : Subset (suc (suc m))) →
  𝐂.wk (𝐂.wk γ) ↓ Z ≡ 𝐂.wk (𝐂.wk (γ ↓ V.tail (V.tail Z)))
wk²↓ γ Z = ↓-dist-wk-tail (𝐂.wk γ) Z ■ cong 𝐂.wk (↓-dist-wk-tail γ (V.tail Z))

⋯²-↑-wk : (γ : Struct m) {ρ : m →ᵣ n} →
  𝐂.wk (𝐂.wk γ) 𝐂.⋯ (ρ ↑ ↑) ≡ 𝐂.wk (𝐂.wk (γ 𝐂.⋯ ρ))
⋯²-↑-wk γ {ρ} = sym (𝐂.⋯-↑-wk (𝐂.wk γ) (ρ ↑)) ■ cong 𝐂.wk (sym (𝐂.⋯-↑-wk γ ρ))

tail²-∁ : (Z : Subset (suc (suc n))) →
  V.tail (V.tail (∁ Z)) ≡ ∁ (V.tail (V.tail Z))
tail²-∁ Z = cong V.tail (tail-∁ Z) ■ tail-∁ (V.tail Z)

descend-abs2 : ∀ {m n} {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {T₀ T₁ : 𝕋} {ρ : m →ᵣ n} →
  𝐂.Inj ρ → ρ ∶ Γ₁ ⇔ Γ₂ →
  (dd : AD) (Fr : Struct (suc (suc m))) (Fr′ : Struct (suc (suc n)))
  (A : Struct (suc (suc m))) (γa : Struct n) →
  Fr 𝐂.⋯ (ρ ↑ ↑) ≡ Fr′ →
  dom Fr′ ⊆ (⁅ zero ⁆ ∪ ⁅ suc zero ⁆) →
  (T₁ ⸴ T₀ ⸴ Γ₂) ∶ (A 𝐂.⋯ (ρ ↑ ↑)) ≼ join dd Fr′ (𝐂.wk (𝐂.wk γa)) →
  ∃[ γr ] ((T₁ ⸴ T₀ ⸴ Γ₁) ∶ A ≼ join dd Fr (𝐂.wk (𝐂.wk γr))) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-abs2 {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {T₀ = T₀} {T₁ = T₁} {ρ = ρ} inj-ρ ρ⇔ dd Fr Fr′ A γa Frinv Frdom ≼b
  = γr , part1 , part2
  where
  Xtrue : Subset (suc (suc n))
  Xtrue = dom (A 𝐂.⋯ (ρ ↑ ↑))
  fr2 : Subset (suc (suc n))
  fr2 = ⁅ zero ⁆ ∪ ⁅ suc zero ⁆
  Xd0 : Subset (suc (suc n))
  Xd0 = Xtrue ∪ fr2
  img : ∀ {y} → y ∈ dom (γa ↓ V.tail (V.tail Xd0)) → y ∈img ρ
  img {y} y∈ with x∈p∪q⁻ Xtrue fr2 (∈tail⁻ {X = Xd0} (∈tail⁻ {X = V.tail Xd0} (↓-dom γa (V.tail (V.tail Xd0)) y∈)))
  ... | inj₁ ssy∈ with ∈dom⋯⇒∈img A ssy∈
  ...   | suc (suc w) , eq = w , suc-injective (suc-injective eq)
  img {y} y∈ | inj₂ ssy∈fr with x∈p∪q⁻ ⁅ zero ⁆ ⁅ suc zero ⁆ ssy∈fr
  ...   | inj₁ e0 = contradiction (x∈⁅y⁆⇒x≡y zero e0) λ ()
  ...   | inj₂ e1 = contradiction (suc-injective (x∈⁅y⁆⇒x≡y (suc zero) e1)) λ ()
  pim = ⋯-preimage {ρ = ρ} (γa ↓ V.tail (V.tail Xd0)) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ V.tail (V.tail Xd0)
  eqr = proj₂ pim
  Fr-eq : Fr′ ↓ Xd0 ≡ Fr′
  Fr-eq = ↓-identity-⊆ Fr′ (⊆-trans Frdom (q⊆p∪q Xtrue fr2))
  rhs-img : (join dd Fr (𝐂.wk (𝐂.wk γr))) 𝐂.⋯ (ρ ↑ ↑) ≡ join dd Fr′ (𝐂.wk (𝐂.wk (γr 𝐂.⋯ ρ)))
  rhs-img = join-⋯ dd {ϕ = ρ ↑ ↑} Fr (𝐂.wk (𝐂.wk γr)) ■ cong₂ (join dd) Frinv (⋯²-↑-wk γr)
  rhs-eq : (join dd Fr′ (𝐂.wk (𝐂.wk γa))) ↓ Xd0 ≡ (join dd Fr (𝐂.wk (𝐂.wk γr))) 𝐂.⋯ (ρ ↑ ↑)
  rhs-eq = join-↓ dd Fr′ (𝐂.wk (𝐂.wk γa))
             ■ (cong₂ (join dd) Fr-eq (wk²↓ γa Xd0 ■ cong (λ z → 𝐂.wk (𝐂.wk z)) (sym eqr)) ■ sym rhs-img)
  lhs-eq : (A 𝐂.⋯ (ρ ↑ ↑)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ ↑ ↑)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ ↑ ↑)) (p⊆p∪q fr2)
  part1 : (T₁ ⸴ T₀ ⸴ Γ₁) ∶ A ≼ join dd Fr (𝐂.wk (𝐂.wk γr))
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd Fr (𝐂.wk (𝐂.wk γr))} {ϕ = ρ ↑ ↑}
            (↑-inj (↑-inj inj-ρ))
            (↑-⇔ (↑-⇔ ρ⇔))
            (subst₂ ((T₁ ⸴ T₀ ⸴ Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk²-eq : (𝐂.wk (𝐂.wk γa)) ↓ ∁ Xtrue ≡ 𝐂.wk (𝐂.wk (γa ↓ ∁ (V.tail (V.tail Xtrue))))
  wk²-eq = wk²↓ γa (∁ Xtrue) ■ cong (λ z → 𝐂.wk (𝐂.wk (γa ↓ z))) (tail²-∁ Xtrue)
  unr-true : UnrCx Γ₂ (γa ↓ ∁ (V.tail (V.tail Xtrue)))
  unr-true = allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ Kᵣ ⦄ Γ₂ (wk*-⇔ (T₁ ⸴ T₀ ⸴ [])))
                       (subst (UnrCx (T₁ ⸴ T₀ ⸴ Γ₂)) (wk²-eq ■ fusion (γa ↓ ∁ (V.tail (V.tail Xtrue))) 𝐂.weakenᵣ 𝐂.weakenᵣ)
                         (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b)))
  unr-part : UnrCx Γ₂ (γa ↓ ∁ (V.tail (V.tail Xd0)))
  unr-part = ↓-⊆ γa (⊆-∁⁺ (⊆-tail⁺ (⊆-tail⁺ (p⊆p∪q {p = Xtrue} fr2)))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)

