module BorrowedCF.Terms.DescendK where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
open import Function.Related.Propositional

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Terms.DescendAbs

open Nat.Variables
open Fin using (suc-injective)

fresh : (n k : ℕ) → Subset (k + n)
fresh n zero    = ⁅⁆
fresh n (suc k) = inside ∷ fresh n k

↑ˡ∈fresh : (k n : ℕ) (x : 𝔽 k) → (x ↑ˡ n) ∈ fresh n k
↑ˡ∈fresh (suc k) n zero    = here
↑ˡ∈fresh (suc k) n (suc x) = there (↑ˡ∈fresh k n x)

↑ʳ∉fresh : (k : ℕ) {y : 𝔽 n} → k ↑ʳ y ∉ fresh n k
↑ʳ∉fresh zero    x         = ∉⊥ x
↑ʳ∉fresh (suc k) (there x) = ↑ʳ∉fresh k x

dom⋯wkʳ⊆fresh : ∀ m (γ : Struct n) → dom (γ 𝐂.⋯ᵣ 𝐂.wkʳ m) ⊆ fresh m n
dom⋯wkʳ⊆fresh m γ x∈ = subst (_∈ fresh m _) (∈dom⋯⇒∈img γ {wkʳ m} x∈ .proj₂) (↑ˡ∈fresh _ m _)

descend-absK : ∀ {AD} ⦃ _ : Join AD ⦄ {Γ₁ : Ctx m} {Γ₂ : Ctx n} {ρ : m →ᵣ n}
  (k : ℕ) (Δ : Ctx k) →
  𝐂.Inj ρ → ρ ∶ Γ₁ ⇔ Γ₂ →
  (dd : AD) (Fr : Struct (k + m)) (Fr′ : Struct (k + n))
  (A : Struct (k + m)) (γa : Struct n) →
  Fr 𝐂.⋯ (ρ 𝐂.↑* k) ≡ Fr′ →
  dom Fr′ ⊆ fresh n k →
  (Δ ⸴* Γ₂) ∶ (A 𝐂.⋯ (ρ 𝐂.↑* k)) ≼ join dd Fr′ (γa ⋯ᵣ weaken* k) →
  ∃[ γr ] ((Δ ⸴* Γ₁) ∶ A ≼ join dd Fr (γr ⋯ᵣ weaken* k)) × (Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa)
descend-absK {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ} k Δ inj-ρ ρ⇔ dd Fr Fr′ A γa Frinv Frdom ≼b
  = γr , part1 , part2
  where
  Xtrue : Subset (k + n)
  Xtrue = dom (A 𝐂.⋯ (ρ 𝐂.↑* k))
  Xd0 : Subset (k + n)
  Xd0 = Xtrue ∪ fresh n k
  img : ∀ {y} → y ∈ dom (γa ↓ V.drop k Xd0) → y ∈img ρ
  img {y} y∈ with x∈p∪q⁻ Xtrue (fresh n k) (∈drop⁻ k (↓-dom γa (V.drop k Xd0) y∈))
  ... | inj₁ sy∈   = ∈img-↑*⁻ k y (∈dom⋯⇒∈img A sy∈)
  ... | inj₂ sy∈fr = contradiction sy∈fr (↑ʳ∉fresh k)
  pim = ⋯-preimage {ρ = ρ} (γa ↓ V.drop k Xd0) img
  γr = proj₁ pim
  eqr : γr 𝐂.⋯ ρ ≡ γa ↓ V.drop k Xd0
  eqr = proj₂ pim
  Fr-eq : Fr′ ↓ Xd0 ≡ Fr′
  Fr-eq = ↓-identity-⊆ Fr′ (⊆-trans Frdom (q⊆p∪q Xtrue (fresh n k)))
  rhs-img : (join dd Fr (γr ⋯ᵣ weaken* k)) 𝐂.⋯ (ρ 𝐂.↑* k) ≡ join dd Fr′ (γr 𝐂.⋯ ρ ⋯ᵣ weaken* k)
  rhs-img = join-⋯ dd {ϕ = ρ 𝐂.↑* k} Fr (γr ⋯ᵣ weaken* k) ■ cong₂ (join dd) Frinv (sym (𝐂.⋯-↑*-wk γr ρ k))
  rhs-eq : (join dd Fr′ (γa ⋯ᵣ weaken* k)) ↓ Xd0 ≡ (join dd Fr (γr ⋯ᵣ weaken* k)) 𝐂.⋯ (ρ 𝐂.↑* k)
  rhs-eq = join-↓ dd Fr′ (γa ⋯ᵣ weaken* k) {Xd0}
             ■ cong₂ (join dd) Fr-eq
                 (cong ((γa ⋯ᵣ weaken* k) ↓_) (sym (V.take++drop≡id k Xd0))
                   ■ 𝐂.↓-dist-wk* γa (V.take k Xd0)
                   ■ cong (_⋯ᵣ weaken* k) (sym eqr))
             ■ sym rhs-img
  lhs-eq : (A 𝐂.⋯ (ρ 𝐂.↑* k)) ↓ Xd0 ≡ A 𝐂.⋯ (ρ 𝐂.↑* k)
  lhs-eq = ↓-identity-⊆ (A 𝐂.⋯ (ρ 𝐂.↑* k)) (p⊆p∪q (fresh n k))
  part1 : (Δ ⸴* Γ₁) ∶ A ≼ join dd Fr (γr ⋯ᵣ weaken* k)
  part1 = ≼-⋯⁻¹ {α = A} {β = join dd Fr (γr ⋯ᵣ weaken* k)} {ϕ = ρ 𝐂.↑* k}
            (𝐂.↑*-inj k inj-ρ)
            (𝐂.↑*-⇔ Δ ρ⇔)
            (subst₂ ((Δ ⸴* Γ₂) ∶_≼_) lhs-eq rhs-eq (↓-mono-≼ {X = Xd0} ≼b))
  wk^-eq : (γa ⋯ᵣ weaken* k) ↓ ∁ Xtrue ≡ (γa ↓ ∁ (V.drop k Xtrue)) ⋯ᵣ weaken* k
  wk^-eq = cong ((γa ⋯ᵣ weaken* k) ↓_) (sym (V.take++drop≡id k _))
             ■ 𝐂.↓-dist-wk* γa (V.take k (∁ Xtrue))
             ■ cong (λ X → (γa ↓ X) ⋯ᵣ weaken* k) (drop-∁ k Xtrue)
  unr-true : UnrCx Γ₂ (γa ↓ ∁ (V.drop k Xtrue))
  unr-true = allCx-⋯⁻¹ (⇔-preserves[ reverseImplication ] ⦃ 𝐂.Kᵣ ⦄ Γ₂ (𝐂.wk*-⇔ Δ))
                       (subst (UnrCx _) wk^-eq (allCx-join↓-proj₂ dd (∁ Xtrue) (≼⇒extra-Unr ≼b)))
  unr-part : AllCx Unr Γ₂ (γa ↓ ∁ (V.drop k Xd0))
  unr-part = ↓-⊆ γa (⊆-∁⁺ (⊆-drop⁺ k (p⊆p∪q {p = Xtrue} (fresh n k)))) unr-true
  part2 : Γ₂ ∶ (γr 𝐂.⋯ ρ) ≼ γa
  part2 = subst (Γ₂ ∶_≼ γa) (sym eqr) (↓-strip≼ γa unr-part)
