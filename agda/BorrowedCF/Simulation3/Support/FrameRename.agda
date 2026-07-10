module BorrowedCF.Simulation3.Support.FrameRename where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (Dir; L; R; 𝟙)
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Simulation3.Support.Base using (funext)
open import BorrowedCF.Simulation3.Support.Frames using (frame*-⋯)
import Data.Sum as Sum
import Data.List as L

open Nat.Variables

private
  variable
    p : ℕ

app₁-cong : {e₁ e₂ : Tm n} {d : Dir} {V?₁ : d ≡ L → Value e₁} {V?₂ : d ≡ L → Value e₂}
          → e₁ ≡ e₂ → app₁ e₁ d V?₁ ≡ app₁ e₂ d V?₂
app₁-cong refl = cong (app₁ _ _) (funext (λ x → Value-irr))

app₂-cong : {e₁ e₂ : Tm n} {d : Dir} {V?₁ : d ≡ 𝟙 Sum.⊎ d ≡ R → Value e₁} {V?₂ : d ≡ 𝟙 Sum.⊎ d ≡ R → Value e₂}
          → e₁ ≡ e₂ → app₂ e₁ d V?₁ ≡ app₂ e₂ d V?₂
app₂-cong refl = cong (app₂ _ _) (funext (λ x → Value-irr))

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : ∀ {𝓕} ⦃ K : Kit 𝓕 ⦄ (E : Frame m) {ϕ ψ : m –[ K ]→ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (app₁ e d V?)  Vϕ Vψ eq = app₁-cong (⋯-cong e eq)
frame-cong (app₂ e d V?)  Vϕ Vψ eq = app₂-cong (⋯-cong e eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))
frame-cong (`inj□ i)      Vϕ Vψ eq = refl
frame-cong (`case□`of⟨ e₁ ; e₂ ⟩) Vϕ Vψ eq =
  cong₂ `case□`of⟨_;_⟩ (⋯-cong e₁ (eq ~↑)) (⋯-cong e₂ (eq ~↑))

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (app₁ e d V?)  {ϕ} Vϕ {ξ} Vξ Vϕξ = app₁-cong (fusion e ϕ ξ)
frame-fusion-gen (app₂ e d V?)  {ϕ} Vϕ {ξ} Vξ Vϕξ = app₂-cong (fusion e ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
frame-fusion-gen (`inj□ i)      {ϕ} Vϕ {ξ} Vξ Vϕξ = refl
frame-fusion-gen (`case□`of⟨ e₁ ; e₂ ⟩) {ϕ} Vϕ {ξ} Vξ Vϕξ =
  cong₂ `case□`of⟨_;_⟩ (fusion e₁ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₁ (λ x → sym (dist-↑-· ϕ ξ x)))
                        (fusion e₂ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₂ (λ x → sym (dist-↑-· ϕ ξ x)))

-- renaming-specialised cong / fusion for the single-frame and Frame* renaming maps.
⋯ᶠ-cong : (E : Frame m) {ϕ ψ : m →ᵣ n} → ϕ ≗ ψ → E ⋯ᶠ ϕ ≡ E ⋯ᶠ ψ
⋯ᶠ-cong E eq = frame-cong E (λ x → V-`) (λ x → V-`) eq

⋯ᶠ*-cong : (E : Frame* m) {ϕ ψ : m →ᵣ n} → ϕ ≗ ψ → E ⋯ᶠ* ϕ ≡ E ⋯ᶠ* ψ
⋯ᶠ*-cong []      eq = refl
⋯ᶠ*-cong (F ∷ E) eq = cong₂ _∷_ (⋯ᶠ-cong F eq) (⋯ᶠ*-cong E eq)

⋯ᶠ-fuse : (E : Frame m) (ϕ : m →ᵣ p) (ψ : p →ᵣ n) → (E ⋯ᶠ ϕ) ⋯ᶠ ψ ≡ E ⋯ᶠ (ϕ ·ₖ ψ)
⋯ᶠ-fuse E ϕ ψ = frame-fusion-gen E {ϕ} (λ x → V-`) {ψ} (λ x → V-`) (λ x → V-`)

⋯ᶠ*-fuse : (E : Frame* m) (ϕ : m →ᵣ p) (ψ : p →ᵣ n) → (E ⋯ᶠ* ϕ) ⋯ᶠ* ψ ≡ E ⋯ᶠ* (ϕ ·ₖ ψ)
⋯ᶠ*-fuse []      ϕ ψ = refl
⋯ᶠ*-fuse (F ∷ E) ϕ ψ = cong₂ _∷_ (⋯ᶠ-fuse F ϕ ψ) (⋯ᶠ*-fuse E ϕ ψ)

-- frame*-⋯ (substitution) followed by a renaming ⋯ᶠ* fuses (frame analogue of U-σ⋯).
F-σ⋯ : (E : Frame* m) {σ : m →ₛ p} (Vσ : VSub σ) (ρ : p →ᵣ n) (Vσρ : VSub (σ ·ₖ ρ)) →
       (frame*-⋯ E σ Vσ) ⋯ᶠ* ρ ≡ frame*-⋯ E (σ ·ₖ ρ) Vσρ
F-σ⋯ []      Vσ ρ Vσρ = refl
F-σ⋯ (F ∷ E) Vσ ρ Vσρ = cong₂ _∷_ (frame-fusion-gen F Vσ (λ x → V-`) Vσρ) (F-σ⋯ E Vσ ρ Vσρ)
