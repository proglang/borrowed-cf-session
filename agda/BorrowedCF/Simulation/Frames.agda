module BorrowedCF.Simulation.Frames where

-- | Expression-level evaluation contexts under substitution: single-/multi-frame
--   plugging commutes with substitution, expression reduction (─→ / ⋯→) is stable
--   under value substitution, value-substitution builders (∷ₛ-VSub, ++ₛ-VSub, …),
--   and the frame congruence/fusion lemmas used by the forward simulation.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*

frame-plug₁ : ⦃ K : Kit 𝓕 ⦄ (E : Frame m) {e : Tm m} (ϕ : m –[ K ]→ n) (Vϕ : VSub ϕ) →
              (E [ e ]) ⋯ ϕ ≡ frame-⋯ E ϕ Vϕ [ e ⋯ ϕ ]
frame-plug₁ (□· e₂)       ϕ Vϕ = refl
frame-plug₁ (V₁ ·□)       ϕ Vϕ = refl
frame-plug₁ (□⊗ e₂)       ϕ Vϕ = refl
frame-plug₁ (V₁ ⊗□)       ϕ Vϕ = refl
frame-plug₁ (□; e₂)       ϕ Vϕ = refl
frame-plug₁ (`let-`in e′)  ϕ Vϕ = refl
frame-plug₁ (`let⊗-`in e′) ϕ Vϕ = refl

-- Head reduction is stable under value substitution.

─→-⋯ₛ : (σ : m →ₛ n) → VSub σ → {e₁ e₂ : Tm m} → e₁ ─→ e₂ → e₁ ⋯ σ ─→ e₂ ⋯ σ
─→-⋯ₛ σ Vσ (E-App {e₁} {e₂} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e₂ e₁ σ)) (E-App (value-⋯ V σ Vσ))
─→-⋯ₛ σ Vσ E-Seq = E-Seq
─→-⋯ₛ σ Vσ (E-Let {e₁} {e₂} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e₂ e₁ σ)) (E-Let (value-⋯ V σ Vσ))
─→-⋯ₛ σ Vσ (E-PairElim {e₁} {e₂} {e} V₁ V₂) =
  subst₂ _─→_ refl eq (E-PairElim (value-⋯ V₁ σ Vσ) (value-⋯ V₂ σ Vσ))
  where
    inner : e ⋯ ⦅ wk e₁ ⦆ ⋯ σ ↑ ≡ e ⋯ σ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ σ) ⦆
    inner = dist-↑-⦅⦆-⋯ e (wk e₁) (σ ↑) ■ cong (λ z → e ⋯ σ ↑ ↑ ⋯ ⦅ z ⦆) (sym (⋯-↑-wk e₁ σ))
    eq : e ⋯ σ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ σ) ⦆ ⋯ ⦅ e₂ ⋯ σ ⦆ ≡ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆ ⋯ σ
    eq = cong (_⋯ ⦅ e₂ ⋯ σ ⦆) (sym inner) ■ sym (dist-↑-⦅⦆-⋯ (e ⋯ ⦅ wk e₁ ⦆) e₂ σ)
─→-⋯ₛ σ Vσ (E-Unfold {e}) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e (μ e) σ)) E-Unfold

-- Substitution commutes with recursive (Frame*) plugging.

frame*-⋯ : Frame* m → (σ : m →ₛ n) → VSub σ → Frame* n
frame*-⋯ E* σ Vσ = L.map (λ E → frame-⋯ E σ Vσ) E*

frame-plug* : (E : Frame* m) {t : Tm m} (σ : m →ₛ n) (Vσ : VSub σ) →
              (E [ t ]*) ⋯ σ ≡ frame*-⋯ E σ Vσ [ t ⋯ σ ]*
frame-plug* []       σ Vσ = refl
frame-plug* (E ∷ E*) σ Vσ =
  frame-plug₁ E σ Vσ ■ cong (frame-⋯ E σ Vσ [_]) (frame-plug* E* σ Vσ)

-- Expression reduction (congruence closure) is stable under value substitution.

⋯→-⋯ₛ : (σ : m →ₛ n) → VSub σ → {e₁ e₂ : Tm m} → e₁ ⋯→ e₂ → e₁ ⋯ σ ⋯→ e₂ ⋯ σ
⋯→-⋯ₛ σ Vσ (E-□ red) = E-□ (─→-⋯ₛ σ Vσ red)
⋯→-⋯ₛ σ Vσ (E-Ctx E red) =
  subst₂ _⋯→_ (sym (frame-plug₁ E σ Vσ)) (sym (frame-plug₁ E σ Vσ))
    (E-Ctx (frame-⋯ E σ Vσ) (⋯→-⋯ₛ σ Vσ red))

∷ₛ-VSub : {t : Tm n} {σ : m →ₛ n} → Value t → VSub σ → VSub (t ∷ₛ σ)
∷ₛ-VSub Vt Vσ zero    = Vt
∷ₛ-VSub Vt Vσ (suc i) = Vσ i

++ₛ-VSub : ∀ {a b N} {σ₁ : a →ₛ N} {σ₂ : b →ₛ N} → VSub σ₁ → VSub σ₂ → VSub (σ₁ ++ₛ σ₂)
++ₛ-VSub {a = a} Vσ₁ Vσ₂ i with splitAt a i
... | inj₁ j = Vσ₁ j
... | inj₂ j = Vσ₂ j

weaken-VSub : ∀ {σ : m →ₛ n} (k : ℕ) → VSub σ → VSub (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ k)
weaken-VSub k Vσ i = Vσ i ⋯ᵛ weaken* ⦃ Kᵣ ⦄ k

-- The φ-nest the translation builds is a congruence in its continuation.

·□-cong : {e e′ : Tm n} (eq : e ≡ e′) {V : Value e} {V′ : Value e′} → (V ·□) ≡ (V′ ·□)
·□-cong refl = cong _·□ Value-irr

⊗□-cong : {e e′ : Tm n} (eq : e ≡ e′) {V : Value e} {V′ : Value e′} → (V ⊗□) ≡ (V′ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

-- A frame renamed then substituted equals it composed-substituted.

frame-fusion : ∀ {m₁} (E : Frame m) {ρ : m →ᵣ m₁} {ψ : m₁ →ₛ n} (Vψ : VSub ψ) →
               frame-⋯ (E ⋯ᶠ ρ) ψ Vψ ≡ frame-⋯ E (ρ ·ₖ ψ) (λ x → Vψ (ρ x))
frame-fusion (□· e₂)        {ρ} {ψ} Vψ = cong □·_ (fusion e₂ ρ ψ)
frame-fusion (V₁ ·□)        {ρ} {ψ} Vψ = ·□-cong (fusion (vTm V₁) ρ ψ)
frame-fusion (□⊗ e₂)        {ρ} {ψ} Vψ = cong □⊗_ (fusion e₂ ρ ψ)
frame-fusion (V₁ ⊗□)        {ρ} {ψ} Vψ = ⊗□-cong (fusion (vTm V₁) ρ ψ)
frame-fusion (□; e₂)        {ρ} {ψ} Vψ = cong □;_ (fusion e₂ ρ ψ)
frame-fusion (`let-`in e′)  {ρ} {ψ} Vψ = cong `let-`in_ (fusion e′ (ρ ↑) (ψ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ρ ψ x)))
frame-fusion (`let⊗-`in e′) {ρ} {ψ} Vψ = cong `let⊗-`in_ (fusion e′ (ρ ↑* 2) (ψ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ρ ψ x)))

-- A frame depends on its substitution only pointwise.

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (□· e₂)        Vϕ Vψ eq = cong □·_ (⋯-cong e₂ eq)
frame-cong (V₁ ·□)        Vϕ Vψ eq = ·□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))

-- General two-kit frame fusion (substitution then renaming, or any composition).

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (□· e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □·_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ·□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ·□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
