module BorrowedCF.Simulation3.Support.Frames where

-- | Expression-level evaluation contexts under substitution: single-/multi-frame
--   plugging commutes with substitution, and expression reduction (─→ / ⋯→) is
--   stable under value substitution.  Ported verbatim from Simulation/Frames.agda
--   (only depends on the Base re-exports, so it is safe to copy here).

open import BorrowedCF.Simulation3.Support.Base

frame-plug₁ : ⦃ K : Kit 𝓕 ⦄ (E : Frame m) {e : Tm m} (ϕ : m –[ K ]→ n) (Vϕ : VSub ϕ) →
              (E [ e ]) ⋯ ϕ ≡ frame-⋯ E ϕ Vϕ [ e ⋯ ϕ ]
frame-plug₁ (app₁ e d V?)  ϕ Vϕ = refl
frame-plug₁ (app₂ e d V?)  ϕ Vϕ = refl
frame-plug₁ (□⊗ e₂)       ϕ Vϕ = refl
frame-plug₁ (V₁ ⊗□)       ϕ Vϕ = refl
frame-plug₁ (□; e₂)       ϕ Vϕ = refl
frame-plug₁ (`let-`in e′)  ϕ Vϕ = refl
frame-plug₁ (`let⊗-`in e′) ϕ Vϕ = refl
frame-plug₁ (`inj□ i)      ϕ Vϕ = refl
frame-plug₁ (`case□`of⟨ e₁ ; e₂ ⟩) ϕ Vϕ = refl

-- Head reduction is stable under value substitution.

─→-⋯ₛ : (σ : m →ₛ n) → VSub σ → {e₁ e₂ : Tm m} → e₁ ─→ e₂ → e₁ ⋯ σ ─→ e₂ ⋯ σ
─→-⋯ₛ σ Vσ (E-App {b} {a} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ a b σ)) (E-App (value-⋯ V σ Vσ))
─→-⋯ₛ σ Vσ (E-Seq V) = E-Seq (value-⋯ V σ Vσ)
─→-⋯ₛ σ Vσ (E-Let {e₁} {e₂} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e₂ e₁ σ)) (E-Let (value-⋯ V σ Vσ))
─→-⋯ₛ σ Vσ (E-PairElim {e₁} {e₂} {e} V₁ V₂) =
  subst₂ _─→_ refl eq (E-PairElim (value-⋯ V₁ σ Vσ) (value-⋯ V₂ σ Vσ))
  where
    inner : e ⋯ ⦅ wk e₁ ⦆ ⋯ σ ↑ ≡ e ⋯ σ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ σ) ⦆
    inner = dist-↑-⦅⦆-⋯ e (wk e₁) (σ ↑) ■ cong (λ z → e ⋯ σ ↑ ↑ ⋯ ⦅ z ⦆) (sym (⋯-↑-wk e₁ σ))
    eq : e ⋯ σ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ σ) ⦆ ⋯ ⦅ e₂ ⋯ σ ⦆ ≡ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆ ⋯ σ
    eq = cong (_⋯ ⦅ e₂ ⋯ σ ⦆) (sym inner) ■ sym (dist-↑-⦅⦆-⋯ (e ⋯ ⦅ wk e₁ ⦆) e₂ σ)
─→-⋯ₛ σ Vσ (E-SumElim {e = e} {e₁ = e₁} {e₂ = e₂} {i = i} V) =
  subst₂ _─→_ refl (sumElim-eq i e₁ e₂ e σ) (E-SumElim (value-⋯ V σ Vσ))
  where
    sumElim-eq : ∀ i (e₁ e₂ : Tm (suc m)) (e : Tm m) (σ : m →ₛ n) →
      (if i then (e₁ ⋯ σ ↑) else (e₂ ⋯ σ ↑)) ⋯ ⦅ e ⋯ σ ⦆
        ≡ ((if i then e₁ else e₂) ⋯ ⦅ e ⦆) ⋯ σ
    sumElim-eq i e₁ e₂ e σ with i
    ... | true  = sym (dist-↑-⦅⦆-⋯ e₁ e σ)
    ... | false = sym (dist-↑-⦅⦆-⋯ e₂ e σ)
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
