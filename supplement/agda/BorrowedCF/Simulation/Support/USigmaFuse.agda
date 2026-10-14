module BorrowedCF.Simulation.Support.USigmaFuse where

-- | Substitution sibling of TranslationProperties.U-σ⋯ (which is stated only
--   for the renaming Kit): the translation commutes with an arbitrary output
--   SUBSTITUTION of its target,
--
--       U[ P ] σ ⋯ₚ τ ≡ U[ P ] (σ ·ₖ τ).
--
--   This is sound for any substitution τ because the flags produced by the
--   φ-nest translation are always ν-binder-LOCAL (indices 0F / weaken* sB₁ 1F
--   in the lifted-identity region), hence fixed — as variables — by any lifted
--   τ; the channel-triple's data slots are the constant * = K `unit (fixed by
--   any τ) or plain terms (substituted by fusion).  The engine bookkeeping
--   comes from AcqSubstNat (the Kit-generic siblings of the renaming plumbing).
--
--   Used by Backward/Acq.agda's reverse RU-Acquire codomain reconciliation
--   (the retired U-σ⋯ₛ this replaces was written against the OLD untelescoped
--   Bφ / ν-float translation and is no longer applicable).

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
open import BorrowedCF.Simulation.Support.TranslationProperties using (U-cong)
open import BorrowedCF.Simulation.Support.AcqSubstNat
  using (subst₂→ₖ; subst-⋯ₚ-codₖ; subst-⋯ₚ-domₖ; liftCastₖ; subst-flipₖ
        ; subst-⋯ᵏ; subst-⋯-codᵏ; subst₂-cancelₖ; subst-subst-symᵏ; varΘ-fixₛ)
open import Data.Nat.ListAction using (sum)

open Fin.Patterns

------------------------------------------------------------------------
-- ++ₛ distributes over ⋯ for an output SUBSTITUTION (Kit-generic sibling of
-- TranslationProperties.++ₛ-⋯).
------------------------------------------------------------------------

++ₛ-⋯ₛ : ∀ {a b N N′} (σ₁ : a →ₛ N) (σ₂ : b →ₛ N) (τ : N →ₛ N′) i →
         (σ₁ ++ₛ σ₂) i ⋯ τ ≡ ((λ j → σ₁ j ⋯ τ) ++ₛ (λ j → σ₂ j ⋯ τ)) i
++ₛ-⋯ₛ {a} σ₁ σ₂ τ i = helper (Fin.splitAt a i)
  where
    helper : (s : 𝔽 a ⊎ 𝔽 _) →
             [ σ₁ , σ₂ ]′ s ⋯ τ ≡ [ (λ j → σ₁ j ⋯ τ) , (λ j → σ₂ j ⋯ τ) ]′ s
    helper (inj₁ j) = refl
    helper (inj₂ j) = refl

------------------------------------------------------------------------
-- Ub[_] : pointwise naturality of the data-block leaf under a SUBSTITUTION τ
-- that fixes the block's middle channel as a variable (τ x ≡ ` x′).
------------------------------------------------------------------------

Ub-natₛ : ∀ {n n′} (b : ℕ) (e₁ : Tm n) (x : 𝔽 n) (e₂ : Tm n) (τ : n →ₛ n′) (x′ : 𝔽 n′)
          → τ x ≡ ` x′ → (j : 𝔽 b)
          → Ub[ b ] (e₁ , x , e₂) j ⋯ τ ≡ Ub[ b ] (e₁ ⋯ τ , x′ , e₂ ⋯ τ) j
Ub-natₛ 1             e₁ x e₂ τ x′ fx zero    =
  cong (λ z → ((e₁ ⋯ τ) ⊗ z) ⊗ (e₂ ⋯ τ)) (⋯-var x τ ■ fx)
Ub-natₛ (suc (suc b)) e₁ x e₂ τ x′ fx zero    =
  cong (λ z → ((e₁ ⋯ τ) ⊗ z) ⊗ *) (⋯-var x τ ■ fx)
Ub-natₛ (suc (suc b)) e₁ x e₂ τ x′ fx (suc j) =
  Ub-natₛ (suc b) * x e₂ τ x′ fx j

------------------------------------------------------------------------
-- Substitution naturality of the φ-nest UB[_] (the flag-fixing sibling of
-- TranslationProperties.UB-nat).
------------------------------------------------------------------------

UB-natₛ : ∀ {n n′} (B : TP.BindGroup) (e₁ : Tm n) (x : 𝔽 n) (e₂ : Tm n)
          (τ : n →ₛ n′) (x′ : 𝔽 n′) (fx : τ x ≡ ` x′)
          {f  : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)}
          {f′ : (sum B →ₛ syncs B + n′) → UP.Proc (syncs B + n′)} →
          (∀ σ → f σ UP.⋯ₚ (τ ↑* syncs B) ≡ f′ (λ i → σ i ⋯ (τ ↑* syncs B))) →
          UB[ B ] (e₁ , x , e₂) f UP.⋯ₚ τ ≡ UB[ B ] (e₁ ⋯ τ , x′ , e₂ ⋯ τ) f′
UB-natₛ [] e₁ x e₂ τ x′ fx {f} {f′} h = h (λ ()) ■ cong f′ (funext (λ ()))
UB-natₛ (b ∷ []) e₁ x e₂ τ x′ fx {f} {f′} h =
  h (Ub[ b + 0 ] (e₁ , x , e₂))
  ■ cong f′ (funext (λ i → Ub-natₛ (b + 0) e₁ x e₂ τ x′ fx i))
UB-natₛ {n} {n′} (b ∷ B@(_ ∷ _)) e₁ x e₂ τ x′ fx {f} {f′} h =
  cong₂ (UP.φ ϕ[ b ]) (⋯-var x τ ■ fx)
    (UB-natₛ B (` 0F) (suc x) (e₂ ⋯ weakenᵣ) (τ ↑) (suc x′) fx′ {f = gL} {f′ = gR} contH
     ■ cong (λ cc → UB[ B ] cc gR) ccEqₛ)
  where
    sB = syncs B
    fx′ : (τ ↑) (suc x) ≡ ` (suc x′)
    fx′ = cong (_⋯ weakenᵣ) fx ■ ⋯-var x′ weakenᵣ
    UbL : b →ₛ (sB + suc n)
    UbL = Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
    UbR : b →ₛ (sB + suc n′)
    UbR = Ub[ b ] (e₁ ⋯ τ ⋯ weakenᵣ , suc x′ , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
    gL : (sum B →ₛ sB + suc n) → UP.Proc (sB + suc n)
    gL σ = subst UP.Proc (sym (+-suc sB n))
             (f (λ y → subst Tm (+-suc sB n) ([ UbL , σ ]′ (Fin.splitAt b y))))
    gR : (sum B →ₛ sB + suc n′) → UP.Proc (sB + suc n′)
    gR σ = subst UP.Proc (sym (+-suc sB n′))
             (f′ (λ y → subst Tm (+-suc sB n′) ([ UbR , σ ]′ (Fin.splitAt b y))))
    ccEqₛ : ((` 0F) ⋯ (τ ↑) , suc x′ , (e₂ ⋯ weakenᵣ) ⋯ (τ ↑)) ≡ (` 0F , suc x′ , (e₂ ⋯ τ) ⋯ weakenᵣ)
    ccEqₛ = cong₂ _,_ refl (cong₂ _,_ refl (sym (⋯-↑-wk e₂ τ)))
    Θ : (sB + suc n) →ₛ (sB + suc n′)
    Θ = (τ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ₛ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ₛ z) (sym (+-suc sB n′)) (τ ↑* suc sB)
    Θ⁺eq = subst-flipₖ (+-suc sB n′) (sym (subst₂→ₖ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCastₖ sB τ)
    Y : (sum B →ₛ sB + suc n) → (sum (b ∷ B) →ₛ suc (sB + n))
    Y σ y = subst Tm (+-suc sB n) ([ UbL , σ ]′ (Fin.splitAt b y))
    Y′ : (sum B →ₛ sB + suc n′) → (sum (b ∷ B) →ₛ suc (sB + n′))
    Y′ σ y = subst Tm (+-suc sB n′) ([ UbR , σ ]′ (Fin.splitAt b y))
    θ⁻ : (sB + suc n) →ₛ suc (sB + n′)
    θ⁻ = subst (λ z → z →ₛ suc (sB + n′)) (sym (+-suc sB n)) (τ ↑* suc sB)
    ΘθEq : Θ ≡ subst (λ z → (sB + suc n) →ₛ z) (sym (+-suc sB n′)) θ⁻
    ΘθEq = sym ( sym (subst₂→ₖ (sym (+-suc sB n)) (sym (+-suc sB n′)) (τ ↑* suc sB))
               ■ cong (subst₂ (λ u v → u →ₛ v) (sym (+-suc sB n)) (sym (+-suc sB n′))) (sym (liftCastₖ sB τ))
               ■ subst₂-cancelₖ (+-suc sB n) (+-suc sB n′) Θ )
    ΘrelEq : (t : Tm (sB + suc n)) → t ⋯ θ⁻ ≡ subst Tm (+-suc sB n′) (t ⋯ Θ)
    ΘrelEq t = sym ( cong (λ r → subst Tm (+-suc sB n′) (t ⋯ r)) ΘθEq
                   ■ cong (subst Tm (+-suc sB n′)) (subst-⋯-codᵏ (sym (+-suc sB n′)) t θ⁻)
                   ■ subst-subst-symᵏ (+-suc sB n′) )
    ccUbEqₛ : (((e₁ ⋯ weakenᵣ) ⋯ (τ ↑)) , suc x′ , ((` 0F) ⋯ (τ ↑))) ≡ ((e₁ ⋯ τ ⋯ weakenᵣ) , suc x′ , ` 0F)
    ccUbEqₛ = cong₂ _,_ (sym (⋯-↑-wk e₁ τ)) refl
    UbReq : (j : 𝔽 b) → UbL j ⋯ Θ ≡ UbR j
    UbReq j =
        sym (⋯-↑*-wk (Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) j) (τ ↑) sB)
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (Ub-natₛ b (e₁ ⋯ weakenᵣ) (suc x) (` 0F) (τ ↑) (suc x′) fx′ j)
      ■ cong (λ cc → Ub[ b ] cc j ⋯ weaken* ⦃ Kᵣ ⦄ sB) ccUbEqₛ
    Yeq : (σ : sum B →ₛ sB + suc n) →
          (λ i → Y σ i ⋯ (τ ↑* suc sB)) ≡ Y′ (λ i → σ i ⋯ Θ)
    Yeq σ = funext (λ i →
        subst-⋯ᵏ (+-suc sB n) ([ UbL , σ ]′ (Fin.splitAt b i)) (τ ↑* suc sB)
      ■ ΘrelEq ([ UbL , σ ]′ (Fin.splitAt b i))
      ■ cong (subst Tm (+-suc sB n′)) (body (Fin.splitAt b i)))
      where
        body : (s : 𝔽 b ⊎ 𝔽 (sum B)) →
               [ UbL , σ ]′ s ⋯ Θ ≡ [ UbR , (λ i → σ i ⋯ Θ) ]′ s
        body (inj₁ j) = UbReq j
        body (inj₂ k) = refl
    contH : (σ : sum B →ₛ sB + suc n) →
            gL σ UP.⋯ₚ ((τ ↑) ↑* sB) ≡ gR (λ i → σ i ⋯ ((τ ↑) ↑* sB))
    contH σ =
        subst-⋯ₚ-domₖ (+-suc sB n) (f (Y σ)) Θ
      ■ cong (f (Y σ) UP.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-codₖ (sym (+-suc sB n′)) (f (Y σ)) (τ ↑* suc sB)
      ■ cong (subst UP.Proc (sym (+-suc sB n′))) (h (Y σ) ■ cong f′ (Yeq σ))

------------------------------------------------------------------------
-- U-σ⋯ₛ : the translation commutes with an output SUBSTITUTION.
------------------------------------------------------------------------

U-σ⋯ₛ : ∀ {m n n′} (P : TP.Proc m) {σ : m →ₛ n} {τ : n →ₛ n′} →
        U[ P ] σ UP.⋯ₚ τ ≡ U[ P ] (σ ·ₖ τ)
U-σ⋯ₛ TP.⟪ e ⟫ {σ} {τ} = cong UP.⟪_⟫ (fusion e σ τ)
U-σ⋯ₛ (P TP.∥ Q)       = cong₂ UP._∥_ (U-σ⋯ₛ P) (U-σ⋯ₛ Q)
U-σ⋯ₛ {n = n} {n′ = n′} (TP.ν B₁ B₂ P) {σ} {τ} =
  cong UP.ν
    (UB-natₛ B₁ * 0F * (τ ↑* 2) 0F refl {f′ = f₁′}
       (λ ξ₁ →
          UB-natₛ B₂ * (weaken* ⦃ Kᵣ ⦄ sB₁ 1F) * Ξ₁ (weaken* ⦃ Kᵣ ⦄ sB₁ 1F) flag1
            {f′ = f₂′ (λ i → ξ₁ i ⋯ Ξ₁)}
            (λ ξ₂ → U-σ⋯ₛ P ■ U-cong P (outdistₛ ξ₁ ξ₂))))
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Ξ₁ : (sB₁ + (2 + n)) →ₛ (sB₁ + (2 + n′))
    Ξ₁ = (τ ↑* 2) ↑* sB₁
    Ξ₂ : (sB₂ + (sB₁ + (2 + n))) →ₛ (sB₂ + (sB₁ + (2 + n′)))
    Ξ₂ = Ξ₁ ↑* sB₂
    flag1 : Ξ₁ (weaken* ⦃ Kᵣ ⦄ sB₁ 1F) ≡ ` (weaken* ⦃ Kᵣ ⦄ sB₁ 1F)
    flag1 = varΘ-fixₛ sB₁ (τ ↑* 2) 1F 1F (⋯-var 0F weakenᵣ)
    f₂′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → (sum B₂ →ₛ sB₂ + (sB₁ + (2 + n′))) → UP.Proc (sB₂ + (sB₁ + (2 + n′)))
    f₂′ σ₁ σ₂ = U[ P ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ σ₂)
                       ++ₛ (λ i → (σ ·ₖ τ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    f₁′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → UP.Proc (sB₁ + (2 + n′))
    f₁′ σ₁ = UB[ B₂ ] (* , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , *) (f₂′ σ₁)
    outdistₛ : ∀ (ξ₁ : sum B₁ →ₛ sB₁ + (2 + n)) (ξ₂ : sum B₂ →ₛ sB₂ + (sB₁ + (2 + n))) →
               (((λ i → ξ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ ξ₂)
                 ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)) ·ₖ Ξ₂
               ≗ ((λ i → (λ j → ξ₁ j ⋯ Ξ₁) i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → ξ₂ i ⋯ Ξ₂))
                 ++ₛ (λ i → (σ ·ₖ τ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    outdistₛ ξ₁ ξ₂ j =
        ++ₛ-⋯ₛ ((λ i → ξ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ ξ₂)
              (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) Ξ₂ j
      ■ [,]-cong compA compB (Fin.splitAt (sum B₁ + sum B₂) j)
      where
        compA : ∀ i → ((λ i → ξ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ ξ₂) i ⋯ Ξ₂
                      ≡ ((λ i → (ξ₁ i ⋯ Ξ₁) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → ξ₂ i ⋯ Ξ₂)) i
        compA i = ++ₛ-⋯ₛ (λ i → ξ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ξ₂ Ξ₂ i
                ■ [,]-cong (λ j → sym (⋯-↑*-wk (ξ₁ j) Ξ₁ sB₂)) (λ j → refl) (Fin.splitAt (sum B₁) i)
        compB : ∀ i → (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ Ξ₂
                      ≡ (σ ·ₖ τ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        compB i = sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) Ξ₁ sB₂)
                ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (τ ↑* 2) sB₁))
                ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i) τ 2))
