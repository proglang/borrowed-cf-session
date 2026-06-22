module BorrowedCF.Simulation.TranslationProperties where

-- | Properties of the translation U[_] / UB[_] / Ub[_]: congruence in the
--   substitution argument, naturality (substitution and renaming commute with the
--   translation), and renaming of channel triples (mapᶜ).

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.Frames

─→-subst : {a b : ℕ} (eq : a ≡ b) {x y : 𝐔.Proc a} → x 𝐔R.─→ₚ y → subst 𝐔.Proc eq x 𝐔R.─→ₚ subst 𝐔.Proc eq y
─→-subst refl xy = xy

-- Value-substitution preservation.

Ub-cong : (b : ℕ) (cc : UChan m) {f g : (b →ₛ m) → 𝐔.Proc m} →
          (∀ σ → f σ 𝐔.≋ g σ) → Ub[ b ] cc f 𝐔.≋ Ub[ b ] cc g
Ub-cong zero cc h = h λ()
Ub-cong (suc zero) (e₁ , x , e₂) h = h (((e₁ ⊗ (` x)) ⊗ e₂) ∷ₛ λ())
Ub-cong (suc (suc b)) (e₁ , x , e₂) h =
  Ub-cong (suc b) (K `unit , x , e₂) (λ σ → h (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ))

UB-cong : (B : 𝐓.BindGroup) (cc : UChan n) {f g : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)} →
          (∀ σ → f σ 𝐔.≋ g σ) → UB[ B ] cc f 𝐔.≋ UB[ B ] cc g
UB-cong [] cc h = h λ()
UB-cong (c ∷ []) cc h = Ub-cong c cc (λ σh → h (σh ++ₛ λ()))
UB-cong (c ∷ B@(_ ∷ _)) cc h =
  𝐔.φ-cong (𝐔.∥-cong ε (UB-cong B _ (λ σt → Ub-cong c _
    (λ σh → ≋-subst (sym (+-suc (syncs B) _))
              (h (subst (sum (c ∷ B) →ₛ_) (+-suc (syncs B) _) (σh ++ₛ σt)))))))

VChan : UChan n → Set
VChan (e₁ , _ , e₂) = Value e₁ × Value e₂

VSub-subst : ∀ {a b D} (eq : a ≡ b) {σ : D →ₛ a} → VSub σ → VSub (subst (D →ₛ_) eq σ)
VSub-subst refl Vσ = Vσ

∥-right-─→ : {P Q R : 𝐔.Proc n} → Q 𝐔R.─→ₚ R → (P 𝐔.∥ Q) 𝐔R.─→ₚ (P 𝐔.∥ R)
∥-right-─→ red = 𝐔R.RU-Struct 𝐔.∥-comm (𝐔R.RU-Par red) 𝐔.∥-comm

-- Reduction-variant of the φ-nest congruence (threads VSub for the recursive sim→).

Ub-cong-─→ : (b : ℕ) (cc : UChan m) → VChan cc → {f g : (b →ₛ m) → 𝐔.Proc m} →
             (∀ σ → VSub σ → f σ 𝐔R.─→ₚ g σ) → Ub[ b ] cc f 𝐔R.─→ₚ Ub[ b ] cc g
Ub-cong-─→ zero cc Vcc h = h _ (λ ())
Ub-cong-─→ (suc zero) (e₁ , x , e₂) (Ve₁ , Ve₂) h = h _ (∷ₛ-VSub (V-⊗ (V-⊗ Ve₁ V-`) Ve₂) (λ ()))
Ub-cong-─→ (suc (suc b)) (e₁ , x , e₂) (Ve₁ , Ve₂) h =
  Ub-cong-─→ (suc b) (K `unit , x , e₂) (V-K , Ve₂)
    (λ σ Vσ → h _ (∷ₛ-VSub (V-⊗ (V-⊗ Ve₁ V-`) V-K) Vσ))

UB-cong-─→ : (B : 𝐓.BindGroup) (cc : UChan n) → VChan cc →
             {f g : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)} →
             (∀ σ → VSub σ → f σ 𝐔R.─→ₚ g σ) → UB[ B ] cc f 𝐔R.─→ₚ UB[ B ] cc g
UB-cong-─→ [] cc Vcc h = h _ (λ ())
UB-cong-─→ (c ∷ []) cc Vcc h = Ub-cong-─→ c cc Vcc (λ σh Vσh → h _ (++ₛ-VSub Vσh (λ ())))
UB-cong-─→ (c ∷ B@(_ ∷ _)) (e₁ , x , e₂) (Ve₁ , Ve₂) h =
  𝐔R.RU-Sync (∥-right-─→
    (UB-cong-─→ B (` 0F , suc x , e₂ ⋯ weakenᵣ) (V-` , Ve₂ ⋯ᵛ weakenᵣ)
      (λ σt Vσt → Ub-cong-─→ c _
        (Ve₁ ⋯ᵛ weakenᵣ ⋯ᵛ weaken* ⦃ Kᵣ ⦄ (syncs B) , V-` ⋯ᵛ weaken* ⦃ Kᵣ ⦄ (syncs B))
        (λ σh Vσh → ─→-subst (sym (+-suc (syncs B) _))
          (h _ (VSub-subst (+-suc (syncs B) _) (++ₛ-VSub Vσh Vσt)))))))

-- ≡-variant of the φ-nest congruence (for reasoning about the translation under renaming).

Ub-cong-≡ : (b : ℕ) (cc : UChan m) {f g : (b →ₛ m) → 𝐔.Proc m} →
            (∀ σ → f σ ≡ g σ) → Ub[ b ] cc f ≡ Ub[ b ] cc g
Ub-cong-≡ zero cc h = h (λ ())
Ub-cong-≡ (suc zero) (e₁ , x , e₂) h = h (((e₁ ⊗ (` x)) ⊗ e₂) ∷ₛ λ ())
Ub-cong-≡ (suc (suc b)) (e₁ , x , e₂) h =
  Ub-cong-≡ (suc b) (K `unit , x , e₂) (λ σ → h (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ))

UB-cong-≡ : (B : 𝐓.BindGroup) (cc : UChan n) {f g : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)} →
            (∀ σ → f σ ≡ g σ) → UB[ B ] cc f ≡ UB[ B ] cc g
UB-cong-≡ [] cc h = h (λ ())
UB-cong-≡ (c ∷ []) cc h = Ub-cong-≡ c cc (λ σh → h (σh ++ₛ λ ()))
UB-cong-≡ (c ∷ B@(_ ∷ _)) cc h =
  cong 𝐔.φ (cong₂ 𝐔._∥_ refl (UB-cong-≡ B _ (λ σt → Ub-cong-≡ c _
    (λ σh → cong (subst 𝐔.Proc (sym (+-suc (syncs B) _)))
              (h (subst (sum (c ∷ B) →ₛ_) (+-suc (syncs B) _) (σh ++ₛ σt)))))))

-- Right congruence of the substitution concatenation.

U-cong : (P : 𝐓.Proc m) {σ₁ σ₂ : m →ₛ n} → σ₁ ≗ σ₂ → U[ P ] σ₁ ≡ U[ P ] σ₂
U-cong 𝐓.⟪ e ⟫   eq = cong 𝐔.⟪_⟫ (⋯-cong e eq)
U-cong (P 𝐓.∥ Q) eq = cong₂ 𝐔._∥_ (U-cong P eq) (U-cong Q eq)
U-cong (𝐓.ν B₁ B₂ P) eq =
  cong 𝐔.ν (UB-cong-≡ B₁ _ (λ τ₁ → UB-cong-≡ B₂ _ (λ τ₂ →
    U-cong P (++ₛ-congʳ _ (λ i →
      cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (eq i))))))

-- A lifted renaming distributes over a substitution concatenation.

dist-↑*-++ₛ : ∀ len {m m′ N} {ρ : m →ᵣ m′} {A : len →ₛ N} {C : m′ →ₛ N} →
              (ρ ↑* len) ·ₖ (A ++ₛ C) ≗ A ++ₛ (ρ ·ₖ C)
dist-↑*-++ₛ len {m} {m′} {N} {ρ} {A} {C} i =
  cong (A ++ₛ C) (↑*∼id/wk-splitAt ρ len i) ■ helper (splitAt len i)
  where
    helper : (s : 𝔽 len ⊎ 𝔽 m) →
             (A ++ₛ C) ([ id/` ⦃ Kᵣ ⦄ ∘ (_↑ˡ m′) , ρ ·ₖ weaken* ⦃ Kᵣ ⦄ len ] s) ≡ [ A , ρ ·ₖ C ]′ s
    helper (inj₁ j) = cong [ A , C ]′ (splitAt-↑ˡ len j m′)
    helper (inj₂ k) =
      cong (A ++ₛ C) (weaken*~↑ʳ ⦃ Kᵣ ⦄ len (ρ k)) ■ cong [ A , C ]′ (splitAt-↑ʳ len m′ (ρ k))

-- The translation commutes with (typed) process renaming.

U-⋯ₚ : (P : 𝐓.Proc m) {ρ : m →ᵣ m′} {σ : m′ →ₛ n} → U[ P 𝐓.⋯ₚ ρ ] σ ≡ U[ P ] (ρ ·ₖ σ)
U-⋯ₚ 𝐓.⟪ e ⟫ {ρ} {σ} = cong 𝐔.⟪_⟫ (fusion e ρ σ)
U-⋯ₚ (P 𝐓.∥ Q)       = cong₂ 𝐔._∥_ (U-⋯ₚ P) (U-⋯ₚ Q)
U-⋯ₚ (𝐓.ν B₁ B₂ P) {ρ} {σ} =
  cong 𝐔.ν (UB-cong-≡ B₁ _ (λ τ₁ → UB-cong-≡ B₂ _ (λ τ₂ →
    U-⋯ₚ P ■ U-cong P (dist-↑*-++ₛ (sum B₁ + sum B₂) {ρ = ρ}
      {A = (λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂}
      {C = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)}))))

mapᶜ : (n →ᵣ n′) → UChan n → UChan n′
mapᶜ θ (e₁ , x , e₂) = (e₁ ⋯ θ , θ x , e₂ ⋯ θ)

mapᶜ-cong : {ρ₁ ρ₂ : n →ᵣ n′} → ρ₁ ≗ ρ₂ → (cc : UChan n) → mapᶜ ρ₁ cc ≡ mapᶜ ρ₂ cc
mapᶜ-cong eq (e₁ , x , e₂) = cong₂ _,_ (⋯-cong e₁ eq) (cong₂ _,_ (eq x) (⋯-cong e₂ eq))

mapᶜ-fusion : ∀ {n‴} (ρ₁ : n →ᵣ n′) (ρ₂ : n′ →ᵣ n‴) (cc : UChan n) →
              mapᶜ ρ₂ (mapᶜ ρ₁ cc) ≡ mapᶜ (ρ₁ ·ₖ ρ₂) cc
mapᶜ-fusion ρ₁ ρ₂ (e₁ , x , e₂) =
  cong₂ _,_ (fusion e₁ ρ₁ ρ₂) (cong₂ _,_ refl (fusion e₂ ρ₁ ρ₂))

-- Substitution concatenation commutes with composition (pointwise).

liftCast : ∀ {n n′} (m : ℕ) (θ : n →ᵣ n′) →
           subst₂ _→ᵣ_ (+-suc m n) (+-suc m n′) ((θ ↑) ↑* m) ≡ (θ ↑* m) ↑
liftCast zero    θ = refl
liftCast (suc k) θ = subst₂-↑ (+-suc k _) (+-suc k _) ((θ ↑) ↑* k) ■ cong _↑ (liftCast k θ)

-- A lifted renaming acts on a weakened variable by renaming underneath.

varΘ : ∀ {a b} sB (ψ : a →ᵣ b) (y : 𝔽 a) →
       (ψ ↑* sB) (weaken* ⦃ Kᵣ ⦄ sB y) ≡ weaken* ⦃ Kᵣ ⦄ sB (ψ y)
varΘ sB ψ y =
  cong (ψ ↑* sB) (weaken*~↑ʳ ⦃ Kᵣ ⦄ sB y)
  ■ ↑*∼id/wk-splitAt ψ sB (sB ↑ʳ y)
  ■ cong [ id/` ⦃ Kᵣ ⦄ ∘ (_↑ˡ _) , ψ ·ₖ weaken* ⦃ Kᵣ ⦄ sB ] (splitAt-↑ʳ sB _ y)

-- Renaming naturality of the (binder-free) sequencing chain.

Ub-nat : (b : ℕ) (cc : UChan m) (θ : m →ᵣ m′)
         {f : (b →ₛ m) → 𝐔.Proc m} {f′ : (b →ₛ m′) → 𝐔.Proc m′} →
         (∀ τ → f τ 𝐔.⋯ₚ θ ≡ f′ (λ i → τ i ⋯ θ)) →
         Ub[ b ] cc f 𝐔.⋯ₚ θ ≡ Ub[ b ] (mapᶜ θ cc) f′
Ub-nat zero cc θ {f} {f′} h = h (λ ()) ■ cong f′ (funext (λ ()))
Ub-nat (suc zero) (e₁ , x , e₂) θ {f} {f′} h =
  h (((e₁ ⊗ (` x)) ⊗ e₂) ∷ₛ λ ()) ■ cong f′ (funext (λ { zero → refl ; (suc ()) }))
Ub-nat (suc (suc b)) (e₁ , x , e₂) θ {f} {f′} h =
  Ub-nat (suc b) (K `unit , x , e₂) θ
    (λ σ → h (((e₁ ⊗ (` x)) ⊗ K `unit) ∷ₛ σ) ■ cong f′ (funext (λ { zero → refl ; (suc i) → refl })))

-- Renaming naturality of the φ-nest.

UB-nat : (B : 𝐓.BindGroup) (cc : UChan n) (θ : n →ᵣ n′)
         {f : (sum B →ₛ syncs B + n) → 𝐔.Proc (syncs B + n)}
         {f′ : (sum B →ₛ syncs B + n′) → 𝐔.Proc (syncs B + n′)} →
         (∀ τ → f τ 𝐔.⋯ₚ (θ ↑* syncs B) ≡ f′ (λ i → τ i ⋯ (θ ↑* syncs B))) →
         UB[ B ] cc f 𝐔.⋯ₚ θ ≡ UB[ B ] (mapᶜ θ cc) f′
UB-nat [] cc θ {f} {f′} h = h (λ ()) ■ cong f′ (funext (λ ()))
UB-nat (c ∷ []) cc θ {f} {f′} h =
  Ub-nat c cc θ (λ σh → h (σh ++ₛ λ ())
    ■ cong f′ (funext (++ₛ-⋯ σh (λ ()) θ) ■ cong ((λ j → σh j ⋯ θ) ++ₛ_) (funext (λ ()))))
UB-nat {n} {n′} (c ∷ B@(_ ∷ _)) (e₁ , x , e₂) θ {f} {f′} h =
  cong 𝐔.φ (cong₂ 𝐔._∥_ refl
    (UB-nat B (` 0F , suc x , e₂ ⋯ weakenᵣ) (θ ↑) {f′ = g′}
       (λ σt →
          Ub-nat c _ Θ {f′ = cg′ (λ i → σt i ⋯ Θ)}
            (λ σh →
                subst-⋯ₚ-dom (+-suc sB n) (f (Y σt σh)) Θ
              ■ cong (f (Y σt σh) 𝐔.⋯ₚ_) Θ⁺eq
              ■ subst-⋯ₚ-cod (sym (+-suc sB n′)) (f (Y σt σh)) (θ ↑* suc sB)
              ■ cong (subst 𝐔.Proc (sym (+-suc sB n′))) (h (Y σt σh) ■ cong f′ (Yeq σt σh)))
          ■ cong (λ cc → Ub[ c ] cc (cg′ (λ i → σt i ⋯ Θ))) ccIEq)
     ■ cong (λ cc → UB[ B ] cc g′) ccEq))
  where
    sB = syncs B
    Θ : (sB + suc n) →ᵣ (sB + suc n′)
    Θ = (θ ↑) ↑* sB
    θ⁻ : (sB + suc n) →ᵣ suc (sB + n′)
    θ⁻ = subst (λ z → z →ᵣ suc (sB + n′)) (sym (+-suc sB n)) (θ ↑* suc sB)
    cg′ : (sum B →ₛ sB + suc n′) → (c →ₛ sB + suc n′) → 𝐔.Proc (sB + suc n′)
    cg′ τ σh = subst 𝐔.Proc (sym (+-suc sB n′)) (f′ (subst (sum (c ∷ B) →ₛ_) (+-suc sB n′) (σh ++ₛ τ)))
    g′ : (sum B →ₛ sB + suc n′) → 𝐔.Proc (sB + suc n′)
    g′ τ = Ub[ c ] ((e₁ ⋯ θ) ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc (θ x)) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) (cg′ τ)
    Y : (sum B →ₛ sB + suc n) → (c →ₛ sB + suc n) → (sum (c ∷ B) →ₛ suc (sB + n))
    Y σt σh = subst (sum (c ∷ B) →ₛ_) (+-suc sB n) (σh ++ₛ σt)
    Θ⁺eq : subst (λ z → z →ᵣ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ᵣ z) (sym (+-suc sB n′)) (θ ↑* suc sB)
    Θ⁺eq = subst-flip (+-suc sB n′) (sym (subst₂→ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCast sB θ)
    ccEq : mapᶜ (θ ↑) (` 0F , suc x , e₂ ⋯ weakenᵣ) ≡ (` 0F , suc (θ x) , (e₂ ⋯ θ) ⋯ weakenᵣ)
    ccEq = cong₂ _,_ refl (cong₂ _,_ refl (sym (⋯-↑-wk e₂ θ)))
    ccIEq : mapᶜ Θ (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc x) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
            ≡ ((e₁ ⋯ θ) ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB , weaken* ⦃ Kᵣ ⦄ sB (suc (θ x)) , (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    ccIEq = cong₂ _,_ (sym (⋯-↑*-wk (e₁ ⋯ weakenᵣ) (θ ↑) sB) ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (⋯-↑-wk e₁ θ)))
                      (cong₂ _,_ (varΘ sB (θ ↑) (suc x)) (cong `_ (varΘ sB (θ ↑) 0F)))
    ΘθEq : Θ ≡ subst (λ z → (sB + suc n) →ᵣ z) (sym (+-suc sB n′)) θ⁻
    ΘθEq = sym ( sym (subst₂→ (sym (+-suc sB n)) (sym (+-suc sB n′)) (θ ↑* suc sB))
               ■ cong (subst₂ _→ᵣ_ (sym (+-suc sB n)) (sym (+-suc sB n′))) (sym (liftCast sB θ))
               ■ subst₂-cancel (+-suc sB n) (+-suc sB n′) Θ )
    ΘrelEq : (t : Tm (sB + suc n)) → t ⋯ θ⁻ ≡ subst Tm (+-suc sB n′) (t ⋯ Θ)
    ΘrelEq t = sym ( cong (λ r → subst Tm (+-suc sB n′) (t ⋯ r)) ΘθEq
                   ■ cong (subst Tm (+-suc sB n′)) (subst-⋯-cod (sym (+-suc sB n′)) t θ⁻)
                   ■ subst-subst-sym′ (+-suc sB n′) )
    Yeq : ∀ σt σh → (λ i → Y σt σh i ⋯ (θ ↑* suc sB))
                    ≡ subst (sum (c ∷ B) →ₛ_) (+-suc sB n′) ((λ i → σh i ⋯ Θ) ++ₛ (λ i → σt i ⋯ Θ))
    Yeq σt σh = funext (λ i →
        cong (_⋯ (θ ↑* suc sB)) (subst-Π (+-suc sB n) (σh ++ₛ σt) i)
      ■ subst-⋯ (+-suc sB n) ((σh ++ₛ σt) i) (θ ↑* suc sB)
      ■ ΘrelEq ((σh ++ₛ σt) i)
      ■ cong (subst Tm (+-suc sB n′)) (++ₛ-⋯ σh σt Θ i)
      ■ sym (subst-Π (+-suc sB n′) ((λ j → σh j ⋯ Θ) ++ₛ (λ j → σt j ⋯ Θ)) i))

-- The translation commutes with renaming of its target (output).

U-σ⋯ : (P : 𝐓.Proc m) {σ : m →ₛ n} {ρ : n →ᵣ n′} → U[ P ] σ 𝐔.⋯ₚ ρ ≡ U[ P ] (σ ·ₖ ρ)
U-σ⋯ 𝐓.⟪ e ⟫ {σ} {ρ} = cong 𝐔.⟪_⟫ (fusion e σ ρ)
U-σ⋯ (P 𝐓.∥ Q)       = cong₂ 𝐔._∥_ (U-σ⋯ P) (U-σ⋯ Q)
U-σ⋯ {n = n} {n′ = n′} (𝐓.ν B₁ B₂ P) {σ} {ρ} =
  cong 𝐔.ν
    (UB-nat B₁ (K `unit , 0F , K `unit) (ρ ↑* 2) {f′ = f₁′}
       (λ τ₁ →
          UB-nat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) Ξ₁ {f′ = f₂′ (λ i → τ₁ i ⋯ Ξ₁)}
            (λ τ₂ → U-σ⋯ P ■ U-cong P (outdist τ₁ τ₂))
          ■ cong (λ cc → UB[ B₂ ] cc (f₂′ (λ i → τ₁ i ⋯ Ξ₁))) cc₂Eq)
     ■ cong (λ cc → UB[ B₁ ] cc f₁′) refl)
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Ξ₁ : (sB₁ + (2 + n)) →ᵣ (sB₁ + (2 + n′))
    Ξ₁ = (ρ ↑* 2) ↑* sB₁
    Ξ₂ : (sB₂ + (sB₁ + (2 + n))) →ᵣ (sB₂ + (sB₁ + (2 + n′)))
    Ξ₂ = Ξ₁ ↑* sB₂
    f₂′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → (sum B₂ →ₛ sB₂ + (sB₁ + (2 + n′))) → 𝐔.Proc (sB₂ + (sB₁ + (2 + n′)))
    f₂′ σ₁ σ₂ = U[ P ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ σ₂)
                       ++ₛ (λ i → (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    f₁′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → 𝐔.Proc (sB₁ + (2 + n′))
    f₁′ σ₁ = UB[ B₂ ] (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) (f₂′ σ₁)
    cc₂Eq : mapᶜ Ξ₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit)
    cc₂Eq = cong₂ _,_ refl (cong₂ _,_ (varΘ sB₁ (ρ ↑* 2) 1F) refl)
    outdist : ∀ (τ₁ : sum B₁ →ₛ sB₁ + (2 + n)) (τ₂ : sum B₂ →ₛ sB₂ + (sB₁ + (2 + n))) →
              (((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
                ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)) ·ₖ Ξ₂
              ≗ ((λ i → (λ j → τ₁ j ⋯ Ξ₁) i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂))
                ++ₛ (λ i → (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    outdist τ₁ τ₂ j =
        ++ₛ-⋯ ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
              (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) Ξ₂ j
      ■ [,]-cong compA compB (splitAt (sum B₁ + sum B₂) j)
      where
        compA : ∀ i → ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂) i ⋯ Ξ₂
                      ≡ ((λ i → (τ₁ i ⋯ Ξ₁) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂)) i
        compA i = ++ₛ-⋯ (λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) τ₂ Ξ₂ i
                ■ [,]-cong (λ j → sym (⋯-↑*-wk (τ₁ j) Ξ₁ sB₂)) (λ j → refl) (splitAt (sum B₁) i)
        compB : ∀ i → (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ Ξ₂
                      ≡ (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        compB i = sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) Ξ₁ sB₂)
                ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2) sB₁))
                ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i) ρ 2))

-- Renaming by the identity is identity.
