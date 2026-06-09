{-# OPTIONS --rewriting #-}

module BorrowedCF.Simulation.SubstLemmas where

-- | Generic transport/coercion plumbing: subst commutes with (process) renaming,
--   ++ₛ / ∷ₛ congruences, subst over ∥ and φ, renaming-identity, and ≡→≋.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*

≋-subst : {a b : ℕ} (eq : a ≡ b) {x y : 𝐔.Proc a} → x 𝐔.≋ y → subst 𝐔.Proc eq x 𝐔.≋ subst 𝐔.Proc eq y
≋-subst refl xy = xy

++ₛ-congʳ : ∀ {a b N} (σ₁ : a →ₛ N) {σ₂ σ₂′ : b →ₛ N} → σ₂ ≗ σ₂′ → σ₁ ++ₛ σ₂ ≗ σ₁ ++ₛ σ₂′
++ₛ-congʳ {a} σ₁ eq i = [,]-cong (λ _ → refl) eq (splitAt a i)

-- The translation only depends on its substitution pointwise.

++ₛ-⋯ : ∀ {a b N N′} (σ₁ : a →ₛ N) (σ₂ : b →ₛ N) (θ : N →ᵣ N′) i →
        (σ₁ ++ₛ σ₂) i ⋯ θ ≡ ((λ j → σ₁ j ⋯ θ) ++ₛ (λ j → σ₂ j ⋯ θ)) i
++ₛ-⋯ {a} σ₁ σ₂ θ i = helper (splitAt a i)
  where
    helper : (s : 𝔽 a ⊎ 𝔽 _) →
             [ σ₁ , σ₂ ]′ s ⋯ θ ≡ [ (λ j → σ₁ j ⋯ θ) , (λ j → σ₂ j ⋯ θ) ]′ s
    helper (inj₁ j) = refl
    helper (inj₂ j) = refl

-- Renaming commutes past a scope-coercion of the process.

subst-⋯ₚ′ : ∀ {a b c} (p : a ≡ b) (Q : 𝐔.Proc a) (θ : b →ᵣ c) →
            subst 𝐔.Proc p Q 𝐔.⋯ₚ θ ≡ Q 𝐔.⋯ₚ subst (λ z → z →ᵣ c) (sym p) θ
subst-⋯ₚ′ refl Q θ = refl

subst-⋯ₚ-cod : ∀ {a c d} (q : c ≡ d) (Q : 𝐔.Proc a) (θ : a →ᵣ c) →
               Q 𝐔.⋯ₚ subst (λ z → a →ᵣ z) q θ ≡ subst 𝐔.Proc q (Q 𝐔.⋯ₚ θ)
subst-⋯ₚ-cod refl Q θ = refl

subst-⋯ : ∀ {a b c} (p : a ≡ b) (t : Tm a) (θ : b →ᵣ c) →
          subst Tm p t ⋯ θ ≡ t ⋯ subst (λ z → z →ᵣ c) (sym p) θ
subst-⋯ refl t θ = refl

subst-⋯-cod : ∀ {a c d} (q : c ≡ d) (t : Tm a) (θ : a →ᵣ c) →
              t ⋯ subst (λ z → a →ᵣ z) q θ ≡ subst Tm q (t ⋯ θ)
subst-⋯-cod refl t θ = refl

subst-Π : ∀ {D a b} (p : a ≡ b) (s : 𝔽 D → Tm a) (i : 𝔽 D) →
          subst (λ z → 𝔽 D → Tm z) p s i ≡ subst Tm p (s i)
subst-Π refl s i = refl

subst₂-↑ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (ρ : a →ᵣ b) →
           subst₂ _→ᵣ_ (cong suc p) (cong suc q) (ρ ↑) ≡ (subst₂ _→ᵣ_ p q ρ) ↑
subst₂-↑ refl refl ρ = refl

subst-⋯ₚ-dom : ∀ {a b c} (p : a ≡ b) (Q : 𝐔.Proc b) (θ : a →ᵣ c) →
               subst 𝐔.Proc (sym p) Q 𝐔.⋯ₚ θ ≡ Q 𝐔.⋯ₚ subst (λ z → z →ᵣ c) p θ
subst-⋯ₚ-dom refl Q θ = refl

subst₂→ : ∀ {a b c d} (p : a ≡ b) (q : c ≡ d) (ρ : a →ᵣ c) →
          subst₂ _→ᵣ_ p q ρ ≡ subst (λ z → b →ᵣ z) q (subst (λ z → z →ᵣ c) p ρ)
subst₂→ refl refl ρ = refl

subst₂-cancel : ∀ {a b c d} (p : a ≡ b) (q : c ≡ d) (ρ : a →ᵣ c) →
                subst₂ _→ᵣ_ (sym p) (sym q) (subst₂ _→ᵣ_ p q ρ) ≡ ρ
subst₂-cancel refl refl ρ = refl

subst-flip : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {a : F x} {b : F y} →
             subst F q a ≡ b → a ≡ subst F (sym q) b
subst-flip refl eq = eq

subst-subst-sym′ : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {b : F y} →
                   subst F q (subst F (sym q) b) ≡ b
subst-subst-sym′ refl = refl

-- Lifting once then m times equals lifting m+1 times, modulo the +-suc coercion.

⋯ₚ-id : (P : 𝐔.Proc m) {ρ : m →ᵣ m} → ρ ≗ idₖ → P 𝐔.⋯ₚ ρ ≡ P
⋯ₚ-id 𝐔.⟪ e ⟫   eq = cong 𝐔.⟪_⟫ (⋯-id e eq)
⋯ₚ-id (P 𝐔.∥ Q) eq = cong₂ 𝐔._∥_ (⋯ₚ-id P eq) (⋯ₚ-id Q eq)
⋯ₚ-id (𝐔.ν P)   eq = cong 𝐔.ν (⋯ₚ-id P (id↑* 2 eq))
⋯ₚ-id (𝐔.φ P)   eq = cong 𝐔.φ (⋯ₚ-id P (id↑ eq))
⋯ₚ-id (x 𝐔.↦ ϕ) eq = cong (𝐔._↦ ϕ) (eq x)

-- Propositional equality embeds into structural congruence.

≡→≋ : {P Q : 𝐔.Proc n} → P ≡ Q → P 𝐔.≋ Q
≡→≋ refl = ε

-- Renaming-free sequencing chain distributes over a left parallel component.

subst-∥ : {a b : ℕ} (eq : a ≡ b) (A B : 𝐔.Proc a) →
          subst 𝐔.Proc eq (A 𝐔.∥ B) ≡ subst 𝐔.Proc eq A 𝐔.∥ subst 𝐔.Proc eq B
subst-∥ refl A B = refl

substFinSuc : ∀ {a b} (p : a ≡ b) (y : 𝔽 a) → subst 𝔽 (cong suc p) (suc y) ≡ suc (subst 𝔽 p y)
substFinSuc refl y = refl

↑ʳ-suc : ∀ k {nn} (x : 𝔽 nn) → subst 𝔽 (+-suc k nn) (k ↑ʳ suc x) ≡ suc (k ↑ʳ x)
↑ʳ-suc zero    x = refl
↑ʳ-suc (suc j) x = substFinSuc (+-suc j _) (j ↑ʳ suc x) ■ cong suc (↑ʳ-suc j x)

subst-ren-cod : ∀ {a c d} (q : c ≡ d) (ρ : a →ᵣ c) (x : 𝔽 a) →
                subst (λ z → a →ᵣ z) q ρ x ≡ subst 𝔽 q (ρ x)
subst-ren-cod refl ρ x = refl

-- Weakening by 1 then by k equals weakening by suc k (modulo the +-suc coercion).

subst-φ-commute : ∀ {a b} (eq : a ≡ b) (X : 𝐔.Proc (suc a)) →
                  subst 𝐔.Proc eq (𝐔.φ X) ≡ 𝐔.φ (subst 𝐔.Proc (cong suc eq) X)
subst-φ-commute refl X = refl

-- ⋯ distributes over the substitution-cons.

∷ₛ-⋯ : ∀ {l n n′} (t : Tm n) (τ : l →ₛ n) (θ : n →ᵣ n′) →
       (λ i → (t ∷ₛ τ) i ⋯ θ) ≗ ((t ⋯ θ) ∷ₛ (λ j → τ j ⋯ θ))
∷ₛ-⋯ t τ θ Fin.zero    = refl
∷ₛ-⋯ t τ θ (Fin.suc i) = refl

-- A φ in the leaf of a Ub-chain commutes out past the (binder-free) chain.

𝐓⋯ₚ-id : (P : 𝐓.Proc m) {ρ : m →ᵣ m} → ρ ≗ idₖ → P 𝐓.⋯ₚ ρ ≡ P
𝐓⋯ₚ-id 𝐓.⟪ e ⟫       eq = cong 𝐓.⟪_⟫ (⋯-id e eq)
𝐓⋯ₚ-id (P 𝐓.∥ Q)     eq = cong₂ 𝐓._∥_ (𝐓⋯ₚ-id P eq) (𝐓⋯ₚ-id Q eq)
𝐓⋯ₚ-id (𝐓.ν B₁ B₂ P) eq = cong (𝐓.ν B₁ B₂) (𝐓⋯ₚ-id P (id↑* _ eq))

subst-≋ : ∀ {a b} (eq : a ≡ b) {A B : 𝐔.Proc a} → A 𝐔.≋ B →
          subst 𝐔.Proc eq A 𝐔.≋ subst 𝐔.Proc eq B
subst-≋ refl pf = pf
