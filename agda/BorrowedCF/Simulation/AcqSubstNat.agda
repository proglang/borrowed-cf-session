module BorrowedCF.Simulation.AcqSubstNat where

-- | Kit-polymorphic subst-bookkeeping lemmas needed to push an *output
--   substitution* through the φ-nest translation blocks.  TranslationProperties
--   provides these only for the renaming Kit (`_→ᵣ_`); here they are stated over
--   an arbitrary Kit so that they cover substitutions as well (the proofs are
--   the same `refl`-after-`refl` bookkeeping, only the map type changes).
--
--   Used by Theorems/Acq.agda's `Bφ-⋯ₛ` (the substitution sibling of `Bφ-⋯`),
--   which is the engine for the ν case of `U-σ⋯ₛ`.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Untyped as U

-- subst over a Kit-map commutes through a single ↑.
subst₂-↑ₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a a′ b b′ : ℕ}
            (p : a ≡ a′) (q : b ≡ b′) (ϕ : a –[ K ]→ b) →
            subst₂ (λ x y → x –[ K ]→ y) (cong suc p) (cong suc q) (ϕ ↑)
            ≡ (subst₂ (λ x y → x –[ K ]→ y) p q ϕ) ↑
subst₂-↑ₖ refl refl ϕ = refl

-- subst₂ over a Kit-map factors into two nested single substs.
subst₂→ₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a b c d : ℕ}
           (p : a ≡ b) (q : c ≡ d) (ϕ : a –[ K ]→ c) →
           subst₂ (λ x y → x –[ K ]→ y) p q ϕ
           ≡ subst (λ z → b –[ K ]→ z) q (subst (λ z → z –[ K ]→ c) p ϕ)
subst₂→ₖ refl refl ϕ = refl

-- codomain-subst on the map pulls out to a subst on the traversed process.
subst-⋯ₚ-codₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a c d : ℕ}
                (q : c ≡ d) (Q : U.Proc a) (ϕ : a –[ K ]→ c) →
                Q U.⋯ₚ subst (λ z → a –[ K ]→ z) q ϕ ≡ subst U.Proc q (Q U.⋯ₚ ϕ)
subst-⋯ₚ-codₖ refl Q ϕ = refl

-- domain-subst on the process pulls into a subst on the map.
subst-⋯ₚ-domₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a b c : ℕ}
                (p : a ≡ b) (Q : U.Proc b) (ϕ : a –[ K ]→ c) →
                subst U.Proc (sym p) Q U.⋯ₚ ϕ ≡ Q U.⋯ₚ subst (λ z → z –[ K ]→ c) p ϕ
subst-⋯ₚ-domₖ refl Q ϕ = refl

-- lifting a Kit-map past m inert binders commutes with the +-suc reassociation.
liftCastₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ (m : ℕ) {n n′ : ℕ} (ϕ : n –[ K ]→ n′) →
            subst₂ (λ x y → x –[ K ]→ y) (+-suc m n) (+-suc m n′) ((ϕ ↑) ↑* m)
            ≡ (ϕ ↑* m) ↑
liftCastₖ zero    ϕ = refl
liftCastₖ (suc k) ϕ = subst₂-↑ₖ (+-suc k _) (+-suc k _) ((ϕ ↑) ↑* k) ■ cong _↑ (liftCastₖ k ϕ)

-- subst-flip specialised (matches TranslationProperties.subst-flip).
subst-flipₖ : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {u : F x} {v : F y} →
              subst F q u ≡ v → u ≡ subst F (sym q) v
subst-flipₖ refl eq = eq

-- Tm-level: domain-subst on the map (Kit-polymorphic sibling of subst-⋯).
subst-⋯ᵏ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a b c : ℕ}
           (p : a ≡ b) (t : Tm a) (ϕ : b –[ K ]→ c) →
           subst Tm p t ⋯ ϕ ≡ t ⋯ subst (λ z → z –[ K ]→ c) (sym p) ϕ
subst-⋯ᵏ refl t ϕ = refl

-- Tm-level: codomain-subst on the map (Kit-polymorphic sibling of subst-⋯-cod).
subst-⋯-codᵏ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a c d : ℕ}
               (q : c ≡ d) (t : Tm a) (ϕ : a –[ K ]→ c) →
               t ⋯ subst (λ z → a –[ K ]→ z) q ϕ ≡ subst Tm q (t ⋯ ϕ)
subst-⋯-codᵏ refl t ϕ = refl

-- subst₂ on a Kit-map is undone by the reversed subst₂.
subst₂-cancelₖ : ∀ {𝓖 : Scoped} ⦃ K : Kit 𝓖 ⦄ {a b c d : ℕ}
                 (p : a ≡ b) (q : c ≡ d) (ϕ : a –[ K ]→ c) →
                 subst₂ (λ x y → x –[ K ]→ y) (sym p) (sym q) (subst₂ (λ x y → x –[ K ]→ y) p q ϕ) ≡ ϕ
subst₂-cancelₖ refl refl ϕ = refl

-- subst-subst-sym for Tm (a subst followed by its symmetric one is identity).
subst-subst-symᵏ : ∀ {a b} (p : a ≡ b) {t : Tm b} →
                   subst Tm p (subst Tm (sym p) t) ≡ t
subst-subst-symᵏ refl = refl

-- A substitution that fixes a variable y (τ y ≡ ` y′) still fixes it — as a
-- variable — after being lifted past m inert binders and applied to the
-- weakened index.  This is the substitution analogue of `varΘ` for the case
-- where the flag sits in the lifted-identity region.
varΘ-fixₛ : (m : ℕ) {a b : ℕ} (τ : a →ₛ b) (y : 𝔽 a) (y′ : 𝔽 b) →
            τ y ≡ ` y′ →
            (τ ↑* m) (weaken* ⦃ Kᵣ ⦄ m y) ≡ ` (weaken* ⦃ Kᵣ ⦄ m y′)
varΘ-fixₛ zero    τ y y′ fy = fy
varΘ-fixₛ (suc m) τ y y′ fy =
    cong (_⋯ weakenᵣ) (varΘ-fixₛ m τ y y′ fy)
  ■ ⋯-var (weaken* ⦃ Kᵣ ⦄ m y′) weakenᵣ
