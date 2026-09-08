-- | Duality is a congruence for session-type equivalence.
--
--   `Types.Syntax` defines `dual` and proves it involutive, and
--   `Types.Substitution` proves `dual-⋯ᵣ` (duality commutes with renaming),
--   but nothing in `Types.*` relates `dual` to `_;_`-free `_≃_`.  The
--   `R-Com` and `R-Choice` cases of process preservation need exactly that:
--   from `s ≃ msg ‼ T ; s*` one has to read off `dual s ≃ msg ⁇ T ; dual s*`.
module BorrowedCF.Safety.Preservation.Support.Dual where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Substitution as 𝐒 using (unfold; _⋯_; _→ₛ_; ⦅_⦆ₛ; _↑; ⋯-cong)

open Nat.Variables

-- | `dual` commutes with substitution, provided the substitution is dualised
--   pointwise.  The renaming case is `Types.Substitution.dual-⋯ᵣ`.
dual-↑ : (ϕ : m →ₛ n) → (dual ∘ ϕ) ↑ ≗ dual ∘ (ϕ ↑)
dual-↑ ϕ zero = refl
dual-↑ ϕ (suc x) = sym (𝐒.dual-⋯ᵣ (ϕ x))

dual-⋯ₛ : (s : 𝕊 m) (ϕ : m →ₛ n) → dual (s ⋯ ϕ) ≡ dual s ⋯ (dual ∘ ϕ)
dual-⋯ₛ (` x) ϕ = refl
dual-⋯ₛ (end p) ϕ = refl
dual-⋯ₛ (msg p t) ϕ = refl
dual-⋯ₛ (brn p s₁ s₂) ϕ = cong₂ (brn (dualPol p)) (dual-⋯ₛ s₁ ϕ) (dual-⋯ₛ s₂ ϕ)
dual-⋯ₛ (mu s) ϕ = cong mu (dual-⋯ₛ s (ϕ ↑) ■ ⋯-cong (dual s) (sym ∘ dual-↑ ϕ))
dual-⋯ₛ (s₁ ; s₂) ϕ = cong₂ _;_ (dual-⋯ₛ s₁ ϕ) (dual-⋯ₛ s₂ ϕ)
dual-⋯ₛ skip ϕ = refl
dual-⋯ₛ ret ϕ = refl
dual-⋯ₛ acq ϕ = refl
dual-⋯ₛ (`` α) ϕ = refl

-- | Unfolding a recursive session commutes with duality.
dual-unfold : (s : 𝕊 (suc n)) → dual (unfold s) ≡ unfold (dual s)
dual-unfold s = dual-⋯ₛ s ⦅ mu s ⦆ₛ ■ ⋯-cong (dual s) eq
  where
  eq : (dual ∘ ⦅ mu s ⦆ₛ) ≗ ⦅ mu (dual s) ⦆ₛ
  eq zero = refl
  eq (suc x) = refl

-- | The congruence itself.
≃-dual : s₁ ≃ s₂ → dual {n} s₁ ≃ dual s₂
≃-dual = go′
  where
  go : s₁ ≃𝕊 s₂ → dual {n} s₁ ≃ dual s₂
  go (≃𝕊-;₁ x) = ≃-; (go x) ≃-refl
  go (≃𝕊-;₂ x) = ≃-; ≃-refl (go x)
  go ≃𝕊-skipˡ = ≃-skipˡ
  go ≃𝕊-skipʳ = ≃-skipʳ
  go (≃𝕊-μ {s = s}) = subst (mu (dual s) ≃_) (sym (dual-unfold s)) ≃-μ
  go ≃𝕊-assoc = ≃-assoc-;
  go ≃𝕊-distr = ≃-distr
  go (≃𝕊-msg x) = Eq*.return (≃𝕊-msg x)
  go (≃𝕊-brn₁ x) = ≃-brn₁ (go x)
  go (≃𝕊-brn₂ x) = ≃-brn₂ (go x)

  go′ : s₁ ≃ s₂ → dual {n} s₁ ≃ dual s₂
  go′ refl = refl
  go′ (fwd x ◅ xs) = go x ◅◅ go′ xs
  go′ (bwd x ◅ xs) = ≃-sym (go x) ◅◅ go′ xs
