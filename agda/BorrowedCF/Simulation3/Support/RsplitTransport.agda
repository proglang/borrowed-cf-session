module BorrowedCF.Simulation3.Support.RsplitTransport where

-- | Portable (canonₛ-independent) transport plumbing for the forward R-RSplit
--   case.  These abstract subst / renaming coherence lemmas are used by the
--   rwk-transport proofs (canonₛ-rwk, leafσ-rwk-id, and the leafRec hole fills)
--   that live in Simulation2.Theorems.Splits (which must reference that module's
--   local canonₛ / leafσ, so the canonₛ-dependent parts cannot move here).

open import BorrowedCF.Simulation3.Support.Base
import BorrowedCF.Processes.Untyped as U

-- ⋯ with a subst₂-coerced renaming: casting the domain of the term and the
-- renaming by the SAME equality lets the two casts fuse into a codomain cast.
⋯-subst₂ : ∀ {A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) (t : Tm A) (ρ : A →ᵣ B) →
           subst Tm p t ⋯ subst₂ _→ᵣ_ p q ρ ≡ subst Tm q (t ⋯ ρ)
⋯-subst₂ refl refl t ρ = refl

-- ⋯ₚ analogue.
⋯ₚ-subst₂ : ∀ {A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) (X : U.Proc A) (ρ : A →ᵣ B) →
            subst U.Proc p X U.⋯ₚ subst₂ _→ᵣ_ p q ρ ≡ subst U.Proc q (X U.⋯ₚ ρ)
⋯ₚ-subst₂ refl refl X ρ = refl

-- recast the subst on a term along a proof-irrelevant scope equality.
subst-Tm-uip : ∀ {A A′} (p q : A ≡ A′) (t : Tm A) → subst Tm p t ≡ subst Tm q t
subst-Tm-uip refl refl t = refl

-- toℕ is stable under a codomain-cast of a renaming.
toℕ-subst-cod : ∀ {A B B′} (e : B ≡ B′) (f : A →ᵣ B) (y : 𝔽 A) →
                Fin.toℕ (subst (λ z → A →ᵣ z) e f y) ≡ Fin.toℕ (f y)
toℕ-subst-cod refl f y = refl

-- toℕ of a subst₂-coerced renaming factors through the domain-cast of the index.
toℕ-subst₂ᵣ : ∀ {A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) (ρ : A →ᵣ B) (j : 𝔽 A′) →
              Fin.toℕ (subst₂ _→ᵣ_ p q ρ j) ≡ Fin.toℕ (ρ (subst 𝔽 (sym p) j))
toℕ-subst₂ᵣ refl refl ρ j = refl

toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
toℕ-subst𝔽 refl y = refl
