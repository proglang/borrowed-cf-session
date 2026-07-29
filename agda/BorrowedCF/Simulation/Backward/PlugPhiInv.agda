-- | φ-telescope injectivity for the backward channel-op reflections.
--
--   The telescoped RU-* rules fire under an arbitrary φ-nest `plugΦ Φ leaf`.
--   To reflect one back, we flatten the image `U[ ν B₁ B₂ P₀ ] σ` (via `Uν-flatΦ`)
--   to `ν (plugΦ (Btel B₁ ++Φ Btel B₂) (U[ P₀ ] leafσ))` and MATCH it against the
--   redex `ν (plugΦ Φ redex-leaf)`.  Since neither leaf is φ-headed (`U[_]` never
--   heads with φ, and the redex leaf is a `∥`), the two φ-nests must have the same
--   width and be pointwise equal, exposing `redex-leaf ≡ U[ P₀ ] leafσ`.
module BorrowedCF.Simulation.Backward.PlugPhiInv where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
import BorrowedCF.Processes.Untyped as U
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; []φ; _◂_; plugΦ)

private
  φ-inj : ∀ {k} {f g : U.Flag} {c d : Tm k} {X Y : U.Proc (suc k)}
        → U.φ f c X ≡ U.φ g d Y → (f ≡ g) × (c ≡ d) × (X ≡ Y)
  φ-inj refl = refl , refl , refl

  subst-◂ : ∀ {a b c} (e : b ≡ c) (fc : U.Flag × Tm a) (Φ : Φ* (suc a) b) →
            subst (Φ* a) e (fc ◂ Φ) ≡ fc ◂ subst (Φ* (suc a)) e Φ
  subst-◂ refl fc Φ = refl

-- non-φ-headed predicate.
NonΦ : ∀ {n} → U.Proc n → Set
NonΦ {n} P = ∀ {f : U.Flag} {c : Tm n} {X : U.Proc (suc n)} → P ≢ U.φ f c X

-- φ-telescope injectivity for non-φ leaves.
plugΦ-inj : ∀ {a b c} (Φ : Φ* a b) (Ψ : Φ* a c) (A : U.Proc b) (B : U.Proc c)
          → NonΦ A → NonΦ B
          → plugΦ Φ A ≡ plugΦ Ψ B
          → Σ[ e ∈ b ≡ c ] ((subst (Φ* a) e Φ ≡ Ψ) × (subst U.Proc e A ≡ B))
plugΦ-inj []φ        []φ        A B nA nB eq = refl , refl , eq
plugΦ-inj []φ        (gd ◂ Ψ)   A B nA nB eq = ⊥-elim (nA eq)
plugΦ-inj (fc ◂ Φ)   []φ        A B nA nB eq = ⊥-elim (nB (sym eq))
plugΦ-inj {a} (fc ◂ Φ) (gd ◂ Ψ) A B nA nB eq
  with fe , ce , be ← φ-inj eq
  with e , Φe , Ae ← plugΦ-inj Φ Ψ A B nA nB be =
  e , (subst-◂ e fc Φ ■ cong₂ (λ p q → p ◂ q) fcgd Φe) , Ae
  where
    fcgd : fc ≡ gd
    fcgd = cong₂ _,_ fe ce
