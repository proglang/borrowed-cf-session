-- | φ-telescope inversion for the telescoped backward channel-op reflections.
--
--   A telescoped RU-Com / RU-Choice / … redex is presented as
--     ν (plugΦ Φ leaf)
--   for an ARBITRARY φ-telescope Φ, with `leaf` a ∥-headed com/choice shape.
--   To reflect it we must recover, from the well-typedness of the source P,
--   that Φ is EXACTLY the bind-group telescope `Btel B₁ ++Φ Btel B₂` that U[_]
--   builds, and that the leaf is the U[_]-image of the source body P₀.
--
--   The engine is `plugΦ-inj-nonφ`: two φ-telescopes plugging NON-φ-headed
--   leaves that agree structurally must have equal width, hence equal codomain
--   scope, equal telescope, and equal leaf.  It is provable — and ONLY provable
--   this cleanly — because every U[_]-image is non-φ-headed (U[_] heads with
--   ⟪⟫ / ∥ / ν, never φ): the φ-nest of an image is EXACTLY its Btel prefix.
module BorrowedCF.Simulation.Backward.PhiInj where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; []φ; _◂_; plugΦ; wkΦ)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)

open UP using (Proc; ⟪_⟫; _∥_; ν; φ)

------------------------------------------------------------------------
-- Non-φ-headedness — the head constructor is one of ⟪⟫ / ∥ / ν.
------------------------------------------------------------------------

data NotΦ {n} : Proc n → Set where
  nΦ-⟪⟫ : ∀ {e}   → NotΦ ⟪ e ⟫
  nΦ-∥  : ∀ {P Q} → NotΦ (P ∥ Q)
  nΦ-ν  : ∀ {P}   → NotΦ (ν P)

-- Every translation image is non-φ-headed.
U-notΦ : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) → NotΦ (U[ P ] σ)
U-notΦ (TP.⟪ e ⟫)    σ = nΦ-⟪⟫
U-notΦ (P TP.∥ Q)    σ = nΦ-∥
U-notΦ (TP.ν B₁ B₂ P) σ = nΦ-ν

------------------------------------------------------------------------
-- φ-injectivity.
------------------------------------------------------------------------

φ-inj : ∀ {n} {f f′ : UP.Flag} {c c′ : Tm n} {b b′ : Proc (1 + n)}
      → φ f c b ≡ φ f′ c′ b′ → (f ≡ f′) × (c ≡ c′) × (b ≡ b′)
φ-inj refl = refl , refl , refl

------------------------------------------------------------------------
-- The inversion.  Two telescopes plugging non-φ-headed leaves that agree
-- have equal width (⇒ equal codomain scope), equal telescope, equal leaf.
------------------------------------------------------------------------

plugΦ-inj-nonφ : ∀ {a k k′} (Φ : Φ* a k) (Ψ : Φ* a k′)
                 {X : Proc k} {Y : Proc k′}
               → NotΦ X → NotΦ Y
               → plugΦ Φ X ≡ plugΦ Ψ Y
               → Σ[ eq ∈ k ≡ k′ ] (subst (Φ* a) eq Φ ≡ Ψ) × (subst Proc eq X ≡ Y)
plugΦ-inj-nonφ []φ      []φ      nX nY heq = refl , refl , heq
plugΦ-inj-nonφ []φ      (gc ◂ Ψ) nΦ-⟪⟫ nY ()
plugΦ-inj-nonφ []φ      (gc ◂ Ψ) nΦ-∥  nY ()
plugΦ-inj-nonφ []φ      (gc ◂ Ψ) nΦ-ν  nY ()
plugΦ-inj-nonφ (fc ◂ Φ) []φ      nX nΦ-⟪⟫ ()
plugΦ-inj-nonφ (fc ◂ Φ) []φ      nX nΦ-∥  ()
plugΦ-inj-nonφ (fc ◂ Φ) []φ      nX nΦ-ν  ()
plugΦ-inj-nonφ (fc ◂ Φ) (gc ◂ Ψ) nX nY heq
  with feq , ceq , beq ← φ-inj heq
  with refl , Φeq , Xeq ← plugΦ-inj-nonφ Φ Ψ nX nY beq =
  refl , cong₂ _◂_ (cong₂ _,_ feq ceq) Φeq , Xeq
