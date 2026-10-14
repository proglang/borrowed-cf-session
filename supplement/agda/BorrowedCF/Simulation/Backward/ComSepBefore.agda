module BorrowedCF.Simulation.Backward.ComSepBefore where

-- Multi-block ";-before" for a LATER same-block position.  Generalizes
-- RevGrindC.before-structBinder-front: the global front 0F is ;-before every
-- non-front position; here `fr` sits at the START of the B₂ region (global
-- offset sum B₁) and `x` at offset sum B₁ + q (q ≢ 0) — both landing in the
-- SAME first block of B₂ — and we conclude before fr x (structBinder (B₁ ++ B₂)).
--
-- Recurse on B₁: B₁ = [] bottoms out at before-structBinder-front B₂; each
-- head block b ∷ B₁' descends into the tail ;-component of structBinder via the
-- wkˡ b left-weakening (both fr,x are ≥ b, so they live entirely in the tail).

open import BorrowedCF.Prelude
open import BorrowedCF.Context.Base using (Struct; _∥_)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before; before-⋯ᵣ-inj)
open import BorrowedCF.Simulation.Support.RevGrindC
  using (before-structBinder-front; inj-wkˡ; inj-wkʳ)

open import Data.Sum using (inj₁; inj₂)

open Nat using (_+_; _<_; _≤_; +-assoc; +-cancelˡ-≡; <⇒≱; m≤m+n; ≤-trans)

before-structBinder-later : (B₁ B₂ : BindGroup) {q : ℕ} (fr x : 𝔽 (sum (B₁ ++ B₂)))
                          → Fin.toℕ fr ≡ sum B₁ → Fin.toℕ x ≡ sum B₁ + q → q ≢ 0
                          → before fr x (structBinder (B₁ ++ B₂))
before-structBinder-later [] B₂ {q} fr x tfr tx qne =
  before-structBinder-front B₂ fr x tfr (λ eq → qne (sym tx ■ eq))
before-structBinder-later (b ∷ B₁') B₂ {q} fr x tfr tx qne
  with Fin.splitAt b fr in eqfr | Fin.splitAt b x in eqx
... | inj₁ frl | _ =
      ⊥-elim (<⇒≱ (subst (_< b) tfr frl<b) (m≤m+n b (sum B₁')))
  where
    fr≡ : frl ↑ˡ sum (B₁' ++ B₂) ≡ fr
    fr≡ = splitAt⁻¹-↑ˡ eqfr
    frl<b : Fin.toℕ fr < b
    frl<b = subst (_< b) (cong Fin.toℕ fr≡)
              (subst (_< b) (sym (Fin.toℕ-↑ˡ frl (sum (B₁' ++ B₂)))) (Fin.toℕ<n frl))
... | inj₂ fr′ | inj₁ xl =
      ⊥-elim (<⇒≱ (subst (_< b) tx xl<b)
                  (≤-trans (m≤m+n b (sum B₁')) (m≤m+n (b + sum B₁') q)))
  where
    x≡ : xl ↑ˡ sum (B₁' ++ B₂) ≡ x
    x≡ = splitAt⁻¹-↑ˡ eqx
    xl<b : Fin.toℕ x < b
    xl<b = subst (_< b) (cong Fin.toℕ x≡)
             (subst (_< b) (sym (Fin.toℕ-↑ˡ xl (sum (B₁' ++ B₂)))) (Fin.toℕ<n xl))
... | inj₂ fr′ | inj₂ x′ =
      inj₂ (inj₂ (subst₂ (λ a c → before a c (structBinder (B₁' ++ B₂) 𝐂S.⋯ᵣ 𝐂S.wkˡ b))
                   freq xeq
                   (before-⋯ᵣ-inj (𝐂S.wkˡ b) (inj-wkˡ b) (structBinder (B₁' ++ B₂))
                     (before-structBinder-later B₁' B₂ {q} fr′ x′ tfr′ tx′ qne))))
  where
    freq : b ↑ʳ fr′ ≡ fr
    freq = splitAt⁻¹-↑ʳ eqfr
    xeq : b ↑ʳ x′ ≡ x
    xeq = splitAt⁻¹-↑ʳ eqx
    tfr′ : Fin.toℕ fr′ ≡ sum B₁'
    tfr′ = +-cancelˡ-≡ b (Fin.toℕ fr′) (sum B₁')
             (sym (Fin.toℕ-↑ʳ b fr′) ■ cong Fin.toℕ freq ■ tfr)
    tx′ : Fin.toℕ x′ ≡ sum B₁' + q
    tx′ = +-cancelˡ-≡ b (Fin.toℕ x′) (sum B₁' + q)
            (sym (Fin.toℕ-↑ʳ b x′) ■ cong Fin.toℕ xeq ■ tx ■ +-assoc b (sum B₁') q)

-- Lift into the ∥-of-two-bind-groups com binder (mirror of
-- RevGrindC.before-com-binderᴸ-gen, but feeding before-structBinder-later so the
-- LEFT group's block-front is ;-before a later same-block handle).
before-com-binderᴸ-later : ∀ (B₁ B₂ BR : BindGroup) {m q} (γ : Struct m)
    (fr x : 𝔽 (sum (B₁ ++ B₂)))
    → Fin.toℕ fr ≡ sum B₁ → Fin.toℕ x ≡ sum B₁ + q → q ≢ 0 →
  before ((fr ↑ˡ sum BR) ↑ˡ m) ((x ↑ˡ sum BR) ↑ˡ m)
    ( (structBinder (B₁ ++ B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (structBinder BR 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum (B₁ ++ B₂)) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    ∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum (B₁ ++ B₂) + sum BR)) )
before-com-binderᴸ-later B₁ B₂ BR {m} γ fr x tfr tx qne =
  inj₁ (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
    (structBinder (B₁ ++ B₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum BR))
    (before-⋯ᵣ-inj (𝐂S.wkʳ (sum BR)) (inj-wkʳ (sum BR)) (structBinder (B₁ ++ B₂))
      (before-structBinder-later B₁ B₂ fr x tfr tx qne))))
