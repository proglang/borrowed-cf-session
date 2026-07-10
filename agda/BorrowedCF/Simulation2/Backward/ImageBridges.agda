-- Strict image→image bridges for the reverse simulation's RU-Struct case.
--
--   For an untyped structural-congruence generator applied to a translation
--   image U[ P ]σ, we exhibit the reduct AS the translation image U[ P′ ]σ of
--   the corresponding typed move P′.  These "strict image" bridges let sim←ᵍ
--   reflect the untyped ≋′ step to a typed structural-congruence step.
--
--   ∥-comm / ∥-assoc / ∥-unit : U[_] is a ∥-homomorphism, so these hold strictly.
--
--   ν-swap : STRICT only when at most ONE of the two bind groups has a nonempty
--   φ-telescope.  For SINGLE-BLOCK groups (b₁ ∷ [] , b₂ ∷ [], syncs ≡ 0) the
--   reduct IS the strict image of the typed ν-swap target (ν-swap-bridge-sb).
--   Once BOTH groups have ≥ 2 blocks the two nonempty φ-telescopes must be
--   TRANSPOSED — a genuine ≋ move (φ-comm/assocSwap), NOT a strict ≡ — so the
--   general strict bridge is FALSE (see report / ProbeSwap counterexample).
module BorrowedCF.Simulation2.Backward.ImageBridges where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Simulation.TranslationProperties
  using (U-σ⋯; U-⋯ₚ; U-cong; Ub-nat; ++ₛ-⋯)
open import Data.Nat using (_+_)
open import Data.Nat.ListAction using (sum)
open import Data.List using (_∷_; [])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open Fin.Patterns

------------------------------------------------------------------------
-- ∥ homomorphism bridges (strict).
------------------------------------------------------------------------

∥-comm-bridge : ∀ {m n} (P Q : TP.Proc m) (σ : m →ₛ n) →
  U[ P TP.∥ Q ] σ UP.≋′ U[ Q TP.∥ P ] σ
∥-comm-bridge P Q σ = UP.∥-comm′

∥-assoc-bridge : ∀ {m n} (P₁ P₂ P₃ : TP.Proc m) (σ : m →ₛ n) →
  U[ P₁ TP.∥ (P₂ TP.∥ P₃) ] σ UP.≋′ U[ (P₁ TP.∥ P₂) TP.∥ P₃ ] σ
∥-assoc-bridge P₁ P₂ P₃ σ = UP.∥-assoc′

∥-unit-bridge : ∀ {m n} (P : TP.Proc m) (σ : m →ₛ n) →
  U[ TP.⟪ K `unit ⟫ TP.∥ P ] σ UP.≋′ U[ P ] σ
∥-unit-bridge P σ = UP.∥-unit′

------------------------------------------------------------------------
-- Substitution algebra for the single-block ν-swap bridge.
------------------------------------------------------------------------

private
  -- weaken* 0 is the identity renaming.
  w0 : ∀ {N} (x : Tm N) → x ⋯ weaken* ⦃ Kᵣ ⦄ 0 ≡ x
  w0 x = ⋯-id x (λ i → refl)

  -- ++ₛ swap-routing (substitution analog of Context's ++-swapᵣ).
  swap-route : ∀ {N} a b {c} (h₁ : 𝔽 a → Tm N) (h₂ : 𝔽 b → Tm N) (hc : 𝔽 c → Tm N)
                 (j : 𝔽 ((a + b) + c)) →
               ((h₂ ++ₛ h₁) ++ₛ hc) (swapᵣ a b j) ≡ ((h₁ ++ₛ h₂) ++ₛ hc) j
  swap-route a b h₁ h₂ hc j
    with Fin.splitAt (a + b) j
  ... | inj₂ jc = cong [ h₂ ++ₛ h₁ , hc ]′ (Fin.splitAt-↑ʳ (b + a) _ jc)
  ... | inj₁ j′
    with Fin.splitAt a j′
  ... | inj₁ j₁ = cong [ h₂ ++ₛ h₁ , hc ]′ (Fin.splitAt-↑ˡ (b + a) (b ↑ʳ j₁) _)
                ■ cong [ h₂ , h₁ ]′ (Fin.splitAt-↑ʳ b _ j₁)
  ... | inj₂ j₂ = cong [ h₂ ++ₛ h₁ , hc ]′ (Fin.splitAt-↑ˡ (b + a) (j₂ ↑ˡ a) _)
                ■ cong [ h₂ , h₁ ]′ (Fin.splitAt-↑ˡ b j₂ _)

------------------------------------------------------------------------
-- ν-swap, single-block groups (both φ-telescopes empty, syncs ≡ 0).
--   The untyped ν-swap′ reduct IS the strict image of the typed ν-swap target.
------------------------------------------------------------------------

ν-swap-bridge-sb : ∀ {m n} (b₁ b₂ : ℕ)
  (P₀ : TP.Proc ((b₁ + 0) + (b₂ + 0) + m)) (σ : m →ₛ n) →
  U[ TP.ν (b₁ ∷ []) (b₂ ∷ []) P₀ ] σ
    UP.≋′ U[ TP.ν (b₂ ∷ []) (b₁ ∷ []) (P₀ TP.⋯ₚ swapᵣ (b₁ + 0) (b₂ + 0)) ] σ
ν-swap-bridge-sb {m} {n} b₁ b₂ P₀ σ =
  subst (U[ TP.ν (b₁ ∷ []) (b₂ ∷ []) P₀ ] σ UP.≋′_)
    (cong UP.ν (U-σ⋯ P₀ ■ U-cong P₀ EQ ■ sym (U-⋯ₚ P₀)))
    (UP.ν-swap′ {P = _})
  where
    eq1 : (k₁ : 𝔽 (b₁ + 0)) →
          (Ub[ b₁ + 0 ] (K `unit , 0F , K `unit) k₁ ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ swapᵣ 1 1 {n}
          ≡ Ub[ b₁ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit) k₁
    eq1 k₁ = cong (_⋯ swapᵣ 1 1) (Ub-nat (b₁ + 0) (K `unit , 0F , K `unit) (weaken* ⦃ Kᵣ ⦄ 0) k₁)
           ■ Ub-nat (b₁ + 0) (K `unit , 0F , K `unit) (swapᵣ 1 1) k₁

    eq2 : (k₂ : 𝔽 (b₂ + 0)) →
          Ub[ b₂ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit) k₂ ⋯ swapᵣ 1 1 {n}
          ≡ Ub[ b₂ + 0 ] (K `unit , 0F , K `unit) k₂ ⋯ weaken* ⦃ Kᵣ ⦄ 0
    eq2 k₂ = Ub-nat (b₂ + 0) (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit) (swapᵣ 1 1) k₂
           ■ sym (Ub-nat (b₂ + 0) (K `unit , 0F , K `unit) (weaken* ⦃ Kᵣ ⦄ 0) k₂)

    eq3 : (l : 𝔽 m) →
          (σ l ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0) ⋯ swapᵣ 1 1
          ≡ σ l ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    eq3 l = cong (_⋯ swapᵣ 1 1) (w0 t1) ■ cong (_⋯ swapᵣ 1 1) (w0 t0)
          ■ weaken*-swap-⋯ (σ l) 1 1
          ■ sym (w0 t0) ■ sym (w0 t1)
      where
        t0 = σ l ⋯ weaken* ⦃ Kᵣ ⦄ 2
        t1 = t0 ⋯ weaken* ⦃ Kᵣ ⦄ 0

    EQ : (((λ i → Ub[ b₁ + 0 ] (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ 0)
            ++ₛ Ub[ b₂ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit))
          ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0))
          ·ₖ swapᵣ 1 1
        ≗ swapᵣ (b₁ + 0) (b₂ + 0)
          ·ₖ (((λ i → Ub[ b₂ + 0 ] (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ 0)
                ++ₛ Ub[ b₁ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit))
              ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0))
    EQ j =
        ++ₛ-⋯ (G₁ ++ₛ G₂) tl (swapᵣ 1 1) j
      ■ [,]-cong outerFirst eq3 (Fin.splitAt ((b₁ + 0) + (b₂ + 0)) j)
      ■ sym (swap-route (b₁ + 0) (b₂ + 0) H₁ H₂ tl j)
      where
        G₁ = λ i → Ub[ b₁ + 0 ] (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ 0
        G₂ = Ub[ b₂ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit)
        H₁ = Ub[ b₁ + 0 ] (K `unit , weaken* ⦃ Kᵣ ⦄ 0 1F , K `unit)
        H₂ = λ i → Ub[ b₂ + 0 ] (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ 0
        tl = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
        outerFirst : ∀ k → (G₁ ++ₛ G₂) k ⋯ swapᵣ 1 1 ≡ (H₁ ++ₛ H₂) k
        outerFirst k = ++ₛ-⋯ G₁ G₂ (swapᵣ 1 1) k ■ [,]-cong eq1 eq2 (Fin.splitAt (b₁ + 0) k)
