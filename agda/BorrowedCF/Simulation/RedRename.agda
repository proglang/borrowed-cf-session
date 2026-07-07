module BorrowedCF.Simulation.RedRename where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Processes.Untyped
open import BorrowedCF.Simulation.Frames using (frame-plug₁)
open import BorrowedCF.Simulation.FrameRename using (⋯ᶠ*-fuse; ⋯ᶠ*-cong)
open import Relation.Binary.Construct.Closure.Equivalence using (gmap)

open Variables
open Fin.Patterns

-- Head reduction is stable under renaming (renaming specialisation of
-- Simulation2.Frames.─→-⋯ₛ; every renaming is a value substitution).

─→-⋯ᵣ : (ρ : m →ᵣ n) → {e₁ e₂ : Tm m} → e₁ ─→ e₂ → e₁ ⋯ ρ ─→ e₂ ⋯ ρ
─→-⋯ᵣ ρ (E-App {a} {_} {b} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ b a ρ)) (E-App (value-⋯ V ρ (λ x → V-`)))
─→-⋯ᵣ ρ (E-Seq V) = E-Seq (value-⋯ V ρ (λ x → V-`))
─→-⋯ᵣ ρ (E-Let {e₁} {e₂} V) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e₂ e₁ ρ)) (E-Let (value-⋯ V ρ (λ x → V-`)))
─→-⋯ᵣ ρ (E-PairElim {e₁} {e₂} {e} V₁ V₂) =
  subst₂ _─→_ refl eq (E-PairElim (value-⋯ V₁ ρ (λ x → V-`)) (value-⋯ V₂ ρ (λ x → V-`)))
  where
    inner : e ⋯ ⦅ wk e₁ ⦆ ⋯ ρ ↑ ≡ e ⋯ ρ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ ρ) ⦆
    inner = dist-↑-⦅⦆-⋯ e (wk e₁) (ρ ↑) ■ cong (λ z → e ⋯ ρ ↑ ↑ ⋯ ⦅ z ⦆) (sym (⋯-↑-wk e₁ ρ))
    eq : e ⋯ ρ ↑ ↑ ⋯ ⦅ wk (e₁ ⋯ ρ) ⦆ ⋯ ⦅ e₂ ⋯ ρ ⦆ ≡ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆ ⋯ ρ
    eq = cong (_⋯ ⦅ e₂ ⋯ ρ ⦆) (sym inner) ■ sym (dist-↑-⦅⦆-⋯ (e ⋯ ⦅ wk e₁ ⦆) e₂ ρ)
─→-⋯ᵣ ρ (E-SumElim {e = e} {e₁ = e₁} {e₂ = e₂} {i = i} V) =
  subst₂ _─→_ refl (sumElim-eq i e₁ e₂ e ρ) (E-SumElim (value-⋯ V ρ (λ x → V-`)))
  where
    sumElim-eq : ∀ i (e₁ e₂ : Tm (suc m)) (e : Tm m) (ρ : m →ᵣ n) →
      (if i then (e₁ ⋯ ρ ↑) else (e₂ ⋯ ρ ↑)) ⋯ ⦅ e ⋯ ρ ⦆
        ≡ ((if i then e₁ else e₂) ⋯ ⦅ e ⦆) ⋯ ρ
    sumElim-eq i e₁ e₂ e ρ with i
    ... | true  = sym (dist-↑-⦅⦆-⋯ e₁ e ρ)
    ... | false = sym (dist-↑-⦅⦆-⋯ e₂ e ρ)
─→-⋯ᵣ ρ (E-Unfold {e}) =
  subst₂ _─→_ refl (sym (dist-↑-⦅⦆-⋯ e (μ e) ρ)) E-Unfold

⋯→-⋯ᵣ : (ρ : m →ᵣ n) → {e₁ e₂ : Tm m} → e₁ ⋯→ e₂ → e₁ ⋯ ρ ⋯→ e₂ ⋯ ρ
⋯→-⋯ᵣ ρ (E-□ red) = E-□ (─→-⋯ᵣ ρ red)
⋯→-⋯ᵣ ρ (E-Ctx E red) =
  subst₂ _⋯→_ (sym (frame-plug₁ E ρ (λ x → V-`))) (sym (frame-plug₁ E ρ (λ x → V-`)))
    (E-Ctx (E ⋯ᶠ ρ) (⋯→-⋯ᵣ ρ red))

-- Recursive (Frame*) plugging commutes with renaming.

fp* : (E* : Frame* m) (ρ : m →ᵣ n) {t : Tm m} →
      (E* [ t ]*) ⋯ ρ ≡ (E* ⋯ᶠ* ρ) [ t ⋯ ρ ]*
fp* []       ρ = refl
fp* (E ∷ E*) ρ = frame-plug₁ E ρ (λ x → V-`) ■ cong ((E ⋯ᶠ ρ) [_]) (fp* E* ρ)

-- Structural congruence is stable under renaming (mirror of the typed
-- Processes.Typed.⋯-preserves-≋′, extended with the φ / νφ constructors).

≋′-⋯ₚ : {ρ : m →ᵣ n} {P Q : Proc m} → P ≋′ Q → (P ⋯ₚ ρ) ≋′ (Q ⋯ₚ ρ)
≋′-⋯ₚ ∥-comm′  = ∥-comm′
≋′-⋯ₚ ∥-assoc′ = ∥-assoc′
≋′-⋯ₚ ∥-unit′  = ∥-unit′
≋′-⋯ₚ {ρ = ρ} ν-swap′ =
  subst₂ _≋′_ refl (cong ν (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-swap 1 1 ρ))) ν-swap′
≋′-⋯ₚ {ρ = ρ} ν-comm′ =
  subst₂ _≋′_ refl (cong (λ z → ν (ν z)) (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-assocSwap 2 2 ρ))) ν-comm′
≋′-⋯ₚ {ρ = ρ} (φ-comm′ {x = x} {y = y}) =
  subst₂ _≋′_ refl (cong (λ z → φ y (φ x z)) (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-assocSwap 1 1 ρ))) φ-comm′
≋′-⋯ₚ {ρ = ρ} (νφ-comm′ {x = x}) =
  subst₂ _≋′_ refl (cong (λ z → φ x (ν z)) (≡-fusedₚ _ _ _ _ _ (sym ∘ dist-↑*-assocSwap 1 2 ρ))) νφ-comm′
≋′-⋯ₚ {ρ = ρ} (ν-ext′ {P = P}) =
  let eq = fusionₚ P ρ (weaken* ⦃ Kᵣ ⦄ 2)
         ■ ⋯ₚ-cong P (↑*-wk ρ 2)
         ■ sym (fusionₚ P (weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2)) in
  subst₂ _≋′_ refl (cong ν (cong₂ _∥_ eq refl)) ν-ext′
≋′-⋯ₚ {ρ = ρ} (φ-ext′ {x = x}) =
  let eq = fusionₚ _ ρ (weaken* ⦃ Kᵣ ⦄ 1)
         ■ ⋯ₚ-cong _ (↑*-wk ρ 1)
         ■ sym (fusionₚ _ (weaken* ⦃ Kᵣ ⦄ 1) (ρ ↑)) in
  subst₂ _≋′_ refl (cong (φ x) (cong₂ _∥_ eq refl)) φ-ext′
≋′-⋯ₚ (∥-cong′ x) = ∥-cong′ (≋′-⋯ₚ x)
≋′-⋯ₚ (ν-cong′ x) = ν-cong′ (≋′-⋯ₚ x)
≋′-⋯ₚ (φ-cong′ x) = φ-cong′ (≋′-⋯ₚ x)

infix 5 _≋-⋯_

_≋-⋯_ : {P Q : Proc m} → P ≋ Q → (ρ : m →ᵣ n) → (P ⋯ₚ ρ) ≋ (Q ⋯ₚ ρ)
eq ≋-⋯ ρ = gmap (_⋯ₚ ρ) ≋′-⋯ₚ eq

-- Untyped process reduction is stable under renaming.

red-⋯ₚ : {m n : ℕ} {R Q : Proc m} (ρ : m →ᵣ n) →
         R ─→ₚ Q → (R ⋯ₚ ρ) ─→ₚ (Q ⋯ₚ ρ)
red-⋯ₚ ρ (RU-Exp red) = RU-Exp (⋯→-⋯ᵣ ρ red)
red-⋯ₚ ρ (RU-Par r)   = RU-Par (red-⋯ₚ ρ r)
red-⋯ₚ ρ (RU-Res r)   = RU-Res (red-⋯ₚ (ρ ↑* 2) r)
red-⋯ₚ ρ (RU-Sync r)  = RU-Sync (red-⋯ₚ (ρ ↑) r)
red-⋯ₚ ρ (RU-Struct c₁ r c₂) = RU-Struct (c₁ ≋-⋯ ρ) (red-⋯ₚ ρ r) (c₂ ≋-⋯ ρ)
red-⋯ₚ ρ (RU-Discard {e = e} F V) =
  subst₂ _─→ₚ_
    (cong ⟪_⟫ (sym (fp* F ρ {t = K `discard ·¹ e})))
    (cong ⟪_⟫ (sym (fp* F ρ {t = *})))
    (RU-Discard (F ⋯ᶠ* ρ) (value-⋯ V ρ (λ x → V-`)))
red-⋯ₚ ρ (RU-Fork {e = e} F V) =
  subst₂ _─→ₚ_
    (cong ⟪_⟫ (sym (fp* F ρ {t = K `fork ·¹ e})))
    (cong (λ z → ⟪ z ⟫ ∥ ⟪ (e ⋯ ρ) ·¹ * ⟫) (sym (fp* F ρ {t = *})))
    (RU-Fork (F ⋯ᶠ* ρ) (value-⋯ V ρ (λ x → V-`)))
red-⋯ₚ ρ (RU-LSplit {s = s} {e₁ = e₁} {e₂ = e₂} {P = P} F) =
  subst₂ _─→ₚ_
    (cong (λ z → ν (⟪ z ⟫ ∥ (P ⋯ₚ ρ ↑* 2)))
          (sym (fp* F (ρ ↑* 2) {t = K (`lsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ]})))
    (cong (λ z → ν (⟪ z ⟫ ∥ (P ⋯ₚ ρ ↑* 2)))
          (sym (fp* F (ρ ↑* 2) {t = 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ]})))
    (RU-LSplit (F ⋯ᶠ* ρ ↑* 2))
red-⋯ₚ ρ (RU-Drop {P = P} F {x = x}) =
  subst₂ _─→ₚ_
    (cong (λ z → φ drop (⟪ z ⟫ ∥ (P ⋯ₚ ρ ↑)))
          (sym (fp* F (ρ ↑) {t = K `drop ·¹ 𝓒[ * × suc x × ` 0F ]})))
    (cong (λ z → φ acq (⟪ z ⟫ ∥ (P ⋯ₚ ρ ↑)))
          (sym (fp* F (ρ ↑) {t = *})))
    (RU-Drop (F ⋯ᶠ* ρ ↑) {x = ρ x})
red-⋯ₚ ρ (RU-Acquire {e = e} {P = P} F) =
  subst₂ _─→ₚ_ (sym leftEq) (sym rightEq)
    (RU-Acquire {e = e ⋯ ρ ↑* 2} {P = P ⋯ₚ ρ ↑* 2} (F ⋯ᶠ* ρ ↑* 2))
  where
    Feq : (F ⋯ᶠ* weakenᵣ) ⋯ᶠ* (ρ ↑* 2 ↑ᵣ) ≡ (F ⋯ᶠ* ρ ↑* 2) ⋯ᶠ* weakenᵣ
    Feq = ⋯ᶠ*-fuse F weakenᵣ (ρ ↑* 2 ↑ᵣ)
        ■ ⋯ᶠ*-cong F (λ x → sym (↑-wk (ρ ↑* 2) x))
        ■ sym (⋯ᶠ*-fuse F (ρ ↑* 2) weakenᵣ)

    Ceq : (K `acq ·¹ 𝓒[ ` 0F × 1F × wk e ]) ⋯ (ρ ↑* 2 ↑ᵣ)
        ≡ K `acq ·¹ 𝓒[ ` 0F × 1F × wk (e ⋯ ρ ↑* 2) ]
    Ceq = cong (K `acq ·¹_) (cong (λ a → 𝓒[ ` 0F × 1F × a ]) wkEq)
      where
        wkEq : wk e ⋯ (ρ ↑* 2 ↑ᵣ) ≡ wk (e ⋯ ρ ↑* 2)
        wkEq = fusion e weakenᵣ (ρ ↑* 2 ↑ᵣ)
             ■ ⋯-cong e (λ x → sym (↑-wk (ρ ↑* 2) x))
             ■ sym (fusion e (ρ ↑* 2) weakenᵣ)

    plugEq : ((F ⋯ᶠ* weakenᵣ) [ K `acq ·¹ 𝓒[ ` 0F × 1F × wk e ] ]*) ⋯ (ρ ↑* 2 ↑ᵣ)
           ≡ ((F ⋯ᶠ* ρ ↑* 2) ⋯ᶠ* weakenᵣ) [ K `acq ·¹ 𝓒[ ` 0F × 1F × wk (e ⋯ ρ ↑* 2) ] ]*
    plugEq = fp* (F ⋯ᶠ* weakenᵣ) (ρ ↑* 2 ↑ᵣ) {t = K `acq ·¹ 𝓒[ ` 0F × 1F × wk e ]}
          ■ cong₂ _[_]* Feq Ceq

    Peq : (P ⋯ₚ weakenᵣ) ⋯ₚ (ρ ↑* 2 ↑ᵣ) ≡ (P ⋯ₚ ρ ↑* 2) ⋯ₚ weakenᵣ
    Peq = fusionₚ P weakenᵣ (ρ ↑* 2 ↑ᵣ)
        ■ ⋯ₚ-cong P (↑-wk (ρ ↑* 2))
        ■ sym (fusionₚ P (ρ ↑* 2) weakenᵣ)

    leftEq :
      ν (φ acq
          (⟪ ((F ⋯ᶠ* weakenᵣ) [ K `acq ·¹ 𝓒[ ` 0F × 1F × wk e ] ]*) ⋯ (ρ ↑* 2 ↑ᵣ) ⟫
             ∥ ((P ⋯ₚ weakenᵣ) ⋯ₚ (ρ ↑* 2 ↑ᵣ))))
      ≡
      ν (φ acq
          (⟪ ((F ⋯ᶠ* ρ ↑* 2) ⋯ᶠ* weakenᵣ) [ K `acq ·¹ 𝓒[ ` 0F × 1F × wk (e ⋯ ρ ↑* 2) ] ]* ⟫
             ∥ ((P ⋯ₚ ρ ↑* 2) ⋯ₚ weakenᵣ)))
    leftEq = cong ν (cong (φ acq)
               (cong₂ _∥_
                 (cong ⟪_⟫ plugEq)
                 Peq))

    rightEq :
      ν ((⟪ F [ 𝓒[ * × 0F × e ] ]* ⟫ ∥ P) ⋯ₚ ρ ↑* 2)
      ≡
      ν (⟪ (F ⋯ᶠ* ρ ↑* 2) [ 𝓒[ * × 0F × (e ⋯ ρ ↑* 2) ] ]* ⟫ ∥ (P ⋯ₚ ρ ↑* 2))
    rightEq = cong ν (cong₂ _∥_ (cong ⟪_⟫ (fp* F (ρ ↑* 2) {t = 𝓒[ * × 0F × e ]})) refl)
red-⋯ₚ ρ (RU-Com {e = e} {P = P} F₁ F₂ V {e₁ = e₁} {e₁′ = e₁′} {e₂ = e₂} {e₂′ = e₂′}) =
  subst₂ _─→ₚ_
    (cong₂ (λ z w → ν (⟪ z ⟫ ∥ (⟪ w ⟫ ∥ (P ⋯ₚ ρ ↑* 2))))
       (sym (fp* F₁ (ρ ↑* 2) {t = K `send ·¹ (e ⊗ 𝓒[ e₁ × 0F × e₁′ ])}))
       (sym (fp* F₂ (ρ ↑* 2) {t = K `recv ·¹ 𝓒[ e₂ × 1F × e₂′ ]})))
    (cong₂ (λ z w → ν (⟪ z ⟫ ∥ (⟪ w ⟫ ∥ (P ⋯ₚ ρ ↑* 2))))
       (sym (fp* F₁ (ρ ↑* 2) {t = *}))
       (sym (fp* F₂ (ρ ↑* 2) {t = e})))
    (RU-Com (F₁ ⋯ᶠ* ρ ↑* 2) (F₂ ⋯ᶠ* ρ ↑* 2) (value-⋯ V (ρ ↑* 2) (λ x → V-`)))
red-⋯ₚ ρ (RU-Choice {P = P} F₁ F₂ k {e₁ = e₁} {e₁′ = e₁′} {e₂ = e₂} {e₂′ = e₂′}) =
  subst₂ _─→ₚ_
    (cong₂ (λ z w → ν (⟪ z ⟫ ∥ (⟪ w ⟫ ∥ (P ⋯ₚ ρ ↑* 2))))
       (sym (fp* F₁ (ρ ↑* 2) {t = K (`select k) ·¹ 𝓒[ e₁ × 0F × e₁′ ]}))
       (sym (fp* F₂ (ρ ↑* 2) {t = K `branch ·¹ 𝓒[ e₂ × 1F × e₂′ ]})))
    (cong₂ (λ z w → ν (⟪ z ⟫ ∥ (⟪ w ⟫ ∥ (P ⋯ₚ ρ ↑* 2))))
       (sym (fp* F₁ (ρ ↑* 2) {t = 𝓒[ e₁ × 0F × e₁′ ]}))
       (sym (fp* F₂ (ρ ↑* 2) {t = `inj k 𝓒[ e₂ × 1F × e₂′ ]})))
    (RU-Choice (F₁ ⋯ᶠ* ρ ↑* 2) (F₂ ⋯ᶠ* ρ ↑* 2) k)
red-⋯ₚ ρ (RU-New {s = s} F) =
  subst₂ _─→ₚ_
    (cong ⟪_⟫ (sym (fp* F ρ {t = K (`new s) ·¹ *})))
    (cong (λ z → ν (φ acq (φ acq ⟪ z ⟫)))
          (sym (fp* (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) (ρ ↑* 2 ↑ ↑)
                    {t = 𝓒[ ` 0F × 3F × * ] ⊗ 𝓒[ ` 1F × 2F × * ]}
                ■ cong (_[ _ ]*) Feq)))
    (RU-New (F ⋯ᶠ* ρ))
  where
    Feq : (F ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) ⋯ᶠ* (ρ ↑* 2 ↑ ↑) ≡ (F ⋯ᶠ* ρ) ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4
    Feq = ⋯ᶠ*-fuse F (weaken* ⦃ Kᵣ ⦄ 4) (ρ ↑* 2 ↑ ↑)
        ■ ⋯ᶠ*-cong F (λ x → sym (↑*-wk ρ 4 x))
        ■ sym (⋯ᶠ*-fuse F ρ (weaken* ⦃ Kᵣ ⦄ 4))
red-⋯ₚ ρ (RU-Close F₁ F₂ {e₁ = e₁} {e₁′ = e₁′} {e₂ = e₂} {e₂′ = e₂′}) =
  subst₂ _─→ₚ_
    (cong₂ (λ z w → ν (⟪ z ⟫ ∥ ⟪ w ⟫))
       (sym (fp* (F₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2)
                 {t = K (`end ‼) ·¹ 𝓒[ e₁ × 0F × e₁′ ]}
             ■ cong (_[ _ ]*) (Feq F₁)))
       (sym (fp* (F₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2)
                 {t = K (`end ⁇) ·¹ 𝓒[ e₂ × 1F × e₂′ ]}
             ■ cong (_[ _ ]*) (Feq F₂))))
    (cong₂ (λ z w → ⟪ z ⟫ ∥ ⟪ w ⟫)
       (sym (fp* F₁ ρ {t = *}))
       (sym (fp* F₂ ρ {t = *})))
    (RU-Close (F₁ ⋯ᶠ* ρ) (F₂ ⋯ᶠ* ρ))
  where
    Feq : (E : Frame* _) → (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) ⋯ᶠ* (ρ ↑* 2) ≡ (E ⋯ᶠ* ρ) ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2
    Feq E = ⋯ᶠ*-fuse E (weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2)
          ■ ⋯ᶠ*-cong E (λ x → sym (↑*-wk ρ 2 x))
          ■ sym (⋯ᶠ*-fuse E ρ (weaken* ⦃ Kᵣ ⦄ 2))
red-⋯ₚ ρ (RU-RSplit {s = s} {e₁ = e₁} {e₂ = e₂} {P = P} F) =
  subst₂ _─→ₚ_
    (cong (λ z → ν (⟪ z ⟫ ∥ (P ⋯ₚ ρ ↑* 2)))
          (sym (fp* F (ρ ↑* 2) {t = K (`rsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ]})))
    (cong₂ (λ z w → ν (φ drop (⟪ z ⟫ ∥ w)))
       (sym (fp* (F ⋯ᶠ* weakenᵣ) (ρ ↑* 2 ↑)
                 {t = 𝓒[ wk e₁ × 1F × ` 0F ] ⊗ 𝓒[ ` 0F × 1F × wk e₂ ]}
             ■ cong₂ _[_]* Feq Ceq))
       Peq)
    (RU-RSplit (F ⋯ᶠ* ρ ↑* 2))
  where
    Feq : (F ⋯ᶠ* weakenᵣ) ⋯ᶠ* (ρ ↑* 2 ↑) ≡ (F ⋯ᶠ* ρ ↑* 2) ⋯ᶠ* weakenᵣ
    Feq = ⋯ᶠ*-fuse F weakenᵣ (ρ ↑* 2 ↑)
        ■ ⋯ᶠ*-cong F (λ x → sym (↑-wk (ρ ↑* 2) x))
        ■ sym (⋯ᶠ*-fuse F (ρ ↑* 2) weakenᵣ)
    Ceq : (𝓒[ wk e₁ × 1F × ` 0F ] ⊗ 𝓒[ ` 0F × 1F × wk e₂ ]) ⋯ (ρ ↑* 2 ↑)
          ≡ 𝓒[ wk (e₁ ⋯ ρ ↑* 2) × 1F × ` 0F ] ⊗ 𝓒[ ` 0F × 1F × wk (e₂ ⋯ ρ ↑* 2) ]
    Ceq = cong₂ (λ a b → 𝓒[ a × 1F × ` 0F ] ⊗ 𝓒[ ` 0F × 1F × b ])
                (sym (⋯-↑-wk e₁ (ρ ↑* 2))) (sym (⋯-↑-wk e₂ (ρ ↑* 2)))
    Peq : (P ⋯ₚ ρ ↑* 2) ⋯ₚ weakenᵣ ≡ (P ⋯ₚ weakenᵣ) ⋯ₚ ρ ↑* 2 ↑
    Peq = fusionₚ P (ρ ↑* 2) weakenᵣ
        ■ ⋯ₚ-cong P (↑-wk (ρ ↑* 2))
        ■ sym (fusionₚ P weakenᵣ (ρ ↑* 2 ↑))
