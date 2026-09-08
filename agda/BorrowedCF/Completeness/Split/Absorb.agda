-- | Completeness toolkit, part 3: an unrestricted structure whose variables all
--   already occur in γ can be dropped from γ.  The engine is `unr-extract`: an
--   unrestricted variable of γ can be pulled out in front of γ, because `Unr`
--   implies `Mobile` (so it commutes past `;`) and duplicates (`∥′-dup`).
module BorrowedCF.Completeness.Split.Absorb where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Completeness.Split.Base using (mem-self)
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (_∈ₘ_; mem-parInv; mem-seqInv; mem-parL; mem-parR; mem-seqL; mem-seqR)

open Nat.Variables
open Variables

private
  variable
    A : Set

unr-mob : {Γ : Ctx n} {x : 𝔽 n} → Unr (Γ ﹫ x) → MobCx Γ (` x)
unr-mob Ux = ` unr⇒mobile Ux

-- An unrestricted variable that occurs in γ can be extracted in front of γ.
unr-extract : {Γ : Ctx n} {x : 𝔽 n} (γ : Struct n) →
  Unr (Γ ﹫ x) → x ∈ₘ γ → Γ ∶ γ ≈ (` x) ∥ γ
unr-extract []            Ux x∈ = ⊥-elim (x∈ refl)
unr-extract {x = x} (` y) Ux x∈ with x Fin.≟ y
... | yes refl = ∥-dup (` Ux)
... | no  _    = ⊥-elim (x∈ refl)
unr-extract {x = x} (γ₁ ∥ γ₂) Ux x∈ with mem-parInv {α = γ₁} {γ₂} x∈
... | inj₁ x∈₁ = ≈-trans (∥-cong (unr-extract γ₁ Ux x∈₁) ≈-refl) ∥-assoc
... | inj₂ x∈₂ = ≈-trans (∥-cong ≈-refl (unr-extract γ₂ Ux x∈₂))
                 (≈-trans (≈-sym ∥-assoc)
                 (≈-trans (∥-cong ∥-comm ≈-refl) ∥-assoc))
unr-extract {x = x} (γ₁ ; γ₂) Ux x∈ with mem-seqInv {α = γ₁} {γ₂} x∈
... | inj₁ x∈₁ = ≈-trans (;-cong (unr-extract γ₁ Ux x∈₁) ≈-refl)
                 (≈-trans (;-cong (∥/;-transmute (inj₁ (unr-mob Ux))) ≈-refl)
                 (≈-trans ;-assoc (≈-sym (∥/;-transmute (inj₁ (unr-mob Ux))))))
... | inj₂ x∈₂ = ≈-trans (;-cong ≈-refl (unr-extract γ₂ Ux x∈₂))
                 (≈-trans (;-cong ≈-refl (∥/;-transmute (inj₁ (unr-mob Ux))))
                 (≈-trans (≈-sym ;-assoc)
                 (≈-trans (;-cong (;-commMob (inj₂ (unr-mob Ux))) ≈-refl)
                 (≈-trans ;-assoc (≈-sym (∥/;-transmute (inj₁ (unr-mob Ux))))))))

------------------------------------------------------------------------
-- Absorption.

unr-absorb : {Γ : Ctx n} {γ β : Struct n} →
  AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ γ ∥ β ≼ γ
unr-absorb []      mem = ≼-refl ∥-unit₂
unr-absorb (` Uy)  mem =
  ≼-refl (≈-trans ∥-comm (≈-sym (unr-extract _ Uy (mem _ (mem-self _)))))
unr-absorb {β = β₁ ∥ β₂} (U₁ ∥ U₂) mem =
  ≼-trans (≼-refl (≈-sym ∥-assoc))
    (≼-trans (≼-cong-∥ (unr-absorb U₁ (λ z z∈ → mem z (mem-parL {α = β₁} {β₂} z∈)))
                       (≼-refl ≈-refl))
             (unr-absorb U₂ (λ z z∈ → mem z (mem-parR {α = β₁} {β₂} z∈))))
unr-absorb {β = β₁ ; β₂} (U₁ ; U₂) mem =
  ≼-trans (≼-refl (≈-trans (∥-cong ≈-refl (≈-sym (∥/;-transmute (inj₁ (UnrCx⇒MobCx U₁)))))
                           (≈-sym ∥-assoc)))
    (≼-trans (≼-cong-∥ (unr-absorb U₁ (λ z z∈ → mem z (mem-seqL {α = β₁} {β₂} z∈)))
                       (≼-refl ≈-refl))
             (unr-absorb U₂ (λ z z∈ → mem z (mem-seqR {α = β₁} {β₂} z∈))))

unr-absorb-; : {Γ : Ctx n} {γ β : Struct n} →
  AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ γ ; β ≼ γ
unr-absorb-; U mem =
  ≼-trans (≼-refl (≈-sym (∥/;-transmute (inj₂ (UnrCx⇒MobCx U))))) (unr-absorb U mem)

unr-absorb-;ˡ : {Γ : Ctx n} {γ β : Struct n} →
  AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ β ; γ ≼ γ
unr-absorb-;ˡ U mem =
  ≼-trans (≼-refl (;-commMob (inj₁ (UnrCx⇒MobCx U)))) (unr-absorb-; U mem)

-- All three at once, for an arbitrary `join`.
unr-absorb-join : ⦃ J : Join A ⦄ (a : A) {Γ : Ctx n} {γ β : Struct n} →
  AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ join a γ β ≼ γ
unr-absorb-join a U mem with joinDir a
... | 𝟙 = unr-absorb U mem
... | L = unr-absorb-; U mem
... | R = unr-absorb-;ˡ U mem

unr-absorb-joinˡ : ⦃ J : Join A ⦄ (a : A) {Γ : Ctx n} {γ β : Struct n} →
  AllCx Unr Γ β → (∀ z → z ∈ₘ β → z ∈ₘ γ) → Γ ∶ join a β γ ≼ γ
unr-absorb-joinˡ a U mem with joinDir a
... | 𝟙 = ≼-trans (≼-refl ∥-comm) (unr-absorb U mem)
... | L = unr-absorb-;ˡ U mem
... | R = unr-absorb-; U mem
