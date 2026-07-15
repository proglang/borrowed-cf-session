module BorrowedCF.Processes.Renamings where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Terms as Terms
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open ≡-Reasoning
open SplitRenamings

⊢wkRSplit : (B₁ B₂ : BindGroup) (m q : ℕ) {b n : ℕ} →
    (Γ₁ : Ctx (sum B₁))
    (Γ₂ : Ctx (sum B₂))
    (Γq : Ctx q)
    (Γb : Ctx (suc b))
    (Γₘ : Ctx m)
    (Γₙ : Ctx n) →
  rwk B₁ B₂ m {q = q}
    ⊢  (V.cast (sym (sum-++ B₁ (q + suc b ∷ B₂))) (Γ₁ ⸴* (Γq ⸴* Γb) ⸴* Γ₂) ⸴* Γₘ) ⸴* Γₙ
    ⇒ᵣ (V.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b ∷ B₂))) (Γ₁ ⸴* (Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂) ⸴* Γₘ) ⸴* Γₙ
⊢wkRSplit B₁ B₂ m q {b} Γ₁ Γ₂ Γq Γb Γₘ Γₙ = ⊢ren (go B₁ Γ₁ Γq) where
  go : ∀ {q} (B₁ : BindGroup) (Γ₁ : Ctx (sum B₁)) (Γq : Ctx q) x →
    ((V.cast (sym (sum-++ B₁ (q + suc b ∷ B₂))) (Γ₁ ⸴* (Γq ⸴* Γb) ⸴* Γ₂) ⸴* Γₘ) ⸴* Γₙ) ﹫ x
      ≡
    ((V.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b ∷ B₂))) (Γ₁ ⸴* (Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂) ⸴* Γₘ) ⸴* Γₙ) ﹫ rwk B₁ B₂ m x
  go [] [] [] x
    rewrite V.cast-is-id refl (Γb ⸴* Γ₂)
    = cong (lookup (((Γb ⸴* Γ₂) ⸴* Γₘ) ⸴* Γₙ)) (sym (Fin.cast-involutive (suc⁻¹ (RSplit.eq₂ [] B₂ m {0} {b})) (RSplit.eq₁ [] B₂ m {0} {b}) x))
  go [] [] (Uq ⸴ Γq) zero = refl
  go [] [] (Uq ⸴ Γq) (suc x) = go [] [] Γq x
  go (zero ∷ B₁) Γ₁ Γq x = go B₁ Γ₁ Γq x
  go {T} (suc b ∷ B₁) Γ₁ Γq zero =
    V.lookup-++ˡ (V.cast _ (Γ₁ ⸴* (Γq ⸴* Γb) ⸴* Γ₂) ⸴* Γₘ) Γₙ zero
      ■ V.lookup-++ˡ (V.cast _ (Γ₁ ⸴* (Γq ⸴* Γb) ⸴* Γ₂)) Γₘ zero
      ■ V.lookup-cast₁ _ (Γ₁ ⸴* (Γq ⸴* Γb) ⸴* Γ₂) zero
      ■ V.lookup-++ˡ Γ₁ ((Γq ⸴* Γb) ⸴* Γ₂) zero
      ■ sym (V.lookup-++ˡ Γ₁ ((Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂) zero)
      ■ sym (V.lookup-cast₁ _ (Γ₁ ⸴* (Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂) zero)
      ■ sym (V.lookup-++ˡ (V.cast _ (Γ₁ ⸴* (Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂)) Γₘ zero)
      ■ sym (V.lookup-++ˡ (V.cast _ (Γ₁ ⸴* (Γq ⸴* V.[ T ]) ⸴* Γb ⸴* Γ₂) ⸴* Γₘ) Γₙ zero)
  go (suc b ∷ B₁) (U ⸴ Γ₁) Γq (suc x) = go (b ∷ B₁) Γ₁ Γq x

⊢wkₚ : ∀ {m₁ m₂ n} (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) (Γ : Ctx n) {T₁ T₂ : 𝕋} →
  wkₚ {n} m₁ m₂ ⊢ (Γ₁ ⸴* Γ₂) ⸴* Γ ⇒ᵣ (T₁ ⸴ Γ₁ ⸴* T₂ ⸴ Γ₂) ⸴* Γ
⊢wkₚ Γ₁ Γ₂ Γ {T₁} {T₂} = ⊢ren (go Γ₁) where
  go : ∀ {m} (Γₘ : Ctx m) x → lookup ((Γₘ ⸴* Γ₂) ⸴* Γ) x ≡ lookup ((T₁ ⸴ Γₘ ⸴* T₂ ⸴ Γ₂) ⸴* Γ) (wkₚ m _ x)
  go [] x rewrite Fin.cast-is-id refl x | Fin.cast-is-id refl x = refl
  go (T ⸴ Γₘ) zero = refl
  go (T ⸴ Γₘ) (suc x) = go Γₘ x

𝔽-cast-injective : ∀ {m n} {x y : 𝔽 m} → .(eq : m ≡ n) → Fin.cast eq x ≡ Fin.cast eq y → x ≡ y
𝔽-cast-injective {suc m} {suc n} {zero} {zero} eq eq′ = refl
𝔽-cast-injective {suc m} {suc n} {suc x} {suc y} eq eq′ = cong suc (𝔽-cast-injective (suc⁻¹ eq) (Fin.suc-injective eq′))

wkₚ-inj : ∀ m₁ m₂ n → 𝐂.Inj (wkₚ {n} m₁ m₂)
wkₚ-inj zero m₂ n = 𝔽-cast-injective refl ∘ 𝔽-cast-injective refl ∘ Fin.suc-injective ∘ Fin.suc-injective
wkₚ-inj (suc m₁) m₂ n {zero} {zero} eq = refl
wkₚ-inj (suc m₁) m₂ n {suc x} {suc y} eq = cong suc (wkₚ-inj m₁ m₂ n (Fin.suc-injective eq))
