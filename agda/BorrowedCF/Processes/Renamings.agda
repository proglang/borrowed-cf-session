module BorrowedCF.Processes.Renamings where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Vec.Functional as F using ()

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Terms as Terms
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open ≡-Reasoning

{-
record ⊢SplitRenamings : Set where
  field
    B₁ B₂ : BindGroup
    m {b} {n} : ℕ

  field
    Γ₁ : Ctx (sum B₁)
    Γ₂ : Ctx (sum B₂)
    Γb : Ctx (suc b)
    Γₘ : Ctx m
    Γₙ : Ctx n
    {Γ}  : Ctx (sum (B₁ ++ suc b ∷ B₂))
    {Γ′} : Ctx (sum (B₁ ++ 1 ∷ suc b ∷ B₂))
    {T}  : 𝕋

  module 𝐒  = SplitRenamings   B₁ B₂ m
  module 𝐒ᶜ = 𝐂.SplitRenamings B₁ B₂ m

  field
    Γ≗  : Γ  ≗ (Γ₁ ⸴* Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (suc b ∷ B₂))
    Γ′≗ : Γ′ ≗ (Γ₁ ⸴* T ⸴ Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (1 ∷ suc b ∷ B₂))

  {-
  wkRSplit-lookup : (Γ ⸴* Γₘ) ⸴* Γₙ ≗ ((Γ′ ⸴* Γₘ) ⸴* Γₙ) ∘ 𝐒ᶜ.wkRSplit
  wkRSplit-lookup = {!!}
  -}
-}

wkRSplit-lookup :
    (B₁ B₂ : BindGroup)
    (m : ℕ) {b n : ℕ}
    (Γ₁ : Ctx (sum B₁))
    (Γ₂ : Ctx (sum B₂))
    (Γb : Ctx (suc b))
    (Γₘ : Ctx m)
    (Γₙ : Ctx n)
    {Γ  : Ctx (sum (B₁ ++ suc b ∷ B₂))}
    {Γ′ : Ctx (sum (B₁ ++ 1 ∷ suc b ∷ B₂))} →
    Γ  ≗ (Γ₁ ⸴* Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (suc b ∷ B₂)) →
    Γ′ ≗ (Γ₁ ⸴* T ⸴ Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (1 ∷ suc b ∷ B₂)) →
  (Γ ⸴* Γₘ) ⸴* Γₙ ≗ ((Γ′ ⸴* Γₘ) ⸴* Γₙ) ∘ SplitRenamings.rwk B₁ B₂ m {q = 0}
wkRSplit-lookup {T = T} [] B₂ m {b} {n} Γ₁ Γ₂ Γb Γₘ Γₙ {Γ} {Γ′} Γ-eq Γ′-eq x
  rewrite Fin.cast-is-id refl x | Fin.cast-is-id refl x =
  ((Γ ⸴* Γₘ) ⸴* Γₙ) x
    ≡⟨ [-,]-cong ([-,]-cong (λ y → Γ-eq y ■ cong (Γb ⸴* Γ₂) (Fin.cast-is-id refl y)) ∘ splitAt (suc b + sum B₂))
                 (splitAt (suc b + sum B₂ + m) x) ⟩
  [ [ (Γ₁ ⸴* Γb ⸴* Γ₂) , Γₘ ] ∘ splitAt _ , Γₙ ] (splitAt _ x)
    ≡⟨⟩
  [ [ (Γ₁ ⸴* T ⸴ Γb ⸴* Γ₂) ∘ suc , Γₘ ] ∘ splitAt _ , Γₙ ] (splitAt _ x)
    ≡⟨ [-,]-cong ([-,]-cong (λ y → Γ′-eq (suc y) ■ cong (Γb ⸴* Γ₂) (Fin.cast-is-id refl y)) ∘ splitAt (suc b + sum B₂))
                 (splitAt (suc b + sum B₂ + m) x) ⟨
  [ [ Γ′ ∘ suc , Γₘ ] ∘ splitAt _ , Γₙ ] (splitAt _ x)
    ≡⟨ [-,]-cong ([,]-map ∘ splitAt (suc b + sum B₂)) (splitAt (suc b + sum B₂ + m) x) ⟨
  [ (Γ′ ⸴* Γₘ) ∘ suc , Γₙ ] (splitAt _ x)
    ≡⟨ [,]-map (splitAt (suc b + sum B₂ + m) x) ⟨
  [ Γ′ ⸴* Γₘ , Γₙ ] (Sum.map₁ suc (splitAt _ x)) ∎
wkRSplit-lookup {T} (zero ∷ B₁) = wkRSplit-lookup B₁
wkRSplit-lookup {T} (suc b₁ ∷ B₁) B₂ m {b} {n} Γ₁ Γ₂ Γb Γₘ Γₙ {Γ} {Γ′} Γ-eq Γ′-eq zero = Γ-eq zero ■ sym (Γ′-eq zero)
wkRSplit-lookup {T} (suc b₁ ∷ B₁) B₂ m {b} {n} Γ₁ Γ₂ Γb Γₘ Γₙ {Γ} {Γ′} Γ-eq Γ′-eq (suc x) =
  let open SplitRenamings (suc b₁ ∷ B₁) B₂ m in
  let IH = wkRSplit-lookup {T} (b₁ ∷ B₁) B₂ m (Γ₁ ∘ suc) Γ₂ Γb Γₘ Γₙ
             (λ y → Γ-eq (suc y) ■ [,]-map (splitAt (b₁ + sum B₁) (Fin.cast _ y)))
             (λ y → Γ′-eq (suc y) ■ [,]-map (splitAt (b₁ + sum B₁) (Fin.cast _ y)))
  in
  let arg₂ = splitAt (b₁ + sum (B₁ ++ 1 ∷ suc b ∷ B₂) + m) (SplitRenamings.rwk (b₁ ∷ B₁) B₂ m {q = 0} x)
  in
  ((Γ ⸴* Γₘ) ⸴* Γₙ) (suc x)
    ≡⟨⟩
  [ Γ ⸴* Γₘ , Γₙ ] (Sum.map₁ suc (splitAt _ x))
    ≡⟨ [,]-map (splitAt (b₁ + sum (B₁ ++ suc b ∷ B₂) + m) x) ⟩
  [ (Γ ⸴* Γₘ) ∘ suc , Γₙ ] (splitAt _ x)
    ≡⟨ [-,]-cong ([,]-map ∘ splitAt (b₁ + sum (B₁ ++ suc b ∷ B₂))) (splitAt (b₁ + sum (B₁ ++ suc b ∷ B₂) + m) x) ⟩
  ((Γ ∘ suc ⸴* Γₘ) ⸴* Γₙ) x
    ≡⟨ IH x ⟩
  ((Γ′ ∘ suc ⸴* Γₘ) ⸴* Γₙ) _
    ≡⟨ [-,]-cong ([,]-map ∘ splitAt (b₁ + sum (B₁ ++ 1 ∷ suc b ∷ B₂))) arg₂ ⟨
  [ (Γ′ ⸴* Γₘ) ∘ suc , Γₙ ] arg₂
    ≡⟨ [,]-map arg₂ ⟨
  [ Γ′ ⸴* Γₘ , Γₙ ] (Sum.map₁ suc arg₂)
    ≡⟨⟩
  ((Γ′ ⸴* Γₘ) ⸴* Γₙ) (rwk {q = 0} (suc x)) ∎

wkRSplit-preserves : (P : Pred 𝕋 0ℓ) (B₁ B₂ : BindGroup) (m : ℕ) {b n : ℕ}
  (Γ₁ : Ctx (sum B₁))
  (Γ₂ : Ctx (sum B₂))
  (Γb : Ctx (suc b))
  (Γₘ : Ctx m)
  (Γₙ : Ctx n)
  {Γ  : Ctx (sum (B₁ ++ suc b ∷ B₂))}
  {Γ′ : Ctx (sum (B₁ ++ 1 ∷ suc b ∷ B₂))} →
  Γ  ≗ (Γ₁ ⸴* Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (suc b ∷ B₂)) →
  Γ′ ≗ (Γ₁ ⸴* T ⸴ Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (1 ∷ suc b ∷ B₂)) →
  SplitRenamings.rwk B₁ B₂ m {q = 0} 𝐂.Preserves[ P ] ((Γ ⸴* Γₘ) ⸴* Γₙ) ⇒ ((Γ′ ⸴* Γₘ) ⸴* Γₙ)
wkRSplit-preserves P B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq px = ` subst P (wkRSplit-lookup B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq _) px

⊢wkRSplit : (B₁ B₂ : BindGroup) (m : ℕ) {b n : ℕ}
  (Γ₁ : Ctx (sum B₁))
  (Γ₂ : Ctx (sum B₂))
  (Γb : Ctx (suc b))
  (Γₘ : Ctx m)
  (Γₙ : Ctx n)
  {Γ  : Ctx (sum (B₁ ++ suc b ∷ B₂))}
  {Γ′ : Ctx (sum (B₁ ++ 1 ∷ suc b ∷ B₂))} →
  Γ  ≗ (Γ₁ ⸴* Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (suc b ∷ B₂)) →
  Γ′ ≗ (Γ₁ ⸴* T ⸴ Γb ⸴* Γ₂) ∘ Fin.cast (sum-++ B₁ (1 ∷ suc b ∷ B₂)) →
  SplitRenamings.rwk B₁ B₂ m {q = 0} ∶ `_ ∘ SplitRenamings.rwk B₁ B₂ m {q = 0}
    ⊢[ TKᵣ ] (Γ ⸴* Γₘ) ⸴* Γₙ ⇒ (Γ′ ⸴* Γₘ) ⸴* Γₙ
⊢wkRSplit B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq = record
  { _&_   = λ x → refl , sym (wkRSplit-lookup B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq x)
  ; &-unr = wkRSplit-preserves Unr B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq
  ; &-mob = wkRSplit-preserves Mobile B₁ B₂ m Γ₁ Γ₂ Γb Γₘ Γₙ Γ-eq Γ′-eq
  }

wkₚ-lookup : ∀ {m₁ m₂ n} (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) (Γ : Ctx n) →
   (Γ₁ ⸴* Γ₂) ⸴* Γ ≗ ((T₁ ⸴ Γ₁ ⸴* T₂ ⸴ Γ₂) ⸴* Γ) ∘ wkₚ m₁ m₂
wkₚ-lookup {T₁ = T₁}{T₂} {m₁ = zero}{m₂} Γ₁ Γ₂ Γ x
  rewrite Fin.cast-is-id refl x | Fin.cast-is-id refl x =
  (Γ₂ ⸴* Γ) x ≡⟨ [,]-map (splitAt m₂ x) ⟨
  [ T₂ ⸴ Γ₂ , Γ ] (Sum.map₁ suc (splitAt m₂ x)) ≡⟨ [,]-map (Sum.map₁ suc (splitAt m₂ x)) ⟨
  [ T₁ ⸴ T₂ ⸴ Γ₂ , Γ ] (Sum.map₁ suc (Sum.map₁ suc (splitAt m₂ x))) ∎
wkₚ-lookup {m₁ = suc m₁} Γ₁ Γ₂ Γ zero = refl
wkₚ-lookup {T₁ = T₁}{T₂} {m₁ = suc m₁}{m₂} Γ₁ Γ₂ Γ (suc x) =
  let IH = wkₚ-lookup {T₁ = T₁}{T₂} (Γ₁ ∘ suc) Γ₂ Γ x in
  let arg = splitAt (m₁ + suc m₂) (Fin.cast _ ((suc ↑* m₁) (Fin.cast _ x))) in
  ((Γ₁ ⸴* Γ₂) ⸴* Γ) (suc x) ≡⟨ [,]-map (splitAt (m₁ + m₂) x)  ⟩
  ((Γ₁ ⸴* Γ₂) ∘ suc ⸴* Γ) x ≡⟨ [-,]-cong ([,]-map ∘ splitAt m₁) (splitAt (m₁ + m₂) x) ⟩
  ((Γ₁ ∘ suc ⸴* Γ₂) ⸴* Γ) x ≡⟨ IH ⟩
  ((T₁ ⸴ Γ₁ ∘ suc ⸴* T₂ ⸴ Γ₂) ⸴* Γ) (wkₚ m₁ m₂ x) ≡⟨ [,]-map arg ⟩
  [ Γ₁ ∘ suc ⸴* T₂ ⸴ Γ₂ , Γ ] arg ≡⟨ [-,]-cong ([,]-map ∘ splitAt m₁) arg ⟨
  [ (Γ₁ ⸴* T₂ ⸴ Γ₂) ∘ suc , Γ ] arg ≡⟨ [,]-map arg ⟨
  [ Γ₁ ⸴* T₂ ⸴ Γ₂ , Γ ] (Sum.map₁ suc arg) ≡⟨ [,]-map (Sum.map₁ suc arg) ⟨
  [ T₁ ⸴ Γ₁ ⸴* T₂ ⸴ Γ₂ , Γ ] (Sum.map₁ suc (Sum.map₁ suc arg)) ≡⟨⟩
  ((T₁ ⸴ Γ₁ ⸴* T₂ ⸴ Γ₂) ⸴* Γ) (wkₚ (suc m₁) m₂ (suc x)) ∎

⊢wkₚ : ∀ {m₁ m₂ n} (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) (Γ : Ctx n) {T₁ T₂ : 𝕋} →
  wkₚ {n} m₁ m₂ ∶ `_ ∘′ wkₚ {n} m₁ m₂ ⊢[ TKᵣ ] (Γ₁ ⸴* Γ₂) ⸴* Γ ⇒ (T₁ ⸴ Γ₁ ⸴* T₂ ⸴ Γ₂) ⸴* Γ
⊢wkₚ Γ₁ Γ₂ Γ = record
  { _&_   = λ x → refl , sym (wkₚ-lookup Γ₁ Γ₂ Γ x)
  ; &-unr = λ px → ` subst Unr (wkₚ-lookup Γ₁ Γ₂ Γ _) px
  ; &-mob = λ px → ` subst Mobile (wkₚ-lookup Γ₁ Γ₂ Γ _) px
  }

𝔽-cast-injective : ∀ {m n} {x y : 𝔽 m} → .(eq : m ≡ n) → Fin.cast eq x ≡ Fin.cast eq y → x ≡ y
𝔽-cast-injective {suc m} {suc n} {zero} {zero} eq eq′ = refl
𝔽-cast-injective {suc m} {suc n} {suc x} {suc y} eq eq′ = cong suc (𝔽-cast-injective (suc⁻¹ eq) (Fin.suc-injective eq′))

wkₚ-inj : ∀ m₁ m₂ n → 𝐂.Inj (wkₚ {n} m₁ m₂)
wkₚ-inj zero m₂ n = 𝔽-cast-injective refl ∘ 𝔽-cast-injective refl ∘ Fin.suc-injective ∘ Fin.suc-injective
wkₚ-inj (suc m₁) m₂ n {zero} {zero} eq = refl
wkₚ-inj (suc m₁) m₂ n {suc x} {suc y} eq = cong suc (wkₚ-inj m₁ m₂ n (Fin.suc-injective eq))
