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
