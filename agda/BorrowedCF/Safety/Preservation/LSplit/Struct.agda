------------------------------------------------------------------------
-- P3c, step 3a: the binder structure of a WIDTH-ONE group under `zap`.
--
-- `Splits/Struct.agda`'s `sb-lsplit` pushes the OLD binder structure along
-- the substitution that expands the consumed handle into `` ` x; ; ` x; ``.  For a
-- mobile handle that substitution is not a legal `⇒` (the two halves are
-- not mobile), so the mobile case erases the handle instead: `z` sends it to
-- `[]` and every other variable along `lwk`.  `sb-zap` says what the erased
-- structure is worth, namely everything but the handle:
--
--     d ∥ (structBinder (B₁ ++ 1 ∷ B₂) ⋯ z)  ≈  structBinder (B₁ ++ 2 ∷ B₂) ⋯ g
--
-- with `d = g j₁ ; g j₂` the pair the split returns.  The group has width
-- ONE, so its own contribution is `` ` h ; [] `` and the handle really is a
-- top-level `∥`-component -- this is the general-position form of
-- `Handles/Acq.agda`'s `fr-split`, which is the same statement at index
-- `0F`.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit.Struct where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed using (BindGroup; structBinder; structNSeq)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open import BorrowedCF.Safety.Preservation.Splits.Struct
  using (⋯ᵣₛ; ⋯ₛ-cong; seqOf; seqOf-cong; nseq-seqOf)

open Nat.Variables
open Fin.Patterns

private variable N : ℕ

private
  swap₁ : ∀ {Γ : Ctx N} {a b c : Struct N} → Γ ∶ a ∥ (b ∥ c) ≈ b ∥ (a ∥ c)
  swap₁ = ≈-trans (≈-sym ∥-assoc) (≈-trans (∥-cong ∥-comm ≈-refl) ∥-assoc)

sb-zap : ∀ {Γ : Ctx N} (B₁ B₂ : BindGroup) {p : ℕ} → sum B₁ ≡ p →
  (z : 𝔽 (sum (B₁ ++ 1 ∷ B₂)) → Struct N)
  (g : 𝔽 (sum (B₁ ++ 2 ∷ B₂)) → Struct N)
  (d : Struct N) →
  (lo  : ∀ j j′ → Fin.toℕ j Nat.< p → Fin.toℕ j′ ≡ Fin.toℕ j → z j ≡ g j′) →
  (atz : ∀ j → Fin.toℕ j ≡ p → z j ≡ []) →
  (atg : ∀ j₁ j₂ → Fin.toℕ j₁ ≡ p → Fin.toℕ j₂ ≡ suc p → (g j₁ ; g j₂) ≡ d) →
  (hi  : ∀ j j′ → p Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) → z j ≡ g j′) →
  Γ ∶ d ∥ (structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ₛ z)
    ≈ structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ₛ g
sb-zap {Γ = Γ} [] B₂ refl z g d lo atz atg hi =
  ≈-trans (≈-reflexive (cong (d ∥_) (cong₂ _∥_ eqLz eqT)))
  (≈-trans lhs≈
  (≈-trans (≈-sym rhs≈) (≈-reflexive (cong₂ _∥_ (sym eqR) refl))))
  where
    j₁ j₂ : 𝔽 (2 + sum B₂)
    j₁ = 0F ↑ˡ sum B₂
    j₂ = 1F ↑ˡ sum B₂
    Tl : Struct _
    Tl = (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ 2) 𝐂.⋯ₛ g
    eqLz : (structNSeq 1 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ₛ z ≡ ([] ; [])
    eqLz = ⋯ᵣₛ (structNSeq 1) (𝐂.wkʳ (sum B₂)) z
         ■ nseq-seqOf 1 (z ∘ 𝐂.wkʳ (sum B₂))
         ■ cong₂ _;_ (atz (0F ↑ˡ sum B₂) (Fin.toℕ-↑ˡ (Fin.zero {n = 0}) (sum B₂))) refl
    eqR : (structNSeq 2 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)) 𝐂.⋯ₛ g ≡ (g j₁ ; (g j₂ ; []))
    eqR = ⋯ᵣₛ (structNSeq 2) (𝐂.wkʳ (sum B₂)) g
        ■ nseq-seqOf 2 (g ∘ 𝐂.wkʳ (sum B₂))
    tailEq : ∀ r → z (1 ↑ʳ r) ≡ g (2 ↑ʳ r)
    tailEq r = hi (1 ↑ʳ r) (2 ↑ʳ r)
                  (subst (0 Nat.<_) (sym (Fin.toℕ-↑ʳ 1 r)) Nat.z<s)
                  (Fin.toℕ-↑ʳ 2 r ■ cong suc (sym (Fin.toℕ-↑ʳ 1 r)))
    eqT : (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ 1) 𝐂.⋯ₛ z ≡ Tl
    eqT = ⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ 1) z
        ■ ⋯ₛ-cong (structBinder B₂) tailEq
        ■ sym (⋯ᵣₛ (structBinder B₂) (𝐂.wkˡ 2) g)
    lhs≈ : Γ ∶ d ∥ (([] ; []) ∥ Tl) ≈ d ∥ Tl
    lhs≈ = ∥-cong ≈-refl (≈-trans (∥-cong ;-unit₁ ≈-refl) ∥-unit₁)
    rhs≈ : Γ ∶ (g j₁ ; (g j₂ ; [])) ∥ Tl ≈ d ∥ Tl
    rhs≈ = ∥-cong (≈-trans (≈-sym ;-assoc)
                  (≈-trans (≈-reflexive (cong₂ _;_ (atg j₁ j₂
                              (Fin.toℕ-↑ˡ (Fin.zero {n = 1}) (sum B₂))
                              (Fin.toℕ-↑ˡ (Fin.suc (Fin.zero {n = 0})) (sum B₂))) refl))
                           ;-unit₂))
                 ≈-refl
sb-zap (b₀ ∷ B₁) B₂ {p} peq z g d lo atz atg hi =
  ≈-trans (≈-reflexive (cong (d ∥_) (cong₂ _∥_ headEq eqθ)))
  (≈-trans swap₁
  (≈-trans (∥-cong ≈-refl IH) (≈-reflexive (cong₂ _∥_ refl (sym eqg)))))
  where
    W  = sum (B₁ ++ 1 ∷ B₂)
    W′ = sum (B₁ ++ 2 ∷ B₂)
    b₀≤p : b₀ Nat.≤ p
    b₀≤p = subst (b₀ Nat.≤_) peq (Nat.m≤m+n b₀ (sum B₁))
    hEq : ∀ (j : 𝔽 b₀) → z (j ↑ˡ W) ≡ g (j ↑ˡ W′)
    hEq j = lo (j ↑ˡ W) (j ↑ˡ W′)
               (subst (Nat._< p) (sym (Fin.toℕ-↑ˡ j W)) (Nat.<-≤-trans (Fin.toℕ<n j) b₀≤p))
               (Fin.toℕ-↑ˡ j W′ ■ sym (Fin.toℕ-↑ˡ j W))
    headEq : (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W) 𝐂.⋯ₛ z ≡ (structNSeq b₀ 𝐂.⋯ᵣ 𝐂.wkʳ W′) 𝐂.⋯ₛ g
    headEq = ⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W) z
           ■ ⋯ₛ-cong (structNSeq b₀) hEq
           ■ sym (⋯ᵣₛ (structNSeq b₀) (𝐂.wkʳ W′) g)
    eqθ : (structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ z
            ≡ structBinder (B₁ ++ 1 ∷ B₂) 𝐂.⋯ₛ (z ∘ 𝐂.wkˡ b₀)
    eqθ = ⋯ᵣₛ (structBinder (B₁ ++ 1 ∷ B₂)) (𝐂.wkˡ b₀) z
    eqg : (structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ᵣ 𝐂.wkˡ b₀) 𝐂.⋯ₛ g
            ≡ structBinder (B₁ ++ 2 ∷ B₂) 𝐂.⋯ₛ (g ∘ 𝐂.wkˡ b₀)
    eqg = ⋯ᵣₛ (structBinder (B₁ ++ 2 ∷ B₂)) (𝐂.wkˡ b₀) g
    lo″ : ∀ j j′ → Fin.toℕ j Nat.< sum B₁ → Fin.toℕ j′ ≡ Fin.toℕ j →
          z (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    lo″ j j′ lt e = lo (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< p) (sym (Fin.toℕ-↑ʳ b₀ j))
                         (subst (b₀ + Fin.toℕ j Nat.<_) peq (Nat.+-monoʳ-< b₀ lt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e ■ sym (Fin.toℕ-↑ʳ b₀ j))
    atz″ : ∀ j → Fin.toℕ j ≡ sum B₁ → z (b₀ ↑ʳ j) ≡ []
    atz″ j e = atz (b₀ ↑ʳ j) (Fin.toℕ-↑ʳ b₀ j ■ cong (b₀ +_) e ■ peq)
    atg″ : ∀ j₁ j₂ → Fin.toℕ j₁ ≡ sum B₁ → Fin.toℕ j₂ ≡ suc (sum B₁) →
           (g (b₀ ↑ʳ j₁) ; g (b₀ ↑ʳ j₂)) ≡ d
    atg″ j₁ j₂ e₁ e₂ = atg (b₀ ↑ʳ j₁) (b₀ ↑ʳ j₂)
                           (Fin.toℕ-↑ʳ b₀ j₁ ■ cong (b₀ +_) e₁ ■ peq)
                           (Fin.toℕ-↑ʳ b₀ j₂ ■ cong (b₀ +_) e₂
                             ■ Nat.+-suc b₀ (sum B₁) ■ cong suc peq)
    hi″ : ∀ j j′ → sum B₁ Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j) →
          z (b₀ ↑ʳ j) ≡ g (b₀ ↑ʳ j′)
    hi″ j j′ gt e = hi (b₀ ↑ʳ j) (b₀ ↑ʳ j′)
                       (subst (Nat._< Fin.toℕ (b₀ ↑ʳ j)) peq
                         (subst (b₀ + sum B₁ Nat.<_) (sym (Fin.toℕ-↑ʳ b₀ j))
                           (Nat.+-monoʳ-< b₀ gt)))
                       (Fin.toℕ-↑ʳ b₀ j′ ■ cong (b₀ +_) e
                         ■ Nat.+-suc b₀ (Fin.toℕ j) ■ cong suc (sym (Fin.toℕ-↑ʳ b₀ j)))
    IH = sb-zap B₁ B₂ {sum B₁} refl (z ∘ 𝐂.wkˡ b₀) (g ∘ 𝐂.wkˡ b₀) d lo″ atz″ atg″ hi″
