module BorrowedCF.Algorithmic.Strengthen where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈⁅y⁆⇒x≡y; p⊆p∪q; q⊆p∪q; ⊆-trans)
import Data.Vec as Vec
open import Data.Vec using (_∷_)
open import Data.Fin using () renaming (zero to fz; suc to fs)

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.DescendAbs using (wk↓'; wk²↓; ↓-join)
open import BorrowedCF.Algorithmic.Split using (fv; fvClose; fvClose*)

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

keep0 : {n : ℕ} → Subset n → Subset (suc n)
keep0 X = inside ∷ X

∈keep0 : {n : ℕ} {X : Subset n} → fz ∈ keep0 X
∈keep0 = Vec.here

∈keep0-s : {n : ℕ} {X : Subset n} {y : 𝔽 n} → y ∈ X → fs y ∈ keep0 X
∈keep0-s y∈ = Vec.there y∈

leaf-keep : {n : ℕ} {X : Subset n} → (` fz) ↓ keep0 X ≡ ` fz
leaf-keep = refl

↓-bind1 : ∀ {A} ⦃ _ : Join A ⦄ {n} (dd : A) (γ : Struct n) (X : Subset n) →
          (join dd (` fz) (𝐂.wk γ)) ↓ keep0 X ≡ join dd (` fz) (𝐂.wk (γ ↓ X))
↓-bind1 dd γ X = ↓-join dd (` fz) (𝐂.wk γ) (keep0 X) ■ cong₂ (join dd) (leaf-keep {X = X}) (wk↓' γ (keep0 X))

fvClose-⊆ : {n : ℕ} {X : Subset n} {S : Subset (suc n)} → fvClose S ⊆ X → S ⊆ keep0 X
fvClose-⊆ {S = hd ∷ tl} S⊆ {fz} _ = Vec.here
fvClose-⊆ {S = hd ∷ tl} S⊆ {fs y} (Vec.there y∈) = Vec.there (S⊆ y∈)

keep01 : {n : ℕ} → Subset n → Subset (suc (suc n))
keep01 X = inside ∷ inside ∷ X

leaf01-0 : {n : ℕ} {X : Subset n} → (` fz) ↓ keep01 X ≡ ` fz
leaf01-0 = refl

leaf01-1 : {n : ℕ} {X : Subset n} → (` fs fz) ↓ keep01 X ≡ ` fs fz
leaf01-1 = refl

↓-absrec : {n : ℕ} (γ : Struct n) (X : Subset n) →
  ((` fz) ∥ (` fs fz) ∥ 𝐂.wk (𝐂.wk γ)) ↓ keep01 X ≡ (` fz) ∥ (` fs fz) ∥ 𝐂.wk (𝐂.wk (γ ↓ X))
↓-absrec γ X = cong₂ _∥_ (cong₂ _∥_ (leaf01-0 {X = X}) (leaf01-1 {X = X})) (wk²↓ γ (keep01 X))

↓-letpair : ∀ {A} ⦃ _ : Join A ⦄ {n} (ps : A) (dr : Dir) (γ : Struct n) (X : Subset n) →
  (join ps (join dr (` fz) (` fs fz)) (𝐂.wk (𝐂.wk γ))) ↓ keep01 X
  ≡ join ps (join dr (` fz) (` fs fz)) (𝐂.wk (𝐂.wk (γ ↓ X)))
↓-letpair ps dr γ X = ↓-join ps (join dr (` fz) (` fs fz)) (𝐂.wk (𝐂.wk γ)) (keep01 X)
  ■ cong₂ (join ps) (↓-join dr (` fz) (` fs fz) (keep01 X) ■ cong₂ (join dr) (leaf01-0 {X = X}) (leaf01-1 {X = X})) (wk²↓ γ (keep01 X))

fvClose*2-⊆ : {n : ℕ} {X : Subset n} {S : Subset (suc (suc n))} → fvClose* 2 S ⊆ X → S ⊆ keep01 X
fvClose*2-⊆ {S = a ∷ b ∷ Ss} h {fz} _ = Vec.here
fvClose*2-⊆ {S = a ∷ b ∷ Ss} h {fs fz} _ = Vec.there Vec.here
fvClose*2-⊆ {S = a ∷ b ∷ Ss} h {fs (fs y)} (Vec.there (Vec.there y∈)) = Vec.there (Vec.there (h y∈))

⊢-↓ : {n : ℕ} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} {X : Subset n} →
      fv e ⊆ X → Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; (γ ↓ X) ⊢ e ∶ T ∣ ϵ
⊢-↓ _ (T-Const ⊢c) = T-Const ⊢c
⊢-↓ {X = X} fv⊆ (T-Var x refl) = subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (sym (↓-identity-⊆ (` x) λ z∈ → subst (_∈ X) (sym (x∈⁅y⁆⇒x≡y x z∈)) (fv⊆ (x∈⁅x⁆ x)))) (T-Var x refl)
⊢-↓ {γ = γ} fv⊆ (T-Abs {a = a} Γ-unr Γ-mob d) =
  T-Abs (allCx-↓ ∘ Γ-unr) (allCx-↓ ∘ Γ-mob)
    (subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (↓-bind1 (Arr.dir a) γ _) (⊢-↓ (fvClose-⊆ fv⊆) d))
⊢-↓ {γ = γ} fv⊆ (T-AppUnr {e₁ = e₁} {e₂ = e₂} a-unr ≤ₐ d₁ d₂) =
  T-AppUnr a-unr ≤ₐ (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂)
⊢-↓ {γ = γ} fv⊆ (T-AppLin {e₁ = e₁} {e₂ = e₂} a-par ≤ₐ d₁ d₂) =
  T-AppLin a-par ≤ₐ (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂)
⊢-↓ {γ = γ} fv⊆ (T-AppLeft {e₁ = e₁} {e₂ = e₂} aL ≤ₐ d₁ d₂) =
  T-AppLeft aL ≤ₐ (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂)
⊢-↓ {γ = γ} fv⊆ (T-AppRight {e₁ = e₁} {e₂ = e₂} aR ≤ₐ d₁ d₂) =
  T-AppRight aR ≤ₐ (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂)
⊢-↓ {X = X} fv⊆ (T-Pair {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} seq⇒p d₁ d₂) =
  subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (sym (↓-join (biasedDir p/s) γ₁ γ₂ X))
    (T-Pair p/s seq⇒p (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂))
⊢-↓ {γ = γ} fv⊆ (T-Seq {e₁ = e₁} {e₂ = e₂} unr-T d₁ d₂) =
  T-Seq unr-T (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁) (⊢-↓ (⊆-trans (q⊆p∪q _ _) fv⊆) d₂)
⊢-↓ fv⊆ (T-Inj d) = T-Inj (⊢-↓ fv⊆ d)
⊢-↓ fv⊆ (T-Conv T≃ ϵ≤ d) = T-Conv T≃ ϵ≤ (⊢-↓ fv⊆ d)
⊢-↓ fv⊆ (T-Weaken γ≤ d) = T-Weaken (↓-mono-≼ γ≤) (⊢-↓ fv⊆ d)
⊢-↓ {Γ = Γ} {γ = γ} {e = μ (ƛ eb)} {X = X} fv⊆ (T-AbsRec {a = a} {T = T} {U = U} Γ-unr a-unr d) =
  T-AbsRec (allCx-↓ Γ-unr) a-unr (subst (λ z → (T ⸴ (T ⟨ a ⟩→ U) ⸴ Γ) ; z ⊢ eb ∶ U ∣ Arr.eff a) (↓-absrec γ X) (⊢-↓ {X = keep01 X} (fvClose-⊆ (fvClose-⊆ fv⊆)) d))
⊢-↓ {X = X} fv⊆ (T-Let {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) =
  subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (sym (↓-join p/s γ₁ γ₂ X))
    (T-Let p/s (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁)
      (subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (↓-bind1 p/s γ₂ X) (⊢-↓ (fvClose-⊆ (⊆-trans (q⊆p∪q _ _) fv⊆)) d₂)))
⊢-↓ {X = X} fv⊆ (T-LetPair {e₁ = e₁} {d = dr} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) =
  subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (sym (↓-join p/s γ₁ γ₂ X))
    (T-LetPair p/s (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) d₁)
      (subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (↓-letpair p/s dr γ₂ X) (⊢-↓ (fvClose*2-⊆ (⊆-trans (q⊆p∪q _ _) fv⊆)) d₂)))
⊢-↓ {X = X} fv⊆ (T-Case {e = ec} {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} de d₁ d₂) =
  subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (sym (↓-join p/s γ₁ γ₂ X))
    (T-Case p/s (⊢-↓ (⊆-trans (p⊆p∪q _) fv⊆) de)
      (subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (↓-bind1 p/s γ₂ X) (⊢-↓ (fvClose-⊆ (⊆-trans (p⊆p∪q _) (⊆-trans (q⊆p∪q _ _) fv⊆))) d₁))
      (subst (λ z → _ ; z ⊢ _ ∶ _ ∣ _) (↓-bind1 p/s γ₂ X) (⊢-↓ (fvClose-⊆ (⊆-trans (q⊆p∪q _ _) (⊆-trans (q⊆p∪q _ _) fv⊆))) d₂)))
