module BorrowedCF.Algorithmic.Split where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (_∈?_; x∈⁅x⁆; x∈∁p⇒x∉p; ⊆-trans)
import Data.Vec as Vec

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.DescendAbs

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

private variable
  e e₁ e₂ e₃ e′ e₁′ e₂′ : Tm n

open V using () renaming (tail to fvClose; drop to fvClose*) public

fv : Tm n → Subset n
fv (` x) = ⁅ x ⁆
fv (K c) = ⁅⁆
fv (ƛ e) = fvClose (fv e)
fv (μ e) = fvClose (fv e)
fv (e₁ ·⟨ _ ⟩ e₂) = fv e₁ ∪ fv e₂
fv (e₁ ; e₂) = fv e₁ ∪ fv e₂
fv (e₁ ⊗ e₂) = fv e₁ ∪ fv e₂
fv (`let e₁ `in e₂) = fv e₁ ∪ fvClose (fv e₂)
fv (`let⊗ e₁ `in e₂) = fv e₁ ∪ fvClose* 2 (fv e₂)
fv (`inj i e) = fv e
fv (`case e `of⟨ e₁ ; e₂ ⟩) = fv e ∪ fvClose (fv e₁) ∪ fvClose (fv e₂)

_∣fv[_] : Struct n → Tm n → Struct n
γ ∣fv[ e ] = γ ↓ fv e

-- A well-typed term's context, restricted to the complement of its free
-- variables, is entirely unrestricted: the linear footprint of e is exactly
-- its free variables.

binder1-Unr : ∀ {A} ⦃ _ : Join A ⦄ {n} {Γ : Ctx n} {T₀ : 𝕋} (dd : A) (γ : Struct n) (eb : Tm (suc n)) →
  AllCx Unr (T₀ ⸴ Γ) ((join dd (` Fin.zero) (𝐂.wk γ)) ↓ ∁ (fv eb)) →
  AllCx Unr Γ (γ ↓ ∁ (fvClose (fv eb)))
binder1-Unr {T₀ = T₀} dd γ eb IH =
  un-wk-Unr (subst (AllCx Unr (T₀ ⸴ _))
    (wk↓' γ (∁ (fv eb)) ■ cong (λ z → 𝐂.wk (γ ↓ z)) (tail-∁ (fv eb)))
    (allCx-join↓-proj₂ dd (∁ (fv eb)) IH))

drop2≡tail² : (X : Subset (2 + n)) → fvClose* 2 X ≡ fvClose (fvClose X)
drop2≡tail² (a Vec.∷ b Vec.∷ X) = refl

binder2-Unr : ∀ {A} ⦃ _ : Join A ⦄ {n} {Γ : Ctx n} {T₀ T₁ : 𝕋} (dd : A) {Fr : Struct (suc (suc n))} (γ : Struct n) (eb : Tm (suc (suc n))) →
  AllCx Unr (T₁ ⸴ T₀ ⸴ Γ) ((join dd Fr (𝐂.wk (𝐂.wk γ))) ↓ ∁ (fv eb)) →
  AllCx Unr Γ (γ ↓ ∁ (fvClose* 2 (fv eb)))
binder2-Unr {T₀ = T₀} {T₁ = T₁} dd γ eb IH =
  subst (λ z → AllCx Unr _ (γ ↓ ∁ z)) (sym (drop2≡tail² (fv eb)))
    (un-wk-Unr (un-wk-Unr (subst (AllCx Unr (T₁ ⸴ T₀ ⸴ _))
      (wk²↓ γ (∁ (fv eb)) ■ cong (λ z → 𝐂.wk (𝐂.wk (γ ↓ z))) (tail²-∁ (fv eb)))
      (allCx-join↓-proj₂ dd (∁ (fv eb)) IH))))

typed⇒complement-Unr : ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → AllCx Unr Γ (γ ↓ ∁ (fv e))
typed⇒complement-Unr (T-Const ⊢c) = []
typed⇒complement-Unr {Γ = Γ} (T-Var x refl) with x ∈? ∁ ⁅ x ⁆
... | yes x∈ = contradiction (x∈∁p⇒x∉p x∈ (x∈⁅x⁆ x)) (λ z → z)
... | no  _  = []
typed⇒complement-Unr {γ = γ} {e = ƛ eb} (T-Abs {a = a} _ _ d) =
  binder1-Unr (Arr.dir a) γ eb (typed⇒complement-Unr d)
typed⇒complement-Unr {γ = γ} {e = μ (ƛ eb)} (T-AbsRec _ _ d) with typed⇒complement-Unr d
... | (_ ∥ v) = un-wk-Unr (un-wk-Unr (subst (AllCx Unr _)
    (wk²↓ γ (∁ (fv eb)) ■ cong (λ z → 𝐂.wk (𝐂.wk (γ ↓ z))) (tail²-∁ (fv eb))) v))
typed⇒complement-Unr {γ = γ₁ ∥ γ₂} (T-AppUnr {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁)
  ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)
typed⇒complement-Unr {γ = γ₁ ∥ γ₂} (T-AppLin {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁)
  ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)
typed⇒complement-Unr {γ = γ₂ ; γ₁} (T-AppLeft {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) =
  ↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)
  ; ↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁)
typed⇒complement-Unr {γ = γ₁ ; γ₂} (T-AppRight {e₁ = e₁} {e₂ = e₂} _ _ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁)
  ; ↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)
typed⇒complement-Unr {γ = γ} (T-Pair {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} _ d₁ d₂) =
  subst (AllCx Unr _) (sym (↓-join (biasedDir p/s) γ₁ γ₂ (∁ (fv e₁ ∪ fv e₂))))
    (allCx-join⁺ (biasedDir p/s)
      (↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁))
      (↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)))
typed⇒complement-Unr {γ = γ} (T-Let {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) =
  subst (AllCx Unr _) (sym (↓-join p/s γ₁ γ₂ (∁ (fv e₁ ∪ fvClose (fv e₂)))))
    (allCx-join⁺ p/s
      (↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fvClose (fv e₂))) (typed⇒complement-Unr d₁))
      (↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fvClose (fv e₂))) (binder1-Unr p/s γ₂ e₂ (typed⇒complement-Unr d₂))))
typed⇒complement-Unr {γ = γ₁ ; γ₂} (T-Seq {e₁ = e₁} {e₂ = e₂} _ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₁)
  ; ↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fv e₂)) (typed⇒complement-Unr d₂)
typed⇒complement-Unr {γ = γ} (T-LetPair {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} d₁ d₂) =
  subst (AllCx Unr _) (sym (↓-join p/s γ₁ γ₂ (∁ (fv e₁ ∪ fvClose* 2 (fv e₂)))))
    (allCx-join⁺ p/s
      (↓-⊆ γ₁ (∁-∪-⊆ˡ (fv e₁) (fvClose* 2 (fv e₂))) (typed⇒complement-Unr d₁))
      (↓-⊆ γ₂ (∁-∪-⊆ʳ (fv e₁) (fvClose* 2 (fv e₂))) (binder2-Unr p/s γ₂ e₂ (typed⇒complement-Unr d₂))))
typed⇒complement-Unr (T-Inj d) = typed⇒complement-Unr d
typed⇒complement-Unr {γ = γ} (T-Case {e = ec} {e₁ = e₁} {e₂ = e₂} p/s {γ₁} {γ₂} de d₁ d₂) =
  subst (AllCx Unr _) (sym (↓-join p/s γ₁ γ₂ (∁ (fv ec ∪ fvClose (fv e₁) ∪ fvClose (fv e₂)))))
    (allCx-join⁺ p/s
      (↓-⊆ γ₁ (∁-∪-⊆ˡ (fv ec) (fvClose (fv e₁) ∪ fvClose (fv e₂))) (typed⇒complement-Unr de))
      (↓-⊆ γ₂ (⊆-trans (∁-∪-⊆ʳ (fv ec) (fvClose (fv e₁) ∪ fvClose (fv e₂))) (∁-∪-⊆ˡ (fvClose (fv e₁)) (fvClose (fv e₂))))
         (binder1-Unr p/s γ₂ e₁ (typed⇒complement-Unr d₁))))
typed⇒complement-Unr (T-Conv _ _ d) = typed⇒complement-Unr d
typed⇒complement-Unr (T-Weaken γ≤ d) =
  allCx-weaken (λ u → u) (↓-mono-≼ γ≤) (typed⇒complement-Unr d)

-- A well-typed term is still typed under its context restricted to its free
-- variables, and that restriction is a subcontext (sound, no uniqueness needed).
own-≼ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) → Γ ∶ γ ↓ fv e ≼ γ
own-≼ {γ = γ} d = ↓-strip≼ γ (typed⇒complement-Unr d)
