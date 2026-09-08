-- | The two abstraction cases of the completeness induction: T-Abs and T-AbsRec (C4).
--
--   Both are CHECKING rules, so the type they are checked against is the goal type, which is
--   solved by hypothesis; `A-Ann` turns the result into an inference.  The body is inferred
--   and `A-Check` compares its type with the (solved) codomain, a constraint the substitution
--   of the body's induction hypothesis already solves.
--
--   Owner: agent C4.
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Decl

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Bin
open import BorrowedCF.Completeness.Main.Interface

import BorrowedCF.Context.Substitution as 𝐂

module BorrowedCF.Completeness.Main.Abs where

open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables
open Fin.Patterns

private
  -- `γ₀ ≼ γ` under one binder, in the idiom of Reduction/Expressions.agda.
  wk≼ : ∀ {n} {Γ : Ctx n} {T : 𝕋} {γ₀ γ : Struct n} →
    Γ ∶ γ₀ ≼ γ → (T ⸴ Γ) ∶ 𝐂.wk γ₀ ≼ 𝐂.wk γ
  wk≼ {Γ = Γ} ≤γ = 𝐂.≼-⋯ (𝐂.⇔→⇒ ⦃ 𝐂.Kₛ ⦄ {Γ} (𝐂.wk-⇔ ⦃ 𝐂.Kₛ ⦄)) ≤γ

  wk²≼ : ∀ {n} {Γ : Ctx n} {T U : 𝕋} {γ₀ γ : Struct n} →
    Γ ∶ γ₀ ≼ γ → (T ⸴ U ⸴ Γ) ∶ 𝐂.wk (𝐂.wk γ₀) ≼ 𝐂.wk (𝐂.wk γ)
  wk²≼ ≤γ = wk≼ (wk≼ ≤γ)

------------------------------------------------------------------------
-- T-Abs.

abs-case : ∀ {n} {e : Tm (suc n)} → IHAt e →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ}
    {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ ƛ e ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (ƛ e) T ϵ m σ₀
abs-case ih {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {m = m} {σ₀ = σ₀} Sσ uΓ ap Se ST lin d
  with inv-ƛ d
... | T₁ , a , U , γ₀ , (eq₁ `→ eq₂) , ≤γ₀ , Γ-unr , Γ-mob , dbody
  with ST₁ ⟨ _ ⟩→ ST₂ ← ST
  with T̂b , ϵb , Δb , k , σ , Sσ′ , ag , SΔb , ϵb≤ , ≃b , m≤k , uvT̂b , uvΔb , derb
     ← ih {Γ = T₁ ⸴ Γ} {Γ̂ = _ ⸴ Γ̂} Sσ
         (uvarsInΓ-⸴ (solved⇒uvarsIn ST₁) uΓ)
         (λ where
            zero    → ≃-trans (≃-reflexive (subTy-id ST₁)) (≃-sym eq₁)
            (suc x) → ap x)
         Se ST₂
         (lin-bind (Arr.dir a) T₁ Γ γ lin)
         (T-Conv eq₂ ≤ϵ-refl
           (T-Weaken (≼-join (Arr.dir a) (≼-refl ≈-refl) (wk≼ ≤γ₀)) dbody))
  = _ , ℙ , _ , k , σ , Sσ′ , ag ,
    solvedΔ-++
      (mobΔ (Arr.mob a) (λ mob≡ → allCx-weaken unr⇒mobile ≤γ₀ (Γ-mob mob≡)))
      (subst (_≃ subTy T̂b σ) (sym (subTy-id ST₂)) (≃-sym ≃b) ∷ SΔb) ,
    ℙ≤ϵ , ≃-reflexive (subTy-id ST) , m≤k , solved⇒uvarsIn ST ,
    uvarsInΔ-++
      (uvarsInΔ-mono Nat.≤-refl m≤k (uvarsInΔ-mobConstraints (Arr.mob a) Γ̂ γ uΓ))
      (C-Eq (solved⇒uvarsIn ST₂) uvT̂b ∷ uvΔb) ,
    A-Ann chk-ƛ (A-Abs (λ u → unrCx→ ap (unrCx-weaken ≤γ₀ (Γ-unr u))) ϵb≤ (A-Check derb) refl)
  where
    -- the mobility constraints of A-Abs.  The declarative `MobCx` transports along the
    -- context approximation (`Mobile` respects `≃`), so this does NOT use `mob-reflect`.
    mobΔ : (𝓂 : Mob) → (𝓂 ≡ M → MobCx Γ γ) → SolvedΔ (mobConstraints 𝓂 Γ̂ γ) σ
    mobΔ M f = allMobile-approx Γ̂ Γ γ (approx-agree {Γ = Γ} {Γ̂ = Γ̂} uΓ ag ap) (f refl)
    mobΔ S f = []


------------------------------------------------------------------------
-- T-AbsRec.  The recursive occurrence has the goal type itself, which is solved.

absrec-case : ∀ {n} {e : Tm (suc (suc n))} → IHAt e →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ}
    {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm (ƛ e) → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ μ (ƛ e) ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (μ (ƛ e)) T ϵ m σ₀
absrec-case ih {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {m = m} {σ₀ = σ₀} Sσ uΓ ap Se ST lin d
  with inv-μ d
... | _ , T₁ , a , U , γ₀ , refl , (eq₁ `→ eq₂) , ≤γ₀ , Γ-unr , a-unr , dbody
  with ST₁ ⟨ _ ⟩→ ST₂ ← ST
  with T̂b , ϵb , Δb , k , σ , Sσ′ , ag , SΔb , ϵb≤ , ≃b , m≤k , uvT̂b , uvΔb , derb
     ← ih {Γ = T₁ ⸴ (T₁ ⟨ a ⟩→ U) ⸴ Γ} {Γ̂ = _ ⸴ _ ⸴ Γ̂} Sσ
         (uvarsInΓ-⸴ (solved⇒uvarsIn ST₁) (uvarsInΓ-⸴ (solved⇒uvarsIn ST) uΓ))
         (λ where
            zero          → ≃-trans (≃-reflexive (subTy-id ST₁)) (≃-sym eq₁)
            (suc zero)    → ≃-trans (≃-reflexive (subTy-id ST)) (≃-sym (eq₁ `→ eq₂))
            (suc (suc x)) → ap x)
         (solvedTm-ƛ Se) ST₂
         (lin-bind-rec T₁ (T₁ ⟨ a ⟩→ U) Γ γ lin)
         (T-Conv eq₂ ≤ϵ-refl (T-Weaken (≼-cong-∥ (≼-refl ≈-refl) (wk²≼ ≤γ₀)) dbody))
  = _ , ℙ , _ , k , σ , Sσ′ , ag ,
    (subst (_≃ subTy T̂b σ) (sym (subTy-id ST₂)) (≃-sym ≃b) ∷ SΔb) ,
    ℙ≤ϵ , ≃-reflexive (subTy-id ST) , m≤k , solved⇒uvarsIn ST ,
    (C-Eq (solved⇒uvarsIn ST₂) uvT̂b ∷ uvΔb) ,
    A-Ann chk-μ (A-AbsRec (unrCx→ ap (unrCx-weaken ≤γ₀ Γ-unr)) a-unr ϵb≤ (A-Check derb))
