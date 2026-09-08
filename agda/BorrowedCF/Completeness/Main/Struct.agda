-- | Three more cases of the completeness induction: T-Seq, T-Pair, T-Inj (agent C4).
--
--   T-Seq is a binary INFERENCE node (`Main/Bin.agda` does the structure work).  T-Pair and
--   T-Inj are checking rules, so they are checked against the (solved) goal type and turned
--   into inferences by `A-Ann`.
--
--   Owner: agent C4.
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Scope
open import BorrowedCF.Completeness.Split
open import BorrowedCF.Completeness.Decl

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Bin
open import BorrowedCF.Completeness.Main.Interface

module BorrowedCF.Completeness.Main.Struct where

open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables

private
  if-≃ : ∀ {T₁ T₂ U₁ U₂ : 𝕋} (i : Side) → T₁ ≃ U₁ → T₂ ≃ U₂ →
    (if i then T₁ else T₂) ≃ (if i then U₁ else U₂)
  if-≃ true  p q = p
  if-≃ false p q = q

------------------------------------------------------------------------
-- T-Seq.

seq-case : ∀ {n} {e₁ e₂ : Tm n} → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ}
    {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e₁ ; e₂ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (e₁ ; e₂) T ϵ m σ₀
seq-case {e₁ = e₁} {e₂ = e₂} ih₁ ih₂ {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {m = m} Sσ uΓ ap Se₁ Se₂ ST lin d
  with α , β , T₀ , unrT₀ , ≤γ , d₁ , d₂ ← inv-; d
  with T̂₁ , ϵ₁ , Δ₁ , m′ , σ₁ , Sσ₁ , ag₁ , SΔ₁ , ϵ₁≤ , ≃₁ , m≤m′ , uvT̂₁ , uvΔ₁ , der₁
     ← ih₁ Sσ uΓ (approx-sub {Γ̂ = Γ̂} {Γ = Γ} Sσ ap) Se₁ (subTy-solved T₀ s₀-solving)
          (lin-sub Γ (γ ↓ (fv e₁)) (lin-↓ Γ γ (fv e₁) lin))
          (solve-ty Se₁ (split-left L lin ≤γ d₁ d₂))
  with T̂₂ , ϵ₂ , Δ₂ , k , σ₂ , Sσ₂ , ag₂ , SΔ₂ , ϵ₂≤ , ≃₂ , m′≤k , uvT̂₂ , uvΔ₂ , der₂
     ← ih₂ Sσ₁ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ) (approx-agree {Γ = Γ} {Γ̂ = Γ̂} uΓ ag₁ ap) Se₂ ST
          (lin-↓ Γ γ (fv e₂) lin)
          (split-right L lin ≤γ d₁ d₂)
  = let Lft = ≼→ Sσ ap uΓ (split-≤γ L lin ≤γ d₁ d₂)
        AG  = agree-trans (agree-narrow m≤m′ ag₂) ag₁
    in _ , _ , _ , k , σ₂ , Sσ₂ , AG ,
       solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
                  (solvedΔ-++ (solvedΔ-agree (agree-sym ag₂) uvΔ₁ SΔ₁) SΔ₂) ,
       ⊔ϵ-lub ϵ₁≤ ϵ₂≤ , ≃₂ , Nat.≤-trans m≤m′ m′≤k , uvT̂₂ ,
       uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m≤m′ m′≤k) (csc Lft))
                   (uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl m′≤k uvΔ₁) uvΔ₂) ,
       A-Seq (unr-approx ≃₁ (subTy-unr unrT₀)) (der Lft) der₁ der₂

------------------------------------------------------------------------
-- T-Pair.

pair-case : ∀ {n} {e₁ e₂ : Tm n} → IHAt e₁ → IHAt e₂ →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {T : 𝕋} {ϵ : Eff} {m : ℕ}
    {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e₁ → SolvedTm e₂ → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ e₁ ⊗ e₂ ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (e₁ ⊗ e₂) T ϵ m σ₀
pair-case {e₁ = e₁} {e₂ = e₂} ih₁ ih₂ {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {m = m} Sσ uΓ ap Se₁ Se₂ ST lin d
  with inv-⊗ d
... | par , α , β , T₁ , T₂ , ϵ₁₀ , ϵ₂₀ , ≤γ , (eq₁ ⊗ eq₂) , ϵ≤ , par , d₁ , d₂
  with ST₁ ⊗⟨ _ ⟩ ST₂ ← ST
  with T̂₁ , ϵ₁ , Δ₁ , m′ , σ₁ , Sσ₁ , ag₁ , SΔ₁ , ϵ₁≤ , ≃₁ , m≤m′ , uvT̂₁ , uvΔ₁ , der₁
     ← ih₁ Sσ uΓ ap Se₁ ST₁ (lin-↓ Γ γ (fv e₁) lin)
          (T-Conv eq₁ ≤ϵ-refl (split-left 𝟙 lin ≤γ d₁ d₂))
  with T̂₂ , ϵ₂ , Δ₂ , k , σ₂ , Sσ₂ , ag₂ , SΔ₂ , ϵ₂≤ , ≃₂ , m′≤k , uvT̂₂ , uvΔ₂ , der₂
     ← ih₂ Sσ₁ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ) (approx-agree {Γ = Γ} {Γ̂ = Γ̂} uΓ ag₁ ap) Se₂ ST₂
          (lin-↓ Γ γ (fv e₂) lin)
          (T-Conv eq₂ ≤ϵ-refl (split-right 𝟙 lin ≤γ d₁ d₂))
  = let Lft = ≼→ Sσ ap uΓ (split-≤γ 𝟙 lin ≤γ d₁ d₂)
        AG  = agree-trans (agree-narrow m≤m′ ag₂) ag₁
    in _ , _ , _ , k , σ₂ , Sσ₂ , AG ,
       solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
         (solvedΔ-++
           (solvedΔ-agree (agree-sym ag₂) (C-Eq (solved⇒uvarsIn ST₁) uvT̂₁ ∷ uvΔ₁)
             (subst (_≃ subTy T̂₁ σ₁) (sym (subTy-id ST₁)) (≃-sym ≃₁) ∷ SΔ₁))
           (subst (_≃ subTy T̂₂ σ₂) (sym (subTy-id ST₂)) (≃-sym ≃₂) ∷ SΔ₂)) ,
       ⊔ϵ-lub (≤ϵ-trans ϵ₁≤ ϵ≤) (≤ϵ-trans ϵ₂≤ ϵ≤) ,
       ≃-reflexive (subTy-id ST) , Nat.≤-trans m≤m′ m′≤k , solved⇒uvarsIn ST ,
       uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m≤m′ m′≤k) (csc Lft))
         (uvarsInΔ-++
           (uvarsInΔ-mono Nat.≤-refl m′≤k (C-Eq (solved⇒uvarsIn ST₁) uvT̂₁ ∷ uvΔ₁))
           (C-Eq (solved⇒uvarsIn ST₂) uvT̂₂ ∷ uvΔ₂)) ,
       A-Ann chk-⊗ (A-Pair par (der Lft) (λ ()) (A-Check der₁) (A-Check der₂))
pair-case {e₁ = e₁} {e₂ = e₂} ih₁ ih₂ {Γ = Γ} {Γ̂ = Γ̂} {γ = γ} {m = m} Sσ uΓ ap Se₁ Se₂ ST lin d
  | seq , α , β , T₁ , T₂ , ϵ₁₀ , ϵ₂₀ , ≤γ , (eq₁ ⊗ eq₂) , ϵ≤ , seq , d₁ , d₂
  with ST₁ ⊗⟨ _ ⟩ ST₂ ← ST
  with T̂₁ , ϵ₁ , Δ₁ , m′ , σ₁ , Sσ₁ , ag₁ , SΔ₁ , ϵ₁≤ , ≃₁ , m≤m′ , uvT̂₁ , uvΔ₁ , der₁
     ← ih₁ Sσ uΓ ap Se₁ ST₁ (lin-↓ Γ γ (fv e₁) lin)
          (T-Conv eq₁ ≤ϵ-refl (split-left L lin ≤γ d₁ d₂))
  with T̂₂ , ϵ₂ , Δ₂ , k , σ₂ , Sσ₂ , ag₂ , SΔ₂ , ϵ₂≤ , ≃₂ , m′≤k , uvT̂₂ , uvΔ₂ , der₂
     ← ih₂ Sσ₁ (uvarsInΓ-mono Nat.≤-refl m≤m′ uΓ) (approx-agree {Γ = Γ} {Γ̂ = Γ̂} uΓ ag₁ ap) Se₂ ST₂
          (lin-↓ Γ γ (fv e₂) lin)
          (T-Conv eq₂ ≤ϵ-refl (split-right L lin ≤γ d₁ d₂))
  = let Lft = ≼→ Sσ ap uΓ (split-≤γ L lin ≤γ d₁ d₂)
        AG  = agree-trans (agree-narrow m≤m′ ag₂) ag₁
    in _ , _ , _ , k , σ₂ , Sσ₂ , AG ,
       solvedΔ-++ (solvedΔ-agree (agree-sym AG) (csc Lft) (sol Lft))
         (solvedΔ-++
           (solvedΔ-agree (agree-sym ag₂) (C-Eq (solved⇒uvarsIn ST₁) uvT̂₁ ∷ uvΔ₁)
             (subst (_≃ subTy T̂₁ σ₁) (sym (subTy-id ST₁)) (≃-sym ≃₁) ∷ SΔ₁))
           (subst (_≃ subTy T̂₂ σ₂) (sym (subTy-id ST₂)) (≃-sym ≃₂) ∷ SΔ₂)) ,
       ⊔ϵ-lub (≤ϵ-trans ϵ₁≤ ϵ≤) (≤ϵ-trans ϵ₂≤ ℙ≤ϵ) ,
       ≃-reflexive (subTy-id ST) , Nat.≤-trans m≤m′ m′≤k , solved⇒uvarsIn ST ,
       uvarsInΔ-++ (uvarsInΔ-mono Nat.≤-refl (Nat.≤-trans m≤m′ m′≤k) (csc Lft))
         (uvarsInΔ-++
           (uvarsInΔ-mono Nat.≤-refl m′≤k (C-Eq (solved⇒uvarsIn ST₁) uvT̂₁ ∷ uvΔ₁))
           (C-Eq (solved⇒uvarsIn ST₂) uvT̂₂ ∷ uvΔ₂)) ,
       A-Ann chk-⊗ (A-Pair seq (der Lft)
                  (λ _ → ≤ϵℙ⇒≡ℙ ϵ₂≤) (A-Check der₁) (A-Check der₂))

------------------------------------------------------------------------
-- T-Inj.

inj-case : ∀ {n} {e : Tm n} → IHAt e →
  ∀ {Γ Γ̂ : Ctx n} {γ : Struct n} {i : Side} {T : 𝕋} {ϵ : Eff} {m : ℕ}
    {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm e → SolvedTy T → LinStruct Γ γ →
  Γ ; γ ⊢ `inj i e ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (`inj i e) T ϵ m σ₀
inj-case ih {Γ̂ = Γ̂} {i = i} {m = m} Sσ uΓ ap Se ST lin d
  with inv-inj d
... | T₁ , T₂ , (eq₁ ⊕ eq₂) , dbody
  with ST₁ ⊕ ST₂ ← ST
  with T̂ , ϵ′ , Δ , k , σ , Sσ′ , ag , SΔ , ϵ≤ , ≃b , m≤k , uvT̂ , uvΔ , der
     ← ih Sσ uΓ ap Se (if[ SolvedTy ] i then ST₁ else ST₂) lin
          (T-Conv (if-≃ i eq₁ eq₂) ≤ϵ-refl dbody)
  = _ , _ , _ , k , σ , Sσ′ , ag ,
    (subst (_≃ subTy T̂ σ) (sym (subTy-id (if[ SolvedTy ] i then ST₁ else ST₂)))
           (≃-sym ≃b) ∷ SΔ) ,
    ϵ≤ , ≃-reflexive (subTy-id ST) , m≤k , solved⇒uvarsIn ST ,
    (C-Eq (solved⇒uvarsIn (if[ SolvedTy ] i then ST₁ else ST₂)) uvT̂ ∷ uvΔ) ,
    A-Ann chk-inj (A-Inj (A-Check der))
