-- | The two leaf cases of the completeness induction: T-Var and T-Const (agent C4).
--
--   Neither needs the induction hypothesis.  `A-Const` covers every constant that is not a
--   split; `` `lsplit `` / `` `rsplit `` allocate the fresh unification variable `m` and the
--   substitution assigns it the second half of the split type.
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

open import BorrowedCF.Completeness.Main.Base
open import BorrowedCF.Completeness.Main.Interface

module BorrowedCF.Completeness.Main.Simple where

open import BorrowedCF.Completeness.Main.Transfer

open Nat.Variables

------------------------------------------------------------------------
-- T-Var.  A-Var infers the type the ALGORITHMIC context gives the variable, which
-- approximates the declarative one by hypothesis; nothing is allocated.

var-case : ∀ {n} {Γ Γ̂ : Ctx n} {γ : Struct n} {x : 𝔽 n} {T : 𝕋} {ϵ : Eff} {m : ℕ}
             {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  Γ ; γ ⊢ ` x ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (` x) T ϵ m σ₀
var-case {Γ̂ = Γ̂} {x = x} {m = m} {σ₀ = σ₀} Sσ uΓ ap d =
  let T≃ , ≤γ = inv-` d
      Lft     = ≼→ Sσ ap uΓ ≤γ
  in Γ̂ ﹫ x , ℙ , cs Lft , m , σ₀ ,
     Sσ , agree (λ _ _ _ → refl) , sol Lft , ℙ≤ϵ , ≃-trans (ap x) (≃-sym T≃) ,
     Nat.≤-refl , lookupΓ uΓ x , csc Lft ,
     A-Var (der Lft)

------------------------------------------------------------------------
-- T-Const.  The declarative type of a constant is a schema instance and need not be
-- solved, so it is solved first with `s₀ = UV.someSub`, which changes neither the
-- constant (it is a `SolvedC`) nor the goal type (it is solved).

const-case : ∀ {n} {Γ Γ̂ : Ctx n} {γ : Struct n} {c : Const} {T : 𝕋} {ϵ : Eff} {m : ℕ}
               {σ₀ : UV.Sub} →
  Solving σ₀ → UVarsInΓ 0 m Γ̂ → Approx Γ̂ Γ σ₀ →
  SolvedTm (K {n} c) → SolvedTy T →
  Γ ; γ ⊢ K c ∶ T ∣ ϵ →
  Conclusion Γ̂ γ (K c) T ϵ m σ₀
const-case {Γ̂ = Γ̂} {γ = γ} {c = c} {T = T} {m = m} {σ₀ = σ₀} Sσ uΓ ap Se ST d
  with U , U≃T , ≤γ , ⊢c ← inv-K d
  with algConst? c
... | inj₁ Ac =
  let Lft = ≼→ Sσ ap uΓ ≤γ in
  subTy U s₀ , ℙ , cs Lft , m , σ₀ ,
    Sσ , agree (λ _ _ _ → refl) , sol Lft , ℙ≤ϵ ,
    subst (_≃ T) (sym (subTy-id (subTy-solved U s₀-solving)))
          (≃-trans (subTy-≃ U≃T) (≃-reflexive (subTy-id ST))) ,
    Nat.≤-refl , solved⇒uvarsIn (subTy-solved U s₀-solving) , csc Lft ,
    A-Const (der Lft) Ac
      (subst (λ z → ⊢ z ∶ subTy U s₀) (subConst-id (solvedTm-K Se)) (subConst-⊢ ⊢c))
... | inj₂ `lsplit
  with `lsplit s s′ ¬Ss ¬Ss′ ← ⊢c
  with Ss ← solvedC-lsplit (solvedTm-K Se)
  =
  let ¬Ss′₀ = ¬Ss′ ∘ subTy-skips⁻¹
      σ     = extend σ₀ m (subTy s′ s₀) ¬Ss′₀
      eqα   : subTy {𝕤} {0} (`` UV.fresh m) σ ≡ subTy s′ s₀
      eqα   = uvar-subTy (UV.fresh m) σ ■ extend-ap σ₀ m (subTy s′ s₀) ¬Ss′₀
      eqs   : subTy s σ ≡ subTy s s₀
      eqs   = subTy-id Ss ■ sym (subTy-id Ss)
      eqT̂   : (⟨ subTy s σ ; subTy {𝕤} {0} (`` UV.fresh m) σ ⟩ →*M
                 ⟨ subTy s σ ⟩ ⊗ᴸ ⟨ subTy {𝕤} {0} (`` UV.fresh m) σ ⟩ ∣ ℙ)
              ≡ subTy U s₀
      eqT̂   = cong₂ (λ x y → ⟨ x ; y ⟩ →*M ⟨ x ⟩ ⊗ᴸ ⟨ y ⟩ ∣ ℙ) eqs eqα
      Lft   = ≼→ Sσ ap uΓ ≤γ
  in ⟨ s ; `` UV.fresh m ⟩ →*M ⟨ s ⟩ ⊗ᴸ ⟨ `` UV.fresh m ⟩ ∣ ℙ ,
     ℙ , cs Lft , suc m , σ ,
     extend-solving σ₀ m (subTy s′ s₀) ¬Ss′₀ Sσ (subTy-solved s′ s₀-solving) ,
     extend-agree σ₀ m (subTy s′ s₀) ¬Ss′₀ ,
     solvedΔ-agree (agree-sym (extend-agree σ₀ m (subTy s′ s₀) ¬Ss′₀)) (csc Lft) (sol Lft) ,
     ℙ≤ϵ ,
     subst (_≃ T) (sym eqT̂) (≃-trans (subTy-≃ U≃T) (≃-reflexive (subTy-id ST))) ,
     Nat.n≤1+n m ,
     (⟨ solved⇒uvarsIn Ss ; `` (Nat.z≤n , Nat.≤-refl) ⟩) ⟨ _ ⟩→
       (⟨ solved⇒uvarsIn Ss ⟩ ⊗⟨ L ⟩ ⟨ `` (Nat.z≤n , Nat.≤-refl) ⟩) ,
     uvarsInΔ-mono Nat.≤-refl (Nat.n≤1+n m) (csc Lft) ,
     A-LSplit (der Lft) ¬Ss
... | inj₂ `rsplit
  with `rsplit s s′ ¬Ss ¬Ss′ ← ⊢c
  with Ss ← solvedC-rsplit (solvedTm-K Se)
  =
  let ¬Ss′₀ = ¬Ss′ ∘ subTy-skips⁻¹
      σ     = extend σ₀ m (subTy s′ s₀) ¬Ss′₀
      eqα   : subTy {𝕤} {0} (`` UV.fresh m) σ ≡ subTy s′ s₀
      eqα   = uvar-subTy (UV.fresh m) σ ■ extend-ap σ₀ m (subTy s′ s₀) ¬Ss′₀
      eqs   : subTy s σ ≡ subTy s s₀
      eqs   = subTy-id Ss ■ sym (subTy-id Ss)
      eqT̂   : (⟨ subTy s σ ; subTy {𝕤} {0} (`` UV.fresh m) σ ⟩ →*M
                 ⟨ subTy s σ ; ret ⟩ ⊗¹ ⟨ acq ; subTy {𝕤} {0} (`` UV.fresh m) σ ⟩ ∣ ℙ)
              ≡ subTy U s₀
      eqT̂   = cong₂ (λ x y → ⟨ x ; y ⟩ →*M ⟨ x ; ret ⟩ ⊗¹ ⟨ acq ; y ⟩ ∣ ℙ) eqs eqα
      Lft   = ≼→ Sσ ap uΓ ≤γ
  in ⟨ s ; `` UV.fresh m ⟩ →*M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; `` UV.fresh m ⟩ ∣ ℙ ,
     ℙ , cs Lft , suc m , σ ,
     extend-solving σ₀ m (subTy s′ s₀) ¬Ss′₀ Sσ (subTy-solved s′ s₀-solving) ,
     extend-agree σ₀ m (subTy s′ s₀) ¬Ss′₀ ,
     solvedΔ-agree (agree-sym (extend-agree σ₀ m (subTy s′ s₀) ¬Ss′₀)) (csc Lft) (sol Lft) ,
     ℙ≤ϵ ,
     subst (_≃ T) (sym eqT̂) (≃-trans (subTy-≃ U≃T) (≃-reflexive (subTy-id ST))) ,
     Nat.n≤1+n m ,
     (⟨ solved⇒uvarsIn Ss ; `` (Nat.z≤n , Nat.≤-refl) ⟩) ⟨ _ ⟩→
       (⟨ solved⇒uvarsIn Ss ; ret ⟩ ⊗⟨ 𝟙 ⟩ ⟨ acq ; `` (Nat.z≤n , Nat.≤-refl) ⟩) ,
     uvarsInΔ-mono Nat.≤-refl (Nat.n≤1+n m) (csc Lft) ,
     A-RSplit (der Lft) ¬Ss
