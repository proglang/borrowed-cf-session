{-# OPTIONS --rewriting #-}
module BorrowedCF.Algorithmic where

open import Data.Fin.Subset using (Subset; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

private variable
  e e₁ e₂ e₃ e′ : Tm n

fvClose : Subset (suc n) → Subset n
fvClose = V.tail

fv : Tm n → Subset n
fv (` x) = ⁅ x ⁆ 
fv (K c) = ⁅⁆
fv (ƛ e) = fvClose (fv e)
fv (μ e) = fvClose (fv e)
fv (e₁ · e₂) = fv e₁ ∪ fv e₂
fv (e₁ ; e₂) = fv e₁ ∪ fv e₂
fv (e₁ ⊗ e₂) = fv e₁ ∪ fv e₂ 
fv (`let e₁ `in e₂) = fv e₁ ∪ fvClose (fv e₂)
fv (`let⊗ e₁ `in e₂) = fv e₁ ∪ fvClose (fvClose (fv e₂))

_∣fv[_] : Struct n → Tm n → Struct n
γ ∣fv[ e ] = γ ↓ fv e

Constraint = 𝕋 × 𝕋

CSet : Set
CSet = List Constraint

private variable
  Δ Δ₁ Δ₂ Δ₃ Δ′ : CSet

data Mode : Set where
  chk inf : Mode

private variable ξ : Mode

infix 4 _;_⊢[_]_∶_∣_↑_ _;_⊢_⇐_∣_↑_ _;_⊢_⇒_∣_↑_

data _;_⊢[_]_∶_∣_↑_ (Γ : Ctx n) (γ : Struct n) : Mode → Tm n → 𝕋 → Eff → CSet → Set

_;_⊢_⇒_∣_↑_ : Ctx n → Struct n → _
_;_⊢_⇒_∣_↑_ Γ γ = _;_⊢[_]_∶_∣_↑_ Γ γ inf

_;_⊢_⇐_∣_↑_ : Ctx n → Struct n → _
_;_⊢_⇐_∣_↑_ Γ γ = _;_⊢[_]_∶_∣_↑_ Γ γ chk

data _;_⊢[_]_∶_∣_↑_ Γ γ where
  A-Var : ∀ {x} →
    (≤γ : Γ ∶ ` x ≼ γ) →
    --------------------------
    Γ ; γ ⊢ ` x ⇒ Γ x ∣ ℙ ↑ []

  A-Const : ∀ {c} →
    (≤γ : Γ ∶ [] ≼ γ) →
    (≢lsplit : ∀ s → c ≢ `lsplit s) →
    (≢rsplit : ∀ s → c ≢ `rsplit s) →
    ⊢ c ∶ T →
    -------------------------
    Γ ; γ ⊢ K c ⇒ T ∣ ℙ ↑ []

  A-LSplit :
    (≤γ : Γ ∶ [] ≼ γ) →
    -----------------------------------------------------------------------
    Γ ; γ ⊢ K (`lsplit s) ⇒ ⟨ s ; `` 0 ⟩ →1M ⟨ s ⟩ ⊗ᴸ ⟨ `` 0 ⟩ ∣ ℙ ∣ ℙ ↑ []


  A-RSplit :
    (≤γ : Γ ∶ [] ≼ γ) →
    -----------------------------------------------------------------------------------
    Γ ; γ ⊢ K (`rsplit s) ⇒ ⟨ s ; `` 0 ⟩ →1M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; `` 0 ⟩ ∣ ℙ ∣ ℙ ↑ []

  A-App :
    (≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ) →
    (L⇒pure₁ : Arr.dir a ≡ L → ϵ₁ ≡ ℙ) →
    (R⇒pure₂ : Arr.dir a ≡ R → ϵ₂ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ →
    Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ →
    -------------------------------------------------------
    Γ ; γ ⊢ e₁ · e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a ↑ Δ₁ ++ Δ₂

  A-LetUnit :
    (≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ) →
    Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ⇐ `⊤ ∣ ϵ₁ ↑ Δ₁ →
    Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ⇒ T  ∣ ϵ₂ ↑ Δ₂ →
    ------------------------------------------
    Γ ; γ ⊢ e₁ ; e₂ ⇒ T ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂

  A-LetPair :
    let open Fin.Patterns in
    let γ₁ = γ ∣fv[ e₁ ] in
    let γ₂ = γ ↓ V.drop 2 (fv e₂) in
    (≤γ : Γ ∶ γ₁ ; γ₂ ≼ γ) →
    Γ ; γ₁ ⊢ e₁ ⇒ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ₁ ↑ Δ₁ →
    T₁ ⸴ T₂ ⸴ Γ ; (join d (` 0F) (` 1F) ; 𝐂.wk (𝐂.wk γ₂)) ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ →
    --------------------------------------------------------------------------
    Γ ; γ ⊢ `let⊗ e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂

  A-Abs :
    (Arr.Unr a → UnrCx Γ γ) →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) ⊢ e ⇐ U ∣ ϵ ↑ Δ →
    ------------------------------------------------------------
    Γ ; γ ⊢ ƛ e ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ

  A-AbsRec :
    let open Fin.Patterns in
    UnrCx Γ γ →
    Arr.Unr a →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) ⊢ e ⇐ U ∣ ϵ ↑ Δ →
    ----------------------------------------------------------------------
    Γ ; γ ⊢ μ (ƛ e) ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ

  A-Pair :
    (≤γ : Γ ∶ join d (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ) →
    (L⇒pure₁ : d ≡ L → ϵ₂ ≡ ℙ) →
    (R⇒pure₂ : d ≡ R → ϵ₁ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ⇐ T ∣ ϵ₁ ↑ Δ₁ →
    Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ →
    --------------------------------------------------
    Γ ; γ ⊢ e₁ ⊗ e₂ ⇐ T ⊗⟨ d ⟩ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂


  A-Check :
    Γ ; γ ⊢ e ⇒ U ∣ ϵ ↑ Δ →
    -------------------------------
    Γ ; γ ⊢ e ⇐ T ∣ ϵ ↑ (T , U) ∷ Δ


-- sound : Γ ; γ ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ → Γ ; γ ⊢ e ∶ T ∣ ϵ
-- sound (A-Var ≤γ) = T-Weaken ≤γ (T-Var _ refl)
-- sound (A-Const ≤γ ≢lsplit ≢rsplit x) = T-Weaken ≤γ (T-Const x)
-- sound (A-LSplit ≤γ) = T-Weaken ≤γ (T-Const `lsplit)
-- sound (A-RSplit ≤γ) = T-Weaken ≤γ (T-Const `rsplit)
-- sound (A-App ≤γ L⇒pure₁ R⇒pure₂ x x₁) = {!!}
-- sound (A-Abs x x₁ x₂) = {!!}
-- sound (A-LetUnit ≤γ x x₁) = {!!}
-- sound (A-LetPair ≤γ x x₁) = {!!}
-- sound (A-Check x) = {!!}

-- complete : Γ ; γ ⊢ e ∶ T ∣ ϵ → ∃[ Δ ] (Γ ; γ ⊢ e ⇐ T ∣ ϵ ↑ Δ)
-- complete = {!!}
