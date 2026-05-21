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

data Constraint : Set where

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
  A-Const : ∀ {c} →
    (≤γ : Γ ∶ [] ≼ γ) →
    (≢lsplit : c ≢ `lsplit) →
    (≢rsplit : c ≢ `rsplit) →
    ⊢ c ∶ T →
    -------------------------
    Γ ; γ ⊢ K c ⇒ T ∣ ℙ ↑ []

  A-LSplit :
    (≤γ : Γ ∶ [] ≼ γ) →
    --------------------------------------------------------------
    Γ ; γ ⊢ K `lsplit ⇒ ⟨ s ⟩ →m,1 ⟨ s′ ⟩ ⊗ᴸ ⟨ {!!} ⟩ ∣ ℙ ∣ ℙ ↑ L.[ {!!} ]

  A-Var : ∀ {x} →
    (≤γ : Γ ∶ ` x ≼ γ) →
    --------------------------
    Γ ; γ ⊢ ` x ⇒ Γ x ∣ ℙ ↑ []

  A-App :
    (≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ) →
    (L⇒pure₁ : Arr.dir a ≡ L → ϵ₁ ≡ ℙ) →
    (R⇒pure₂ : Arr.dir a ≡ R → ϵ₂ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ →
    Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ →
    -------------------------------------------------------
    Γ ; γ ⊢ e₁ · e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a ↑ Δ₁ ++ Δ₂

  A-Abs :
    ϵ ≤ϵ Arr.eff a →
    (Arr.Unr a → UnrCx Γ γ) →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) ⊢ e ⇐ U ∣ ϵ ↑ Δ →
    ------------------------------------------------------------
    Γ ; γ ⊢ ƛ e ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ

  A-LetUnit :
    (≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ) →
    Γ ; γ ∣fv[ e₁ ] ⊢ e₁ ⇐ `⊤ ∣ ϵ₁ ↑ Δ₁ →
    Γ ; γ ∣fv[ e₂ ] ⊢ e₂ ⇒ T  ∣ ϵ₂ ↑ Δ₂ →
    ------------------------------------------
    Γ ; γ ⊢ e₁ ; e₂ ⇒ T ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂

--  A-Check


-- sound : Γ ; γ ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ → Γ ; γ ⊢ e ∶ T ∣ ϵ
-- sound (A-App {a = a} ≤γ L⇒pure₁ R⇒pure₂ e₁ e₂) with a
-- ... | record { lin = unr } = T-Weaken {!!} {!!} $ T-AppUnr refl (T-Weaken {!!} {!!} (sound e₁)) (T-Weaken {!!} {!!} (sound e₂))
-- ... | record { lin = 𝟙; dir = 𝟙 } = {!!}
-- ... | record { lin = 𝟙; dir = L } = {!!}
-- ... | record { lin = 𝟙; dir = R } = {!!}
-- {-
--   let open EffProperties in
--   let open ≤ϵ-Reasoning in
--   T-Weaken {!x≤y⇒x≤z⊔y!} {!!} $
--     T-App refl (T-Weaken {!≤ϵ-refl!} {!!} (sound e₁)) (T-Weaken {!!} {!!} (sound e₂))
-- -}
-- sound (A-Abs x x₁ x₂) = {!!}

-- complete : Γ ; γ ⊢ e ∶ T ∣ ϵ → ∃[ Δ ] (Γ ; γ ⊢ e ⇐ T ∣ ϵ ↑ Δ)
-- complete = {!!}
