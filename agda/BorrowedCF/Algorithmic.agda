{-# OPTIONS --rewriting #-}
module BorrowedCF.Algorithmic where

open import Data.Fin.Subset using (Subset; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

import Data.List.Relation.Unary.All.Properties as All

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)

open import BorrowedCF.Algorithmic.Solved

import BorrowedCF.Types.Substitution as 𝐓
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
fv (`inj i e) = fv e
fv (`case e `of⟨ e₁ ; e₂ ⟩) = fv e ∪ fvClose (fv e₁) ∪ fvClose (fv e₂)

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

  A-Case :
    let γ′ = γ ∣fv[ e ] in
    let γ₁ = γ ↓ V.tail (fv e₁) in
    let γ₂ = γ ↓ V.tail (fv e₂) in
    (≤γ₁ : Γ ∶ γ′ ; γ₁ ≼ γ) →
    (≤γ₂ : Γ ∶ γ′ ; γ₂ ≼ γ) →
    Γ ; γ ∣fv[ e ] ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ →
    T₁ ⸴ Γ ; (` zero ; 𝐂.wk γ₁) ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ →
    T₂ ⸴ Γ ; (` zero ; 𝐂.wk γ₂) ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ →
    -------------------------------------------------------------------------------
    Γ ; γ ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ (U₁ , U₂) ∷ Δ ++ Δ₁ ++ Δ₂

  A-Abs :
    (Arr.Unr a → UnrCx Γ γ) →
    (Arr.Mobile a → MobCx Γ γ) →
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

  A-Inj : ∀ {i} →
    Γ ; γ ⊢ e ⇐ if i then T₁ else T₂ ∣ ϵ ↑ Δ →
    ------------------------------------------
    Γ ; γ ⊢ `inj i e ⇐ T₁ ⊕ T₂ ∣ ϵ ↑ Δ

  A-Check :
    Γ ; γ ⊢ e ⇒ U ∣ ϵ ↑ Δ →
    -------------------------------
    Γ ; γ ⊢ e ⇐ T ∣ ϵ ↑ (T , U) ∷ Δ

sound :
  Γ ; γ ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ →
  (∀ x → SolvedTy (subTy (Γ x) σ)) →
  SolvedTy (subTy T σ) →
  SolvedTm (subTm e σ) →
  All (λ (U₁ , U₂) → subTy U₁ σ ≃ subTy U₂ σ) Δ →
  flip subTy σ ∘ Γ ; γ ⊢ subTm e σ ∶ subTy T σ ∣ ϵ
sound {σ = σ} (A-Var ≤γ) SΓ ST Se SΔ = T-Weaken (≼-map⁺ subTy-unr ≤γ) (T-Var _ refl)
sound (A-Const ≤γ ≢lsplit ≢rsplit ⊢c) SΓ ST Se SΔ = T-Weaken (≼-map⁺ subTy-unr ≤γ) (T-Const {!⊢c!})
sound (A-LSplit ≤γ) SΓ ST Se SΔ = {!!}
sound (A-RSplit ≤γ) SΓ ST Se SΔ = {!!}
sound (A-App ≤γ L⇒pure₁ R⇒pure₂ x x₁) SΓ ST Se SΔ = {!!}
sound (A-LetUnit ≤γ x x₁) SΓ ST Se SΔ = {!!}
sound (A-LetPair ≤γ x x₁) SΓ ST Se SΔ = {!!}
sound (A-Case ≤γ₁ ≤γ₂ x x₁ x₂) SΓ ST Se SΔ = {!!}
sound (A-Abs x x₁ x₂ x₃) SΓ ST Se SΔ = {!!}
sound (A-AbsRec x x₁ x₂ x₃) SΓ ST Se SΔ = {!!}
sound (A-Pair ≤γ L⇒pure₁ R⇒pure₂ x x₁) SΓ ST Se SΔ = {!!}
sound (A-Inj x) SΓ ST Se SΔ = {!!}
sound (A-Check x) SΓ ST Se SΔ = {!sound x!}

{-
complete :
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  SolvedTm e →
  SolvedTy T →
  ∃[ Δ ] ∃[ σ ]
    All (λ (T , U) → SolvedTy (subTy T σ) × SolvedTy (subTy U σ) × subTy T σ ≃ subTy U σ) Δ
      × Γ ; γ ⊢ e ⇐ T ∣ ϵ ↑ Δ
complete (T-Const {c = c} ⊢c) Se ST with isSplit? c
complete (T-Const {c = _} (`lsplit s s′)) Se ST@(⟨ Ss ; Ss′ ⟩ ⟨ _ ⟩→ Sc) | yes (_ , inj₁ refl) =
  let Sσs  = subTy-solved Ss in
  let Sσs′ = subst SolvedTy (sym (𝐓.⋯-id s′ λ())) Ss′ in
  let σ[s′]≃wk[s′] = ≃-reflexive (subTy-id Ss′ ■ sym (𝐓.⋯-id s′ λ())) in
  _ , const s′
    , (subTy-solved ST , ⟨ Sσs ; Sσs′ ⟩ ⟨ _ ⟩→ ⟨ Sσs ⟩ ⊗⟨ L ⟩ ⟨ Sσs′ ⟩ ,
        ⟨ ≃-; ≃-refl σ[s′]≃wk[s′] ⟩ `→ (≃-refl ⊗ ⟨ σ[s′]≃wk[s′] ⟩)) ∷ []
    , A-Check (A-LSplit (≼-refl refl))
complete (T-Const {c = _} (`rsplit s s′)) Se ST | yes (_ , inj₂ refl) = {!!}
... | no no-split =
  _ , const skip
    , (subTy-solved ST , subTy-solved ST , ≃-refl) ∷ []
    , A-Check (A-Const (≼-refl refl) (λ s z → no-split (s , inj₁ z)) (λ s z → no-split (s , inj₂ z)) ⊢c)
complete (T-Var x T-eq) Se ST = {!!}
complete (T-Abs Γ-unr Γ-mob e) Se ST = {!!}
complete (T-AbsRec x x₁ e) Se ST = {!!}
complete (T-AppUnr x f e) S[fe] ST =
  let _ , σf , Sf , Af = complete f {!!} {!!} in
  _ , {!!} , {!!}
    , A-Check (A-App {!!} {!!} {!!} {!Af!} {!!})
complete (T-AppLin x e e₁) Se ST = {!!}
complete (T-AppLeft x e e₁) Se ST = {!!}
complete (T-AppRight x e e₁) Se ST = {!!}
complete (T-Pair p/s e e₁ x) Se ST = {!!}
complete (T-Let p/s e e₁) Se ST = {!!}
complete (T-LetUnit p/s e e₁) Se ST = {!!}
complete (T-LetPair p/s e e₁) Se ST = {!!}
complete (T-Inj e) Se ST = {!!}
complete (T-Case p/s e e₁ e₂) Se ST = {!!}
complete (T-Conv T≃ ϵ≤ e) Se ST = {!!}
complete (T-Weaken γ≤ e) Se ST = {!!}
-}
