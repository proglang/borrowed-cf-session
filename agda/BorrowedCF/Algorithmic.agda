module BorrowedCF.Algorithmic where

open import Data.Bool.Properties
open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
import Data.Fin.Subset.Properties as S
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

import Data.List.Relation.Unary.All.Properties as All

open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Prelude
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved

import BorrowedCF.Types.Substitution as 𝐓
import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open EffProperties

private variable
  e e₁ e₂ e₃ e′ e₁′ e₂′ : Tm n

open V using () renaming (tail to fvClose; drop to fvClose*) public

fv : Tm n → Subset n
fv (` x) = ⁅ x ⁆ 
fv (K c) = ⁅⁆
fv (ƛ e) = fvClose (fv e)
fv (μ e) = fvClose (fv e)
fv (e₁ · e₂) = fv e₁ ∪ fv e₂
fv (e₁ ; e₂) = fv e₁ ∪ fv e₂
fv (e₁ ⊗ e₂) = fv e₁ ∪ fv e₂ 
fv (`let e₁ `in e₂) = fv e₁ ∪ fvClose (fv e₂)
fv (`let⊗ e₁ `in e₂) = fv e₁ ∪ fvClose* 2 (fv e₂)
fv (`inj i e) = fv e
fv (`case e `of⟨ e₁ ; e₂ ⟩) = fv e ∪ fvClose (fv e₁) ∪ fvClose (fv e₂)

fv-subTm : (e : Tm n) → fv (subTm e σ) ≡ fv e
fv-subTm (` x) = refl
fv-subTm (K c) = refl
fv-subTm (ƛ e) = cong fvClose (fv-subTm e)
fv-subTm (μ e) = cong fvClose (fv-subTm e)
fv-subTm (e · e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (e ; e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (e ⊗ e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (`let e `in e₁) = cong₂ _∪_ (fv-subTm e) (cong fvClose (fv-subTm e₁))
fv-subTm (`let⊗ e `in e₁) = cong₂ _∪_ (fv-subTm e) (cong (fvClose* 2) (fv-subTm e₁))
fv-subTm (`inj i e) = fv-subTm e
fv-subTm `case e `of⟨ e₁ ; e₂ ⟩ = cong₂ _∪_ (fv-subTm e) (cong₂ _∪_ (cong fvClose (fv-subTm e₁)) (cong fvClose (fv-subTm e₂)))

postulate
  fv-wk : (e : Tm n) → fv (wk e) ≡ outside ∷ fv e
{-
fv[wk ` x ] = refl
fv[wk K c ] = refl
fv[wk ƛ e ] = {!!}
fv[wk μ e ] = {!!}
fv[wk e₁ · e₂ ] rewrite fv[wk e₁ ] | fv[wk e₂ ] = refl
fv[wk e₁ ; e₂ ] rewrite fv[wk e₁ ] | fv[wk e₂ ] = refl
fv[wk e₁ ⊗ e₂ ] rewrite fv[wk e₁ ] | fv[wk e₂ ] = refl
fv[wk `let e `in e₁ ] = {!!}
fv[wk `let⊗ e `in e₁ ] = {!!}
fv[wk `inj i e ] = fv[wk e ]
fv[wk `case e `of⟨ e₁ ; e₂ ⟩ ] = {!!}
-}

_∣fv[_] : Struct n → Tm n → Struct n
γ ∣fv[ e ] = γ ↓ fv e

_∣∁fv[_] : Struct n → Tm n → Struct n
γ ∣∁fv[ e ] = γ ↓ ∁ (fv e)

postulate
  ↓;↓≼⇒≼∁ : ∀ (X₁ X₂ : Subset n) {γ γ₁ γ₂ α β} →
    Γ ∶ α ∥ β ≈ γ →
    AllCx Unr Γ α →
    AllCx (Un.∁ Unr) Γ β →
    γ₁ ≡ γ ↓ X₁ →
    γ₂ ≡ γ ↓ X₂ →
    Γ ∶ γ₁ ; γ₂ ≼ γ →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    Γ ∶ γ₂ ≼ α ∥ (γ ↓ ∁ X₁)


{-
↓;↓≼⇒≼∁ : ∀ {γ : Struct n} {γ₁ X₁ γ₂ X₂} →
  γ₁ ≡ γ ↓ X₁ →
  γ₂ ≡ γ ↓ X₂ →
  Γ ∶ γ₁ ; γ₂ ≼ γ →
  Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
  Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
  Γ ∶ γ₂ ≼ γ ↓ ∁ X₁
↓;↓≼⇒≼∁ {Γ = Γ} {γ = γ} {γ₁} {X₁} eq₁ eq₂ ≤γ (T-Const ⊢c) y =
  let dom[γ]∩X₁≡⁅⁆ = ↓-empty⁻¹ {Γ = Γ} γ X₁ (≈-reflexive (sym eq₁))
      dom[γ]∩∁[X₁]≡dom[γ] = ∩-∁ (dom γ) X₁ dom[γ]∩X₁≡⁅⁆
  in ≼-trans (≼-refl (≈-sym ;-unit₁)) $ ≼-trans ≤γ $ ≼-refl $ ≈-reflexive $ sym $
       ↓-identity-⊆ _ λ ∈dom[γ] → S.x∈p∩q⁻ (dom γ) (∁ X₁) (subst (_ ∈_) (sym dom[γ]∩∁[X₁]≡dom[γ]) ∈dom[γ]) .proj₂
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Var x T-eq) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Abs Γ-unr Γ-mob x) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-AbsRec Γ-unr a-unr x) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-AppUnr a-unr ≤ₐ x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-AppLin a-par ≤ₐ x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-AppLeft aL ≤ₐ x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-AppRight aR ≤ₐ x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Pair p/s seq⇒p x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Let p/s x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-LetUnit x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-LetPair p/s x x₁) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Inj x) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Case p/s x x₁ x₂) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Conv T≃ ϵ≤ x) y = {!!}
↓;↓≼⇒≼∁ eq₁ eq₂ ≤γ (T-Weaken γ≤ x) y = {!!}
-}

{-
fv;∁fv≼ :
  γ ∣fv[ e ] ≡ γ′ →
  Γ ; γ′ ⊢ e ∶ T ∣ ϵ →
  Γ ∶ γ′ ; γ ∣∁fv[ e ] ≈ γ
fv;∁fv≼ {n} {γ = γ} eq (T-Const ⊢c) =
  ≈-trans ;-unit₁ $ ≈-reflexive $
    cong (γ ↓_) (S.∣p∣≡n⇒p≡⊤ (S.∣∁p∣≡n∸∣p∣ {n} ⁅⁆ ■ cong (n Nat.∸_) (S.∣⊥∣≡0 n)))
      ■ ↓-identity _
fv;∁fv≼ eq (T-Var x T-eq) = {!!}
fv;∁fv≼ eq (T-Abs Γ-unr Γ-mob x) = {!!}
fv;∁fv≼ eq (T-AbsRec Γ-unr a-unr x) = {!!}
fv;∁fv≼ eq (T-AppUnr a-unr ≤ₐ x x₁) = {!!}
fv;∁fv≼ eq (T-AppLin a-par ≤ₐ x x₁) = {!!}
fv;∁fv≼ eq (T-AppLeft aL ≤ₐ x x₁) = {!!}
fv;∁fv≼ eq (T-AppRight aR ≤ₐ x x₁) = {!!}
fv;∁fv≼ eq (T-Pair p/s seq⇒p x x₁) = {!!}
fv;∁fv≼ eq (T-Let p/s x x₁) = {!!}
fv;∁fv≼ eq (T-LetUnit x x₁) = {!!}
fv;∁fv≼ eq (T-LetPair p/s x x₁) = {!!}
fv;∁fv≼ eq (T-Inj x) = {!!}
fv;∁fv≼ eq (T-Case p/s x x₁ x₂) = {!!}
fv;∁fv≼ eq (T-Conv T≃ ϵ≤ x) = {!!}
fv;∁fv≼ eq (T-Weaken γ≤ x) = {!!}
-}

data Mode : Set where
  chk inf : Mode

private variable ξ : Mode

{-
countSplitsC : Const → ℕ
countSplitsC `unit = 0
countSplitsC `fork = 0
countSplitsC `send = 0
countSplitsC `recv = 0
countSplitsC `drop = 0
countSplitsC `acq = 0
countSplitsC (`end x) = 0
countSplitsC (`new x) = 0
countSplitsC (`lsplit x) = 1
countSplitsC (`rsplit x) = 1

countSplits : Tm n → ℕ
countSplits (` x) = 0
countSplits (K c) = countSplitsC c
countSplits (ƛ e) = countSplits e
countSplits (μ e) = countSplits e
countSplits (e₁ · e₂) = countSplits e₁ + countSplits e₂
countSplits (e₁ ; e₂) = countSplits e₁ + countSplits e₂
countSplits (e₁ ⊗ e₂) = countSplits e₁ + countSplits e₂
countSplits (`let e `in e′) = countSplits e + countSplits e′
countSplits (`let⊗ e `in e′) = countSplits e + countSplits e′
countSplits (`inj i e) = countSplits e
countSplits `case e `of⟨ e₁ ; e₂ ⟩ = countSplits e + countSplits e₁ + countSplits e₂

liftUVars : ℕ → Tm n → Tm n
liftUVars n e = subTm e (UV.weaken n)
-}

{-
infix 4 _─→η_

data _─→η_ {n} : Tm n → Tm n → Set where
  refl : e ─→η e
  here : e ─→η e′ → e ─→η ƛ (wk e′ · (` zero))
  ƛ : e ─→η e′ → ƛ e ─→η ƛ e′
  μ : e ─→η e′ → μ e ─→η μ e′
  _·_ : e₁ ─→η e₁′ → e₂ ─→η e₂′ → e₁ · e₂ ─→η e₁′ · e₂′
  _;_ : e₁ ─→η e₁′ → e₂ ─→η e₂′ → e₁ ; e₂ ─→η e₁′ ; e₂′
  _⊗_ : e₁ ─→η e₁′ → e₂ ─→η e₂′ → e₁ ⊗ e₂ ─→η e₁′ ⊗ e₂′
  `let⊗_`in_ : e₁ ─→η e₁′ → e₂ ─→η e₂′ → `let⊗ e₁ `in e₂ ─→η `let⊗ e₁′ `in e₂′
  `inj : ∀ {i} → e ─→η e′ → `inj i e ─→η `inj i e′
  `case_`of⟨_;_⟩ : e ─→η e′ → e₁ ─→η e₁′ → e₂ ─→η e₂′ → `case e `of⟨ e₁ ; e₂ ⟩ ─→η `case e′ `of⟨ e₁′ ; e₂′ ⟩
-}

data ¬AlgConst : Const → Set where
  `lsplit : ¬AlgConst (`lsplit s)
  `rsplit : ¬AlgConst (`rsplit s)
  `select : ∀ {k} → ¬AlgConst (`select k)
  `branch : ¬AlgConst `branch

AlgConst : Pred Const _
AlgConst = Un.∁ ¬AlgConst

algConst? : ∀ c → AlgConst c ⊎ ¬AlgConst c
algConst? `unit = inj₁ λ()
algConst? `fork = inj₁ λ()
algConst? `send = inj₁ λ()
algConst? `recv = inj₁ λ()
algConst? `drop = inj₁ λ()
algConst? `acq = inj₁ λ()
algConst? (`end x) = inj₁ λ()
algConst? (`new x) = inj₁ λ()
algConst? (`lsplit x) = inj₂ `lsplit
algConst? (`rsplit x) = inj₂ `rsplit
algConst? (`select x) = inj₂ `select
algConst? `branch     = inj₂ `branch

infix 4 _;_/_⊢[_]_∶_∣_↑_/_ _;_/_⊢_⇐_∣_↑_/_ _;_/_⊢_⇒_∣_↑_/_

data _;_/_⊢[_]_∶_∣_↑_/_ (Γ : Ctx n) (γ : Struct n) (m : ℕ) : Mode → Tm n → 𝕋 → Eff → CSet → ℕ → Set

_;_/_⊢_⇒_∣_↑_/_ : Ctx n → Struct n → ℕ → _
_;_/_⊢_⇒_∣_↑_/_ Γ γ m = _;_/_⊢[_]_∶_∣_↑_/_ Γ γ m inf

_;_/_⊢_⇐_∣_↑_/_ : Ctx n → Struct n → ℕ → _
_;_/_⊢_⇐_∣_↑_/_ Γ γ m = _;_/_⊢[_]_∶_∣_↑_/_ Γ γ m chk

data _;_/_⊢[_]_∶_∣_↑_/_ Γ γ m where
  A-Var : ∀ {x} →
    (≤γ : Γ ∶ ` x ≼ γ) →
    ----------------------------------
    Γ ; γ / m ⊢ ` x ⇒ Γ x ∣ ℙ ↑ [] / m

  A-Const : ∀ {c} →
    (≤γ : Γ ∶ [] ≼ γ) →
    (Ac : AlgConst c) →
    ⊢ c ∶ T →
    --------------------------------
    Γ ; γ / m ⊢ K c ⇒ T ∣ ℙ ↑ [] / m

  A-LSplit :
    let α = UV.fresh m in
    (≤γ : Γ ∶ [] ≼ γ) →
    ¬ Skips s →
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`lsplit s) ⇒ ⟨ s ; `` α ⟩ →1M ⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-RSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ) →
    ¬ Skips s →
    -----------------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`rsplit s) ⇒ ⟨ s ; `` α ⟩ →1M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-App :
    (≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ) →
    (L⇒pure₁ : Arr.dir a ≡ L → ϵ₁ ≡ ℙ) →
    (R⇒pure₂ : Arr.dir a ≡ R → ϵ₂ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ / n →
    --------------------------------------------------------------
    Γ ; γ / m ⊢ e₁ · e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a ↑ Δ₁ ++ Δ₂ / n

  A-Seq :
    Unr T →
    (≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇒ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n  →
    -------------------------------------------------
    Γ ; γ / m ⊢ e₁ ; e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

  A-LetPair :
    let open Fin.Patterns in
    let γ₁ = γ ∣fv[ e₁ ] in
    let γ₂ = γ ↓ fvClose* 2 (fv e₂) in
    (≤γ : Γ ∶ γ₁ ; γ₂ ≼ γ) →
    Γ ; γ₁ / m ⊢ e₁ ⇒ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ₁ ↑ Δ₁ / m′ →
    T₁ ⸴ T₂ ⸴ Γ ; (join d (` 0F) (` 1F) ; 𝐂.wk (𝐂.wk γ₂)) / m′ ⊢ e₂ ⇒ U ∣ ϵ₂ ↑ Δ₂ / n →
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ `let⊗ e₁ `in e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

  A-Case :
    let γ′ = γ ∣fv[ e ] in
    let γ₁ = γ ↓ V.tail (fv e₁) in
    let γ₂ = γ ↓ V.tail (fv e₂) in
    (≤γ₁ : Γ ∶ γ′ ; γ₁ ≼ γ) →
    (≤γ₂ : Γ ∶ γ′ ; γ₂ ≼ γ) →
    ∀ {ϵ ϵ₁ ϵ₂ T₁ T₂ Δ Δ₁ Δ₂} →
    Γ ; γ ∣fv[ e ] / m ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / m₁ →
    T₁ ⸴ Γ ; (` zero ; 𝐂.wk γ₁) / m₁ ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
    T₂ ⸴ Γ ; (` zero ; 𝐂.wk γ₂) / m₂ ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ / n  →
    ---------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ (U₁ , U₂) ∷ Δ ++ Δ₁ ++ Δ₂ / n

  A-Abs :
    (Arr.Unr a → UnrCx Γ γ) →
    (Arr.Mobile a → MobCx Γ γ) →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) / m ⊢ e ⇐ U ∣ ϵ ↑ Δ / n →
    --------------------------------------------------------------------
    Γ ; γ / m ⊢ ƛ e ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ / n

  A-AbsRec :
    let open Fin.Patterns in
    UnrCx Γ γ →
    Arr.Unr a →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) / m ⊢ e ⇐ U ∣ ϵ ↑ Δ / n →
    ------------------------------------------------------------------------------
    Γ ; γ / m ⊢ μ (ƛ e) ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ / n

  A-Pair :
    ∀ (p/s : ParSeq) {ϵ₁ ϵ₂} →
    (≤γ : Γ ∶ join p/s (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ) →
    (seq⇒pure : p/s ≡ seq → ϵ₂ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇐ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ U ∣ ϵ₂ ↑ Δ₂ / n  →
    ----------------------------------------------------------------------
    Γ ; γ / m ⊢ e₁ ⊗ e₂ ⇐ T ⊗⟨ biasedDir p/s ⟩ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

  A-Inj : ∀ {i} →
    Γ ; γ / m ⊢ e ⇐ if i then T₁ else T₂ ∣ ϵ ↑ Δ / n →
    --------------------------------------------------
    Γ ; γ / m ⊢ `inj i e ⇐ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / n

  A-Check :
    Γ ; γ / m ⊢ e ⇒ U ∣ ϵ ↑ Δ / n →
    ---------------------------------------
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ (T , U) ∷ Δ / n

  A-Ann :
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n →
    -------------------------------
    Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n

{-
solvedTy⇒solvedTm :
  SolvedΓ Γ σ →
  SolvedΔ Δ σ →
  SolvedTy (subTy T σ) →
  Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n →
  SolvedTm (subTm e σ)

solvedTy⇒solvedTm SΓ SΔ ST (A-Var ≤γ) = ` _
solvedTy⇒solvedTm SΓ SΔ ST (A-Const ≤γ ≢lsplit ≢rsplit x) = {!!}
solvedTy⇒solvedTm SΓ SΔ (_ ⟨ a ⟩→ (⟨ Sα ⟩ ⊗⟨ d ⟩ _)) (A-LSplit ≤γ x) = K (`lsplit Sα)
solvedTy⇒solvedTm SΓ SΔ (_ ⟨ a ⟩→ (⟨ Sα ; _ ⟩ ⊗⟨ d ⟩ _)) (A-RSplit ≤γ) = K (`rsplit Sα)
solvedTy⇒solvedTm SΓ SΔ ST (A-App ≤γ L⇒pure₁ R⇒pure₂ x y) = solvedTy⇒solvedTm SΓ {!!} ({!!} ⟨ _ ⟩→ ST) x · solvedTy⇒solvedTm SΓ {!!} {!ST!} y
solvedTy⇒solvedTm SΓ SΔ ST (A-LetUnit ≤γ x x₁) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-LetPair ≤γ x x₁) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-Case ≤γ₁ ≤γ₂ x x₁ x₂) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-Abs x x₁ x₂ x₃) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-AbsRec x x₁ x₂ x₃) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-Pair ≤γ L⇒pure₁ R⇒pure₂ x x₁) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-Inj x) = {!!}
solvedTy⇒solvedTm SΓ SΔ ST (A-Check x) = {!!}
-}

private
  ty : Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n → 𝕋
  ty {T = T} _ = T


module _ {σ : UV.Sub} (Sσ : Solving σ) where
  open EffProperties

  sound :
    Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n →
    SolvedΓ Γ σ →
    SolvedΔ Δ σ →
    subCtx Γ σ ; γ ⊢ subTm e σ ∶ subTy T σ ∣ ϵ

  sound-app :
    (Arr.dir a ≡ L → ϵ₁ ≡ ℙ) →
    (Arr.dir a ≡ R → ϵ₂ ≡ ℙ) →
    Γ ; γ₁ / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ₂ / m′ ⊢ e₂ ⇐ T          ∣ ϵ₂ ↑ Δ₂ / n  →
    SolvedΓ Γ σ →
    SolvedΔ Δ₁ σ →
    SolvedΔ Δ₂ σ →
    subCtx Γ σ ; join (Arr.dir a) γ₂ γ₁
      ⊢ subTm (e₁ · e₂) σ ∶ subTy U σ ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a

  sound-app {a = a} L⇒pure₁ R⇒pure₂ x y SΓ SΔ₁ SΔ₂
    using x′ ← T-Conv ≃-refl (x≤y⇒x≤y⊔z (Arr.eff a) (x≤x⊔y _ _)) (sound x SΓ SΔ₁)
    using y′ ← T-Conv ≃-refl (x≤y⇒x≤y⊔z (Arr.eff a) (x≤y⊔x _ _)) (sound y SΓ SΔ₂)
    with Arr.lin a in a-lin-eq
  ... | unr rewrite Arr.ω⇒𝟙 a a-lin-eq = T-Weaken (≼-refl ∥-comm) $ T-AppUnr a-lin-eq (x≤y⊔x _ _) x′ y′
  ... | 𝟙
    with Arr.dir a in a-dir-eq
  ... | 𝟙 = T-Weaken (≼-refl ∥-comm) $ T-AppLin a-dir-eq (x≤y⊔x _ _) x′ y′
  ... | L = T-AppLeft a-dir-eq (x≤y⊔x _ _) (subst-ϵ (L⇒pure₁ refl) (sound x SΓ SΔ₁)) y′
  ... | R = T-AppRight a-dir-eq (x≤y⊔x _ _) x′ (subst-ϵ (R⇒pure₂ refl) (sound y SΓ SΔ₂))

  sound (A-Var ≤γ) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ) (T-Var _ refl)
  sound (A-Const ≤γ Ac ⊢c) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
             (T-Const (subConst-⊢ ⊢c))
  sound (A-LSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
             (T-Const (`lsplit (¬skips ∘ subTy-skips⁻¹) _))
  sound (A-RSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
             (T-Const (`rsplit (¬skips ∘ subTy-skips⁻¹) _))
  sound (A-App {Δ₁ = Δ₁} ≤γ L⇒pure₁ R⇒pure₂ x y) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
             (sound-app L⇒pure₁ R⇒pure₂ x y SΓ (All.++⁻ˡ Δ₁ SΔ ) (All.++⁻ʳ Δ₁ SΔ))
  sound (A-Seq {Δ₁ = Δ₁} unr-T ≤γ x y) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
             (T-Seq (subTy-unr unr-T)
                    (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                    (T-Conv ≃-refl (x≤y⊔x _ _) (sound y SΓ (All.++⁻ʳ Δ₁ SΔ))))
  sound (A-LetPair {T₁ = T₁} {T₂ = T₂} {Δ₁ = Δ₁} ≤γ x y) SΓ SΔ =
    let p/s , join≼ = parOrSeq? ≤γ in
    T-Weaken (≼-map⁺ subTy-unr join≼)
             (T-LetPair p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                            (T-Weaken (;-≼-join p/s) (T-Conv ≃-refl (x≤y⊔x _ _)
                              (sound y (solved-⸴ (subTy-solved T₁ Sσ) (solved-⸴ (subTy-solved T₂ Sσ) SΓ)) (All.++⁻ʳ Δ₁ SΔ)
                                ⊢≗ λ z → ⸴-dist (flip subTy σ) z ■ ⸴-cong refl (⸴-dist (flip subTy σ)) z))))
  sound {Γ = Γ} {γ} (A-Case {e} {e₁} {e₂} ≤₁ ≤₂ {ϵ} {ϵ₁} {ϵ₂} {T₁} {T₂} {Δ} {Δ₁} {Δ₂} x y₁ y₂) SΓ (U≃ ∷ SΔ)
    using SΔ₁ , SΔ₂ ← All.++⁻ Δ₁ (All.++⁻ʳ Δ SΔ)
    using x′  ← sound x SΓ (All.++⁻ˡ Δ SΔ)
    using y₁′ ← sound y₁ (solved-⸴ (subTy-solved T₁ Sσ) SΓ) SΔ₁ ⊢≗ ⸴-dist (flip subTy σ)
    using y₂′ ← sound y₂ (solved-⸴ (subTy-solved T₂ Sσ) SΓ) SΔ₂ ⊢≗ ⸴-dist (flip subTy σ)
    = {!!}
  {-
    let open ≼-Reasoning in
    let γu , γo , γuo≈γₑ , γu-U , γo-O = unjoinUnr Γ (γ ∣fv[ e ]) in
    let γₑ-γu-∁γₑ≼γ = begin
          γ ∣fv[ e ] ; (γu ∥ γ ∣∁fv[ e ]) ≡⟨ {!!} ⟩
          γ ∎
    in
    let yyy = begin
          [] ; ((γ ∣fv[ e ]) 𝐂.⋯ₛ 𝐂.weaken) ; ((` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₂))) ≲⟨ {!!} ⟩
          (` zero) ; ((γ ∣fv[ e ]) ; γ ↓ fvClose (fv e₂) 𝐂.Traversal.⋯ suc) ≲⟨ ≼-cong-; (≼-refl refl) (𝐂.≼-⋯ 𝐂.wk-preserves (≼-≗ {!!} ≤₂)) ⟩
          ` zero ; 𝐂.wk γ ∎
    in
    let zzz = ↓;↓≼⇒≼∁ (outside ∷ fv e) (inside ∷ fvClose (fv e₂)) {` zero ; 𝐂.wk γ}
                {!unjoinUnr (subCtx Γ σ) γ .proj₂ .proj₂ .proj₁!}
                {!!}
                {!!}
                (cong ([] ;_) (𝐂.⋯-congᶜ (γ ∣fv[ e ]) (λ _ → refl) ■ sym (↓-dist-wk γ {outside} {fv e})))
                (cong ((` zero) ;_) (sym (↓-dist-wk γ {inside} {fvClose (fv e₂)})))
                yyy
                (T-Weaken (≼-refl (≈-sym ;-unit₁)) $ x′ ⊢⋯ ⊢weakenᵣ (subCtx Γ σ))
                y₂′
    in
    let γ₂≼γu∥∁γ₂ = begin
          𝐂.wk (γ ↓ fvClose (fv e₂)) ≲⟨ {!!} ⟩
          {!!} ≡⟨ {!zzz!} ⟩
          𝐂.wk (γu ∥ γ ↓ ∁ (fv e)) ∎
    in
    T-Weaken γₑ-γu-∁γₑ≼γ
      $ T-Case seq
         {γ ∣fv[ e ]}         -- context structure for scrutinee
         {γu ∥ γ ↓ ∁ (fv e)}  -- some upper bound for context structures of the two branches
         (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤x⊔y ϵ ϵ₁)) x′)
         (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤y⊔x ϵ ϵ₁)) $
           T-Weaken ((≼-cong-; (≼-refl refl) {!zz!})) y₁′)
         (T-Conv (≃-sym U≃) (x≤y⊔x _ ϵ₂) $
           T-Weaken (≼-cong-; (≼-refl refl) γ₂≼γu∥∁γ₂) y₂′)
    {-
    let zz = ↓;↓≼⇒≼∁ {γ = (` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁))}
                     {X₁ = fv (wk e)}
                     {X₂ = inside ∷ fvClose (fv e₁)}
                     (begin (` zero ↓ fv (wk e))
                              ; 𝐂.wk (γ ↓ fvClose (fv e₁)) ↓ fv (wk e)
                              ; ((` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁)) ↓ (inside ∷ fvClose (fv e₁)))
                       ≡⟨ cong₂ _;_
                            (cong₂ _;_
                              (cong ((` zero) ↓_) (fv-wk e))
                              (cong (𝐂.wk (γ ↓ fvClose (fv e₁)) ↓_) (fv-wk e) ■ 𝐂.↓-dist-wk (γ ↓ fvClose (fv e₁))))
                            (cong (_ ;_) (𝐂.↓-dist-wk (γ ↓ fvClose (fv e₁)) ■ cong 𝐂.wk (↓-idempotent γ _))) ⟩
                         [] ; 𝐂.wk (γ ↓ fvClose (fv e₁) ↓ fv e) ; ((` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁)))
                       ≈⟨ ;-cong ;-unit₁ refl ⟩
                         𝐂.wk (γ ↓ fvClose (fv e₁) ↓ fv e) ; ((` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁)))
                       ≲⟨ ≼-cong-; {!≼-∅!} (≼-refl refl) ⟩
                         [] ; ((` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁)))
                       ≈⟨ ;-unit₁ ⟩
                         (` zero) ; 𝐂.wk (γ ↓ fvClose (fv e₁)) ∎)
                     (T-Weaken {!!} $ x′ ⊢⋯ ⊢weakenᵣ {T = subTy T₁ σ} (subCtx Γ σ) ⊢≗ ⸴-cons)
                     (subst-γ (cong (_ ;_) (sym (cong 𝐂.wk (↓-idempotent γ _)) ■ sym (𝐂.↓-dist-wk (γ ↓ fvClose (fv e₁))))) y₁′)
    in
    -}
    -- ≼-refl $ subst (λ fv[e] → _ ∶ γ ↓ fv[e] ; γ ↓ ∁ fv[e] ≈ _) (fv-subTm e)
    --        $ fv;∁fv≼ {γ = γ} $ subst-γ (cong (γ ↓_) (sym (fv-subTm e))) x′
  -}
  sound (A-Abs {T = T} unr-Γ mob-Γ ϵ≤ x) SΓ SΔ =
    T-Abs (allCx-gmap subTy-unr ∘ unr-Γ) (allCx-gmap subTy-mobile ∘ mob-Γ)
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ (subTy-solved T Sσ) SΓ) SΔ ⊢≗ sym ∘ ⸴-cons
  sound {Γ = Γ} (A-AbsRec {T = T} {U = U} unr-Γ unr-a ϵ≤ x) SΓ SΔ =
    let T′  = subTy-solved T Sσ in
    let T→U = T′ ⟨ _ ⟩→ subTy-solved U Sσ in
    T-AbsRec (allCx-gmap subTy-unr unr-Γ) unr-a
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ T′ (solved-⸴ T→U SΓ)) SΔ ⊢≗ λ k → {!!}
  sound (A-Pair p/s {ϵ₁} {ϵ₂} ≤γ seq⇒pure x y) SΓ SΔ =
    let _ , _ , ≤ϵ₁ , ≤ϵ₂ , ≤ϵ⊔ , S⇒P = mk-seq⇒pure seq⇒pure in
    T-Weaken (≼-map⁺ subTy-unr ≤γ)
      $ T-Conv ≃-refl ≤ϵ⊔
      $ T-Pair p/s S⇒P
          (T-Conv ≃-refl ≤ϵ₁ (sound x SΓ {!!}))
          (T-Conv ≃-refl ≤ϵ₂ (sound y SΓ {!!}))
  sound (A-Inj {i = i} x) SΓ SΔ =
    T-Inj
      $ subst (_ ; _ ⊢ _ ∶_∣ _) (if-float (flip subTy σ) i)
      $ sound x SΓ SΔ
  sound (A-Ann x) SΓ SΔ =
    sound x SΓ SΔ
  sound (A-Check x) SΓ (eq ∷ SΔ) =
    T-Conv (≃-sym eq) ≤ϵ-refl
      $ sound x SΓ SΔ

complete :
  Un.Π[ SolvedTy ∘ Γ ] →
  SolvedTm e →
  SolvedTy T →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∃[ σ ] ∃[ Δ ] ∃[ n ]
     Solving σ × SolvedΔ Δ σ × Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n
complete SΓ Se ST (T-Const {c = c} ⊢c) with algConst? c
... | inj₁ Ac =
  UV.someSub , _ , _ , (λ _ → end) , ≃-refl ∷ []
    , A-Check (A-Const (≼-∅ []) Ac ⊢c)
... | inj₂ ¬Ac = {!¬Ac!}
-- ... | yes (_ , inj₁ refl) =
--   record { ap = {!!} ; ap-¬skips = {!!} ; ap-dual/dual = {!!} }
--     , {!!} , {!!} , {!!} , {!!} , A-Check (A-LSplit (≼-∅ []) {!!})
-- ... | yes (_ , inj₂ refl) = {!!}
complete SΓ Se ST (T-Var x T-eq) = {!!}
complete SΓ Se ST (T-Abs Γ-unr Γ-mob x) = {!!}
complete SΓ Se ST (T-AbsRec Γ-unr a-unr x) = {!!}
complete SΓ Se ST (T-AppUnr a-unr ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-AppLin a-par ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-AppLeft aL ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-AppRight aR ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-Pair p/s seq⇒p x x₁) = {!!}
complete SΓ Se ST (T-Seq unr-T x y) = {!!}
complete SΓ Se ST (T-LetPair p/s x y) = {!!}
complete SΓ Se ST (T-Inj x) = {!!}
complete SΓ Se ST (T-Case p/s x y₁ y₂) = {!!}
complete SΓ Se ST (T-Conv T≃ ϵ≤ x) = {!!}
complete SΓ Se ST (T-Weaken γ≤ x) = {!!}
-- complete (T-Const {c = c} ⊢c) Se ST with isSplit? c
-- complete (T-Const {c = _} (`lsplit s s′)) Se ST@(⟨ Ss ; Ss′ ⟩ ⟨ _ ⟩→ Sc) | yes (_ , inj₁ refl) =
--   let Sσs  = subTy-solved Ss in
--   let Sσs′ = subst SolvedTy (sym (𝐓.⋯-id s′ λ())) Ss′ in
--   let σ[s′]≃wk[s′] = ≃-reflexive (subTy-id Ss′ ■ sym (𝐓.⋯-id s′ λ())) in
--   _ , const s′
--     , (subTy-solved ST , ⟨ Sσs ; Sσs′ ⟩ ⟨ _ ⟩→ ⟨ Sσs ⟩ ⊗⟨ L ⟩ ⟨ Sσs′ ⟩ ,
--         ⟨ ≃-; ≃-refl σ[s′]≃wk[s′] ⟩ `→ (≃-refl ⊗ ⟨ σ[s′]≃wk[s′] ⟩)) ∷ []
--     , A-Check (A-LSplit (≼-refl refl))
-- complete (T-Const {c = _} (`rsplit s s′)) Se ST | yes (_ , inj₂ refl) = {!!}
-- ... | no no-split =
--   _ , const skip
--     , (subTy-solved ST , subTy-solved ST , ≃-refl) ∷ []
--     , A-Check (A-Const (≼-refl refl) (λ s z → no-split (s , inj₁ z)) (λ s z → no-split (s , inj₂ z)) ⊢c)
-- complete (T-Var x T-eq) Se ST = {!!}
-- complete (T-Abs Γ-unr Γ-mob e) Se ST = {!!}
-- complete (T-AbsRec x x₁ e) Se ST = {!!}
-- complete (T-AppUnr x f e) S[fe] ST =
--   let _ , σf , Sf , Af = complete f {!!} {!!} in
--   _ , {!!} , {!!}
--     , A-Check (A-App {!!} {!!} {!!} {!Af!} {!!})
-- complete (T-AppLin x e e₁) Se ST = {!!}
-- complete (T-AppLeft x e e₁) Se ST = {!!}
-- complete (T-AppRight x e e₁) Se ST = {!!}
-- complete (T-Pair p/s e e₁ x) Se ST = {!!}
-- complete (T-Let p/s e e₁) Se ST = {!!}
-- complete (T-LetUnit p/s e e₁) Se ST = {!!}
-- complete (T-LetPair p/s e e₁) Se ST = {!!}
-- complete (T-Inj e) Se ST = {!!}
-- complete (T-Case p/s e e₁ e₂) Se ST = {!!}
-- complete (T-Conv T≃ ϵ≤ e) Se ST = {!!}
-- complete (T-Weaken γ≤ e) Se ST = {!!}
