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

_∣fv[_] : Struct n → Tm n → Struct n
γ ∣fv[ e ] = γ ↓ fv e

data Mode : Set where
  chk inf : Mode

private variable ξ : Mode

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
    (≢lsplit : ∀ s → c ≢ `lsplit s) →
    (≢rsplit : ∀ s → c ≢ `rsplit s) →
    ⊢ c ∶ T →
    --------------------------------
    Γ ; γ / m ⊢ K c ⇒ T ∣ ℙ ↑ [] / m

  A-LSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ) →
    ¬ Skips s →
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`lsplit s) ⇒ ⟨ s ; `` α ⟩ →1M ⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-RSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ) →
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

  A-LetUnit :
    (≤γ : Γ ∶ γ ∣fv[ e₁ ] ; γ ∣fv[ e₂ ] ≼ γ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇐ `⊤ ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇒ T  ∣ ϵ₂ ↑ Δ₂ / n  →
    -------------------------------------------------
    Γ ; γ / m ⊢ e₁ ; e₂ ⇒ T ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

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
    (≤γ : Γ ∶ join d (γ ∣fv[ e₁ ]) (γ ∣fv[ e₂ ]) ≼ γ) →
    (L⇒pure₁ : d ≡ L → ϵ₂ ≡ ℙ) →
    (R⇒pure₂ : d ≡ R → ϵ₁ ≡ ℙ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇐ T ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ / n  →
    ----------------------------------------------------------
    Γ ; γ / m ⊢ e₁ ⊗ e₂ ⇐ T ⊗⟨ d ⟩ U ∣ ϵ₁ ⊔ϵ ϵ₂ ↑ Δ₁ ++ Δ₂ / n

  A-Inj : ∀ {i} →
    Γ ; γ / m ⊢ e ⇐ if i then T₁ else T₂ ∣ ϵ ↑ Δ / n →
    --------------------------------------------------
    Γ ; γ / m ⊢ `inj i e ⇐ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / n

  A-Check :
    Γ ; γ / m ⊢ e ⇒ U ∣ ϵ ↑ Δ / n →
    ---------------------------------------
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ (T , U) ∷ Δ / n

sound :
  Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n →
  (∀ x → SolvedTy (subTy (Γ x) σ)) →
  SolvedΔ Δ σ →
  -- ∃[ e′ ] e ─→η e′ ×
  flip subTy σ ∘ Γ ; γ ⊢ subTm e σ ∶ subTy T σ ∣ ϵ

sound-app :
  (Arr.dir a ≡ L → ϵ₁ ≡ ℙ) →
  (Arr.dir a ≡ R → ϵ₂ ≡ ℙ) →
  Γ ; γ₁ / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
  Γ ; γ₂ / m′ ⊢ e₂ ⇐ T          ∣ ϵ₂ ↑ Δ₂ / n  →
  (∀ x → SolvedTy (subTy (Γ x) σ)) →
  SolvedΔ Δ₁ σ →
  SolvedΔ Δ₂ σ →
--  ∃[ e₁′ ] ∃[ e₂′ ]
--    e₁ ─→η e₁′ × e₂ ─→η e₂′ ×
      flip subTy σ ∘ Γ ; join (Arr.dir a) γ₂ γ₁
        ⊢ subTm (e₁ · e₂) σ ∶ subTy U σ ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a

sound-app {a = a} L⇒pure₁ R⇒pure₂ x y SΓ SΔ₁ SΔ₂
  with Arr.lin a in a-lin-eq
... | unr rewrite Arr.ω⇒𝟙 a a-lin-eq =
  T-Weaken (≼-refl ∥-comm)
    $ T-AppUnr a-lin-eq
        (x≤y⇒x≤y⊔z (Arr.eff a) (x≤x⊔y _ _)) (x≤y⇒x≤y⊔z (Arr.eff a) (x≤y⊔x _ _)) (x≤y⊔x _ _)
        (sound x SΓ SΔ₁) (sound y SΓ SΔ₂)
... | 𝟙
  with Arr.dir a in a-dir-eq
... | 𝟙 =
  T-Weaken (≼-refl ∥-comm)
    $ T-AppLin a-dir-eq
        (x≤y⇒x≤y⊔z (Arr.eff a) (x≤x⊔y _ _)) (x≤y⇒x≤y⊔z (Arr.eff a) (x≤y⊔x _ _)) (x≤y⊔x _ _)
        (sound x SΓ SΔ₁) (sound y SΓ SΔ₂)
... | L = T-AppLeft a-dir-eq (x≤y⇒x≤y⊔z (Arr.eff a) (x≤y⊔x _ _)) (x≤y⊔x _ _)
            (subst-ϵ (L⇒pure₁ refl) (sound x SΓ SΔ₁)) (sound y SΓ SΔ₂)
... | R = T-AppRight a-dir-eq (x≤y⇒x≤y⊔z (Arr.eff a) (x≤x⊔y _ _)) (x≤y⊔x _ _)
            (sound x SΓ SΔ₁) (subst-ϵ (R⇒pure₂ refl) (sound y SΓ SΔ₂))

sound {σ = σ} (A-Var ≤γ) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ) (T-Var _ refl)
sound (A-Const ≤γ ≢lsplit ≢rsplit ⊢c) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ)
           (T-Const (subConst-⊢ ⊢c))
sound {σ = σ} (A-LSplit ≤γ ¬skips) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ)
           (T-Const (`lsplit (¬skips ∘ subTy-skips⁻¹) _))
sound (A-RSplit ≤γ) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ)
           (T-Const (`rsplit _ _))
sound (A-App {Δ₁ = Δ₁} ≤γ L⇒pure₁ R⇒pure₂ x y) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ)
           (sound-app L⇒pure₁ R⇒pure₂ x y SΓ (All.++⁻ˡ Δ₁ SΔ ) (All.++⁻ʳ Δ₁ SΔ))
sound (A-LetUnit {Δ₁ = Δ₁} ≤γ x y) SΓ SΔ =
  T-Weaken (≼-map⁺ subTy-unr ≤γ)
           (T-LetUnit (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ )))
                      (T-Conv ≃-refl (x≤y⊔x _ _) (sound y SΓ (All.++⁻ʳ Δ₁ SΔ ))))
sound {σ = σ} (A-LetPair {Δ₁ = Δ₁} ≤γ x y) SΓ SΔ =
  let p/s , join≼ = parOrSeq? ≤γ in
  T-Weaken (≼-map⁺ subTy-unr join≼)
           (T-LetPair p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                          (T-Weaken (;-≼-join p/s) (T-Conv ≃-refl (x≤y⊔x _ _) (sound y {!f!} (All.++⁻ʳ Δ₁ SΔ)
                            ⊢≗ λ z → ⸴-dist (flip subTy σ) z ■ ⸴-cong refl (⸴-dist (flip subTy σ)) z))))
sound {σ = σ} (A-Case {Δ = Δ} {Δ₁ = Δ₁} ≤γ₁ ≤γ₂ x y₁ y₂) SΓ ((SU₁ , SU₂ , U≃) ∷ SΔ) =
  let SΔ₁ , SΔ₂ = All.++⁻ Δ₁ (All.++⁻ʳ Δ SΔ) in
  T-Weaken {!!} $ T-Case seq
    (T-Conv ≃-refl {!!} (sound x SΓ (All.++⁻ˡ Δ SΔ)))
    (T-Conv ≃-refl {!!} (sound y₁ (λ{ zero → {!!}; (suc x) → SΓ x }) SΔ₁ ⊢≗ ⸴-dist (flip subTy σ)))
    (T-Conv (≃-sym U≃) {!!} (sound y₂ (λ{ zero → {!SU₂!}; (suc x) → SΓ x }) SΔ₂ ⊢≗ ⸴-dist (flip subTy σ)))
sound (A-Abs x x₁ x₂ x₃) SΓ SΔ = {!!}
sound (A-AbsRec x x₁ x₂ x₃) SΓ SΔ = {!!}
sound (A-Pair ≤γ L⇒pure₁ R⇒pure₂ x x₁) SΓ SΔ = {!!}
sound (A-Inj x) SΓ SΔ = {!!}
sound (A-Check x) SΓ SΔ = {!sound x!}

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
