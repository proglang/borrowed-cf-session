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

open import BorrowedCF.Algorithmic.Split public
open import BorrowedCF.Algorithmic.LinUnique
open import BorrowedCF.Algorithmic.SoundSplit
open import BorrowedCF.Algorithmic.Strengthen

fv-subTm : (e : Tm n) → fv (subTm e σ) ≡ fv e
fv-subTm (` x) = refl
fv-subTm (K c) = refl
fv-subTm (ƛ e) = cong fvClose (fv-subTm e)
fv-subTm (μ e) = cong fvClose (fv-subTm e)
fv-subTm (e ·⟨ _ ⟩ e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (e ; e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (e ⊗ e₁) = cong₂ _∪_ (fv-subTm e) (fv-subTm e₁)
fv-subTm (`let e `in e₁) = cong₂ _∪_ (fv-subTm e) (cong fvClose (fv-subTm e₁))
fv-subTm (`let⊗ e `in e₁) = cong₂ _∪_ (fv-subTm e) (cong (fvClose* 2) (fv-subTm e₁))
fv-subTm (`inj i e) = fv-subTm e
fv-subTm `case e `of⟨ e₁ ; e₂ ⟩ = cong₂ _∪_ (fv-subTm e) (cong₂ _∪_ (cong fvClose (fv-subTm e₁)) (cong fvClose (fv-subTm e₂)))

{-
postulate
  fv-wk : (e : Tm n) → fv (wk e) ≡ outside ∷ fv e
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


data Mode : Set where
  chk inf : Mode

private variable ξ : Mode

EffCompat : Dir → Rel Eff 0ℓ
EffCompat L ϵ₁ ϵ₂ = ϵ₂ ≡ ℙ
EffCompat R ϵ₁ ϵ₂ = ϵ₁ ≡ ℙ
EffCompat 𝟙 ϵ₁ ϵ₂ = Unit.⊤

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
algConst? `discard    = inj₁ λ()
algConst? (`lsplit x) = inj₂ `lsplit
algConst? (`rsplit x) = inj₂ `rsplit
algConst? (`select x) = inj₂ `select
algConst? `branch     = inj₂ `branch

allMobile : Ctx n → Struct n → List Constraint
allMobile Γ (` x) = L.[ C-Mob (Γ x) ]
allMobile Γ [] = []
allMobile Γ (α ∥ β) = allMobile Γ α ++ allMobile Γ β
allMobile Γ (α ; β) = allMobile Γ α ++ allMobile Γ β

mobConstraints : Mob → Ctx n → Struct n → List Constraint
mobConstraints M Γ γ = allMobile Γ γ
mobConstraints S Γ γ = []

data JoinParSeq (Γ : Ctx n) (γ : Struct n) (X : Subset n) : ParSeq → Set where
  par : Γ ∶ (γ ↓ X) ∥ (γ ↓ ∁ X) ≼ γ → JoinParSeq Γ γ X par
  seq : Γ ∶ (γ ↓ X) ; (γ ↓ ∁ X) ≼ γ → JoinParSeq Γ γ X seq

join-joinParSeq : ∀ {X p/s} → JoinParSeq Γ γ X p/s → Γ ∶ join p/s (γ ↓ X) (γ ↓ ∁ X) ≼ γ
join-joinParSeq (par x) = x
join-joinParSeq (seq x) = x

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
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`lsplit s) ⇒ ⟨ s ; `` α ⟩ →*M ⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-RSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ) →
    -----------------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`rsplit s) ⇒ ⟨ s ; `` α ⟩ →*M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-App :
    EffCompat (Arr.dir a) ϵ₂ ϵ₁ →
    (≤γ : Γ ∶ join (Arr.dir a) (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ) →
    Γ ; γ ∣fv[ e₁ ] / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ ∣fv[ e₂ ] / m′ ⊢ e₂ ⇐ T ∣ ϵ₂ ↑ Δ₂ / n →
    --------------------------------------------------------------
    Γ ; γ / m ⊢ e₁ ·⟨ Arr.dir a ⟩ e₂ ⇒ U ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a ↑ Δ₁ ++ Δ₂ / n

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

  A-Case : (p/s : ParSeq) →
    let γ′ = γ ↓ ∁ (fv e) in
    JoinParSeq Γ γ (fv e) p/s →
    ∀ {ϵ ϵ₁ ϵ₂ T₁ T₂ Δ Δ₁ Δ₂} →
    Γ ; γ ∣fv[ e ] / m ⊢ e ⇒ T₁ ⊕ T₂ ∣ ϵ ↑ Δ / m₁ →
    T₁ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ′) / m₁ ⊢ e₁ ⇒ U₁ ∣ ϵ₁ ↑ Δ₁ / m₂ →
    T₂ ⸴ Γ ; join p/s (` zero) (𝐂.wk γ′) / m₂ ⊢ e₂ ⇒ U₂ ∣ ϵ₂ ↑ Δ₂ / n  →
    ---------------------------------------------------------------------------------------
    Γ ; γ / m ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ⇒ U₁ ∣ ϵ ⊔ϵ ϵ₁ ⊔ϵ ϵ₂ ↑ C-Eq U₁ U₂ ∷ Δ ++ Δ₁ ++ Δ₂ / n

  A-Abs :
    (Arr.Unr a → UnrCx Γ γ) →
    ϵ ≤ϵ Arr.eff a →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) / m ⊢ e ⇐ U ∣ ϵ ↑ Δ / n →
    Δ′ ≡ mobConstraints (Arr.mob a) Γ γ →
    --------------------------------------------------------------------
    Γ ; γ / m ⊢ ƛ e ⇐ T ⟨ a ⟩→ U ∣ ℙ ↑ Δ′ ++ Δ / n

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
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ C-Eq T U ∷ Δ / n

  A-Ann :
    Γ ; γ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / n →
    -------------------------------
    Γ ; γ / m ⊢ e ⇒ T ∣ ϵ ↑ Δ / n

private
  ty : Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n → 𝕋
  ty {T = T} _ = T

module _ {σ : UV.Sub} (Sσ : Solving σ) where
  open EffProperties

  mobConstraints⇒MobCx : (Γ : Ctx n)(γ : Struct n) → SolvedΔ (allMobile Γ γ) σ → MobCx (subCtx Γ σ) γ
  mobConstraints⇒MobCx Γ (` x) (px ∷ Sm) = ` px
  mobConstraints⇒MobCx Γ [] Sm = []
  mobConstraints⇒MobCx Γ (α ∥ β) Sm = mobConstraints⇒MobCx Γ α (All.++⁻ˡ (allMobile Γ α) Sm) ∥ mobConstraints⇒MobCx Γ β (All.++⁻ʳ (allMobile Γ α) Sm)
  mobConstraints⇒MobCx Γ (α ; β) Sm = mobConstraints⇒MobCx Γ α (All.++⁻ˡ (allMobile Γ α) Sm) ; mobConstraints⇒MobCx Γ β (All.++⁻ʳ (allMobile Γ α) Sm)

  sound :
    Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / n →
    SolvedΓ Γ σ →
    SolvedΔ Δ σ →
    subCtx Γ σ ; γ ⊢ subTm e σ ∶ subTy T σ ∣ ϵ

  sound-app :
    EffCompat (Arr.dir a) ϵ₂ ϵ₁ →
    Γ ; γ₁ / m  ⊢ e₁ ⇒ T ⟨ a ⟩→ U ∣ ϵ₁ ↑ Δ₁ / m′ →
    Γ ; γ₂ / m′ ⊢ e₂ ⇐ T          ∣ ϵ₂ ↑ Δ₂ / n  →
    SolvedΓ Γ σ →
    SolvedΔ Δ₁ σ →
    SolvedΔ Δ₂ σ →
    subCtx Γ σ ; join (Arr.dir a) γ₂ γ₁
      ⊢ subTm (e₁ ·⟨ Arr.dir a ⟩ e₂) σ ∶ subTy U σ ∣ ϵ₁ ⊔ϵ ϵ₂ ⊔ϵ Arr.eff a

  sound-app {a = a} ec x y SΓ SΔ₁ SΔ₂
    using x′ ← T-Conv ≃-refl (x≤y⇒x≤y⊔z (Arr.eff a) (x≤x⊔y _ _)) (sound x SΓ SΔ₁)
    using y′ ← T-Conv ≃-refl (x≤y⇒x≤y⊔z (Arr.eff a) (x≤y⊔x _ _)) (sound y SΓ SΔ₂)
    with Arr.lin a in a-lin-eq
  ... | unr rewrite Arr.ω⇒𝟙 a a-lin-eq =
    T-Weaken (≼-refl ∥-comm) $ T-AppUnr a-lin-eq (x≤y⊔x _ _) x′ y′
  ... | 𝟙
    with Arr.dir a in a-dir-eq
  ... | 𝟙 = T-Weaken (≼-refl ∥-comm) $ T-AppLin (a-lin-eq , a-dir-eq) (x≤y⊔x _ _) x′ y′
  ... | L = T-AppLeft a-dir-eq (x≤y⊔x _ _) (subst-ϵ ec (sound x SΓ SΔ₁)) y′
  ... | R = T-AppRight a-dir-eq (x≤y⊔x _ _) x′ (subst-ϵ ec (sound y SΓ SΔ₂))

  sound (A-Var ≤γ) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ) (T-Var _ refl)
  sound (A-Const ≤γ Ac ⊢c) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Const (subConst-⊢ ⊢c))
  sound (A-LSplit ≤γ) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Const (`lsplit _ _ (UV.ap-¬skips σ _ ∘ skips-⋯ᵣ⁻¹)))
  sound (A-RSplit ≤γ) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Const (`rsplit _ _ (UV.ap-¬skips σ _ ∘ skips-⋯ᵣ⁻¹)))
  sound (A-App {Δ₁ = Δ₁} ec ≤γ x y) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (sound-app ec x y SΓ (All.++⁻ˡ Δ₁ SΔ ) (All.++⁻ʳ Δ₁ SΔ))
  sound (A-Seq {Δ₁ = Δ₁} unr-T ≤γ x y) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Seq (subTy-unr unr-T)
                    (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                    (T-Conv ≃-refl (x≤y⊔x _ _) (sound y SΓ (All.++⁻ʳ Δ₁ SΔ))))
  sound (A-LetPair {T₁ = T₁} {T₂ = T₂} {Δ₁ = Δ₁} ≤γ x y) SΓ SΔ =
    let p/s , join≼ = parOrSeq? ≤γ in
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile join≼)
             (T-LetPair p/s (T-Conv ≃-refl (x≤x⊔y _ _) (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
                            (T-Weaken (;-≼-join p/s) (T-Conv ≃-refl (x≤y⊔x _ _)
                              (sound y (solved-⸴ (subTy-solved T₁ Sσ) (solved-⸴ (subTy-solved T₂ Sσ) SΓ)) (All.++⁻ʳ Δ₁ SΔ)
                                ⊢≗ λ z → ⸴-dist (flip subTy σ) z ■ ⸴-cong refl (⸴-dist (flip subTy σ)) z))))
  sound {Γ = Γ} {γ} (A-Case {e} {e₁} {e₂} p/s j-p/s {ϵ} {ϵ₁} {ϵ₂} {T₁} {T₂} {Δ} {Δ₁} {Δ₂} x y₁ y₂) SΓ (U≃ ∷ SΔ)
    using SΔ₁ , SΔ₂ ← All.++⁻ Δ₁ (All.++⁻ʳ Δ SΔ)
    using x′  ← sound x SΓ (All.++⁻ˡ Δ SΔ)
    using y₁′ ← sound y₁ (solved-⸴ (subTy-solved T₁ Sσ) SΓ) SΔ₁ ⊢≗ ⸴-dist (flip subTy σ)
    using y₂′ ← sound y₂ (solved-⸴ (subTy-solved T₂ Sσ) SΓ) SΔ₂ ⊢≗ ⸴-dist (flip subTy σ)
    =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile (join-joinParSeq j-p/s)) $
      T-Case p/s
        (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤x⊔y ϵ ϵ₁)) x′)
        (T-Conv ≃-refl (x≤y⇒x≤y⊔z ϵ₂ (x≤y⊔x ϵ ϵ₁)) y₁′)
        (T-Conv (≃-sym U≃) (x≤y⊔x _ ϵ₂) y₂′)
  sound {Γ = Γ} {γ = γ} (A-Abs {T = T}{Δ′ = Δ′} unr-Γ ϵ≤ x refl) SΓ SΔ =
    T-Abs (allCx-gmap subTy-unr ∘ unr-Γ) (λ{ refl → mobConstraints⇒MobCx Γ γ (All.++⁻ˡ Δ′ SΔ) })
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ (subTy-solved T Sσ) SΓ) (All.++⁻ʳ Δ′ SΔ) ⊢≗ sym ∘ ⸴-cons
  sound {Γ = Γ} (A-AbsRec {T = T} {U = U} unr-Γ unr-a ϵ≤ x) SΓ SΔ =
    let open Fin.Patterns in
    let T′  = subTy-solved T Sσ in
    let T→U = T′ ⟨ _ ⟩→ subTy-solved U Sσ in
    T-AbsRec (allCx-gmap subTy-unr unr-Γ) unr-a
      $ T-Conv ≃-refl ϵ≤
      $ sound x (solved-⸴ T′ (solved-⸴ T→U SΓ)) SΔ ⊢≗ λ where
          0F → refl
          1F → refl
          (suc (suc k)) → refl
  sound (A-Pair {Δ₁ = Δ₁} p/s {ϵ₁} {ϵ₂} ≤γ seq⇒pure x y) SΓ SΔ =
    let _ , _ , ≤ϵ₁ , ≤ϵ₂ , ≤ϵ⊔ , S⇒P = mk-seq⇒pure seq⇒pure in
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
      $ T-Conv ≃-refl ≤ϵ⊔
      $ T-Pair p/s S⇒P
          (T-Conv ≃-refl ≤ϵ₁ (sound x SΓ (All.++⁻ˡ Δ₁ SΔ)))
          (T-Conv ≃-refl ≤ϵ₂ (sound y SΓ (All.++⁻ʳ Δ₁ SΔ)))
  sound (A-Inj {i = i} x) SΓ SΔ =
    T-Inj
      $ subst (_ ; _ ⊢ _ ∶_∣ _) (if-float (flip subTy σ) i)
      $ sound x SΓ SΔ
  sound (A-Ann x) SΓ SΔ =
    sound x SΓ SΔ
  sound (A-Check x) SΓ (eq ∷ SΔ) =
    T-Conv (≃-sym eq) ≤ϵ-refl
      $ sound x SΓ SΔ

subAll-solving : (¬Ss : ¬ Skips s) → SolvedTy s → Solving (UV.subAll ¬Ss)
subAll-solving ¬Ss x (uvar ‼ var) = x
subAll-solving ¬Ss x (uvar ⁇ var) = solved-dual x

someSub-solving : Solving UV.someSub
someSub-solving = subAll-solving (λ ()) end

------------------------------------------------------------------------
-- Type (unification-variable) substitution preserves declarative typing.
-- Instantiating with a Solving σ (e.g. someSub) makes every type in the
-- derivation `subTy _ σ`, hence solved: this is the "any subterm can be
-- typed with a solved type" fact needed by completeness.
------------------------------------------------------------------------

⊢-sub : (σ : UV.Sub) → Γ ; γ ⊢ e ∶ T ∣ ϵ → subCtx Γ σ ; γ ⊢ subTm e σ ∶ subTy T σ ∣ ϵ
⊢-sub σ (T-Const ⊢c) = T-Const (subConst-⊢ ⊢c)
⊢-sub σ (T-Var x refl) = T-Var x refl
⊢-sub σ (T-Abs Γ-unr Γ-mob d) =
  T-Abs (allCx-gmap subTy-unr ∘ Γ-unr) (allCx-gmap subTy-mobile ∘ Γ-mob)
        (⊢-sub σ d ⊢≗ ⸴-dist (flip subTy σ))
⊢-sub σ (T-AbsRec Γ-unr a-unr d) =
  T-AbsRec (allCx-gmap subTy-unr Γ-unr) a-unr
           (⊢-sub σ d ⊢≗ λ z → ⸴-dist (flip subTy σ) z ■ ⸴-cong refl (⸴-dist (flip subTy σ)) z)
⊢-sub σ (T-AppUnr a-unr ≤ₐ d₁ d₂) = T-AppUnr a-unr ≤ₐ (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-AppLin a-par ≤ₐ d₁ d₂) = T-AppLin a-par ≤ₐ (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-AppLeft aL ≤ₐ d₁ d₂) = T-AppLeft aL ≤ₐ (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-AppRight aR ≤ₐ d₁ d₂) = T-AppRight aR ≤ₐ (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-Pair p/s seq⇒p d₁ d₂) = T-Pair p/s seq⇒p (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-Let p/s d₁ d₂) = T-Let p/s (⊢-sub σ d₁) (⊢-sub σ d₂ ⊢≗ ⸴-dist (flip subTy σ))
⊢-sub σ (T-Seq unr-T d₁ d₂) = T-Seq (subTy-unr unr-T) (⊢-sub σ d₁) (⊢-sub σ d₂)
⊢-sub σ (T-LetPair p/s d₁ d₂) =
  T-LetPair p/s (⊢-sub σ d₁)
            (⊢-sub σ d₂ ⊢≗ λ z → ⸴-dist (flip subTy σ) z ■ ⸴-cong refl (⸴-dist (flip subTy σ)) z)
⊢-sub σ (T-Inj {i = i} d) =
  T-Inj (subst (_ ; _ ⊢ _ ∶_∣ _) (if-float (flip subTy σ) i) (⊢-sub σ d))
⊢-sub σ (T-Case p/s d d₁ d₂) =
  T-Case p/s (⊢-sub σ d)
             (⊢-sub σ d₁ ⊢≗ ⸴-dist (flip subTy σ))
             (⊢-sub σ d₂ ⊢≗ ⸴-dist (flip subTy σ))
⊢-sub σ (T-Conv T≃ ϵ≤ d) = T-Conv (subTy-≃ T≃) ϵ≤ (⊢-sub σ d)
⊢-sub σ (T-Weaken γ≤ d) = T-Weaken (≼-map⁺ subTy-unr subTy-mobile γ≤) (⊢-sub σ d)

------------------------------------------------------------------------
-- Completeness infrastructure.
------------------------------------------------------------------------

height : Γ ; γ ⊢ e ∶ T ∣ ϵ → ℕ
height (T-Const _) = 0
height (T-Var _ _) = 0
height (T-Abs _ _ d) = suc (height d)
height (T-AbsRec _ _ d) = suc (height d)
height (T-AppUnr _ _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-AppLin _ _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-AppLeft _ _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-AppRight _ _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-Pair _ _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-Let _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-Seq _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-LetPair _ d₁ d₂) = suc (height d₁ Nat.⊔ height d₂)
height (T-Inj d) = suc (height d)
height (T-Case _ d d₁ d₂) = suc (height d Nat.⊔ height d₁ Nat.⊔ height d₂)
height (T-Conv _ _ d) = suc (height d)
height (T-Weaken _ d) = suc (height d)

reType : Un.Π[ SolvedTy ∘ Γ ] → SolvedTm e → SolvedTy T → Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ⊢ e ∶ T ∣ ϵ
reType SΓ Se ST d =
  subst (λ e′ → _ ; _ ⊢ e′ ∶ _ ∣ _) (subTm-id Se)
    (subst (λ T′ → _ ; _ ⊢ _ ∶ T′ ∣ _) (subTy-id ST)
      (⊢-sub UV.someSub d ⊢≗ λ x → subTy-id (SΓ x)))

postulate
  merge₂ : ∀ {σ₁ σ₂ Δ₁ Δ₂} → Solving σ₁ → Solving σ₂ → SolvedΔ Δ₁ σ₁ → SolvedΔ Δ₂ σ₂ →
           ∃[ σ ] Solving σ × SolvedΔ (Δ₁ ++ Δ₂) σ


⸴Π : SolvedTy T → Un.Π[ SolvedTy ∘ Γ ] → Un.Π[ SolvedTy ∘ (T ⸴ Γ) ]
⸴Π ST SΓ zero = ST
⸴Π ST SΓ (suc x) = SΓ x

mobΔ-M : ∀ {n} {Γ : Ctx n} {σ} (γ : Struct n) → MobCx Γ γ → SolvedΔ (allMobile Γ γ) σ
mobΔ-M (` x) (` m) = subTy-mobile m ∷ []
mobΔ-M [] [] = []
mobΔ-M (α ∥ β) (mα ∥ mβ) = All.++⁺ (mobΔ-M α mα) (mobΔ-M β mβ)
mobΔ-M (α ; β) (mα ; mβ) = All.++⁺ (mobΔ-M α mα) (mobΔ-M β mβ)

mobΔ : ∀ {n} {Γ : Ctx n} {γ a σ} → (Arr.Mobile a → MobCx Γ γ) →
       SolvedΔ (mobConstraints (Arr.mob a) Γ γ) σ
mobΔ {Γ = Γ} {γ = γ} {a = a} f = go (Arr.mob a) refl
  where
  go : (m : Mob) → Arr.mob a ≡ m → SolvedΔ (mobConstraints m Γ γ) _
  go M eq = mobΔ-M _ (f eq)
  go S eq = []


substγ-height : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ e T ϵ} (eq : γ₁ ≡ γ₂) (d : Γ ; γ₁ ⊢ e ∶ T ∣ ϵ) →
                height (subst (λ z → Γ ; z ⊢ e ∶ T ∣ ϵ) eq d) ≡ height d
substγ-height refl d = refl

⊢-↓-height : ∀ {n} {Γ : Ctx n} {γ e T ϵ X} (fv⊆ : fv e ⊆ X) (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) →
             height (⊢-↓ fv⊆ d) ≡ height d
⊢-↓-height _ (T-Const ⊢c) = refl
⊢-↓-height fv⊆ (T-Var x refl) = substγ-height _ (T-Var x refl)
⊢-↓-height fv⊆ (T-Abs Γ-unr Γ-mob d) = cong suc (substγ-height _ (⊢-↓ (fvClose-⊆ fv⊆) d) ■ ⊢-↓-height (fvClose-⊆ fv⊆) d)
⊢-↓-height fv⊆ (T-AbsRec Γ-unr a-unr d) = cong suc (substγ-height _ (⊢-↓ (fvClose-⊆ (fvClose-⊆ fv⊆)) d) ■ ⊢-↓-height (fvClose-⊆ (fvClose-⊆ fv⊆)) d)
⊢-↓-height fv⊆ (T-AppUnr a-unr ≤ₐ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-AppLin a-par ≤ₐ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-AppLeft aL ≤ₐ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-AppRight aR ≤ₐ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-Pair p/s seq⇒p d₁ d₂) = substγ-height _ _ ■ cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-Seq unr-T d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (⊢-↓-height (S.⊆-trans (S.q⊆p∪q _ _) fv⊆) d₂))
⊢-↓-height fv⊆ (T-Let p/s d₁ d₂) = substγ-height _ _ ■ cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (substγ-height _ (⊢-↓ (fvClose-⊆ (S.⊆-trans (S.q⊆p∪q _ _) fv⊆)) d₂) ■ ⊢-↓-height (fvClose-⊆ (S.⊆-trans (S.q⊆p∪q _ _) fv⊆)) d₂))
⊢-↓-height fv⊆ (T-LetPair p/s d₁ d₂) = substγ-height _ _ ■ cong suc (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) d₁) (substγ-height _ (⊢-↓ (fvClose*2-⊆ (S.⊆-trans (S.q⊆p∪q _ _) fv⊆)) d₂) ■ ⊢-↓-height (fvClose*2-⊆ (S.⊆-trans (S.q⊆p∪q _ _) fv⊆)) d₂))
⊢-↓-height fv⊆ (T-Inj d) = cong suc (⊢-↓-height fv⊆ d)
⊢-↓-height fv⊆ (T-Case p/s de d₁ d₂) = substγ-height _ _ ■ cong suc (cong₂ Nat._⊔_ (cong₂ Nat._⊔_ (⊢-↓-height (S.⊆-trans (S.p⊆p∪q _) fv⊆) de) (substγ-height _ (⊢-↓ (fvClose-⊆ (S.⊆-trans (S.p⊆p∪q _) (S.⊆-trans (S.q⊆p∪q _ _) fv⊆))) d₁) ■ ⊢-↓-height (fvClose-⊆ (S.⊆-trans (S.p⊆p∪q _) (S.⊆-trans (S.q⊆p∪q _ _) fv⊆))) d₁)) (substγ-height _ (⊢-↓ (fvClose-⊆ (S.⊆-trans (S.q⊆p∪q _ _) (S.⊆-trans (S.q⊆p∪q _ _) fv⊆))) d₂) ■ ⊢-↓-height (fvClose-⊆ (S.⊆-trans (S.q⊆p∪q _ _) (S.⊆-trans (S.q⊆p∪q _ _) fv⊆))) d₂))
⊢-↓-height fv⊆ (T-Conv T≃ ϵ≤ d) = cong suc (⊢-↓-height fv⊆ d)
⊢-↓-height fv⊆ (T-Weaken γ≤ d) = cong suc (⊢-↓-height fv⊆ d)

CGoal : ∀ {n} → Ctx n → Struct n → ℕ → Tm n → 𝕋 → Eff → Set
CGoal Γ γ m e T ϵ =
  ∃[ σ ] ∃[ Δ ] ∃[ ϵ′ ] ∃[ nn ]
     ϵ′ ≤ϵ ϵ × Solving σ × SolvedΔ Δ σ × Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / nn

reType′ : Un.Π[ SolvedTy ∘ Γ ] → SolvedTm e → Γ ; γ ⊢ e ∶ T ∣ ϵ →
          Γ ; γ ⊢ e ∶ subTy T UV.someSub ∣ ϵ
reType′ SΓ Se d =
  subst (λ e′ → _ ; _ ⊢ e′ ∶ _ ∣ _) (subTm-id Se)
    (⊢-sub UV.someSub d ⊢≗ λ x → subTy-id (SΓ x))

substTm-height : ∀ {n} {Γ : Ctx n} {γ e e′ T ϵ} (eq : e ≡ e′) (x : Γ ; γ ⊢ e ∶ T ∣ ϵ) →
                 height (subst (λ z → Γ ; γ ⊢ z ∶ T ∣ ϵ) eq x) ≡ height x
substTm-height refl x = refl

substTy-height : ∀ {n} {Γ : Ctx n} {γ e T T′ ϵ} (eq : T ≡ T′) (x : Γ ; γ ⊢ e ∶ T ∣ ϵ) →
                 height (subst (λ z → Γ ; γ ⊢ e ∶ z ∣ ϵ) eq x) ≡ height x
substTy-height refl x = refl

⊢≗-height : ∀ {n} {Γ₁ Γ₂ : Ctx n} {γ e T ϵ} (d : Γ₁ ; γ ⊢ e ∶ T ∣ ϵ) (eq : Γ₁ ≗ Γ₂) →
            height (d ⊢≗ eq) ≡ height d
⊢≗-height (T-Const _) eq = refl
⊢≗-height (T-Var _ _) eq = refl
⊢≗-height (T-Abs _ _ d) eq = cong suc (⊢≗-height d _)
⊢≗-height (T-AbsRec _ _ d) eq = cong suc (⊢≗-height d _)
⊢≗-height (T-AppUnr _ _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-AppLin _ _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-AppLeft _ _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-AppRight _ _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-Pair _ _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-Let _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ _))
⊢≗-height (T-Seq _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ eq))
⊢≗-height (T-LetPair _ d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (⊢≗-height d₁ eq) (⊢≗-height d₂ _))
⊢≗-height (T-Inj d) eq = cong suc (⊢≗-height d eq)
⊢≗-height (T-Case _ d d₁ d₂) eq = cong suc (cong₂ Nat._⊔_ (cong₂ Nat._⊔_ (⊢≗-height d eq) (⊢≗-height d₁ _)) (⊢≗-height d₂ _))
⊢≗-height (T-Conv _ _ d) eq = cong suc (⊢≗-height d eq)
⊢≗-height (T-Weaken _ d) eq = cong suc (⊢≗-height d eq)

⊢-sub-height : ∀ {n} {Γ : Ctx n} {γ e T ϵ} (σ : UV.Sub) (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) →
               height (⊢-sub σ d) ≡ height d
⊢-sub-height σ (T-Const _) = refl
⊢-sub-height σ (T-Var _ refl) = refl
⊢-sub-height σ (T-Abs _ _ d) = cong suc (⊢≗-height (⊢-sub σ d) _ ■ ⊢-sub-height σ d)
⊢-sub-height σ (T-AbsRec _ _ d) = cong suc (⊢≗-height (⊢-sub σ d) _ ■ ⊢-sub-height σ d)
⊢-sub-height σ (T-AppUnr _ _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-AppLin _ _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-AppLeft _ _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-AppRight _ _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-Pair _ _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-Let _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢≗-height (⊢-sub σ d₂) _ ■ ⊢-sub-height σ d₂))
⊢-sub-height σ (T-Seq _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢-sub-height σ d₂))
⊢-sub-height σ (T-LetPair _ d₁ d₂) = cong suc (cong₂ Nat._⊔_ (⊢-sub-height σ d₁) (⊢≗-height (⊢-sub σ d₂) _ ■ ⊢-sub-height σ d₂))
⊢-sub-height σ (T-Inj d) = cong suc (substTy-height _ _ ■ ⊢-sub-height σ d)
⊢-sub-height σ (T-Case _ d d₁ d₂) = cong suc (cong₂ Nat._⊔_ (cong₂ Nat._⊔_ (⊢-sub-height σ d) (⊢≗-height (⊢-sub σ d₁) _ ■ ⊢-sub-height σ d₁)) (⊢≗-height (⊢-sub σ d₂) _ ■ ⊢-sub-height σ d₂))
⊢-sub-height σ (T-Conv _ _ d) = cong suc (⊢-sub-height σ d)
⊢-sub-height σ (T-Weaken _ d) = cong suc (⊢-sub-height σ d)

reType-height : (SΓ : Un.Π[ SolvedTy ∘ Γ ]) (Se : SolvedTm e) (ST : SolvedTy T)
                (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) → height (reType SΓ Se ST d) ≡ height d
reType-height SΓ Se ST d =
  substTm-height (subTm-id Se) _ ■ substTy-height (subTy-id ST) _ ■ ⊢≗-height (⊢-sub UV.someSub d) (λ x → subTy-id (SΓ x)) ■ ⊢-sub-height UV.someSub d

reType′-height : (SΓ : Un.Π[ SolvedTy ∘ Γ ]) (Se : SolvedTm e) (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) →
                 height (reType′ SΓ Se d) ≡ height d
reType′-height SΓ Se d =
  substTm-height (subTm-id Se) _ ■ ⊢≗-height (⊢-sub UV.someSub d) (λ x → subTy-id (SΓ x)) ■ ⊢-sub-height UV.someSub d

postulate
  refine-fv : ∀ {γ′ : Struct n} (γ : Struct n) (d : Γ ; γ′ ⊢ e ∶ T ∣ ϵ) →
              Σ[ d′ ∈ Γ ; γ ∣fv[ e ] ⊢ e ∶ T ∣ ϵ ] height d′ Nat.≤ height d
  algo-weaken : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ e T ϵ Δ m nn} → Γ ∶ γ₁ ≼ γ₂ →
    Γ ; γ₁ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / nn → Γ ; γ₂ / m ⊢ e ⇐ T ∣ ϵ ↑ Δ / nn

⊔ϵ-lub : ∀ {ϵ₁ ϵ₂ ϵ} → ϵ₁ ≤ϵ ϵ → ϵ₂ ≤ϵ ϵ → (ϵ₁ ⊔ϵ ϵ₂) ≤ϵ ϵ
⊔ϵ-lub ℙ≤ϵ q = q
⊔ϵ-lub 𝕀≤𝕀 q = 𝕀≤𝕀

ϵ≤ℙ⇒≡ℙ : ∀ {ϵ} → ϵ ≤ϵ ℙ → ϵ ≡ ℙ
ϵ≤ℙ⇒≡ℙ ℙ≤ϵ = refl

pairEff : ∀ {p/s ϵ₁ ϵ₂ ϵ₁′ ϵ₂′} → Seq⇒Pure p/s ϵ₁ ϵ₂ → ϵ₁′ ≤ϵ ϵ₁ → ϵ₂′ ≤ϵ ϵ₂ →
          (ϵ₁′ ⊔ϵ ϵ₂′) ≤ϵ ϵ₁ × (p/s ≡ seq → ϵ₂′ ≡ ℙ)
pairEff par p q = ⊔ϵ-lub p q , λ ()
pairEff seq p q = ⊔ϵ-lub p (≤ϵ-trans q ℙ≤ϵ) , λ _ → ϵ≤ℙ⇒≡ℙ q

postulate
  -- CORE (sound): restricting a join-combined context to a well-typed subterm's
  -- free variables yields a subcontext of that subterm's own context.  Both
  -- orientations of the same fact.  This is the single ordered-context-split
  -- debt (sibling of parOrSeq?); the five per-rule split witnesses below are
  -- *derived* from it.
  ↓fv-≼  : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e T ϵ} (a : Dir) →
           Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → Γ ∶ (join a γ₁ γ₂) ↓ fv e ≼ γ₁
  ≤γ-letpair : ∀ {n} {Γ : Ctx n} {γ e₁ e₂} → Γ ∶ (γ ∣fv[ e₁ ]) ; (γ ↓ fvClose* 2 (fv e₂)) ≼ γ
  ≤γ-case : ∀ {n} {Γ : Ctx n} {γ e} (p/s : ParSeq) → JoinParSeq Γ γ (fv e) p/s
  refine-lp₂ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {γ₂d : Struct n} {e₂ : Tm (2 + n)} {T₁ T₂ U ϵ} {ps : ParSeq} {dr : Dir}
    (d₂ : (T₁ ⸴ T₂ ⸴ Γ) ; join ps (join dr (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ₂d)) ⊢ e₂ ∶ U ∣ ϵ) →
    Σ[ d′ ∈ (subTy T₁ UV.someSub ⸴ subTy T₂ UV.someSub ⸴ Γ) ; (join dr (` zero) (` suc zero) ; 𝐂.wk (𝐂.wk (γ ↓ fvClose* 2 (fv e₂)))) ⊢ e₂ ∶ U ∣ ϵ ]
        height d′ Nat.≤ height d₂
  refine-cb : ∀ {n} {Γ : Ctx n} {γ : Struct n} {γ₂d : Struct n} {e : Tm n} {eb : Tm (suc n)} {T U ϵ} {ps : ParSeq}
    (db : (T ⸴ Γ) ; join ps (` zero) (𝐂.wk γ₂d) ⊢ eb ∶ U ∣ ϵ) →
    Σ[ d′ ∈ (subTy T UV.someSub ⸴ Γ) ; join ps (` zero) (𝐂.wk (γ ↓ ∁ (fv e))) ⊢ eb ∶ U ∣ ϵ ] height d′ Nat.≤ height db

app-dir≡ : ∀ {n} {Γ : Ctx n} {γ e₁ e₂ T ϵ Δ m nn} {d₁ d₂ : Dir} → d₁ ≡ d₂ →
  Γ ; γ / m ⊢ e₁ ·⟨ d₁ ⟩ e₂ ⇒ T ∣ ϵ ↑ Δ / nn → Γ ; γ / m ⊢ e₁ ·⟨ d₂ ⟩ e₂ ⇒ T ∣ ϵ ↑ Δ / nn
app-dir≡ refl x = x

¬SolvedTm-select : ∀ {n k} → ¬ SolvedTm (K {n} (`select k))
¬SolvedTm-select (K ())

¬SolvedTm-branch : ∀ {n} → ¬ SolvedTm (K {n} `branch)
¬SolvedTm-branch (K ())

-- The right-orientation of the core split fact, derived from ↓fv-≼ by join-flip.
↓fv-≼ʳ : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e T ϵ} (a : Dir) →
         Γ ; γ₂ ⊢ e ∶ T ∣ ϵ → Γ ∶ (join a γ₁ γ₂) ↓ fv e ≼ γ₂
↓fv-≼ʳ {γ₁ = γ₁} {γ₂} a d = ≼-trans (≼-refl (↓-mono-≈ (≈-sym (join-flip a)))) (↓fv-≼ {γ₁ = γ₂} {γ₂ = γ₁} (flipDir a) d)

-- ≤γ for A-App: all four T-App shapes satisfy γ ≈ join (dir a) γ₂ γ₁, so this
-- reduces to the core split fact applied on each side.
≤γ-app : ∀ {n} {Γ : Ctx n} {γ γ₁ γ₂ : Struct n} {e₁ e₂ : Tm n} {S₁ S₂ ϵ₁ ϵ₂} (a : Dir) →
         Γ ; γ₁ ⊢ e₁ ∶ S₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ S₂ ∣ ϵ₂ →
         Γ ∶ γ ≈ join a γ₂ γ₁ →
         Γ ∶ join a (γ ∣fv[ e₂ ]) (γ ∣fv[ e₁ ]) ≼ γ
≤γ-app a d₁ d₂ γ≈ =
  ≼-trans (≼-join a (≼-trans (≼-refl (↓-mono-≈ γ≈)) (↓fv-≼ a d₂))
                    (≼-trans (≼-refl (↓-mono-≈ γ≈)) (↓fv-≼ʳ a d₁)))
          (≼-refl (≈-sym γ≈))

-- ≤γ for A-Pair, derived from the core split fact.
≤γ-par : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e₁ e₂ T₁ T₂ ϵ₁ ϵ₂} (p/s : ParSeq) →
  Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂ →
  Γ ∶ join (biasedDir p/s) ((join (biasedDir p/s) γ₁ γ₂) ↓ fv e₁) ((join (biasedDir p/s) γ₁ γ₂) ↓ fv e₂)
    ≼ join (biasedDir p/s) γ₁ γ₂
≤γ-par {γ₁ = γ₁} {γ₂ = γ₂} p/s d₁ d₂ = ≼-join (biasedDir p/s) (↓fv-≼ {γ₂ = γ₂} (biasedDir p/s) d₁) (↓fv-≼ʳ {γ₁ = γ₁} (biasedDir p/s) d₂)

-- ≤γ for A-Seq (the ambient γ₁ ; γ₂ is join L γ₁ γ₂).
≤γ-seq : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {e₁ e₂ T₁ T₂ ϵ₁ ϵ₂} →
  Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁ → Γ ; γ₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂ →
  Γ ∶ ((γ₁ ; γ₂) ↓ fv e₁) ; ((γ₁ ; γ₂) ↓ fv e₂) ≼ γ₁ ; γ₂
≤γ-seq {γ₁ = γ₁} {γ₂ = γ₂} d₁ d₂ = ≼-join L (↓fv-≼ {γ₂ = γ₂} L d₁) (↓fv-≼ʳ {γ₁ = γ₁} L d₂)

lsplit-case : ∀ {n} {Γ : Ctx n} {γ s T m} → Γ ∶ [] ≼ γ →
  ⊢ (`lsplit s) ∶ T → SolvedTy T → CGoal Γ γ m (K (`lsplit s)) T ℙ
lsplit-case ≤γ (`lsplit s s′ ¬s′) (⟨ Ss ; Ss′ ⟩ ⟨ a ⟩→ Scod) =
  let leaf = ≃-reflexive (subTy-id Ss′ ■ sym (𝐓.⋯-id s′ λ())) in
  UV.subAll ¬s′ , _ , _ , _ , ≤ϵ-refl , subAll-solving ¬s′ Ss′ ,
    (⟨ ≃-; ≃-refl leaf ⟩ `→ (≃-refl ⊗ ⟨ leaf ⟩)) ∷ [] , A-Check (A-LSplit ≤γ)

rsplit-case : ∀ {n} {Γ : Ctx n} {γ s T m} → Γ ∶ [] ≼ γ →
  ⊢ (`rsplit s) ∶ T → SolvedTy T → CGoal Γ γ m (K (`rsplit s)) T ℙ
rsplit-case ≤γ (`rsplit s s′ ¬s′) (⟨ Ss ; Ss′ ⟩ ⟨ a ⟩→ Scod) =
  let leaf = ≃-reflexive (subTy-id Ss′ ■ sym (𝐓.⋯-id s′ λ())) in
  UV.subAll ¬s′ , _ , _ , _ , ≤ϵ-refl , subAll-solving ¬s′ Ss′ ,
    (⟨ ≃-; ≃-refl leaf ⟩ `→ (≃-refl ⊗ ⟨ ≃-; ≃-refl leaf ⟩)) ∷ [] , A-Check (A-RSplit ≤γ)

complete-fuel : (k : ℕ) (d : Γ ; γ ⊢ e ∶ T ∣ ϵ) → height d Nat.< k →
  Un.Π[ SolvedTy ∘ Γ ] → SolvedTm e → SolvedTy T → CGoal Γ γ m e T ϵ
complete-fuel zero d h< SΓ Se ST = ⊥-elim (Nat.n≮0 h<)
complete-fuel (suc k) (T-Const {c = c} ⊢c) h< SΓ Se ST with algConst? c
... | inj₁ Ac = UV.someSub , _ , _ , _ , ≤ϵ-refl , someSub-solving , ≃-refl ∷ [] , A-Check (A-Const (≼-∅ []) Ac ⊢c)
... | inj₂ `lsplit = lsplit-case (≼-∅ []) ⊢c ST
... | inj₂ `rsplit = rsplit-case (≼-∅ []) ⊢c ST
... | inj₂ `select = ⊥-elim (¬SolvedTm-select Se)
... | inj₂ `branch = ⊥-elim (¬SolvedTm-branch Se)
complete-fuel (suc k) (T-Var x refl) h< SΓ Se ST =
  UV.someSub , _ , _ , _ , ≤ϵ-refl , someSub-solving , ≃-refl ∷ [] , A-Check (A-Var (≼-refl refl))
complete-fuel (suc k) (T-Abs Γ-unr Γ-mob d) h< SΓ (ƛ Se) (ST-T ⟨ a ⟩→ ST-U) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k d (Nat.s≤s⁻¹ h<) (⸴Π ST-T SΓ) Se ST-U in
  σ , _ , _ , n , ≤ϵ-refl , Sσ , All.++⁺ (mobΔ {a = a} {σ = σ} Γ-mob) SΔ , A-Abs Γ-unr ϵ′≤ A refl
complete-fuel (suc k) (T-AbsRec Γ-unr a-unr d) h< SΓ (μ (ƛ Se)) (ST-T ⟨ a ⟩→ ST-U) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k d (Nat.s≤s⁻¹ h<) (⸴Π ST-T (⸴Π (ST-T ⟨ a ⟩→ ST-U) SΓ)) Se ST-U in
  σ , Δ , _ , n , ≤ϵ-refl , Sσ , SΔ , A-AbsRec Γ-unr a-unr ϵ′≤ A
complete-fuel {γ = γ} {e = e₁ ·¹ e₂} (suc k) (T-AppUnr {a = a} {T = T} {U = U} a-unr ≤ₐ d₁ d₂) h< SΓ (Se₁ · Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-fv γ (reType′ SΓ Se₂ d₂)
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₂≤ (Nat.≤-reflexive (reType′-height SΓ Se₂ d₂))) (Nat.m≤n⊔m _ _)) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved (T ⟨ a ⟩→ U) someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ SΓ Se₂ (subTy-solved T someSub-solving)
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      ec = subst (λ dd → EffCompat dd ϵ₂′ ϵ₁′) (sym (Arr.ω⇒𝟙 a a-unr)) tt
      app = app-dir≡ (Arr.ω⇒𝟙 a a-unr) (A-App ec (≤γ-app (Arr.dir a) d₁ d₂ (subst (λ dr → _ ∶ γ ≈ join dr _ _) (sym (Arr.ω⇒𝟙 a a-unr)) ∥-comm)) (A-Ann A₁) A₂)
      cp = subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id (subTy-solved U someSub-solving))) (≃-reflexive (sym (subTy-id ST)))
  in σ , _ , _ , n , ⊔ϵ-lub (⊔ϵ-lub ϵ₁′≤ ϵ₂′≤) ≤ₐ , Sσ , cp ∷ SΔ , A-Check app
complete-fuel {γ = γ} {e = e₁ ·¹ e₂} (suc k) (T-AppLin {a = a} {T = T} {U = U} a-par ≤ₐ d₁ d₂) h< SΓ (Se₁ · Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-fv γ (reType′ SΓ Se₂ d₂)
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₂≤ (Nat.≤-reflexive (reType′-height SΓ Se₂ d₂))) (Nat.m≤n⊔m _ _)) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved (T ⟨ a ⟩→ U) someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ SΓ Se₂ (subTy-solved T someSub-solving)
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      ec = subst (λ dd → EffCompat dd ϵ₂′ ϵ₁′) (sym (proj₂ a-par)) tt
      app = app-dir≡ (proj₂ a-par) (A-App ec (≤γ-app (Arr.dir a) d₁ d₂ (subst (λ dr → _ ∶ γ ≈ join dr _ _) (sym (proj₂ a-par)) ∥-comm)) (A-Ann A₁) A₂)
      cp = subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id (subTy-solved U someSub-solving))) (≃-reflexive (sym (subTy-id ST)))
  in σ , _ , _ , n , ⊔ϵ-lub (⊔ϵ-lub ϵ₁′≤ ϵ₂′≤) ≤ₐ , Sσ , cp ∷ SΔ , A-Check app
complete-fuel {γ = γ} {e = e₁ ·ᴸ e₂} (suc k) (T-AppLeft {a = a} {T = T} {U = U} aL ≤ₐ d₁ d₂) h< SΓ (Se₁ · Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-fv γ (reType′ SΓ Se₂ d₂)
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₂≤ (Nat.≤-reflexive (reType′-height SΓ Se₂ d₂))) (Nat.m≤n⊔m _ _)) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved (T ⟨ a ⟩→ U) someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ SΓ Se₂ (subTy-solved T someSub-solving)
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      ec = subst (λ dd → EffCompat dd ϵ₂′ ϵ₁′) (sym aL) (ϵ≤ℙ⇒≡ℙ ϵ₁′≤)
      app = app-dir≡ aL (A-App ec (≤γ-app (Arr.dir a) d₁ d₂ (subst (λ dr → _ ∶ γ ≈ join dr _ _) (sym (aL)) ≈-refl)) (A-Ann A₁) A₂)
      cp = subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id (subTy-solved U someSub-solving))) (≃-reflexive (sym (subTy-id ST)))
  in σ , _ , _ , n , ⊔ϵ-lub (⊔ϵ-lub (≤ϵ-trans ϵ₁′≤ ℙ≤ϵ) ϵ₂′≤) ≤ₐ , Sσ , cp ∷ SΔ , A-Check app
complete-fuel {γ = γ} {e = e₁ ·ᴿ e₂} (suc k) (T-AppRight {a = a} {T = T} {U = U} aR ≤ₐ d₁ d₂) h< SΓ (Se₁ · Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-fv γ (reType′ SΓ Se₂ d₂)
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₂≤ (Nat.≤-reflexive (reType′-height SΓ Se₂ d₂))) (Nat.m≤n⊔m _ _)) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved (T ⟨ a ⟩→ U) someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ SΓ Se₂ (subTy-solved T someSub-solving)
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      ec = subst (λ dd → EffCompat dd ϵ₂′ ϵ₁′) (sym aR) (ϵ≤ℙ⇒≡ℙ ϵ₂′≤)
      app = app-dir≡ aR (A-App ec (≤γ-app (Arr.dir a) d₁ d₂ (subst (λ dr → _ ∶ γ ≈ join dr _ _) (sym (aR)) ≈-refl)) (A-Ann A₁) A₂)
      cp = subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id (subTy-solved U someSub-solving))) (≃-reflexive (sym (subTy-id ST)))
  in σ , _ , _ , n , ⊔ϵ-lub (⊔ϵ-lub ϵ₁′≤ (≤ϵ-trans ϵ₂′≤ ℙ≤ϵ)) ≤ₐ , Sσ , cp ∷ SΔ , A-Check app
complete-fuel {γ = γ} {e = e₁ ⊗ e₂} (suc k) (T-Pair p/s seq⇒p d₁ d₂) h< SΓ (Se₁ ⊗ Se₂) (ST-T ⊗⟨ d ⟩ ST-U) =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ d₁
      ref₂ , h₂≤ = refine-fv γ d₂
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ =
        complete-fuel k ref₁ (Nat.≤-<-trans (Nat.≤-trans h₁≤ (Nat.m≤m⊔n _ _)) hlt) SΓ Se₁ ST-T
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ =
        complete-fuel {m = m′} k ref₂ (Nat.≤-<-trans (Nat.≤-trans h₂≤ (Nat.m≤n⊔m _ _)) hlt) SΓ Se₂ ST-U
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      effB , s⇒p = pairEff seq⇒p ϵ₁′≤ ϵ₂′≤
  in σ , Δ₁ ++ Δ₂ , _ , n , effB , Sσ , SΔ , A-Pair p/s (≤γ-par p/s d₁ d₂) s⇒p A₁ A₂
complete-fuel (suc k) (T-Let p/s x y) h< SΓ () ST
complete-fuel {γ = γ} {e = e₁ ; e₂} (suc k) (T-Seq {T = T} unr-T d₁ d₂) h< SΓ (Se₁ ; Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-fv γ d₂
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans h₂≤ (Nat.m≤n⊔m _ _)) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved T someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ SΓ Se₂ ST
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
  in σ , _ , _ , n , ⊔ϵ-lub ϵ₁′≤ ϵ₂′≤ , Sσ , ≃-refl ∷ SΔ ,
     A-Check (A-Seq (subTy-unr unr-T) (≤γ-seq d₁ d₂) (A-Ann A₁) (A-Ann A₂))
complete-fuel {γ = γ} {e = `let⊗ e₁ `in e₂} (suc k) (T-LetPair {T₁ = T₁} {d = d} {T₂ = T₂} p/s {γ₂ = γ₂} d₁ d₂) h< SΓ (`let⊗ Se₁ `in Se₂) ST =
  let hlt = Nat.s≤s⁻¹ h<
      ref₁ , h₁≤ = refine-fv γ (reType′ SΓ Se₁ d₁)
      ref₂ , h₂≤ = refine-lp₂ {γ = γ} {γ₂d = γ₂} {ps = p/s} {dr = d} d₂
      b₁ = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans h₁≤ (Nat.≤-reflexive (reType′-height SΓ Se₁ d₁))) (Nat.m≤m⊔n _ _)) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans h₂≤ (Nat.m≤n⊔m (height d₁) (height d₂))) hlt
      σ₁ , Δ₁ , ϵ₁′ , m′ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel k ref₁ b₁ SΓ Se₁ (subTy-solved (T₁ ⊗⟨ d ⟩ T₂) someSub-solving)
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m′} k ref₂ b₂ (⸴Π (subTy-solved T₁ someSub-solving) (⸴Π (subTy-solved T₂ someSub-solving) SΓ)) Se₂ ST
      σ , Sσ , SΔ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
  in σ , _ , _ , n , ⊔ϵ-lub ϵ₁′≤ ϵ₂′≤ , Sσ , ≃-refl ∷ SΔ ,
     A-Check (A-LetPair (≤γ-letpair {γ = γ} {e₁ = e₁} {e₂ = e₂}) (A-Ann A₁) (A-Ann A₂))
complete-fuel (suc k) (T-Inj {i = true} x) h< SΓ (`inj Se) (ST₁ ⊕ ST₂) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k x (Nat.s≤s⁻¹ h<) SΓ Se ST₁ in
  σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A-Inj A
complete-fuel (suc k) (T-Inj {i = false} x) h< SΓ (`inj Se) (ST₁ ⊕ ST₂) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k x (Nat.s≤s⁻¹ h<) SΓ Se ST₂ in
  σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A-Inj A
complete-fuel {γ = γ} {e = `case e `of⟨ e₁ ; e₂ ⟩} (suc k) (T-Case {T₁ = T₁} {T₂ = T₂} p/s {γ₂ = γ₂} de d₁ d₂) h< SΓ (`case Se `of⟨ Se₁ ; Se₂ ⟩) ST =
  let hlt = Nat.s≤s⁻¹ h<
      refe , he≤ = refine-fv γ (reType′ SΓ Se de)
      ref₁ , h₁≤ = refine-cb {γ = γ} {γ₂d = γ₂} {e = e} {ps = p/s} d₁
      ref₂ , h₂≤ = refine-cb {γ = γ} {γ₂d = γ₂} {e = e} {ps = p/s} d₂
      be = Nat.≤-<-trans (Nat.≤-trans (Nat.≤-trans he≤ (Nat.≤-reflexive (reType′-height SΓ Se de))) (Nat.≤-trans (Nat.m≤m⊔n (height de) (height d₁)) (Nat.m≤m⊔n (height de Nat.⊔ height d₁) (height d₂)))) hlt
      b₁ = Nat.≤-<-trans (Nat.≤-trans h₁≤ (Nat.≤-trans (Nat.m≤n⊔m (height de) (height d₁)) (Nat.m≤m⊔n (height de Nat.⊔ height d₁) (height d₂)))) hlt
      b₂ = Nat.≤-<-trans (Nat.≤-trans h₂≤ (Nat.m≤n⊔m (height de Nat.⊔ height d₁) (height d₂))) hlt
      σe , Δe , ϵe′ , m₁ , ϵe′≤ , Sσe , SΔe , Ae = complete-fuel k refe be SΓ Se (subTy-solved (T₁ ⊕ T₂) someSub-solving)
      σ₁ , Δ₁ , ϵ₁′ , m₂ , ϵ₁′≤ , Sσ₁ , SΔ₁ , A₁ = complete-fuel {m = m₁} k ref₁ b₁ (⸴Π (subTy-solved T₁ someSub-solving) SΓ) Se₁ ST
      σ₂ , Δ₂ , ϵ₂′ , n , ϵ₂′≤ , Sσ₂ , SΔ₂ , A₂ = complete-fuel {m = m₂} k ref₂ b₂ (⸴Π (subTy-solved T₂ someSub-solving) SΓ) Se₂ ST
      σ′ , Sσ′ , SΔ′ = merge₂ Sσ₁ Sσ₂ SΔ₁ SΔ₂
      σ , Sσ , SΔ = merge₂ Sσe Sσ′ SΔe SΔ′
  in σ , _ , _ , n , ⊔ϵ-lub (⊔ϵ-lub ϵe′≤ ϵ₁′≤) ϵ₂′≤ , Sσ , ≃-refl ∷ ≃-refl ∷ SΔ ,
     A-Check (A-Case p/s (≤γ-case {e = e} p/s) (A-Ann Ae) (A-Ann A₁) (A-Ann A₂))
complete-fuel (suc k) (T-Conv {T = T} {U = U} T≃ ϵ≤ x) h< SΓ Se ST =
  let ST-T = ≃-solved⁻¹ T≃ ST in
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k x (Nat.s≤s⁻¹ h<) SΓ Se ST-T in
  σ , C-Eq U T ∷ Δ , ϵ′ , n , ≤ϵ-trans ϵ′≤ ϵ≤ , Sσ ,
    subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id ST-T)) (≃-sym T≃) ∷ SΔ , A-Check (A-Ann A)
complete-fuel (suc k) (T-Weaken γ≤ x) h< SΓ Se ST =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete-fuel k x (Nat.s≤s⁻¹ h<) SΓ Se ST in
  σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , algo-weaken γ≤ A

complete :
  Un.Π[ SolvedTy ∘ Γ ] →
  SolvedTm e →
  SolvedTy T →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∃[ σ ] ∃[ Δ ] ∃[ ϵ′ ] ∃[ n ]
     ϵ′ ≤ϵ ϵ × Solving σ × SolvedΔ Δ σ × Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / n
complete SΓ Se ST d = complete-fuel (suc (height d)) d Nat.≤-refl SΓ Se ST
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
