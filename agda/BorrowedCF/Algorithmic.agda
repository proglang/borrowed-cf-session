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
fv (e₁ ·⟨ _ ⟩ e₂) = fv e₁ ∪ fv e₂
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

_∣fv[_] : Struct n → Tm n → Struct n
γ ∣fv[ e ] = γ ↓ fv e

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
    ¬ Skips s →
    -----------------------------------------------------------------------------------
    Γ ; γ / m ⊢ K (`lsplit s) ⇒ ⟨ s ; `` α ⟩ →*M ⟨ s ⟩ ⊗ᴸ ⟨ `` α ⟩ ∣ ℙ ∣ ℙ ↑ [] / suc m

  A-RSplit :
    let α = record { var = m; pol = ‼ } in
    (≤γ : Γ ∶ [] ≼ γ) →
    ¬ Skips s →
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
  sound (A-LSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Const (`lsplit _ _))
  sound (A-RSplit ≤γ ¬skips) SΓ SΔ =
    T-Weaken (≼-map⁺ subTy-unr subTy-mobile ≤γ)
             (T-Const (`rsplit _ _))
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

complete :
  Un.Π[ SolvedTy ∘ Γ ] →
  SolvedTm e →
  SolvedTy T →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∃[ σ ] ∃[ Δ ] ∃[ ϵ′ ] ∃[ n ]
     ϵ′ ≤ϵ ϵ × Solving σ × SolvedΔ Δ σ × Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / n
complete SΓ Se ST (T-Const {c = c} ⊢c) with algConst? c
... | inj₁ Ac =
  UV.someSub , _ , _ , _ , ≤ϵ-refl , someSub-solving , ≃-refl ∷ [] , A-Check (A-Const (≼-∅ []) Ac ⊢c)
... | inj₂ ¬Ac = {!¬Ac!}
complete SΓ Se ST (T-Var x refl) =
  UV.someSub , _ , _ , _ , ≤ϵ-refl , someSub-solving , ≃-refl ∷ [] , A-Check (A-Var (≼-refl refl))
complete SΓ Se ST (T-Abs Γ-unr Γ-mob x) = {!!}
complete SΓ Se ST (T-AbsRec Γ-unr a-unr x) = {!!}
complete SΓ Se ST (T-AppUnr a-unr ≤ₐ x y) = {!!}
complete SΓ Se ST (T-AppLin a-par ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-AppLeft aL ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-AppRight aR ≤ₐ x x₁) = {!!}
complete SΓ Se ST (T-Pair p/s seq⇒p x x₁) = {!!}
complete SΓ Se ST (T-Seq unr-T x y) = {!!}
complete SΓ Se ST (T-LetPair p/s x y) = {!!}
complete SΓ (`inj Se) (ST₁ ⊕ ST₂) (T-Inj {i = true} x) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete SΓ Se ST₁ x in
  σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A-Inj A
complete SΓ (`inj Se) (ST₁ ⊕ ST₂) (T-Inj {i = false} x) =
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete SΓ Se ST₂ x in
  σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A-Inj A
complete SΓ Se ST (T-Case p/s x y₁ y₂) = {!!}
complete SΓ Se ST (T-Conv {T = T} {U = U} T≃ ϵ≤ x) =
  let ST-T = ≃-solved⁻¹ T≃ ST in
  let σ , Δ , ϵ′ , n , ϵ′≤ , Sσ , SΔ , A = complete SΓ Se ST-T x in
  σ , C-Eq U T ∷ Δ , ϵ′ , n , ≤ϵ-trans ϵ′≤ ϵ≤ , Sσ ,
    subst₂ _≃_ (sym (subTy-id ST)) (sym (subTy-id ST-T)) (≃-sym T≃) ∷ SΔ ,
    A-Check (A-Ann A)
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
