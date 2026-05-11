{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction where

open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅◅_) renaming (ε to refl)
open import Data.Nat.ListAction using (sum)

import Data.Vec.Functional as F

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes
open import BorrowedCF.Types
open import BorrowedCF.Context

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

private variable
  e e₁ e₂ e₃ e′ : Tm n
  t t₁ t₂ t₃ t′ : 𝕋

-- NB. Values are predicates on _unclosed_ terms. That is because
-- channel variables are values but we don't want to keep two kinds of
-- environments around. The notion of a "Value" is only correct in a
-- context Γ where `ChanCx Γ` holds.

ChanCx : Ctx n → Set
ChanCx Γ = ∀ x → ∃ λ s → Γ x ≡ ⟨ s ⟩

data Value {n} : Tm n → Set where
  V-` : ∀ {x} → Value (` x)
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (ƛ e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ⊗ e₂)

vTm : {e : Tm n} → Value e → Tm n
vTm {e = e} _ = e

data Frame n : Set where
  □·_ : (e₂ : Tm n) → Frame n
  _·□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □⊗_ : (e₂ : Tm n) → Frame n
  _⊗□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □;_ : (e₂ : Tm n) → Frame n
  `let-`in_ : (e′ : Tm (1 + n)) → Frame n
  `let⊗-`in_ : (e′ : Tm (2 + n)) → Frame n

infixl 4.5 _[_]

_[_] : Frame n → Tm n → Tm n
(□· e) [ e₀ ] = e₀ · e
(V ·□) [ e₀ ] = vTm V · e₀
(□⊗ e) [ e₀ ] = e₀ ⊗ e
(V ⊗□) [ e₀ ] = vTm V ⊗ e₀
(□; e) [ e₀ ] = e₀ ; e
(`let-`in e) [ e₀ ] = `let e₀ `in e
(`let⊗-`in e) [ e₀ ] = `let⊗ e₀ `in e

VSub : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Set
VSub ϕ = ∀ x → Value (`/id (ϕ x))

value-⋯ : ⦃ K : Kit 𝓕 ⦄ → Value e → (ϕ : m –[ K ]→ n) → VSub ϕ → Value (e ⋯ ϕ)
value-⋯ V-` ϕ Vϕ = Vϕ _
value-⋯ V-K ϕ Vϕ = V-K
value-⋯ V-λ ϕ Vϕ = V-λ
value-⋯ (V-⊗ V₁ V₂) ϕ Vϕ = V-⊗ (value-⋯ V₁ ϕ Vϕ) (value-⋯ V₂ ϕ Vϕ)

frame-⋯ : ⦃ K : Kit 𝓕 ⦄ → Frame m → (ϕ : m –[ K ]→ n) → VSub ϕ → Frame n
frame-⋯ (□· e₂) ϕ Vϕ = □· (e₂ ⋯ ϕ)
frame-⋯ (V₁ ·□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ·□
frame-⋯ (□⊗ e₂) ϕ Vϕ = □⊗ (e₂ ⋯ ϕ)
frame-⋯ (V₁ ⊗□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ·□
frame-⋯ (□; e₂) ϕ Vϕ = □; (e₂ ⋯ ϕ)
frame-⋯ (`let-`in e′) ϕ Vϕ = `let-`in (e′ ⋯ ϕ ↑)
frame-⋯ (`let⊗-`in e′) ϕ Vϕ = `let⊗-`in (e′ ⋯ ϕ ↑ ↑)

infixl 5 _⋯ᵛ_ _⋯ᶠ_

_⋯ᵛ_ : Value e → (ϕ : m →ᵣ n) → Value (e ⋯ ϕ)
V ⋯ᵛ ϕ = value-⋯ V ϕ λ x → V-`

_⋯ᶠ_ : Frame m → (ϕ : m →ᵣ n) → Frame n
E ⋯ᶠ ϕ = frame-⋯ E ϕ λ x → V-`

infix 4 _─→_ _⋯→_

data _─→_ {n} : Tm n → Tm n → Set where
  E-App : (V : Value e₂) → (ƛ e₁) · e₂ ─→ e₁ ⋯ ⦅ e₂ ⦆
  E-Seq : K `unit ; e ─→ e
  E-Let : Value e₁ → `let e₁ `in e₂ ─→ e₂ ⋯ ⦅ e₁ ⦆
  E-PairElim : (V₁ : Value e₁) (V₂ : Value e₂) → `let⊗ (e₁ ⊗ e₂) `in e ─→ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆

data _⋯→_ {n} : Tm n → Tm n → Set where
  E-□   : e₁ ─→ e₂ → e₁ ⋯→ e₂
  E-Ctx : (E : Frame n) → e₁ ⋯→ e₂ → E [ e₁ ] ⋯→ E [ e₂ ]

value⇒pure : Value e → (x : Γ ; γ ⊢ e ∶ T ∣ ϵ) → Γ ; γ ⊢ e ∶ T ∣ ℙ
value⇒pure V (T-Var x T-eq) = T-Var x T-eq
value⇒pure V (T-Const x) = T-Const x
value⇒pure V (T-Abs Γ-unr Γ-mob x) = T-Abs Γ-unr Γ-mob x
value⇒pure (V-⊗ V₁ V₂) (T-Pair p/s x₁ x₂ seq⇒p) = T-Pair p/s (value⇒pure V₁ x₁) (value⇒pure V₂ x₂) seq⇒pure-ℙℙ
value⇒pure V (T-Weaken ϵ≤ γ≤ x) = T-Weaken ≤ϵ-refl γ≤ (value⇒pure V x)

inv-⊢abs : Γ ; γ ⊢ ƛ e ∶ T ⟨ a ⟩→ U ∣ ℙ →
  ∃[ γ′ ] T F.∷ Γ ∶ γ′ ≼ join (Arr.dir a) (` zero) (𝐂.wk γ)
        × T F.∷ Γ ; γ′ ⊢ e ∶ U ∣ Arr.eff a
inv-⊢abs (T-Abs Γ-unr Γ-mob x) = _ , ≼-refl refl , x
inv-⊢abs {a = a} (T-Weaken ℙ≤ϵ γ≤ x) =
  let _ , γ≤₁ , x′ = inv-⊢abs x in
  let γ≤₂ = ≼-join (Arr.dir a) (≼-refl refl) $
              subst₂ (_ ∶_≼_) (𝐂.weaken/wk _) (𝐂.weaken/wk _) (𝐂.≼-⋯ `_ γ≤)
  in
  _ , ≼-trans γ≤₁ γ≤₂ , x′

inv-⊢pair : Γ ; γ ⊢ e₁ ⊗ e₂ ∶ T ⊗⟨ d ⟩ U ∣ ℙ →
  ∃[ γ₁ ] ∃[ γ₂ ] Γ ∶ join d γ₁ γ₂ ≼ γ
     × Γ ; γ₁ ⊢ e₁ ∶ T ∣ ℙ
     × Γ ; γ₂ ⊢ e₂ ∶ U ∣ ℙ
inv-⊢pair (T-Pair p/s x₁ x₂ par⇒seq)
  rewrite seq⇒pure-ℙϵ⁻¹ par⇒seq
  = _ , _ , ≼-refl refl , x₁ , x₂
inv-⊢pair (T-Weaken ℙ≤ϵ γ≤ x) =
  let _ , _ , γ≤′ , x₁ , x₂ = inv-⊢pair x in
  _ , _ , ≼-trans γ≤′ γ≤ , x₁ , x₂

module _ (Γ-S : ChanCx Γ) where
  ⊢`⊤⇒[]≼γ : Value e → Γ ; γ ⊢ e ∶ `⊤ ∣ ϵ → Γ ∶ [] ≼ γ
  ⊢`⊤⇒[]≼γ V (T-Const x)        = ≼-refl refl
  ⊢`⊤⇒[]≼γ V (T-Weaken ϵ≤ γ≤ x) = ≼-trans (⊢`⊤⇒[]≼γ V x) γ≤
  ⊢`⊤⇒[]≼γ V (T-Var x T-eq)     = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-pair : Value e → Γ ; γ ⊢ e ∶ T ⊗⟨ d ⟩ U ∣ ℙ →
    ∃[ α ] ∃[ β ] ∃[ e₁ ] ∃[ e₂ ]
      e ≡ e₁ ⊗ e₂
        × Γ ∶ join d α β ≼ γ
        × Γ ; α ⊢ e₁ ∶ T ∣ ℙ
        × Γ ; β ⊢ e₂ ∶ U ∣ ℙ
  inv-pair V (T-Pair p/s x₁ x₂ seq⇒p)
    rewrite seq⇒pure-ℙϵ⁻¹ seq⇒p
    = _ , _ , _ , _ , refl , ≼-refl refl , x₁ , x₂
  inv-pair V (T-Weaken ℙ≤ϵ γ≤ x)
    = let _ , _ , _ , _ , eq , γ≤′ , x₁,x₂ = inv-pair V x in
      _ , _ , _ , _ , eq , ≼-trans γ≤′ γ≤ , x₁,x₂
  inv-pair V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-session : Value e → Γ ; γ ⊢ e ∶ ⟨ s ⟩ ∣ ϵ →
    ∃[ x ] e ≡ ` x × Γ x ≡ ⟨ s ⟩ × Γ ∶ ` x ≼ γ
  inv-session V (T-Var x T-eq) = x , refl , T-eq , ≼-refl refl
  inv-session V (T-Weaken ϵ≤ γ≤ x) =
    _ , inv-session V x .proj₂ .proj₁
      , inv-session V x .proj₂ .proj₂ .proj₁
      , ≼-trans (inv-session V x .proj₂ .proj₂ .proj₂) γ≤

  Unr×Value⇒UnrCx : Unr T → Value e → Γ ; γ ⊢ e ∶ T ∣ ϵ → UnrCx Γ γ
  Unr×Value⇒UnrCx U V (T-Const c) = []
  Unr×Value⇒UnrCx U V (T-Var x refl) = ` U
  Unr×Value⇒UnrCx (arr U) V (T-Abs Γ-unr Γ-mob e) = Γ-unr U
  Unr×Value⇒UnrCx (U₁ ⊗ U₂) (V-⊗ V₁ V₂) (T-Pair p/s e₁ e₂ seq⇒p) =
    allCx-join⁺ p/s (Unr×Value⇒UnrCx U₁ V₁ e₁) (Unr×Value⇒UnrCx U₂ V₂ e₂)
  Unr×Value⇒UnrCx U V (T-Weaken ϵ≤ γ≤ e) = allCx-≼ id (Unr×Value⇒UnrCx U V e) γ≤

  Mobile×Value⇒MobCx : Mobile T → Value e → Γ ; γ ⊢ e ∶ T ∣ ϵ → MobCx Γ γ
  Mobile×Value⇒MobCx m V (T-Const x) = []
  Mobile×Value⇒MobCx m V (T-Var x refl) = ` m
  Mobile×Value⇒MobCx (arr m) V (T-Abs Γ-unr Γ-mob x) = Γ-mob m
  Mobile×Value⇒MobCx (m₁ ⊗ m₂) (V-⊗ V₁ V₂) (T-Pair p/s e₁ e₂ seq⇒p) =
    allCx-join⁺ p/s (Mobile×Value⇒MobCx m₁ V₁ e₁) (Mobile×Value⇒MobCx m₂ V₂ e₂)
  Mobile×Value⇒MobCx m V (T-Weaken ϵ≤ γ≤ e) = allCx-≼ Unr⇒Mobile (Mobile×Value⇒MobCx m V e) γ≤

  preservation′ : Γ ; γ ⊢ e ∶ t ∣ ϵ → e ─→ e′ → Γ ; γ ⊢ e′ ∶ t ∣ ϵ
  preservation′ (T-App {a = a} {γ₁ = γ₁} {γ₂} refl f e) (E-App V) =
    let open ≼-Reasoning in
    let open Arr a in
    let γ′ , γ≤ , f′ = inv-⊢abs (value⇒pure V-λ f) in
    let γ≤′ = begin
                γ′ 𝐂.⋯ 𝐂.⦅ γ₂ ⦆
              ≲⟨ 𝐂.≼-⋯ (λ{ {zero} U → Unr×Value⇒UnrCx U V e; {suc x} → `_ }) γ≤ ⟩
                join dir (` zero) (𝐂.wk γ₁) 𝐂.⋯ 𝐂.⦅ γ₂ ⦆
              ≡⟨ join-⋯ dir _ _ ⟩
                join dir γ₂ (𝐂.wk γ₁ 𝐂.⋯ 𝐂.⦅ γ₂ ⦆)
              ≡⟨ cong (join dir γ₂) (γ₁ 𝐂.⋯-wk-cancels-⦅ γ₂ ⦆) ⟩
                join dir γ₂ γ₁
              ∎
    in
    T-Weaken ≤ϵ-refl γ≤′ (f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V e) (λ U → Unr×Value⇒UnrCx U V e) (λ m → Mobile×Value⇒MobCx m V e))
  preservation′ (T-Let p/s {γ₁} {γ₂} e₁ e₂) (E-Let V-e₁) =
    let eq = join-⋯ {σ = 𝐂.⦅ γ₁ ⦆} p/s (` zero) (𝐂.wk γ₂)
               ■ cong (join p/s γ₁) (γ₂ 𝐂.⋯-wk-cancels-⦅ γ₁ ⦆)
    in
    subst-γ eq (e₂ ⊢⋯ₛ ⊢subₛ (value⇒pure V-e₁ e₁) (λ U → Unr×Value⇒UnrCx U V-e₁ e₁) (λ m → Mobile×Value⇒MobCx m V-e₁ e₁))
  preservation′ (T-LetUnit p/s e₁ e₂) E-Seq =
    let γ≼ = ≼-trans (≼-refl (≈-sym (join-[]₁ p/s)))
                     (≼-join p/s (⊢`⊤⇒[]≼γ V-K e₁) (≼-refl refl))
    in
    T-Weaken ≤ϵ-refl γ≼ e₂
  preservation′ (T-LetPair {d = d} {T₂ = T₂} p/s {γ₁} {γ₂} e e′) (E-PairElim V₁ V₂) =
    let open Fin.Patterns in
    let open ≼-Reasoning in
    let α , β , γ≤ , e₁ , e₂ = inv-⊢pair (value⇒pure (V-⊗ V₁ V₂) e) in
    let γ≤′ = begin
                join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ₂))
                  𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆ 𝐂.⋯ 𝐂.⦅ β ⦆
              ≡⟨ cong (𝐂._⋯ 𝐂.⦅ β ⦆) (join-⋯ p/s _ _) ⟩
                join p/s (join d (` 0F) (` 1F) 𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆) (𝐂.wk (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ α 𝐂.⋯ 𝐂.weaken ⦆) 𝐂.⋯ 𝐂.⦅ β ⦆
              ≡⟨ cong₂ (λ x y → join p/s x y 𝐂.⋯ 𝐂.⦅ β ⦆)
                       (join-⋯ d _ _)
                       (𝐂.wk γ₂ 𝐂.⋯-wk-cancels-⦅ _ ⦆) ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F)) (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ β ⦆
              ≡⟨ join-⋯ p/s _ _ ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F) 𝐂.⋯ 𝐂.⦅ β ⦆) (𝐂.wk γ₂ 𝐂.⋯ 𝐂.⦅ β ⦆)
              ≡⟨ cong₂ (join p/s) (join-⋯ d _ _) (γ₂ 𝐂.⋯-wk-cancels-⦅ _ ⦆) ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weaken 𝐂.⋯ 𝐂.⦅ β ⦆) β) γ₂
              ≡⟨ cong (λ x → join p/s (join d x β) γ₂) (α 𝐂.⋯-weaken-cancels-⦅ β ⦆) ⟩
                join p/s (join d α β) γ₂
              ≲⟨ ≼-join p/s γ≤ (≼-refl refl) ⟩
                join p/s γ₁ γ₂
              ∎
    in
    T-Weaken ≤ϵ-refl γ≤′ $
      e′ ⊢⋯ₛ ⊢subₛ (e₁ ⊢⋯ ⊢weakenᵣ _) (λ U → 𝐂.allCx-⋯ `_ (Unr×Value⇒UnrCx U V₁ e₁))
                                      (λ m → 𝐂.allCx-⋯ `_ (Mobile×Value⇒MobCx m V₁ e₁))
         ⊢⋯ₛ ⊢subₛ e₂ (λ U → Unr×Value⇒UnrCx U V₂ e₂)
                      (λ m → Mobile×Value⇒MobCx m V₂ e₂)
  preservation′ (T-Weaken ϵ≤ γ≤ e) x =
    T-Weaken ϵ≤ γ≤ (preservation′ e x)

  preservation : Γ ; γ ⊢ e ∶ t ∣ ϵ → e ⋯→ e′ → Γ ; γ ⊢ e′ ∶ t ∣ ϵ
  preservation e (E-□ x) = preservation′ e x
  preservation e E@(E-Ctx (□· _) E₁) with e
  ... | T-App ϵ-eq e₁ e₂ = T-App ϵ-eq (preservation e₁ E₁) e₂
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (V₁ ·□) E₂) with e
  ... | T-App ϵ-eq e₁ e₂ = T-App ϵ-eq e₁ (preservation e₂ E₂)
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (□⊗ _) E₁) with e
  ... | T-Pair p/s e₁ e₂ seq⇒p = T-Pair p/s (preservation e₁ E₁) e₂ seq⇒p
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (V₁ ⊗□) E₂) with e
  ... | T-Pair p/s e₁ e₂ seq⇒p = T-Pair p/s e₁ (preservation e₂ E₂) seq⇒p
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (□; _) E₁) with e
  ... | T-LetUnit p/s e₁ e₂ = T-LetUnit p/s (preservation e₁ E₁) e₂
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (`let-`in _) E₁) with e
  ... | T-Let p/s e₁ e₂ = T-Let p/s (preservation e₁ E₁) e₂
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)
  preservation e E@(E-Ctx (`let⊗-`in _) E₁) with e
  ... | T-LetPair p/s e₁ e₂ = T-LetPair p/s (preservation e₁ E₁) e₂
  ... | T-Weaken ϵ≤ γ≤ e′ = T-Weaken ϵ≤ γ≤ (preservation e′ E)

module _ where
  variable
    b b₁ b₂ : ℕ

  open Fin.Patterns

  infix 4 _─→ₚ_

  data _─→ₚ_ {n} : Proc n → Proc n → Set where
    R-Exp : e₁ ⋯→ e₂ → ⟪ e₁ ⟫ ─→ₚ ⟪ e₂ ⟫

    R-New : (E : Frame n) →
      ⟪ E [ K (`new s) · K `unit ] ⟫
        ─→ₚ
      ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
        ⟪ E ⋯ᶠ weaken* _ [ (` 0F) ⊗ (` 1F) ] ⟫

    R-Fork : (E : Frame n) (V : Value e) →
      ⟪ E [ K `fork · e ] ⟫
        ─→ₚ
      ⟪ E [ K `unit ] ⟫ ∥ ⟪ e · K `unit ⟫

    R-Com : ∀ {E₁ E₂} → Value e →
      let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
      ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
        ((⟪ E₁ ⋯ᶠ wkρ [ K `send · ((` 0F) ⊗ (e ⋯ wkρ)) ] ⟫
          ∥ ⟪ E₂ ⋯ᶠ wkρ [ K `recv · (` {!weaken* ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (zero {?})!}) ] ⟫)
          ∥ (P ⋯ₚ wkρ))
        ─→ₚ
      ν (b₁ ∷ B₁) (b₂ ∷ B₂) ((⟪ E₁ [ K `unit ] ⟫ ∥ ⟪ E₂ [ e ] ⟫) ∥ P)

    R-LSplit : ∀ {E} →
      let x = Fin.cast (sym (cong (λ m → m + sum B + n) (L.sum-++ B₁ (suc b₁ ∷ B₂)) ■ {!+-assoc (sum B₁)!}))
                       (weaken* ⦃ Kᵣ ⦄ (sum B₁) 0F)
      in
      ν (B₁ ++ suc b₁ ∷ B₂) B (⟪ E [ K (`lsplit {!!} {!!}) · (` x) ] ⟫ ∥ P)
        ─→ₚ
      ν (B₁ ++ suc (suc b₁) ∷ B₂) B (⟪ E ⋯ᶠ {!!} [ (` {!!}) ⊗ (` {!!}) ] ⟫ ∥ (P ⋯ₚ {!!}))

    R-Drop : ∀ {E} →
      ν (suc b₁ ∷ B₁) B₂
        (⟪ E ⋯ᶠ weakenᵣ [ K `drop · (` 0F) ] ⟫ ∥ (P ⋯ₚ weakenᵣ))
        ─→ₚ
      ν (b₁ ∷ B₁) B₂
        (⟪ E [ K `unit ] ⟫ ∥ P)

    R-Acq : ∀ {E} →
      ν (zero ∷ suc b₁ ∷ B₁) B₂
        (⟪ E [ K `acq · (` 0F) ] ⟫ ∥ P)
        ─→ₚ
      ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ] ⟫ ∥ P)

    R-Close : ∀ {E₁ E₂} →
      ν L.[ 1 ] L.[ 1 ]
        ( ⟪ E₁ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ _ [ K (`end ‼) · (` 0F) ] ⟫
        ∥ ⟪ E₂ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ _ [ K (`end ⁇) · (` 1F) ] ⟫
        )
        ─→ₚ
      ⟪ E₁ [ K `unit ] ⟫ ∥ ⟪ E₂ [ K `unit ] ⟫

    R-Par :
      P ─→ₚ P′ →
      P ∥ Q ─→ₚ P′ ∥ Q

    R-Bind :
      P ─→ₚ Q →
      ν B₁ B₂ P ─→ₚ ν B₁ B₂ Q

    R-Struct :
      P ≋ P′ →
      P′ ─→ₚ Q′ →
      Q′ ≋ Q →
      P ─→ₚ Q
