{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction.Expressions where

import Data.Vec.Functional as F

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context

open import BorrowedCF.Reduction.Base
open Variables

import BorrowedCF.Context.Substitution as 𝐂

infix 4 _─→_ _⋯→_

data _─→_ {n} : Tm n → Tm n → Set where
  E-App : (V : Value e₂) → (ƛ e₁) · e₂ ─→ e₁ ⋯ ⦅ e₂ ⦆
  E-Seq : K `unit ; e ─→ e
  E-Let : Value e₁ → `let e₁ `in e₂ ─→ e₂ ⋯ ⦅ e₁ ⦆
  E-PairElim : (V₁ : Value e₁) (V₂ : Value e₂) → `let⊗ (e₁ ⊗ e₂) `in e ─→ e ⋯ ⦅ wk e₁ ⦆ ⋯ ⦅ e₂ ⦆
  E-Unfold : μ e ─→ e ⋯ ⦅ μ e ⦆

data _⋯→_ {n} : Tm n → Tm n → Set where
  E-□   : e₁ ─→ e₂ → e₁ ⋯→ e₂
  E-Ctx : (E : Frame n) → e₁ ⋯→ e₂ → E [ e₁ ] ⋯→ E [ e₂ ]

infixl 4 _⋯↛

data _⋯↛ {n} : Tm n → Set where
  E-□   : Blocked e → e ⋯↛
  E-Ctx : (E : Frame n) → e ⋯↛ → E [ e ] ⋯↛

value⇒pure : Value e → (x : Γ ; γ ⊢ e ∶ T ∣ ϵ) → Γ ; γ ⊢ e ∶ T ∣ ℙ
value⇒pure V (T-Var x T-eq) = T-Var x T-eq
value⇒pure V (T-Const x) = T-Const x
value⇒pure V (T-Abs Γ-unr Γ-mob x) = T-Abs Γ-unr Γ-mob x
value⇒pure (V-⊗ V₁ V₂) (T-Pair p/s x₁ x₂ seq⇒p) = T-Pair p/s (value⇒pure V₁ x₁) (value⇒pure V₂ x₂) seq⇒pure-ℙℙ
value⇒pure V (T-Weaken ϵ≤ γ≤ x) = T-Weaken ≤ϵ-refl γ≤ (value⇒pure V x)

module _ (Γ-S : ChanCx Γ) where
  inv-`⊤ : Value e → Γ ; γ ⊢ e ∶ `⊤ ∣ ϵ → e ≡ K `unit × Γ ∶ [] ≼ γ
  inv-`⊤ V (T-Const `unit)    = refl , (≼-∅ [])
  inv-`⊤ V (T-Weaken ϵ≤ γ≤ e) = Π.map₂ (λ z → ≼-trans z γ≤) (inv-`⊤ V e)
  inv-`⊤ V (T-Var x T-eq)     = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-arr : Value e → Γ ; γ ⊢ e ∶ T ⟨ a ⟩→ U ∣ ϵ →
    (∃[ c ] e ≡ K c × ⊢ c ∶ T ⟨ a ⟩→ U)
      ⊎ (∃[ e′ ] e ≡ ƛ e′ × T F.∷ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) ⊢ e′ ∶ U ∣ Arr.eff a)
  inv-arr V (T-Const c) = inj₁ (_ , refl , c)
  inv-arr V (T-Abs Γ-unr Γ-mob e) = inj₂ (_ , refl , e)
  inv-arr {a = a} V (T-Weaken ϵ≤ γ≤ e)
    with inv-arr V e
  ... | inj₁ x = inj₁ x
  ... | inj₂ (_ , eq , x) = inj₂ (_ , eq , T-Weaken ≤ϵ-refl (≼-join (Arr.dir a) (≼-refl refl) (𝐂.≼-𝐂wk γ≤)) x)
  inv-arr V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-⊗ : Value e → Γ ; γ ⊢ e ∶ T ⊗⟨ d ⟩ U ∣ ℙ →
    ∃[ α ] ∃[ β ] ∃[ e₁ ] ∃[ e₂ ]
      e ≡ e₁ ⊗ e₂
        × Γ ∶ join d α β ≼ γ
        × Γ ; α ⊢ e₁ ∶ T ∣ ℙ
        × Γ ; β ⊢ e₂ ∶ U ∣ ℙ
  inv-⊗ V (T-Pair p/s x₁ x₂ seq⇒p)
    rewrite seq⇒pure-ℙϵ⁻¹ seq⇒p
    = _ , _ , _ , _ , refl , ≼-refl refl , x₁ , x₂
  inv-⊗ V (T-Weaken ℙ≤ϵ γ≤ x)
    = let _ , _ , _ , _ , eq , γ≤′ , x₁,x₂ = inv-⊗ V x in
       _ , _ , _ , _ , eq , ≼-trans γ≤′ γ≤ , x₁,x₂
  inv-⊗ V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()

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

  preservation′ : Γ ; γ ⊢ e ∶ T ∣ ϵ → e ─→ e′ → Γ ; γ ⊢ e′ ∶ T ∣ ϵ
  preservation′ (T-App {a = a} refl f e) (E-App V)
    with inj₂ (_ , refl , f′) ← inv-arr V-λ f
    =
    let open Arr a in
    T-Weaken ≤ϵ-refl (≼-refl (≈-reflexive (join-⋯ dir _ _ ■ cong (join dir _) (_ 𝐂.⋯-wk-cancels-⦅ _ ⦆))))
                     (f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V e) (λ U → Unr×Value⇒UnrCx U V e) (λ m → Mobile×Value⇒MobCx m V e))
  preservation′ (T-Let p/s {γ₁} {γ₂} e₁ e₂) (E-Let V-e₁) =
    let eq = join-⋯ {σ = 𝐂.⦅ γ₁ ⦆} p/s (` zero) (𝐂.wk γ₂)
               ■ cong (join p/s γ₁) (γ₂ 𝐂.⋯-wk-cancels-⦅ γ₁ ⦆)
    in
    subst-γ eq (e₂ ⊢⋯ₛ ⊢subₛ (value⇒pure V-e₁ e₁) (λ U → Unr×Value⇒UnrCx U V-e₁ e₁) (λ m → Mobile×Value⇒MobCx m V-e₁ e₁))
  preservation′ (T-LetUnit p/s e₁ e₂) E-Seq =
    let γ≼ = ≼-trans (≼-refl (≈-sym (join-[]₁ p/s)))
                     (≼-join p/s (inv-`⊤ V-K e₁ .proj₂) (≼-refl refl))
    in
    T-Weaken ≤ϵ-refl γ≼ e₂
  preservation′ (T-LetPair {d = d} {T₂ = T₂} p/s {γ₁} {γ₂} e e′) (E-PairElim V₁ V₂)
    with α , β , _ , _ , refl , γ≤ , e₁ , e₂ ← inv-⊗ (V-⊗ V₁ V₂) (value⇒pure (V-⊗ V₁ V₂) e)
    =
    let open Fin.Patterns in
    let open ≼-Reasoning in
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
  preservation′ (T-AbsRec {γ = γ} {a = a} Γ-unr a-unr e) E-Unfold =
    let open Fin.Patterns in
    let open ≼-Reasoning in
    let γ≤ = begin
               (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) 𝐂.⋯ 𝐂.⦅ γ ⦆ 𝐂.↑    ≡⟨⟩
               (` 0F) ∥ 𝐂.wk γ ∥ (𝐂.wk (𝐂.wk γ) 𝐂.⋯ 𝐂.⦅ γ ⦆ 𝐂.↑)  ≡⟨ cong ((` 0F) ∥ 𝐂.wk γ ∥_) (𝐂.⋯-↑-wk (𝐂.wk γ) _) ⟨
               (` 0F) ∥ 𝐂.wk γ ∥ 𝐂.wk (𝐂.wk γ 𝐂.⋯ 𝐂.⦅ γ ⦆)        ≡⟨ cong ((` 0F) ∥ 𝐂.wk γ ∥_) (cong 𝐂.wk (γ 𝐂.⋯-wk-cancels-⦅ γ ⦆)) ⟩
               (` 0F) ∥ 𝐂.wk γ ∥ 𝐂.wk γ                           ≈⟨ ∥-assoc ⟩
               (` 0F) ∥ (𝐂.wk γ ∥ 𝐂.wk γ)                         ≈⟨ ∥-cong ≈-refl (∥-dup (𝐂.allCx-wk Γ-unr)) ⟨
               (` 0F) ∥ 𝐂.wk γ                                    ≡⟨⟩
               join 𝟙 (` 0F) (𝐂.wk γ)                             ≡⟨ cong (λ d → join d _ _) (Arr.ω⇒𝟙 a a-unr) ⟨
               join (Arr.dir a) (` 0F) (𝐂.wk γ)                   ∎
    in
    T-Abs {a = a} (const Γ-unr) (const (UnrCx⇒MobCx Γ-unr))
      $ T-Weaken ≤ϵ-refl γ≤
      $ e ⊢⋯ₛ ⊢↑ (⊢subₛ (T-AbsRec Γ-unr a-unr e) (const Γ-unr) (const (UnrCx⇒MobCx Γ-unr)))
  preservation′ (T-Weaken ϵ≤ γ≤ e) x =
    T-Weaken ϵ≤ γ≤ (preservation′ e x)

  preservation : Γ ; γ ⊢ e ∶ T ∣ ϵ → e ⋯→ e′ → Γ ; γ ⊢ e′ ∶ T ∣ ϵ
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

  progress : Γ ; γ ⊢ e ∶ T ∣ ϵ → Value e ⊎ e ⋯↛ ⊎ ∃[ e′ ] e ⋯→ e′
  progress (T-Const x) = inj₁ V-K
  progress (T-Var x T-eq) = inj₁ V-`
  progress (T-Abs Γ-unr Γ-mob e) = inj₁ V-λ
  progress (T-AbsRec Γ-unr a-unr e) = inj₂ (inj₂ (_ , E-□ E-Unfold))
  progress (T-App refl e₁ e₂)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□· _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□· _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ·□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ·□) e₂→))
  ... | inj₁ V-e₂
    with inv-arr V-e₁ e₁
  ... | inj₁ (c , refl , x) = inj₂ (inj₁ (E-□ (_ , _ , V-e₂ , refl)))
  ... | inj₂ (e , refl , x) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress (T-Pair p/s e₁ e₂ seq⇒pure)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□⊗ _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□⊗ _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₁ V-e₂             = inj₁ (V-⊗ V-e₁ V-e₂)
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ⊗□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ⊗□) e₂→))
  progress (T-Let p/s e e′)
    with progress e
  ... | inj₁ V-e              = inj₂ (inj₂ (_ , E-□ (E-Let V-e)))
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (`let-`in _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (`let-`in _) e₁→))
  progress (T-LetUnit p/s e e′)
    with progress e
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□; _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□; _) e₁→))
  ... | inj₁ V-e rewrite inv-`⊤ V-e e .proj₁ = inj₂ (inj₂ (_ , E-□ E-Seq))
  progress (T-LetPair p/s e e′)
    with progress e
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (`let⊗-`in _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (`let⊗-`in _) e₁→))
  ... | inj₁ V-e
    with inv-⊗ V-e (value⇒pure V-e e)
  ... | _ , _ , _ , _ , refl , _
    with V-e
  ... | V-⊗ V₁ V₂ = inj₂ (inj₂ (_ , E-□ (E-PairElim V₁ V₂)))
  progress (T-Weaken ϵ≤ γ≤ e) = progress e
