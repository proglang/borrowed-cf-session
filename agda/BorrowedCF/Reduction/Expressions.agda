{-# OPTIONS --rewriting #-}

module BorrowedCF.Reduction.Expressions where

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
  E-SumElim : ∀ {i} (V : Value e) → `case `inj i e `of⟨ e₁ ; e₂ ⟩ ─→ (if i then e₁ else e₂) ⋯ ⦅ e ⦆
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
value⇒pure (V-⊗ V₁ V₂) (T-Pair p/s seq⇒p x₁ x₂) = T-Pair p/s seq⇒pure-ℙℙ (value⇒pure V₁ x₁) (value⇒pure V₂ x₂)
value⇒pure (V-⊕ V) (T-Inj x) = T-Inj (value⇒pure V x)
value⇒pure V (T-Conv eq ϵ≤ x) = T-Conv eq ≤ϵ-refl (value⇒pure V x)
value⇒pure V (T-Weaken γ≤ x) = T-Weaken γ≤ (value⇒pure V x)

module _ (Γ-S : ChanCx Γ) where
  inv-`⊤ : Value e → Γ ; γ ⊢ e ∶ `⊤ ∣ ϵ → e ≡ K `unit × Γ ∶ [] ≼ γ
  inv-`⊤ V (T-Const `unit)  = refl , (≼-∅ [])
  inv-`⊤ V (T-Conv `⊤ ϵ≤ e) = inv-`⊤ V e
  inv-`⊤ V (T-Weaken γ≤ e)  = Π.map₂ (λ z → ≼-trans z γ≤) (inv-`⊤ V e)
  inv-`⊤ V (T-Var x T-eq)   = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-arr : Value e → Γ ; γ ⊢ e ∶ T ⟨ a ⟩→ U ∣ ϵ →
    ∃[ T′ ] ∃[ U′ ] ∃[ ϵ ] T ≃ T′ × U ≃ U′ × ϵ ≤ϵ Arr.eff a ×
      ((∃[ c ] e ≡ K c × ⊢ c ∶ T′ ⟨ record a { eff = ϵ } ⟩→ U′)
        ⊎ (∃[ e′ ] e ≡ ƛ e′ × T′ ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) ⊢ e′ ∶ U′ ∣ ϵ))
  inv-arr V (T-Const c) = _ , _ , _ , ≃-refl , ≃-refl , ≤ϵ-refl , inj₁ (_ , refl , c)
  inv-arr V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()
  inv-arr V (T-Abs Γ-unr Γ-mob e) = _ , _ , _ , ≃-refl , ≃-refl , ≤ϵ-refl , inj₂ (_ , refl , e)
  inv-arr V (T-Conv (eq₁ `→ eq₂) ϵ≤ e)
    with _ , _ , _ , T≃ , U≃ , ϵ′≤ , x ← inv-arr V e
    = _ , _ , _ , ≃-trans (≃-sym eq₁) T≃ ,  ≃-trans (≃-sym eq₂) U≃ , ϵ′≤ , x
  inv-arr {a = a} V (T-Weaken γ≤ e)
    with inv-arr V e
  ... | _ , _ , _ , T≃ , U≃ , ϵ″≤ , inj₁ x
    = _ , _ , _ , T≃ , U≃ , ϵ″≤ , inj₁ x
  ... | _ , _ , _ , T≃ , U≃ , ϵ″≤ , inj₂ (_ , eq , x)
    = _ , _ , _ , T≃ , U≃ , ϵ″≤ , inj₂ (_ , eq , T-Weaken (≼-join (Arr.dir a) (≼-refl refl) (𝐂.≼-⋯ 𝐂.wk-preserves γ≤)) x)

  inv-⊗ : Value e → Γ ; γ ⊢ e ∶ T ⊗⟨ d ⟩ U ∣ ℙ →
    ∃[ α ] ∃[ β ] ∃[ e₁ ] ∃[ e₂ ]
      e ≡ e₁ ⊗ e₂
        × Γ ∶ join d α β ≼ γ
        × Γ ; α ⊢ e₁ ∶ T ∣ ℙ
        × Γ ; β ⊢ e₂ ∶ U ∣ ℙ
  inv-⊗ V (T-Pair p/s seq⇒p x₁ x₂)
    rewrite seq⇒pure-ℙϵ⁻¹ seq⇒p
    = _ , _ , _ , _ , refl , ≼-refl refl , x₁ , x₂
  inv-⊗ V (T-Conv (eq₁ ⊗ eq₂) ℙ≤ϵ x)
    = let _ , _ , _ , _ , eq , γ≤′ , x₁ , x₂ = inv-⊗ V x in
      _ , _ , _ , _ , eq , γ≤′ , T-Conv eq₁ ℙ≤ϵ x₁ , T-Conv eq₂ ℙ≤ϵ x₂
  inv-⊗ V (T-Weaken γ≤ x)
    = let _ , _ , _ , _ , eq , γ≤′ , x₁,x₂ = inv-⊗ V x in
      _ , _ , _ , _ , eq , ≼-trans γ≤′ γ≤ , x₁,x₂
  inv-⊗ V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()

  inv-inj : Value e → Γ ; γ ⊢ e ∶ T ⊕ U ∣ ϵ →
    ∃[ i ] ∃[ e′ ] e ≡ `inj i e′ × Γ ; γ ⊢ e′ ∶ if i then T else U ∣ ϵ
  inv-inj V (T-Var x T-eq) = case sym T-eq ■ Γ-S x .proj₂ of λ()
  inv-inj V (T-Inj x) = _ , _ , refl , x
  inv-inj V (T-Conv (T≃ ⊕ U≃) ϵ≤ x) with inv-inj V x
  ... | L , _ , eq , x′ = _ , _ , eq , T-Conv T≃ ϵ≤ x′
  ... | R , _ , eq , x′ = _ , _ , eq , T-Conv U≃ ϵ≤ x′
  inv-inj V (T-Weaken γ≤ x) =
    let _ , _ , eq , x′ = inv-inj V x in
    _ , _ , eq , T-Weaken γ≤ x′

  inv-session : Value e → Γ ; γ ⊢ e ∶ ⟨ s ⟩ ∣ ϵ →
    ∃[ s′ ] ∃[ x ] s ≃ s′ × e ≡ ` x × Γ x ≡ ⟨ s′ ⟩ × Γ ∶ ` x ≼ γ
  inv-session V (T-Var x T-eq) = _ , x , refl , refl , T-eq , ≼-refl refl
  inv-session V (T-Conv ⟨ eq ⟩ ϵ≤ x)
    = let _ , _ , eq-s , eq-e , eq-Γ , γ≤′ = inv-session V x in
      _ , _ , ≃-trans (≃-sym eq) eq-s , eq-e , eq-Γ , γ≤′
  inv-session V (T-Weaken γ≤ x)
    = let  _ , _ , eq-s , eq-e , eq-Γ , γ≤′ = inv-session V x in
      _ , _ , eq-s , eq-e , eq-Γ , ≼-trans γ≤′ γ≤

  tpred×value⇒allCx : {PA : Arr → Set} {PS : 𝕊 0 → Set} →
    PS Bin.Respects _≃_ →
    (∀ {a} → PA a → Arr.Unr a × ∀ {n} {Γ′ : Ctx n} {γ′} → UnrCx Γ′ γ′ → AllCx (TPred PA PS) Γ′ γ′) ⊎
       (∀ {a} → PA a → Arr.Mobile a × ∀ {n} {Γ′ : Ctx n} {γ′} → MobCx Γ′ γ′ → AllCx (TPred PA PS) Γ′ γ′) →
    Unr Un.⊆ TPred PA PS →
    TPred PA PS T → Value e → Γ ; γ ⊢ e ∶ T ∣ ϵ → AllCx (TPred PA PS) Γ γ
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P V (T-Const c) = []
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P V (T-Var x refl) = ` P
  tpred×value⇒allCx ps≃ (inj₁ pa⇒U) unr⇒P (arr pa) V (T-Abs Γ-unr Γ-mob x) = pa⇒U pa .proj₂ (Γ-unr (pa⇒U pa .proj₁))
  tpred×value⇒allCx ps≃ (inj₂ pa⇒M) unr⇒P (arr pa) V (T-Abs Γ-unr Γ-mob x) = pa⇒M pa .proj₂ (Γ-mob (pa⇒M pa .proj₁))
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P (P₁ ⊗ P₂) (V-⊗ V₁ V₂) (T-Pair p/s seq⇒p x₁ x₂) =
    allCx-join⁺ p/s (tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P₁ V₁ x₁)
                    (tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P₂ V₂ x₂)
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P (P₁ ⊕ P₂) (V-⊕ V) (T-Inj {i = i} x) =
    tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P (if[ TPred _ _ ] i then P₁ else P₂) V x
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P V (T-Conv T≃ ϵ≤ x) =
    tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P (tpred-≃ ps≃ (≃-sym T≃) P) V x
  tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P V (T-Weaken γ≤ x) =
    allCx-weaken unr⇒P γ≤ $ tpred×value⇒allCx ps≃ pa⇒M/U unr⇒P P V x

  unr×value⇒unrCx : Unr T → Value e → Γ ; γ ⊢ e ∶ T ∣ ϵ → UnrCx Γ γ
  unr×value⇒unrCx = tpred×value⇒allCx ≃-skips (inj₁ λ U → U , id) id

  mobile×value⇒mobCx : Mobile T → Value e → Γ ; γ ⊢ e ∶ T ∣ ϵ → MobCx Γ γ
  mobile×value⇒mobCx = tpred×value⇒allCx
    (λ eq → Sum.map (≃-skips eq) (Π.map₂ (Π.map₂ (≃-trans (≃-sym eq)))))
    (inj₂ (λ M → M , id))
    (tpred-map (λ {a} → Arr.ω⇒M a) inj₁)

  preservation′ : Γ ; γ ⊢ e ∶ T ∣ ϵ → e ─→ e′ → Γ ; γ ⊢ e′ ∶ T ∣ ϵ
  preservation′ (T-AppUnr {a = a} unr-a ≤₁ ≤₂ ≤ₐ f e) (E-App V)
    with (_ , _ , _ , T≃ , U≃ , ϵ≤ , inj₂ (_ , refl , f′)) ← inv-arr V-λ f
    rewrite Arr.ω⇒𝟙 a unr-a
    = T-Conv (≃-sym U≃) (≤ϵ-trans ϵ≤ ≤ₐ)
        $ T-Weaken (≼-refl (≈-trans (≈-reflexive (cong (_ ∥_) (𝐂.wk-cancels-⦅⦆-⋯ _ _))) ∥-comm))
        $ f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V (T-Conv T≃ ≤ϵ-refl e))
                       (λ U → unr×value⇒unrCx (unr-≃ (≃-sym T≃) U) V e)
                       (λ m → mobile×value⇒mobCx (mobile-≃ (≃-sym T≃) m) V e)
  preservation′ (T-AppLin refl ≤₁ ≤₂ ≤ₐ f e) (E-App V)
    with (_ , _ , _ , T≃ , U≃ , ϵ≤ , inj₂ (_ , refl , f′)) ← inv-arr V-λ f
    = T-Conv (≃-sym U≃) (≤ϵ-trans ϵ≤ ≤ₐ)
        $ T-Weaken (≼-refl (≈-trans (≈-reflexive (cong (_ ∥_) (𝐂.wk-cancels-⦅⦆-⋯ _ _))) ∥-comm))
        $ f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V (T-Conv T≃ ≤ϵ-refl e))
                       (λ U → unr×value⇒unrCx (unr-≃ (≃-sym T≃) U) V e)
                       (λ m → mobile×value⇒mobCx (mobile-≃ (≃-sym T≃) m) V e)
  preservation′ (T-AppLeft refl ≤₂ ≤ₐ f e) (E-App V)
    with (_ , _ , _ , T≃ , U≃ , ϵ≤ , inj₂ (_ , refl , f′)) ← inv-arr V-λ f
    = T-Conv (≃-sym U≃) (≤ϵ-trans ϵ≤ ≤ₐ)
        $ T-Weaken (≼-refl (≈-reflexive (cong (_ ;_) (𝐂.wk-cancels-⦅⦆-⋯ _ _))))
        $ f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V (T-Conv T≃ ≤ϵ-refl e))
                       (λ U → unr×value⇒unrCx (unr-≃ (≃-sym T≃) U) V e)
                       (λ m → mobile×value⇒mobCx (mobile-≃ (≃-sym T≃) m) V e)
  preservation′ (T-AppRight refl ≤₁ ≤ₐ f e) (E-App V)
    with (_ , _ , _ , T≃ , U≃ , ϵ≤ , inj₂ (_ , refl , f′)) ← inv-arr V-λ f
    = T-Conv (≃-sym U≃) (≤ϵ-trans ϵ≤ ≤ₐ)
        $ T-Weaken (≼-refl (≈-reflexive (cong (_; _) (𝐂.wk-cancels-⦅⦆-⋯ _ _))))
        $ f′ ⊢⋯ₛ ⊢subₛ (value⇒pure V (T-Conv T≃ ≤ϵ-refl e))
                       (λ U → unr×value⇒unrCx (unr-≃ (≃-sym T≃) U) V e)
                       (λ m → mobile×value⇒mobCx (mobile-≃ (≃-sym T≃) m) V e)
  preservation′ (T-Let p/s {γ₁} {γ₂} e₁ e₂) (E-Let V-e₁) =
    let eq = join-⋯ {ϕ = 𝐂.⦅ γ₁ ⦆} p/s (` zero) (𝐂.wk γ₂)
               ■ cong (join p/s γ₁) (𝐂.wk-cancels-⦅⦆-⋯ γ₂ γ₁)
    in
    subst-γ eq (e₂ ⊢⋯ₛ ⊢subₛ (value⇒pure V-e₁ e₁) (λ U → unr×value⇒unrCx U V-e₁ e₁) (λ m → mobile×value⇒mobCx m V-e₁ e₁))
  preservation′ (T-LetUnit {γ₁ = γ₁} {γ₂} e₁ e₂) E-Seq =
    let open ≼-Reasoning in
    let γ≤ = begin  γ₂       ≈⟨ ;-unit₁ ⟨
                    [] ; γ₂  ≲⟨ ≼-cong-; (inv-`⊤ V-K e₁ .proj₂) (≼-refl refl) ⟩
                    γ₁ ; γ₂  ∎
    in
    T-Weaken γ≤ e₂
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
                       (𝐂.wk-cancels-⦅⦆-⋯ (γ₂ 𝐂.⋯ 𝐂.weaken) _) ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F)) (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ β ⦆
              ≡⟨ join-⋯ p/s _ _ ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weaken) (` 0F) 𝐂.⋯ 𝐂.⦅ β ⦆) (𝐂.wk γ₂ 𝐂.⋯ 𝐂.⦅ β ⦆)
              ≡⟨ cong₂ (join p/s) (join-⋯ d _ _) (𝐂.wk-cancels-⦅⦆-⋯ _ _) ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weakenₛ 𝐂.⋯ 𝐂.⦅ β ⦆) β) γ₂
              ≡⟨ cong (λ x → join p/s (join d (x 𝐂.⋯ 𝐂.⦅ β ⦆) β) γ₂) (𝐂.⋯-congᶜ α {𝐂.weakenₛ} {𝐂.weakenᵣ} λ x → refl) ⟩
                join p/s (join d (α 𝐂.⋯ 𝐂.weakenᵣ 𝐂.⋯ 𝐂.⦅ β ⦆) β) γ₂
              ≡⟨ cong (λ x → join p/s (join d x β) γ₂) (𝐂.wk-cancels-⦅⦆-⋯ α β) ⟩
                join p/s (join d α β) γ₂
              ≲⟨ ≼-join p/s γ≤ (≼-refl refl) ⟩
                join p/s γ₁ γ₂
              ∎
    in
    T-Weaken γ≤′ $
      e′ ⊢⋯ₛ ⊢subₛ (e₁ ⊢⋯ ⊢weakenᵣ _) (λ U → 𝐂.allCx-⋯ `_ (unr×value⇒unrCx U V₁ e₁))
                                      (λ m → 𝐂.allCx-⋯ `_ (mobile×value⇒mobCx m V₁ e₁))
         ⊢⋯ₛ ⊢subₛ e₂ (λ U → unr×value⇒unrCx U V₂ e₂)
                      (λ m → mobile×value⇒mobCx m V₂ e₂)
  preservation′ (T-AbsRec {γ = γ} {a = a} Γ-unr a-unr e) E-Unfold =
    let open Fin.Patterns in
    let open ≼-Reasoning in
    let γ≤ = begin
           (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) 𝐂.⋯ 𝐂.⦅ γ ⦆ 𝐂.↑    ≡⟨⟩
           (` 0F) ∥ 𝐂.wk γ ∥ (𝐂.wk (𝐂.wk γ) 𝐂.⋯ 𝐂.⦅ γ ⦆ 𝐂.↑)  ≡⟨ cong ((` 0F) ∥ 𝐂.wk γ ∥_) (𝐂.⋯-↑-wk (𝐂.wk γ) 𝐂.⦅ γ ⦆ₛ) ⟨
           (` 0F) ∥ 𝐂.wk γ ∥ 𝐂.wk (𝐂.wk γ 𝐂.⋯ 𝐂.⦅ γ ⦆)        ≡⟨ cong ((` 0F) ∥ 𝐂.wk γ ∥_) (cong 𝐂.wk (𝐂.wk-cancels-⦅⦆-⋯ γ γ)) ⟩
           (` 0F) ∥ 𝐂.wk γ ∥ 𝐂.wk γ                           ≈⟨ ∥-assoc ⟩
           (` 0F) ∥ (𝐂.wk γ ∥ 𝐂.wk γ)                         ≈⟨ ∥-cong ≈-refl (∥-dup (𝐂.allCx-wk Γ-unr)) ⟨
           (` 0F) ∥ 𝐂.wk γ                                    ≡⟨⟩
           join 𝟙 (` 0F) (𝐂.wk γ)                             ≡⟨ cong (λ d → join d _ _) (Arr.ω⇒𝟙 a a-unr) ⟨
           join (Arr.dir a) (` 0F) (𝐂.wk γ) ∎
    in
    T-Abs {a = a} (const Γ-unr) (const (UnrCx⇒MobCx Γ-unr))
      $ T-Weaken γ≤
      $ e ⊢⋯ₛ ⊢↑ (⊢subₛ (T-AbsRec Γ-unr a-unr e) (const Γ-unr) (const (UnrCx⇒MobCx Γ-unr)))
  preservation′ (T-Case p/s {γ₁} {γ₂} e e₁ e₂) (E-SumElim V)
    with inv-inj (V-⊕ V) (value⇒pure (V-⊕ V) e)
  ... | L , _ , refl , e′ =
    let open ≡-Reasoning in
    let γ≡ = join p/s (` zero) (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ γ₁ ⦆  ≡⟨ join-⋯ p/s (` zero) (𝐂.wk γ₂) ⟩
             join p/s γ₁ (𝐂.wk γ₂ 𝐂.⋯ 𝐂.⦅ γ₁ ⦆)        ≡⟨ cong (join p/s γ₁) (𝐂.wk-cancels-⦅⦆-⋯ γ₂ γ₁) ⟩
             join p/s γ₁ γ₂ ∎
    in
    subst-γ γ≡ $ e₁ ⊢⋯ₛ ⊢subₛ e′ (λ U → unr×value⇒unrCx U V e′) λ m → mobile×value⇒mobCx m V e′
  ... | R , _ , refl , e′ =
    let open ≡-Reasoning in
    let γ≡ = join p/s (` zero) (𝐂.wk γ₂) 𝐂.⋯ 𝐂.⦅ γ₁ ⦆  ≡⟨ join-⋯ p/s (` zero) (𝐂.wk γ₂) ⟩
             join p/s γ₁ (𝐂.wk γ₂ 𝐂.⋯ 𝐂.⦅ γ₁ ⦆)        ≡⟨ cong (join p/s γ₁) (𝐂.wk-cancels-⦅⦆-⋯ γ₂ γ₁) ⟩
             join p/s γ₁ γ₂ ∎
    in
    subst-γ γ≡ $ e₂ ⊢⋯ₛ ⊢subₛ e′ (λ U → unr×value⇒unrCx U V e′) λ m → mobile×value⇒mobCx m V e′
  preservation′ (T-Weaken γ≤ e) x =
    T-Weaken γ≤ (preservation′ e x)
  preservation′ (T-Conv eq ϵ≤ e) x =
    T-Conv eq ϵ≤ (preservation′ e x)

  preservation : Γ ; γ ⊢ e ∶ T ∣ ϵ → e ⋯→ e′ → Γ ; γ ⊢ e′ ∶ T ∣ ϵ
  preservation e (E-□ x) = preservation′ e x
  preservation e E@(E-Ctx (□· _) E₁) with e
  ... | T-AppUnr   x ≤₁ ≤₂ ≤ₐ e₁ e₂  = T-AppUnr   x ≤₁ ≤₂ ≤ₐ (preservation e₁ E₁) e₂
  ... | T-AppLin   x ≤₁ ≤₂ ≤ₐ e₁ e₂  = T-AppLin   x ≤₁ ≤₂ ≤ₐ (preservation e₁ E₁) e₂
  ... | T-AppLeft  x    ≤₂ ≤ₐ e₁ e₂  = T-AppLeft  x    ≤₂ ≤ₐ (preservation e₁ E₁) e₂
  ... | T-AppRight x ≤₁    ≤ₐ e₁ e₂  = T-AppRight x ≤₁    ≤ₐ (preservation e₁ E₁) e₂
  ... | T-Weaken   γ≤ e′    = T-Weaken  γ≤ (preservation e′ E)
  ... | T-Conv     eq ϵ≤ e′ = T-Conv    eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (V₁ ·□) E₂) with e
  ... | T-AppUnr   x ≤₁ ≤₂ ≤ₐ e₁ e₂  = T-AppUnr   x ≤₁ ≤₂ ≤ₐ e₁ (preservation e₂ E₂)
  ... | T-AppLin   x ≤₁ ≤₂ ≤ₐ e₁ e₂  = T-AppLin   x ≤₁ ≤₂ ≤ₐ e₁ (preservation e₂ E₂)
  ... | T-AppLeft  x    ≤₂ ≤ₐ e₁ e₂  = T-AppLeft  x    ≤₂ ≤ₐ e₁ (preservation e₂ E₂)
  ... | T-AppRight x ≤₁    ≤ₐ e₁ e₂  = T-AppRight x ≤₁    ≤ₐ e₁ (preservation e₂ E₂)
  ... | T-Weaken   γ≤ e′    = T-Weaken  γ≤ (preservation e′ E)
  ... | T-Conv     eq ϵ≤ e′ = T-Conv    eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (□⊗ _) E₁) with e
  ... | T-Pair p/s seq⇒p e₁ e₂ = T-Pair p/s seq⇒p (preservation e₁ E₁) e₂
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (V₁ ⊗□) E₂) with e
  ... | T-Pair p/s seq⇒p e₁ e₂ = T-Pair p/s seq⇒p e₁ (preservation e₂ E₂)
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (□; _) E₁) with e
  ... | T-LetUnit e₁ e₂ = T-LetUnit (preservation e₁ E₁) e₂
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (`let-`in _) E₁) with e
  ... | T-Let p/s e₁ e₂ = T-Let p/s (preservation e₁ E₁) e₂
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (`let⊗-`in _) E₁) with e
  ... | T-LetPair p/s e₁ e₂ = T-LetPair p/s (preservation e₁ E₁) e₂
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx (`inj□ i) E′) with e
  ... | T-Inj e′        = T-Inj (preservation e′ E′)
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)
  preservation e E@(E-Ctx `case□`of⟨ e₁ ; e₂ ⟩ E′) with e
  ... | T-Case p/s e e₁ e₂ = T-Case p/s (preservation e E′) e₁ e₂
  ... | T-Weaken γ≤ e′  = T-Weaken γ≤ (preservation e′ E)
  ... | T-Conv eq ϵ≤ e′ = T-Conv eq ϵ≤ (preservation e′ E)

  progress : Γ ; γ ⊢ e ∶ T ∣ ϵ → Value e ⊎ e ⋯↛ ⊎ ∃[ e′ ] e ⋯→ e′
  progress (T-Const x) = inj₁ V-K
  progress (T-Var x T-eq) = inj₁ V-`
  progress (T-Abs Γ-unr Γ-mob e) = inj₁ V-λ
  progress (T-AbsRec Γ-unr a-unr e) = inj₂ (inj₂ (_ , E-□ E-Unfold))
  progress (T-AppUnr unr-a ≤₁ ≤₂ ≤ₐ e₁ e₂)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□· _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□· _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ·□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ·□) e₂→))
  ... | inj₁ V-e₂
    with inv-arr V-e₁ e₁
  ... | (_ , _ , _ , _ , _ , _ , inj₁ (c , refl , x)) = inj₂ (inj₁ (E-□ (_ , _ , V-e₂ , refl)))
  ... | (_ , _ , _ , _ , _ , _ , inj₂ (e , refl , x)) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress (T-AppLin lin-a ≤₁ ≤₂ ≤ₐ e₁ e₂)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□· _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□· _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ·□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ·□) e₂→))
  ... | inj₁ V-e₂
    with inv-arr V-e₁ e₁
  ... | (_ , _ , _ , _ , _ , _ , inj₁ (c , refl , x)) = inj₂ (inj₁ (E-□ (_ , _ , V-e₂ , refl)))
  ... | (_ , _ , _ , _ , _ , _ , inj₂ (e , refl , x)) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress (T-AppLeft a-L ≤₂ ≤ₐ e₁ e₂)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□· _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□· _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ·□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ·□) e₂→))
  ... | inj₁ V-e₂
    with inv-arr V-e₁ e₁
  ... | (_ , _ , _ , _ , _ , _ , inj₁ (c , refl , x)) = inj₂ (inj₁ (E-□ (_ , _ , V-e₂ , refl)))
  ... | (_ , _ , _ , _ , _ , _ , inj₂ (e , refl , x)) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress (T-AppRight a-R ≤₁ ≤ₐ e₁ e₂)
    with progress e₁
  ... | inj₂ (inj₁ e₁↛)       = inj₂ (inj₁ (E-Ctx (□· _) e₁↛))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□· _) e₁→))
  ... | inj₁ V-e₁
    with progress e₂
  ... | inj₂ (inj₁ e₂↛)       = inj₂ (inj₁ (E-Ctx (V-e₁ ·□) e₂↛))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ·□) e₂→))
  ... | inj₁ V-e₂
    with inv-arr V-e₁ e₁
  ... | (_ , _ , _ , _ , _ , _ , inj₁ (c , refl , x)) = inj₂ (inj₁ (E-□ (_ , _ , V-e₂ , refl)))
  ... | (_ , _ , _ , _ , _ , _ , inj₂ (e , refl , x)) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress (T-Pair p/s seq⇒pure e₁ e₂)
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
  progress (T-LetUnit e e′)
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
  progress (T-Inj e)
    with progress e
  ... | inj₁ V-e             = inj₁ (V-⊕ V-e)
  ... | inj₂ (inj₁ e↛)       = inj₂ (inj₁ (E-Ctx (`inj□ _) e↛))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx (`inj□ _) e→))
  progress (T-Case p/s e e₁ e₂)
    with progress e
  ... | inj₂ (inj₁ e↛)       = inj₂ (inj₁ (E-Ctx `case□`of⟨ _ ; _ ⟩ e↛))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx `case□`of⟨ _ ; _ ⟩ e→))
  ... | inj₁ V-e
    with _ , _ , refl , e′ ← inv-inj V-e e
    with V-⊕ V ← V-e
    = inj₂ (inj₂ (_ , E-□ (E-SumElim V)))
  progress (T-Weaken γ≤ e) = progress e
  progress (T-Conv eq ϵ≤ e) = progress e
