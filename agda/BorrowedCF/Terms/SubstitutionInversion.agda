module BorrowedCF.Terms.SubstitutionInversion where

open import Data.Fin.Subset renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties
open import Function.Related.Propositional

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Context.Substitution as 𝐂 using (_∈img_; _∶_⇔_)
open import BorrowedCF.Terms.Base
open import BorrowedCF.Terms.DescendAbs
open import BorrowedCF.Types

open Nat.Variables
open Fin using (suc-injective)

inv-ƛ : ∀ {n} {Γ : Ctx n} {γ e} {U : 𝕋} {ϵ} → Γ ; γ ⊢ ƛ e ∶ U ∣ ϵ → ∃[ a ] ∃[ Ta ] ∃[ Ua ] ∃[ γ₀ ]
  (U ≃ Ta ⟨ a ⟩→ Ua) × Γ ∶ γ₀ ≼ γ
    × (Arr.Unr a → UnrCx Γ γ₀) × (Arr.Mobile a → MobCx Γ γ₀)
    × (Ta ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ₀) ⊢ e ∶ Ua ∣ Arr.eff a)
inv-ƛ (T-Abs Γ-unr Γ-mob d) =
  _ , _ , _ , _ , ≃-refl , ≼-refl refl , Γ-unr , Γ-mob , d
inv-ƛ (T-Conv U≃ ϵ≤ x) =
  let a , Ta , Ua , γ₀ , arr≃ , ≤ , u , mo , d = inv-ƛ x in
  a , Ta , Ua , γ₀ , ≃-trans (≃-sym U≃) arr≃ , ≤ , u , mo , d
inv-ƛ (T-Weaken γ≤ x) =
  let a , Ta , Ua , γ₀ , arr≃ , ≤ , u , mo , d = inv-ƛ x in
  a , Ta , Ua , γ₀ , arr≃ , ≼-trans ≤ γ≤ , u , mo , d

μ-ƛ : ∀ {n} {Γ : Ctx n} {γ} {b} {V : 𝕋} {ϵ} → Γ ; γ ⊢ μ b ∶ V ∣ ϵ → ∃[ e ] b ≡ ƛ e
μ-ƛ (T-AbsRec _ _ _) = _ , refl
μ-ƛ (T-Conv _ _ x) = μ-ƛ x
μ-ƛ (T-Weaken _ x) = μ-ƛ x

inv-μ : ∀ {n} {Γ : Ctx n} {γ e} {V : 𝕋} {ϵ} → Γ ; γ ⊢ μ (ƛ e) ∶ V ∣ ϵ →
  ∃[ a ] ∃[ T ] ∃[ U ] ∃[ γ₀ ]
    (V ≃ T ⟨ a ⟩→ U) × Arr.Unr a × Γ ∶ γ₀ ≼ γ × UnrCx Γ γ₀
    × (T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` zero) ∥ (` suc zero) ∥ 𝐂.wk (𝐂.wk γ₀) ⊢ e ∶ U ∣ Arr.eff a)
inv-μ (T-AbsRec Γ-unr a-unr d) = _ , _ , _ , _ , ≃-refl , a-unr , ≼-refl refl , Γ-unr , d
inv-μ (T-Conv V≃ ϵ≤ x) =
  let a , T , U , γ₀ , arr≃ , au , ≤ , uc , d = inv-μ x in
  a , T , U , γ₀ , ≃-trans (≃-sym V≃) arr≃ , au , ≤ , uc , d
inv-μ (T-Weaken γ≤ x) =
  let a , T , U , γ₀ , arr≃ , au , ≤ , uc , d = inv-μ x in
  a , T , U , γ₀ , arr≃ , au , ≼-trans ≤ γ≤ , uc , d

lift-disg : {ρ : m →ᵣ n} {σ : m 𝐂.→ₛ n} →
  (∀ x → ` ρ x ≡ σ x) →
  (∀ x → ` (ρ 𝐂.↑ᵣ) x ≡ (σ 𝐂.↑ₛ) x)
lift-disg eq zero    = refl
lift-disg eq (suc y) = cong (𝐂._⋯ᵣ 𝐂.weakenᵣ) (eq y)

brₛ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct m) → γ 𝐂.⋯ ϕ ≡ γ 𝐂.⋯ σ
brₛ ⊢ϕ γ = sym (𝐂.conv-⋯ᵣₛ γ) ■ 𝐂.⋯-cong γ (⊢ren-ϕ≗σ ⊢ϕ)

brₛ↑ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (suc m)) → γ 𝐂.⋯ (ϕ 𝐂.↑ᵣ) ≡ γ 𝐂.⋯ (σ 𝐂.↑ₛ)
brₛ↑ ⊢ϕ γ = sym (𝐂.conv-⋯ᵣₛ γ) ■ 𝐂.⋯-cong γ (lift-disg (⊢ren-ϕ≗σ ⊢ϕ))

brₛ↑↑ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (suc (suc m))) →
  γ 𝐂.⋯ᵣ (ϕ 𝐂.↑ᵣ 𝐂.↑ᵣ) ≡ γ 𝐂.⋯ (σ 𝐂.↑ₛ 𝐂.↑ₛ)
brₛ↑↑ ⊢ϕ γ = sym (𝐂.conv-⋯ᵣₛ γ) ■ 𝐂.⋯-cong γ (lift-disg (lift-disg (⊢ren-ϕ≗σ ⊢ϕ)))

⊢⋯⁻¹ : ∀ {m n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {γ} {e} {T : 𝕋} {ϵ} {ϕ : m →ᵣ n} {σ} →
  𝐂.Inj ϕ → Γ₂ ; γ ⊢ e ⋯ ϕ ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ e ∶ T ∣ ϵ
⊢⋯⁻¹ {e = ` x} inj p ⊢ϕ =
  let T≃ , ≼γ = inv-` p in
  _ , ≼-respˡ-≈ (≈-reflexive (sym (proj₁ (⊢ϕ & x)))) ≼γ
    , T-Conv (≃-trans (≃-reflexive (sym (V.[]=⇒lookup (proj₂ (⊢ϕ & x))))) (≃-sym T≃)) ℙ≤ϵ (T-Var _ refl)
⊢⋯⁻¹ {e = K c} inj p ⊢ϕ =
  let _ , T≃ , ≼γ , ⊢c = inv-K p in
  _ , ≼γ , T-Conv T≃ ℙ≤ϵ (T-Const ⊢c)
⊢⋯⁻¹ {Γ₁ = Γ₁} {e = ƛ e} {ϕ = ρ} inj p ⊢ϕ =
  let a , Ta , Ua , γa , T≃ , γa≼γ , uc , mc , d = inv-ƛ p
      γb′ , ≼b , pb = ⊢⋯⁻¹ {e = e} {T = Ua} {ϵ = Arr.eff a} {ϕ = ρ ↑ᵣ} (↑-inj inj) d (⊢↑ ⊢ϕ)
      ≼bᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑ ⊢ϕ γb′)) ≼b
      γr , p1 , p2 = descend-abs inj (⊢ren-ϕ⇔ ⊢ϕ) (Arr.dir a) γa γb′ ≼bᵣ
      out≼ = ≼-trans (subst (λ z → _ ∶ z ≼ γa) (brₛ ⊢ϕ γr) p2) γa≼γ
      uc′ = λ ua → 𝐂.allCx-⋯⁻¹ (𝐂.⇔-preserves[ reverseImplication ] ⦃ 𝐂.Kₛ ⦄ Γ₁ (⊢ren-ϕ⇔ ⊢ϕ)) (allCx-strengthen p2 (uc ua))
      mc′ = λ ma → 𝐂.allCx-⋯⁻¹ (𝐂.⇔-preserves[ reverseImplication ] ⦃ 𝐂.Kₛ ⦄ Γ₁ (⊢ren-ϕ⇔ ⊢ϕ)) (allCx-strengthen p2 (mc ma))
  in γr , out≼ , (T-Conv (≃-sym T≃) ℙ≤ϵ (T-Abs uc′ mc′ (T-Weaken p1 pb)))
⊢⋯⁻¹ {Γ₁ = Γ₁} {e = μ (ƛ e)} {ϕ = ρ} inj p ⊢ϕ =
  let a , T , U , γ₀ , V≃ , a-unr , γ₀≼γ , uc , d = inv-μ p
      γbb , ≼bb , pbb = ⊢⋯⁻¹ {e = e} {T = U} {ϵ = Arr.eff a} {ϕ = ρ ↑ᵣ ↑ᵣ}
                          (↑-inj (↑-inj inj)) d (⊢↑ (⊢↑ ⊢ϕ))
      ≼bbᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑↑ ⊢ϕ γbb)) ≼bb
      γr , p1 , p2 = descend-abs² inj (⊢ren-ϕ⇔ ⊢ϕ) 𝟙 γ₀ ((` zero) ∥ (` suc zero)) γbb ⊆-refl ≼bbᵣ
      out≼ = ≼-trans (subst (λ z → _ ∶ z ≼ γ₀) (brₛ ⊢ϕ γr) p2) γ₀≼γ
      uc′ = 𝐂.allCx-⋯⁻¹ (𝐂.⇔-preserves[ reverseImplication ] ⦃ 𝐂.Kₛ ⦄ Γ₁ (⊢ren-ϕ⇔ ⊢ϕ)) (allCx-strengthen p2 uc)
  in γr , out≼ , T-Conv (≃-sym V≃) ℙ≤ϵ (T-AbsRec uc′ a-unr (T-Weaken p1 pbb))
⊢⋯⁻¹ {e = μ (` x)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (K c)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (μ e)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (e₁ ·⟨ d ⟩ e₂)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (e₁ ; e₂)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (e₁ ⊗ e₂)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (`let e₁ `in e₂)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (`let⊗ e₁ `in e₂)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (`inj i e)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = μ (`case e `of⟨ e₁ ; e₂ ⟩)} inj p ⊢ϕ with _ , () ← μ-ƛ p
⊢⋯⁻¹ {e = e₁ ·⟨ d ⟩ e₂} inj p ⊢ϕ with inv-· p
... | a , α , β , _ , ≤γ , d≡ , eff≤ , T-AppUnr a-unr x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ dd → _ ∶ join dd β α ≼ _) (Arr.ω⇒𝟙 a a-unr) ≤γ
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≼α ≼β) (≼-trans (≼-refl ∥-comm) jeq)
     , subst (λ dd → _ ; (α′ ∥ β′) ⊢ e₁ ·⟨ dd ⟩ e₂ ∶ _ ∣ _) (sym (sym d≡ ■ Arr.ω⇒𝟙 a a-unr)) (T-AppUnr a-unr eff≤ x′ y′)
... | a , α , β , _ , ≤γ , d≡ , eff≤ , T-AppLin a-par x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ dd → _ ∶ join dd β α ≼ _) (proj₂ a-par) ≤γ
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≼α ≼β) (≼-trans (≼-refl ∥-comm) jeq)
     , subst (λ dd → _ ; (α′ ∥ β′) ⊢ e₁ ·⟨ dd ⟩ e₂ ∶ _ ∣ _) (sym (sym d≡ ■ proj₂ a-par)) (T-AppLin a-par eff≤ x′ y′)
... | a , α , β , _ , ≤γ , d≡ , eff≤ , T-AppLeft aL x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ dd → _ ∶ join dd β α ≼ _) aL ≤γ
  in β′ ; α′ , ≼-trans (≼-cong-; ≼β ≼α) jeq
     , subst (λ dd → _ ; (β′ ; α′) ⊢ e₁ ·⟨ dd ⟩ e₂ ∶ _ ∣ _) (sym (sym d≡ ■ aL)) (T-AppLeft aL eff≤ x′ y′)
... | a , α , β , _ , ≤γ , d≡ , eff≤ , T-AppRight aR x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ dd → _ ∶ join dd β α ≼ _) aR ≤γ
  in α′ ; β′ , ≼-trans (≼-cong-; ≼α ≼β) jeq
     , subst (λ dd → _ ; (α′ ; β′) ⊢ e₁ ·⟨ dd ⟩ e₂ ∶ _ ∣ _) (sym (sym d≡ ■ aR)) (T-AppRight aR eff≤ x′ y′)
⊢⋯⁻¹ {e = e₁ ; e₂} inj p ⊢ϕ =
  let γ₁ , γ₂ , T , uT , ≤ , x , y = inv-; p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂′ , ≼₂ , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
  in γ₁′ ; γ₂′ , ≼-trans (≼-cong-; ≼₁ ≼₂) ≤ , T-Seq uT x′ y′
⊢⋯⁻¹ {e = e₁ ⊗ e₂} inj p ⊢ϕ =
  let p/s , γ₁ , γ₂ , T , U , ϵ₁ , ϵ₂ , ≤ , ty≃ , e≤ , s⇒p , x , y = inv-⊗ p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂′ , ≼₂ , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
  in join (biasedDir p/s) γ₁′ γ₂′
   , subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ (biasedDir p/s) γ₁′ γ₂′)) (≼-trans (≼-join (biasedDir p/s) ≼₁ ≼₂) ≤)
   , T-Conv ty≃ e≤ (T-Pair p/s s⇒p x′ y′)
⊢⋯⁻¹ {e = `let e₁ `in e₂} {ϕ = ρ} inj p ⊢ϕ =
  let p/s , γ₁ , γ₂ , T , ≤ , x , y = inv-`let p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂b , ≼₂ , y′ = ⊢⋯⁻¹ {e = e₂} {ϕ = ρ ↑ᵣ} (↑-inj inj) y (⊢↑ ⊢ϕ)
      ≼₂ᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑ ⊢ϕ γ₂b)) ≼₂
      γr , p1 , p2 = descend-abs inj (⊢ren-ϕ⇔ ⊢ϕ) p/s γ₂ γ₂b ≼₂ᵣ
      out≼ = subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ p/s γ₁′ γr))
               (≼-trans (≼-join p/s ≼₁ (subst (λ z → _ ∶ z ≼ γ₂) (brₛ ⊢ϕ γr) p2)) ≤)
  in join p/s γ₁′ γr , out≼ , T-Let p/s x′ (T-Weaken p1 y′)
⊢⋯⁻¹ {Γ₂ = Γ₂} {e = `let⊗ e₁ `in e₂} {ϕ = ρ} inj p ⊢ϕ =
  let p/s , d , γ₁ , γ₂ , T₁ , T₂ , ≤ , x , y = inv-`let⊗ p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γbb , ≼₂ , y′ = ⊢⋯⁻¹ {e = e₂} {ϕ = ρ ↑ᵣ ↑ᵣ}
                        (↑-inj (↑-inj inj)) y (⊢↑ (⊢↑ ⊢ϕ))
      ≼₂ᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑↑ ⊢ϕ γbb)) ≼₂
      γr , p1 , p2 = descend-abs² inj (⊢ren-ϕ⇔ ⊢ϕ) p/s
                       γ₂
                       (join d (` zero) (` suc zero))
                       γbb
                       (⊆-reflexive (cong dom (join-⋯ d (` zero) (` suc zero)) ■ dom-join d (` zero) (` suc zero)))
                       (subst₂ (T₁ ∷ T₂ ∷ Γ₂ ∶_≼_) refl (cong₂ (join p/s) (sym (join-⋯ d (` zero) (` suc zero))) refl) ≼₂ᵣ)
      out≼ = subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ p/s γ₁′ γr))
               (≼-trans (≼-join p/s ≼₁ (subst (λ z → _ ∶ z ≼ γ₂) (brₛ ⊢ϕ γr) p2)) ≤)
  in join p/s γ₁′ γr , out≼ , T-LetPair p/s x′ (T-Weaken p1 y′)
⊢⋯⁻¹ {e = `inj i e} inj p ⊢ϕ =
  let T , U , ty≃ , d = inv-inj p
      γ′ , ≼₀ , d′ = ⊢⋯⁻¹ inj d ⊢ϕ
  in γ′ , ≼₀ , T-Conv ty≃ ≤ϵ-refl (T-Inj d′)
⊢⋯⁻¹ {e = `case e `of⟨ e₁ ; e₂ ⟩} {ϕ = ρ} inj p ⊢ϕ =
  let p/s , γ₁ , γ₂ , T₁ , T₂ , ≤ , de , d₁ , d₂ = inv-`case p
      γ₁′ , ≼₁ , e′ = ⊢⋯⁻¹ inj de ⊢ϕ
      γₐ , ≼ₐ , pe₁ = ⊢⋯⁻¹ {e = e₁} {ϕ = ρ ↑ᵣ} (↑-inj inj) d₁ (⊢↑ ⊢ϕ)
      γᵦ , ≼ᵦ , pe₂ = ⊢⋯⁻¹ {e = e₂} {ϕ = ρ ↑ᵣ} (↑-inj inj) d₂ (⊢↑ ⊢ϕ)
      ≼ₐᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑ ⊢ϕ γₐ)) ≼ₐ
      ≼ᵦᵣ = subst (λ z → _ ∶ z ≼ _) (sym (brₛ↑ ⊢ϕ γᵦ)) ≼ᵦ
      Ximg : ∀ {sy} → sy ∈ (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) → sy ∈img ρ 𝐂.↑ᵣ
      Ximg {sy} sy∈ = [ 𝐂.∈dom⋯⇒∈img γₐ {ρ 𝐂.↑ᵣ} , 𝐂.∈dom⋯⇒∈img γᵦ {ρ 𝐂.↑ᵣ} ]′
                        (x∈p∪q⁻ (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) (dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) sy∈)
      γr , p1ₐ , p2 = descend-abs-⊆ inj (⊢ren-ϕ⇔ ⊢ϕ) p/s γ₂ γₐ
                        (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) Ximg (p⊆p∪q _) ≼ₐᵣ
      _ , p1ᵦ , _ = descend-abs-⊆ inj (⊢ren-ϕ⇔ ⊢ϕ) p/s γ₂ γᵦ
                        (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) Ximg (q⊆p∪q _ _) ≼ᵦᵣ
      out≼ = subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ p/s γ₁′ γr))
               (≼-trans (≼-join p/s ≼₁ (subst (λ z → _ ∶ z ≼ γ₂) (brₛ ⊢ϕ γr) p2)) ≤)
  in join p/s γ₁′ γr , out≼ , T-Case p/s e′ (T-Weaken p1ₐ pe₁) (T-Weaken p1ᵦ pe₂)

infixl 5 _⊢⋯⁻¹_/_

_⊢⋯⁻¹_/_ : ∀ {m n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {γ} {e} {T : 𝕋} {ϵ} {ϕ : m →ᵣ n} {σ} →
  Γ₂ ; γ ⊢ e ⋯ ϕ ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → 𝐂.Inj ϕ →
  ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ e ∶ T ∣ ϵ
e ⊢⋯⁻¹ ⊢ϕ / ϕ-inj = ⊢⋯⁻¹ ϕ-inj e ⊢ϕ
