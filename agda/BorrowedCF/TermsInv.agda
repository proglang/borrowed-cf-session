module BorrowedCF.TermsInv where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context
import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms hiding (_⊢⋯⁻¹_)
import BorrowedCF.Context.Base as CB
open import BorrowedCF.DescendAbs
open import Data.Fin.Subset using (Subset; ∁; _∈_; ⁅_⁆; _∪_) renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties using (x∈p⇒x∉∁p; x∉∁p⇒x∈p; x∈∁p⇒x∉p; _∈?_; x∈⁅x⁆; ⊆-trans; ⊆-refl; ∪-identityʳ; p⊆p∪q; q⊆p∪q; x∈⁅y⁆⇒x≡y; x∈p∪q⁻)
import Data.Vec as Vec
open import Data.Vec using (_∷_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (not)
open import Relation.Nullary using (yes; no)

open Nat.Variables

Inj-↑ᵣ : {ρ : m →ᵣ n} → 𝐂.Inj ρ → 𝐂.Inj (ρ ↑ᵣ)
Inj-↑ᵣ inj {fzero}  {fzero}  eq = refl
Inj-↑ᵣ inj {fzero}  {fsuc y} ()
Inj-↑ᵣ inj {fsuc x} {fzero}  ()
Inj-↑ᵣ inj {fsuc x} {fsuc y} eq = cong fsuc (inj (suc-injective eq))

inv-ƛ : ∀ {n} {Γ : Ctx n} {γ e} {U : 𝕋} {ϵ} → Γ ; γ ⊢ ƛ e ∶ U ∣ ϵ → ∃[ a ] ∃[ Ta ] ∃[ Ua ] ∃[ γ₀ ]
  (U ≃ Ta ⟨ a ⟩→ Ua) × Γ ∶ γ₀ ≼ γ
  × (Arr.Unr a → UnrCx Γ γ₀) × (Arr.Mobile a → MobCx Γ γ₀)
  × (Ta ⸴ Γ ; join (Arr.dir a) (CB.`_ zero) (𝐂.wk γ₀) ⊢ e ∶ Ua ∣ Arr.eff a)
inv-ƛ (T-Abs Γ-unr Γ-mob d) =
  _ , _ , _ , _ , ≃-refl , ≼-refl refl , Γ-unr , Γ-mob , d
inv-ƛ (T-Conv U≃ ϵ≤ x) =
  let a , Ta , Ua , γ₀ , arr≃ , ≤ , u , mo , d = inv-ƛ x in
  a , Ta , Ua , γ₀ , ≃-trans (≃-sym U≃) arr≃ , ≤ , u , mo , d
inv-ƛ (T-Weaken γ≤ x) =
  let a , Ta , Ua , γ₀ , arr≃ , ≤ , u , mo , d = inv-ƛ x in
  a , Ta , Ua , γ₀ , arr≃ , ≼-trans ≤ γ≤ , u , mo , d


inv-⊗ : ∀ {n} {Γ : Ctx n} {γ} {e₁ e₂} {V : 𝕋} {ϵ} → Γ ; γ ⊢ e₁ ⊗ e₂ ∶ V ∣ ϵ →
  ∃[ p/s ] ∃[ T ] ∃[ U ] ∃[ γ₁ ] ∃[ γ₂ ] ∃[ ϵ₁ ] ∃[ ϵ₂ ]
    (V ≃ T ⊗⟨ biasedDir p/s ⟩ U) × (ϵ₁ ≤ϵ ϵ)
    × Γ ∶ join (biasedDir p/s) γ₁ γ₂ ≼ γ × Seq⇒Pure p/s ϵ₁ ϵ₂
    × (Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁) × (Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂)
inv-⊗ (T-Pair p/s s⇒p x y) = p/s , _ , _ , _ , _ , _ , _ , ≃-refl , ≤ϵ-refl , ≼-refl refl , s⇒p , x , y
inv-⊗ (T-Conv V≃ ϵ≤ x) =
  let p/s , T , U , γ₁ , γ₂ , ϵ₁ , ϵ₂ , ty≃ , e≤ , ≤ , s⇒p , d₁ , d₂ = inv-⊗ x in
  p/s , T , U , γ₁ , γ₂ , ϵ₁ , ϵ₂ , ≃-trans (≃-sym V≃) ty≃ , ≤ϵ-trans e≤ ϵ≤ , ≤ , s⇒p , d₁ , d₂
inv-⊗ (T-Weaken γ≤ x) =
  let p/s , T , U , γ₁ , γ₂ , ϵ₁ , ϵ₂ , ty≃ , e≤ , ≤ , s⇒p , d₁ , d₂ = inv-⊗ x in
  p/s , T , U , γ₁ , γ₂ , ϵ₁ , ϵ₂ , ty≃ , e≤ , ≼-trans ≤ γ≤ , s⇒p , d₁ , d₂

inv-seq : ∀ {n} {Γ : Ctx n} {γ} {e₁ e₂} {V : 𝕋} {ϵ} → Γ ; γ ⊢ e₁ ; e₂ ∶ V ∣ ϵ →
  ∃[ T ] ∃[ U ] ∃[ γ₁ ] ∃[ γ₂ ] ∃[ ϵ₀ ]
    Unr T × (U ≃ V) × (ϵ₀ ≤ϵ ϵ) × Γ ∶ γ₁ ; γ₂ ≼ γ
    × (Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₀) × (Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₀)
inv-seq (T-Seq uT x y) = _ , _ , _ , _ , _ , uT , ≃-refl , ≤ϵ-refl , ≼-refl refl , x , y
inv-seq (T-Conv V≃ ϵ≤ x) =
  let T , U , γ₁ , γ₂ , ϵ₀ , uT , U≃ , e≤ , ≤ , d₁ , d₂ = inv-seq x in
  T , U , γ₁ , γ₂ , ϵ₀ , uT , ≃-trans U≃ V≃ , ≤ϵ-trans e≤ ϵ≤ , ≤ , d₁ , d₂
inv-seq (T-Weaken γ≤ x) =
  let T , U , γ₁ , γ₂ , ϵ₀ , uT , U≃ , e≤ , ≤ , d₁ , d₂ = inv-seq x in
  T , U , γ₁ , γ₂ , ϵ₀ , uT , U≃ , e≤ , ≼-trans ≤ γ≤ , d₁ , d₂

inv-inj : ∀ {n} {Γ : Ctx n} {γ} {i} {e} {V : 𝕋} {ϵ} → Γ ; γ ⊢ `inj i e ∶ V ∣ ϵ →
  ∃[ T ] ∃[ U ] ∃[ γ₀ ] (V ≃ T ⊕ U) × Γ ∶ γ₀ ≼ γ × (Γ ; γ₀ ⊢ e ∶ (if i then T else U) ∣ ϵ)
inv-inj (T-Inj x) = _ , _ , _ , ≃-refl , ≼-refl refl , x
inv-inj (T-Conv V≃ ϵ≤ x) =
  let T , U , γ₀ , ty≃ , ≤ , d = inv-inj x in
  T , U , γ₀ , ≃-trans (≃-sym V≃) ty≃ , ≤ , T-Conv ≃-refl ϵ≤ d
inv-inj (T-Weaken γ≤ x) =
  let T , U , γ₀ , ty≃ , ≤ , d = inv-inj x in
  T , U , γ₀ , ty≃ , ≼-trans ≤ γ≤ , d

inv-let : ∀ {n} {Γ : Ctx n} {γ} {e₁ e₂} {V : 𝕋} {ϵ} → Γ ; γ ⊢ `let e₁ `in e₂ ∶ V ∣ ϵ →
  ∃[ p/s ] ∃[ T ] ∃[ U ] ∃[ γ₁ ] ∃[ γ₂ ] ∃[ ϵ₀ ]
    (U ≃ V) × (ϵ₀ ≤ϵ ϵ) × Γ ∶ join p/s γ₁ γ₂ ≼ γ
    × (Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₀)
    × (T ⸴ Γ ; join p/s (CB.`_ zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ₀)
inv-let (T-Let p/s x y) = p/s , _ , _ , _ , _ , _ , ≃-refl , ≤ϵ-refl , ≼-refl refl , x , y
inv-let (T-Conv V≃ ϵ≤ x) =
  let p/s , T , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , d₁ , d₂ = inv-let x in
  p/s , T , U , γ₁ , γ₂ , ϵ₀ , ≃-trans U≃ V≃ , ≤ϵ-trans e≤ ϵ≤ , ≤ , d₁ , d₂
inv-let (T-Weaken γ≤ x) =
  let p/s , T , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , d₁ , d₂ = inv-let x in
  p/s , T , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≼-trans ≤ γ≤ , d₁ , d₂

inv-case : ∀ {n} {Γ : Ctx n} {γ} {e e₁ e₂} {V : 𝕋} {ϵ} → Γ ; γ ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ∶ V ∣ ϵ →
  ∃[ p/s ] ∃[ T₁ ] ∃[ T₂ ] ∃[ U ] ∃[ γ₁ ] ∃[ γ₂ ] ∃[ ϵ₀ ]
    (U ≃ V) × (ϵ₀ ≤ϵ ϵ) × Γ ∶ join p/s γ₁ γ₂ ≼ γ
    × (Γ ; γ₁ ⊢ e ∶ T₁ ⊕ T₂ ∣ ϵ₀)
    × (T₁ ⸴ Γ ; join p/s (CB.`_ zero) (𝐂.wk γ₂) ⊢ e₁ ∶ U ∣ ϵ₀)
    × (T₂ ⸴ Γ ; join p/s (CB.`_ zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ₀)
inv-case (T-Case p/s de d₁ d₂) = p/s , _ , _ , _ , _ , _ , _ , ≃-refl , ≤ϵ-refl , ≼-refl refl , de , d₁ , d₂
inv-case (T-Conv V≃ ϵ≤ x) =
  let p/s , T₁ , T₂ , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , de , d₁ , d₂ = inv-case x in
  p/s , T₁ , T₂ , U , γ₁ , γ₂ , ϵ₀ , ≃-trans U≃ V≃ , ≤ϵ-trans e≤ ϵ≤ , ≤ , de , d₁ , d₂
inv-case (T-Weaken γ≤ x) =
  let p/s , T₁ , T₂ , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , de , d₁ , d₂ = inv-case x in
  p/s , T₁ , T₂ , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≼-trans ≤ γ≤ , de , d₁ , d₂

μ-ƛ : ∀ {n} {Γ : Ctx n} {γ} {b} {V : 𝕋} {ϵ} → Γ ; γ ⊢ μ b ∶ V ∣ ϵ → ∃[ b′ ] b ≡ ƛ b′
μ-ƛ (T-AbsRec _ _ _) = _ , refl
μ-ƛ (T-Conv _ _ x) = μ-ƛ x
μ-ƛ (T-Weaken _ x) = μ-ƛ x

inv-μ : ∀ {n} {Γ : Ctx n} {γ e} {V : 𝕋} {ϵ} → Γ ; γ ⊢ μ (ƛ e) ∶ V ∣ ϵ →
  ∃[ a ] ∃[ T ] ∃[ U ] ∃[ γ₀ ]
    (V ≃ T ⟨ a ⟩→ U) × Arr.Unr a × Γ ∶ γ₀ ≼ γ × UnrCx Γ γ₀
    × (T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (CB.`_ fzero) ∥ (CB.`_ (fsuc fzero)) ∥ 𝐂.wk (𝐂.wk γ₀) ⊢ e ∶ U ∣ Arr.eff a)
inv-μ (T-AbsRec Γ-unr a-unr d) = _ , _ , _ , _ , ≃-refl , a-unr , ≼-refl refl , Γ-unr , d
inv-μ (T-Conv V≃ ϵ≤ x) =
  let a , T , U , γ₀ , arr≃ , au , ≤ , uc , d = inv-μ x in
  a , T , U , γ₀ , ≃-trans (≃-sym V≃) arr≃ , au , ≤ , uc , d
inv-μ (T-Weaken γ≤ x) =
  let a , T , U , γ₀ , arr≃ , au , ≤ , uc , d = inv-μ x in
  a , T , U , γ₀ , arr≃ , au , ≼-trans ≤ γ≤ , uc , d

σ≗ϕ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → σ ≗ (λ x → ` (ϕ x))
σ≗ϕ ⊢ϕ x = proj₁ (⊢ϕ & x)

brₛ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct m) → γ 𝐂.⋯ σ ≡ γ 𝐂.⋯ ϕ
brₛ ⊢ϕ γ = 𝐂.⋯-cong γ (σ≗ϕ ⊢ϕ) ■ 𝐂.conv-⋯ᵣₛ γ

ϕ-any⇐ : ∀ {ℓ} {P : Pred 𝕋 ℓ} {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → ϕ 𝐂.Preserves[ P ] Γ₁ ⇐ Γ₂
ϕ-any⇐ {P = P} ⊢ϕ {x} (` px) = subst P (proj₂ (⊢ϕ & x)) px

lift-disg : {ρ : m →ᵣ n} {σ : m 𝐂.→ₛ n} →
  σ ≗ (λ x → CB.`_ (ρ x)) → (σ 𝐂.↑ₛ) ≗ (λ x → CB.`_ ((ρ 𝐂.↑ᵣ) x))
lift-disg eq fzero    = refl
lift-disg eq (fsuc y) = cong (𝐂._⋯ᵣ 𝐂.weakenᵣ) (eq y)

brₛ↑ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (suc m)) → γ 𝐂.⋯ (σ 𝐂.↑ₛ) ≡ γ 𝐂.⋯ᵣ (ϕ 𝐂.↑ᵣ)
brₛ↑ ⊢ϕ γ = 𝐂.⋯-cong γ (lift-disg (σ≗ϕ ⊢ϕ)) ■ 𝐂.conv-⋯ᵣₛ γ

brₛ↑↑ : {ϕ : m →ᵣ n} {σ : _} {Γ₁ : Ctx m} {Γ₂ : Ctx n} →
  ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ → (γ : Struct (suc (suc m))) →
  γ 𝐂.⋯ (σ 𝐂.↑ₛ 𝐂.↑ₛ) ≡ γ 𝐂.⋯ᵣ (ϕ 𝐂.↑ᵣ 𝐂.↑ᵣ)
brₛ↑↑ ⊢ϕ γ = 𝐂.⋯-cong γ (lift-disg (lift-disg (σ≗ϕ ⊢ϕ))) ■ 𝐂.conv-⋯ᵣₛ γ

⊢⋯⁻¹ : ∀ {m n} {Γ₁ : Ctx m} {Γ₂ : Ctx n} {γ} {e} {T : 𝕋} {ϵ} {ϕ : m →ᵣ n} {σ} →
  𝐂.Inj ϕ → Γ₂ ; γ ⊢ e ⋯ ϕ ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ e ∶ T ∣ ϵ
⊢⋯⁻¹ {e = ` x} inj p ⊢ϕ =
  let T≃ , ≼γ = inv-` p in
  _ , ≼-respˡ-≈ (≈-reflexive (sym (proj₁ (⊢ϕ & x)))) ≼γ
    , T-Conv (≃-trans (≃-reflexive (sym (proj₂ (⊢ϕ & x)))) (≃-sym T≃)) ℙ≤ϵ (T-Var _ refl)
⊢⋯⁻¹ {e = K c} inj p ⊢ϕ =
  let _ , T≃ , ≼γ , ⊢c = inv-K p in
  _ , ≼γ , T-Conv T≃ ℙ≤ϵ (T-Const ⊢c)
⊢⋯⁻¹ {e = ƛ e} {ϕ = ρ} inj p ⊢ϕ =
  let a , Ta , Ua , γa , T≃ , γa≼γ , uc , mc , d = inv-ƛ p
      γb′ , ≼b , pb = ⊢⋯⁻¹ {e = e} {T = Ua} {ϵ = Arr.eff a} {ϕ = ρ ↑ᵣ} (Inj-↑ᵣ inj) d (⊢↑ ⊢ϕ)
      ≼bᵣ = subst (λ z → _ ∶ z ≼ _) (brₛ↑ ⊢ϕ γb′) ≼b
      γr , p1 , p2 = descend-abs inj (ϕ-any⇐ ⊢ϕ) (Arr.dir a) γb′ γa ≼bᵣ
      out≼ = ≼-trans (subst (λ z → _ ∶ z ≼ γa) (sym (brₛ ⊢ϕ γr)) p2) γa≼γ
      uc′ = λ ua → 𝐂.allCx-⋯⁻¹ (ϕ-any⇐ ⊢ϕ) (allCx-strengthen p2 (uc ua))
      mc′ = λ ma → 𝐂.allCx-⋯⁻¹ (ϕ-any⇐ ⊢ϕ) (allCx-strengthen p2 (mc ma))
  in γr , out≼ , T-Conv (≃-sym T≃) ℙ≤ϵ (T-Abs uc′ mc′ (T-Weaken p1 pb))
⊢⋯⁻¹ {e = μ (ƛ e)} {ϕ = ρ} inj p ⊢ϕ =
  let a , T , U , γ₀ , V≃ , a-unr , γ₀≼γ , uc , d = inv-μ p
      γbb , ≼bb , pbb = ⊢⋯⁻¹ {e = e} {T = U} {ϵ = Arr.eff a} {ϕ = ρ ↑ᵣ ↑ᵣ}
                          (Inj-↑ᵣ (Inj-↑ᵣ inj)) d (⊢↑ (⊢↑ ⊢ϕ))
      ≼bbᵣ = subst (λ z → _ ∶ z ≼ _) (brₛ↑↑ ⊢ϕ γbb) ≼bb
      γr , p1 , p2 = descend-abs2 inj (ϕ-any⇐ ⊢ϕ) 𝟙
                       ((CB.`_ fzero) ∥ (CB.`_ (fsuc fzero))) ((CB.`_ fzero) ∥ (CB.`_ (fsuc fzero)))
                       γbb γ₀ refl ⊆-refl ≼bbᵣ
      out≼ = ≼-trans (subst (λ z → _ ∶ z ≼ γ₀) (sym (brₛ ⊢ϕ γr)) p2) γ₀≼γ
      uc′ = 𝐂.allCx-⋯⁻¹ (ϕ-any⇐ ⊢ϕ) (allCx-strengthen p2 uc)
  in γr , out≼ , T-Conv (≃-sym V≃) ℙ≤ϵ (T-AbsRec uc′ a-unr (T-Weaken p1 pbb))
⊢⋯⁻¹ {e = μ (` x)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (K c)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (μ e)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (e₁ · e₂)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (e₁ ; e₂)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (e₁ ⊗ e₂)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (`let e₁ `in e₂)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (`let⊗ e₁ `in e₂)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (`inj i e)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = μ (`case e `of⟨ e₁ ; e₂ ⟩)} inj p ⊢ϕ with μ-ƛ p
... | _ , ()
⊢⋯⁻¹ {e = e₁ · e₂} inj p ⊢ϕ with inv-· p
... | a , α , β , _ , ≤γ , eff≤ , T-AppUnr a-unr x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ d → _ ∶ join d β α ≼ _) (Arr.ω⇒𝟙 a a-unr) ≤γ
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≼α ≼β) (≼-trans (≼-refl ∥-comm) jeq) , T-AppUnr a-unr eff≤ x′ y′
... | a , α , β , _ , ≤γ , eff≤ , T-AppLin a-par x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ d → _ ∶ join d β α ≼ _) a-par ≤γ
  in α′ ∥ β′ , ≼-trans (≼-cong-∥ ≼α ≼β) (≼-trans (≼-refl ∥-comm) jeq) , T-AppLin a-par eff≤ x′ y′
... | a , α , β , _ , ≤γ , eff≤ , T-AppLeft aL x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ d → _ ∶ join d β α ≼ _) aL ≤γ
  in β′ ; α′ , ≼-trans (≼-cong-; ≼β ≼α) jeq , T-AppLeft aL eff≤ x′ y′
... | a , α , β , _ , ≤γ , eff≤ , T-AppRight aR x y =
  let α′ , ≼α , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      β′ , ≼β , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
      jeq = subst (λ d → _ ∶ join d β α ≼ _) aR ≤γ
  in α′ ; β′ , ≼-trans (≼-cong-; ≼α ≼β) jeq , T-AppRight aR eff≤ x′ y′
⊢⋯⁻¹ {e = e₁ ; e₂} inj p ⊢ϕ =
  let T , U , γ₁ , γ₂ , ϵ₀ , uT , U≃ , e≤ , ≤ , x , y = inv-seq p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂′ , ≼₂ , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
  in γ₁′ ; γ₂′ , ≼-trans (≼-cong-; ≼₁ ≼₂) ≤ , T-Conv U≃ e≤ (T-Seq uT x′ y′)
⊢⋯⁻¹ {e = e₁ ⊗ e₂} inj p ⊢ϕ =
  let p/s , T , U , γ₁ , γ₂ , ϵ₁ , ϵ₂ , ty≃ , e≤ , ≤ , s⇒p , x , y = inv-⊗ p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂′ , ≼₂ , y′ = ⊢⋯⁻¹ inj y ⊢ϕ
  in join (biasedDir p/s) γ₁′ γ₂′
   , subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ (biasedDir p/s) γ₁′ γ₂′)) (≼-trans (≼-join (biasedDir p/s) ≼₁ ≼₂) ≤)
   , T-Conv (≃-sym ty≃) e≤ (T-Pair p/s s⇒p x′ y′)
⊢⋯⁻¹ {e = `let e₁ `in e₂} {ϕ = ρ} inj p ⊢ϕ =
  let p/s , T , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , x , y = inv-let p
      γ₁′ , ≼₁ , x′ = ⊢⋯⁻¹ inj x ⊢ϕ
      γ₂b , ≼₂ , y′ = ⊢⋯⁻¹ {e = e₂} {T = U} {ϵ = ϵ₀} {ϕ = ρ ↑ᵣ} (Inj-↑ᵣ inj) y (⊢↑ ⊢ϕ)
      ≼₂ᵣ = subst (λ z → _ ∶ z ≼ _) (brₛ↑ ⊢ϕ γ₂b) ≼₂
      γr , p1 , p2 = descend-abs inj (ϕ-any⇐ ⊢ϕ) p/s γ₂b γ₂ ≼₂ᵣ
      out≼ = subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ p/s γ₁′ γr))
               (≼-trans (≼-join p/s ≼₁ (subst (λ z → _ ∶ z ≼ γ₂) (sym (brₛ ⊢ϕ γr)) p2)) ≤)
  in join p/s γ₁′ γr , out≼ , T-Conv U≃ e≤ (T-Let p/s x′ (T-Weaken p1 y′))
⊢⋯⁻¹ {e = `let⊗ e₁ `in e₂} inj p ⊢ϕ = {!!}
⊢⋯⁻¹ {e = `inj i e} inj p ⊢ϕ =
  let T , U , γ₀ , ty≃ , ≤ , d = inv-inj p
      γ′ , ≼₀ , d′ = ⊢⋯⁻¹ inj d ⊢ϕ
  in γ′ , ≼-trans ≼₀ ≤ , T-Conv (≃-sym ty≃) ≤ϵ-refl (T-Inj d′)
⊢⋯⁻¹ {e = `case e `of⟨ e₁ ; e₂ ⟩} {ϕ = ρ} inj p ⊢ϕ =
  let p/s , T₁ , T₂ , U , γ₁ , γ₂ , ϵ₀ , U≃ , e≤ , ≤ , de , d₁ , d₂ = inv-case p
      γ₁′ , ≼₁ , e′ = ⊢⋯⁻¹ inj de ⊢ϕ
      γₐ , ≼ₐ , pe₁ = ⊢⋯⁻¹ {e = e₁} {T = U} {ϵ = ϵ₀} {ϕ = ρ ↑ᵣ} (Inj-↑ᵣ inj) d₁ (⊢↑ ⊢ϕ)
      γᵦ , ≼ᵦ , pe₂ = ⊢⋯⁻¹ {e = e₂} {T = U} {ϵ = ϵ₀} {ϕ = ρ ↑ᵣ} (Inj-↑ᵣ inj) d₂ (⊢↑ ⊢ϕ)
      ≼ₐᵣ = subst (λ z → _ ∶ z ≼ _) (brₛ↑ ⊢ϕ γₐ) ≼ₐ
      ≼ᵦᵣ = subst (λ z → _ ∶ z ≼ _) (brₛ↑ ⊢ϕ γᵦ) ≼ᵦ
      Ximg : ∀ {sy} → sy ∈ (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) → InImage (ρ 𝐂.↑ᵣ) sy
      Ximg {sy} sy∈ = [ dom-⋯-InImage γₐ {ρ 𝐂.↑ᵣ} , dom-⋯-InImage γᵦ {ρ 𝐂.↑ᵣ} ]′
                        (x∈p∪q⁻ (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) (dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) sy∈)
      γr , p1ₐ , p2 = descend-absX inj (ϕ-any⇐ ⊢ϕ) p/s γₐ γ₂
                        (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) Ximg (p⊆p∪q _) ≼ₐᵣ
      _ , p1ᵦ , _ = descend-absX inj (ϕ-any⇐ ⊢ϕ) p/s γᵦ γ₂
                        (dom (γₐ 𝐂.⋯ (ρ 𝐂.↑ᵣ)) ∪ dom (γᵦ 𝐂.⋯ (ρ 𝐂.↑ᵣ))) Ximg (q⊆p∪q _ _) ≼ᵦᵣ
      out≼ = subst (λ z → _ ∶ z ≼ _) (sym (join-⋯ p/s γ₁′ γr))
               (≼-trans (≼-join p/s ≼₁ (subst (λ z → _ ∶ z ≼ γ₂) (sym (brₛ ⊢ϕ γr)) p2)) ≤)
  in join p/s γ₁′ γr , out≼
   , T-Conv U≃ e≤ (T-Case p/s e′ (T-Weaken p1ₐ pe₁) (T-Weaken p1ᵦ pe₂))


fvClose : Subset (suc n) → Subset n
fvClose = Vec.tail

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


wk↓∁ : (γ : Struct m) (T₀ : Subset (suc m)) → 𝐂.wk γ ↓ ∁ T₀ ≡ 𝐂.wk (γ ↓ ∁ (fvClose T₀))
wk↓∁ γ (b ∷ T₀) = ↓-dist-wk γ

⊢⇒∁fv-Unr : ∀ {n} {Γ : Ctx n} {γ} {e} {T : 𝕋} {ϵ} →
  Γ ; γ ⊢ e ∶ T ∣ ϵ → AllCx Unr Γ (γ ↓ ∁ (fv e))
⊢⇒∁fv-Unr (T-Const ⊢c) = []
⊢⇒∁fv-Unr {Γ = Γ} (T-Var x refl) with x ∈? ∁ ⁅ x ⁆
... | yes x∈∁ = contradiction (x∈⁅x⁆ x) (x∈∁p⇒x∉p x∈∁)
... | no  _   = []
⊢⇒∁fv-Unr (T-Conv T≃ ϵ≤ d) = ⊢⇒∁fv-Unr d
⊢⇒∁fv-Unr (T-Weaken γ≤ d) = allCx-weaken (λ u → u) (↓-mono-≼ γ≤) (⊢⇒∁fv-Unr d)
⊢⇒∁fv-Unr {e = ƛ e} (T-Abs {a = a} {γ = γ} Γ-unr Γ-mob d) =
  un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ (fv e))
              (allCx-join↓-proj₂ (Arr.dir a) (∁ (fv e)) (⊢⇒∁fv-Unr d)))
⊢⇒∁fv-Unr {e = μ (ƛ e)} (T-AbsRec {γ = γ} Γ-unr a-unr d) with ⊢⇒∁fv-Unr d
... | (_ ∥ _) ∥ w =
  un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ (fvClose (fv e)))
    (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ (𝐂.wk γ) (fv e)) w)))
⊢⇒∁fv-Unr (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} a-unr ≤ₐ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} a-par ≤ₐ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} aL ≤ₐ d₁ d₂) =
  ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂) ; ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁)
⊢⇒∁fv-Unr (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} aR ≤ₐ d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ; ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr (T-Pair par {γ₁ = γ₁} {γ₂ = γ₂} s⇒p d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr (T-Pair seq {γ₁ = γ₁} {γ₂ = γ₂} s⇒p d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ; ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr {e = `let e₁ `in e₂} (T-Let par {γ₁ = γ₁} {γ₂ = γ₂} d₁ d₂) with ⊢⇒∁fv-Unr d₂
... | _ ∥ w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁)
  ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fv e₂)) w))
⊢⇒∁fv-Unr {e = `let e₁ `in e₂} (T-Let seq {γ₁ = γ₁} {γ₂ = γ₂} d₁ d₂) with ⊢⇒∁fv-Unr d₂
... | _ ; w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁)
  ; ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fv e₂)) w))
⊢⇒∁fv-Unr (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} uT d₁ d₂) =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁) ; ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (⊢⇒∁fv-Unr d₂)
⊢⇒∁fv-Unr {e = `let⊗ e₁ `in e₂} (T-LetPair par {γ₁ = γ₁} {γ₂ = γ₂} d₁ d₂) with ⊢⇒∁fv-Unr d₂
... | _ ∥ w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁)
  ∥ ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fvClose (fv e₂)))
      (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ (𝐂.wk γ₂) (fv e₂)) w))))
⊢⇒∁fv-Unr {e = `let⊗ e₁ `in e₂} (T-LetPair seq {γ₁ = γ₁} {γ₂ = γ₂} d₁ d₂) with ⊢⇒∁fv-Unr d₂
... | _ ; w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d₁)
  ; ↓-⊆ γ₂ (∁-∪-⊆ʳ _ _) (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fvClose (fv e₂)))
      (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ (𝐂.wk γ₂) (fv e₂)) w))))
⊢⇒∁fv-Unr (T-Inj d) = ⊢⇒∁fv-Unr d
⊢⇒∁fv-Unr {e = `case e `of⟨ e₁ ; e₂ ⟩} (T-Case par {γ₁ = γ₁} {γ₂ = γ₂} d d₁ d₂) with ⊢⇒∁fv-Unr d₁
... | _ ∥ w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d)
  ∥ ↓-⊆ γ₂ (⊆-trans (∁-∪-⊆ʳ _ _) (∁-∪-⊆ˡ _ _))
      (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fv e₁)) w))
⊢⇒∁fv-Unr {e = `case e `of⟨ e₁ ; e₂ ⟩} (T-Case seq {γ₁ = γ₁} {γ₂ = γ₂} d d₁ d₂) with ⊢⇒∁fv-Unr d₁
... | _ ; w =
  ↓-⊆ γ₁ (∁-∪-⊆ˡ _ _) (⊢⇒∁fv-Unr d)
  ; ↓-⊆ γ₂ (⊆-trans (∁-∪-⊆ʳ _ _) (∁-∪-⊆ˡ _ _))
      (un-wk-Unr (subst (AllCx Unr _) (wk↓∁ γ₂ (fv e₁)) w))
