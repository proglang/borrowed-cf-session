module BorrowedCF.Simulation2.InvFrame where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types using (𝕋; 𝕊; Eff; Unr; Arr; Dir; Skips; _≃_; ≃-refl; ≃-sym; ≃-trans; unr-≃; _`→_; ⟨_⟩; _;_; _⟨_⟩→_)
open import BorrowedCF.Context.Base using (Struct; Ctx; ParSeq; _⸴_; `_)
open import BorrowedCF.Context.Domain using (dom)
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Simulation2.Confine
open import BorrowedCF.Simulation2.HandleLinear using (¬Skips⇒¬Unr-seq)
open import BorrowedCF.Context.Join using (biasedDir; join)
import BorrowedCF.Context.Substitution as 𝐂S
open import BorrowedCF.Simulation2.Strengthen using (Inverter; inv↑; strengthen-Tm-gen)
open import Data.Fin.Subset using (_∉_)

open Nat.Variables
open Nat using (_≤_; ≤-refl; ≤-reflexive; ≤-trans; +-comm; +-identityʳ; +-cancelˡ-≤; ≤-antisym; z≤n; m≤m+n; m≤n+m)

-- A renaming cannot create a value: if `e ⋯ ρ` is a value, so is `e`.
value-reflect : ∀ {m n} (ρ : m →ᵣ n) (e : Tm m) → Value (e ⋯ ρ) → Value e
value-reflect ρ (` x)        _          = V-`
value-reflect ρ (K c)        _          = V-K
value-reflect ρ (ƛ e)        _          = V-λ
value-reflect ρ (e₁ ⊗ e₂) (V-⊗ V₁ V₂) = V-⊗ (value-reflect ρ e₁ V₁) (value-reflect ρ e₂ V₂)
value-reflect ρ (`inj i e) (V-⊕ V) = V-⊕ (value-reflect ρ e V)

-- a + b ≤ a forces b ≡ 0.
+≤ˡ⇒0 : ∀ a {b} → a + b ≤ a → b ≡ 0
+≤ˡ⇒0 a {b} le = ≤-antisym (+-cancelˡ-≤ a b 0 (subst (a + b ≤_) (sym (+-identityʳ a)) le)) z≤n

-- Inversion of an application typing (peeling Conv / Weaken); returns both
-- operand typings and the count-superadditivity of the result context.
inv-app : ∀ {N} {Γ : Ctx N} {α : Struct N} {e₁ e₂ : Tm N} {T ϵ}
  → Γ ; α ⊢ e₁ · e₂ ∶ T ∣ ϵ
  → Σ[ α₁ ∈ Struct N ] Σ[ α₂ ∈ Struct N ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; α₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
      × (∃[ T₂ ] ∃[ ϵ₂ ] Γ ; α₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h α₁ + count h α₂ ≤ count h α)
inv-app (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , λ h _ → ≤-refl
inv-app (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , λ h _ → ≤-refl
inv-app (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , λ h _ → ≤-reflexive (+-comm (count h γ₁) (count h γ₂))
inv-app (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , λ h _ → ≤-refl
inv-app (T-Conv _ _ d) = inv-app d
inv-app (T-Weaken γ≤ d) =
  let α₁ , α₂ , p , q , cle = inv-app d
  in α₁ , α₂ , p , q , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

inv-pair : ∀ {N} {Γ : Ctx N} {α : Struct N} {e₁ e₂ : Tm N} {T ϵ}
  → Γ ; α ⊢ e₁ ⊗ e₂ ∶ T ∣ ϵ
  → Σ[ α₁ ∈ Struct N ] Σ[ α₂ ∈ Struct N ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; α₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
      × (∃[ T₂ ] ∃[ ϵ₂ ] Γ ; α₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h α₁ + count h α₂ ≤ count h α)
inv-pair (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) ,
    λ h _ → ≤-reflexive (sym (count-join-Dir (biasedDir p/s) h γ₁ γ₂))
inv-pair (T-Conv _ _ d) = inv-pair d
inv-pair (T-Weaken γ≤ d) =
  let α₁ , α₂ , p , q , cle = inv-pair d
  in α₁ , α₂ , p , q , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

inv-seq : ∀ {N} {Γ : Ctx N} {α : Struct N} {e₁ e₂ : Tm N} {T ϵ}
  → Γ ; α ⊢ e₁ ; e₂ ∶ T ∣ ϵ
  → Σ[ α₁ ∈ Struct N ] Σ[ α₂ ∈ Struct N ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; α₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
      × (∃[ T₂ ] ∃[ ϵ₂ ] Γ ; α₂ ⊢ e₂ ∶ T₂ ∣ ϵ₂)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h α₁ + count h α₂ ≤ count h α)
inv-seq (T-Seq {γ₁ = γ₁} {γ₂ = γ₂} _ ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) ,
    λ h _ → ≤-refl
inv-seq (T-Conv _ _ d) = inv-seq d
inv-seq (T-Weaken γ≤ d) =
  let α₁ , α₂ , p , q , cle = inv-seq d
  in α₁ , α₂ , p , q , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

inv-let : ∀ {N} {Γ : Ctx N} {α : Struct N} {e₁ : Tm N} {e₂ : Tm (suc N)} {T ϵ}
  → Γ ; α ⊢ `let e₁ `in e₂ ∶ T ∣ ϵ
  → Σ[ γ₁ ∈ Struct N ] Σ[ γ₂ ∈ Struct N ] Σ[ p/s ∈ ParSeq ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
      × (∃[ T₁ ] ∃[ U ] ∃[ ϵ' ] (T₁ ⸴ Γ) ; join p/s (` zero) (𝐂S.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ')
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h γ₁ + count h γ₂ ≤ count h α)
inv-let (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , p/s , (_ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) ,
    λ h _ → ≤-reflexive (sym (count-join-PS p/s h γ₁ γ₂))
inv-let (T-Conv _ _ d) = inv-let d
inv-let (T-Weaken γ≤ d) =
  let γ₁ , γ₂ , p/s , p , q , cle = inv-let d
  in γ₁ , γ₂ , p/s , p , q , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

inv-letpair : ∀ {N} {Γ : Ctx N} {α : Struct N} {e₁ : Tm N} {e₂ : Tm (suc (suc N))} {T ϵ}
  → Γ ; α ⊢ `let⊗ e₁ `in e₂ ∶ T ∣ ϵ
  → Σ[ γ₁ ∈ Struct N ] Σ[ γ₂ ∈ Struct N ] Σ[ p/s ∈ ParSeq ] Σ[ d ∈ Dir ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; γ₁ ⊢ e₁ ∶ T₁ ∣ ϵ₁)
      × (∃[ T₁ ] ∃[ T₂ ] ∃[ U ] ∃[ ϵ' ]
           (T₁ ⸴ T₂ ⸴ Γ) ; join p/s (join d (` zero) (` suc zero)) (𝐂S.wk (𝐂S.wk γ₂)) ⊢ e₂ ∶ U ∣ ϵ')
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h γ₁ + count h γ₂ ≤ count h α)
inv-letpair (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , (_ , _ , _ , _ , ⊢e₂) ,
    λ h _ → ≤-reflexive (sym (count-join-PS p/s h γ₁ γ₂))
inv-letpair (T-Conv _ _ d) = inv-letpair d
inv-letpair (T-Weaken γ≤ d) =
  let γ₁ , γ₂ , p/s , dd , p , q , cle = inv-letpair d
  in γ₁ , γ₂ , p/s , dd , p , q , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

inv-inj : ∀ {N} {Γ : Ctx N} {α : Struct N} {i} {e : Tm N} {T ϵ}
  → Γ ; α ⊢ `inj i e ∶ T ∣ ϵ
  → (∃[ T₀ ] ∃[ ϵ₀ ] Γ ; α ⊢ e ∶ T₀ ∣ ϵ₀)
inv-inj (T-Inj ⊢e)     = _ , _ , ⊢e
inv-inj (T-Conv _ _ d) = inv-inj d
inv-inj (T-Weaken γ≤ d) =
  let _ , _ , ⊢e = inv-inj d in _ , _ , T-Weaken γ≤ ⊢e

inv-case : ∀ {N} {Γ : Ctx N} {α : Struct N} {e : Tm N} {e₁ e₂ : Tm (suc N)} {T ϵ}
  → Γ ; α ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ∶ T ∣ ϵ
  → Σ[ γ₁ ∈ Struct N ] Σ[ γ₂ ∈ Struct N ] Σ[ p/s ∈ ParSeq ]
      (∃[ T₁ ] ∃[ ϵ₁ ] Γ ; γ₁ ⊢ e ∶ T₁ ∣ ϵ₁)
      × (∃[ T₁ ] ∃[ U ] ∃[ ϵ' ] (T₁ ⸴ Γ) ; join p/s (` zero) (𝐂S.wk γ₂) ⊢ e₁ ∶ U ∣ ϵ')
      × (∃[ T₂ ] ∃[ U ] ∃[ ϵ' ] (T₂ ⸴ Γ) ; join p/s (` zero) (𝐂S.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ')
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h γ₁ + count h γ₂ ≤ count h α)
inv-case (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) =
  γ₁ , γ₂ , p/s , (_ , _ , ⊢e) , (_ , _ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) ,
    λ h _ → ≤-reflexive (sym (count-join-PS p/s h γ₁ γ₂))
inv-case (T-Conv _ _ d) = inv-case d
inv-case (T-Weaken γ≤ d) =
  let γ₁ , γ₂ , p/s , p , q₁ , q₂ , cle = inv-case d
  in γ₁ , γ₂ , p/s , p , q₁ , q₂ , λ h ¬u → ≤-trans (cle h ¬u) (≼⇒count≤ ¬u γ≤)

·□-cong : ∀ {n} {e e' : Tm n} (eq : e ≡ e') (V : Value e) (V' : Value e') → (V ·□) ≡ (V' ·□)
·□-cong {e = e} eq V V' =
  subst (λ ee → (V'' : Value ee) → (V ·□) ≡ (V'' ·□)) eq (λ V'' → cong _·□ Value-irr) V'

⊗□-cong : ∀ {n} {e e' : Tm n} (eq : e ≡ e') (V : Value e) (V' : Value e') → (V ⊗□) ≡ (V' ⊗□)
⊗□-cong {e = e} eq V V' =
  subst (λ ee → (V'' : Value ee) → (V ⊗□) ≡ (V'' ⊗□)) eq (λ V'' → cong _⊗□ Value-irr) V'

+≤ʳ⇒0 : ∀ a b → a + b ≤ b → a ≡ 0
+≤ʳ⇒0 a b le = +≤ˡ⇒0 b (subst (_≤ b) (+-comm a b) le)

-- Strengthening a frame: from the typing of E [ t ]*, peel each frame, and given
-- the plug t already accounts for all of h's count, factor E through any ρ that
-- misses h.  Frame components are strengthened by strengthen-Tm-gen (value frames
-- via value-reflect; binder frames at the shifted hole).
strengthen-frame : ∀ {N} {Γ : Ctx N} {α : Struct N} {t : Tm N} {T ϵ}
  (E : Frame* N) → Γ ; α ⊢ E [ t ]* ∶ T ∣ ϵ
  → Σ[ β ∈ Struct N ] (∃[ T₀ ] ∃[ ϵ₀ ] Γ ; β ⊢ t ∶ T₀ ∣ ϵ₀)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h β ≤ count h α)
      × ((h : 𝔽 N) → ¬ Unr (Γ h) → count h α ≤ count h β
         → {k : ℕ} (ρ : k →ᵣ N) → Inverter ρ h → Σ[ E₀ ∈ Frame* k ] E ≡ E₀ ⋯ᶠ* ρ)
strengthen-frame [] ⊢t =
  _ , (_ , _ , ⊢t) , (λ h _ → ≤-refl) , (λ h _ _ ρ inv → [] , refl)
strengthen-frame (L._∷_ (□· e₂) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cα₂0 = +≤ˡ⇒0 (count h α₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cα₁≤β = ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cα₁≤β ρ inv
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ ρ h inv (count0⇒∉dom α₂ cα₂0)
        in (L._∷_ (□· e₂₀) E₀') , cong₂ L._∷_ (cong □·_ e₂eq) E'eq)
strengthen-frame (L._∷_ (_·□ {e₁ = e₁} V) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢V) , (_ , _ , ⊢inner) , cle = inv-app ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cα₁0 = +≤ʳ⇒0 (count h α₁) (count h α₂) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cα₂≤β = ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cα₂≤β ρ inv
            comp₀ , compeq = strengthen-Tm-gen ⊢V ρ h inv (count0⇒∉dom α₁ cα₁0)
            V₀ = value-reflect ρ comp₀ (subst Value compeq V)
        in (L._∷_ (_·□ V₀) E₀') , cong₂ L._∷_ (·□-cong compeq V (V₀ ⋯ᵛ ρ)) E'eq)
strengthen-frame (L._∷_ (□⊗ e₂) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cα₂0 = +≤ˡ⇒0 (count h α₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cα₁≤β = ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cα₁≤β ρ inv
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ ρ h inv (count0⇒∉dom α₂ cα₂0)
        in (L._∷_ (□⊗ e₂₀) E₀') , cong₂ L._∷_ (cong □⊗_ e₂eq) E'eq)
strengthen-frame (L._∷_ (_⊗□ {e₁ = e₁} V) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢V) , (_ , _ , ⊢inner) , cle = inv-pair ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cα₁0 = +≤ʳ⇒0 (count h α₁) (count h α₂) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cα₂≤β = ≤-trans (≤-trans (m≤n+m (count h α₂) (count h α₁)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cα₂≤β ρ inv
            comp₀ , compeq = strengthen-Tm-gen ⊢V ρ h inv (count0⇒∉dom α₁ cα₁0)
            V₀ = value-reflect ρ comp₀ (subst Value compeq V)
        in (L._∷_ (_⊗□ V₀) E₀') , cong₂ L._∷_ (⊗□-cong compeq V (V₀ ⋯ᵛ ρ)) E'eq)
strengthen-frame (L._∷_ (□; e₂) E') ⊢E =
  let α₁ , α₂ , (_ , _ , ⊢inner) , (_ , _ , ⊢e₂) , cle = inv-seq ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cα₂0 = +≤ˡ⇒0 (count h α₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cα₁≤β = ≤-trans (≤-trans (m≤m+n (count h α₁) (count h α₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cα₁≤β ρ inv
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ ρ h inv (count0⇒∉dom α₂ cα₂0)
        in (L._∷_ (□; e₂₀) E₀') , cong₂ L._∷_ (cong □;_ e₂eq) E'eq)
strengthen-frame (L._∷_ (`let-`in e') E') ⊢E =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = inv-let ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢e₁
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cγ₂0 = +≤ˡ⇒0 (count h γ₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cγ₁≤β = ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cγ₁≤β ρ inv
            COUNT0 = count-join-PS p/s (suc h) (` zero) (𝐂S.wk γ₂) ■ count-wk-suc γ₂ h ■ cγ₂0
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ (ρ ↑) (suc h) (inv↑ inv)
                           (count0⇒∉dom (join p/s (` zero) (𝐂S.wk γ₂)) COUNT0)
        in (L._∷_ (`let-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let-`in_ e₂eq) E'eq)
strengthen-frame (L._∷_ (`let⊗-`in e') E') ⊢E =
  let γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , (_ , _ , _ , _ , ⊢e₂) , cle = inv-letpair ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢e₁
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cγ₂0 = +≤ˡ⇒0 (count h γ₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cγ₁≤β = ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cγ₁≤β ρ inv
            COUNT0 = count-join-PS p/s (suc (suc h)) (join d (` zero) (` suc zero)) (𝐂S.wk (𝐂S.wk γ₂))
                   ■ cong₂ _+_ (count-join-Dir d (suc (suc h)) (` zero) (` suc zero))
                               (count-wk-suc (𝐂S.wk γ₂) (suc h) ■ count-wk-suc γ₂ h ■ cγ₂0)
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ (ρ ↑ ↑) (suc (suc h)) (inv↑ (inv↑ inv))
                           (count0⇒∉dom (join p/s (join d (` zero) (` suc zero)) (𝐂S.wk (𝐂S.wk γ₂))) COUNT0)
        in (L._∷_ (`let⊗-`in e₂₀) E₀') , cong₂ L._∷_ (cong `let⊗-`in_ e₂eq) E'eq)

strengthen-frame (L._∷_ (`inj□ i) E') ⊢E =
  let _ , _ , ⊢inner = inv-inj ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢inner
  in β , pt , support' ,
     (λ h ¬u cα≤β ρ inv →
        let E₀' , E'eq = factor' h ¬u cα≤β ρ inv
        in (L._∷_ (`inj□ i) E₀') , cong₂ L._∷_ refl E'eq)
strengthen-frame (L._∷_ (`case□`of⟨ e₁ ; e₂ ⟩) E') ⊢E =
  let γ₁ , γ₂ , p/s , (_ , _ , ⊢e) , (_ , _ , _ , ⊢e₁) , (_ , _ , _ , ⊢e₂) , cle = inv-case ⊢E
      β , pt , support' , factor' = strengthen-frame E' ⊢e
  in β , pt ,
     (λ h ¬u → ≤-trans (support' h ¬u) (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u))) ,
     (λ h ¬u cα≤β ρ inv →
        let cγ₂0 = +≤ˡ⇒0 (count h γ₁) (≤-trans (≤-trans (cle h ¬u) cα≤β) (support' h ¬u))
            cγ₁≤β = ≤-trans (≤-trans (m≤m+n (count h γ₁) (count h γ₂)) (cle h ¬u)) cα≤β
            E₀' , E'eq = factor' h ¬u cγ₁≤β ρ inv
            COUNT0 = count-join-PS p/s (suc h) (` zero) (𝐂S.wk γ₂) ■ count-wk-suc γ₂ h ■ cγ₂0
            ∉br = count0⇒∉dom (join p/s (` zero) (𝐂S.wk γ₂)) COUNT0
            e₁₀ , e₁eq = strengthen-Tm-gen ⊢e₁ (ρ ↑) (suc h) (inv↑ inv) ∉br
            e₂₀ , e₂eq = strengthen-Tm-gen ⊢e₂ (ρ ↑) (suc h) (inv↑ inv) ∉br
        in (L._∷_ (`case□`of⟨ e₁₀ ; e₂₀ ⟩) E₀') ,
           cong₂ L._∷_ (cong₂ (λ a b → `case□`of⟨ a ; b ⟩) e₁eq e₂eq) E'eq)
-- A variable's typing context counts that variable at least as much as its
-- canonical singleton context.
inv-var-count : ∀ {N} {Γ : Ctx N} {α : Struct N} {x : 𝔽 N} {T ϵ}
  → Γ ; α ⊢ ` x ∶ T ∣ ϵ → (h : 𝔽 N) → ¬ Unr (Γ h) → count h (` x) ≤ count h α
inv-var-count (T-Var _ _)   h _  = ≤-refl
inv-var-count (T-Conv _ _ d) h ¬u = inv-var-count d h ¬u
inv-var-count (T-Weaken γ≤ d) h ¬u = ≤-trans (inv-var-count d h ¬u) (≼⇒count≤ ¬u γ≤)

-- The function side of an lsplit application has domain ≃ ⟨ s ; s′ ⟩ and carries
-- the ¬ Skips s premise of the `lsplit constant.
fn-lsplit-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {T U a ϵ}
  → Γ ; β ⊢ K (`lsplit s) ∶ T ⟨ a ⟩→ U ∣ ϵ → ¬ Skips s × Σ[ s′ ∈ 𝕊 0 ] (⟨ s ; s′ ⟩ ≃ T)
fn-lsplit-dom (T-Const (`lsplit ¬Ss s′)) = ¬Ss , s′ , ≃-refl
fn-lsplit-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let ¬Ss , s′ , eq = fn-lsplit-dom d in ¬Ss , s′ , ≃-trans eq dom≃
fn-lsplit-dom (T-Weaken _ d) = fn-lsplit-dom d

-- A variable's type is ≃-related to its context entry.
arg-type : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ ` x ∶ T ∣ ϵ → Γ x ≃ T
arg-type (T-Var _ T-eq)   = subst (_ ≃_) T-eq ≃-refl
arg-type (T-Conv T≃ _ d)  = ≃-trans (arg-type d) T≃
arg-type (T-Weaken _ d)   = arg-type d

-- The consumed lsplit handle has a non-unrestricted type.
lsplit-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K (`lsplit s) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
lsplit-app-nonUnr d = go d
  where
    go : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {x : 𝔽 N} {T ϵ}
       → Γ ; β ⊢ K (`lsplit s) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
    go (T-AppUnr _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-lsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLin _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-lsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLeft _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-lsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppRight _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-lsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-Conv _ _ d) u = go d u
    go (T-Weaken _ d) u = go d u

-- The function side of an rsplit application has domain ≃ ⟨ s ; s′ ⟩ and carries
-- the ¬ Skips s premise of the `rsplit constant.
fn-rsplit-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {T U a ϵ}
  → Γ ; β ⊢ K (`rsplit s) ∶ T ⟨ a ⟩→ U ∣ ϵ → ¬ Skips s × Σ[ s′ ∈ 𝕊 0 ] (⟨ s ; s′ ⟩ ≃ T)
fn-rsplit-dom (T-Const (`rsplit ¬Ss s′)) = ¬Ss , s′ , ≃-refl
fn-rsplit-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let ¬Ss , s′ , eq = fn-rsplit-dom d in ¬Ss , s′ , ≃-trans eq dom≃
fn-rsplit-dom (T-Weaken _ d) = fn-rsplit-dom d

-- The consumed rsplit handle has a non-unrestricted type.
rsplit-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K (`rsplit s) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
rsplit-app-nonUnr d = go d
  where
    go : ∀ {N} {Γ : Ctx N} {β : Struct N} {s : 𝕊 0} {x : 𝔽 N} {T ϵ}
       → Γ ; β ⊢ K (`rsplit s) · (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
    go (T-AppUnr _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-rsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLin _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-rsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppLeft _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-rsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-AppRight _ _ ⊢fn ⊢arg) u =
      let ¬Ss , s′ , eq = fn-rsplit-dom ⊢fn
      in ¬Skips⇒¬Unr-seq ¬Ss (unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym eq)) u)
    go (T-Conv _ _ d) u = go d u
    go (T-Weaken _ d) u = go d u
