module BorrowedCF.Simulation.Support.RevGrindA where

-- Grind helpers for the RU-Com / RU-Choice reverse-simulation cases
-- (BorrowedCF.Simulation.Support.Reverse).  Kept separate so the parallel merge of
-- Reverse.agda stays clean: Reverse.agda only fills hole lines and imports here.

open import BorrowedCF.Simulation.Support.Base
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅)
open import BorrowedCF.Simulation.Support.Confine using (count; count-self; count-join-PS; count-join-Dir; ≼⇒count≤)
open import BorrowedCF.Simulation.Support.BeforeOrder using (before; before⇒mem; before-mono-≼)
open import BorrowedCF.Simulation.Support.RevComConfine using (count-plug-add)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 using (fn-send-dom)

open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-mono-≤)

------------------------------------------------------------------------
-- Channels are never unrestricted.  A ChanCx entry is a channel type
-- ⟨ s ⟩, and Unr ⟨ s ⟩ = TPred Arr.Unr (λ _ → ⊥) ⟨ s ⟩ is uninhabited
-- (its channel constructor ⟨_⟩ carries a ⊥).  Mirrors d57a798 (main).
------------------------------------------------------------------------

chanCx-¬Unr : ∀ {N} {Γ : Ctx N} → ChanCx Γ → (x : 𝔽 N) → ¬ Unr (Γ x)
chanCx-¬Unr Γ-S x u with Γ-S x
... | s , eq with subst Unr eq u
...   | ⟨ () ⟩

------------------------------------------------------------------------
-- Small utilities.
------------------------------------------------------------------------

-- ≃ on ⊗-types is rigid in the direction annotation.
⊗≃-dir : ∀ {Ta Ua Tb Ub : 𝕋} {d d' : Dir}
       → (Ta ⊗⟨ d ⟩ Ua) ≃ (Tb ⊗⟨ d' ⟩ Ub) → d ≡ d'
⊗≃-dir (_ ⊗ _) = refl

-- biasedDir par = 𝟙, biasedDir seq = L, so biasedDir p/s ≡ 𝟙 forces par.
biasedDir-par : ∀ {p/s} → biasedDir p/s ≡ 𝟙 → p/s ≡ par
biasedDir-par {par} refl = refl
biasedDir-par {seq} ()

-- The fn side of an InvApp.
invApp-fn : ∀ {N} {Γ : Ctx N} {α β : Struct N} {e₁ e₂ a T U ϵ}
  → InvApp Γ α β e₁ e₂ a T U ϵ
  → Σ[ ϵ' ∈ Eff ] (Γ ; α ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ')
invApp-fn (T-AppUnr  _ x _) = _ , x
invApp-fn (T-AppLin  _ x _) = _ , x
invApp-fn (T-AppLeft _ x _) = _ , x
invApp-fn (T-AppRight _ x _) = _ , x

invApp-arg : ∀ {N} {Γ : Ctx N} {α β : Struct N} {e₁ e₂ a T U ϵ}
  → InvApp Γ α β e₁ e₂ a T U ϵ → Σ[ ϵ' ∈ Eff ] (Γ ; β ⊢ e₂ ∶ T ∣ ϵ')
invApp-arg (T-AppUnr  _ _ y) = _ , y
invApp-arg (T-AppLin  _ _ y) = _ , y
invApp-arg (T-AppLeft _ _ y) = _ , y
invApp-arg (T-AppRight _ _ y) = _ , y

1≤ne : ∀ {n} → n ≢ 0 → 1 ≤ n
1≤ne {zero}  ne = ⊥-elim (ne refl)
1≤ne {suc _} _  = s≤s z≤n

2≰1 : 2 ≤ 1 → ⊥
2≰1 (s≤s ())

------------------------------------------------------------------------
-- com-¬before : in the send-redex context γrˢ, nothing (0F in particular)
-- ;-precedes the send handle xS.  The send argument pair  aS ⊗ ` xS  has
-- direction 𝟙 (the `send` constant's ⊗¹ domain), so its context is
-- (msg ∥ chan): xS lives only in the chan branch, and the whole redex
-- application is a ∥ of fn/arg.  Any occurrence of xS OTHER than the chan
-- leaf would push  count xS γrˢ ≥ 2, contradicting the confinement
-- count xS γinner ≡ 1.  So  before y xS γrˢ  is impossible.
------------------------------------------------------------------------

com-¬before :
  ∀ {N} {Γ : Ctx N} {γrˢ αcom βcom γinner : Struct N} {𝒫ˢ : CxPat N}
    {aS : Tm N} {xS y : 𝔽 N} {U ϵ}
  → ¬ Mobile (Γ xS) → ¬ Mobile (Γ y)
  → Γ ; γrˢ ⊢ K `send ·¹ (aS ⊗ (` xS)) ∶ U ∣ ϵ
  → Γ ∶ 𝒫ˢ [ γrˢ ]𝓅 ≼ αcom
  → Γ ∶ αcom ∥ βcom ≼ γinner
  → count xS γinner ≡ 1
  → ¬ before y xS γrˢ
com-¬before {Γ = Γ} {γrˢ} {αcom} {βcom} {γinner} {𝒫ˢ} {aS} {xS} {y}
            ¬uxS ¬uy ⊢redex ≼ˢ αβ≼ cnt1 bfr
  with inv-· ⊢redex
... | a , α , β , T , ≤γ , dir≡ , ≤ₐ , invapp
  with subst (λ d → before y xS (join d β α)) dir≡ (before-mono-≼ ¬uy ¬uxS ≤γ bfr)
... | inj₂ bα =
      -- fn side (K send): constant context is ≽ [], nothing before xS there.
      let _ , _ , []≼α , _ = inv-K (proj₂ (invApp-fn invapp))
      in before-mono-≼ ¬uy ¬uxS []≼α bα
... | inj₁ bβ
  with fn-send-dom (proj₂ (invApp-fn invapp))
... | Tᵐ , domeq
  with invApp-arg invapp
... | _ , ⊢arg
  with inv-⊗ ⊢arg
... | p/s , α' , β' , T₁ , T₂ , ϵ₁ , ϵ₂ , ≤β , pdeq , _ , _ , ⊢aS , ⊢xS
  with biasedDir-par (⊗≃-dir (≃-trans pdeq (≃-sym domeq)))
... | refl
  with before-mono-≼ ¬uy ¬uxS ≤β bβ
... | inj₂ bβ' =
      -- chan side: the bare variable ` xS has no ;-order at all.
      before-mono-≼ ¬uy ¬uxS (proj₂ (inv-` ⊢xS)) bβ'
... | inj₁ bα' =
      -- msg side: xS occurs both in msg (bα') and chan (` xS) → count ≥ 2 > 1.
      let xS∈α'  = proj₂ (before⇒mem α' bα')
          1≤α'   = 1≤ne xS∈α'
          1≤β'   = subst (_≤ count xS β') (count-self xS) (≼⇒count≤ (¬uxS ∘ unr⇒mobile) (proj₂ (inv-` ⊢xS)))
          2≤pair = subst (2 ≤_) (sym (count-join-PS par xS α' β')) (+-mono-≤ 1≤α' 1≤β')
          pair≤β = ≼⇒count≤ (¬uxS ∘ unr⇒mobile) ≤β
          β≤ba   = m≤m+n (count xS β) (count xS α)
          ba≤γrˢ = ≼⇒count≤ (¬uxS ∘ unr⇒mobile) (subst (λ d → Γ ∶ join d β α ≼ γrˢ) dir≡ ≤γ)
          γrˢ≤plug = subst (count xS γrˢ ≤_) (sym (count-plug-add 𝒫ˢ γrˢ xS))
                       (m≤n+m (count xS γrˢ) (count xS (𝒫ˢ [ [] ]𝓅)))
          γrˢ≤1  = subst (count xS γrˢ ≤_) cnt1
                     (≤-trans γrˢ≤plug
                       (≤-trans (≼⇒count≤ (¬uxS ∘ unr⇒mobile) ≼ˢ)
                         (≤-trans (m≤m+n (count xS αcom) (count xS βcom))
                                  (≼⇒count≤ (¬uxS ∘ unr⇒mobile) αβ≼))))
      in ⊥-elim (2≰1 (≤-trans 2≤pair
                       (≤-trans pair≤β
                         (≤-trans β≤ba (≤-trans ba≤γrˢ γrˢ≤1)))))


------------------------------------------------------------------------
-- Bare-variable channel-op front-forcing helpers (select / branch).
-- Analogues of the send-* lemmas, but the argument is a BARE channel
-- variable ` x (not a pair), so the derivations are simpler.
------------------------------------------------------------------------

𝕀≤⇒≡𝕀 : ∀ {ϵ} → 𝕀 ≤ϵ ϵ → ϵ ≡ 𝕀
𝕀≤⇒≡𝕀 𝕀≤𝕀 = refl

-- select ------------------------------------------------------------------
select-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {T U a ϵ} {i}
  → Γ ; α ⊢ K (`select i) ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.eff a ≡ 𝕀
select-fn-eff-𝕀 (T-Const `select) = refl
select-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = select-fn-eff-𝕀 d
select-fn-eff-𝕀 (T-Weaken _ d) = select-fn-eff-𝕀 d

select-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {U ϵ} {i}
  → Γ ; γ ⊢ K (`select i) ·¹ arg ∶ U ∣ ϵ → ϵ ≡ 𝕀
select-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (select-fn-eff-𝕀 ⊢fn) ≤ₐ)
select-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (select-fn-eff-𝕀 ⊢fn) ≤ₐ)
select-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (select-app-𝕀 d) ≤)
select-app-𝕀 (T-Weaken _ d) = select-app-𝕀 d

select-fn-dom : ∀ {N} {Γ : Ctx N} {α : Struct N} {T U a ϵ} {i}
  → Γ ; α ⊢ K (`select i) ∶ T ⟨ a ⟩→ U ∣ ϵ
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] (⟨ brn ‼ s₁ s₂ ⟩ ≃ T)
select-fn-dom (T-Const `select) = _ , _ , ≃-refl
select-fn-dom (T-Conv (dom≃ `→ _) _ d) = let s₁ , s₂ , eq = select-fn-dom d in s₁ , s₂ , ≃-trans eq dom≃
select-fn-dom (T-Weaken _ d) = select-fn-dom d

sad-select : ∀ {N} {Γ : Ctx N} {α β : Struct N} {arg : Tm N} {Targ Uu ϵ₁ ϵ₂ a} {i}
  → Γ ; α ⊢ K (`select i) ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ arg ∶ Targ ∣ ϵ₂
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ brn ‼ s₁ s₂ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
sad-select {β = β} ⊢fn ⊢arg with select-fn-dom ⊢fn
... | s₁ , s₂ , domeq = s₁ , s₂ , β , _ , _ , domeq , ⊢arg

select-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {U ϵ} {i}
  → Γ ; γ ⊢ K (`select i) ·¹ arg ∶ U ∣ ϵ
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ brn ‼ s₁ s₂ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
select-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = sad-select ⊢fn ⊢arg
select-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = sad-select ⊢fn ⊢arg
select-arg-decomp (T-Conv _ _ d) = select-arg-decomp d
select-arg-decomp (T-Weaken _ d) = select-arg-decomp d

-- branch ------------------------------------------------------------------
branch-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {T U a ϵ}
  → Γ ; α ⊢ K `branch ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.eff a ≡ 𝕀
branch-fn-eff-𝕀 (T-Const `branch) = refl
branch-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = branch-fn-eff-𝕀 d
branch-fn-eff-𝕀 (T-Weaken _ d) = branch-fn-eff-𝕀 d

branch-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {U ϵ}
  → Γ ; γ ⊢ K `branch ·¹ arg ∶ U ∣ ϵ → ϵ ≡ 𝕀
branch-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (branch-fn-eff-𝕀 ⊢fn) ≤ₐ)
branch-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (branch-fn-eff-𝕀 ⊢fn) ≤ₐ)
branch-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (branch-app-𝕀 d) ≤)
branch-app-𝕀 (T-Weaken _ d) = branch-app-𝕀 d

branch-fn-dom : ∀ {N} {Γ : Ctx N} {α : Struct N} {T U a ϵ}
  → Γ ; α ⊢ K `branch ∶ T ⟨ a ⟩→ U ∣ ϵ
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] (⟨ brn ⁇ s₁ s₂ ⟩ ≃ T)
branch-fn-dom (T-Const `branch) = _ , _ , ≃-refl
branch-fn-dom (T-Conv (dom≃ `→ _) _ d) = let s₁ , s₂ , eq = branch-fn-dom d in s₁ , s₂ , ≃-trans eq dom≃
branch-fn-dom (T-Weaken _ d) = branch-fn-dom d

sad-branch : ∀ {N} {Γ : Ctx N} {α β : Struct N} {arg : Tm N} {Targ Uu ϵ₁ ϵ₂ a}
  → Γ ; α ⊢ K `branch ∶ Targ ⟨ a ⟩→ Uu ∣ ϵ₁
  → Γ ; β ⊢ arg ∶ Targ ∣ ϵ₂
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ brn ⁇ s₁ s₂ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
sad-branch {β = β} ⊢fn ⊢arg with branch-fn-dom ⊢fn
... | s₁ , s₂ , domeq = s₁ , s₂ , β , _ , _ , domeq , ⊢arg

branch-arg-decomp : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {U ϵ}
  → Γ ; γ ⊢ K `branch ·¹ arg ∶ U ∣ ϵ
  → Σ[ s₁ ∈ 𝕊 0 ] Σ[ s₂ ∈ 𝕊 0 ] Σ[ β' ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ' ∈ Eff ]
      (⟨ brn ⁇ s₁ s₂ ⟩ ≃ R) × (Γ ; β' ⊢ arg ∶ R ∣ ϵ')
branch-arg-decomp (T-AppUnr _ _ ⊢fn ⊢arg) = sad-branch ⊢fn ⊢arg
branch-arg-decomp (T-AppLin _ _ ⊢fn ⊢arg) = sad-branch ⊢fn ⊢arg
branch-arg-decomp (T-Conv _ _ d) = branch-arg-decomp d
branch-arg-decomp (T-Weaken _ d) = branch-arg-decomp d

-- bare-variable argument count + precedence ------------------------------
barevar-arg-count : ∀ {N} {Γ : Ctx N} {γ : Struct N} {x : 𝔽 N} {c U ϵ}
  → ¬ Unr (Γ x) → Γ ; γ ⊢ K c ·¹ (` x) ∶ U ∣ ϵ → 1 ≤ count x γ
barevar-arg-count {x = x} ¬u ⊢redex
  with aa , α , β , T , join≼ , _ , _ , invapp ← inv-· ⊢redex
  with _ , ⊢x ← invApp-arg invapp =
  let x≼β = proj₂ (inv-` ⊢x)
      1≤β = subst (Nat._≤ count x β) (count-self x) (≼⇒count≤ ¬u x≼β)
      β≤joinγ = subst (count x β Nat.≤_) (sym (count-join-Dir (Arr.dir aa) x β α)) (m≤m+n (count x β) (count x α))
      β≤γ = ≤-trans β≤joinγ (≼⇒count≤ ¬u join≼)
  in ≤-trans 1≤β β≤γ

choice-¬before : ∀ {N} {Γ : Ctx N} {γrˢ : Struct N} {x y : 𝔽 N} {c U ϵ}
  → ¬ Mobile (Γ x) → ¬ Mobile (Γ y)
  → Γ ; γrˢ ⊢ K c ·¹ (` x) ∶ U ∣ ϵ
  → ¬ before y x γrˢ
choice-¬before {x = x} {y = y} ¬ux ¬uy ⊢redex bfr
  with inv-· ⊢redex
... | a , α , β , T , ≤γ , dir≡ , ≤ₐ , invapp
  with subst (λ d → before y x (join d β α)) dir≡ (before-mono-≼ ¬uy ¬ux ≤γ bfr)
... | inj₂ bα =
      let _ , _ , []≼α , _ = inv-K (proj₂ (invApp-fn invapp))
      in before-mono-≼ ¬uy ¬ux []≼α bα
... | inj₁ bβ =
      before-mono-≼ ¬uy ¬ux (proj₂ (inv-` (proj₂ (invApp-arg invapp)))) bβ
