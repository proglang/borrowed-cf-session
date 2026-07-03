module BorrowedCF.Simulation.RevGrindA where

-- Grind helpers for the RU-Com / RU-Choice reverse-simulation cases
-- (BorrowedCF.Simulation.Reverse).  Kept separate so the parallel merge of
-- Reverse.agda stays clean: Reverse.agda only fills hole lines and imports here.

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern using (CxPat; _[_]𝓅)
open import BorrowedCF.Simulation.Confine using (count; count-self; count-join-PS; ≼⇒count≤)
open import BorrowedCF.Simulation.BeforeOrder using (before; before⇒mem; before-mono-≼)
open import BorrowedCF.Simulation.RevComConfine using (count-plug-add)
open import BorrowedCF.Simulation.Theorems.ComHelpers2 using (fn-send-dom)

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
  → ¬ Unr (Γ xS) → ¬ Unr (Γ y)
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
          1≤β'   = subst (_≤ count xS β') (count-self xS) (≼⇒count≤ ¬uxS (proj₂ (inv-` ⊢xS)))
          2≤pair = subst (2 ≤_) (sym (count-join-PS par xS α' β')) (+-mono-≤ 1≤α' 1≤β')
          pair≤β = ≼⇒count≤ ¬uxS ≤β
          β≤ba   = m≤m+n (count xS β) (count xS α)
          ba≤γrˢ = ≼⇒count≤ ¬uxS (subst (λ d → Γ ∶ join d β α ≼ γrˢ) dir≡ ≤γ)
          γrˢ≤plug = subst (count xS γrˢ ≤_) (sym (count-plug-add 𝒫ˢ γrˢ xS))
                       (m≤n+m (count xS γrˢ) (count xS (𝒫ˢ [ [] ]𝓅)))
          γrˢ≤1  = subst (count xS γrˢ ≤_) cnt1
                     (≤-trans γrˢ≤plug
                       (≤-trans (≼⇒count≤ ¬uxS ≼ˢ)
                         (≤-trans (m≤m+n (count xS αcom) (count xS βcom))
                                  (≼⇒count≤ ¬uxS αβ≼))))
      in ⊥-elim (2≰1 (≤-trans 2≤pair
                       (≤-trans pair≤β
                         (≤-trans β≤ba (≤-trans ba≤γrˢ γrˢ≤1)))))
