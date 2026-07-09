-- | drop-confine : the R-Drop weakenᵣ factoring.  The drop redex K drop · (` 0F)
--   consumes 0F linearly, so the frame F₀ and the parallel rest P₀ᵣ both AVOID
--   0F, hence factor through weakenᵣ (inserts the consumed channel at 0F).
--   Mirror of close-confine's single side + strengthen-Proc-gen* for the rest.
module BorrowedCF.Simulation2.Backward.DropConfine where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx; Frame*; _[_]*; _⋯ᶠ*_)
open import BorrowedCF.Simulation.Strengthen using (Inverter*; strengthen-Proc-gen*)
open import BorrowedCF.Simulation.ReverseConfine using (strengthen-frame*)
open import BorrowedCF.Simulation.RevDropConfine using (count-handle-groupᴸ)
open import BorrowedCF.Simulation.Confine using (count; count-self; ≼⇒count≤; count0⇒∉dom)
open import BorrowedCF.Simulation2.Backward.Drop using (fn-drop-dom)
import BorrowedCF.Simulation.InvFrame as IF
open import BorrowedCF.Types using (Unr; unr-≃; _≃_; ≃-trans; ≃-sym)
open import BorrowedCF.Simulation.InvFrame using (arg-type; inv-var-count)
open import BorrowedCF.Context.Domain using (dom)
open import Data.Fin.Subset using (_∉_)
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Base using (_↑ˡ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open TP using (inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx; _⋯ₚ_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤0⇒n≡0; m≤n+m; +-monoˡ-≤; +-identityʳ; +-comm)

open Fin.Patterns

-- The consumed drop handle (bare var x) has a non-Unr (ret) type.
drop-app-nonUnr : ∀ {N} {Γ : Ctx N} {β : Struct N} {x : 𝔽 N} {T ϵ}
  → Γ ; β ⊢ K `drop ·¹ (` x) ∶ T ∣ ϵ → ¬ Unr (Γ x)
drop-app-nonUnr (T-AppUnr _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u
... | ⟨ () ⟩
drop-app-nonUnr (T-AppLin _ _ ⊢fn ⊢arg) u with unr-≃ (≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))) u
... | ⟨ () ⟩
drop-app-nonUnr (T-Conv _ _ d) u = drop-app-nonUnr d u
drop-app-nonUnr (T-Weaken _ d) u = drop-app-nonUnr d u

-- Handle set at 0F and its weakenᵣ inverter.
H1 : ∀ {N} → 𝔽 (suc N) → Set
H1 z = z ≡ 0F

inv-wk1 : ∀ {N} → Inverter* (weakenᵣ {n = N}) H1
inv-wk1 0F          ¬H = ⊥-elim (¬H refl)
inv-wk1 (Fin.suc y) ¬H = y , refl

drop-confine : ∀ (c b₂ : ℕ) {m} {Γ : Ctx m} → ChanCx Γ → {g : Struct m}
    {F₀ : Frame* (sum (1 ∷ c ∷ []) + sum (b₂ ∷ []) + m)}
    {P₀ᵣ : TP.Proc (sum (1 ∷ c ∷ []) + sum (b₂ ∷ []) + m)}
  → Γ ; g ⊢ₚ TP.ν (1 ∷ c ∷ []) (b₂ ∷ []) (TP.⟪ F₀ [ K `drop ·¹ (` 0F) ]* ⟫ TP.∥ P₀ᵣ)
  → Σ[ E ∈ Frame* (sum (0 ∷ c ∷ []) + sum (b₂ ∷ []) + m) ] (F₀ ≡ E ⋯ᶠ* weakenᵣ)
      × Σ[ Pp ∈ TP.Proc (sum (0 ∷ c ∷ []) + sum (b₂ ∷ []) + m) ] (P₀ᵣ ≡ Pp ⋯ₚ weakenᵣ)
drop-confine c b₂ {m} Γ-S {g} {F₀} {P₀ᵣ} ⊢P =
  let Γ₁ , Γ₂ , s' , _p , _N , _⊢B₁ , _⊢B₂ , C , C′ , ⊢body = inv-ν ⊢P
      α , β , αβ≼ , ⊢tL , ⊢Pr = inv-∥ ⊢body
      ⊢L = inv-⟪⟫ ⊢tL
      cγ = count-handle-groupᴸ (1 ∷ c ∷ []) (b₂ ∷ []) g 0F
      strres = strengthen-frame* F₀ ⊢L H1
      βp = proj₁ strres
      ⊢plug = proj₂ (proj₂ (proj₁ (proj₂ strres)))
      support = proj₁ (proj₂ (proj₂ strres))
      factor = proj₂ (proj₂ (proj₂ strres))
      ¬u0 = drop-app-nonUnr ⊢plug
      appres = IF.inv-app ⊢plug
      αfn = proj₁ appres
      αarg = proj₁ (proj₂ appres)
      ⊢arg = proj₂ (proj₂ (proj₁ (proj₂ (proj₂ (proj₂ appres)))))
      cle-plug = proj₂ (proj₂ (proj₂ (proj₂ appres)))
      1≤βp0 : 1 ≤ count 0F βp
      1≤βp0 = ≤-trans (subst (_≤ count 0F αarg) (count-self (Fin.zero {(c + 0) + (b₂ + 0) + m})) (inv-var-count ⊢arg 0F ¬u0))
                      (≤-trans (m≤n+m (count 0F αarg) (count 0F αfn)) (cle-plug 0F ¬u0))
      c0-αβ≤1 : count 0F α + count 0F β ≤ 1
      c0-αβ≤1 = subst (count 0F α + count 0F β ≤_) cγ (≼⇒count≤ {x = 0F} ¬u0 αβ≼)
      1≤α0 : 1 ≤ count 0F α
      1≤α0 = ≤-trans 1≤βp0 (support 0F ¬u0)
      cβ0≡0 : count 0F β ≡ 0
      cβ0≡0 = n≤0⇒n≡0 (Nat.s≤s⁻¹ (≤-trans (+-monoˡ-≤ (count 0F β) 1≤α0) c0-αβ≤1))
      α0≤βp : count 0F α ≤ count 0F βp
      α0≤βp = ≤-trans (subst (_≤ 1) (cong (count 0F α +_) cβ0≡0 ■ +-identityʳ (count 0F α)) c0-αβ≤1) 1≤βp0
      hypF = λ { h refl → ¬u0 , α0≤βp }
      Eres = factor hypF weakenᵣ inv-wk1
      Pres = strengthen-Proc-gen* ⊢Pr weakenᵣ H1 inv-wk1 (λ z z≡0F → subst (λ h → h ∉ dom β) (sym z≡0F) (count0⇒∉dom β cβ0≡0))
  in proj₁ Eres , proj₂ Eres , proj₁ Pres , proj₂ Pres
