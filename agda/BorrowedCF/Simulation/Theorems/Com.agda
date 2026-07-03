module BorrowedCF.Simulation.Theorems.Com where

-- | The (reworked) translation U[_] respects the typed structural congruence ≋.
--   Ported to the NEW (simpler) translation on git main: φ is a single Flag
--   binder; the heavy φ^ engine of the old development is gone.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; R2; R2'; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; wk·assocSwap; toℕ-weaken*ᵣ; weaken*ᵣ~↑ʳ
        ; toℕ-swapᵣ-lt; toℕ-swapᵣ-mid; toℕ-swapᵣ-ge
        ; toℕ-assoc-lt; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-reduce≥
        ; swap-place-A; swap-place-B; swap-place-tail; R'-fix-ge; toℕ-↑*-ge; toℕ-↑*-lt
        ; commuteS; wkSwap-cancel; assocSwap-invol
        ; toℕ-assoc↑*-fix-ge; toℕ-assoc↑*-lt; toℕ-wk↑*-lt; toℕ-wk↑*-ge; toℕ-swap↑*-ge
        ; assoc-place-lo; assoc-place-mid; assoc-place-tail )

open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Context.Base using (_⸴*_; _⸴_)
open T using (inv-∥; inv-ν; inv-⟪⟫; BindCtx; BindCtx′; bindCtx⇒chanCtx)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import BorrowedCF.Simulation.InvFrame using (inv-app; inv-pair; arg-type; strengthen-frame)
open import BorrowedCF.Types using (Bounded; ≃-bounded; Skips; skips⊥bounded)
open import BorrowedCF.Context.Join using (biasedDir)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.TranslationProperties using (VChan; chanTriple-V; Value-subst)

open T using (_;_⊢ₚ_)
open import BorrowedCF.Simulation.Theorems.ComHelpers2 public

------------------------------------------------------------------------
-- The exported forward-simulation case R-Com.
------------------------------------------------------------------------

U-com : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  → {E₁ E₂ : Frame* (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {P : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {e : Tm (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → (V : Value e)
  → (let wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
       ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
         T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
         T.∥ (P T.⋯ₚ wkρ)))
  → (let wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
                T.∥ (P T.⋯ₚ wkρ)) ] σ
       UR─→ₚ*
      U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ)
     ⊎
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send ·¹ ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
                T.∥ (P T.⋯ₚ wkρ)) ] σ
       U.≋
      U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ))
U-com {m} {n} σ Vσ Γ-S {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} {P = P} {e = e} V ⊢P
  with com-head≥1 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = e} {E₁ = E₁} {E₂ = E₂} {P = P} V ⊢P
     | com-head≥2 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = e} {E₁ = E₁} {E₂ = E₂} {P = P} V ⊢P
... | b₁' , refl | b₂' , refl =
  ≋-wrap-⊎ front fire back
  where
    wkρ : (b₁ + sum B₁) + (b₂ + sum B₂) + m →ᵣ sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m
    wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂
    yv : 𝔽 (sum B₁′ + sum B₂′ + m)
    yv = wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)
    EE₁ EE₂ : Frame* (sum B₁′ + sum B₂′ + m)
    EE₁ = E₁ ⋯ᶠ* wkρ
    EE₂ = E₂ ⋯ᶠ* wkρ
    ee : Tm (sum B₁′ + sum B₂′ + m)
    ee = e ⋯ wkρ
    PP : T.Proc (sum B₁′ + sum B₂′ + m)
    PP = P T.⋯ₚ wkρ
    QL : T.Proc (sum B₁′ + sum B₂′ + m)
    QL = (T.⟪ EE₁ [ K `send ·¹ (ee ⊗ (` 0F)) ]* ⟫ T.∥ T.⟪ EE₂ [ K `recv ·¹ (` yv) ]* ⟫) T.∥ PP
    τ : sum B₁′ + sum B₂′ + m →ₛ syncs B₂′ + (syncs B₁′ + (2 + n))
    τ = leafσ σ B₁′ B₂′
    XL : U.Proc (syncs B₂′ + (syncs B₁′ + (2 + n)))
    XL = U[ QL ] τ
    sA sB : ℕ
    sA = syncs B₁′
    sB = syncs B₂′
    push : ∀ {k} → U.Proc (sB + (sA + (2 + k))) → U.Proc (2 + (sB + (sA + k)))
    push {k} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    YL : U.Proc (2 + (sB + (sA + n)))
    YL = push XL
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ B₁′ (Bφ B₂′ X)) U.≋ Bφ B₁′ (Bφ B₂′ (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ B₁′ (Bφ B₂′ X)
      ◅◅ Bφ-cong B₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B₂′ X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong B₁′ (ν-past-Bφ B₂′ (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν B₁′ B₂′ QL ] σ U.≋ Bφ B₁′ (Bφ B₂′ (U.ν YL))
    front = ≡→≋ (Uν-flat σ B₁′ B₂′ QL) ◅◅ ν↓ XL
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ B₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    τyv≡ : τ yv ≡ canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) 0F
    τyv≡ = cong [ _ , _ ]′ split-outer ■ cong [ _ , _ ]′ split-inner
      where
        z0 : 𝔽 (sum B₂′)
        z0 = 0F
        split-outer : Fin.splitAt (sum B₁′ + sum B₂′) yv ≡ inj₁ (sum B₁′ ↑ʳ z0)
        split-outer = Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) (sum B₁′ ↑ʳ z0) m
        split-inner : Fin.splitAt (sum B₁′) (sum B₁′ ↑ʳ z0) ≡ inj₂ z0
        split-inner = Fin.splitAt-↑ʳ (sum B₁′) (sum B₂′) z0
    tr₀ : Σ[ a ∈ Tm (syncs B₁′ + (2 + n)) ] Σ[ c ∈ Tm (syncs B₁′ + (2 + n)) ]
          Σ[ j ∈ 𝔽 (syncs B₁′ + (2 + n)) ]
            (canonₛ B₁′ (K `unit , 0F , K `unit) 0F ≡ (a ⊗ (` j)) ⊗ c)
            × (Fin.toℕ j ≡ syncs B₁′ + Fin.toℕ (Fin.zero {n = 1 + n}))
    tr₀ = canonₛ-head-triple b₁ B₁ (K `unit) (K `unit) 0F
    tr₁ : Σ[ a ∈ Tm (syncs B₂′ + (sA + (2 + n))) ] Σ[ c ∈ Tm (syncs B₂′ + (sA + (2 + n))) ]
          Σ[ j ∈ 𝔽 (syncs B₂′ + (sA + (2 + n))) ]
            (canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) 0F ≡ (a ⊗ (` j)) ⊗ c)
            × (Fin.toℕ j ≡ syncs B₂′ + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA (Fin.suc (Fin.zero {n = n}))))
    tr₁ = canonₛ-head-triple b₂ B₂ (K `unit) (K `unit) (weaken* ⦃ Kᵣ ⦄ sA 1F)
    tA0 tB0 tA1 tB1 : Tm (2 + (sB + (sA + n)))
    tA0 = rn (proj₁ tr₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tB0 = rn (proj₁ (proj₂ tr₀) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tA1 = rn (proj₁ tr₁)
    tB1 = rn (proj₁ (proj₂ tr₁))
    cc₀ cc₁ : Tm (2 + (sB + (sA + n)))
    cc₀ = (tA0 ⊗ (` 0F)) ⊗ tB0
    cc₁ = (tA1 ⊗ (` 1F)) ⊗ tB1
    rn-trip : (a c : Tm (sB + (sA + (2 + n)))) (j : 𝔽 (sB + (sA + (2 + n)))) →
              rn ((a ⊗ (` j)) ⊗ c) ≡ (rn a ⊗ (` (assocSwapᵣ sB 2 ((assocSwapᵣ sA 2 ↑* sB) j)))) ⊗ rn c
    rn-trip a c j = refl
    cc₀-eq : rn (τ 0F) ≡ cc₀
    cc₀-eq =
          cong rn (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ tr₀)))))
        ■ rn-trip (proj₁ tr₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ tr₀) ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀))))
        ■ cong (λ z → (tA0 ⊗ (` z)) ⊗ tB0)
            (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ tr₀))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ tr₀))))
    cc₁-eq : rn (τ yv) ≡ cc₁
    cc₁-eq =
          cong rn (τyv≡ ■ proj₁ (proj₂ (proj₂ (proj₂ tr₁))))
        ■ rn-trip (proj₁ tr₁) (proj₁ (proj₂ tr₁)) (proj₁ (proj₂ (proj₂ tr₁)))
        ■ cong (λ z → (tA1 ⊗ (` z)) ⊗ tB1)
            (Fin.toℕ-injective (assocPush-junc sA sB 1 (proj₁ (proj₂ (proj₂ tr₁))) jvtoℕ (Nat.s≤s (Nat.s≤s Nat.z≤n))))
      where
        jvtoℕ : Fin.toℕ (proj₁ (proj₂ (proj₂ tr₁))) ≡ sB + (sA + 1)
        jvtoℕ = proj₂ (proj₂ (proj₂ (proj₂ tr₁))) ■ cong (sB +_) (toℕ-weaken*ᵣ sA 1F)
    F₁ F₂ : Frame* (2 + (sB + (sA + n)))
    F₁ = (frame*-⋯ EE₁ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    F₂ = (frame*-⋯ EE₂ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ PP ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    eM : Tm (2 + (sB + (sA + n)))
    eM = rn (ee ⋯ τ)
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = (U.⟪ F₁ [ K `send ·¹ (eM ⊗ cc₀) ]* ⟫ U.∥ (U.⟪ F₂ [ K `recv ·¹ cc₁ ]* ⟫ U.∥ RP))
    contractumR : U.Proc (2 + (sB + (sA + n)))
    contractumR = (U.⟪ F₁ [ * ]* ⟫ U.∥ (U.⟪ F₂ [ eM ]* ⟫ U.∥ RP))
    VeM : Value eM
    VeM = (value-⋯ (V ⋯ᵛ wkρ) τ Vτ ⋯ᵛ ρ₁) ⋯ᵛ ρ₂
    comStep : U.ν redexL UR.─→ₚ U.ν contractumR
    comStep = UR.RU-Com F₁ F₂ VeM {e₁ = tA0} {e₁′ = tB0} {e₂ = tA1} {e₂′ = tB1}
    threadEq : (E : Frame* (sum B₁′ + sum B₂′ + m)) (p : Tm (sum B₁′ + sum B₂′ + m)) →
               (U[ T.⟪ E [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq E p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* E τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ E τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    thread₁≡ : (U[ T.⟪ EE₁ [ K `send ·¹ (ee ⊗ (` 0F)) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₁ [ K `send ·¹ (eM ⊗ cc₀) ]* ⟫
    thread₁≡ = threadEq EE₁ (K `send ·¹ (ee ⊗ (` 0F)))
             ■ cong (λ t → U.⟪ F₁ [ K `send ·¹ (eM ⊗ t) ]* ⟫) cc₀-eq
    thread₂≡ : (U[ T.⟪ EE₂ [ K `recv ·¹ (` yv) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₂ [ K `recv ·¹ cc₁ ]* ⟫
    thread₂≡ = threadEq EE₂ (K `recv ·¹ (` yv))
             ■ cong (λ t → U.⟪ F₂ [ K `recv ·¹ t ]* ⟫) cc₁-eq
    YL≡ : YL ≡ (U.⟪ F₁ [ K `send ·¹ (eM ⊗ cc₀) ]* ⟫ U.∥ U.⟪ F₂ [ K `recv ·¹ cc₁ ]* ⟫) U.∥ RP
    YL≡ = cong₂ U._∥_ (cong₂ U._∥_ thread₁≡ thread₂≡) refl
    frontL : U.ν YL U.≋ U.ν redexL
    frontL = U.ν-cong (≡→≋ YL≡ ◅◅ Eq*.symmetric _ U.∥-assoc)
    YR : U.Proc (2 + (sB + (sA + n)))
    YR = (U.⟪ F₁ [ * ]* ⟫ U.∥ U.⟪ F₂ [ eM ]* ⟫) U.∥ RP
    backR : U.ν contractumR U.≋ U.ν YR
    backR = U.ν-cong (U.∥-assoc ◅◅ ≡→≋ (sym YR≡))
      where
        YR≡ : YR ≡ (U.⟪ F₁ [ * ]* ⟫ U.∥ U.⟪ F₂ [ eM ]* ⟫) U.∥ RP
        YR≡ = refl
    leaf-fire : U.ν YL UR.─→ₚ U.ν YR
    leaf-fire = UR.RU-Struct frontL comStep backR
    fire : Bφ B₁′ (Bφ B₂′ (U.ν YL)) UR─→ₚ* Bφ B₁′ (Bφ B₂′ (U.ν YR))
    fire = Bφ-lift-step B₁′ (Bφ-lift-step B₂′ leaf-fire) ◅ ε
    QR : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)
    QR = (T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P
    sA≡ : syncs (b₁ ∷ B₁) ≡ sA
    sA≡ = syncs-cons-irrel b₁ (suc b₁) B₁
    sB≡ : syncs (b₂ ∷ B₂) ≡ sB
    sB≡ = syncs-cons-irrel b₂ (suc b₂) B₂
    τR : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n))
    τR = leafσ σ (b₁ ∷ B₁) (b₂ ∷ B₂)
    XR₀ : U.Proc (syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)))
    XR₀ = U[ QR ] τR
    eqAB : syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (sA + (2 + n))
    eqAB = cong₂ (λ u v → u + (v + (2 + n))) sB≡ sA≡
    XR : U.Proc (sB + (sA + (2 + n)))
    XR = subst U.Proc eqAB XR₀
    ν↓R : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
          U.ν (Bφ B₁′ (Bφ B₂′ X)) U.≋ Bφ B₁′ (Bφ B₂′ (U.ν (push X)))
    ν↓R X =
         ν-past-Bφ B₁′ (Bφ B₂′ X)
      ◅◅ Bφ-cong B₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B₂′ X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong B₁′ (ν-past-Bφ B₂′ (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    -- the RHS flatten, transported into the sA/sB (B₁′/B₂′) shape via the
    -- head-irrelevance of syncs and the head-irrelevance of the φ-prefix (drop).
    bridge-in : Bφ (b₂ ∷ B₂) XR₀
              ≡ Bφ B₂′ (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
    bridge-in = Bφ-suc-head≡ b₂' (suc b₂') B₂ XR₀
    flatR≡ : U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂) QR ] σ ≡ U.ν (Bφ B₁′ (Bφ B₂′ XR))
    flatR≡ =
        Uν-flat σ (b₁ ∷ B₁) (b₂ ∷ B₂) QR
      ■ cong U.ν
          ( Bφ-suc-head≡ b₁' (suc b₁') B₁ (Bφ (b₂ ∷ B₂) XR₀)
          ■ cong (Bφ B₁′) bridge2 )
      where
        subst-fn-≡ : ∀ {a a′} (e : a ≡ a′) {K} (Y : U.Proc (a + K)) →
                     subst (λ z → U.Proc (z + K)) e Y ≡ subst U.Proc (cong (_+ K) e) Y
        subst-fn-≡ refl Y = refl
        bridge2 : subst (λ z → U.Proc (z + (2 + n))) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)
                    (Bφ (b₂ ∷ B₂) XR₀)
                  ≡ Bφ B₂′ XR
        bridge2 =
            cong (subst (λ z → U.Proc (z + (2 + n))) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)) bridge-in
          ■ subst-fn-≡ (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁) (Bφ B₂′ (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀))
          ■ subst-Bφ (cong (_+ (2 + n)) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)) B₂′
              (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
          ■ cong (Bφ B₂′) substComp
          where
            q₁ : syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (syncs (b₁ ∷ B₁) + (2 + n))
            q₁ = cong (_+ (syncs (b₁ ∷ B₁) + (2 + n))) sB≡
            q₂ : sB + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (sA + (2 + n))
            q₂ = cong (syncs B₂′ +_) (cong (_+ (2 + n)) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁))
            substComp : subst U.Proc q₂
                          (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
                        ≡ subst U.Proc eqAB XR₀
            substComp =
                cong (subst U.Proc q₂) (subst-fn-≡ sB≡ XR₀)
              ■ subst-subst q₁ {q₂} {XR₀}
              ■ cong (λ e → subst U.Proc e XR₀) (≡-irrelevant (q₁ ■ q₂) eqAB)
    -- QL' : the contractum at the BIG scope = QR weakened by wkρ.
    QL' : T.Proc (sum B₁′ + sum B₂′ + m)
    QL' = (T.⟪ EE₁ [ K `unit ]* ⟫ T.∥ T.⟪ EE₂ [ ee ]* ⟫) T.∥ PP
    WR : U.Proc (sB + (sA + (2 + n)))
    WR = U[ QL' ] τ
    -- YR is the push of WR (the * / ee threads, frames carry the τ already).
    *⋯τ≡ : K `unit ⋯ τ ≡ K `unit
    *⋯τ≡ = refl
    rn*≡ : rn (K `unit ⋯ τ) ≡ K `unit
    rn*≡ = refl
    YR≡pushWR : YR ≡ push WR
    YR≡pushWR = cong₂ U._∥_
        (cong₂ U._∥_
          (sym (threadEq EE₁ (K `unit) ■ cong (λ t → U.⟪ F₁ [ t ]* ⟫) rn*≡))
          (sym (threadEq EE₂ ee)))
        refl
    -- QL' = QR ⋯ₚ wkρ  (the contractum weakening: *, ee, PP are the wkρ-images).
    QL'≡ : QL' ≡ QR T.⋯ₚ wkρ
    QL'≡ = cong₂ T._∥_
             (cong₂ T._∥_
               (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₁ wkρ)))
               (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₂ wkρ))))
             refl
    -- subst commutes through U[_] on the codomain.
    U-subst-cod : ∀ {c d} (eq : c ≡ d) (Q : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m))
                  (ρ : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ c) →
                  subst U.Proc eq (U[ Q ] ρ) ≡ U[ Q ] (subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eq ρ)
    U-subst-cod refl Q ρ = refl
    -- THE wkρ-cancellation: weakening then big leaf = (transported) small leaf.
    subst-σ-app : ∀ {c d D} (eq : c ≡ d) (ρ : D →ₛ c) (x : 𝔽 D) →
                  subst (λ z → D →ₛ z) eq ρ x ≡ subst Tm eq (ρ x)
    subst-σ-app refl ρ x = refl
    a₀ c₀ : ℕ
    a₀ = b₁ + sum B₁
    c₀ = b₂ + sum B₂
    -- wkρ acts as the head-slot insertion on each group: +1 below a₀, +2 at/above.
    -- inner: wkρ x = cast (((weakenᵣ ↑* suc a₀)) (cast (weakenᵣ x))); casts/weakenᵣ
    -- preserve/shift toℕ.  Express via weaken* 1 = (1 ↑ʳ_) on the inner weakenᵣ.
    wkₚ-step : (x : 𝔽 (a₀ + c₀ + m)) →
               Fin.toℕ (wkρ x)
               ≡ Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀) (Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))
    wkₚ-step x = Fin.toℕ-cast (sym (+-assoc (suc a₀) (suc c₀) m))
                   ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀) (Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))
    toℕ-wkρ-lt : (x : 𝔽 (a₀ + c₀ + m)) → Fin.toℕ x Nat.< a₀ → Fin.toℕ (wkρ x) ≡ suc (Fin.toℕ x)
    toℕ-wkρ-lt x lt =
        wkₚ-step x
      ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀) zc zclt
      ■ czN
      where
        zc = Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zclt : Fin.toℕ zc Nat.< suc a₀
        zclt = subst (Nat._< suc a₀) (sym czN) (Nat.s≤s lt)
    toℕ-wkρ-ge : (x : 𝔽 (a₀ + c₀ + m)) → a₀ Nat.≤ Fin.toℕ x → Fin.toℕ (wkρ x) ≡ 2 + Fin.toℕ x
    toℕ-wkρ-ge x ge =
        wkₚ-step x
      ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀) zc zcge
      ■ cong (suc a₀ +_) (toℕ-weaken*ᵣ 1 (Fin.reduce≥ zc zcge) ■ cong suc redN)
      ■ arith
      where
        zc = Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zcge : suc a₀ Nat.≤ Fin.toℕ zc
        zcge = subst (suc a₀ Nat.≤_) (sym czN) (Nat.s≤s ge)
        redN : Fin.toℕ (Fin.reduce≥ zc zcge) ≡ Fin.toℕ x Nat.∸ a₀
        redN = toℕ-reduce≥ zc zcge ■ cong (Nat._∸ suc a₀) czN ■ refl
        arith : suc a₀ + suc (Fin.toℕ x Nat.∸ a₀) ≡ 2 + Fin.toℕ x
        arith = cong suc (Nat.+-suc a₀ (Fin.toℕ x Nat.∸ a₀))
              ■ cong (λ z → suc (suc z)) (Nat.m+[n∸m]≡n ge)
    -- (wkρ ·ₖ τ) x = τ (wkρ x).
    compEq : (x : 𝔽 (a₀ + c₀ + m)) → (wkρ ·ₖ τ) x ≡ τ (wkρ x)
    compEq x = refl
    -- RHS subst pushed to Tm.
    rhsEq : (x : 𝔽 (a₀ + c₀ + m)) →
            subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eqAB τR x ≡ subst Tm eqAB (τR x)
    rhsEq x = subst-σ-app eqAB τR x
    -- the three region maps of wkρ, by Fin.toℕ-injective from toℕ-wkρ-lt/ge.
    wkρ-map-tail : (i : 𝔽 m) → wkρ ((a₀ + c₀) ↑ʳ i) ≡ (suc a₀ + suc c₀) ↑ʳ i
    wkρ-map-tail i = Fin.toℕ-injective
      ( toℕ-wkρ-ge ((a₀ + c₀) ↑ʳ i) geq
      ■ cong (2 +_) (Fin.toℕ-↑ʳ (a₀ + c₀) i)
      ■ sym (Fin.toℕ-↑ʳ (suc a₀ + suc c₀) i ■ arith) )
      where
        geq : a₀ Nat.≤ Fin.toℕ ((a₀ + c₀) ↑ʳ i)
        geq = subst (a₀ Nat.≤_) (sym (Fin.toℕ-↑ʳ (a₀ + c₀) i)) (Nat.≤-trans (Nat.m≤m+n a₀ c₀) (Nat.m≤m+n (a₀ + c₀) (Fin.toℕ i)))
        arith : suc a₀ + suc c₀ + Fin.toℕ i ≡ 2 + ((a₀ + c₀) + Fin.toℕ i)
        arith = solve 3 (λ A C I → con 1 :+ A :+ (con 1 :+ C) :+ I := con 2 :+ ((A :+ C) :+ I)) refl a₀ c₀ (Fin.toℕ i)
          where open +-*-Solver
    wkρ-leafσ : (wkρ ·ₖ τ) ≗ subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eqAB τR
    wkρ-leafσ x = compEq x ■ coreEq ■ sym (rhsEq x)
      where
        coreEq : τ (wkρ x) ≡ subst Tm eqAB (τR x)
        coreEq with Fin.splitAt (a₀ + c₀) x in eqo
        ... | inj₂ i =
              leafσ-tail σ B₁′ B₂′ (wkρ x) i splitWkρ
            ■ tailReconcile
          where
            x≡ : x ≡ (a₀ + c₀) ↑ʳ i
            x≡ = sym (Fin.splitAt⁻¹-↑ʳ eqo)
            wkρx≡ : wkρ x ≡ (suc a₀ + suc c₀) ↑ʳ i
            wkρx≡ = cong wkρ x≡ ■ wkρ-map-tail i
            splitWkρ : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₂ i
            splitWkρ = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                     ■ Fin.splitAt-↑ʳ (sum B₁′ + sum B₂′) m i
            -- syncs ignores the head, so the LHS/RHS differ only by the eqAB cast.
            tailReconcile :
              σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁′) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
              ≡ subst Tm eqAB (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
            tailReconcile = J-tail sB≡ sA≡
              where
                J-tail : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                       → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sb₁ ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                         ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                             (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                J-tail refl refl = refl
        ... | inj₁ z with Fin.splitAt a₀ z in eqi
        ...   | inj₁ j =
                  leafσ-A₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc j) splitWkρ-outer splitWkρ-inner
                ■ B₁reconcile
              where
                x≡ : x ≡ (j ↑ˡ c₀) ↑ˡ m
                x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ˡ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
                toℕj< : Fin.toℕ j Nat.< a₀
                toℕj< = Fin.toℕ<n j
                toℕx< : Fin.toℕ x Nat.< a₀
                toℕx< = subst (Nat._< a₀) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀) m ■ Fin.toℕ-↑ˡ j c₀)) toℕj<
                zB : 𝔽 (sum B₁′ + sum B₂′)
                zB = (Fin.suc j) ↑ˡ sum B₂′
                wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
                wkρx≡ = Fin.toℕ-injective
                  ( toℕ-wkρ-lt x toℕx<
                  ■ cong suc (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀) m ■ Fin.toℕ-↑ˡ j c₀)
                  ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ˡ (Fin.suc j) (sum B₂′) ) )
                splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
                splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                               ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
                splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₁ (Fin.suc j)
                splitWkρ-inner = Fin.splitAt-↑ˡ (sum B₁′) (Fin.suc j) (sum B₂′)
                B₁reconcile :
                  canonₛ B₁′ (K `unit , 0F , K `unit) (Fin.suc j) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
                  ≡ subst Tm eqAB (canonₛ (b₁ ∷ B₁) (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                B₁reconcile =
                    cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)) (canonₛ-suc-shift b₁ B₁ 0F (K `unit) j)
                  ■ J-A₁ sB≡ sA≡
                  where
                    ccA : UChan (2 + n)
                    ccA = (K `unit , 0F , K `unit)
                    J-A₁ : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                         → subst (λ z → Tm (z + (2 + n))) e₁ (canonₛ (b₁ ∷ B₁) ccA j) ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                           ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                               (canonₛ (b₁ ∷ B₁) ccA j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                    J-A₁ refl refl = refl
        ...   | inj₂ k =
                  leafσ-B₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc k) splitWkρ-outer splitWkρ-inner
                ■ B₂reconcile
              where
                x≡ : x ≡ (a₀ ↑ʳ k) ↑ˡ m
                x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ʳ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
                toℕx≥ : a₀ Nat.≤ Fin.toℕ x
                toℕx≥ = subst (a₀ Nat.≤_) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ k)) (Nat.m≤m+n a₀ (Fin.toℕ k))
                zB : 𝔽 (sum B₁′ + sum B₂′)
                zB = sum B₁′ ↑ʳ (Fin.suc k)
                wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
                wkρx≡ = Fin.toℕ-injective
                  ( toℕ-wkρ-ge x toℕx≥
                  ■ cong (2 +_) (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ k)
                  ■ arith
                  ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ʳ (sum B₁′) (Fin.suc k) ) )
                  where
                    arith : 2 + (a₀ + Fin.toℕ k) ≡ suc a₀ + suc (Fin.toℕ k)
                    arith = solve 2 (λ A K → con 2 :+ (A :+ K) := con 1 :+ A :+ (con 1 :+ K)) refl a₀ (Fin.toℕ k)
                      where open +-*-Solver
                splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
                splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                               ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
                splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₂ (Fin.suc k)
                splitWkρ-inner = Fin.splitAt-↑ʳ (sum B₁′) (sum B₂′) (Fin.suc k)
                ccB : ∀ (s : ℕ) → UChan (s + (2 + n))
                ccB s = (K `unit , weaken* ⦃ Kᵣ ⦄ s 1F , K `unit)
                B₂reconcile :
                  canonₛ B₂′ (ccB (syncs B₁′)) (Fin.suc k)
                  ≡ subst Tm eqAB (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
                B₂reconcile = J-B₂ sA≡
                  where
                    -- bridge the inner-scope flag arg from syncs(b₁∷B₁) to sA (= syncs B₁′),
                    -- absorbing the canonₛ-suc-shift outer subst (≡ sB≡ by ≡-irrelevance).
                    J-B₂ : ∀ {sb₁} (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                         → canonₛ (suc b₂ ∷ B₂) (ccB sb₁) (Fin.suc k)
                           ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ e₁)
                               (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
                    J-B₂ refl =
                        canonₛ-suc-shift b₂ B₂ (weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) 1F) (K `unit) k
                      ■ cong (λ e → subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e
                                      (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k))
                          (≡-irrelevant (syncs-cons-irrel b₂ (suc b₂) B₂) sB≡)
                      ■ substReshape
                      where
                        T₀ = canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k
                        substReshape :
                          subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ T₀
                          ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ refl) T₀
                        substReshape = subst-fn-≡′ sB≡ T₀
                          where
                            subst-fn-≡′ : ∀ {a a′} (e : a ≡ a′) (t : Tm (a + (syncs (b₁ ∷ B₁) + (2 + n)))) →
                                          subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e t
                                          ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e refl) t
                            subst-fn-≡′ refl t = refl
    WR≡XR : WR ≡ XR
    WR≡XR =
        cong (λ Q → U[ Q ] τ) QL'≡
      ■ U-⋯ₚ QR
      ■ U-cong QR wkρ-leafσ
      ■ sym (U-subst-cod eqAB QR τR)
    leafEq : YR ≡ push XR
    leafEq = YR≡pushWR ■ cong push WR≡XR
    back : Bφ B₁′ (Bφ B₂′ (U.ν YR)) U.≋ U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ
    back =
         Bφ-cong B₁′ (Bφ-cong B₂′ (U.ν-cong (≡→≋ leafEq)))
      ◅◅ Eq*.symmetric _ (ν↓R XR)
      ◅◅ ≡→≋ (sym flatR≡)
