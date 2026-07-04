module BorrowedCF.Simulation.RevLSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.ReverseInv using (νσ; ⊗-inj; νσ-VSub; U-ν-singleton)
open import BorrowedCF.Simulation.Theorems.SplitsH2
  using (leafσ; leafσ-lwk-id; syncs-lwkq; canonₛ-handleq; canonₛ-handleq-b1;
         handle-L-lwkq; handle-R-lwkq; handle-R0-*q; handle-b1-L-*q; canonₛ;
         F-⋯f*-fuse; frame*-cong; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.TranslationProperties using (U-⋯ₚ; U-cong; ≡→≋)
open import BorrowedCF.Simulation.SplitConfine using (lsplit-confine)
open import BorrowedCF.Simulation.InvFrame using (fn-lsplit-dom)
open import BorrowedCF.Simulation.BlockPerm using (toℕ-weaken*ᵣ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m+[n∸m]≡n)
import Data.Sum as Sum
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open T using (BindGroup; _;_⊢ₚ_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

lsplit-arg-chan : ∀ {N} {Γ : Ctx N} {α : Struct N} {s : 𝕊 0} {arg : Tm N} {T ϵ}
  → Γ ; α ⊢ K (`lsplit s) ·¹ arg ∶ T ∣ ϵ
  → Σ[ s′ ∈ 𝕊 0 ] Σ[ β ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ₂ ∈ Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) × (⟨ s ; s′ ⟩ ≃ R)
lsplit-arg-chan (T-AppUnr _ _ ⊢fn ⊢arg) = let _ , s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
lsplit-arg-chan (T-AppLin _ _ ⊢fn ⊢arg) = let _ , s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
lsplit-arg-chan (T-Conv _ _ d) = lsplit-arg-chan d
lsplit-arg-chan (T-Weaken _ d) = lsplit-arg-chan d

fin-split : (k : ℕ) (z : 𝔽 (k + 0)) → Σ[ b₁' ∈ ℕ ] (k ≡ Fin.toℕ z + suc b₁')
fin-split k z = k Nat.∸ suc (Fin.toℕ z) , sym (+-suc q (k Nat.∸ suc q) ■ m+[n∸m]≡n q<k)
  where
    q = Fin.toℕ z
    q<k : suc q Nat.≤ k
    q<k = subst (suc q Nat.≤_) (+-identityʳ k) (toℕ<n z)

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) (q b₁' b₂ : ℕ) where

  private
    module 𝐒 = TR.SplitRenamings [] [] (b₂ ∷ [])
    slwk = 𝐒.lwk {q = q} {b = b₁'} {n = m}
    C₁ C₁' : BindGroup
    C₁  = (q + suc b₁') ∷ []
    C₁' = (q + suc (suc b₁')) ∷ []
    Bg : BindGroup
    Bg  = b₂ ∷ []

    νσ0 : sum C₁ + sum Bg + m →ₛ 2 + n
    νσ0 = νσ (q + suc b₁') b₂ σ
    νσ1 : sum C₁' + sum Bg + m →ₛ 2 + n
    νσ1 = νσ (q + suc (suc b₁')) b₂ σ

    atkU  : 𝔽 (sum C₁ + sum Bg + m)
    atkU  = 𝐒.atk {q + suc b₁'} {m} (q ↑ʳ 0F)
    atkG0 : 𝔽 (sum C₁' + sum Bg + m)
    atkG0 = 𝐒.atk {q + suc (suc b₁')} {m} (q ↑ʳ 0F)
    atkG1 : 𝔽 (sum C₁' + sum Bg + m)
    atkG1 = 𝐒.atk {q + suc (suc b₁')} {m} (q ↑ʳ 1F)

    castposU : 𝔽 (sum C₁)
    castposU = Fin.cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
    castposG0 : 𝔽 (sum C₁')
    castposG0 = Fin.cast (sym (sum-++ [] C₁')) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
    castposG1 : 𝔽 (sum C₁')
    castposG1 = Fin.cast (sym (sum-++ [] C₁')) (sum [] ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum []))

    atkeqU : νσ0 atkU ≡ canonₛ C₁ (K `unit , 0F , K `unit) castposU ⋯ weaken* ⦃ Kᵣ ⦄ 0
    atkeqU = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum Bg) (castposU ↑ˡ sum Bg) m)
           ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castposU (sum Bg))

    atkeqG0 : νσ1 atkG0 ≡ canonₛ C₁' (K `unit , 0F , K `unit) castposG0 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    atkeqG0 = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum Bg) (castposG0 ↑ˡ sum Bg) m)
            ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁') castposG0 (sum Bg))

    atkeqG1 : νσ1 atkG1 ≡ canonₛ C₁' (K `unit , 0F , K `unit) castposG1 ⋯ weaken* ⦃ Kᵣ ⦄ 0
    atkeqG1 = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁' + sum Bg) (castposG1 ↑ˡ sum Bg) m)
            ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁') castposG1 (sum Bg))

    wk0 : (2 + n) →ᵣ (0 + (2 + n))
    wk0 = weaken* ⦃ Kᵣ ⦄ 0

    hc  = canonₛ-handleq   [] {2 + n} (K `unit) 0F (K `unit) q b₁'        []
    hc' = canonₛ-handleq   [] {2 + n} (K `unit) 0F (K `unit) q (suc b₁') []
    hb1 = canonₛ-handleq-b1 [] {2 + n} (K `unit) 0F (K `unit) q b₁'       []

    L0 R0 : Tm (0 + (2 + n))
    L0 = proj₁ hc ⋯ wk0
    R0 = proj₁ (proj₂ hc) ⋯ wk0

    junc0 : (j : 𝔽 (syncs C₁ + (2 + n))) → Fin.toℕ j ≡ 0 → weaken* ⦃ Kᵣ ⦄ 0 j ≡ 0F
    junc0 j tj = Fin.toℕ-injective (toℕ-weaken*ᵣ 0 j ■ tj)

    junc0' : (j : 𝔽 (syncs C₁' + (2 + n))) → Fin.toℕ j ≡ 0 → weaken* ⦃ Kᵣ ⦄ 0 j ≡ 0F
    junc0' j tj = Fin.toℕ-injective (toℕ-weaken*ᵣ 0 j ■ tj)

  -- ungrown handle triple: 𝓒[ L0 × 0F × R0 ].
  νσ0-tri : νσ0 atkU ≡ ((proj₁ hc ⋯ wk0) ⊗ (` 0F)) ⊗ (proj₁ (proj₂ hc) ⋯ wk0)
  νσ0-tri = atkeqU
          ■ cong (_⋯ wk0) (proj₁ (proj₂ (proj₂ (proj₂ hc))))
          ■ cong (λ z → ((proj₁ hc ⋯ wk0) ⊗ (` z)) ⊗ (proj₁ (proj₂ hc) ⋯ wk0))
              (junc0 (proj₁ (proj₂ (proj₂ hc))) (proj₂ (proj₂ (proj₂ (proj₂ hc)))))

  -- grown borrow-0 triple: 𝓒[ L0 × 0F × * ].
  leafL : νσ1 atkG0 ≡ ((proj₁ hc ⋯ wk0) ⊗ (` 0F)) ⊗ (K `unit)
  leafL = atkeqG0
        ■ cong (_⋯ wk0) (proj₁ (proj₂ (proj₂ (proj₂ hc'))))
        ■ cong (λ z → ((proj₁ hc' ⋯ wk0) ⊗ (` z)) ⊗ (proj₁ (proj₂ hc') ⋯ wk0))
            (junc0' (proj₁ (proj₂ (proj₂ hc'))) (proj₂ (proj₂ (proj₂ (proj₂ hc')))))
        ■ cong₂ (λ L R → (L ⊗ (` 0F)) ⊗ R)
            (cong (_⋯ wk0) (sym (handle-L-lwkq [] (K `unit) 0F (K `unit) q b₁' [])))
            (cong (_⋯ wk0) (handle-R0-*q [] (K `unit) 0F (K `unit) q b₁' []))

  -- grown borrow-1 triple: 𝓒[ * × 0F × R0 ].
  leafR : νσ1 atkG1 ≡ ((K `unit) ⊗ (` 0F)) ⊗ (proj₁ (proj₂ hc) ⋯ wk0)
  leafR = atkeqG1
        ■ cong (_⋯ wk0) (proj₁ (proj₂ (proj₂ (proj₂ hb1))))
        ■ cong (λ z → ((proj₁ hb1 ⋯ wk0) ⊗ (` z)) ⊗ (proj₁ (proj₂ hb1) ⋯ wk0))
            (junc0' (proj₁ (proj₂ (proj₂ hb1))) (proj₂ (proj₂ (proj₂ (proj₂ hb1)))))
        ■ cong₂ (λ L R → (L ⊗ (` 0F)) ⊗ R)
            (cong (_⋯ wk0) (handle-b1-L-*q [] (K `unit) 0F (K `unit) q b₁' []))
            (cong (_⋯ wk0) (sym (handle-R-lwkq [] (K `unit) 0F (K `unit) q b₁' [])))

  private
    Vνσ0 : VSub νσ0
    Vνσ0 = νσ-VSub (q + suc b₁') b₂ σ Vσ
    Vνσ1 : VSub νσ1
    Vνσ1 = νσ-VSub (q + suc (suc b₁')) b₂ σ Vσ

  lsplit-recon :
    ∀ {Γ : Ctx m} (Γ-S : ChanCx Γ) {γ : Struct m} {s : 𝕊 0}
      {F₀ : Frame* (sum C₁ + sum Bg + m)} {P₁t : T.Proc (sum C₁ + sum Bg + m)}
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : U.Proc (2 + n)}
    → Γ ; γ ⊢ₚ T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ T.∥ P₁t)
    → F ≡ frame*-⋯ F₀ νσ0 Vνσ0
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
    → P₁ ≡ U[ P₁t ] νσ0
    → U.ν (U.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ U.∥ P₁)
      ≡ U[ T.ν C₁' Bg (T.⟪ F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]* ⟫ T.∥ (P₁t T.⋯ₚ slwk)) ] σ
  lsplit-recon Γ-S {s = s} {F₀ = F₀} {P₁t = P₁t} {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq
    with lsplit-confine Γ-S {B₁ = []} {B₂ = []} {B = b₂ ∷ []} {q = q} {b₁ = b₁'} {s = s} {E = F₀} {P = P₁t} ⊢P
  ... | _ , ρ⁻ , skipH , E₀ , Eeq , P₀ , Peq =
    cong U.ν (cong₂ U._∥_ threadEq restEq)
    where
      lwk-id : (i : 𝔽 (sum C₁ + sum Bg + m)) → i ≢ atkU → νσ0 i ≡ νσ1 (slwk i)
      lwk-id i i≢ = leafσ-lwk-id σ [] [] (b₂ ∷ []) q b₁' i i≢

      frameLeafeq : frame*-⋯ (F₀ ⋯ᶠ* slwk) νσ1 Vνσ1 ≡ frame*-⋯ F₀ νσ0 Vνσ0
      frameLeafeq =
          cong (λ E → frame*-⋯ (E ⋯ᶠ* slwk) νσ1 Vνσ1) Eeq
        ■ F-⋯f*-fuse (E₀ ⋯ᶠ* ρ⁻) {ρ = slwk} {τ = νσ1} Vνσ1 (·ₖ-VSubᵣ slwk Vνσ1)
        ■ F-⋯f*-fuse E₀ {ρ = ρ⁻} {τ = slwk ·ₖ νσ1} (·ₖ-VSubᵣ slwk Vνσ1)
             (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ slwk Vνσ1))
        ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ slwk Vνσ1)) (·ₖ-VSubᵣ ρ⁻ Vνσ0)
            (λ y → sym (lwk-id (ρ⁻ y) (skipH y)))
        ■ sym (F-⋯f*-fuse E₀ {ρ = ρ⁻} {τ = νσ0} Vνσ0 (·ₖ-VSubᵣ ρ⁻ Vνσ0))
        ■ cong (λ E → frame*-⋯ E νσ0 Vνσ0) (sym Eeq)

      Pleafeq : U[ P₁t ] νσ0 ≡ U[ P₁t T.⋯ₚ slwk ] νσ1
      Pleafeq =
          cong (λ p → U[ p ] νσ0) Peq
        ■ U-⋯ₚ P₀
        ■ U-cong P₀ (λ y → lwk-id (ρ⁻ y) (skipH y))
        ■ sym (U-⋯ₚ P₀)
        ■ sym (U-⋯ₚ (P₀ T.⋯ₚ ρ⁻))
        ■ cong (λ p → U[ p T.⋯ₚ slwk ] νσ1) (sym Peq)

      e₁≡L0 : e₁ ≡ proj₁ hc ⋯ wk0
      e₁≡L0 = proj₁ (⊗-inj (proj₁ (⊗-inj (argeq ■ νσ0-tri))))
      e₂≡R0 : e₂ ≡ proj₁ (proj₂ hc) ⋯ wk0
      e₂≡R0 = proj₂ (⊗-inj (argeq ■ νσ0-tri))

      leaf-eq : ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂)
              ≡ ((` atkG0) ⊗ (` atkG1)) ⋯ νσ1
      leaf-eq = cong₂ (λ a b → ((a ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ b)) e₁≡L0 e₂≡R0
              ■ cong₂ _⊗_ (sym leafL) (sym leafR)

      threadEq : U.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫
               ≡ U.⟪ (F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]*) ⋯ νσ1 ⟫
      threadEq = cong U.⟪_⟫
        ( cong₂ _[_]* (Feq ■ sym frameLeafeq) leaf-eq
        ■ sym (frame-plug* (F₀ ⋯ᶠ* slwk) νσ1 Vνσ1) )

      restEq : P₁ ≡ U[ P₁t T.⋯ₚ slwk ] νσ1
      restEq = Resteq ■ Pleafeq

  lsplit-go :
    ∀ {Γ : Ctx m} (Γ-S : ChanCx Γ) {γ : Struct m} {s : 𝕊 0}
      (b₁ : ℕ) (b₁≡ : b₁ ≡ q + suc b₁')
      (z : 𝔽 (b₁ + 0)) (toℕz≡q : Fin.toℕ z ≡ q)
      {F₀ : Frame* (sum (b₁ ∷ []) + sum Bg + m)}
      {P₁t : T.Proc (sum (b₁ ∷ []) + sum Bg + m)}
      {argᴸ : Tm (sum (b₁ ∷ []) + sum Bg + m)}
      (argᴸ≡ : argᴸ ≡ (` ((z ↑ˡ sum Bg) ↑ˡ m)))
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : U.Proc (2 + n)}
    → Γ ; γ ⊢ₚ T.ν (b₁ ∷ []) Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ T.∥ P₁t)
    → F ≡ frame*-⋯ F₀ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ argᴸ ⋯ νσ b₁ b₂ σ
    → P₁ ≡ U[ P₁t ] (νσ b₁ b₂ σ)
    → Σ[ P′ ∈ T.Proc m ] Σ[ Q′ ∈ U.Proc n ]
        (Star TR._─→ₚ_
           (T.ν (b₁ ∷ []) Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ T.∥ P₁t)) P′)
      × ( ((U.ν (U.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ U.∥ P₁)) ≡ Q′)
          Sum.⊎
          ((U.ν (U.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ U.∥ P₁)) UR.─→ₚ Q′) )
      × (Q′ ≈ U[ P′ ] σ)
  lsplit-go Γ-S {s = s} b₁ refl z toℕz≡q {F₀ = F₀} {P₁t = P₁t} {argᴸ = argᴸ} argᴸ≡
            {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq =
    P′ , _ , step , Sum.inj₁ refl , ≋⇒≈ (≡→≋ recon)
    where
      P′ : T.Proc m
      P′ = T.ν C₁' Bg (T.⟪ F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]* ⟫ T.∥ (P₁t T.⋯ₚ slwk))

      castposU-toℕ : Fin.toℕ castposU ≡ q
      castposU-toℕ =
          toℕ-cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
        ■ toℕ-↑ˡ (q ↑ʳ 0F) (sum [])
        ■ toℕ-↑ʳ q 0F
        ■ +-identityʳ q

      z≡ : z ≡ castposU
      z≡ = toℕ-injective (toℕz≡q ■ sym castposU-toℕ)

      argᴸ≡atkU : argᴸ ≡ (` atkU)
      argᴸ≡atkU = argᴸ≡ ■ cong (λ w → (` ((w ↑ˡ sum Bg) ↑ˡ m))) z≡

      ⊢P' : _ ; _ ⊢ₚ T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ T.∥ P₁t)
      ⊢P' = subst (λ v → _ ; _ ⊢ₚ T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ v ]* ⟫ T.∥ P₁t))
              argᴸ≡atkU ⊢P

      argeq' : ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
      argeq' = argeq ■ cong (λ v → v ⋯ νσ0) argᴸ≡atkU

      recon : U.ν (U.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ U.∥ P₁)
              ≡ U[ P′ ] σ
      recon = lsplit-recon Γ-S ⊢P' Feq argeq' Resteq

      stepAtk : Star TR._─→ₚ_
                  (T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ T.∥ P₁t)) P′
      stepAtk = TR.R-LSplit {B₁ = []} {B₂ = []} {B = Bg} {q = q} {b₁ = b₁'} {s = s} {P = P₁t} {E = F₀} ◅ ε

      step : Star TR._─→ₚ_
               (T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ T.∥ P₁t)) P′
      step = subst (λ v → Star TR._─→ₚ_
                     (T.ν C₁ Bg (T.⟪ F₀ [ K (`lsplit s) ·¹ v ]* ⟫ T.∥ P₁t)) P′)
               (sym argᴸ≡atkU) stepAtk
