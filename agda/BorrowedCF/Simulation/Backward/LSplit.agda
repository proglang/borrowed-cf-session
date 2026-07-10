-- | Backward simulation, RU-LSplit.  Reflects one untyped local-split step back
--   to a typed R-LSplit step in the CLEAN single-step codomain.  Ported from
--   BorrowedCF.Simulation.Support.RevLSplit (SplitRenamings moved to Terms and now takes
--   a `sum B`-shaped ℕ; the ⊎ cleanup slot of the codomain collapsed).
module BorrowedCF.Simulation.Backward.LSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Terms using (module SplitRenamings)
open import BorrowedCF.Simulation.Support.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; U-ν-singleton;
         frameApp-reflect; inv-U-ν-∥-shape; inv-ν-chanCx; ν-inj; close-arg-var)
open import BorrowedCF.Simulation.Support.InvFrame using (fn-lsplit-dom; strengthen-frame)
open import BorrowedCF.Simulation.Support.RevComImage using (com-image-block1)
open import BorrowedCF.Simulation.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2
  using (leafσ; leafσ-lwk-id; syncs-lwkq; canonₛ-handleq; canonₛ-handleq-b1;
         handle-L-lwkq; handle-R-lwkq; handle-R0-*q; handle-b1-L-*q; canonₛ;
         F-⋯f*-fuse; frame*-cong; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.TranslationProperties using (U-⋯ₚ; U-cong; ≡→≋)
open import BorrowedCF.Simulation.Support.SplitConfine using (lsplit-confine)
open import BorrowedCF.Simulation.Support.BlockPerm using (toℕ-weaken*ᵣ)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≋⇒≈)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m+[n∸m]≡n)
import Data.Sum as Sum
open TP using (BindGroup)
open import Data.Nat.ListAction.Properties using (sum-++)

lsplit-arg-chan : ∀ {N} {Γ : Ctx N} {α : Struct N} {s : 𝕊 0} {arg : Tm N} {T ϵ}
  → Γ ; α ⊢ K (`lsplit s) ·¹ arg ∶ T ∣ ϵ
  → Σ[ s′ ∈ 𝕊 0 ] Σ[ β ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ₂ ∈ Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) × (⟨ s ; s′ ⟩ ≃ R)
lsplit-arg-chan (T-AppUnr _ _ ⊢fn ⊢arg) = let s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
lsplit-arg-chan (T-AppLin _ _ ⊢fn ⊢arg) = let s′ , eq = fn-lsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
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
    module 𝐒 = SplitRenamings [] [] (sum (b₂ ∷ []))
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
      {F₀ : Frame* (sum C₁ + sum Bg + m)} {P₁t : TP.Proc (sum C₁ + sum Bg + m)}
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
    → Γ ; γ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)
    → F ≡ frame*-⋯ F₀ νσ0 Vνσ0
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
    → P₁ ≡ U[ P₁t ] νσ0
    → UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
      ≡ U[ TP.ν C₁' Bg (TP.⟪ F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]* ⟫ TP.∥ (P₁t TP.⋯ₚ slwk)) ] σ
  lsplit-recon Γ-S {s = s} {F₀ = F₀} {P₁t = P₁t} {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq
    with lsplit-confine Γ-S {B₁ = []} {B₂ = []} {B = b₂ ∷ []} {q = q} {b₁ = b₁'} {s = s} {E = F₀} {P = P₁t} ⊢P
  ... | _ , ρ⁻ , skipH , E₀ , Eeq , P₀ , Peq =
    cong UP.ν (cong₂ UP._∥_ threadEq restEq)
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

      Pleafeq : U[ P₁t ] νσ0 ≡ U[ P₁t TP.⋯ₚ slwk ] νσ1
      Pleafeq =
          cong (λ p → U[ p ] νσ0) Peq
        ■ U-⋯ₚ P₀
        ■ U-cong P₀ (λ y → lwk-id (ρ⁻ y) (skipH y))
        ■ sym (U-⋯ₚ P₀)
        ■ sym (U-⋯ₚ (P₀ TP.⋯ₚ ρ⁻))
        ■ cong (λ p → U[ p TP.⋯ₚ slwk ] νσ1) (sym Peq)

      e₁≡L0 : e₁ ≡ proj₁ hc ⋯ wk0
      e₁≡L0 = proj₁ (⊗-inj (proj₁ (⊗-inj (argeq ■ νσ0-tri))))
      e₂≡R0 : e₂ ≡ proj₁ (proj₂ hc) ⋯ wk0
      e₂≡R0 = proj₂ (⊗-inj (argeq ■ νσ0-tri))

      leaf-eq : ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂)
              ≡ ((` atkG0) ⊗ (` atkG1)) ⋯ νσ1
      leaf-eq = cong₂ (λ a b → ((a ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ b)) e₁≡L0 e₂≡R0
              ■ cong₂ _⊗_ (sym leafL) (sym leafR)

      threadEq : UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫
               ≡ UP.⟪ (F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]*) ⋯ νσ1 ⟫
      threadEq = cong UP.⟪_⟫
        ( cong₂ _[_]* (Feq ■ sym frameLeafeq) leaf-eq
        ■ sym (frame-plug* (F₀ ⋯ᶠ* slwk) νσ1 Vνσ1) )

      restEq : P₁ ≡ U[ P₁t TP.⋯ₚ slwk ] νσ1
      restEq = Resteq ■ Pleafeq

  lsplit-go :
    ∀ {Γ : Ctx m} (Γ-S : ChanCx Γ) {γ : Struct m} {s : 𝕊 0}
      (b₁ : ℕ) (b₁≡ : b₁ ≡ q + suc b₁')
      (z : 𝔽 (b₁ + 0)) (toℕz≡q : Fin.toℕ z ≡ q)
      {F₀ : Frame* (sum (b₁ ∷ []) + sum Bg + m)}
      {P₁t : TP.Proc (sum (b₁ ∷ []) + sum Bg + m)}
      {argᴸ : Tm (sum (b₁ ∷ []) + sum Bg + m)}
      (argᴸ≡ : argᴸ ≡ (` ((z ↑ˡ sum Bg) ↑ˡ m)))
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
    → Γ ; γ ⊢ₚ TP.ν (b₁ ∷ []) Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)
    → F ≡ frame*-⋯ F₀ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ argᴸ ⋯ νσ b₁ b₂ σ
    → P₁ ≡ U[ P₁t ] (νσ b₁ b₂ σ)
    → Σ[ P′ ∈ TP.Proc m ]
        (Star TR._─→ₚ_
           (TP.ν (b₁ ∷ []) Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)) P′)
      × ((UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)) ≈ U[ P′ ] σ)
  lsplit-go Γ-S {s = s} b₁ refl z toℕz≡q {F₀ = F₀} {P₁t = P₁t} {argᴸ = argᴸ} argᴸ≡
            {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq =
    P′ , step , ≋⇒≈ (≡→≋ recon)
    where
      P′ : TP.Proc m
      P′ = TP.ν C₁' Bg (TP.⟪ F₀ ⋯ᶠ* slwk [ (` atkG0) ⊗ (` atkG1) ]* ⟫ TP.∥ (P₁t TP.⋯ₚ slwk))

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

      ⊢P' : _ ; _ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)
      ⊢P' = subst (λ v → _ ; _ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ v ]* ⟫ TP.∥ P₁t))
              argᴸ≡atkU ⊢P

      argeq' : ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
      argeq' = argeq ■ cong (λ v → v ⋯ νσ0) argᴸ≡atkU

      recon : UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
              ≡ U[ P′ ] σ
      recon = lsplit-recon Γ-S ⊢P' Feq argeq' Resteq

      stepAtk : Star TR._─→ₚ_
                  (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)) P′
      stepAtk = TR.R-LSplit {B₁ = []} {B₂ = []} {B = Bg} {q = q} {b₁ = b₁'} {s = s} {P = P₁t} {E = F₀} ◅ ε

      step : Star TR._─→ₚ_
               (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)) P′
      step = subst (λ v → Star TR._─→ₚ_
                     (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`lsplit s) ·¹ v ]* ⟫ TP.∥ P₁t)) P′)
               (sym argᴸ≡atkU) stepAtk

-- RU-LSplit reflection.  Interface mirrors Backward.Leaf.bwd-fork: the untyped
-- redex is presented as its frame F plus the equation  U[ P ] σ ≡ (RU-LSplit LHS);
-- the result is the (RU-LSplit RHS) ≈-bridged to U[ P′ ] σ.  Wired at
-- Backward.agda:118 by  lsplit-reflect σ Vσ Γ-S ⊢P (sym eq).
lsplit-reflect : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
               → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
               → {s : 𝕊 0} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
                 {F : Frame* (2 + n)}
               → U[ P ] σ ≡ UP.ν (UP.⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
               → Σ[ P′ ∈ TP.Proc m ]
                   (Star TR._─→ₚ_ P P′
                    × UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
                        ≈ U[ P′ ] σ)
lsplit-reflect σ Vσ Γ-S {P = P} ⊢P {s = s} {F = F} eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PL , P₁t , refl , Leq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢P₁t ← inv-∥ ⊢body
  with F₀ , argᴸ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`lsplit s)
           F (sym Leq′)
  with _ , (_ , _ , ⊢plug) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢PL)
  with _ , _ , _ , _ , ⊢argᴸ , ch ← lsplit-arg-chan ⊢plug
  with x , argᴸ≡ ← close-arg-var argᴸ ⊢argᴸ ch (νσ b₁ b₂ σ) (sym argeq)
  with z , _ , xeq ← com-image-block1 b₁ b₂ σ Vσ x (argeq ■ cong (_⋯ νσ b₁ b₂ σ) argᴸ≡)
  with b₁' , b₁≡ ← fin-split b₁ z =
  lsplit-go σ Vσ (Fin.toℕ z) b₁' b₂ Γ-S b₁ b₁≡ z refl
    (argᴸ≡ ■ cong `_ xeq) ⊢P Feq argeq Resteq
