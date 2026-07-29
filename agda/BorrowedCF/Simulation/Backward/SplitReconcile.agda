-- | Reconcile equality for the telescoped backward R-LSplit: the RU-LSplit
--   reduct `fired` equals `U[ ν C₁′ B QR ] σ`.  Extracted (duplicated) from the
--   forward SplitsH2.U-lsplit-step `back`/`bodyReconcile` chain; imports SplitsH2's
--   publics.  Zero forward-risk (append-only new module).
module BorrowedCF.Simulation.Backward.SplitReconcile where

open import BorrowedCF.Terms using (module SplitRenamings)

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.Support.SplitConfine using (lsplit-confine; rsplit-confine)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.Support.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ
        ; VChan; chanTriple-V; Value-subst; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.Support.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup; _;_⊢ₚ_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation.Support.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation.Support.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)

open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ public

open import BorrowedCF.Simulation.Support.Theorems.PhiTel
  using ( Btel; Bφ; UB-flatΦ; Uν-flatΦ; plugΦ-subst; plugΦ-++; _++Φ_
        ; widthΦ; toℕ-wkΦ; widthΦ-Btel; widthΦ-subst; widthΦ-++ )
open import BorrowedCF.Reduction.Processes.Untyped
  using (Φ*; []φ; _◂_; plugΦ; wkΦ; 𝓒[_×_×_])
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2
  using ( Bφ-lift-step; plugΦ-cong; Bφ-cong-c; subst-Bφ-c )
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2

module _ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {B₁ B₂ B : BindGroup} {q b₁ : ℕ} {s : 𝕊 0}
         (E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m))
         (P : T.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) where
  private module 𝐒 = SplitRenamings B₁ B₂ (sum B)
  C₁ C₁′ : BindGroup
  C₁  = B₁ ++ (q + suc b₁) ∷ B₂
  C₁′ = B₁ ++ (q + suc (suc b₁)) ∷ B₂
  QL : T.Proc (sum C₁ + sum B + m)
  QL = T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P
  QR : T.Proc (sum C₁′ + sum B + m)
  QR = T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.atk (q ↑ʳ 0F)) ⊗ (` 𝐒.atk (q ↑ʳ 1F)) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)
  sA sA′ sB : ℕ
  sA  = syncs C₁
  sA′ = syncs C₁′
  sB  = syncs B
  cc₁ : UChan (2 + n)
  cc₁ = (K `unit , 0F , K `unit)
  cc₂ : UChan (sA + (2 + n))
  cc₂ = (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit)
  τ : sum C₁ + sum B + m →ₛ sB + (sA + (2 + n))
  τ = leafσ σ C₁ B
  Vτ : VSub τ
  Vτ = ++ₛ-VSub
         (++ₛ-VSub
           (λ i → value-⋯ (VSub-canonₛ C₁ (K `unit , 0F , K `unit) (V-K , V-K) i)
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
           (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
         (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                   (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
  Φ_C₁ : Φ* (2 + n) (sA + (2 + n))
  Φ_C₁ = Btel C₁ cc₁
  Φ_B : Φ* (sA + (2 + n)) (sB + (sA + (2 + n)))
  Φ_B = Btel B cc₂
  Φfull : Φ* (2 + n) (sB + (sA + (2 + n)))
  Φfull = Φ_C₁ ++Φ Φ_B
  Fᶠ : Frame* (sB + (sA + (2 + n)))
  Fᶠ = frame*-⋯ E τ Vτ
  resid : U.Proc (sB + (sA + (2 + n)))
  resid = U[ P ] τ
  hc = canonₛ-handleq B₁ {N = 2 + n} (K `unit) 0F (K `unit) q b₁ B₂
  e₁L e₂L : Tm (sB + (sA + (2 + n)))
  e₁L = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB
  e₂L = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB
  slotL0 slotR0 : Tm (sB + (sA + (2 + n)))
  slotL0 = 𝓒[ e₁L × wkΦ Φfull 0F × * ]
  slotR0 = 𝓒[ * × wkΦ Φfull 0F × e₂L ]
  body : U.Proc (sB + (sA + (2 + n)))
  body = U.⟪ Fᶠ [ slotL0 ⊗ slotR0 ]* ⟫ U.∥ resid
  fired : U.Proc n
  fired = U.ν (plugΦ Φfull body)
  wr : widthΦ Φfull ≡ sA + sB
  wr = widthΦ-++ Φ_C₁ Φ_B ■ cong₂ _+_ (widthΦ-Btel C₁ cc₁) (widthΦ-Btel B cc₂)

  lsplit-back : ∀ {Γ : Ctx m} {γ : Struct m} → ChanCx Γ
              → Γ ; γ ⊢ₚ T.ν C₁ B QL → fired ≡ U[ T.ν C₁′ B QR ] σ
  lsplit-back Γ-S ⊢P with lsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  ... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq =
        cong U.ν (plugΦ-++ Φ_C₁ Φ_B body)
      ■ cong U.ν (Bφ-lwk B₁ cc₁ {q} {b₁} {B₂} (Bφ B cc₂ body))
      ■ cong (λ z → U.ν (Bφ C₁′ cc₁ z)) bodyReconcile
      ■ sym (Uν-flatΦ σ C₁′ B QR)
    where
      e1 : sA ≡ sA′
      e1 = syncs-lwkq B₁
      esA : sA + (2 + n) ≡ sA′ + (2 + n)
      esA = cong (_+ (2 + n)) e1
      cc₂′ : UChan (sA′ + (2 + n))
      cc₂′ = (K `unit , weaken* ⦃ Kᵣ ⦄ sA′ 1F , K `unit)
      τ′ : sum C₁′ + sum B + m →ₛ sB + (sA′ + (2 + n))
      τ′ = leafσ σ C₁′ B
      Vτ′ : VSub τ′
      Vτ′ = ++ₛ-VSub
              (++ₛ-VSub
                (λ i → value-⋯ (VSub-canonₛ C₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                          (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
                (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA′ 1F , K `unit) (V-K , V-K)))
              (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                        (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                        (weaken* ⦃ Kᵣ ⦄ sA′) (λ _ → V-`))
                        (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
      residR : U.Proc (sB + (sA′ + (2 + n)))
      residR = U[ P T.⋯ₚ 𝐒.lwk ] τ′
      Fᶠ′ : Frame* (sB + (sA′ + (2 + n)))
      Fᶠ′ = frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′
      hc′ = canonₛ-handleq B₁ {N = 2 + n} (K `unit) 0F (K `unit) q (suc b₁) B₂
      hb1 = canonₛ-handleq-b1 B₁ {N = 2 + n} (K `unit) 0F (K `unit) q b₁ B₂
      castpos′ : 𝔽 (sum C₁′)
      castpos′ = Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
      castpos1′ : 𝔽 (sum C₁′)
      castpos1′ = Fin.cast (sym (sum-++ B₁ ((q + suc (suc b₁)) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum B₂))
      τ′inj0 : τ′ (𝐒.atk (q ↑ʳ 0F)) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos′ ⋯ weaken* ⦃ Kᵣ ⦄ sB
      τ′inj0 =
          cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos′ ↑ˡ sum B) m)
        ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos′ (sum B))
      τ′inj1 : τ′ (𝐒.atk (q ↑ʳ 1F)) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos1′ ⋯ weaken* ⦃ Kᵣ ⦄ sB
      τ′inj1 =
          cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos1′ ↑ˡ sum B) m)
        ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos1′ (sum B))
      L-inv : subst Tm (cong (_+ (2 + n)) e1) (proj₁ hc) ≡ proj₁ hc′
      L-inv = handle-L-lwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂
      R0-* : proj₁ (proj₂ hc′) ≡ *
      R0-* = handle-R0-*q B₁ (K `unit) 0F (K `unit) q b₁ B₂
      R-corr : subst Tm (cong (_+ (2 + n)) e1) (proj₁ (proj₂ hc)) ≡ proj₁ (proj₂ hb1)
      R-corr = handle-R-lwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂
      L0-* : proj₁ hb1 ≡ *
      L0-* = handle-b1-L-*q B₁ (K `unit) 0F (K `unit) q b₁ B₂
      substσ-app : (h : ℕ → ℕ) {x yy : ℕ} (eq : x ≡ yy) {aa : ℕ} (ϱ : aa →ₛ h x) (i : 𝔽 aa) →
                   subst (λ j → aa →ₛ h j) eq ϱ i ≡ subst (λ j → Tm (h j)) eq (ϱ i)
      substσ-app h refl ϱ i = refl
      frameLeafeq : subst (λ j → Frame* (sB + (j + (2 + n)))) e1 (frame*-⋯ E τ Vτ)
                    ≡ frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′
      frameLeafeq =
          F-cod-transport E (λ j → sB + (j + (2 + n))) e1 Vτ
        ■ cong (λ EE → frame*-⋯ EE (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)
                          (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)) Eeq
        ■ F-⋯f*-fuse E₀ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)
                     (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
        ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
                         (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
            (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                 ■ leafσ-lwk-id σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y))
        ■ sym (F-⋯f*-fuse E₀ (·ₖ-VSubᵣ 𝐒.lwk Vτ′) (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′)))
        ■ cong (λ EE → frame*-⋯ EE (𝐒.lwk ·ₖ τ′) (·ₖ-VSubᵣ 𝐒.lwk Vτ′)) (sym Eeq)
        ■ sym (F-⋯f*-fuse E Vτ′ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
      Pleafeq : subst (λ j → U.Proc (sB + (j + (2 + n)))) e1 (U[ P ] τ) ≡ residR
      Pleafeq =
          U-cod-transport P (λ j → sB + (j + (2 + n))) e1 τ
        ■ cong (λ p → U[ p ] (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)) Peq
        ■ U-⋯ₚ P₀
        ■ U-cong P₀ (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                         ■ leafσ-lwk-id σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y))
        ■ sym (U-⋯ₚ P₀)
        ■ cong (λ p → U[ p ] (𝐒.lwk ·ₖ τ′)) (sym Peq)
        ■ sym (U-⋯ₚ P)
      leafSlot : (t : Tm (sA + (2 + n))) {t′ : Tm (sA′ + (2 + n))}
                 → subst Tm (cong (_+ (2 + n)) e1) t ≡ t′
                 → subst (λ j → Tm (sB + (j + (2 + n)))) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                   ≡ (t′ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      leafSlot t {t′} et = subst-wkB sB e1 t
                         ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+ e1 t) ■ et)
      juncEqTo : ∀ (jv : 𝔽 (sA′ + (2 + n))) → Fin.toℕ jv ≡ sA′ + 0 →
                 subst (λ j → Tm (sB + (j + (2 + n)))) e1 (` wkΦ Φfull 0F)
                 ≡ (` weaken* ⦃ Kᵣ ⦄ sB jv)
      juncEqTo jv jvto =
          subst-`Ff (λ j → sB + (j + (2 + n))) e1 (wkΦ Φfull 0F)
        ■ cong `_ (Fin.toℕ-injective
            ( toℕ-subst𝔽f (λ j → sB + (j + (2 + n))) e1 (wkΦ Φfull 0F)
            ■ toℕ-wkΦ Φfull 0F ■ Nat.+-identityʳ (widthΦ Φfull) ■ wr
            ■ cong (_+ sB) e1 ■ Nat.+-comm sA′ sB
            ■ sym (toℕ-weaken*ᵣ sB jv ■ cong (sB +_) (jvto ■ Nat.+-identityʳ sA′)) ))
      juncEq0 : subst (λ j → Tm (sB + (j + (2 + n)))) e1 (` wkΦ Φfull 0F)
                ≡ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′))))
      juncEq0 = juncEqTo (proj₁ (proj₂ (proj₂ hc′))) (proj₂ (proj₂ (proj₂ (proj₂ hc′))))
      juncEq1 : subst (λ j → Tm (sB + (j + (2 + n)))) e1 (` wkΦ Φfull 0F)
                ≡ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1))))
      juncEq1 = juncEqTo (proj₁ (proj₂ (proj₂ hb1))) (proj₂ (proj₂ (proj₂ (proj₂ hb1))))
      τ′inj0-shape : τ′ (𝐒.atk (q ↑ʳ 0F))
                   ≡ ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′))))) ⊗ *
      τ′inj0-shape = τ′inj0
                   ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc′))))
                   ■ cong (λ z → ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′))))) ⊗ z)
                       (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) R0-*)
      τ′inj1-shape : τ′ (𝐒.atk (q ↑ʳ 1F))
                   ≡ (* ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1))))) ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      τ′inj1-shape = τ′inj1
                   ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hb1))))
                   ■ cong (λ z → (z ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1))))) ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB))
                       (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) L0-*)
      slot0 : subst (λ j → Tm (sB + (j + (2 + n)))) e1 slotL0 ≡ τ′ (𝐒.atk (q ↑ʳ 0F))
      slot0 =
          subst-⊗f (λ j → sB + (j + (2 + n))) e1 (e₁L ⊗ (` wkΦ Φfull 0F)) *
        ■ cong₂ _⊗_
            ( subst-⊗f (λ j → sB + (j + (2 + n))) e1 e₁L (` wkΦ Φfull 0F)
            ■ cong₂ _⊗_ (leafSlot (proj₁ hc) L-inv) juncEq0 )
            (subst-*f (λ j → sB + (j + (2 + n))) e1)
        ■ sym τ′inj0-shape
      slot1 : subst (λ j → Tm (sB + (j + (2 + n)))) e1 slotR0 ≡ τ′ (𝐒.atk (q ↑ʳ 1F))
      slot1 =
          subst-⊗f (λ j → sB + (j + (2 + n))) e1 (* ⊗ (` wkΦ Φfull 0F)) e₂L
        ■ cong₂ _⊗_
            ( subst-⊗f (λ j → sB + (j + (2 + n))) e1 * (` wkΦ Φfull 0F)
            ■ cong₂ _⊗_ (subst-*f (λ j → sB + (j + (2 + n))) e1) juncEq1 )
            (leafSlot (proj₁ (proj₂ hc)) R-corr)
        ■ sym τ′inj1-shape
      slots : subst (λ j → Tm (sB + (j + (2 + n)))) e1 (slotL0 ⊗ slotR0)
              ≡ τ′ (𝐒.atk (q ↑ʳ 0F)) ⊗ τ′ (𝐒.atk (q ↑ʳ 1F))
      slots = subst-⊗f (λ j → sB + (j + (2 + n))) e1 slotL0 slotR0
            ■ cong₂ _⊗_ slot0 slot1
      bodyRshape : U[ QR ] τ′
                   ≡ U.⟪ Fᶠ′ [ τ′ (𝐒.atk (q ↑ʳ 0F)) ⊗ τ′ (𝐒.atk (q ↑ʳ 1F)) ]* ⟫ U.∥ residR
      bodyRshape = cong (λ z → U.⟪ z ⟫ U.∥ residR)
                     (frame-plug* (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′)
      leafReconcile′ : subst (λ j → U.Proc (sB + (j + (2 + n)))) e1 body ≡ U[ QR ] τ′
      leafReconcile′ =
          subst-∥f (λ j → sB + (j + (2 + n))) e1 (U.⟪ Fᶠ [ slotL0 ⊗ slotR0 ]* ⟫) resid
        ■ cong₂ U._∥_
            ( subst-⟪⟫f (λ j → sB + (j + (2 + n))) e1 (Fᶠ [ slotL0 ⊗ slotR0 ]*)
            ■ cong U.⟪_⟫ ( subst-frame-plug (λ j → sB + (j + (2 + n))) e1 Fᶠ (slotL0 ⊗ slotR0)
                          ■ cong₂ _[_]* frameLeafeq slots ) )
            Pleafeq
        ■ sym bodyRshape
      bodyReconcile : subst U.Proc esA (Bφ B cc₂ body) ≡ Bφ B cc₂′ (U[ QR ] τ′)
      bodyReconcile =
          subst-Bφ-c esA B cc₂ body
        ■ cong₂ (Bφ B) (subst-chan-wk1 e1 1F)
            ( cong (λ p → subst U.Proc p body) (uipℕ (cong (sB +_) esA) (cong (λ j → sB + (j + (2 + n))) e1))
            ■ substP-∘ (λ j → sB + (j + (2 + n))) e1 body
            ■ leafReconcile′ )
