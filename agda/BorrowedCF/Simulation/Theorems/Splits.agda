module BorrowedCF.Simulation.Theorems.Splits where

-- | Forward-simulation cases R-LSplit and R-RSplit for the reworked
--   paper-matching process definitions.  Exports U-lsplit and U-rsplit.
--
--   The route mirrors the (un-importable, hole-gated) Simulation2.Congruence
--   transpose engine: U[ ν (B₁++suc b₁∷B₂) B (…) ]σ flattens (Uν-flat) to
--   ν (Bφ 𝔅 (Bφ B (leaf))); the outer ν is pushed past both φ-nests to the
--   leaf (ν-past-Bφ), RU-LSplit/RU-RSplit fires on the leaf ν, then the ν is
--   pulled back out.  The transpose engine (Bφ/canonₛ/ν-past-Bφ/Bφ-transpose…)
--   is COPIED here verbatim from Congruence's hole-free prefix because
--   Congruence carries open interaction metas downstream and is unimportable.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.SplitConfine using (lsplit-confine; rsplit-confine)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ
        ; VChan; chanTriple-V; Value-subst; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)

open T using (_;_⊢ₚ_)
open import BorrowedCF.Simulation.Theorems.SplitsH3 public

U-rsplit : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {B₁ B₂ B : BindGroup} {b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → {P : T.Proc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     Γ ; γ ⊢ₚ T.ν (B₁ ++ suc b₁ ∷ B₂) B
                 (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P))
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       UR─→ₚ*
      U[ T.ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)) ] σ)
     ⊎
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       U.≋
      U[ T.ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)) ] σ))
U-rsplit {m} {n} σ Vσ Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with rsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq =
      inj₁ (wrapNE front (Bφ-lift-step C₁ (Bφ-lift-step B leaf-fire)) ε back)
  where
    module 𝐒 = TR.SplitRenamings B₁ B₂ B
    C₁ C₁ᴿ : BindGroup
    C₁  = B₁ ++ suc b₁ ∷ B₂
    C₁ᴿ = B₁ ++ 1 ∷ suc b₁ ∷ B₂
    QL : T.Proc (sum C₁ + sum B + m)
    QL = T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P
    QR : T.Proc (sum C₁ᴿ + sum B + m)
    QR = T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)
    sA sAᴿ sB : ℕ
    sA  = syncs C₁
    sAᴿ = syncs C₁ᴿ
    sB  = syncs B
    τ : sum C₁ + sum B + m →ₛ syncs B + (syncs C₁ + (2 + n))
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
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    push : ∀ {kk} → U.Proc (sB + (sA + (2 + kk))) → U.Proc (2 + (sB + (sA + kk)))
    push {kk} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    XL : U.Proc (sB + (sA + (2 + n)))
    XL = U[ QL ] τ
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ C₁ (Bφ B X)) U.≋ Bφ C₁ (Bφ B (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ C₁ (Bφ B X)
      ◅◅ Bφ-cong C₁ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong C₁ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν C₁ B QL ] σ U.≋ Bφ C₁ (Bφ B (U.ν (push XL)))
    front = ≡→≋ (Uν-flat σ C₁ B QL) ◅◅ ν↓ XL
    castpos : 𝔽 (sum C₁)
    castpos = Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
    hc = canonₛ-handle B₁ (K `unit) 0F (K `unit) b₁ B₂
    cc : Tm (2 + (sB + (sA + n)))
    cc = rn (τ (𝐒.inj 0F))
    τinj0 : τ (𝐒.inj 0F) ≡ canonₛ C₁ (K `unit , 0F , K `unit) castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τinj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
    ccTriple : cc ≡ ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` 0F))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
    ccTriple =
        cong rn (τinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc)))))
      ■ cong (λ z → ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` z))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂))
          (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc))))
    Fr : Frame* (2 + (sB + (sA + n)))
    Fr = (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ P ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    threadEq : (Ef : Frame* (sum C₁ + sum B + m)) (p : Tm (sum C₁ + sum B + m)) →
               (U[ T.⟪ Ef [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* Ef τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ Ef τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    YL≡ : push XL ≡ U.⟪ Fr [ K (`rsplit s) ·¹ cc ]* ⟫ U.∥ RP
    YL≡ = cong₂ U._∥_
            (threadEq E (K (`rsplit s) ·¹ (` 𝐒.inj 0F)))
            refl
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = U.⟪ Fr [ K (`rsplit s) ·¹ cc ]* ⟫ U.∥ RP
    -- the two non-junction components of the handle triple cc = (ccA ⊗ ` 0F) ⊗ ccC.
    ccA ccC : Tm (2 + (sB + (sA + n)))
    ccA = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccC = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccEq : cc ≡ UR.𝓒[ ccA × 0F × ccC ]
    ccEq = ccTriple
    -- RU-RSplit contractum: fresh φ drop, frame/P weakened by weakenᵣ, two distinct triples.
    contractumR : U.Proc (1 + (2 + (sB + (sA + n))))
    contractumR = U.⟪ (Fr ⋯ᶠ* weakenᵣ) [ UR.𝓒[ wk ccA × 1F × ` 0F ] ⊗ UR.𝓒[ ` 0F × 1F × wk ccC ] ]* ⟫
                    U.∥ (RP U.⋯ₚ weakenᵣ)
    rsplitStep : U.ν redexL UR.─→ₚ U.ν (U.φ U.drop contractumR)
    rsplitStep = subst (λ z → U.ν (U.⟪ Fr [ K (`rsplit s) ·¹ z ]* ⟫ U.∥ RP)
                              UR.─→ₚ
                              U.ν (U.φ U.drop contractumR))
                   (sym ccEq)
                   (UR.RU-RSplit {e₁ = ccA} {e₂ = ccC} Fr)
    leaf-fire : U.ν (push XL) UR.─→ₚ U.ν (U.φ U.drop contractumR)
    leaf-fire = UR.RU-Struct (U.ν-cong (≡→≋ YL≡)) rsplitStep ε
    -- ----- grown-group (RHS) flatten side -----
    τᴿ : sum C₁ᴿ + sum B + m →ₛ syncs B + (syncs C₁ᴿ + (2 + n))
    τᴿ = leafσ σ C₁ᴿ B
    Vτᴿ : VSub τᴿ
    Vτᴿ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁ᴿ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sAᴿ 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sAᴿ) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    XRᴿ : U.Proc (sB + (sAᴿ + (2 + n)))
    XRᴿ = U[ QR ] τᴿ
    pushR : ∀ {kk} → U.Proc (sB + (sAᴿ + (2 + kk))) → U.Proc (2 + (sB + (sAᴿ + kk)))
    pushR {kk} X = (X U.⋯ₚ (assocSwapᵣ sAᴿ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ν↓ᴿ : ∀ (X : U.Proc (sB + (sAᴿ + (2 + n)))) →
          U.ν (Bφ C₁ᴿ (Bφ B X)) U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR X)))
    ν↓ᴿ X =
         ν-past-Bφ C₁ᴿ (Bφ B X)
      ◅◅ Bφ-cong C₁ᴿ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sAᴿ 2))))
      ◅◅ Bφ-cong C₁ᴿ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sAᴿ 2 ↑* sB)))
    rhs : U[ T.ν C₁ᴿ B QR ] σ U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
    rhs = ≡→≋ (Uν-flat σ C₁ᴿ B QR) ◅◅ ν↓ᴿ XRᴿ

    -- ----- grown-leaf (RHS) thread expansion (mirror of lsplit pushR-thread) -----
    ρ₁ᴿ : (sB + (sAᴿ + (2 + n))) →ᵣ (sB + (2 + (sAᴿ + n)))
    ρ₁ᴿ = assocSwapᵣ sAᴿ 2 ↑* sB
    ρ₂ᴿ : (sB + (2 + (sAᴿ + n))) →ᵣ (2 + (sB + (sAᴿ + n)))
    ρ₂ᴿ = assocSwapᵣ sB 2
    rnᴿ : Tm (sB + (sAᴿ + (2 + n))) → Tm (2 + (sB + (sAᴿ + n)))
    rnᴿ t = (t ⋯ ρ₁ᴿ) ⋯ ρ₂ᴿ
    Frᴿ : Frame* (2 + (sB + (sAᴿ + n)))
    Frᴿ = (frame*-⋯ (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ⋯ᶠ* ρ₂ᴿ
    threadEqᴿ : (Ef : Frame* (sum C₁ᴿ + sum B + m)) (p : Tm (sum C₁ᴿ + sum B + m)) →
                (U[ T.⟪ Ef [ p ]* ⟫ ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
                ≡ U.⟪ ((frame*-⋯ Ef τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ⋯ᶠ* ρ₂ᴿ) [ rnᴿ (p ⋯ τᴿ) ]* ⟫
    threadEqᴿ Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁ᴿ) ⋯ ρ₂ᴿ) (frame-plug* Ef τᴿ Vτᴿ)
      ■ cong (_⋯ ρ₂ᴿ) (frame-plug*ᵣ (frame*-⋯ Ef τᴿ Vτᴿ) ρ₁ᴿ)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ρ₂ᴿ )
    pushR-threadᴿ : U.Proc (2 + (sB + (sAᴿ + n)))
    pushR-threadᴿ = (U[ T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
    pushR-Pᴿ : U.Proc (2 + (sB + (sAᴿ + n)))
    pushR-Pᴿ = (U[ P T.⋯ₚ 𝐒.rwk ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
    pushR-threadEqᴿ : pushR-threadᴿ ≡ U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫
    pushR-threadEqᴿ = threadEqᴿ (E ⋯ᶠ* 𝐒.rwk) ((` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F))
    -- U-rwk naturality: translating the rwk-renamed residual P is the same as
    -- translating P and inserting the fresh sync slot (sins ↑* syncs B), because
    -- P's variables (all images of ρ⁻) avoid the consumed handle, where τ and τᴿ
    -- agree modulo the insertion by leafσ-rwk-id.
    Prwkeq : U[ P T.⋯ₚ 𝐒.rwk ] τᴿ ≡ U[ P ] τ U.⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)
    Prwkeq =
        cong (λ p → U[ p T.⋯ₚ 𝐒.rwk ] τᴿ) Peq
      ■ cong (λ p → U[ p ] τᴿ) (T.fusionₚ P₀ ρ⁻ 𝐒.rwk)
      ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → sym (leafσ-rwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y)))
      ■ sym (U-σ⋯ P₀)
      ■ cong (U._⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)) (sym (U-⋯ₚ P₀))
      ■ cong (λ p → U[ p ] τ U.⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)) (sym Peq)

    -- ----- the residual bridge (back) -----
    -- Brwk-slide pulls C₁ᴿ's extra φ-drop binder down to the leaf, reducing the
    -- reconcile to commuting that φ-drop past (Bφ B ; ν) and matching the leaf.
    slid : Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
           U.≋ Bφ C₁ (U.φ U.drop (subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                                    U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}))
    slid = Brwk-slide B₁ {b₁} {B₂} {n} (Bφ B (U.ν (pushR XRᴿ)))
    innerReconcile : Bφ B (U.ν (U.φ U.drop contractumR))
                     U.≋ U.φ U.drop (subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                                      U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n})
    -- pushR XRᴿ splits into the grown thread + P, with the thread expanded via
    -- the proven pushR-threadEqᴿ.  (Reusable building block for leafRec.)
    pushR-bodyᴿ : pushR XRᴿ
                  ≡ U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫ U.∥ pushR-Pᴿ
    pushR-bodyᴿ = cong₂ U._∥_ pushR-threadEqᴿ refl
    leafRec : Bφ B ((U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B))
              U.≋ subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                    U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
    leafRec = ≡→≋ leafRec≡
      where
        EQ′ : syncs C₁ᴿ + n ≡ syncs C₁ + suc n
        EQ′ = cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)
        sD′ : ℕ
        sD′ = syncs (suc b₁ ∷ B₂)
        rawR : (sD′ + (1 + (L.length B₁ + n))) →ᵣ (1 + (sD′ + (L.length B₁ + n)))
        rawR = assocSwapᵣ sD′ 1 {L.length B₁ + n}
        rhsR≡ : subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
                ≡ subst U.Proc (sw-cod B₁ {b₁} {B₂} {n})
                    (subst U.Proc (EQ′ ■ sw-dom B₁ {b₁} {B₂} {n}) (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ rawR)
        rhsR≡ = cast-⋯2 (sw-dom B₁ {b₁} {B₂} {n}) (sw-cod B₁ {b₁} {B₂} {n}) (subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ)))) rawR
             ■ cong (λ w → subst U.Proc (sw-cod B₁ {b₁} {B₂} {n}) (w U.⋯ₚ rawR))
                 (ss-U EQ′ (sw-dom B₁ {b₁} {B₂} {n}) {t = Bφ B (U.ν (pushR XRᴿ))})
        e2 : syncs C₁ᴿ + n ≡ sD′ + (1 + (L.length B₁ + n))
        e2 = EQ′ ■ sw-dom B₁ {b₁} {B₂} {n}
        rhsPush : subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
                  ≡ Bφ B (subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                            (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B)))
        rhsInner : subst U.Proc e2 (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ rawR
                   ≡ Bφ B (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        rhsInner =
            cong (U._⋯ₚ rawR) (subst-Bφ e2 B (U.ν (pushR XRᴿ)))
          ■ Bφ-⋯ B (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ))) rawR
        rhsPush = rhsR≡
                ■ cong (subst U.Proc (sw-cod B₁ {b₁} {B₂} {n})) rhsInner
                ■ subst-Bφ (sw-cod B₁ {b₁} {B₂} {n}) B
                    (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        rhsνOut : subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                     (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
                  ≡ U.ν (subst U.Proc (cong (2 +_) (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                          (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ)
                             U.⋯ₚ ((rawR ↑* syncs B) ↑* 2)))
        rhsνOut =
            cong (subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
              (cong (U._⋯ₚ (rawR ↑* syncs B)) (subst-ν (cong (syncs B +_) e2) (pushR XRᴿ)))
          ■ subst-ν (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
              (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ) U.⋯ₚ ((rawR ↑* syncs B) ↑* 2))
        νInner : (contractumR U.⋯ₚ assocSwapᵣ 1 2) U.⋯ₚ ((assocSwapᵣ 1 (syncs B)) ↑* 2)
                 ≡ subst U.Proc (cong (2 +_) (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                     (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ)
                        U.⋯ₚ ((rawR ↑* syncs B) ↑* 2))
        SQ : ℕ → ℕ
        SQ section = suc (suc section)
        ρρ : (syncs B + (sD′ + (1 + (L.length B₁ + n)))) →ᵣ (syncs B + (1 + (sD′ + (L.length B₁ + n))))
        ρρ = (rawR ↑* syncs B)
        -- distribute RHS subst/⋯ over the ∥ of pushR-bodyᴿ
        rhsSplit : subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                     (subst U.Proc (cong SQ (cong (syncs B +_) e2)) (pushR XRᴿ) U.⋯ₚ (ρρ ↑* 2))
                   ≡ subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                       ( (subst U.Proc (cong SQ (cong (syncs B +_) e2))
                           (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
                       U.∥ (subst U.Proc (cong SQ (cong (syncs B +_) e2)) pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2)) )
        rhsSplit =
            cong (subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))))
              ( cong (λ z → (subst U.Proc (cong SQ (cong (syncs B +_) e2)) z) U.⋯ₚ (ρρ ↑* 2)) pushR-bodyᴿ
              ■ cong (U._⋯ₚ (ρρ ↑* 2))
                  (subst-∥f (λ z → z) (cong SQ (cong (syncs B +_) e2))
                     (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) pushR-Pᴿ) )
        -- ===== outer renaming reconciliation (fresh-φ insertion commutes) =====
        Θ : (syncs B + (sA + (2 + n))) →ᵣ (syncs B + (sAᴿ + (2 + n)))
        Θ = sins B₁ b₁ B₂ {2 + n} ↑* syncs B
        E-dom : (2 + (syncs B + (sAᴿ + n))) ≡ SQ (syncs B + (sD′ + (1 + (L.length B₁ + n))))
        E-dom = cong SQ (cong (syncs B +_) e2)
        E-cod : SQ (syncs B + (1 + (sD′ + (L.length B₁ + n)))) ≡ SQ (syncs B + suc (sA + n))
        E-cod = cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
        θ1R : SQ (syncs B + (sAᴿ + n)) →ᵣ SQ (syncs B + (1 + (sD′ + (L.length B₁ + n))))
        θ1R = subst (λ z → z →ᵣ SQ (syncs B + (1 + (sD′ + (L.length B₁ + n))))) (sym E-dom) (ρρ ↑* 2)
        ρR' : SQ (syncs B + (sAᴿ + n)) →ᵣ SQ (syncs B + suc (sA + n))
        ρR' = subst (λ z → SQ (syncs B + (sAᴿ + n)) →ᵣ z) E-cod θ1R
        ρLtot : (syncs B + (sA + (2 + n))) →ᵣ (2 + (syncs B + (1 + (sA + n))))
        ρLtot = ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
        ρRtot : (syncs B + (sA + (2 + n))) →ᵣ (2 + (syncs B + suc (sA + n)))
        ρRtot = Θ ·ₖ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR'))
        sdom : ∀ {a b c} (p : a ≡ b) (Q : U.Proc a) (θ : b →ᵣ c) →
               subst U.Proc p Q U.⋯ₚ θ ≡ Q U.⋯ₚ subst (λ z → z →ᵣ c) (sym p) θ
        sdom refl Q θ = refl
        toℕ-subst-dom : ∀ {A A′ Bb} (e : A ≡ A′) (ρ : A →ᵣ Bb) (y : 𝔽 A′) →
                        Fin.toℕ (subst (λ z → z →ᵣ Bb) e ρ y) ≡ Fin.toℕ (ρ (subst 𝔽 (sym e) y))
        toℕ-subst-dom refl ρ y = refl
        fuseL : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
                Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
                ≡ Y U.⋯ₚ ρLtot
        fuseL Y =
            U.fusionₚ (Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ) (assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2)
          ■ U.fusionₚ (Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂) weakenᵣ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))
          ■ U.fusionₚ (Y U.⋯ₚ ρ₁) ρ₂ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2)))
          ■ U.fusionₚ Y ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
        fuseR4 : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
                 Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ U.⋯ₚ ρR' ≡ Y U.⋯ₚ ρRtot
        fuseR4 Y =
            U.fusionₚ (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ) ρ₂ᴿ ρR'
          ■ U.fusionₚ (Y U.⋯ₚ Θ) ρ₁ᴿ (ρ₂ᴿ ·ₖ ρR')
          ■ U.fusionₚ Y Θ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR'))
        collapseR : ∀ (Z : U.Proc (SQ (syncs B + (sAᴿ + n)))) →
                    subst U.Proc E-cod (subst U.Proc E-dom Z U.⋯ₚ (ρρ ↑* 2))
                    ≡ Z U.⋯ₚ ρR'
        collapseR Z =
            cong (subst U.Proc E-cod) (sdom E-dom Z (ρρ ↑* 2))
          ■ sym (subst-⋯ₚ-cod E-cod Z θ1R)
        ρL≗ρR : ρLtot ≗ ρRtot
        ρL≗ρR i = go
          where
            toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
            toℕ-subst𝔽 refl y = refl
            eAR : sAᴿ ≡ suc sA
            eAR = syncs-rwk B₁
            sD′≤sA : sD′ Nat.≤ sA
            sD′≤sA = sD≤ B₁ {b₁} {B₂}
            sA≤sAᴿ : sA Nat.≤ sAᴿ
            sA≤sAᴿ = subst (sA Nat.≤_) (sym eAR) (Nat.n≤1+n sA)
            sD′≤sAᴿ : sD′ Nat.≤ sAᴿ
            sD′≤sAᴿ = Nat.≤-trans sD′≤sA sA≤sAᴿ
            sB2≤3di : syncs B Nat.≤ Fin.toℕ i → syncs B + 2 Nat.≤ 3 + Fin.toℕ i
            sB2≤3di h = Nat.≤-trans (Nat.+-monoˡ-≤ 2 h)
                          (Nat.≤-trans (Nat.+-monoʳ-≤ (Fin.toℕ i) (Nat.n≤1+n 2))
                                       (Nat.≤-reflexive (Nat.+-comm (Fin.toℕ i) 3)))
            v2R : 𝔽 (SQ (syncs B + (sAᴿ + n)))
            v2R = ρ₂ᴿ (ρ₁ᴿ (Θ i))
            w2 : 𝔽 (SQ (syncs B + (sD′ + (1 + (L.length B₁ + n)))))
            w2 = subst 𝔽 (sym (sym E-dom)) v2R
            lhsSB : Fin.toℕ i Nat.< syncs B → Fin.toℕ (ρLtot i) ≡ 2 + Fin.toℕ i
            lhsSB p =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-mid 1 (syncs B) (Fin.reduce≥ X4 q) ge lt ■ cong (Nat._∸ 1) redX)
              where
                v1 = toℕ-↑*-lt (assocSwapᵣ sA 2) (syncs B) i p
                v2 = toℕ-assoc-lt (syncs B) 2 (ρ₁ i) (subst (Nat._< syncs B) (sym v1) p) ■ cong (2 +_) v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                       (subst (3 Nat.≤_) (sym v3) (Nat.m≤m+n 3 (Fin.toℕ i))) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
                ge = subst (1 Nat.≤_) (sym redX) (Nat.s≤s Nat.z≤n)
                lt = subst (Nat._< suc (syncs B)) (sym redX) (Nat.s≤s p)
            rhsSB : Fin.toℕ i Nat.< syncs B → Fin.toℕ (ρRtot i) ≡ 2 + Fin.toℕ i
            rhsSB p =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) (toℕ-↑*-lt rawR (syncs B) (Fin.reduce≥ w2 q2) (subst (Nat._< syncs B) (sym redw2) p) ■ redw2)
              where
                r1 = toℕ-↑*-lt (sins B₁ b₁ B₂ {2 + n}) (syncs B) i p
                r2 = toℕ-↑*-lt (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) (subst (Nat._< syncs B) (sym r1) p) ■ r1
                r3 = toℕ-assoc-lt (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (Nat._< syncs B) (sym r2) p) ■ cong (2 +_) r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
            lhsSA : syncs B Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA → Fin.toℕ (ρLtot i) ≡ 3 + Fin.toℕ i
            lhsSA sB≤ di<A =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-ge 1 (syncs B) (Fin.reduce≥ X4 q) ge ■ redX)
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sA = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sA (subst (Nat._< syncs B + sA) (sym recon) di<A)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-lt sA 2 (Fin.reduce≥ i sB≤) (subst (Nat._< sA) (sym rdi≡) rd<sA) ■ cong (2 +_) rdi≡)
                   ■ comm3 (syncs B) 2 (Fin.toℕ i Nat.∸ syncs B) ■ cong (2 +_) recon
                v2 = toℕ-assoc-ge (syncs B) 2 (ρ₁ i)
                       (subst (syncs B + 2 Nat.≤_) (sym v1) (subst (Nat._≤ 2 + Fin.toℕ i) (Nat.+-comm 2 (syncs B)) (Nat.+-monoʳ-≤ 2 sB≤))) ■ v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                       (subst (3 Nat.≤_) (sym v3) (Nat.m≤m+n 3 (Fin.toℕ i))) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
                ge = subst (suc (syncs B) Nat.≤_) (sym redX) (Nat.s≤s sB≤)
            rhsSAlo : syncs B Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sD′ → Fin.toℕ (ρRtot i) ≡ 3 + Fin.toℕ i
            rhsSAlo sB≤ di<lo =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-lt sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) (subst (Nat._< sD′) (sym rr≡) rd<sD) ■ cong (1 +_) rr≡)
                            ■ comm3 (syncs B) 1 (Fin.toℕ i Nat.∸ syncs B) ■ cong (1 +_) recon )
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sD = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sD′ (subst (Nat._< syncs B + sD′) (sym recon) di<lo)
                rd<sAᴿ = Nat.<-≤-trans rd<sD sD′≤sAᴿ
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-lo B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (Nat._< sD′) (sym rdi≡) rd<sD) ■ rdi≡)
                   ■ recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) sB≤
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-lt sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (Nat._< sAᴿ) (sym redΘ) rd<sAᴿ) ■ cong (2 +_) redΘ)
                   ■ comm3 (syncs B) 2 (Fin.toℕ i Nat.∸ syncs B) ■ cong (2 +_) recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i))
                       (subst (syncs B + 2 Nat.≤_) (sym r2) (subst (Nat._≤ 2 + Fin.toℕ i) (Nat.+-comm 2 (syncs B)) (Nat.+-monoʳ-≤ 2 sB≤))) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) sB≤
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2
            rhsSAhi : syncs B Nat.≤ Fin.toℕ i → syncs B + sD′ Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA → Fin.toℕ (ρRtot i) ≡ 3 + Fin.toℕ i
            rhsSAhi sB≤ sDle di<A =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-ge sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) sD1≤rr ■ rr≡)
                            ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon )
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sA = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sA (subst (Nat._< syncs B + sA) (sym recon) di<A)
                rd≥sD = Nat.+-cancelˡ-≤ (syncs B) sD′ (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sD′ Nat.≤_) (sym recon) sDle)
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) rd≥sD) ■ cong suc rdi≡)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.+-∸-assoc 1 sB≤
                sucrd<sAᴿ = subst (suc (Fin.toℕ i Nat.∸ syncs B) Nat.<_) (sym eAR) (Nat.s≤s rd<sA)
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-lt sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (Nat._< sAᴿ) (sym redΘ) sucrd<sAᴿ) ■ cong (2 +_) redΘ)
                   ■ comm3 (syncs B) 3 (Fin.toℕ i Nat.∸ syncs B) ■ cong (3 +_) recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B + 2 Nat.≤_) (sym r2) (sB2≤3di sB≤)) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2 ■ Nat.+-∸-assoc 1 sB≤
                sD1≤rr = Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm sD′ 1)) (subst (suc sD′ Nat.≤_) (sym rr≡) (Nat.s≤s rd≥sD))
            lhsTWO : syncs B + sA Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA + 2 → Fin.toℕ (ρLtot i) ≡ (Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA
            lhsTWO sBsA≤ di<T =
                toℕ-↑*-lt (assocSwapᵣ 1 (syncs B)) 2 X4 (subst (Nat._< 2) (sym v4) t2<2) ■ v4
              where
                sB≤ = Nat.≤-trans (Nat.m≤m+n (syncs B) sA) sBsA≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA≤rd = Nat.+-cancelˡ-≤ (syncs B) sA (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sA Nat.≤_) (sym recon) sBsA≤)
                rd<sA2 = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) (sA + 2) (subst (Nat._< syncs B + (sA + 2)) (sym recon) (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc (syncs B) sA 2) di<T))
                t2<2 = Nat.+-cancelˡ-< sA ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA) 2 (subst (Nat._< sA + 2) (sym (Nat.m+[n∸m]≡n sA≤rd)) rd<sA2)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-mid sA 2 (Fin.reduce≥ i sB≤) (subst (sA Nat.≤_) (sym rdi≡) sA≤rd) (subst (Nat._< sA + 2) (sym rdi≡) rd<sA2) ■ cong (Nat._∸ sA) rdi≡)
                v2 = toℕ-assoc-mid (syncs B) 2 (ρ₁ i) (subst (syncs B Nat.≤_) (sym v1) (Nat.m≤m+n (syncs B) _)) (subst (Nat._< syncs B + 2) (sym v1) (Nat.+-monoʳ-< (syncs B) t2<2))
                   ■ cong (Nat._∸ syncs B) v1 ■ Nat.m+n∸m≡n (syncs B) ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA)
                v3 = cong suc v2
                v4 = toℕ-assoc-mid 1 2 (weakenᵣ (ρ₂ (ρ₁ i))) (subst (1 Nat.≤_) (sym v3) (Nat.s≤s Nat.z≤n)) (subst (Nat._< 3) (sym v3) (Nat.s≤s t2<2)) ■ cong (Nat._∸ 1) v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
            rhsTWO : syncs B + sA Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA + 2 → Fin.toℕ (ρRtot i) ≡ (Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA
            rhsTWO sBsA≤ di<T =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-lt ρρ 2 w2 (subst (Nat._< 2) (sym w2N) t2<2)
              ■ w2N
              where
                sB≤ = Nat.≤-trans (Nat.m≤m+n (syncs B) sA) sBsA≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA≤rd = Nat.+-cancelˡ-≤ (syncs B) sA (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sA Nat.≤_) (sym recon) sBsA≤)
                rd<sA2 = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) (sA + 2) (subst (Nat._< syncs B + (sA + 2)) (sym recon) (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc (syncs B) sA 2) di<T))
                t2<2 = Nat.+-cancelˡ-< sA ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA) 2 (subst (Nat._< sA + 2) (sym (Nat.m+[n∸m]≡n sA≤rd)) rd<sA2)
                sD≤rd = Nat.≤-trans sD′≤sA sA≤rd
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) sD≤rd) ■ cong suc rdi≡)
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.m≤m+n (syncs B) (suc (Fin.toℕ i Nat.∸ syncs B)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.m+n∸m≡n (syncs B) (suc (Fin.toℕ i Nat.∸ syncs B))
                sucrd≥sAᴿ = subst (Nat._≤ suc (Fin.toℕ i Nat.∸ syncs B)) (sym eAR) (Nat.s≤s sA≤rd)
                sucrd<sAᴿ2 = subst (suc (Fin.toℕ i Nat.∸ syncs B) Nat.<_) (sym (cong (_+ 2) eAR)) (Nat.s≤s rd<sA2)
                midEq = cong (λ z → suc (Fin.toℕ i Nat.∸ syncs B) Nat.∸ z) eAR
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-mid sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (sAᴿ Nat.≤_) (sym redΘ) sucrd≥sAᴿ) (subst (Nat._< sAᴿ + 2) (sym redΘ) sucrd<sAᴿ2) ■ cong (Nat._∸ sAᴿ) redΘ ■ midEq)
                r3 = toℕ-assoc-mid (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B Nat.≤_) (sym r2) (Nat.m≤m+n (syncs B) _)) (subst (Nat._< syncs B + 2) (sym r2) (Nat.+-monoʳ-< (syncs B) t2<2))
                   ■ cong (Nat._∸ syncs B) r2 ■ Nat.m+n∸m≡n (syncs B) ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA)
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
            lhsN : syncs B + sA + 2 Nat.≤ Fin.toℕ i → Fin.toℕ (ρLtot i) ≡ suc (Fin.toℕ i)
            lhsN sBsA2≤ =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-ge 1 (syncs B) (Fin.reduce≥ X4 q) (subst (1 + syncs B Nat.≤_) (sym redX) B1≤) ■ redX)
              ■ cong suc (Nat.m+[n∸m]≡n oneleq)
              where
                sB≤ = Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (syncs B) sA) (Nat.m≤m+n (syncs B + sA) 2)) sBsA2≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA2≤rd = Nat.+-cancelˡ-≤ (syncs B) (sA + 2) (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + (sA + 2) Nat.≤_) (sym recon) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤))
                sB2≤di = Nat.≤-trans (Nat.+-monoʳ-≤ (syncs B) (Nat.m≤n+m 2 sA)) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤)
                two≤di = Nat.≤-trans (Nat.m≤n+m 2 (syncs B + sA)) sBsA2≤
                oneleq = Nat.≤-trans (Nat.n≤1+n 1) two≤di
                B1≤ = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B) (Nat.s≤s Nat.z≤n) ■ Nat.+-comm (syncs B) 1) (Nat.∸-monoˡ-≤ 1 sB2≤di)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-ge sA 2 (Fin.reduce≥ i sB≤) (subst (sA + 2 Nat.≤_) (sym rdi≡) sA2≤rd) ■ rdi≡) ■ recon
                v2 = toℕ-assoc-ge (syncs B) 2 (ρ₁ i) (subst (syncs B + 2 Nat.≤_) (sym v1) sB2≤di) ■ v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i))) (subst (3 Nat.≤_) (sym v3) (Nat.s≤s two≤di)) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.≤-trans two≤di (Nat.n≤1+n (Fin.toℕ i)))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
            rhsN : syncs B + sA + 2 Nat.≤ Fin.toℕ i → Fin.toℕ (ρRtot i) ≡ suc (Fin.toℕ i)
            rhsN sBsA2≤ =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-ge sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) sD1≤rr ■ rr≡)
                            ■ Nat.m+[n∸m]≡n sB≤di∸1 )
              ■ cong suc (Nat.m+[n∸m]≡n oneleq)
              where
                sB≤ = Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (syncs B) sA) (Nat.m≤m+n (syncs B + sA) 2)) sBsA2≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA2≤rd = Nat.+-cancelˡ-≤ (syncs B) (sA + 2) (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + (sA + 2) Nat.≤_) (sym recon) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤))
                sB2≤di = Nat.≤-trans (Nat.+-monoʳ-≤ (syncs B) (Nat.m≤n+m 2 sA)) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤)
                two≤di = Nat.≤-trans (Nat.m≤n+m 2 (syncs B + sA)) sBsA2≤
                oneleq = Nat.≤-trans (Nat.n≤1+n 1) two≤di
                sD≤rd = Nat.≤-trans sD′≤sA (Nat.≤-trans (Nat.m≤m+n sA 2) sA2≤rd)
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) sD≤rd) ■ cong suc rdi≡)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.+-∸-assoc 1 sB≤
                sAᴿ2≤sucrd = subst (Nat._≤ suc (Fin.toℕ i Nat.∸ syncs B)) (sym (cong (_+ 2) eAR)) (Nat.s≤s sA2≤rd)
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-ge sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (sAᴿ + 2 Nat.≤_) (sym redΘ) sAᴿ2≤sucrd) ■ redΘ)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B + 2 Nat.≤_) (sym r2) (Nat.≤-trans sB2≤di (Nat.n≤1+n (Fin.toℕ i)))) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.≤-trans two≤di (Nat.n≤1+n (Fin.toℕ i)))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                B1≤ = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B) (Nat.s≤s Nat.z≤n) ■ Nat.+-comm (syncs B) 1) (Nat.∸-monoˡ-≤ 1 sB2≤di)
                sB≤di∸1 = Nat.≤-trans (Nat.n≤1+n (syncs B)) B1≤
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) sB≤di∸1
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2
                sBsA1≤di∸1 = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B + sA) (Nat.s≤s Nat.z≤n) ■ Nat.+-assoc (syncs B) sA 1) (Nat.∸-monoˡ-≤ 1 sBsA2≤)
                sA1≤rr = subst (Nat._≤ (Fin.toℕ i Nat.∸ 1) Nat.∸ syncs B) (Nat.m+n∸m≡n (syncs B) (sA + 1)) (Nat.∸-monoˡ-≤ (syncs B) sBsA1≤di∸1)
                sD1≤rr = subst (sD′ + 1 Nat.≤_) (sym rr≡) (Nat.≤-trans (Nat.+-monoˡ-≤ 1 sD′≤sA) sA1≤rr)
            go : ρLtot i ≡ ρRtot i
            go with Fin.toℕ i Nat.<? syncs B
            ... | yes p = Fin.toℕ-injective (lhsSB p ■ sym (rhsSB p))
            ... | no ¬p with Fin.toℕ i Nat.<? (syncs B + sD′)
            ...   | yes qlo = Fin.toℕ-injective (lhsSA (Nat.≮⇒≥ ¬p) (Nat.<-≤-trans qlo (Nat.+-monoʳ-≤ (syncs B) sD′≤sA)) ■ sym (rhsSAlo (Nat.≮⇒≥ ¬p) qlo))
            ...   | no ¬qlo with Fin.toℕ i Nat.<? (syncs B + sA)
            ...     | yes rhi = Fin.toℕ-injective (lhsSA (Nat.≮⇒≥ ¬p) rhi ■ sym (rhsSAhi (Nat.≮⇒≥ ¬p) (Nat.≮⇒≥ ¬qlo) rhi))
            ...     | no ¬rhi with Fin.toℕ i Nat.<? (syncs B + sA + 2)
            ...       | yes ttwo = Fin.toℕ-injective (lhsTWO (Nat.≮⇒≥ ¬rhi) ttwo ■ sym (rhsTWO (Nat.≮⇒≥ ¬rhi) ttwo))
            ...       | no ¬ttwo = Fin.toℕ-injective (lhsN (Nat.≮⇒≥ ¬ttwo) ■ sym (rhsN (Nat.≮⇒≥ ¬ttwo)))
        outerRec : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
          Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
          ≡ subst U.Proc E-cod
              (subst U.Proc E-dom (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ) U.⋯ₚ (ρρ ↑* 2))
        outerRec Y =
            fuseL Y
          ■ U.⋯ₚ-cong Y ρL≗ρR
          ■ sym (fuseR4 Y)
          ■ sym (collapseR (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ))
        pushRPᴿ-fac : pushR-Pᴿ ≡ U[ P ] τ U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ
        pushRPᴿ-fac = cong (λ z → (z U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ) Prwkeq
        Prest≡ : RP U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
                 ≡ subst U.Proc E-cod (subst U.Proc E-dom pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2))
        Prest≡ =
            outerRec (U[ P ] τ)
          ■ cong (λ z → subst U.Proc E-cod (subst U.Proc E-dom z U.⋯ₚ (ρρ ↑* 2)))
              (sym pushRPᴿ-fac)
        -- Tm-level analogue of outerRec (for the body-triple slots), reusing ρL≗ρR.
        outerRec-Tm : ∀ (t : Tm (syncs B + (sA + (2 + n)))) →
          t ⋯ ρ₁ ⋯ ρ₂ ⋯ weakenᵣ ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
          ≡ t ⋯ Θ ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR'
        outerRec-Tm t =
            fusion (t ⋯ ρ₁ ⋯ ρ₂ ⋯ weakenᵣ) (assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2)
          ■ fusion (t ⋯ ρ₁ ⋯ ρ₂) weakenᵣ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))
          ■ fusion (t ⋯ ρ₁) ρ₂ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2)))
          ■ fusion t ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
          ■ ⋯-cong t ρL≗ρR
          ■ sym ( fusion (t ⋯ Θ ⋯ ρ₁ᴿ) ρ₂ᴿ ρR'
                ■ fusion (t ⋯ Θ) ρ₁ᴿ (ρ₂ᴿ ·ₖ ρR')
                ■ fusion t Θ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR')) )
        -- grown handle inj0 (fresh 1-channel) triple decomposition (mirror of ccTriple).
        hcᴿ0 = canonₛ-handle B₁ (K `unit) 0F (K `unit) 0 (suc b₁ ∷ B₂)
        castposᴿ0 : 𝔽 (sum C₁ᴿ)
        castposᴿ0 = Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
        τᴿinj0 : τᴿ (𝐒.inj 0F) ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
        τᴿinj0 =
            cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum B) (castposᴿ0 ↑ˡ sum B) m)
          ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ0 (sum B))
        ccTripleᴿ0 : rnᴿ (τᴿ (𝐒.inj 0F))
                     ≡ ((proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ) ⊗ (` 0F))
                       ⊗ (proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ)
        ccTripleᴿ0 =
            cong rnᴿ (τᴿinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) (proj₁ (proj₂ (proj₂ (proj₂ hcᴿ0)))))
          ■ cong (λ z → ((proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ) ⊗ (` z))
                        ⊗ (proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ))
              (Fin.toℕ-injective (assocPush-junc sAᴿ (syncs B) 0 (weaken* ⦃ Kᵣ ⦄ (syncs B) (proj₁ (proj₂ (proj₂ hcᴿ0)))) jvtoℕᴿ (Nat.s≤s Nat.z≤n)))
          where
            jvtoℕᴿ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ (syncs B) (proj₁ (proj₂ (proj₂ hcᴿ0)))) ≡ syncs B + (sAᴿ + 0)
            jvtoℕᴿ = toℕ-weaken*ᵣ (syncs B) (proj₁ (proj₂ (proj₂ hcᴿ0))) ■ cong (syncs B +_) (proj₂ (proj₂ (proj₂ (proj₂ hcᴿ0))))
        slotL0 : proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ≡ proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ Θ
        slotL0 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) (handle-L-rwk B₁ (K `unit) 0F (K `unit) b₁ B₂)
               ■ ⋯-↑*-wk (proj₁ hc) (sins B₁ b₁ B₂ {2 + n}) (syncs B)
        Leq0 : ccA ⋯ weakenᵣ ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
               ≡ proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR'
        Leq0 = outerRec-Tm (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
             ■ cong (λ z → z ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR') (sym slotL0)
        -- grown handle inj1 (residual suc b₁-channel) triple decomposition (mirror of ccTripleᴿ0).
        hcᴿ1 = canonₛ-handle (B₁ ++ 1 ∷ []) (K `unit) 0F (K `unit) b₁ B₂
        passocᴿ : (B₁ ++ 1 ∷ []) ++ suc b₁ ∷ B₂ ≡ C₁ᴿ
        passocᴿ = ++-assoc B₁ (1 ∷ []) (suc b₁ ∷ B₂)
        castRRᴿ : syncs ((B₁ ++ 1 ∷ []) ++ suc b₁ ∷ B₂) + (2 + n) ≡ syncs C₁ᴿ + (2 + n)
        castRRᴿ = cong (λ z → syncs z + (2 + n)) passocᴿ
        posᴿ1 : 𝔽 (sum ((B₁ ++ 1 ∷ []) ++ suc b₁ ∷ B₂))
        posᴿ1 = Fin.cast (sym (sum-++ (B₁ ++ 1 ∷ []) (suc b₁ ∷ B₂))) (sum (B₁ ++ 1 ∷ []) ↑ʳ 0F)
        j0ᴿ = proj₁ (proj₂ (proj₂ hcᴿ1))
        castposᴿ1 : 𝔽 (sum C₁ᴿ)
        castposᴿ1 = Fin.cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 1F)
        τᴿinj1 : τᴿ (𝐒.inj 1F) ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
        τᴿinj1 =
            cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum B) (castposᴿ1 ↑ˡ sum B) m)
          ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ1 (sum B))
        posEqᴿ : castposᴿ1 ≡ subst (λ L → 𝔽 (sum L)) passocᴿ posᴿ1
        posEqᴿ = Fin.toℕ-injective
          ( (Fin.toℕ-cast (sym (sum-++ B₁ (1 ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 1F) ■ Fin.toℕ-↑ʳ (sum B₁) 1F)
          ■ sym ( tf𝔽 passocᴿ posᴿ1
                ■ Fin.toℕ-cast (sym (sum-++ (B₁ ++ 1 ∷ []) (suc b₁ ∷ B₂))) (sum (B₁ ++ 1 ∷ []) ↑ʳ 0F)
                ■ Fin.toℕ-↑ʳ (sum (B₁ ++ 1 ∷ [])) 0F
                ■ Nat.+-identityʳ (sum (B₁ ++ 1 ∷ []))
                ■ sum-++ B₁ (1 ∷ []) ) )
          where
            tf𝔽 : ∀ {L1 L2 : BindGroup} (p : L1 ≡ L2) (y : 𝔽 (sum L1)) →
                  Fin.toℕ (subst (λ L → 𝔽 (sum L)) p y) ≡ Fin.toℕ y
            tf𝔽 refl y = refl
        canonᴿ1-decomp : canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1
                         ≡ ((subst Tm castRRᴿ (proj₁ hcᴿ1)) ⊗ (` subst 𝔽 castRRᴿ j0ᴿ))
                           ⊗ subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1))
        canonᴿ1-decomp =
            cong (canonₛ C₁ᴿ (K `unit , 0F , K `unit)) posEqᴿ
          ■ canonₛ-cast passocᴿ (K `unit , 0F , K `unit) posᴿ1
          ■ subst-syncs passocᴿ (canonₛ ((B₁ ++ 1 ∷ []) ++ suc b₁ ∷ B₂) (K `unit , 0F , K `unit) posᴿ1)
          ■ cong (subst Tm castRRᴿ) (proj₁ (proj₂ (proj₂ (proj₂ hcᴿ1))))
          ■ substTripⱼ castRRᴿ (proj₁ hcᴿ1) j0ᴿ (proj₁ (proj₂ hcᴿ1))
        ccTripleᴿ1 : rnᴿ (τᴿ (𝐒.inj 1F))
                     ≡ ((subst Tm castRRᴿ (proj₁ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ) ⊗ (` 0F))
                       ⊗ (subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ)
        ccTripleᴿ1 =
            cong rnᴿ (τᴿinj1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) canonᴿ1-decomp)
          ■ cong (λ z → ((subst Tm castRRᴿ (proj₁ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ) ⊗ (` z))
                        ⊗ (subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ))
              (Fin.toℕ-injective (assocPush-junc sAᴿ (syncs B) 0 (weaken* ⦃ Kᵣ ⦄ (syncs B) (subst 𝔽 castRRᴿ j0ᴿ)) jvtoℕᴿ1 (Nat.s≤s Nat.z≤n)))
          where
            jvtoℕᴿ1 : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ (syncs B) (subst 𝔽 castRRᴿ j0ᴿ)) ≡ syncs B + (sAᴿ + 0)
            jvtoℕᴿ1 = toℕ-weaken*ᵣ (syncs B) (subst 𝔽 castRRᴿ j0ᴿ)
                    ■ cong (syncs B +_)
                        ( tf𝔽 castRRᴿ j0ᴿ
                        ■ proj₂ (proj₂ (proj₂ (proj₂ hcᴿ1)))
                        ■ cong (_+ 0) (cong syncs passocᴿ) )
              where
                tf𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
                tf𝔽 refl y = refl
        slotR1 : subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
                 ≡ proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ Θ
        slotR1 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) (handle-R-rwk B₁ (K `unit) 0F (K `unit) b₁ B₂)
               ■ ⋯-↑*-wk (proj₁ (proj₂ hc)) (sins B₁ b₁ B₂ {2 + n}) (syncs B)
        Req1 : ccC ⋯ weakenᵣ ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
               ≡ subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR'
        Req1 = outerRec-Tm (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
             ■ cong (λ z → z ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR') (sym slotR1)
        -- ===== body-triple slot reconciliation (junction toℕ identities) =====
        tf𝔽b : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        tf𝔽b refl y = refl
        mid-lhs-toℕ : Fin.toℕ ((assocSwapᵣ 1 (syncs B) {sA + n} ↑* 2) (assocSwapᵣ 1 2 {syncs B + (sA + n)} 1F)) ≡ 0
        mid-lhs-toℕ =
            toℕ-↑*-lt (assocSwapᵣ 1 (syncs B) {sA + n}) 2 (assocSwapᵣ 1 2 {syncs B + (sA + n)} 1F)
              (subst (Nat._< 2) (sym innr) (Nat.s≤s Nat.z≤n))
          ■ innr
          where
            innr : Fin.toℕ (assocSwapᵣ 1 2 {syncs B + (sA + n)} 1F) ≡ 0
            innr = toℕ-assoc-mid 1 2 {syncs B + (sA + n)} 1F (Nat.s≤s Nat.z≤n) (Nat.s≤s (Nat.s≤s Nat.z≤n))
        mid-rhs-toℕ : Fin.toℕ (ρR' 0F) ≡ 0
        mid-rhs-toℕ =
            toℕ-subst-cod E-cod θ1R 0F
          ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) 0F
          ■ toℕ-↑*-lt ρρ 2 (subst 𝔽 (sym (sym E-dom)) 0F) (subst (Nat._< 2) (sym z0) (Nat.s≤s Nat.z≤n))
          ■ z0
          where
            z0 : Fin.toℕ (subst 𝔽 (sym (sym E-dom)) 0F) ≡ 0
            z0 = tf𝔽b (sym (sym E-dom)) 0F
        Y0-toℕ : Fin.toℕ ((assocSwapᵣ 1 (syncs B) {sA + n} ↑* 2) (assocSwapᵣ 1 2 {syncs B + (sA + n)} 0F)) ≡ 2 + syncs B
        Y0-toℕ =
            toℕ-↑*-ge (assocSwapᵣ 1 (syncs B) {sA + n}) 2 X0 q
          ■ cong (2 +_) (toℕ-assoc-lt 1 (syncs B) (Fin.reduce≥ X0 q) rd<1 ■ cong (syncs B +_) rd0 ■ Nat.+-identityʳ (syncs B))
          where
            X0 = assocSwapᵣ 1 2 {syncs B + (sA + n)} 0F
            innr : Fin.toℕ X0 ≡ 2
            innr = toℕ-assoc-lt 1 2 {syncs B + (sA + n)} 0F (Nat.s≤s Nat.z≤n)
            q : 2 Nat.≤ Fin.toℕ X0
            q = subst (2 Nat.≤_) (sym innr) Nat.≤-refl
            rd0 : Fin.toℕ (Fin.reduce≥ X0 q) ≡ 0
            rd0 = toℕ-reduce≥ X0 q ■ cong (Nat._∸ 2) innr
            rd<1 : Fin.toℕ (Fin.reduce≥ X0 q) Nat.< 1
            rd<1 = subst (Nat._< 1) (sym rd0) (Nat.s≤s Nat.z≤n)
        varComposite : ∀ (w : 𝔽 (sAᴿ + (2 + n))) → Fin.toℕ w ≡ sD′ →
                       Fin.toℕ (ρR' (ρ₂ᴿ (ρ₁ᴿ (weaken* ⦃ Kᵣ ⦄ (syncs B) w)))) ≡ 2 + syncs B
        varComposite w wt =
            toℕ-subst-cod E-cod θ1R V
          ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) V
          ■ toℕ-↑*-ge ρρ 2 W2 q2
          ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ W2 q2) sB≤rw
                        ■ cong (syncs B +_) ( toℕ-assoc-mid sD′ 1 (Fin.reduce≥ (Fin.reduce≥ W2 q2) sB≤rw) geD ltD
                                            ■ cong (Nat._∸ sD′) rr≡ ■ Nat.n∸n≡0 sD′ )
                        ■ Nat.+-identityʳ (syncs B) )
          where
            wsB = weaken* ⦃ Kᵣ ⦄ (syncs B) w
            V = ρ₂ᴿ (ρ₁ᴿ wsB)
            wsB≡ : Fin.toℕ wsB ≡ syncs B + sD′
            wsB≡ = toℕ-weaken*ᵣ (syncs B) w ■ cong (syncs B +_) wt
            sB≤wsB : syncs B Nat.≤ Fin.toℕ wsB
            sB≤wsB = subst (syncs B Nat.≤_) (sym wsB≡) (Nat.m≤m+n (syncs B) sD′)
            rdw≡ : Fin.toℕ (Fin.reduce≥ wsB sB≤wsB) ≡ sD′
            rdw≡ = toℕ-reduce≥ wsB sB≤wsB ■ cong (Nat._∸ syncs B) wsB≡ ■ Nat.m+n∸m≡n (syncs B) sD′
            sD′<sAᴿ : sD′ Nat.< sAᴿ
            sD′<sAᴿ = subst (suc sD′ Nat.≤_) (sym (syncs-rwk B₁)) (Nat.s≤s (sD≤ B₁ {b₁} {B₂}))
            ρ₁≡ : Fin.toℕ (ρ₁ᴿ wsB) ≡ syncs B + (2 + sD′)
            ρ₁≡ = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) wsB sB≤wsB
                ■ cong (syncs B +_) (toℕ-assoc-lt sAᴿ 2 (Fin.reduce≥ wsB sB≤wsB) (subst (Nat._< sAᴿ) (sym rdw≡) sD′<sAᴿ) ■ cong (2 +_) rdw≡)
            sB2≤ρ₁ : syncs B + 2 Nat.≤ Fin.toℕ (ρ₁ᴿ wsB)
            sB2≤ρ₁ = subst (syncs B + 2 Nat.≤_) (sym ρ₁≡) (Nat.+-monoʳ-≤ (syncs B) (Nat.m≤m+n 2 sD′))
            VtoN : Fin.toℕ V ≡ 2 + (syncs B + sD′)
            VtoN = (toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ wsB) sB2≤ρ₁ ■ ρ₁≡) ■ comm3 (syncs B) 2 sD′
            W2 = subst 𝔽 (sym (sym E-dom)) V
            W2toN : Fin.toℕ W2 ≡ 2 + (syncs B + sD′)
            W2toN = tf𝔽b (sym (sym E-dom)) V ■ VtoN
            q2 : 2 Nat.≤ Fin.toℕ W2
            q2 = subst (2 Nat.≤_) (sym W2toN) (Nat.m≤m+n 2 (syncs B + sD′))
            redW2 : Fin.toℕ (Fin.reduce≥ W2 q2) ≡ syncs B + sD′
            redW2 = toℕ-reduce≥ W2 q2 ■ cong (Nat._∸ 2) W2toN
            sB≤rw : syncs B Nat.≤ Fin.toℕ (Fin.reduce≥ W2 q2)
            sB≤rw = subst (syncs B Nat.≤_) (sym redW2) (Nat.m≤m+n (syncs B) sD′)
            rr≡ : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ W2 q2) sB≤rw) ≡ sD′
            rr≡ = toℕ-reduce≥ (Fin.reduce≥ W2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redW2 ■ Nat.m+n∸m≡n (syncs B) sD′
            geD : sD′ Nat.≤ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ W2 q2) sB≤rw)
            geD = subst (sD′ Nat.≤_) (sym rr≡) Nat.≤-refl
            ltD : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ W2 q2) sB≤rw) Nat.< sD′ + 1
            ltD = subst (Nat._< sD′ + 1) (sym rr≡) (subst (sD′ Nat.<_) (Nat.+-comm 1 sD′) (Nat.n<1+n sD′))
        mid : (` ((assocSwapᵣ 1 (syncs B) {sA + n} ↑* 2) (assocSwapᵣ 1 2 {syncs B + (sA + n)} 1F))) ≡ (` 0F) ⋯ ρR'
        mid = cong `_ (Fin.toℕ-injective (mid-lhs-toℕ ■ sym mid-rhs-toℕ))
        inj0-triple : ((wk ccA ⊗ (` 1F)) ⊗ (` 0F)) ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
                      ≡ rnᴿ (τᴿ (𝐒.inj 0F)) ⋯ ρR'
        inj0-triple = cong₂ _⊗_ (cong₂ _⊗_ Leq0 mid) r0 ■ sym (cong (_⋯ ρR') ccTripleᴿ0)
          where
            v0 = proj₁ (handle-R0-var B₁ (K `unit) 0F (K `unit) b₁ B₂)
            eq0 = proj₁ (proj₂ (handle-R0-var B₁ (K `unit) 0F (K `unit) b₁ B₂))
            tn0 = proj₂ (proj₂ (handle-R0-var B₁ (K `unit) 0F (K `unit) b₁ B₂))
            r0 : (` ((assocSwapᵣ 1 (syncs B) {sA + n} ↑* 2) (assocSwapᵣ 1 2 {syncs B + (sA + n)} 0F)))
                 ≡ proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR'
            r0 = cong `_ (Fin.toℕ-injective (Y0-toℕ ■ sym (varComposite v0 tn0)))
               ■ sym (cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR') eq0)
        inj1-triple : (((` 0F) ⊗ (` 1F)) ⊗ wk ccC) ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
                      ≡ rnᴿ (τᴿ (𝐒.inj 1F)) ⋯ ρR'
        inj1-triple = cong₂ _⊗_ (cong₂ _⊗_ l1 mid) Req1 ■ sym (cong (_⋯ ρR') ccTripleᴿ1)
          where
            v1 = proj₁ (handle-L1-var B₁ (K `unit) 0F (K `unit) b₁ B₂)
            eq1 = proj₁ (proj₂ (handle-L1-var B₁ (K `unit) 0F (K `unit) b₁ B₂))
            tn1 = proj₂ (proj₂ (handle-L1-var B₁ (K `unit) 0F (K `unit) b₁ B₂))
            L1var : subst Tm castRRᴿ (proj₁ hcᴿ1) ≡ ` (subst 𝔽 castRRᴿ v1)
            L1var = cong (subst Tm castRRᴿ) eq1 ■ subst-`v castRRᴿ v1
            w1tn : Fin.toℕ (subst 𝔽 castRRᴿ v1) ≡ sD′
            w1tn = tf𝔽b castRRᴿ v1 ■ tn1
            l1 : (` ((assocSwapᵣ 1 (syncs B) {sA + n} ↑* 2) (assocSwapᵣ 1 2 {syncs B + (sA + n)} 0F)))
                 ≡ subst Tm castRRᴿ (proj₁ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR'
            l1 = cong `_ (Fin.toℕ-injective (Y0-toℕ ■ sym (varComposite (subst 𝔽 castRRᴿ v1) w1tn)))
               ■ sym (cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B) ⋯ ρ₁ᴿ ⋯ ρ₂ᴿ ⋯ ρR') L1var)
        body-eq : (((wk ccA ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk ccC))
                    ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)
                  ≡ (rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F))) ⋯ ρR'
        body-eq = cong₂ _⊗_ inj0-triple inj1-triple
        -- ===== thread-leaf reconciliation (frame naturality + body triple) =====
        frameLeafeqᴿ : frame*-⋯ E τ Vτ ⋯ᶠ* Θ ≡ frame*-⋯ (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ
        frameLeafeqᴿ = sym
            ( cong (λ EE → frame*-⋯ (EE ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ) Eeq
            ■ cong (λ EE → frame*-⋯ EE τᴿ Vτᴿ) (⋯ᶠ*-fuse E₀ ρ⁻ 𝐒.rwk)
            ■ F-⋯f*-fuse E₀ Vτᴿ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ)
            ■ frame*-cong E₀ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ) (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) Θ (λ x → V-`))
                (λ y → sym (leafσ-rwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y)))
            ■ sym (F-σ⋯ E₀ (·ₖ-VSubᵣ ρ⁻ Vτ) Θ (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) Θ (λ x → V-`)))
            ■ cong (_⋯ᶠ* Θ) (sym (F-⋯f*-fuse E₀ Vτ (·ₖ-VSubᵣ ρ⁻ Vτ)))
            ■ cong (λ EE → frame*-⋯ EE τ Vτ ⋯ᶠ* Θ) (sym Eeq) )
        frame-eq : (Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* assocSwapᵣ 1 2 ⋯ᶠ* (assocSwapᵣ 1 (syncs B) ↑* 2) ≡ Frᴿ ⋯ᶠ* ρR'
        frame-eq =
            ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁ ⋯ᶠ* ρ₂ ⋯ᶠ* weakenᵣ) (assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2)
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁ ⋯ᶠ* ρ₂) weakenᵣ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ρ₂ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2)))
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ) ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
          ■ ⋯ᶠ*-cong (frame*-⋯ E τ Vτ) ρL≗ρR
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ) Θ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR')))
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* Θ) ρ₁ᴿ (ρ₂ᴿ ·ₖ ρR'))
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* Θ ⋯ᶠ* ρ₁ᴿ) ρ₂ᴿ ρR')
          ■ cong (λ z → z ⋯ᶠ* ρ₁ᴿ ⋯ᶠ* ρ₂ᴿ ⋯ᶠ* ρR') frameLeafeqᴿ
        thread≡ : U.⟪ ((Fr ⋯ᶠ* weakenᵣ) [ ((wk ccA ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk ccC) ]*)
                        ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2) ⟫
                  ≡ subst U.Proc E-cod (subst U.Proc E-dom (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
        thread≡ =
            cong U.⟪_⟫ ( cong (_⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)) (frame-plug*ᵣ (Fr ⋯ᶠ* weakenᵣ) (assocSwapᵣ 1 2))
                       ■ frame-plug*ᵣ ((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2) )
          ■ cong U.⟪_⟫ (cong₂ _[_]* frame-eq body-eq)
          ■ cong U.⟪_⟫ (sym (frame-plug*ᵣ Frᴿ ρR'))
          ■ sym (collapseR (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫))
        νInner =
            cong₂ U._∥_ thread≡ Prest≡
          ■ sym ( rhsSplit
                ■ subst-∥f (λ z → z) (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                    (subst U.Proc (cong SQ (cong (syncs B +_) e2))
                       (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
                    (subst U.Proc (cong SQ (cong (syncs B +_) e2)) pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2)) )
        bodyEq : (U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B)
                 ≡ subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                     (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        bodyEq = cong U.ν νInner ■ sym rhsνOut
        leafRec≡ : Bφ B ((U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B))
                   ≡ subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
        leafRec≡ = cong (Bφ B) bodyEq ■ sym rhsPush
    innerReconcile =
         Bφ-cong B (Eq*.return U.νφ-comm′)
      ◅◅ Bφ-φ-comm B U.drop (U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2))
      ◅◅ U.φ-cong leafRec
    middleReconcile : Bφ C₁ (Bφ B (U.ν (U.φ U.drop contractumR)))
                      U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
    middleReconcile = Bφ-cong C₁ innerReconcile ◅◅ Eq*.symmetric _ slid
    back : Bφ C₁ (Bφ B (U.ν (U.φ U.drop contractumR))) U.≋ U[ T.ν C₁ᴿ B QR ] σ
    back = middleReconcile ◅◅ Eq*.symmetric _ rhs
