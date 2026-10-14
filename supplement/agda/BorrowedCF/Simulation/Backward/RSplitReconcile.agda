module BorrowedCF.Simulation.Backward.RSplitReconcile where
open import BorrowedCF.Terms using (module SplitRenamings)

-- | Forward-simulation cases R-LSplit and R-RSplit for the reworked
--   paper-matching (linked-φ) process definitions.  Exports U-lsplit
--   (re-exported from the SplitsRQ2 → … → SplitsH2 public chain) and U-rsplit.
--
--   Under linked-φ a cell cannot commute out of the ν that binds its channel,
--   so the channel operation fires UNDER the φ-telescope Φfull.  R-RSplit fires
--   the telescoped `RU-RSplit Φfull Fᶠ` IN PLACE (leaf-drop shape): the fresh
--   φ-drop cell is inserted at the leaf, then slid into its canonical telescope
--   position with `Brwk-slideq` (after commuting it up past `Bφ B` with
--   `Bφ-φ-comm`).  No ν-float; the transpose engine `ν-past-Bφ` is gone.

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
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation.Support.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation.Support.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)

open T using (_;_⊢ₚ_)
open import BorrowedCF.Simulation.Support.Theorems.SplitsRQ2 public

open import BorrowedCF.Simulation.Support.Theorems.PhiTel
  using ( Btel; Bφ; Uν-flatΦ; plugΦ-++; _++Φ_
        ; widthΦ; toℕ-wkΦ; widthΦ-Btel; widthΦ-++ )
open import BorrowedCF.Reduction.Processes.Untyped
  using (Φ*; []φ; _◂_; plugΦ; wkΦ; 𝓒[_×_×_])
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2
  using ( Bφ-lift-step; plugΦ-cong; Bφ-cong-c; subst-Bφ-c; φ-past-Bφ-c; Bφ-cons; subst-φ; Bφ-⋯-c )

private
  tf𝔽 : ∀ {p p'} (e : p ≡ p') (v : 𝔽 p) → Fin.toℕ (subst 𝔽 e v) ≡ Fin.toℕ v
  tf𝔽 refl v = refl
  tf𝔽h : ∀ (h : ℕ → ℕ) {x y} (e : x ≡ y) (v : 𝔽 (h x)) →
         Fin.toℕ (subst (λ j → 𝔽 (h j)) e v) ≡ Fin.toℕ v
  tf𝔽h h refl v = refl
  subst-UChan-hd : ∀ {p p'} (e : p ≡ p') (cc : UChan p) →
                   proj₁ (proj₂ (subst UChan e cc)) ≡ subst 𝔽 e (proj₁ (proj₂ cc))
  subst-UChan-hd refl cc = refl
  subst-UChan-tri : ∀ {p p'} (e : p ≡ p') (a : Tm p) (x : 𝔽 p) (b : Tm p) →
                    subst UChan e (a , x , b) ≡ (subst Tm e a , subst 𝔽 e x , subst Tm e b)
  subst-UChan-tri refl a x b = refl
  cc↓-hd-toℕ : ∀ (B₁' : BindGroup) {p} (cc : UChan p) →
               Fin.toℕ (proj₁ (proj₂ (cc↓ B₁' cc))) ≡ L.length B₁' + Fin.toℕ (proj₁ (proj₂ cc))
  cc↓-hd-toℕ []          cc            = refl
  cc↓-hd-toℕ (b ∷ B₁') {p} (e1 , x , e2) =
      cong Fin.toℕ (subst-UChan-hd (+-suc (L.length B₁') p) (cc↓ B₁' (` 0F , suc x , wk e2)))
    ■ tf𝔽 (+-suc (L.length B₁') p) (proj₁ (proj₂ (cc↓ B₁' (` 0F , suc x , wk e2))))
    ■ cc↓-hd-toℕ B₁' (` 0F , suc x , wk e2)
    ■ Nat.+-suc (L.length B₁') (Fin.toℕ x)

module _ {m n} (σ : m →ₛ n) (Vσ : VSub σ) (B₁ B₂ B : BindGroup) (q b₁ : ℕ) (s : 𝕊 0)
         (E : Frame* (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m))
         (P : T.Proc (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) where
  private module 𝐒 = SplitRenamings B₁ B₂ (sum B)
  C₁ C₁ᴿ : BindGroup
  C₁  = B₁ ++ (q + suc b₁) ∷ B₂
  C₁ᴿ = B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂
  QL : T.Proc (sum C₁ + sum B + m)
  QL = T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]* ⟫ T.∥ P
  QR : T.Proc (sum C₁ᴿ + sum B + m)
  QR = T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ⊗ (` 𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)
  sA sAᴿ sB : ℕ
  sA  = syncs C₁
  sAᴿ = syncs C₁ᴿ
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
  leafL : U.Proc (sB + (sA + (2 + n)))
  leafL = U[ QL ] τ
  hc = canonₛ-handleq B₁ {N = 2 + n} (K `unit) 0F (K `unit) q b₁ B₂
  e₁L e₂L : Tm (sB + (sA + (2 + n)))
  e₁L = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB
  e₂L = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB
  dc : 𝔽 (sB + (sA + (2 + n)))
  dc = wkΦ Φfull 0F
  mid : U.Proc n
  mid = U.ν (plugΦ Φfull leafL)
  castpos : 𝔽 (sum C₁)
  castpos = Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))
  τinj0 : τ (𝐒.atk (q ↑ʳ 0F)) ≡ canonₛ C₁ (K `unit , 0F , K `unit) castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
  τinj0 =
      cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
    ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
  wr : widthΦ Φfull ≡ sA + sB
  wr = widthΦ-++ Φ_C₁ Φ_B ■ cong₂ _+_ (widthΦ-Btel C₁ cc₁) (widthΦ-Btel B cc₂)
  junc≡ : weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc))) ≡ wkΦ Φfull 0F
  junc≡ = Fin.toℕ-injective (toℕL ■ sym toℕR)
    where
      toℕL : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) ≡ sB + sA
      toℕL = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc)))
           ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc))) ■ Nat.+-identityʳ sA)
      toℕR : Fin.toℕ (wkΦ Φfull 0F) ≡ sB + sA
      toℕR = toℕ-wkΦ Φfull 0F ■ Nat.+-identityʳ (widthΦ Φfull) ■ wr ■ Nat.+-comm sA sB
  leafσ-atk : τ (𝐒.atk (q ↑ʳ 0F)) ≡ 𝓒[ e₁L × wkΦ Φfull 0F × e₂L ]
  leafσ-atk = τinj0
            ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc))))
            ■ cong (λ z → (e₁L ⊗ (` z)) ⊗ e₂L) junc≡
  redShapeEq : (E [ K (`rsplit s) ·¹ (` 𝐒.atk (q ↑ʳ 0F)) ]*) ⋯ τ
               ≡ Fᶠ [ K (`rsplit s) ·¹ 𝓒[ e₁L × wkΦ Φfull 0F × e₂L ] ]*
  redShapeEq = frame-plug* E τ Vτ
             ■ cong (λ z → Fᶠ [ K (`rsplit s) ·¹ z ]*) leafσ-atk
  leafL-shape : leafL ≡ U.⟪ Fᶠ [ K (`rsplit s) ·¹ 𝓒[ e₁L × wkΦ Φfull 0F × e₂L ] ]* ⟫ U.∥ resid
  leafL-shape = cong (λ z → U.⟪ z ⟫ U.∥ resid) redShapeEq
  -- fired leaf-drop body (mirror of the RU-RSplit contractum at Φ = Φfull)
  bodyD : U.Proc (1 + (sB + (sA + (2 + n))))
  bodyD = U.⟪ (Fᶠ ⋯ᶠ* weakenᵣ) [ 𝓒[ wk e₁L × weakenᵣ dc × ` 0F ] ⊗ 𝓒[ ` 0F × weakenᵣ dc × wk e₂L ] ]* ⟫
            U.∥ (resid U.⋯ₚ weakenᵣ)
  fired : U.Proc n
  fired = U.ν (plugΦ Φfull (U.φ U.drop (` dc) bodyD))

  rsplit-back : ∀ {Γ : Ctx m} {γ : Struct m} → ChanCx Γ
              → Γ ; γ ⊢ₚ T.ν C₁ B QL → fired U.≋ U[ T.ν C₁ᴿ B QR ] σ
  rsplit-back Γ-S ⊢P with rsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {q = q} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  ... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq =
         ≡→≋ (cong U.ν (plugΦ-++ Φ_C₁ Φ_B (U.φ U.drop (` dc) bodyD)))
      ◅◅ U.ν-cong (Bφ-cong-c C₁ cc₁ innerReconcile)
      ◅◅ U.ν-cong (Eq*.symmetric _ slid)
      ◅◅ ≡→≋ (sym (Uν-flatΦ σ C₁ᴿ B QR))
      where
        cc₂ᴿ : UChan (sAᴿ + (2 + n))
        cc₂ᴿ = (K `unit , weaken* ⦃ Kᵣ ⦄ sAᴿ 1F , K `unit)
        τᴿ : sum C₁ᴿ + sum B + m →ₛ sB + (sAᴿ + (2 + n))
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
        residR : U.Proc (sB + (sAᴿ + (2 + n)))
        residR = U[ P T.⋯ₚ 𝐒.rwk ] τᴿ
        leafR : U.Proc (sB + (sAᴿ + (2 + n)))
        leafR = U[ QR ] τᴿ
        cz0 : 𝔽 (sA + (2 + n))
        cz0 = wkΦ Φ_C₁ 0F
        -- Brwk-slideq's transported drop cell (its exact RHS at cc₁, a = 2+n, Z = Bφ B cc₂ᴿ leafR)
        dcBR : Tm (sA + (2 + n))
        dcBR = subst Tm (sym (peel-eq B₁ (q + suc b₁) B₂ {2 + n}))
                 (subst (λ w → Tm (w + (L.length B₁ + (2 + n)))) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂)
                    ((` proj₁ (proj₂ (cc↓ B₁ cc₁))) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂))))
        ZBR : U.Proc (suc (sA + (2 + n)))
        ZBR = subst U.Proc (cong (_+ (2 + n)) (syncs-rwkq B₁ q) ■ sym (+-suc (syncs C₁) (2 + n))) (Bφ B cc₂ᴿ leafR)
                U.⋯ₚ sw-castq B₁ {q} {b₁} {B₂} {2 + n}
        dropForm : U.Proc (sA + (2 + n))
        dropForm = U.φ U.drop dcBR ZBR
        slid : Bφ C₁ᴿ cc₁ (Bφ B cc₂ᴿ leafR) U.≋ Bφ C₁ cc₁ dropForm
        slid = Brwk-slideq B₁ {q} {b₁} {B₂} {2 + n} cc₁ (Bφ B cc₂ᴿ leafR)
        chanFac : (` dc) ≡ (` cz0) ⋯ weaken* ⦃ Kᵣ ⦄ sB
        chanFac = cong `_ (Fin.toℕ-injective (dtoℕ ■ sym ctoℕ))
          where
            dtoℕ : Fin.toℕ dc ≡ sA + sB
            dtoℕ = toℕ-wkΦ Φfull 0F ■ Nat.+-identityʳ (widthΦ Φfull) ■ wr
            ctoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB cz0) ≡ sA + sB
            ctoℕ = toℕ-weaken*ᵣ sB cz0
                 ■ cong (sB +_) (toℕ-wkΦ Φ_C₁ 0F ■ Nat.+-identityʳ (widthΦ Φ_C₁) ■ widthΦ-Btel C₁ cc₁)
                 ■ Nat.+-comm sB sA
        channelEq : (` cz0) ≡ dcBR
        channelEq = cong `_ (Fin.toℕ-injective (cztoℕ ■ sym dctoℕ)) ■ sym dcBR-var
          where
            AA : ℕ
            AA = L.length B₁ + (2 + n)
            e2eq : syncs (suc b₁ ∷ B₂) ≡ syncs (q + suc b₁ ∷ B₂)
            e2eq = syncs-head-irrel (suc b₁) (q + suc b₁) B₂
            e1eq : syncs (q + suc b₁ ∷ B₂) + (L.length B₁ + (2 + n)) ≡ syncs C₁ + (2 + n)
            e1eq = sym (peel-eq B₁ (q + suc b₁) B₂ {2 + n})
            W : 𝔽 (syncs (suc b₁ ∷ B₂) + AA)
            W = weaken* ⦃ Kᵣ ⦄ (syncs (suc b₁ ∷ B₂)) (proj₁ (proj₂ (cc↓ B₁ cc₁)))
            dcBR-var : dcBR ≡ ` (subst 𝔽 e1eq (subst (λ w → 𝔽 (w + AA)) e2eq W))
            dcBR-var = cong (subst Tm e1eq) (subst-`Ff (λ w → w + AA) e2eq W)
                     ■ subst-`v e1eq (subst (λ w → 𝔽 (w + AA)) e2eq W)
            cztoℕ : Fin.toℕ cz0 ≡ sA
            cztoℕ = toℕ-wkΦ Φ_C₁ 0F ■ Nat.+-identityʳ (widthΦ Φ_C₁) ■ widthΦ-Btel C₁ cc₁
            dctoℕ : Fin.toℕ (subst 𝔽 e1eq (subst (λ w → 𝔽 (w + AA)) e2eq W)) ≡ sA
            dctoℕ = tf𝔽 e1eq (subst (λ w → 𝔽 (w + AA)) e2eq W)
                  ■ tf𝔽h (λ w → w + AA) e2eq W
                  ■ toℕ-weaken*ᵣ (syncs (suc b₁ ∷ B₂)) (proj₁ (proj₂ (cc↓ B₁ cc₁)))
                  ■ cong (syncs (suc b₁ ∷ B₂) +_) (cc↓-hd-toℕ B₁ cc₁ ■ Nat.+-identityʳ (L.length B₁))
                  ■ Nat.+-comm (syncs (suc b₁ ∷ B₂)) (L.length B₁)
                  ■ sym (syncs-split-genq B₁ q b₁ B₂)
        swc : (sA + suc (2 + n)) →ᵣ suc (sA + (2 + n))
        swc = sw-castq B₁ {q} {b₁} {B₂} {2 + n}
        E' : sAᴿ + (2 + n) ≡ sA + suc (2 + n)
        E' = cong (_+ (2 + n)) (syncs-rwkq B₁ q) ■ sym (+-suc (syncs C₁) (2 + n))
        rhsT : ZBR ≡ Bφ B (mapᶜ swc (subst UChan E' cc₂ᴿ))
                        ((subst U.Proc (cong (sB +_) E') leafR) U.⋯ₚ (swc ↑* sB))
        rhsT = cong (U._⋯ₚ swc) (subst-Bφ-c E' B cc₂ᴿ leafR)
             ■ Bφ-⋯-c B (subst UChan E' cc₂ᴿ) (subst U.Proc (cong (sB +_) E') leafR) swc
        ccEq : mapᶜ (weaken ⦃ Kᵣ ⦄) cc₂ ≡ mapᶜ swc (subst UChan E' cc₂ᴿ)
        ccEq = cong₂ _,_ ke (cong₂ _,_ midEq ke)
             ■ cong (mapᶜ swc) (sym (subst-UChan-tri E' (K `unit) (weaken* ⦃ Kᵣ ⦄ sAᴿ 1F) (K `unit)))
          where
            ke : (K `unit ⋯ weaken ⦃ Kᵣ ⦄) ≡ (subst Tm E' (K `unit) ⋯ swc)
            ke = cong (_⋯ swc) (sym (subst-Kunit E'))
            sD : ℕ
            sD = syncs ((q + suc b₁) ∷ B₂)
            v : 𝔽 (sA + suc (2 + n))
            v = subst 𝔽 E' (weaken* ⦃ Kᵣ ⦄ sAᴿ 1F)
            vtoℕ : Fin.toℕ v ≡ sAᴿ + 1
            vtoℕ = tf𝔽 E' (weaken* ⦃ Kᵣ ⦄ sAᴿ 1F) ■ toℕ-weaken*ᵣ sAᴿ 1F
            w : 𝔽 (sD + (1 + (L.length B₁ + (2 + n))))
            w = subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) v
            wtoℕ : Fin.toℕ w ≡ sAᴿ + 1
            wtoℕ = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) v ■ vtoℕ
            sD≤sAᴿ : sD Nat.≤ sAᴿ
            sD≤sAᴿ = Nat.≤-trans
                       (subst (Nat._≤ sA) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂) (sD≤q B₁ q {b₁} {B₂}))
                       (subst (sA Nat.≤_) (sym (syncs-rwkq B₁ q)) (Nat.n≤1+n sA))
            hge : sD + 1 Nat.≤ Fin.toℕ w
            hge = subst (sD + 1 Nat.≤_) (sym wtoℕ) (Nat.+-monoˡ-≤ 1 sD≤sAᴿ)
            midEq : weaken ⦃ Kᵣ ⦄ (weaken* ⦃ Kᵣ ⦄ sA 1F) ≡ swc v
            midEq = Fin.toℕ-injective
              ( cong suc (toℕ-weaken*ᵣ sA 1F)
              ■ sym ( toℕ-subst₂ᵣ (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n})) (sw-codq B₁ {q} {b₁} {B₂} {2 + n})
                        (assocSwapᵣ sD 1 {L.length B₁ + (2 + n)}) v
                    ■ toℕ-assoc-ge sD 1 {L.length B₁ + (2 + n)} w hge
                    ■ wtoℕ
                    ■ cong (_+ 1) (syncs-rwkq B₁ q) ) )
        Fᶠᴿ : Frame* (sB + (sAᴿ + (2 + n)))
        Fᶠᴿ = frame*-⋯ (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ
        gtri : Tm (sB + (sAᴿ + (2 + n)))
        gtri = τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
                 ⊗ τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F))
        leafRshape : leafR ≡ U.⟪ Fᶠᴿ [ gtri ]* ⟫ U.∥ residR
        leafRshape = cong (λ z → U.⟪ z ⟫ U.∥ residR) (frame-plug* (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ)
        rhsD : (subst U.Proc (cong (sB +_) E') leafR) U.⋯ₚ (swc ↑* sB)
               ≡ (subst U.Proc (cong (sB +_) E') (U.⟪ Fᶠᴿ [ gtri ]* ⟫) U.⋯ₚ (swc ↑* sB))
                 U.∥ (subst U.Proc (cong (sB +_) E') residR U.⋯ₚ (swc ↑* sB))
        rhsD = cong (λ z → subst U.Proc (cong (sB +_) E') z U.⋯ₚ (swc ↑* sB)) leafRshape
             ■ cong (U._⋯ₚ (swc ↑* sB))
                 ( substcong E' (U.⟪ Fᶠᴿ [ gtri ]* ⟫ U.∥ residR)
                 ■ subst-∥f (sB +_) E' (U.⟪ Fᶠᴿ [ gtri ]* ⟫) residR
                 ■ cong₂ U._∥_ (sym (substcong E' (U.⟪ Fᶠᴿ [ gtri ]* ⟫))) (sym (substcong E' residR)) )
          where
            substcong : ∀ {a b} (e : a ≡ b) (t : U.Proc (sB + a)) →
                        subst U.Proc (cong (sB +_) e) t ≡ subst (λ z → U.Proc (sB + z)) e t
            substcong refl t = refl
        Prwkeq : residR ≡ resid U.⋯ₚ (sinsq B₁ q b₁ B₂ {2 + n} ↑* sB)
        Prwkeq =
            cong (λ p → U[ p T.⋯ₚ 𝐒.rwk ] τᴿ) Peq
          ■ cong (λ p → U[ p ] τᴿ) (T.fusionₚ P₀ ρ⁻ 𝐒.rwk)
          ■ U-⋯ₚ P₀
          ■ U-cong P₀ (λ y → sym (leafσ-rwk-idq σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y)))
          ■ sym (U-σ⋯ P₀)
          ■ cong (U._⋯ₚ (sinsq B₁ q b₁ B₂ {2 + n} ↑* sB)) (sym (U-⋯ₚ P₀))
          ■ cong (λ p → U[ p ] τ U.⋯ₚ (sinsq B₁ q b₁ B₂ {2 + n} ↑* sB)) (sym Peq)
        substcod : ∀ {a c d} (e : c ≡ d) (Q : U.Proc a) (θ : a →ᵣ c) →
                   subst U.Proc e (Q U.⋯ₚ θ) ≡ Q U.⋯ₚ subst (λ z → a →ᵣ z) e θ
        substcod refl Q θ = refl
        sinsρ : (sB + (sA + (2 + n))) →ᵣ (sB + (sAᴿ + (2 + n)))
        sinsρ = sinsq B₁ q b₁ B₂ {2 + n} ↑* sB
        ρL ρR : (sB + (sA + (2 + n))) →ᵣ (sB + suc (sA + (2 + n)))
        ρL = weakenᵣ ·ₖ assocSwapᵣ 1 sB
        ρR = subst (λ z → (sB + (sA + (2 + n))) →ᵣ z) (cong (sB +_) E') sinsρ ·ₖ (swc ↑* sB)
        sD' : ℕ
        sD' = syncs (suc b₁ ∷ B₂)
        sr : (sB + (sA + (2 + n))) →ᵣ (sB + (sA + suc (2 + n)))
        sr = subst (λ z → (sB + (sA + (2 + n))) →ᵣ z) (cong (sB +_) E') sinsρ
        srtoℕ : ∀ (i : 𝔽 (sB + (sA + (2 + n)))) → Fin.toℕ (sr i) ≡ Fin.toℕ (sinsρ i)
        srtoℕ i = toℕ-subst-cod (cong (sB +_) E') sinsρ i
        -- toℕ of sinsρ i by region
        wtoℕ : ∀ (i : 𝔽 (sB + (sA + (2 + n)))) → Fin.toℕ (weakenᵣ i) ≡ suc (Fin.toℕ i)
        wtoℕ i = toℕ-weaken*ᵣ 1 i
        ρL≗ρR : ρL ≗ ρR
        ρL≗ρR i with Fin.toℕ i Nat.<? sB
        ... | yes p = Fin.toℕ-injective (lhs ■ sym rhs)
          where
            lhs : Fin.toℕ (ρL i) ≡ Fin.toℕ i
            lhs = toℕ-assoc-mid 1 sB (weakenᵣ i)
                    (subst (1 Nat.≤_) (sym (wtoℕ i)) (Nat.s≤s Nat.z≤n))
                    (subst (Nat._< 1 + sB) (sym (wtoℕ i)) (Nat.s≤s p))
                ■ cong (Nat._∸ 1) (wtoℕ i)
            sinsρtoℕ : Fin.toℕ (sinsρ i) ≡ Fin.toℕ i
            sinsρtoℕ = toℕ-↑*-lt (sinsq B₁ q b₁ B₂ {2 + n}) sB i p
            rhs : Fin.toℕ (ρR i) ≡ Fin.toℕ i
            rhs = toℕ-↑*-lt swc sB (sr i) (subst (Nat._< sB) (sym (srtoℕ i ■ sinsρtoℕ)) p)
                ■ srtoℕ i ■ sinsρtoℕ
        ... | no ¬p = Fin.toℕ-injective (lhs ■ sym rhs)
          where
            sB≤i : sB Nat.≤ Fin.toℕ i
            sB≤i = Nat.≮⇒≥ ¬p
            r : ℕ
            r = Fin.toℕ i Nat.∸ sB
            recon : sB + r ≡ Fin.toℕ i
            recon = Nat.m+[n∸m]≡n sB≤i
            lhs : Fin.toℕ (ρL i) ≡ suc (Fin.toℕ i)
            lhs = toℕ-assoc-ge 1 sB (weakenᵣ i)
                    (subst (1 + sB Nat.≤_) (sym (wtoℕ i)) (Nat.s≤s sB≤i))
                ■ wtoℕ i
            ri : 𝔽 (sA + (2 + n))
            ri = Fin.reduce≥ i sB≤i
            ritoℕ : Fin.toℕ ri ≡ r
            ritoℕ = toℕ-reduce≥ i sB≤i
            sinsρtoℕ-ge : Fin.toℕ (sinsρ i) ≡ sB + Fin.toℕ (sinsq B₁ q b₁ B₂ {2 + n} ri)
            sinsρtoℕ-ge = toℕ-↑*-ge (sinsq B₁ q b₁ B₂ {2 + n}) sB i sB≤i
            sDq : ℕ
            sDq = syncs ((q + suc b₁) ∷ B₂)
            HI : sD' ≡ sDq
            HI = syncs-head-irrel (suc b₁) (q + suc b₁) B₂
            rhs : Fin.toℕ (ρR i) ≡ suc (Fin.toℕ i)
            rhs with Fin.toℕ ri Nat.<? sD'
            ... | yes rlo =
                    toℕ-↑*-ge swc sB (sr i) sB≤sr
                  ■ cong (sB +_) ( toℕ-subst₂ᵣ (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n})) (sw-codq B₁ {q} {b₁} {B₂} {2 + n})
                                     (assocSwapᵣ sDq 1 {L.length B₁ + (2 + n)}) (Fin.reduce≥ (sr i) sB≤sr)
                                 ■ toℕ-assoc-lt sDq 1 _ (subst (Nat._< sDq) (sym redsr) (subst (Fin.toℕ ri Nat.<_) HI rlo))
                                 ■ cong (1 +_) redsr )
                  ■ cong (λ z → sB + suc z) ritoℕ
                  ■ Nat.+-suc sB r ■ cong suc recon
              where
                sinsr≡ : Fin.toℕ (sinsq B₁ q b₁ B₂ {2 + n} ri) ≡ Fin.toℕ ri
                sinsr≡ = sins-toℕ-loq B₁ q b₁ B₂ ri rlo
                srtoℕ-ge : Fin.toℕ (sr i) ≡ sB + Fin.toℕ ri
                srtoℕ-ge = srtoℕ i ■ sinsρtoℕ-ge ■ cong (sB +_) sinsr≡
                sB≤sr : sB Nat.≤ Fin.toℕ (sr i)
                sB≤sr = subst (sB Nat.≤_) (sym srtoℕ-ge) (Nat.m≤m+n sB (Fin.toℕ ri))
                redsr : Fin.toℕ (subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (sr i) sB≤sr)) ≡ Fin.toℕ ri
                redsr = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (sr i) sB≤sr)
                      ■ toℕ-reduce≥ (sr i) sB≤sr ■ cong (Nat._∸ sB) srtoℕ-ge ■ Nat.m+n∸m≡n sB (Fin.toℕ ri)
            ... | no ¬rlo =
                    toℕ-↑*-ge swc sB (sr i) sB≤sr
                  ■ cong (sB +_) ( toℕ-subst₂ᵣ (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n})) (sw-codq B₁ {q} {b₁} {B₂} {2 + n})
                                     (assocSwapᵣ sDq 1 {L.length B₁ + (2 + n)}) (Fin.reduce≥ (sr i) sB≤sr)
                                 ■ toℕ-assoc-ge sDq 1 _ (subst (sDq + 1 Nat.≤_) (sym redsr) sDq+1≤)
                                 ■ redsr )
                  ■ cong (λ z → sB + suc z) ritoℕ
                  ■ Nat.+-suc sB r ■ cong suc recon
              where
                sinsr≡' : Fin.toℕ (sinsq B₁ q b₁ B₂ {2 + n} ri) ≡ suc (Fin.toℕ ri)
                sinsr≡' = sins-toℕ-hiq B₁ q b₁ B₂ ri (Nat.≮⇒≥ ¬rlo)
                srtoℕ-ge : Fin.toℕ (sr i) ≡ sB + suc (Fin.toℕ ri)
                srtoℕ-ge = srtoℕ i ■ sinsρtoℕ-ge ■ cong (sB +_) sinsr≡'
                sB≤sr : sB Nat.≤ Fin.toℕ (sr i)
                sB≤sr = subst (sB Nat.≤_) (sym srtoℕ-ge) (Nat.m≤m+n sB (suc (Fin.toℕ ri)))
                redsr : Fin.toℕ (subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (sr i) sB≤sr)) ≡ suc (Fin.toℕ ri)
                redsr = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (sr i) sB≤sr)
                      ■ toℕ-reduce≥ (sr i) sB≤sr ■ cong (Nat._∸ sB) srtoℕ-ge ■ Nat.m+n∸m≡n sB (suc (Fin.toℕ ri))
                sDq+1≤ : sDq + 1 Nat.≤ suc (Fin.toℕ ri)
                sDq+1≤ = subst (Nat._≤ suc (Fin.toℕ ri)) (Nat.+-comm 1 sDq)
                           (Nat.s≤s (subst (Nat._≤ Fin.toℕ ri) HI (Nat.≮⇒≥ ¬rlo)))
        threadEq : (U.⟪ (Fᶠ ⋯ᶠ* weakenᵣ) [ 𝓒[ wk e₁L × weakenᵣ dc × ` 0F ] ⊗ 𝓒[ ` 0F × weakenᵣ dc × wk e₂L ] ]* ⟫) U.⋯ₚ assocSwapᵣ 1 sB
                   ≡ (subst U.Proc (cong (sB +_) E') (U.⟪ Fᶠᴿ [ gtri ]* ⟫) U.⋯ₚ (swc ↑* sB))
        threadEq =
            cong U.⟪_⟫ (frame-plug*ᵣ (Fᶠ ⋯ᶠ* weakenᵣ) (assocSwapᵣ 1 sB))
          ■ cong U.⟪_⟫ (cong₂ _[_]* frame-eq triple-eq)
          ■ sym rhsThread
          where
            substcong2 : ∀ {a b} (e : a ≡ b) (t : U.Proc (sB + a)) →
                         subst U.Proc (cong (sB +_) e) t ≡ subst (λ z → U.Proc (sB + z)) e t
            substcong2 refl t = refl
            frameR : Frame* (sB + (sA + suc (2 + n)))
            frameR = subst (λ z → Frame* (sB + z)) E' Fᶠᴿ
            gtriR : Tm (sB + (sA + suc (2 + n)))
            gtriR = subst (λ z → Tm (sB + z)) E' gtri
            rhsThread : subst U.Proc (cong (sB +_) E') (U.⟪ Fᶠᴿ [ gtri ]* ⟫) U.⋯ₚ (swc ↑* sB)
                        ≡ U.⟪ (frameR ⋯ᶠ* (swc ↑* sB)) [ gtriR ⋯ (swc ↑* sB) ]* ⟫
            rhsThread =
                cong (U._⋯ₚ (swc ↑* sB))
                  ( substcong2 E' (U.⟪ Fᶠᴿ [ gtri ]* ⟫)
                  ■ subst-⟪⟫f (sB +_) E' (Fᶠᴿ [ gtri ]*)
                  ■ cong U.⟪_⟫ (subst-frame-plug (sB +_) E' Fᶠᴿ gtri) )
              ■ cong U.⟪_⟫ (frame-plug*ᵣ frameR (swc ↑* sB))
            frame-⋯-cod : ∀ {a c d} (e : c ≡ d) (Ef : Frame* a) (ρ : a →ᵣ c) →
                          Ef ⋯ᶠ* subst (λ z → a →ᵣ z) e ρ ≡ subst Frame* e (Ef ⋯ᶠ* ρ)
            frame-⋯-cod refl Ef ρ = refl
            substcong-frame : ∀ {a b} (e : a ≡ b) (t : Frame* (sB + a)) →
                              subst Frame* (cong (sB +_) e) t ≡ subst (λ z → Frame* (sB + z)) e t
            substcong-frame refl t = refl
            frameLeafeqᴿ : Fᶠ ⋯ᶠ* sinsρ ≡ Fᶠᴿ
            frameLeafeqᴿ = sym
                ( cong (λ EE → frame*-⋯ (EE ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ) Eeq
                ■ cong (λ EE → frame*-⋯ EE τᴿ Vτᴿ) (⋯ᶠ*-fuse E₀ ρ⁻ 𝐒.rwk)
                ■ F-⋯f*-fuse E₀ Vτᴿ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ)
                ■ frame*-cong E₀ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ)
                    (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) sinsρ (λ x → V-`))
                    (λ y → sym (leafσ-rwk-idq σ B₁ B₂ B q b₁ (ρ⁻ y) (ρ⁻-skip y)))
                ■ sym (F-σ⋯ E₀ (·ₖ-VSubᵣ ρ⁻ Vτ) sinsρ (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) sinsρ (λ x → V-`)))
                ■ cong (_⋯ᶠ* sinsρ) (sym (F-⋯f*-fuse E₀ Vτ (·ₖ-VSubᵣ ρ⁻ Vτ)))
                ■ cong (λ EE → frame*-⋯ EE τ Vτ ⋯ᶠ* sinsρ) (sym Eeq) )
            frameSrEq : Fᶠ ⋯ᶠ* sr ≡ frameR
            frameSrEq = frame-⋯-cod (cong (sB +_) E') Fᶠ sinsρ
                      ■ cong (subst Frame* (cong (sB +_) E')) frameLeafeqᴿ
                      ■ substcong-frame E' Fᶠᴿ
            frame-eq : ((Fᶠ ⋯ᶠ* weakenᵣ) ⋯ᶠ* assocSwapᵣ 1 sB) ≡ (frameR ⋯ᶠ* (swc ↑* sB))
            frame-eq =
                ⋯ᶠ*-fuse Fᶠ weakenᵣ (assocSwapᵣ 1 sB)
              ■ ⋯ᶠ*-cong Fᶠ ρL≗ρR
              ■ sym (⋯ᶠ*-fuse Fᶠ sr (swc ↑* sB))
              ■ cong (_⋯ᶠ* (swc ↑* sB)) frameSrEq
            triple-eq : ((𝓒[ wk e₁L × weakenᵣ dc × ` 0F ] ⊗ 𝓒[ ` 0F × weakenᵣ dc × wk e₂L ]) ⋯ assocSwapᵣ 1 sB)
                        ≡ (gtriR ⋯ (swc ↑* sB))
            triple-eq = cong₂ _⊗_ inj0eq inj1eq
                      ■ cong (_⋯ (swc ↑* sB))
                          (sym (subst-⊗f (λ z → sB + z) E'
                                 (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))))
                                 (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)))))
              where
                tm-⋯-cod : ∀ {a c d} (e : c ≡ d) (t : Tm a) (ρ : a →ᵣ c) →
                           t ⋯ subst (λ z → a →ᵣ z) e ρ ≡ subst Tm e (t ⋯ ρ)
                tm-⋯-cod refl t ρ = refl
                substcong-Tm : ∀ {a b} (e : a ≡ b) (t : Tm (sB + a)) →
                               subst Tm (cong (sB +_) e) t ≡ subst (λ z → Tm (sB + z)) e t
                substcong-Tm refl t = refl
                slotSrEq : ∀ (t : Tm (sB + (sA + (2 + n)))) →
                           t ⋯ weakenᵣ ⋯ assocSwapᵣ 1 sB
                           ≡ subst (λ z → Tm (sB + z)) E' (t ⋯ sinsρ) ⋯ (swc ↑* sB)
                slotSrEq t =
                    fusion t weakenᵣ (assocSwapᵣ 1 sB)
                  ■ ⋯-cong t ρL≗ρR
                  ■ sym (fusion t sr (swc ↑* sB))
                  ■ cong (_⋯ (swc ↑* sB)) (tm-⋯-cod (cong (sB +_) E') t sinsρ ■ substcong-Tm E' (t ⋯ sinsρ))
                -- inj0 : fresh q+1 channel handle
                hcᴿ0 = canonₛ-handleq B₁ (K `unit) 0F (K `unit) q 0 (suc b₁ ∷ B₂)
                castposᴿ0 : 𝔽 (sum C₁ᴿ)
                castposᴿ0 = Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
                τᴿinj0 : τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂))) ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ sB
                τᴿinj0 =
                    cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum B) (castposᴿ0 ↑ˡ sum B) m)
                  ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ0 (sum B))
                τᴿinj0-full : τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))
                             ≡ ((proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hcᴿ0)))))
                               ⊗ (proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                τᴿinj0-full = τᴿinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hcᴿ0))))
                slotL0 : proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ sB ≡ e₁L ⋯ sinsρ
                slotL0 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (handle-L-rwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂)
                       ■ ⋯-↑*-wk (proj₁ hc) (sinsq B₁ q b₁ B₂ {2 + n}) sB
                v0 = proj₁ (handle-R0-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂)
                eq0 = proj₁ (proj₂ (handle-R0-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂))
                tn0 = proj₂ (proj₂ (handle-R0-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂))
                sDq : ℕ
                sDq = syncs ((q + suc b₁) ∷ B₂)
                sD'q : ℕ
                sD'q = syncs (suc b₁ ∷ B₂)
                HIq : sD'q ≡ sDq
                HIq = syncs-head-irrel (suc b₁) (q + suc b₁) B₂
                sDq≤sA : sDq Nat.≤ sA
                sDq≤sA = subst (Nat._≤ sA) HIq (sD≤q B₁ q {b₁} {B₂})
                dctoℕ : Fin.toℕ dc ≡ sA + sB
                dctoℕ = toℕ-wkΦ Φfull 0F ■ Nat.+-identityʳ (widthΦ Φfull) ■ wr
                sTm : Tm (sB + (sAᴿ + (2 + n))) → Tm (sB + (sA + suc (2 + n)))
                sTm = subst (λ z → Tm (sB + z)) E'
                s𝔽 : 𝔽 (sB + (sAᴿ + (2 + n))) → 𝔽 (sB + (sA + suc (2 + n)))
                s𝔽 = subst (λ z → 𝔽 (sB + z)) E'
                s𝔽toℕ : ∀ (w : 𝔽 (sB + (sAᴿ + (2 + n)))) → Fin.toℕ (s𝔽 w) ≡ Fin.toℕ w
                s𝔽toℕ w = tf𝔽h (λ z → sB + z) E' w
                -- swc ↑* sB applied to a var in the ge (≥ sB) region: reduce, cross swc
                swcUp-ge : ∀ (w : 𝔽 (sB + (sA + suc (2 + n)))) (le : sB Nat.≤ Fin.toℕ w) →
                           Fin.toℕ ((swc ↑* sB) w)
                           ≡ sB + Fin.toℕ (assocSwapᵣ sDq 1 {L.length B₁ + (2 + n)}
                                            (subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ w le)))
                swcUp-ge w le = toℕ-↑*-ge swc sB w le
                              ■ cong (sB +_) (toℕ-subst₂ᵣ (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n})) (sw-codq B₁ {q} {b₁} {B₂} {2 + n})
                                               (assocSwapᵣ sDq 1 {L.length B₁ + (2 + n)}) (Fin.reduce≥ w le))
                inj0eq : (𝓒[ wk e₁L × weakenᵣ dc × ` 0F ]) ⋯ assocSwapᵣ 1 sB
                         ≡ subst (λ z → Tm (sB + z)) E' (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) ⋯ (swc ↑* sB)
                inj0eq =
                    cong₂ _⊗_ (cong₂ _⊗_ Ldata juncEq0) dropEq0
                  ■ sym rhsInj0
                  where
                    L0 R0 : Tm (sB + (sAᴿ + (2 + n)))
                    L0 = proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ sB
                    R0 = proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ sB
                    junc0 : 𝔽 (sB + (sAᴿ + (2 + n)))
                    junc0 = weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hcᴿ0)))
                    rhsInj0 : sTm (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁ + sum B₂)))) ⋯ (swc ↑* sB)
                              ≡ ((sTm L0 ⋯ (swc ↑* sB)) ⊗ (` (swc ↑* sB) (s𝔽 junc0))) ⊗ (sTm R0 ⋯ (swc ↑* sB))
                    rhsInj0 = cong (λ z → sTm z ⋯ (swc ↑* sB)) τᴿinj0-full
                            ■ cong (_⋯ (swc ↑* sB))
                                ( subst-⊗f (λ z → sB + z) E' (L0 ⊗ (` junc0)) R0
                                ■ cong (_⊗ sTm R0)
                                    ( subst-⊗f (λ z → sB + z) E' L0 (` junc0)
                                    ■ cong (sTm L0 ⊗_) (subst-`Ff (λ z → sB + z) E' junc0) ) )
                    Ldata : wk e₁L ⋯ assocSwapᵣ 1 sB ≡ sTm L0 ⋯ (swc ↑* sB)
                    Ldata = slotSrEq e₁L ■ cong (λ z → sTm z ⋯ (swc ↑* sB)) (sym slotL0)
                    juncEq0 : (` assocSwapᵣ 1 sB (weakenᵣ dc)) ≡ (` (swc ↑* sB) (s𝔽 junc0))
                    juncEq0 = cong `_ (Fin.toℕ-injective (lhsJ ■ sym rhsJ))
                      where
                        wdc : Fin.toℕ (weakenᵣ dc) ≡ suc (sA + sB)
                        wdc = wtoℕ dc ■ cong suc dctoℕ
                        lhsJ : Fin.toℕ (assocSwapᵣ 1 sB (weakenᵣ dc)) ≡ suc (sB + sA)
                        lhsJ = toℕ-assoc-ge 1 sB (weakenᵣ dc) (subst (1 + sB Nat.≤_) (sym wdc) (Nat.s≤s (Nat.m≤n+m sB sA)))
                             ■ wdc ■ cong suc (Nat.+-comm sA sB)
                        jv : Fin.toℕ (s𝔽 junc0) ≡ sB + sAᴿ
                        jv = s𝔽toℕ junc0 ■ toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hcᴿ0)))
                           ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hcᴿ0))) ■ Nat.+-identityʳ sAᴿ)
                        jle : sB Nat.≤ Fin.toℕ (s𝔽 junc0)
                        jle = subst (sB Nat.≤_) (sym jv) (Nat.m≤m+n sB sAᴿ)
                        wpos = subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 junc0) jle)
                        wpostoℕ : Fin.toℕ wpos ≡ sAᴿ
                        wpostoℕ = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 junc0) jle)
                                ■ toℕ-reduce≥ (s𝔽 junc0) jle ■ cong (Nat._∸ sB) jv ■ Nat.m+n∸m≡n sB sAᴿ
                        sDq1≤ : sDq + 1 Nat.≤ sAᴿ
                        sDq1≤ = subst (Nat._≤ sAᴿ) (Nat.+-comm 1 sDq)
                                  (subst (suc sDq Nat.≤_) (sym (syncs-rwkq B₁ q)) (Nat.s≤s sDq≤sA))
                        rhsJ : Fin.toℕ ((swc ↑* sB) (s𝔽 junc0)) ≡ suc (sB + sA)
                        rhsJ = swcUp-ge (s𝔽 junc0) jle
                             ■ cong (sB +_) (toℕ-assoc-ge sDq 1 wpos (subst (sDq + 1 Nat.≤_) (sym wpostoℕ) sDq1≤) ■ wpostoℕ ■ syncs-rwkq B₁ q)
                             ■ Nat.+-suc sB sA
                    dropEq0 : (` assocSwapᵣ 1 sB 0F) ≡ (sTm R0 ⋯ (swc ↑* sB))
                    dropEq0 = cong `_ (Fin.toℕ-injective (lhsD ■ sym rhsD0)) ■ sym R0asvar
                      where
                        R0asvar : sTm R0 ⋯ (swc ↑* sB) ≡ (` (swc ↑* sB) (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)))
                        R0asvar = cong (λ z → sTm z ⋯ (swc ↑* sB)) (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) eq0)
                                ■ cong (_⋯ (swc ↑* sB)) (subst-`Ff (λ z → sB + z) E' (weaken* ⦃ Kᵣ ⦄ sB v0))
                        wv : Fin.toℕ (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)) ≡ sB + sDq
                        wv = s𝔽toℕ (weaken* ⦃ Kᵣ ⦄ sB v0) ■ toℕ-weaken*ᵣ sB v0 ■ cong (sB +_) (tn0 ■ HIq)
                        wle : sB Nat.≤ Fin.toℕ (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0))
                        wle = subst (sB Nat.≤_) (sym wv) (Nat.m≤m+n sB sDq)
                        wpos = subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)) wle)
                        wpostoℕ : Fin.toℕ wpos ≡ sDq
                        wpostoℕ = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)) wle)
                                ■ toℕ-reduce≥ (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)) wle ■ cong (Nat._∸ sB) wv ■ Nat.m+n∸m≡n sB sDq
                        lhsD : Fin.toℕ (assocSwapᵣ 1 sB 0F) ≡ sB
                        lhsD = toℕ-assoc-lt 1 sB 0F (Nat.s≤s Nat.z≤n) ■ Nat.+-identityʳ sB
                        rhsD0 : Fin.toℕ ((swc ↑* sB) (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0))) ≡ sB
                        rhsD0 = swcUp-ge (s𝔽 (weaken* ⦃ Kᵣ ⦄ sB v0)) wle
                              ■ cong (sB +_) (toℕ-assoc-mid sDq 1 wpos
                                                (subst (sDq Nat.≤_) (sym wpostoℕ) Nat.≤-refl)
                                                (subst (Nat._< sDq + 1) (sym wpostoℕ) (subst (sDq Nat.<_) (Nat.+-comm 1 sDq) (Nat.n<1+n sDq)))
                                            ■ cong (Nat._∸ sDq) wpostoℕ ■ Nat.n∸n≡0 sDq)
                              ■ Nat.+-identityʳ sB
                hcᴿ1 = canonₛ-handle (B₁ ++ (q + 1) ∷ []) (K `unit) 0F (K `unit) b₁ B₂
                passocᴿ : (B₁ ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂ ≡ C₁ᴿ
                passocᴿ = ++-assoc B₁ ((q + 1) ∷ []) (suc b₁ ∷ B₂)
                castRRᴿ : syncs ((B₁ ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂) + (2 + n) ≡ syncs C₁ᴿ + (2 + n)
                castRRᴿ = cong (λ z → syncs z + (2 + n)) passocᴿ
                posᴿ1 : 𝔽 (sum ((B₁ ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂))
                posᴿ1 = Fin.cast (sym (sum-++ (B₁ ++ (q + 1) ∷ []) (suc b₁ ∷ B₂))) (sum (B₁ ++ (q + 1) ∷ []) ↑ʳ 0F)
                j0ᴿ = proj₁ (proj₂ (proj₂ hcᴿ1))
                castposᴿ1 : 𝔽 (sum C₁ᴿ)
                castposᴿ1 = Fin.cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F))
                τᴿinj1 : τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F)) ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1 ⋯ weaken* ⦃ Kᵣ ⦄ sB
                τᴿinj1 =
                    cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum B) (castposᴿ1 ↑ˡ sum B) m)
                  ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ1 (sum B))
                tf𝔽L : ∀ {L1 L2 : BindGroup} (p : L1 ≡ L2) (y : 𝔽 (sum L1)) →
                       Fin.toℕ (subst (λ L → 𝔽 (sum L)) p y) ≡ Fin.toℕ y
                tf𝔽L refl y = refl
                posEqᴿ : castposᴿ1 ≡ subst (λ L → 𝔽 (sum L)) passocᴿ posᴿ1
                posEqᴿ = Fin.toℕ-injective
                  ( (Fin.toℕ-cast (sym (sum-++ B₁ ((q + 1) ∷ suc b₁ ∷ B₂))) (sum B₁ ↑ʳ ((q + 1) ↑ʳ 0F))
                     ■ Fin.toℕ-↑ʳ (sum B₁) ((q + 1) ↑ʳ 0F)
                     ■ cong (sum B₁ +_) (Fin.toℕ-↑ʳ (q + 1) 0F ■ Nat.+-identityʳ (q + 1)))
                  ■ sym ( tf𝔽L passocᴿ posᴿ1
                        ■ Fin.toℕ-cast (sym (sum-++ (B₁ ++ (q + 1) ∷ []) (suc b₁ ∷ B₂))) (sum (B₁ ++ (q + 1) ∷ []) ↑ʳ 0F)
                        ■ Fin.toℕ-↑ʳ (sum (B₁ ++ (q + 1) ∷ [])) 0F
                        ■ Nat.+-identityʳ (sum (B₁ ++ (q + 1) ∷ []))
                        ■ sum-++ B₁ ((q + 1) ∷ [])
                        ■ cong (sum B₁ +_) (Nat.+-identityʳ (q + 1)) ) )
                canonᴿ1-decomp : canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1
                                 ≡ ((subst Tm castRRᴿ (proj₁ hcᴿ1)) ⊗ (` subst 𝔽 castRRᴿ j0ᴿ))
                                   ⊗ subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1))
                canonᴿ1-decomp =
                    cong (canonₛ C₁ᴿ (K `unit , 0F , K `unit)) posEqᴿ
                  ■ canonₛ-cast passocᴿ (K `unit , 0F , K `unit) posᴿ1
                  ■ subst-syncs passocᴿ (canonₛ ((B₁ ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂) (K `unit , 0F , K `unit) posᴿ1)
                  ■ cong (subst Tm castRRᴿ) (proj₁ (proj₂ (proj₂ (proj₂ hcᴿ1))))
                  ■ substTripⱼ castRRᴿ (proj₁ hcᴿ1) j0ᴿ (proj₁ (proj₂ hcᴿ1))
                τᴿinj1-full : τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F))
                             ≡ ((subst Tm castRRᴿ (proj₁ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⊗ (` weaken* ⦃ Kᵣ ⦄ sB (subst 𝔽 castRRᴿ j0ᴿ)))
                               ⊗ (subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                τᴿinj1-full = τᴿinj1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) canonᴿ1-decomp
                slotR1 : subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ sB ≡ e₂L ⋯ sinsρ
                slotR1 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (handle-R-rwkq B₁ (K `unit) 0F (K `unit) q b₁ B₂)
                       ■ ⋯-↑*-wk (proj₁ (proj₂ hc)) (sinsq B₁ q b₁ B₂ {2 + n}) sB
                v1 = proj₁ (handle-L1-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂)
                eq1 = proj₁ (proj₂ (handle-L1-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂))
                tn1 = proj₂ (proj₂ (handle-L1-varq B₁ {2 + n} (K `unit) 0F (K `unit) q b₁ B₂))
                L1var : subst Tm castRRᴿ (proj₁ hcᴿ1) ≡ ` (subst 𝔽 castRRᴿ v1)
                L1var = cong (subst Tm castRRᴿ) eq1 ■ subst-`v castRRᴿ v1
                inj1eq : (𝓒[ ` 0F × weakenᵣ dc × wk e₂L ]) ⋯ assocSwapᵣ 1 sB
                         ≡ subst (λ z → Tm (sB + z)) E' (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F))) ⋯ (swc ↑* sB)
                inj1eq =
                    cong₂ _⊗_ (cong₂ _⊗_ dropEq1 juncEq1) Rdata
                  ■ sym rhsInj1
                  where
                    L1 R1 : Tm (sB + (sAᴿ + (2 + n)))
                    L1 = subst Tm castRRᴿ (proj₁ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ sB
                    R1 = subst Tm castRRᴿ (proj₁ (proj₂ hcᴿ1)) ⋯ weaken* ⦃ Kᵣ ⦄ sB
                    junc1 : 𝔽 (sB + (sAᴿ + (2 + n)))
                    junc1 = weaken* ⦃ Kᵣ ⦄ sB (subst 𝔽 castRRᴿ j0ᴿ)
                    dv : 𝔽 (sB + (sAᴿ + (2 + n)))
                    dv = weaken* ⦃ Kᵣ ⦄ sB (subst 𝔽 castRRᴿ v1)
                    rhsInj1 : sTm (τᴿ (𝐒.inj {B = (q + 1) ∷ suc b₁ ∷ []} ((q + 1) ↑ʳ 0F))) ⋯ (swc ↑* sB)
                              ≡ ((sTm L1 ⋯ (swc ↑* sB)) ⊗ (` (swc ↑* sB) (s𝔽 junc1))) ⊗ (sTm R1 ⋯ (swc ↑* sB))
                    rhsInj1 = cong (λ z → sTm z ⋯ (swc ↑* sB)) τᴿinj1-full
                            ■ cong (_⋯ (swc ↑* sB))
                                ( subst-⊗f (λ z → sB + z) E' (L1 ⊗ (` junc1)) R1
                                ■ cong (_⊗ sTm R1)
                                    ( subst-⊗f (λ z → sB + z) E' L1 (` junc1)
                                    ■ cong (sTm L1 ⊗_) (subst-`Ff (λ z → sB + z) E' junc1) ) )
                    L1asvar : sTm L1 ⋯ (swc ↑* sB) ≡ (` (swc ↑* sB) (s𝔽 dv))
                    L1asvar = cong (λ z → sTm z ⋯ (swc ↑* sB)) (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) L1var)
                            ■ cong (_⋯ (swc ↑* sB)) (subst-`Ff (λ z → sB + z) E' dv)
                    Rdata : wk e₂L ⋯ assocSwapᵣ 1 sB ≡ sTm R1 ⋯ (swc ↑* sB)
                    Rdata = slotSrEq e₂L ■ cong (λ z → sTm z ⋯ (swc ↑* sB)) (sym slotR1)
                    juncEq1 : (` assocSwapᵣ 1 sB (weakenᵣ dc)) ≡ (` (swc ↑* sB) (s𝔽 junc1))
                    juncEq1 = cong `_ (Fin.toℕ-injective (lhsJ ■ sym rhsJ))
                      where
                        wdc : Fin.toℕ (weakenᵣ dc) ≡ suc (sA + sB)
                        wdc = wtoℕ dc ■ cong suc dctoℕ
                        lhsJ : Fin.toℕ (assocSwapᵣ 1 sB (weakenᵣ dc)) ≡ suc (sB + sA)
                        lhsJ = toℕ-assoc-ge 1 sB (weakenᵣ dc) (subst (1 + sB Nat.≤_) (sym wdc) (Nat.s≤s (Nat.m≤n+m sB sA)))
                             ■ wdc ■ cong suc (Nat.+-comm sA sB)
                        jv : Fin.toℕ (s𝔽 junc1) ≡ sB + sAᴿ
                        jv = s𝔽toℕ junc1 ■ toℕ-weaken*ᵣ sB (subst 𝔽 castRRᴿ j0ᴿ)
                           ■ cong (sB +_) (tf𝔽 castRRᴿ j0ᴿ ■ proj₂ (proj₂ (proj₂ (proj₂ hcᴿ1)))
                                          ■ cong (_+ 0) (cong syncs passocᴿ) ■ Nat.+-identityʳ sAᴿ)
                        jle : sB Nat.≤ Fin.toℕ (s𝔽 junc1)
                        jle = subst (sB Nat.≤_) (sym jv) (Nat.m≤m+n sB sAᴿ)
                        wpos = subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 junc1) jle)
                        wpostoℕ : Fin.toℕ wpos ≡ sAᴿ
                        wpostoℕ = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 junc1) jle)
                                ■ toℕ-reduce≥ (s𝔽 junc1) jle ■ cong (Nat._∸ sB) jv ■ Nat.m+n∸m≡n sB sAᴿ
                        sDq1≤ : sDq + 1 Nat.≤ sAᴿ
                        sDq1≤ = subst (Nat._≤ sAᴿ) (Nat.+-comm 1 sDq)
                                  (subst (suc sDq Nat.≤_) (sym (syncs-rwkq B₁ q)) (Nat.s≤s sDq≤sA))
                        rhsJ : Fin.toℕ ((swc ↑* sB) (s𝔽 junc1)) ≡ suc (sB + sA)
                        rhsJ = swcUp-ge (s𝔽 junc1) jle
                             ■ cong (sB +_) (toℕ-assoc-ge sDq 1 wpos (subst (sDq + 1 Nat.≤_) (sym wpostoℕ) sDq1≤) ■ wpostoℕ ■ syncs-rwkq B₁ q)
                             ■ Nat.+-suc sB sA
                    dropEq1 : (` assocSwapᵣ 1 sB 0F) ≡ (sTm L1 ⋯ (swc ↑* sB))
                    dropEq1 = cong `_ (Fin.toℕ-injective (lhsD ■ sym rhsD1)) ■ sym L1asvar
                      where
                        wv : Fin.toℕ (s𝔽 dv) ≡ sB + sDq
                        wv = s𝔽toℕ dv ■ toℕ-weaken*ᵣ sB (subst 𝔽 castRRᴿ v1) ■ cong (sB +_) (tf𝔽 castRRᴿ v1 ■ tn1 ■ HIq)
                        wle : sB Nat.≤ Fin.toℕ (s𝔽 dv)
                        wle = subst (sB Nat.≤_) (sym wv) (Nat.m≤m+n sB sDq)
                        wpos = subst 𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 dv) wle)
                        wpostoℕ : Fin.toℕ wpos ≡ sDq
                        wpostoℕ = tf𝔽 (sym (sym (sw-domq B₁ {q} {b₁} {B₂} {2 + n}))) (Fin.reduce≥ (s𝔽 dv) wle)
                                ■ toℕ-reduce≥ (s𝔽 dv) wle ■ cong (Nat._∸ sB) wv ■ Nat.m+n∸m≡n sB sDq
                        lhsD : Fin.toℕ (assocSwapᵣ 1 sB 0F) ≡ sB
                        lhsD = toℕ-assoc-lt 1 sB 0F (Nat.s≤s Nat.z≤n) ■ Nat.+-identityʳ sB
                        rhsD1 : Fin.toℕ ((swc ↑* sB) (s𝔽 dv)) ≡ sB
                        rhsD1 = swcUp-ge (s𝔽 dv) wle
                              ■ cong (sB +_) (toℕ-assoc-mid sDq 1 wpos
                                                (subst (sDq Nat.≤_) (sym wpostoℕ) Nat.≤-refl)
                                                (subst (Nat._< sDq + 1) (sym wpostoℕ) (subst (sDq Nat.<_) (Nat.+-comm 1 sDq) (Nat.n<1+n sDq)))
                                            ■ cong (Nat._∸ sDq) wpostoℕ ■ Nat.n∸n≡0 sDq)
                              ■ Nat.+-identityʳ sB
        PEq : (resid U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 sB)
              ≡ (subst U.Proc (cong (sB +_) E') residR U.⋯ₚ (swc ↑* sB))
        PEq = U.fusionₚ resid weakenᵣ (assocSwapᵣ 1 sB)
            ■ U.⋯ₚ-cong resid ρL≗ρR
            ■ sym (U.fusionₚ resid (subst (λ z → (sB + (sA + (2 + n))) →ᵣ z) (cong (sB +_) E') sinsρ) (swc ↑* sB))
            ■ cong (U._⋯ₚ (swc ↑* sB)) (sym (substcod (cong (sB +_) E') resid sinsρ))
            ■ cong (λ z → subst U.Proc (cong (sB +_) E') z U.⋯ₚ (swc ↑* sB)) (sym Prwkeq)
        innerLeafEq : (bodyD U.⋯ₚ assocSwapᵣ 1 sB)
                      ≡ (subst U.Proc (cong (sB +_) E') leafR) U.⋯ₚ (swc ↑* sB)
        innerLeafEq = cong₂ U._∥_ threadEq PEq ■ sym rhsD
        bodyEq : Bφ B (mapᶜ (weaken ⦃ Kᵣ ⦄) cc₂) (bodyD U.⋯ₚ assocSwapᵣ 1 sB) ≡ ZBR
        bodyEq = cong₂ (Bφ B) ccEq innerLeafEq ■ sym rhsT
        finalMatch : U.φ U.drop (` cz0) (Bφ B (mapᶜ (weaken ⦃ Kᵣ ⦄) cc₂) (bodyD U.⋯ₚ assocSwapᵣ 1 sB))
                     ≡ U.φ U.drop dcBR ZBR
        finalMatch = cong₂ (U.φ U.drop) channelEq bodyEq
        innerReconcile : Bφ B cc₂ (U.φ U.drop (` dc) bodyD) U.≋ dropForm
        innerReconcile =
             Bφ-cong-c B cc₂ (≡→≋ (cong (λ c → U.φ U.drop c bodyD) chanFac))
          ◅◅ Bφ-φ-comm B U.drop (` cz0) cc₂ bodyD
          ◅◅ ≡→≋ finalMatch
