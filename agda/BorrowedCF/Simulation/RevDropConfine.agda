module BorrowedCF.Simulation.RevDropConfine where

-- Wide-block confinement for the (now IMPURE) drop redex.  `drop` is 𝕀
-- (⊢ `drop ∶ ⟨ ret ⟩ →*M `⊤ ∣ 𝕀), so the impurity front-forcing squeeze of
-- RevComConfine applies to drop redexes: the frame stack above the redex is
-- all-LeftPat, hence nothing in the thread's struct sits ;-before the handle
-- (com-xS-min).  But a handle that is the LAST index of a binder block of
-- width ≥ 2 has the block front ;-before it in the ν binder (structNSeq is a
-- ;-chain), at ANY position of the group list.  Contradiction: a well-typed
-- ν process whose left thread holds an active drop redex on such a handle is
-- impossible.
--
--   blkIx / toℕ-blkIx / before-blkIx : embed an in-block index at a general
--     list position into structBinder (D ++ b ∷ B′), transporting `before`.
--   count-handle-wideᴸ/ᴿ : ReverseConfine.count-handle-comᴸ / RevGrindC.
--     count-handle-comᴿ with the singleton groups generalized to arbitrary
--     bind groups.
--   before-drop-binderᴸ/ᴿ : before-com-binderᴸ/ᴿ at a general block position.
--   drop-wide₁-⊥ / drop-wide₂-⊥ : the assembled impossibilities (drop block
--     in group 1 with singleton group 2 / in group 2 with arbitrary group 1).

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as T
open import BorrowedCF.Simulation.RevGrindA
  using (chanCx-¬Unr; choice-¬before; barevar-arg-count; 𝕀≤⇒≡𝕀)
open import BorrowedCF.Simulation.RevGrindC using (inj-wkˡ)
open import BorrowedCF.Simulation.RevComConfine
  using (frames-𝕀; com-xS-min; inj-wkʳ)
open import BorrowedCF.Simulation.BeforeOrder
  using (before; before-structNSeq; before-⋯ᵣ-inj)
open import BorrowedCF.Simulation.Confine using (count)
open import BorrowedCF.Simulation.StructDom
  using (count-structBinder-lt; count-weaken*-lo; count-weaken*-shift;
         count-⋯ᵣwkʳ-↑ˡ; count-⋯ᵣwkʳ-↑ʳ; ⋯ᵣwkˡ≡⋯weaken*)
open import BorrowedCF.Context using (Ctx; Struct)
import BorrowedCF.Context.Substitution as 𝐂S
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ-fromℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_; []; _++_)
open T using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx;
              structBinder; structNSeq)

open Nat using (_<_; _≤_; m≤m+n; <-≤-trans; +-monoʳ-<)

------------------------------------------------------------------------
-- General-position block embedding.
------------------------------------------------------------------------

blkIx : ∀ (D : BindGroup) {b} (B′ : BindGroup) → 𝔽 b → 𝔽 (sum (D ++ b ∷ B′))
blkIx []      {b} B′ u = u ↑ˡ sum B′
blkIx (d ∷ D) {b} B′ u = d ↑ʳ blkIx D B′ u

toℕ-blkIx : ∀ (D : BindGroup) {b} (B′ : BindGroup) (u : 𝔽 b) →
            Fin.toℕ (blkIx D B′ u) ≡ sum D + Fin.toℕ u
toℕ-blkIx []      {b} B′ u = toℕ-↑ˡ u (sum B′)
toℕ-blkIx (d ∷ D) {b} B′ u =
  toℕ-↑ʳ d (blkIx D B′ u) ■ cong (d +_) (toℕ-blkIx D B′ u)
  ■ sym (Nat.+-assoc d (sum D) (Fin.toℕ u))

before-blkIx : ∀ (D : BindGroup) {b} (B′ : BindGroup) {u v : 𝔽 b} →
               before u v (structNSeq b) →
               before (blkIx D B′ u) (blkIx D B′ v) (structBinder (D ++ b ∷ B′))
before-blkIx []      {b} B′ buv =
  inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ (sum B′)) (inj-wkʳ (sum B′)) (structNSeq b) buv)
before-blkIx (d ∷ D) {b} B′ buv =
  inj₂ (before-⋯ᵣ-inj (𝐂S.wkˡ d) (inj-wkˡ d) (structBinder (D ++ b ∷ B′))
         (before-blkIx D B′ buv))

------------------------------------------------------------------------
-- ;-order facts at a general block position (mirrors of before-com-binderᴸ/ᴿ):
-- the front of a width-(2+w″) block sits ;-before the block's last index in
-- the TP-Res binder context.
------------------------------------------------------------------------

before-drop-binderᴸ : ∀ (D₁ : BindGroup) (w″ b′ b₂ : ℕ) {m : ℕ} (γ : Struct m) →
  let C₁ = D₁ ++ suc (suc w″) ∷ b′ ∷ [] in
  before ((blkIx D₁ (b′ ∷ []) (Fin.zero {suc w″}) ↑ˡ (b₂ + 0)) ↑ˡ m)
         ((blkIx D₁ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″)) ↑ˡ (b₂ + 0)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (b₂ ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (structBinder (b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum (b₂ ∷ []))) )
before-drop-binderᴸ D₁ w″ b′ b₂ {m} γ =
  inj₁ (inj₁ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
         (structBinder (D₁ ++ suc (suc w″) ∷ b′ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkʳ (b₂ + 0))
         (before-⋯ᵣ-inj (𝐂S.wkʳ (b₂ + 0)) (inj-wkʳ (b₂ + 0))
           (structBinder (D₁ ++ suc (suc w″) ∷ b′ ∷ []))
           (before-blkIx D₁ (b′ ∷ [])
             (before-structNSeq (suc w″) (Fin.fromℕ w″))))))

before-drop-binderᴿ : ∀ (B₁ D₂ : BindGroup) (w″ b′ : ℕ) {m : ℕ} (γ : Struct m) →
  let C₂ = D₂ ++ suc (suc w″) ∷ b′ ∷ [] in
  before ((sum B₁ ↑ʳ blkIx D₂ (b′ ∷ []) (Fin.zero {suc w″})) ↑ˡ m)
         ((sum B₁ ↑ʳ blkIx D₂ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″))) ↑ˡ m)
    ( (structBinder B₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum B₁ + sum C₂)) )
before-drop-binderᴿ B₁ D₂ w″ b′ {m} γ =
  inj₁ (inj₂ (before-⋯ᵣ-inj (𝐂S.wkʳ m) (inj-wkʳ m)
         (structBinder (D₂ ++ suc (suc w″) ∷ b′ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁))
         (before-⋯ᵣ-inj (𝐂S.wkˡ (sum B₁)) (inj-wkˡ (sum B₁))
           (structBinder (D₂ ++ suc (suc w″) ∷ b′ ∷ []))
           (before-blkIx D₂ (b′ ∷ [])
             (before-structNSeq (suc w″) (Fin.fromℕ w″))))))

------------------------------------------------------------------------
-- Cross-thread linearity at a general block position: any group-1 (resp.
-- group-2) handle counts exactly once in the TP-Res binder context.
------------------------------------------------------------------------

count-handle-wideᴸ : ∀ (C₁ : BindGroup) (b₂ : ℕ) {m : ℕ} (γ : Struct m) (z : 𝔽 (sum C₁)) →
  count ((z ↑ˡ (b₂ + 0)) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (b₂ ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (structBinder (b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum (b₂ ∷ []))) ) ≡ 1
count-handle-wideᴸ C₁ b₂ {m} γ z = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    C₂ : BindGroup
    C₂ = b₂ ∷ []
    z<C₁ : Fin.toℕ z < sum C₁
    z<C₁ = Fin.toℕ<n z
    partA : count ((z ↑ˡ sum C₂) ↑ˡ m) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) (z ↑ˡ sum C₂)
          ■ count-⋯ᵣwkʳ-↑ˡ (sum C₂) (structBinder C₁) z
          ■ count-structBinder-lt C₁ z z<C₁
    partB : count ((z ↑ˡ sum C₂) ↑ˡ m) (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) (z ↑ˡ sum C₂)
          ■ cong (count (z ↑ˡ sum C₂)) (⋯ᵣwkˡ≡⋯weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-lo (sum C₁) (structBinder C₂) (z ↑ˡ sum C₂) z↑<C₁
      where
        z↑<C₁ : Fin.toℕ (z ↑ˡ sum C₂) < sum C₁
        z↑<C₁ = subst (_< sum C₁) (sym (toℕ-↑ˡ z (sum C₂))) z<C₁
    partC : count ((z ↑ˡ sum C₂) ↑ˡ m) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ ((z ↑ˡ sum C₂) ↑ˡ m) hdl<
      where
        hdl< : Fin.toℕ ((z ↑ˡ sum C₂) ↑ˡ m) < sum C₁ + sum C₂
        hdl< = subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ (z ↑ˡ sum C₂) m))
                 (subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ z (sum C₂)))
                   (<-≤-trans z<C₁ (m≤m+n (sum C₁) (sum C₂))))

count-handle-wideᴿ : ∀ (C₁ C₂ : BindGroup) {m : ℕ} (γ : Struct m) (w : 𝔽 (sum C₂)) →
  count ((sum C₁ ↑ʳ w) ↑ˡ m)
    ( (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
    Struct.∥ (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ) ≡ 1
count-handle-wideᴿ C₁ C₂ {m} γ w = cong₂ _+_ (cong₂ _+_ partA partB) partC
  where
    hdl : 𝔽 (sum C₁ + sum C₂)
    hdl = sum C₁ ↑ʳ w
    w<C₂ : Fin.toℕ w < sum C₂
    w<C₂ = Fin.toℕ<n w
    partA : count (hdl ↑ˡ m) (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 0
    partA = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂)) hdl
          ■ count-⋯ᵣwkʳ-↑ʳ (sum C₂) (structBinder C₁) w
    partB : count (hdl ↑ˡ m) (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m) ≡ 1
    partB = count-⋯ᵣwkʳ-↑ˡ m (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁)) hdl
          ■ cong (count hdl) (⋯ᵣwkˡ≡⋯weaken* (sum C₁) (structBinder C₂))
          ■ count-weaken*-shift (sum C₁) (structBinder C₂) w
          ■ count-structBinder-lt C₂ w w<C₂
    partC : count (hdl ↑ˡ m) (γ 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum C₂)) ≡ 0
    partC = count-weaken*-lo (sum C₁ + sum C₂) γ (hdl ↑ˡ m) hdl<
      where
        hdl< : Fin.toℕ (hdl ↑ˡ m) < sum C₁ + sum C₂
        hdl< = subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ˡ hdl m))
                 (subst (_< sum C₁ + sum C₂) (sym (toℕ-↑ʳ (sum C₁) w))
                   (+-monoʳ-< (sum C₁) w<C₂))

------------------------------------------------------------------------
-- drop is impure (mirror of end-app-𝕀 / select-app-𝕀).
------------------------------------------------------------------------

drop-fn-eff-𝕀 : ∀ {N} {Γ : Ctx N} {α : Struct N} {Td Uu a ϵ}
  → Γ ; α ⊢ K `drop ∶ Td ⟨ a ⟩→ Uu ∣ ϵ → Arr.eff a ≡ 𝕀
drop-fn-eff-𝕀 (T-Const `drop) = refl
drop-fn-eff-𝕀 (T-Conv (_ `→ _) _ d) = drop-fn-eff-𝕀 d
drop-fn-eff-𝕀 (T-Weaken _ d) = drop-fn-eff-𝕀 d

drop-app-𝕀 : ∀ {N} {Γ : Ctx N} {γ : Struct N} {arg : Tm N} {Uu ϵ}
  → Γ ; γ ⊢ K `drop ·¹ arg ∶ Uu ∣ ϵ → ϵ ≡ 𝕀
drop-app-𝕀 (T-AppUnr _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-fn-eff-𝕀 ⊢fn) ≤ₐ)
drop-app-𝕀 (T-AppLin _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-fn-eff-𝕀 ⊢fn) ≤ₐ)
drop-app-𝕀 (T-Conv _ ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (drop-app-𝕀 d) ≤)
drop-app-𝕀 (T-Weaken _ d) = drop-app-𝕀 d

------------------------------------------------------------------------
-- The assembled impossibilities: an active drop redex on the LAST index of
-- a block of width ≥ 2 cannot be well typed under the ν binder.
------------------------------------------------------------------------

drop-wide₁-⊥ : ∀ {m : ℕ} (D₁ : T.BindGroup) (w″ b′ b₂ : ℕ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
               {P₀r : T.Proc (sum (D₁ ++ suc (suc w″) ∷ b′ ∷ []) + sum (b₂ ∷ []) + m)}
               (F₀ : Frame* (sum (D₁ ++ suc (suc w″) ∷ b′ ∷ []) + sum (b₂ ∷ []) + m))
               (z : 𝔽 (sum (D₁ ++ suc (suc w″) ∷ b′ ∷ []) + sum (b₂ ∷ []) + m)) →
               Fin.toℕ z ≡ sum D₁ + suc w″ →
               Γ ; g ⊢ₚ T.ν (D₁ ++ suc (suc w″) ∷ b′ ∷ []) (b₂ ∷ [])
                 (T.⟪ F₀ [ K `drop ·¹ (` z) ]* ⟫ T.∥ P₀r) →
               ⊥
drop-wide₁-⊥ {m = m} D₁ w″ b′ b₂ {Γ = Γ} Γ-S {g = g} F₀ z toℕz ⊢P
  with Γ₁ , Γ₂ , s′ , p′ , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with αD , βrest , ≼₁ , ⊢PD , ⊢Pr ← inv-∥ ⊢body
  with 𝒫 , γr , _ , _ , _ , _ , ≼ᵈ , _ , _ , ⊢F , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `drop ·¹ (` z)) (inv-⟪⟫ ⊢PD)
  with refl ← drop-app-𝕀 ⊢redex
  with refl , lp ← frames-𝕀 ⊢F
  = com-xS-min ¬uz ¬uy lp ≼ᵈ ≼₁ cnt1 bfr 1≤c ¬brs
  where
    C₁ : T.BindGroup
    C₁ = D₁ ++ suc (suc w″) ∷ b′ ∷ []
    Sb : Struct (sum C₁ + sum (b₂ ∷ []) + m)
    Sb = (structBinder C₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum (b₂ ∷ [])) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (structBinder (b₂ ∷ []) 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum C₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum C₁ + sum (b₂ ∷ [])))
    zc : 𝔽 (sum C₁)
    zc = blkIx D₁ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″))
    yc : 𝔽 (sum C₁)
    yc = blkIx D₁ (b′ ∷ []) (Fin.zero {suc w″})
    Y : 𝔽 (sum C₁ + sum (b₂ ∷ []) + m)
    Y = (yc ↑ˡ (b₂ + 0)) ↑ˡ m
    z≡Z : z ≡ (zc ↑ˡ (b₂ + 0)) ↑ˡ m
    z≡Z = toℕ-injective
      ( toℕz
      ■ sym ( toℕ-↑ˡ (zc ↑ˡ (b₂ + 0)) m
            ■ toℕ-↑ˡ zc (b₂ + 0)
            ■ toℕ-blkIx D₁ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″))
            ■ cong (λ t → sum D₁ + suc t) (toℕ-fromℕ w″) ) )
    ¬uz = chanCx-¬Unr Γ′-S z
    ¬uy = chanCx-¬Unr Γ′-S Y
    1≤c = barevar-arg-count ¬uz ⊢redex
    ¬brs = choice-¬before ¬uz ¬uy ⊢redex
    cnt1 : count z Sb ≡ 1
    cnt1 = subst (λ v → count v Sb ≡ 1) (sym z≡Z) (count-handle-wideᴸ C₁ b₂ g zc)
    bfr : before Y z Sb
    bfr = subst (λ v → before Y v Sb) (sym z≡Z) (before-drop-binderᴸ D₁ w″ b′ b₂ g)

drop-wide₂-⊥ : ∀ {m : ℕ} (B₁ D₂ : T.BindGroup) (w″ b′ : ℕ) {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
               {P₀r : T.Proc (sum B₁ + sum (D₂ ++ suc (suc w″) ∷ b′ ∷ []) + m)}
               (F₀ : Frame* (sum B₁ + sum (D₂ ++ suc (suc w″) ∷ b′ ∷ []) + m))
               (z : 𝔽 (sum B₁ + sum (D₂ ++ suc (suc w″) ∷ b′ ∷ []) + m)) →
               Fin.toℕ z ≡ sum B₁ + (sum D₂ + suc w″) →
               Γ ; g ⊢ₚ T.ν B₁ (D₂ ++ suc (suc w″) ∷ b′ ∷ [])
                 (T.⟪ F₀ [ K `drop ·¹ (` z) ]* ⟫ T.∥ P₀r) →
               ⊥
drop-wide₂-⊥ {m = m} B₁ D₂ w″ b′ {Γ = Γ} Γ-S {g = g} F₀ z toℕz ⊢P
  with Γ₁ , Γ₂ , s′ , p′ , Nnew , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
  with Γ′-S ← chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S
  with αD , βrest , ≼₁ , ⊢PD , ⊢Pr ← inv-∥ ⊢body
  with 𝒫 , γr , _ , _ , _ , _ , ≼ᵈ , _ , _ , ⊢F , ⊢redex
       ← ⊢[]*⁻¹ F₀ (K `drop ·¹ (` z)) (inv-⟪⟫ ⊢PD)
  with refl ← drop-app-𝕀 ⊢redex
  with refl , lp ← frames-𝕀 ⊢F
  = com-xS-min ¬uz ¬uy lp ≼ᵈ ≼₁ cnt1 bfr 1≤c ¬brs
  where
    C₂ : T.BindGroup
    C₂ = D₂ ++ suc (suc w″) ∷ b′ ∷ []
    Sb : Struct (sum B₁ + sum C₂ + m)
    Sb = (structBinder B₁ 𝐂S.⋯ᵣ 𝐂S.wkʳ (sum C₂) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (structBinder C₂ 𝐂S.⋯ᵣ 𝐂S.wkˡ (sum B₁) 𝐂S.⋯ᵣ 𝐂S.wkʳ m)
         Struct.∥ (g 𝐂S.⋯ 𝐂S.weaken* ⦃ 𝐂S.Kᵣ ⦄ (sum B₁ + sum C₂))
    zc : 𝔽 (sum C₂)
    zc = blkIx D₂ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″))
    yc : 𝔽 (sum C₂)
    yc = blkIx D₂ (b′ ∷ []) (Fin.zero {suc w″})
    Y : 𝔽 (sum B₁ + sum C₂ + m)
    Y = (sum B₁ ↑ʳ yc) ↑ˡ m
    z≡Z : z ≡ (sum B₁ ↑ʳ zc) ↑ˡ m
    z≡Z = toℕ-injective
      ( toℕz
      ■ sym ( toℕ-↑ˡ (sum B₁ ↑ʳ zc) m
            ■ toℕ-↑ʳ (sum B₁) zc
            ■ cong (sum B₁ +_)
                ( toℕ-blkIx D₂ (b′ ∷ []) (Fin.suc (Fin.fromℕ w″))
                ■ cong (λ t → sum D₂ + suc t) (toℕ-fromℕ w″) ) ) )
    ¬uz = chanCx-¬Unr Γ′-S z
    ¬uy = chanCx-¬Unr Γ′-S Y
    1≤c = barevar-arg-count ¬uz ⊢redex
    ¬brs = choice-¬before ¬uz ¬uy ⊢redex
    cnt1 : count z Sb ≡ 1
    cnt1 = subst (λ v → count v Sb ≡ 1) (sym z≡Z) (count-handle-wideᴿ B₁ C₂ g zc)
    bfr : before Y z Sb
    bfr = subst (λ v → before Y v Sb) (sym z≡Z) (before-drop-binderᴿ B₁ D₂ w″ b′ g)
