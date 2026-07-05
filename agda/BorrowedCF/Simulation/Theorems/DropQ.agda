module BorrowedCF.Simulation.Theorems.DropQ where

-- | Forward-simulation case for the q-generalized R-Drop (interior block-list
--   position ∣B₁∣ of group 1).  Exports U-dropQ.
--
--   suffix []  : the drop block is the group's LAST — its front-handle session
--                is NoRet, so the ⟨ ret ⟩ redex is untypeable (dropVac-last).
--   width ≥ 2  : the front handle would be ⟨ ret ⟩ with live pieces after it —
--                RetTip/¬skips refutes (dropVac-mid).
--   width 1    : fire.  Uν-flat; slide the cell to the leaf (Bw-slide 1 +
--                φ-past-Bφ); RU-Drop; slide back with flag acq (Bw-slide 0);
--                reconcile the leaf through leaf-dwk.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import BorrowedCF.Context using (Ctx; Struct; _⸴*_; _⸴_)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Base using (NonZero)
open T using (BindGroup; _;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν)
open import BorrowedCF.Simulation.Theorems.DropQH
open import BorrowedCF.Simulation.Theorems.Drop
  using (drop-handle-≃ret; ⟨⟩≃; noRet⇒≄ret)
open import BorrowedCF.Simulation.Theorems.B1VacProbe as VP using (NoRet; new⇒noRet)
open import BorrowedCF.Simulation.InvFrame using (strengthen-frame)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.TranslationProperties using (U-cong; U-⋯ₚ; VChan)

private
  subst-∥U : ∀ {a b} (eq : a ≡ b) (X Y : U.Proc a) →
             subst U.Proc eq (X U.∥ Y) ≡ subst U.Proc eq X U.∥ subst U.Proc eq Y
  subst-∥U refl X Y = refl

  subst-⟪⟫U : ∀ {a b} (eq : a ≡ b) (t : Tm a) →
              subst U.Proc eq U.⟪ t ⟫ ≡ U.⟪ subst Tm eq t ⟫
  subst-⟪⟫U refl t = refl

  subst-⋯ₛ-cod : ∀ {D a c} (q : a ≡ c) (t : Tm D) (s : D →ₛ a) →
                 t ⋯ subst (λ z → D →ₛ z) q s ≡ subst Tm q (t ⋯ s)
  subst-⋯ₛ-cod refl t s = refl

  subst-cod-pt : ∀ {D a c} (eq : a ≡ c) (s : D →ₛ a) (i : 𝔽 D) →
                 subst (λ z → D →ₛ z) eq s i ≡ subst Tm eq (s i)
  subst-cod-pt refl s i = refl

  Vsubst : ∀ {a c} {t : Tm a} (eq : a ≡ c) → Value t → Value (subst Tm eq t)
  Vsubst refl V = V

  U-substσ : ∀ {mm a b} (e : a ≡ b) (τ : mm →ₛ a) (P : T.Proc mm) →
             U[ P ] (λ i → subst Tm e (τ i)) ≡ subst U.Proc e (U[ P ] τ)
  U-substσ refl τ P = refl

  VSub-leafσS : ∀ {mm nn} (σ : mm →ₛ nn) → VSub σ → (Bx Bg : BindGroup) →
                VSub (leafσ σ Bx Bg)
  VSub-leafσS σ Vσ Bx Bg i with Fin.splitAt (sum Bx + sum Bg) i
  ... | inj₂ u = value-⋯ (value-⋯ (value-⋯ (Vσ u)
                   (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ (syncs Bx)) (λ _ → V-`))
                   (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`)
  ... | inj₁ d with Fin.splitAt (sum Bx) d
  ...   | inj₁ g1 = value-⋯ (VSub-canonₛ Bx (K `unit , 0F , K `unit) (V-K , V-K) g1)
                      (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`)
  ...   | inj₂ g2 = VSub-canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs Bx) 1F , K `unit) (V-K , V-K) g2

U-dropQ : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
        → {g : Struct m} (B₁ : BindGroup) (b₁ : ℕ) (B₂ Bg : BindGroup)
          {E : Frame* (sum (B₁ ++ b₁ ∷ B₂) + sum Bg + m)}
          {P : T.Proc (sum (B₁ ++ b₁ ∷ B₂) + sum Bg + m)}
        → Γ ; g ⊢ₚ T.ν (B₁ ++ suc b₁ ∷ B₂) Bg
            (T.⟪ (E ⋯ᶠ* TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m}) [ K `drop ·¹ (` TR.SplitRenamings.atk B₁ B₂ Bg {suc b₁} {m} 0F) ]* ⟫
              T.∥ (P T.⋯ₚ TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m}))
        → (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) Bg
              (T.⟪ (E ⋯ᶠ* TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m}) [ K `drop ·¹ (` TR.SplitRenamings.atk B₁ B₂ Bg {suc b₁} {m} 0F) ]* ⟫
                T.∥ (P T.⋯ₚ TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m})) ] σ
             UR─→ₚ* U[ T.ν (B₁ ++ b₁ ∷ B₂) Bg (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
          ⊎ (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) Bg
              (T.⟪ (E ⋯ᶠ* TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m}) [ K `drop ·¹ (` TR.SplitRenamings.atk B₁ B₂ Bg {suc b₁} {m} 0F) ]* ⟫
                T.∥ (P T.⋯ₚ TR.SplitRenamings.dwk B₁ B₂ Bg {b₁} {m})) ] σ
             U.≋ U[ T.ν (B₁ ++ b₁ ∷ B₂) Bg (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
U-dropQ {m} {n} σ Vσ Γ-S B₁ b₁ [] Bg {E} {P} ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , sN , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* TR.SplitRenamings.dwk B₁ [] Bg {b₁} {m}) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with dropVac-last B₁ {b₁} (VP._;_ (new⇒noRet N) VP.end) C
... | s'' , eq'' , nr''
  = ⊥-elim (noRet⇒≄ret nr''
      (⟨⟩≃ (≃-trans (≃-reflexive (sym (bodyNav ■ eq''))) (drop-handle-≃ret ⊢plug))))
  where
    g1c : 𝔽 (sum (B₁ ++ suc b₁ ∷ []))
    g1c = Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ []))) (sum B₁ ↑ʳ 0F)
    bodyNav : ((Γ₁ ⸴* Γ₂) ⸴* _) (TR.SplitRenamings.atk B₁ [] Bg {suc b₁} {m} 0F) ≡ Γ₁ g1c
    bodyNav =
        cong [ Γ₁ ⸴* Γ₂ , _ ]′ (Fin.splitAt-↑ˡ (sum (B₁ ++ suc b₁ ∷ []) + sum Bg) (g1c ↑ˡ sum Bg) m)
      ■ cong [ Γ₁ , Γ₂ ]′ (Fin.splitAt-↑ˡ (sum (B₁ ++ suc b₁ ∷ [])) g1c (sum Bg))
U-dropQ {m} {n} σ Vσ Γ-S B₁ (suc b₁') (c ∷ B₂') Bg {E} {P} ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , sN , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* TR.SplitRenamings.dwk B₁ (c ∷ B₂') Bg {suc b₁'} {m}) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  = ⊥-elim (dropVac-mid B₁ {b₁'} {c} {B₂'} (VP._;_ (new⇒noRet N) VP.end) C
      (≃-trans (≃-reflexive (sym bodyNav)) (drop-handle-≃ret ⊢plug)))
  where
    g1c : 𝔽 (sum (B₁ ++ suc (suc b₁') ∷ c ∷ B₂'))
    g1c = Fin.cast (sym (sum-++ B₁ (suc (suc b₁') ∷ c ∷ B₂'))) (sum B₁ ↑ʳ 0F)
    bodyNav : ((Γ₁ ⸴* Γ₂) ⸴* _) (TR.SplitRenamings.atk B₁ (c ∷ B₂') Bg {suc (suc b₁')} {m} 0F) ≡ Γ₁ g1c
    bodyNav =
        cong [ Γ₁ ⸴* Γ₂ , _ ]′ (Fin.splitAt-↑ˡ (sum (B₁ ++ suc (suc b₁') ∷ c ∷ B₂') + sum Bg) (g1c ↑ˡ sum Bg) m)
      ■ cong [ Γ₁ , Γ₂ ]′ (Fin.splitAt-↑ˡ (sum (B₁ ++ suc (suc b₁') ∷ c ∷ B₂')) g1c (sum Bg))
U-dropQ {m} {n} σ Vσ Γ-S B₁ zero (c ∷ B₂') Bg {E} {P} ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , sN , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with nonZero⇒sucℕ (allNZ-drop1 B₁ ⊢B₁)
... | c' , refl = ≋-wrap-⊎ front fire back
  where
    module LD = LeafDwk {m} {n} σ B₁ c' B₂' Bg
    sBg = syncs Bg
    dwk′ = TR.SplitRenamings.dwk B₁ (suc c' ∷ B₂') Bg {0} {m}
    atk0 = TR.SplitRenamings.atk B₁ (suc c' ∷ B₂') Bg {1} {m} 0F
    swc = sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}
    EQ1P = cong (syncs Bg +_) LD.EQ1
    EQ0P = cong (syncs Bg +_) LD.EQ0
    QL : T.Proc (sum LD.L1 + sum Bg + m)
    QL = T.⟪ (E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]* ⟫ T.∥ (P T.⋯ₚ dwk′)
    QR : T.Proc (sum LD.L0 + sum Bg + m)
    QR = T.⟪ E [ K `unit ]* ⟫ T.∥ P
    leafL : U.Proc (sBg + (syncs LD.L1 + (2 + n)))
    leafL = U[ QL ] (leafσ σ LD.L1 Bg)
    leafR : U.Proc (sBg + (syncs LD.L0 + (2 + n)))
    leafR = U[ QR ] (leafσ σ LD.L0 Bg)
    leafL₁ = subst U.Proc EQ1P leafL U.⋯ₚ LD.ρ₁
    leafL₂ = leafL₁ U.⋯ₚ LD.ρ₂
    leafR₁ = subst U.Proc EQ0P leafR U.⋯ₚ LD.ρ₁
    leafR₂ = leafR₁ U.⋯ₚ LD.ρ₂

    aL : Tm (sBg + (syncs LD.L1 + (2 + n)))
    aL = ((E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]*) ⋯ leafσ σ LD.L1 Bg
    bL : U.Proc (sBg + (syncs LD.L1 + (2 + n)))
    bL = U[ P T.⋯ₚ dwk′ ] (leafσ σ LD.L1 Bg)
    aR : Tm (sBg + (syncs LD.L0 + (2 + n)))
    aR = (E [ K `unit ]*) ⋯ leafσ σ LD.L0 Bg
    bR : U.Proc (sBg + (syncs LD.L0 + (2 + n)))
    bR = U[ P ] (leafσ σ LD.L0 Bg)

    bodySubst1 : subst U.Proc LD.EQ1 (Bφ Bg leafL) U.⋯ₚ swc ≡ Bφ Bg leafL₁
    bodySubst1 =
        cong (U._⋯ₚ swc) (subst-Bφ LD.EQ1 Bg leafL)
      ■ Bφ-⋯ Bg (subst U.Proc EQ1P leafL) swc
    bodySubst0 : subst U.Proc LD.EQ0 (Bφ Bg leafR) U.⋯ₚ swc ≡ Bφ Bg leafR₁
    bodySubst0 =
        cong (U._⋯ₚ swc) (subst-Bφ LD.EQ0 Bg leafR)
      ■ Bφ-⋯ Bg (subst U.Proc EQ0P leafR) swc

    front : U[ T.ν LD.L1 Bg QL ] σ U.≋ U.ν (Bφ LD.LW (Bφ Bg (U.φ U.drop leafL₂)))
    front = ≡→≋ (Uν-flat σ LD.L1 Bg QL)
         ◅◅ U.ν-cong ( Bw-slide 1 B₁ {c'} {B₂'} {2 + n} (Bφ Bg leafL)
                     ◅◅ Bφ-cong LD.LW ( ≡→≋ (cong (U.φ U.drop) bodySubst1)
                                      ◅◅ φ-past-Bφ Bg U.drop leafL₁ ) )

    θ : (sum LD.L1 + sum Bg + m) →ₛ suc (sBg + (syncs LD.LW + (2 + n)))
    θ = ((subst (λ z → (sum LD.L1 + sum Bg + m) →ₛ z) EQ1P (leafσ σ LD.L1 Bg)) ·ₖ LD.ρ₁) ·ₖ LD.ρ₂
    θR : (sum LD.L0 + sum Bg + m) →ₛ suc (sBg + (syncs LD.LW + (2 + n)))
    θR = ((subst (λ z → (sum LD.L0 + sum Bg + m) →ₛ z) EQ0P (leafσ σ LD.L0 Bg)) ·ₖ LD.ρ₁) ·ₖ LD.ρ₂

    Vθ : VSub θ
    Vθ i = value-⋯ (value-⋯
             (subst Value (sym (subst-cod-pt EQ1P (leafσ σ LD.L1 Bg) i))
               (Vsubst EQ1P (VSub-leafσS σ Vσ LD.L1 Bg i)))
             LD.ρ₁ (λ _ → V-`))
             LD.ρ₂ (λ _ → V-`)

    redTm : Tm (suc (sBg + (syncs LD.LW + (2 + n))))
    redTm = subst Tm EQ1P aL ⋯ LD.ρ₁ ⋯ LD.ρ₂
    Qθ : U.Proc (suc (sBg + (syncs LD.LW + (2 + n))))
    Qθ = subst U.Proc EQ1P bL U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂

    split2 : leafL₂ ≡ U.⟪ redTm ⟫ U.∥ Qθ
    split2 =
      cong (λ z → z U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂)
        ( subst-∥U EQ1P U.⟪ aL ⟫ bL
        ■ cong (U._∥ subst U.Proc EQ1P bL) (subst-⟪⟫U EQ1P aL) )

    redTm≡θ : redTm ≡ ((E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]*) ⋯ θ
    redTm≡θ =
        cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂)
          (sym (subst-⋯ₛ-cod EQ1P ((E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]*) (leafσ σ LD.L1 Bg)))
      ■ cong (_⋯ LD.ρ₂)
          (fusion ((E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]*)
            (subst (λ z → (sum LD.L1 + sum Bg + m) →ₛ z) EQ1P (leafσ σ LD.L1 Bg)) LD.ρ₁)
      ■ fusion ((E ⋯ᶠ* dwk′) [ K `drop ·¹ (` atk0) ]*)
          ((subst (λ z → (sum LD.L1 + sum Bg + m) →ₛ z) EQ1P (leafσ σ LD.L1 Bg)) ·ₖ LD.ρ₁) LD.ρ₂

    Fθ : Frame* (suc (sBg + (syncs LD.LW + (2 + n))))
    Fθ = frame*-⋯ (E ⋯ᶠ* dwk′) θ Vθ

    θ-atk0 : θ atk0 ≡ subst Tm EQ1P (leafσ σ LD.L1 Bg atk0) ⋯ LD.ρ₁ ⋯ LD.ρ₂
    θ-atk0 = cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂) (subst-cod-pt EQ1P (leafσ σ LD.L1 Bg) atk0)

    hθ = LD.handleθ
    eH = proj₁ hθ
    x̂ = proj₁ (proj₂ hθ)

    redShape : redTm ≡ Fθ [ K `drop ·¹ ((eH ⊗ (` Fin.suc x̂)) ⊗ (` 0F)) ]*
    redShape =
        redTm≡θ
      ■ frame-plug* (E ⋯ᶠ* dwk′) θ Vθ
      ■ cong (Fθ [_]*) (cong (K `drop ·¹_) (θ-atk0 ■ proj₂ (proj₂ hθ)))

    lhsEq : leafL₂ ≡ U.⟪ Fθ [ K `drop ·¹ ((eH ⊗ (` Fin.suc x̂)) ⊗ (` 0F)) ]* ⟫ U.∥ Qθ
    lhsEq = split2 ■ cong (U._∥ Qθ) (cong U.⟪_⟫ redShape)

    dropStep : U.φ U.drop leafL₂ UR.─→ₚ U.φ U.acq (U.⟪ Fθ [ K `unit ]* ⟫ U.∥ Qθ)
    dropStep = subst (λ z → U.φ U.drop z UR.─→ₚ U.φ U.acq (U.⟪ Fθ [ K `unit ]* ⟫ U.∥ Qθ))
                 (sym lhsEq) (UR.RU-Drop Fθ {x = x̂})

    fired : U.Proc n
    fired = U.ν (Bφ LD.LW (Bφ Bg (U.φ U.acq (U.⟪ Fθ [ K `unit ]* ⟫ U.∥ Qθ))))

    fire : U.ν (Bφ LD.LW (Bφ Bg (U.φ U.drop leafL₂))) UR─→ₚ* fired
    fire = UR.RU-Res (Bφ-lift-step LD.LW (Bφ-lift-step Bg dropStep)) ◅ ε

    θ-agree : (x : 𝔽 (sum LD.L0 + sum Bg + m)) → θ (dwk′ x) ≡ θR x
    θ-agree x =
        cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂) (subst-cod-pt EQ1P (leafσ σ LD.L1 Bg) (dwk′ x))
      ■ cong (λ z → subst Tm EQ1P z ⋯ LD.ρ₁ ⋯ LD.ρ₂) (LD.leaf-dwk x)
      ■ cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂)
          ( ss-Tm LD.EQL EQ1P (leafσ σ LD.L0 Bg x)
          ■ cong (λ e → subst Tm e (leafσ σ LD.L0 Bg x)) (uipℕ (LD.EQL ■ EQ1P) EQ0P) )
      ■ sym (cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂) (subst-cod-pt EQ0P (leafσ σ LD.L0 Bg) x))

    Eunit : Tm (sum LD.L0 + sum Bg + m)
    Eunit = E [ K `unit ]*

    aR≡θR : subst Tm EQ0P aR ⋯ LD.ρ₁ ⋯ LD.ρ₂ ≡ Eunit ⋯ θR
    aR≡θR =
        cong (λ z → z ⋯ LD.ρ₁ ⋯ LD.ρ₂)
          (sym (subst-⋯ₛ-cod EQ0P Eunit (leafσ σ LD.L0 Bg)))
      ■ cong (_⋯ LD.ρ₂)
          (fusion Eunit (subst (λ z → (sum LD.L0 + sum Bg + m) →ₛ z) EQ0P (leafσ σ LD.L0 Bg)) LD.ρ₁)
      ■ fusion Eunit ((subst (λ z → (sum LD.L0 + sum Bg + m) →ₛ z) EQ0P (leafσ σ LD.L0 Bg)) ·ₖ LD.ρ₁) LD.ρ₂

    thread : Fθ [ K `unit ]* ≡ subst Tm EQ0P aR ⋯ LD.ρ₁ ⋯ LD.ρ₂
    thread =
        sym (frame-plug* (E ⋯ᶠ* dwk′) θ Vθ)
      ■ cong (_⋯ θ) (sym (frame-plug*ᵣ E dwk′))
      ■ fusion Eunit dwk′ θ
      ■ ⋯-cong Eunit θ-agree
      ■ sym aR≡θR
      
    resid : Qθ ≡ subst U.Proc EQ0P bR U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂
    resid = cong (λ z → z U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂)
        ( cong (subst U.Proc EQ1P)
            ( U-⋯ₚ P {ρ = dwk′} {σ = leafσ σ LD.L1 Bg}
            ■ U-cong P LD.leaf-dwk
            ■ U-substσ LD.EQL (leafσ σ LD.L0 Bg) P )
        ■ ss-U LD.EQL EQ1P {t = bR}
        ■ cong (λ e → subst U.Proc e bR) (uipℕ (LD.EQL ■ EQ1P) EQ0P) )

    split2R : leafR₂ ≡ U.⟪ subst Tm EQ0P aR ⋯ LD.ρ₁ ⋯ LD.ρ₂ ⟫ U.∥ (subst U.Proc EQ0P bR U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂)
    split2R =
      cong (λ z → z U.⋯ₚ LD.ρ₁ U.⋯ₚ LD.ρ₂)
        ( subst-∥U EQ0P U.⟪ aR ⟫ bR
        ■ cong (U._∥ subst U.Proc EQ0P bR) (subst-⟪⟫U EQ0P aR) )

    recon : U.⟪ Fθ [ K `unit ]* ⟫ U.∥ Qθ ≡ leafR₂
    recon = cong₂ U._∥_ (cong U.⟪_⟫ thread) resid ■ sym split2R

    back : fired U.≋ U[ T.ν LD.L0 Bg QR ] σ
    back = U.ν-cong (Bφ-cong LD.LW (Bφ-cong Bg (U.φ-cong (≡→≋ recon))))
        ◅◅ Eq*.symmetric _
             (U.ν-cong ( Bw-slide 0 B₁ {c'} {B₂'} {2 + n} (Bφ Bg leafR)
                       ◅◅ Bφ-cong LD.LW ( ≡→≋ (cong (U.φ U.acq) bodySubst0)
                                        ◅◅ φ-past-Bφ Bg U.acq leafR₁ ) ))
        ◅◅ ≡→≋ (sym (Uν-flat σ LD.L0 Bg QR))
