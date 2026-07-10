-- | Forward simulation, R-Drop, ported to a SINGLE untyped step.
--   Reuses the flatten/transpose engine (Bφ / Uν-flat / leafσ / …) and the
--   R-Drop vacuity + leaf machinery from the compiling Theorems.Drop; only the
--   real (b₁ = zero) clause's fire is rebuilt one-step (Bφ-lift-step for Bφ-red,
--   UR.RU-Drop for leaf-fire-drop, UR.RU-Res for the ν gmap) and packaged with
--   UR.RU-Struct.  The two vacuity clauses stay ⊥-elim (codomain-agnostic).
module BorrowedCF.Simulation.Forward.Drop where

open import BorrowedCF.Simulation.Base
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR

open import BorrowedCF.Simulation.Support.Theorems.Drop
  using ( Bφ; Bφ-cong; Bφ-⋯; φ-past-Bφ; subst-Bφ; leafσ; Uν-flat
        ; VSub-leafσ; leafσ-shift; assocPush-junc; frame-plug*ᵣ
        ; ≡→≋; ─→-subst
        ; head-noRet-last; noRet⇒≄ret; ⟨⟩≃; drop-handle-≃ret )

open import BorrowedCF.Simulation.Support.BlockPerm
  using ( toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-↑*-ge; toℕ-assoc-mid; toℕ-assoc-ge )

open import BorrowedCF.Simulation.Support.Frames using ( frame-plug*; frame*-⋯ )
open import BorrowedCF.Simulation.Support.InvFrame using ( strengthen-frame )
open import BorrowedCF.Simulation.Support.TranslationProperties using ( U-cong; U-⋯ₚ )

open import BorrowedCF.Simulation.Support.Theorems.B1VacProbe
  using ( NoRet; RetTip; new⇒noRet; noRet-≃
        ; retTip-Sc-skips; noRet-front-cons; retTip-≃; noRet-;-fst )
import BorrowedCF.Simulation.Support.Theorems.B1VacProbe as VP

open import BorrowedCF.Types.Equivalence using ( _≃𝕊_ )
import Relation.Binary.Construct.Closure.Equivalence as EqC

open TP using ( cons-ret/acq; cons )

-- single-step analogue of Bφ-red, over Theorems.Drop's own Bφ so the indices
-- line up; mirrors SplitsH1.Bφ-lift-step but via Drop's ─→-subst.
Bφ-lift-step : ∀ {n} (B : TP.BindGroup) {P Q : UP.Proc (syncs B + n)} →
               P UR.─→ₚ Q → Bφ {n} B P UR.─→ₚ Bφ B Q
Bφ-lift-step []            r = r
Bφ-lift-step (b ∷ [])      r = r
Bφ-lift-step {n} (b ∷ B@(_ ∷ _)) r =
  UR.RU-Sync (Bφ-lift-step B (─→-subst (sym (+-suc (syncs B) n)) r))

U-drop→ : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
       → {g : Struct m} {b₁ : ℕ} {B₁ B₂ : TP.BindGroup}
         {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
         {P : TP.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)}
       → Γ ; g ⊢ₚ TP.ν (suc b₁ ∷ B₁) B₂
           (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ))
       → U[ TP.ν (suc b₁ ∷ B₁) B₂
             (TP.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ TP.∥ (P TP.⋯ₚ weakenᵣ)) ] σ
            UR.─→ₚ U[ TP.ν (b₁ ∷ B₁) B₂ (TP.⟪ E [ * ]* ⟫ TP.∥ P) ] σ
U-drop→ σ Vσ Γ-S {b₁ = b₁} {B₁ = []} {B₂ = B₂} {E = E} {P = P} ⊢P
  with inv-ν ⊢P
... | _ , _ , sN , _ , N , _ , _ , C , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-noRet-last (VP._;_ (new⇒noRet N) VP.end) C
... | s , Γ0≡ , Ns
  = ⊥-elim (noRet⇒≄ret Ns (⟨⟩≃ (≃-trans (≃-reflexive (sym Γ0≡)) (drop-handle-≃ret ⊢plug))))
U-drop→ {m} {n} σ Vσ Γ-S {b₁ = suc b₁} {B₁ = C@(_ ∷ _)} {B₂ = B₂} {E = E} {P = P} ⊢P
  with inv-ν ⊢P
... | _ , _ , sN , _ , N , _ , _
    , cons-ret/acq sh scra Γ≗ (cons s1ʰ s2ʰ ¬sk1 s≃1 Γ≗1 (cons _ _ ¬Ss s≃2 _ _)) _ , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  = ⊥-elim (¬Ss (retTip-Sc-skips rt-borrow head≃ret))
  where
    head≃ret : s1ʰ ≃ ret
    head≃ret = ⟨⟩≃ (≃-trans (≃-reflexive (sym (sym (Γ≗ 0F) ■ sym (Γ≗1 0F)))) (drop-handle-≃ret ⊢plug))
    noRet-sh : NoRet sh
    noRet-sh = noRet-;-fst (noRet-≃ (EqC.symmetric _≃𝕊_ scra) (VP._;_ (new⇒noRet N) VP.end))
    rt-borrow : RetTip (s1ʰ ; s2ʰ)
    rt-borrow = retTip-≃ (EqC.symmetric _≃𝕊_ s≃1) (noRet-front-cons noRet-sh)
U-drop→ {m} {n} σ Vσ Γ-S {b₁ = zero} {B₁ = C@(cHd ∷ cTl)} {B₂ = B₂} {E = E} {P = P} ⊢P =
  UR.RU-Struct front fire₁ back
  where
    Eᵂ : Frame* (sum (suc zero ∷ C) + sum B₂ + m)
    Eᵂ = E ⋯ᶠ* weakenᵣ
    Pᵂ : TP.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    Pᵂ = P TP.⋯ₚ weakenᵣ
    QL : TP.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    QL = TP.⟪ Eᵂ [ K `drop ·¹ (` 0F) ]* ⟫ TP.∥ Pᵂ
    QR : TP.Proc (sum (zero ∷ C) + sum B₂ + m)
    QR = TP.⟪ E [ K `unit ]* ⟫ TP.∥ P
    sC = syncs C
    sB₂ = syncs B₂
    LL : UP.Proc (sB₂ + (suc sC + (2 + n)))
    LL = U[ QL ] (leafσ σ (suc zero ∷ C) B₂)
    flatL : U[ TP.ν (suc zero ∷ C) B₂ QL ] σ
            ≡ UP.ν (Bφ (suc zero ∷ C) (Bφ B₂ LL))
    flatL = Uν-flat σ (suc zero ∷ C) B₂ QL
    flatR : U[ TP.ν (zero ∷ C) B₂ QR ] σ
            ≡ UP.ν (Bφ (zero ∷ C) (Bφ B₂ (U[ QR ] (leafσ σ (zero ∷ C) B₂))))
    flatR = Uν-flat σ (zero ∷ C) B₂ QR
    eqC : sB₂ + suc (sC + suc (suc n)) ≡ sB₂ + (sC + suc (suc (suc n)))
    eqC = cong (sB₂ +_) (sym (+-suc sC (suc (suc n))))
    -- leaf after pushing φ drop past Bφ C then Bφ B₂
    LL₂ : UP.Proc (suc (sB₂ + (sC + (2 + n))))
    LL₂ = subst UP.Proc eqC LL
            UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)
            UP.⋯ₚ assocSwapᵣ sB₂ 1
    mid : UP.Proc n
    mid = UP.ν (Bφ C (Bφ B₂ (UP.φ UP.drop LL₂)))
    -- generic: push a head φ z past Bφ C then Bφ B₂ down to the leaf, keeping ν.
    pushφ-down : (z : UP.Flag) (X : UP.Proc (sB₂ + (suc sC + (2 + n)))) →
      UP.φ z (Bφ C (subst UP.Proc (sym (+-suc sC (suc (suc n)))) (Bφ B₂ X)))
        UP.≋
      Bφ C (Bφ B₂ (UP.φ z (subst UP.Proc eqC X
                            UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)
                            UP.⋯ₚ assocSwapᵣ sB₂ 1)))
    pushφ-down z X =
         φ-past-Bφ C z (subst UP.Proc (sym (+-suc sC (suc (suc n)))) (Bφ B₂ X))
      ◅◅ Bφ-cong C (UP.φ-cong (≡→≋
           ( cong (UP._⋯ₚ assocSwapᵣ sC 1)
               (subst-Bφ (sym (+-suc sC (suc (suc n)))) B₂ X)
           ■ Bφ-⋯ B₂ (subst UP.Proc eqC X) (assocSwapᵣ sC 1) )))
      ◅◅ Bφ-cong C (φ-past-Bφ B₂ z
           (subst UP.Proc eqC X UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)))
    front : U[ TP.ν (suc zero ∷ C) B₂ QL ] σ UP.≋ mid
    front = ≡→≋ flatL ◅◅ UP.ν-cong (pushφ-down UP.drop LL)
    -- decompose LL₂ into ⟪ redex-thread ⟫ ∥ residual
    subst-∥ : ∀ {a b} (eq : a ≡ b) (X Y : UP.Proc a) →
              subst UP.Proc eq (X UP.∥ Y) ≡ subst UP.Proc eq X UP.∥ subst UP.Proc eq Y
    subst-∥ refl X Y = refl
    subst-⟪⟫ : ∀ {a b} (eq : a ≡ b) (t : Tm a) →
               subst UP.Proc eq UP.⟪ t ⟫ ≡ UP.⟪ subst Tm eq t ⟫
    subst-⟪⟫ refl t = refl
    aTm : Tm (sB₂ + (suc sC + (2 + n)))
    aTm = (Eᵂ [ K `drop ·¹ (` 0F) ]*) ⋯ leafσ σ (suc zero ∷ C) B₂
    bPr : UP.Proc (sB₂ + (suc sC + (2 + n)))
    bPr = U[ Pᵂ ] (leafσ σ (suc zero ∷ C) B₂)
    -- the redex thread after subst+renamings
    redTm : Tm (suc (sB₂ + (sC + (2 + n))))
    redTm = subst Tm eqC aTm ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
    Qᶠ : UP.Proc (suc (sB₂ + (sC + (2 + n))))
    Qᶠ = subst UP.Proc eqC bPr UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1
    LL₂-split : LL₂ ≡ UP.⟪ redTm ⟫ UP.∥ Qᶠ
    LL₂-split =
        cong (UP._⋯ₚ assocSwapᵣ sB₂ 1)
          (cong (UP._⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂))
            (subst-∥ eqC UP.⟪ aTm ⟫ bPr
             ■ cong (UP._∥ subst UP.Proc eqC bPr) (subst-⟪⟫ eqC aTm)))
    -- the combined value-substitution applied to the redex thread
    Vleafσ : VSub (leafσ σ (suc zero ∷ C) B₂)
    Vleafσ = VSub-leafσ σ Vσ (suc zero ∷ C) B₂
    θ : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ suc (sB₂ + (sC + (2 + n)))
    θ = ((subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
          ·ₖ (assocSwapᵣ sC 1 ↑* sB₂)) ·ₖ assocSwapᵣ sB₂ 1
    Vθ-cod : ∀ {a c} {t : Tm a} (eq : a ≡ c) → Value t → Value (subst Tm eq t)
    Vθ-cod refl V = V
    subst-cod-pt : ∀ {a c} (eq : a ≡ c) (s : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                   subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
    subst-cod-pt refl s i = refl
    Vθ : VSub θ
    Vθ i = value-⋯ (value-⋯
             (subst Value (sym (subst-cod-pt eqC (leafσ σ (suc zero ∷ C) B₂) i))
               (Vθ-cod eqC (Vleafσ i)))
             (assocSwapᵣ sC 1 ↑* sB₂) (λ _ → V-`))
             (assocSwapᵣ sB₂ 1) (λ _ → V-`)
    subst-⊗ : ∀ {a b} (eq : a ≡ b) (p r : Tm a) →
              subst Tm eq (p ⊗ r) ≡ subst Tm eq p ⊗ subst Tm eq r
    subst-⊗ refl p r = refl
    subst-`F : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
    subst-`F refl q = refl
    -- the dropped handle term under θ is a chanTriple with `suc x` middle, `0F last
    handle : Σ[ e ∈ Tm (suc (sB₂ + (sC + (2 + n)))) ]
             Σ[ x ∈ 𝔽 (sB₂ + (sC + (2 + n))) ]
               θ 0F ≡ ((e ⊗ (` (Fin.suc x))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))
    handle = handleE , handleX , handleEq
      where
        ρ1 = assocSwapᵣ sC 1 ↑* sB₂
        ρ2 = assocSwapᵣ sB₂ 1
        handleE : Tm (suc (sB₂ + (sC + (2 + n))))
        handleE = K `unit
        handleX : 𝔽 (sB₂ + (sC + (2 + n)))
        handleX = weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc n}))
        midV0 : 𝔽 (sC + suc (suc (suc n)))
        midV0 = weaken* ⦃ Kᵣ ⦄ sC (Fin.suc (Fin.zero {n = suc n}))
        lastV0 : 𝔽 (sC + suc (suc (suc n)))
        lastV0 = weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc (suc n)})
        l0≡ : leafσ σ (suc zero ∷ C) B₂ 0F
              ≡ subst Tm (+-suc sC (suc (suc n)))
                    (((K `unit) ⊗ (` midV0)) ⊗ (` lastV0))
                  ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        l0≡ = refl
        rnV : 𝔽 (sC + suc (suc (suc n))) → 𝔽 (suc (sB₂ + (sC + (2 + n))))
        rnV v = ρ2 (ρ1 (subst 𝔽 eqC
                  (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))))
        toℕ-subst𝔽 : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → Fin.toℕ (subst 𝔽 eq q) ≡ Fin.toℕ q
        toℕ-subst𝔽 refl q = refl
        -- inner var of rnV before the ρ1/ρ2 push, with toℕ characterisation.
        innerV : 𝔽 (sC + suc (suc (suc n))) → 𝔽 (sB₂ + (sC + (1 + (2 + n))))
        innerV v = subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))
        innerV-toℕ : (v : 𝔽 (sC + suc (suc (suc n)))) (d : ℕ) →
                     Fin.toℕ v ≡ sC + d → Fin.toℕ (innerV v) ≡ sB₂ + (sC + d)
        innerV-toℕ v d veq =
            toℕ-subst𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))
          ■ toℕ-weaken*ᵣ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v)
          ■ cong (sB₂ +_) (toℕ-subst𝔽 (+-suc sC (suc (suc n))) v ■ veq)
        midV0-toℕ : Fin.toℕ midV0 ≡ sC + 1
        midV0-toℕ = toℕ-weaken*ᵣ sC (Fin.suc (Fin.zero {n = suc n}))
        lastV0-toℕ : Fin.toℕ lastV0 ≡ sC + 0
        lastV0-toℕ = toℕ-weaken*ᵣ sC (Fin.zero {n = suc (suc n)})
        mid≡ : rnV midV0 ≡ Fin.suc handleX
        mid≡ = Fin.toℕ-injective
          ( toℕ-assoc-ge sB₂ 1 ((assocSwapᵣ sC 1 ↑* sB₂) (innerV midV0)) geρ2
          ■ toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (innerV midV0) geB
          ■ cong (sB₂ +_) (toℕ-assoc-ge sC 1 (Fin.reduce≥ (innerV midV0) geB) geρ1)
          ■ cong (sB₂ +_) redmid
          ■ sym ( cong suc (toℕ-weaken*ᵣ sB₂ (weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc n}))
                          ■ cong (sB₂ +_) (toℕ-weaken*ᵣ sC (Fin.zero {n = suc n})
                                          ■ Nat.+-identityʳ sC))
                ■ sym (Nat.+-suc sB₂ sC)
                ■ cong (sB₂ +_) (sym (Nat.+-comm sC 1)) ) )
          where
            imeq : Fin.toℕ (innerV midV0) ≡ sB₂ + (sC + 1)
            imeq = innerV-toℕ midV0 1 midV0-toℕ
            geB : sB₂ Nat.≤ Fin.toℕ (innerV midV0)
            geB = subst (sB₂ Nat.≤_) (sym imeq) (Nat.m≤m+n sB₂ (sC + 1))
            redmid : Fin.toℕ (Fin.reduce≥ (innerV midV0) geB) ≡ sC + 1
            redmid = toℕ-reduce≥ (innerV midV0) geB ■ cong (Nat._∸ sB₂) imeq ■ Nat.m+n∸m≡n sB₂ (sC + 1)
            geρ1 : sC + 1 Nat.≤ Fin.toℕ (Fin.reduce≥ (innerV midV0) geB)
            geρ1 = subst (sC + 1 Nat.≤_) (sym redmid) Nat.≤-refl
            geρ2 : sB₂ + 1 Nat.≤ Fin.toℕ ((assocSwapᵣ sC 1 ↑* sB₂) (innerV midV0))
            geρ2 = subst (sB₂ + 1 Nat.≤_)
                     (sym ( toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (innerV midV0) geB
                          ■ cong (sB₂ +_) (toℕ-assoc-ge sC 1 (Fin.reduce≥ (innerV midV0) geB) geρ1 ■ redmid) ))
                     (Nat.+-monoʳ-≤ sB₂ (subst (1 Nat.≤_) (Nat.+-comm 1 sC) (Nat.s≤s (Nat.z≤n {sC}))))
        last≡ : rnV lastV0 ≡ Fin.zero {n = sB₂ + (sC + (2 + n))}
        last≡ = Fin.toℕ-injective
          (assocPush-junc sC sB₂ 1 0 (innerV lastV0) (innerV-toℕ lastV0 0 lastV0-toℕ) (Nat.s≤s Nat.z≤n))
        θ0≡ : θ 0F ≡ subst Tm eqC (leafσ σ (suc zero ∷ C) B₂ 0F) ⋯ ρ1 ⋯ ρ2
        θ0≡ = cong (λ z → z ⋯ ρ1 ⋯ ρ2) (subst-cod-pt eqC (leafσ σ (suc zero ∷ C) B₂) 0F)
        subst-K : ∀ {a b} (eq : a ≡ b) (c : _) → subst Tm eq (K c) ≡ K c
        subst-K refl c = refl
        -- push subst (+-suc) through the chanTriple ⊗-structure
        push1 : subst Tm (+-suc sC (suc (suc n))) (((K `unit) ⊗ (` midV0)) ⊗ (` lastV0))
                ≡ ((K `unit ⊗ (` subst 𝔽 (+-suc sC (suc (suc n))) midV0))
                    ⊗ (` subst 𝔽 (+-suc sC (suc (suc n))) lastV0))
        push1 = subst-⊗ (+-suc sC (suc (suc n))) ((K `unit) ⊗ (` midV0)) (` lastV0)
              ■ cong₂ _⊗_
                  (subst-⊗ (+-suc sC (suc (suc n))) (K `unit) (` midV0)
                   ■ cong₂ _⊗_ (subst-K (+-suc sC (suc (suc n))) `unit)
                               (subst-`F (+-suc sC (suc (suc n))) midV0))
                  (subst-`F (+-suc sC (suc (suc n))) lastV0)
        -- push subst eqC through (after ⋯ weaken*sB₂, which is definitional over ⊗)
        push2 : subst Tm eqC
                  ((K `unit ⊗ (` weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0)))
                    ⊗ (` weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0)))
                ≡ ((K `unit ⊗ (` subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0))))
                    ⊗ (` subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0))))
        push2 = subst-⊗ eqC _ _
              ■ cong₂ _⊗_
                  (subst-⊗ eqC (K `unit) _
                   ■ cong₂ _⊗_ (subst-K eqC `unit)
                               (subst-`F eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0))))
                  (subst-`F eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0)))
        decomp : subst Tm eqC (leafσ σ (suc zero ∷ C) B₂ 0F) ⋯ ρ1 ⋯ ρ2
                 ≡ ((K `unit ⊗ (` rnV midV0)) ⊗ (` rnV lastV0))
        decomp =
            cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρ1 ⋯ ρ2) push1
          ■ cong (λ z → subst Tm eqC z ⋯ ρ1 ⋯ ρ2) refl
          ■ cong (λ z → z ⋯ ρ1 ⋯ ρ2) push2
        handleEq : θ 0F ≡ ((handleE ⊗ (` (Fin.suc handleX))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))
        handleEq = θ0≡ ■ decomp
                 ■ cong (λ z → (K `unit ⊗ (` z)) ⊗ (` rnV lastV0)) mid≡
                 ■ cong (λ z → (K `unit ⊗ (` Fin.suc handleX)) ⊗ (` z)) last≡
    subst-⋯ₛ-cod : ∀ {a c d} (q : c ≡ d) (t : Tm a) (s : a →ₛ c) →
                   t ⋯ subst (λ z → a →ₛ z) q s ≡ subst Tm q (t ⋯ s)
    subst-⋯ₛ-cod refl t s = refl
    redTm≡θ : redTm ≡ (Eᵂ [ K `drop ·¹ (` 0F) ]*) ⋯ θ
    redTm≡θ =
        cong (λ z → z ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
          (sym (subst-⋯ₛ-cod eqC (Eᵂ [ K `drop ·¹ (` 0F) ]*) (leafσ σ (suc zero ∷ C) B₂)))
      ■ cong (_⋯ assocSwapᵣ sB₂ 1)
          (fusion (Eᵂ [ K `drop ·¹ (` 0F) ]*)
            (subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
            (assocSwapᵣ sC 1 ↑* sB₂))
      ■ fusion (Eᵂ [ K `drop ·¹ (` 0F) ]*)
          ((subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
            ·ₖ (assocSwapᵣ sC 1 ↑* sB₂))
          (assocSwapᵣ sB₂ 1)
    -- the redex thread is a drop-redex applied to a chanTriple ending in `0F
    redShapeF : Frame* (suc (sB₂ + (sC + (2 + n))))
    redShapeF = frame*-⋯ Eᵂ θ Vθ
    redShapeE : Tm (suc (sB₂ + (sC + (2 + n))))
    redShapeE = proj₁ handle
    redShapeX : 𝔽 (sB₂ + (sC + (2 + n)))
    redShapeX = proj₁ (proj₂ handle)
    redShapeEq : redTm ≡ redShapeF [ K `drop ·¹ (((redShapeE ⊗ (` (Fin.suc redShapeX))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))) ]*
    redShapeEq =
        redTm≡θ
      ■ frame-plug* Eᵂ θ Vθ
      ■ cong (redShapeF [_]*) (cong (K `drop ·¹_) (proj₂ (proj₂ handle)))
    redShape : Σ[ F ∈ Frame* (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ e ∈ Tm (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ x ∈ 𝔽 (sB₂ + (sC + (2 + n))) ]
                 redTm ≡ F [ K `drop ·¹ (((e ⊗ (` (Fin.suc x))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))) ]*
    redShape = redShapeF , redShapeE , redShapeX , redShapeEq
    Eᶠ : Frame* (suc (sB₂ + (sC + (2 + n))))
    Eᶠ = redShapeF
    fired : UP.Proc n
    fired = UP.ν (Bφ C (Bφ B₂ (UP.φ UP.acq (UP.⟪ Eᶠ [ K `unit ]* ⟫ UP.∥ Qᶠ))))
    fire₁ : mid UR.─→ₚ fired
    fire₁ = UR.RU-Res
      (Bφ-lift-step C (Bφ-lift-step B₂
        (subst (λ z → UP.φ UP.drop z UR.─→ₚ UP.φ UP.acq (UP.⟪ Eᶠ [ K `unit ]* ⟫ UP.∥ Qᶠ))
          (sym (LL₂-split ■ cong (UP._∥ Qᶠ) (cong UP.⟪_⟫ (proj₂ (proj₂ (proj₂ redShape))))))
          (UR.RU-Drop Eᶠ {proj₁ (proj₂ (proj₂ redShape))}))))
    Yleaf : UP.Proc (sB₂ + (suc sC + (2 + n)))
    Yleaf = U[ QR ] (leafσ σ (zero ∷ C) B₂)
    aR : Tm (sB₂ + (suc sC + (2 + n)))
    aR = (E [ K `unit ]*) ⋯ leafσ σ (zero ∷ C) B₂
    bR : UP.Proc (sB₂ + (suc sC + (2 + n)))
    bR = U[ P ] (leafσ σ (zero ∷ C) B₂)
    Yleaf≡ : Yleaf ≡ UP.⟪ aR ⟫ UP.∥ bR
    Yleaf≡ = refl
    RHS-split : subst UP.Proc eqC Yleaf UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1
                ≡ UP.⟪ subst Tm eqC aR ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1 ⟫
                  UP.∥ (subst UP.Proc eqC bR UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1)
    RHS-split =
        cong (λ z → z UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1)
          (subst-∥ eqC UP.⟪ aR ⟫ bR ■ cong (UP._∥ subst UP.Proc eqC bR) (subst-⟪⟫ eqC aR))
    reconcile : (UP.⟪ Eᶠ [ K `unit ]* ⟫ UP.∥ Qᶠ)
                ≡ subst UP.Proc eqC Yleaf UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1
    reconcile = cong₂ UP._∥_ thread resid ■ sym RHS-split
      where
        subst-cod-ptR : ∀ {a c} (eq : a ≡ c) (s : (sum (zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                        subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
        subst-cod-ptR refl s i = refl
        subst-cod-pt1 : ∀ {a c} (eq : a ≡ c) (s : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                        subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
        subst-cod-pt1 refl s i = refl
        -- dropping the head handle of leafσ (suc zero ∷ C) recovers leafσ (zero ∷ C).
        leaf-drop-head : (i : 𝔽 (sum (zero ∷ C) + sum B₂ + m)) →
                         leafσ σ (suc zero ∷ C) B₂ (weakenᵣ i) ≡ leafσ σ (zero ∷ C) B₂ i
        leaf-drop-head i = sym (leafσ-shift σ cHd cTl B₂ i)
        -- *⋯θ = * (K `unit is closed).
        unit-θ : (K `unit) ⋯ θ ≡ K `unit
        unit-θ = refl
        -- Eᶠ[*]* = (Eᵂ[*]*) ⋯ θ
        Eᶠ-plug : Eᶠ [ K `unit ]* ≡ (Eᵂ [ K `unit ]*) ⋯ θ
        Eᶠ-plug = sym (frame-plug* Eᵂ θ Vθ ■ cong (frame*-⋯ Eᵂ θ Vθ [_]*) unit-θ)
        -- Eᵂ[*]* = (E[*]*) ⋯ weakenᵣ
        Eᵂ-plug : Eᵂ [ K `unit ]* ≡ (E [ K `unit ]*) ⋯ weakenᵣ
        Eᵂ-plug = sym (frame-plug*ᵣ E weakenᵣ)
        -- the leaf-substitution agreement, pointwise, lifted through subst eqC and ρ1,ρ2
        θ-agree : (x : 𝔽 (sum (zero ∷ C) + sum B₂ + m)) →
                  θ (weakenᵣ x)
                  ≡ subst Tm eqC (leafσ σ (zero ∷ C) B₂ x)
                      ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
        θ-agree x =
            cong (λ t → t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (subst-cod-pt1 eqC (leafσ σ (suc zero ∷ C) B₂) (weakenᵣ x))
          ■ cong (λ t → subst Tm eqC t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (leaf-drop-head x)
        -- the codomain leaf substitution for the RHS (leafσ of zero ∷ C).
        θR : (sum (zero ∷ C) + sum B₂ + m) →ₛ suc (sB₂ + (sC + (2 + n)))
        θR = ((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
               ·ₖ (assocSwapᵣ sC 1 ↑* sB₂)) ·ₖ assocSwapᵣ sB₂ 1
        aR≡θR : subst Tm eqC aR ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
                ≡ (E [ K `unit ]*) ⋯ θR
        aR≡θR =
            cong (λ z → z ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (sym (subst-⋯ₛ-cod eqC (E [ K `unit ]*) (leafσ σ (zero ∷ C) B₂)))
          ■ cong (_⋯ assocSwapᵣ sB₂ 1)
              (fusion (E [ K `unit ]*)
                (subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
                (assocSwapᵣ sC 1 ↑* sB₂))
          ■ fusion (E [ K `unit ]*)
              ((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
                ·ₖ (assocSwapᵣ sC 1 ↑* sB₂))
              (assocSwapᵣ sB₂ 1)
        -- (weakenᵣ ·ₖ θ) agrees pointwise with θR (the head-handle drop).
        θ-agreeR : (weakenᵣ ·ₖ θ) ≗ θR
        θ-agreeR x = θ-agree x
                   ■ cong (λ t → t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
                       (sym (subst-cod-ptR eqC (leafσ σ (zero ∷ C) B₂) x))
        thread =
          cong UP.⟪_⟫
            ( Eᶠ-plug
            ■ cong (_⋯ θ) Eᵂ-plug
            ■ fusion (E [ K `unit ]*) weakenᵣ θ
            ■ ⋯-cong (E [ K `unit ]*) θ-agreeR
            ■ sym aR≡θR )
        resid : Qᶠ ≡ subst UP.Proc eqC bR UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1
        resid = cong (λ z → subst UP.Proc eqC z UP.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) UP.⋯ₚ assocSwapᵣ sB₂ 1)
                  (U-⋯ₚ P {ρ = weakenᵣ} {σ = leafσ σ (suc zero ∷ C) B₂}
                   ■ U-cong P leaf-drop-head)
    back : fired UP.≋ U[ TP.ν (zero ∷ C) B₂ QR ] σ
    back =
         UP.ν-cong (Bφ-cong C (Bφ-cong B₂ (UP.φ-cong (≡→≋ reconcile))))
      ◅◅ Eq*.symmetric _ (UP.ν-cong (pushφ-down UP.acq Yleaf))
      ◅◅ ≡→≋ (sym (Uν-flat σ (zero ∷ C) B₂ QR))
