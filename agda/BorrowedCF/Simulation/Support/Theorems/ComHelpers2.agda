module BorrowedCF.Simulation.Support.Theorems.ComHelpers2 where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.Support.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; mapᶜ-fusion; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.Support.BlockPerm
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
open import BorrowedCF.Simulation.Support.InvFrame using (inv-app; inv-pair; arg-type; strengthen-frame)
open import BorrowedCF.Types using (Bounded; ≃-bounded; Skips; skips⊥bounded)
open import BorrowedCF.Context.Join using (biasedDir)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.Support.TranslationProperties using (VChan; chanTriple-V; Value-subst)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers1 public
open import BorrowedCF.Simulation.Support.Theorems.PhiTel
  using ( Btel; Bφ; canonₛ; leafσ; Uν-flatΦ; plugΦ-subst ) public
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; []φ; _◂_; plugΦ)

------------------------------------------------------------------------
-- Channel-carrying φ-telescope engine (linked-φ design).
--
-- `U-ν-swap` (image of a typed ν-swap) is a CONGRUENCE / block move: the two
-- flattened nests (via `Uν-flatΦ`) differ by swapping the B₁-block and the
-- B₂-block of the channel-carrying φ-telescope.  The block swap is realised by
-- the gate-safe untyped `φ-comm′` (a φ past a φ — never a φ past a ν) plus the
-- `ν-swap′` on the two data channels, and the leaf substitution is reconciled
-- by the channel-agnostic `subEq-gen` re-exported from ComHelpers1.
------------------------------------------------------------------------

-- congruence of plugΦ in its body.
plugΦ-cong : ∀ {a b} (Φ : Φ* a b) {P Q : U.Proc b} → P U.≋ Q → plugΦ Φ P U.≋ plugΦ Φ Q
plugΦ-cong []φ            pq = pq
plugΦ-cong ((f , c) ◂ Φ)  pq = U.φ-cong (plugΦ-cong Φ pq)

-- congruence of Bφ in its body.
Bφ-cong-c : ∀ {n} (B : BindGroup) (cc : UChan n) {P Q : U.Proc (syncs B + n)} →
            P U.≋ Q → Bφ B cc P U.≋ Bφ B cc Q
Bφ-cong-c B cc pq = plugΦ-cong (Btel B cc) pq

-- one-cell unfolding of Bφ on a non-singleton head.
Bφ-cons : ∀ {n} (b c : ℕ) (B : BindGroup) (e1 e2 : Tm n) (x : 𝔽 n)
          (P : U.Proc (syncs (b ∷ c ∷ B) + n)) →
          Bφ (b ∷ c ∷ B) (e1 , x , e2) P
          ≡ U.φ ϕ[ b ] (` x)
              (Bφ (c ∷ B) (` 0F , suc x , wk e2)
                (subst U.Proc (sym (+-suc (syncs (c ∷ B)) n)) P))
Bφ-cons {n} b c B e1 e2 x P =
  cong (U.φ ϕ[ b ] (` x))
    (plugΦ-subst (+-suc (syncs (c ∷ B)) n) (Btel (c ∷ B) (` 0F , suc x , wk e2)) P)

-- naturality of Bφ under target renaming (channel-carrying `Bφ-⋯`).
Bφ-⋯-c : ∀ {n n′} (B : BindGroup) (cc : UChan n) (P : U.Proc (syncs B + n)) (ρ : n →ᵣ n′) →
         Bφ B cc P U.⋯ₚ ρ ≡ Bφ B (mapᶜ ρ cc) (P U.⋯ₚ (ρ ↑* syncs B))
Bφ-⋯-c []            cc            P ρ = refl
Bφ-⋯-c (b ∷ [])      cc            P ρ = refl
Bφ-⋯-c {n} {n′} (b ∷ c ∷ B) (e1 , x , e2) P ρ =
    cong (U._⋯ₚ ρ) (Bφ-cons b c B e1 e2 x P)
  ■ cong (U.φ ϕ[ b ] (` ρ x))
      ( Bφ-⋯-c (c ∷ B) (` 0F , suc x , wk e2) (subst U.Proc (sym (+-suc sCB n)) P) (ρ ↑)
      ■ cong₂ (λ cc′ Q → Bφ (c ∷ B) cc′ Q) channelEq bodyEq )
  ■ sym (Bφ-cons b c B (e1 ⋯ ρ) (e2 ⋯ ρ) (ρ x) (P U.⋯ₚ (ρ ↑* suc sCB)))
  where
    sCB = syncs (c ∷ B)
    channelEq : mapᶜ (ρ ↑) (` 0F , suc x , wk e2)
                ≡ (` 0F , suc (ρ x) , wk (e2 ⋯ ρ))
    channelEq = cong (λ t → (` 0F , suc (ρ x) , t)) (sym (⋯-↑-wk e2 ρ))
    Θ : (sCB + suc n) →ᵣ (sCB + suc n′)
    Θ = (ρ ↑) ↑* sCB
    Θ⁺eq : subst (λ z → z →ᵣ (sCB + suc n′)) (+-suc sCB n) Θ
           ≡ subst (λ z → suc (sCB + n) →ᵣ z) (sym (+-suc sCB n′)) (ρ ↑* suc sCB)
    Θ⁺eq = subst-flip (+-suc sCB n′) (sym (subst₂→ (+-suc sCB n) (+-suc sCB n′) Θ) ■ liftCast sCB ρ)
    bodyEq : (subst U.Proc (sym (+-suc sCB n)) P) U.⋯ₚ ((ρ ↑) ↑* sCB)
             ≡ subst U.Proc (sym (+-suc sCB n′)) (P U.⋯ₚ (ρ ↑* suc sCB))
    bodyEq =
        TP-subst-⋯ₚ-dom (+-suc sCB n) P Θ
      ■ cong (P U.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-cod (sym (+-suc sCB n′)) P (ρ ↑* suc sCB)

weaken*1≡suc : ∀ {p} (x : 𝔽 p) → weaken* ⦃ Kᵣ ⦄ 1 x ≡ suc x
weaken*1≡suc x = weaken*~↑ʳ 1 x

-- φ-comm′ presented with the crossed cell's channel in suc-headed form.
φ-comm-c : ∀ {n} (f₁ f₂ : U.Flag) (c : Tm n) (v : 𝔽 n) (P : U.Proc (2 + n)) →
   U.φ f₁ c (U.φ f₂ (` suc v) P)
     U.≋ U.φ f₂ (` v) (U.φ f₁ (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (P U.⋯ₚ assocSwapᵣ 1 1))
φ-comm-c {n} f₁ f₂ c v P =
  subst (λ w → U.φ f₁ c (U.φ f₂ (` w) P)
                 U.≋ U.φ f₂ (` v) (U.φ f₁ (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (P U.⋯ₚ assocSwapᵣ 1 1)))
        (weaken*1≡suc v)
        (Eq*.return U.φ-comm′)

-- subst over U.Proc commutes through a φ-binder.
subst-φ : ∀ {a b} (eq : a ≡ b) {z : U.Flag} {c : Tm a} (Q : U.Proc (suc a)) →
          subst U.Proc eq (U.φ z c Q)
          ≡ U.φ z (subst Tm eq c) (subst U.Proc (cong suc eq) Q)
subst-φ refl Q = refl

-- transport a renaming through substs on both ends (Proc).
substⱼ-⋯ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (X : U.Proc a′)
           (ρ : a →ᵣ b) (ρ′ : a′ →ᵣ b′) →
           (∀ x → ρ x ≡ subst 𝔽 (sym q) (ρ′ (subst 𝔽 p x))) →
           subst U.Proc (sym p) X U.⋯ₚ ρ ≡ subst U.Proc (sym q) (X U.⋯ₚ ρ′)
substⱼ-⋯ refl refl X ρ ρ′ h = U.⋯ₚ-cong X h

-- transport a renaming through substs on both ends (Tm).
substⱼ-⋯ₜ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (t : Tm a′)
            (ρ : a →ᵣ b) (ρ′ : a′ →ᵣ b′) →
            (∀ x → ρ x ≡ subst 𝔽 (sym q) (ρ′ (subst 𝔽 p x))) →
            subst Tm (sym p) t ⋯ ρ ≡ subst Tm (sym q) (t ⋯ ρ′)
substⱼ-⋯ₜ refl refl t ρ ρ′ h = ⋯-cong t h

toℕ-subst𝔽ᶜ : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
toℕ-subst𝔽ᶜ refl y = refl

cast≡subst : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.cast e y ≡ subst 𝔽 e y
cast≡subst refl y = Fin.cast-is-id refl y

assoc11-0 : ∀ {p} → assocSwapᵣ 1 1 {p} 0F ≡ 1F
assoc11-0 {p} = Fin.toℕ-injective (toℕ-assoc-lt 1 1 {p} 0F (Nat.s≤s Nat.z≤n))

assoc11-ss : ∀ {p} (w : 𝔽 p) → assocSwapᵣ 1 1 (suc (suc w)) ≡ suc (suc w)
assoc11-ss {p} w = Fin.toℕ-injective (toℕ-assoc-ge 1 1 {p} (suc (suc w)) (Nat.s≤s (Nat.s≤s Nat.z≤n)))

wkwk-assoc11 : ∀ {p} (t : Tm p) → wk (wk t) ⋯ assocSwapᵣ 1 1 ≡ wk (wk t)
wkwk-assoc11 t =
    cong (_⋯ assocSwapᵣ 1 1) (fusion t weaken weaken)
  ■ fusion t (weaken ·ₖ weaken) (assocSwapᵣ 1 1)
  ■ ⋯-cong t (λ x → assoc11-ss x)
  ■ sym (fusion t weaken weaken)

-- Push a single φ cell (flag f_z, channel c_z) past a whole `Bφ B` block whose
-- channels are `mapᶜ weaken` of ambient (so every cell avoids f_z's binder,
-- keeping every `φ-comm′` gate-safe).  Channel-carrying `φ-past-Bφ`.
φ-past-Bφ-c : ∀ {n} (B : BindGroup) (f_z : U.Flag) (c_z : Tm n) (cc₀ : UChan n)
              (X : U.Proc (syncs B + suc n)) →
   U.φ f_z c_z (Bφ B (mapᶜ (weaken ⦃ Kᵣ ⦄) cc₀) X)
     U.≋ Bφ B cc₀ (U.φ f_z (c_z ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) (X U.⋯ₚ assocSwapᵣ (syncs B) 1))
φ-past-Bφ-c []            f_z c_z cc₀ X =
  ≡→≋ (cong₂ (U.φ f_z) (sym (⋯-id c_z (λ _ → refl)))
              (sym (local-⋯ₚ-id X assocSwap-01)))
φ-past-Bφ-c (b ∷ [])      f_z c_z cc₀ X =
  ≡→≋ (cong₂ (U.φ f_z) (sym (⋯-id c_z (λ _ → refl)))
              (sym (local-⋯ₚ-id X assocSwap-01)))
φ-past-Bφ-c {n} (b ∷ c ∷ B₀) f_z c_z (g1 , w , g2) X =
     ≡→≋ (cong (U.φ f_z c_z) (Bφ-cons {suc n} b c B₀ (wk g1) (wk g2) (suc w) X))
  ◅◅ φ-comm-c f_z ϕ[ b ] c_z w (Bφ (c ∷ B₀) cc'' W)
  ◅◅ U.φ-cong
       ( U.φ-cong (≡→≋ (Bφ-⋯-c (c ∷ B₀) cc'' W (assocSwapᵣ 1 1)))
       ◅◅ U.φ-cong (≡→≋ (cong (λ cc → Bφ (c ∷ B₀) cc (W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sCB))) ccstep))
       ◅◅ φ-past-Bφ-c (c ∷ B₀) f_z (c_z ⋯ weaken* ⦃ Kᵣ ⦄ 1) (` 0F , suc w , wk g2)
            (W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sCB))
       ◅◅ Bφ-cong-c (c ∷ B₀) (` 0F , suc w , wk g2) (≡→≋ bodyren) )
  ◅◅ ≡→≋ (sym (Bφ-cons b c B₀ g1 g2 w
                (U.φ f_z (c_z ⋯ weaken* ⦃ Kᵣ ⦄ (suc sCB)) (X U.⋯ₚ assocSwapᵣ (suc sCB) 1))))
  where
    sCB = syncs (c ∷ B₀)
    cc'' : UChan (suc (suc n))
    cc'' = (` 0F , suc (suc w) , wk (wk g2))
    W : U.Proc (sCB + suc (suc n))
    W = subst U.Proc (sym (+-suc sCB (suc n))) X
    -- after the head swap, the tail block channels are `mapᶜ weaken` of the
    -- recursion triple.
    ccstep : mapᶜ (assocSwapᵣ 1 1) cc'' ≡ mapᶜ (weaken ⦃ Kᵣ ⦄) (` 0F , suc w , wk g2)
    ccstep = cong₂ _,_ (cong `_ assoc11-0) (cong₂ _,_ (assoc11-ss w) (wkwk-assoc11 g2))
    -- body / f_z-channel reconcile through the tail block's binders.
    ρ₁ : (sCB + suc (suc n)) →ᵣ suc (sCB + suc n)
    ρ₁ = (assocSwapᵣ 1 1 {n} ↑* sCB) ·ₖ assocSwapᵣ sCB 1 {suc n}
    ptwise : ∀ x → ρ₁ x ≡ subst 𝔽 (cong suc (sym (+-suc sCB n)))
                          (assocSwapᵣ (suc sCB) 1 {n} (subst 𝔽 (+-suc sCB (suc n)) x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R3 sCB x
      ■ cong (λ y → Fin.toℕ (assocSwapᵣ (suc sCB) 1 y)) (cast≡subst (+-suc sCB (suc n)) x)
      ■ sym (toℕ-subst𝔽ᶜ (cong suc (sym (+-suc sCB n)))
               (assocSwapᵣ (suc sCB) 1 (subst 𝔽 (+-suc sCB (suc n)) x))) )
    qq : suc (suc (sCB + n)) ≡ suc (sCB + suc n)
    qq = cong suc (sym (+-suc sCB n))
    chanren : (c_z ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ weaken* ⦃ Kᵣ ⦄ sCB
              ≡ subst Tm (sym (+-suc sCB n)) (c_z ⋯ weaken* ⦃ Kᵣ ⦄ (suc sCB))
    chanren =
        fusion c_z (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ sCB)
      ■ ⋯-cong c_z wkchan
      ■ subst-⋯-cod-local (sym (+-suc sCB n)) c_z (weaken* ⦃ Kᵣ ⦄ (suc sCB))
      where
        wkchan : weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ sCB
                 ≗ subst (λ z → n →ᵣ z) (sym (+-suc sCB n)) (weaken* ⦃ Kᵣ ⦄ (suc sCB))
        wkchan y =
            cong (weaken* ⦃ Kᵣ ⦄ sCB) (weaken*~↑ʳ 1 y)
          ■ weaken*~↑ʳ sCB (suc y)
          ■ subst-flip (+-suc sCB n) (↑ʳ-suc sCB y)
          ■ cong (subst 𝔽 (sym (+-suc sCB n))) (sym (weaken*~↑ʳ (suc sCB) y))
          ■ sym (subst-ren-cod (sym (+-suc sCB n)) (weaken* ⦃ Kᵣ ⦄ (suc sCB)) y)
    bodyren : U.φ f_z ((c_z ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ weaken* ⦃ Kᵣ ⦄ sCB)
                ((W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sCB)) U.⋯ₚ assocSwapᵣ sCB 1)
              ≡ subst U.Proc (sym (+-suc sCB n))
                  (U.φ f_z (c_z ⋯ weaken* ⦃ Kᵣ ⦄ (suc sCB)) (X U.⋯ₚ assocSwapᵣ (suc sCB) 1))
    bodyren =
        cong₂ (U.φ f_z) chanren bodyProc
      ■ sym (subst-φ (sym (+-suc sCB n)) (X U.⋯ₚ assocSwapᵣ (suc sCB) 1))
      where
        bodyProc : (W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sCB)) U.⋯ₚ assocSwapᵣ sCB 1
                   ≡ subst U.Proc (cong suc (sym (+-suc sCB n)))
                       (X U.⋯ₚ assocSwapᵣ (suc sCB) 1)
        bodyProc =
            U.fusionₚ W (assocSwapᵣ 1 1 ↑* sCB) (assocSwapᵣ sCB 1)
          ■ substⱼ-⋯ (+-suc sCB (suc n)) (sym qq) X ρ₁ (assocSwapᵣ (suc sCB) 1)
              (λ x → ptwise x ■ cong (λ e → subst 𝔽 e (assocSwapᵣ (suc sCB) 1 (subst 𝔽 (+-suc sCB (suc n)) x)))
                                   (≡-irrelevant qq (sym (sym qq))))
          ■ cong (λ e → subst U.Proc e (X U.⋯ₚ assocSwapᵣ (suc sCB) 1))
              (≡-irrelevant (sym (sym qq)) qq)

-- subst over U.Proc commutes through a whole `Bφ B` block (channel-carrying).
subst-Bφ-c : ∀ {a a′} (e : a ≡ a′) (B : BindGroup) (cc : UChan a) (Y : U.Proc (syncs B + a)) →
             subst U.Proc e (Bφ B cc Y)
             ≡ Bφ B (subst UChan e cc) (subst U.Proc (cong (syncs B +_) e) Y)
subst-Bφ-c refl B cc Y = refl

mapᶜ-id : ∀ {a} (cc : UChan a) → mapᶜ (idₖ ⦃ Kᵣ ⦄) cc ≡ cc
mapᶜ-id (e1 , x , e2) = cong₂ _,_ (⋯-id e1 (λ _ → refl)) (cong₂ _,_ refl (⋯-id e2 (λ _ → refl)))

subst-UChan-triple : ∀ {p q} (e : p ≡ q) (a c : Tm p) (y : 𝔽 p) →
                     subst UChan e (a , y , c) ≡ (subst Tm e a , subst 𝔽 e y , subst Tm e c)
subst-UChan-triple refl a c y = refl

-- a `weaken` followed by `weaken* k` equals `weaken* (suc k)` (modulo +-suc), 𝔽.
wk-then-wk*-F : ∀ {p} k (y : 𝔽 p) →
                weaken* ⦃ Kᵣ ⦄ k (weaken ⦃ Kᵣ ⦄ y)
                ≡ subst 𝔽 (sym (+-suc k p)) (weaken* ⦃ Kᵣ ⦄ (suc k) y)
wk-then-wk*-F {p} k y = Fin.toℕ-injective
  ( toℕ-weaken*ᵣ k (weaken ⦃ Kᵣ ⦄ y)
  ■ Nat.+-suc k (Fin.toℕ y)
  ■ sym (toℕ-subst𝔽ᶜ (sym (+-suc k p)) (weaken* ⦃ Kᵣ ⦄ (suc k) y)
       ■ toℕ-weaken*ᵣ (suc k) y) )

-- Tm analogue.
wk-then-wk* : ∀ {p} k (t : Tm p) →
              (t ⋯ weaken ⦃ Kᵣ ⦄) ⋯ weaken* ⦃ Kᵣ ⦄ k
              ≡ subst Tm (sym (+-suc k p)) (t ⋯ weaken* ⦃ Kᵣ ⦄ (suc k))
wk-then-wk* {p} k t =
    fusion t (weaken ⦃ Kᵣ ⦄) (weaken* ⦃ Kᵣ ⦄ k)
  ■ ⋯-cong t wkc
  ■ subst-⋯-cod-local (sym (+-suc k p)) t (weaken* ⦃ Kᵣ ⦄ (suc k))
  where
    wkc : weaken ⦃ Kᵣ ⦄ ·ₖ weaken* ⦃ Kᵣ ⦄ k
          ≗ subst (λ z → p →ᵣ z) (sym (+-suc k p)) (weaken* ⦃ Kᵣ ⦄ (suc k))
    wkc y = wk-then-wk*-F k y ■ sym (subst-ren-cod (sym (+-suc k p)) (weaken* ⦃ Kᵣ ⦄ (suc k)) y)

-- channel transport for the transpose recursion.
cc-shift-gen : ∀ {p} k (a c : Tm p) (y : 𝔽 p) →
  subst UChan (sym (+-suc k p)) (mapᶜ (weaken* ⦃ Kᵣ ⦄ (suc k)) (a , y , c))
  ≡ mapᶜ (weaken* ⦃ Kᵣ ⦄ k) (mapᶜ (weaken ⦃ Kᵣ ⦄) (a , y , c))
cc-shift-gen {p} k a c y =
    subst-UChan-triple (sym (+-suc k p)) (a ⋯ weaken* ⦃ Kᵣ ⦄ (suc k))
      (c ⋯ weaken* ⦃ Kᵣ ⦄ (suc k)) (weaken* ⦃ Kᵣ ⦄ (suc k) y)
  ■ cong₂ _,_ (sym (wk-then-wk* k a))
      (cong₂ _,_ (sym (wk-then-wk*-F k y)) (sym (wk-then-wk* k c)))

-- Channel-carrying block transpose: swap two `Bφ` blocks past each other,
-- accumulating an `assocSwap` on the body.  The B₂-block channels are carried as
-- `mapᶜ (weaken* (syncs B₁)) cc₂` (weakened past B₁'s cells); after the swap they
-- descend to `cc₂` and B₁'s become `mapᶜ (weaken* (syncs B₂)) cc₁`.
Bφ-transposeΦ : (B₁ B₂ : BindGroup) {n : ℕ} (cc₁ cc₂ : UChan n)
                (X : U.Proc (syncs B₂ + (syncs B₁ + n))) →
   Bφ B₁ cc₁ (Bφ B₂ (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs B₁)) cc₂) X)
     U.≋ Bφ B₂ cc₂ (Bφ B₁ (mapᶜ (weaken* ⦃ Kᵣ ⦄ (syncs B₂)) cc₁)
                       (X U.⋯ₚ assocSwapᵣ (syncs B₂) (syncs B₁)))
Bφ-transposeΦ []            B₂ cc₁ cc₂ X =
  ≡→≋ (cong₂ (Bφ B₂) (mapᶜ-id cc₂) (sym (local-⋯ₚ-id X (R-base-b0 (syncs B₂)))))
Bφ-transposeΦ (b ∷ [])      B₂ cc₁ cc₂ X =
  ≡→≋ (cong₂ (Bφ B₂) (mapᶜ-id cc₂) (sym (local-⋯ₚ-id X (R-base-b0 (syncs B₂)))))
Bφ-transposeΦ (b ∷ c ∷ B₁₀) B₂ {n} (g1 , u , g2) (a , y , c₀) X =
     ≡→≋ step1
  ◅◅ U.φ-cong (Bφ-transposeΦ (c ∷ B₁₀) B₂ (` 0F , suc u , wk g2) (mapᶜ (weaken ⦃ Kᵣ ⦄) (a , y , c₀)) X₁)
  ◅◅ φ-past-Bφ-c B₂ ϕ[ b ] (` u) (a , y , c₀)
       (Bφ (c ∷ B₁₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (` 0F , suc u , wk g2)) (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA'))
  ◅◅ Bφ-cong-c B₂ (a , y , c₀)
       (U.φ-cong (≡→≋ (Bφ-⋯-c (c ∷ B₁₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (` 0F , suc u , wk g2))
                        (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') (assocSwapᵣ sB₂ 1))))
  ◅◅ Bφ-cong-c B₂ (a , y , c₀) (≡→≋ reconcile)
  where
    sA' = syncs (c ∷ B₁₀)
    sB₂ = syncs B₂
    pc = cong (sB₂ +_) (+-suc sA' n)
    X₁ : U.Proc (sB₂ + (sA' + suc n))
    X₁ = subst U.Proc (cong (sB₂ +_) (sym (+-suc sA' n))) X
    X₁≡ : X₁ ≡ subst U.Proc (sym pc) X
    X₁≡ = cong (λ e → subst U.Proc e X) (≡-irrelevant (cong (sB₂ +_) (sym (+-suc sA' n))) (sym pc))
    cc-shift : subst UChan (sym (+-suc sA' n)) (mapᶜ (weaken* ⦃ Kᵣ ⦄ (suc sA')) (a , y , c₀))
               ≡ mapᶜ (weaken* ⦃ Kᵣ ⦄ sA') (mapᶜ (weaken ⦃ Kᵣ ⦄) (a , y , c₀))
    cc-shift = cc-shift-gen sA' a c₀ y
    step1 : Bφ (b ∷ c ∷ B₁₀) (g1 , u , g2)
              (Bφ B₂ (mapᶜ (weaken* ⦃ Kᵣ ⦄ (suc sA')) (a , y , c₀)) X)
            ≡ U.φ ϕ[ b ] (` u)
                (Bφ (c ∷ B₁₀) (` 0F , suc u , wk g2)
                  (Bφ B₂ (mapᶜ (weaken* ⦃ Kᵣ ⦄ sA') (mapᶜ (weaken ⦃ Kᵣ ⦄) (a , y , c₀))) X₁))
    step1 =
        Bφ-cons b c B₁₀ g1 g2 u (Bφ B₂ (mapᶜ (weaken* ⦃ Kᵣ ⦄ (suc sA')) (a , y , c₀)) X)
      ■ cong (U.φ ϕ[ b ] (` u))
          (cong (Bφ (c ∷ B₁₀) (` 0F , suc u , wk g2))
            ( subst-Bφ-c (sym (+-suc sA' n)) B₂ (mapᶜ (weaken* ⦃ Kᵣ ⦄ (suc sA')) (a , y , c₀)) X
            ■ cong (λ cc → Bφ B₂ cc X₁) cc-shift))
    -- body reconcile (channel-free, ported verbatim from AcqH2.Bφ-transpose)
    ρ₂ : (sB₂ + (sA' + suc n)) →ᵣ sA' + (1 + (sB₂ + n))
    ρ₂ = assocSwapᵣ sB₂ sA' ·ₖ (assocSwapᵣ sB₂ 1 ↑* sA')
    ptwise : ∀ x → ρ₂ x ≡ subst 𝔽 (sym (+-suc sA' (sB₂ + n)))
                         (assocSwapᵣ sB₂ (suc sA') (subst 𝔽 pc x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R4 sB₂ sA' x
      ■ cong (λ w → Fin.toℕ (assocSwapᵣ sB₂ (suc sA') w)) (cast≡subst pc x)
      ■ sym (toℕ-subst𝔽ᶜ (sym (+-suc sA' (sB₂ + n)))
               (assocSwapᵣ sB₂ (suc sA') (subst 𝔽 pc x))) )
    bodyEq : (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')
             ≡ subst U.Proc (sym (+-suc sA' (sB₂ + n))) (X U.⋯ₚ assocSwapᵣ sB₂ (suc sA'))
    bodyEq =
        cong (λ z → (z U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')) X₁≡
      ■ U.fusionₚ (subst U.Proc (sym pc) X) (assocSwapᵣ sB₂ sA') (assocSwapᵣ sB₂ 1 ↑* sA')
      ■ substⱼ-⋯ pc (+-suc sA' (sB₂ + n)) X ρ₂ (assocSwapᵣ sB₂ (suc sA')) ptwise
    -- inner channel reconcile: the tail block channel descends to `0F`.
    Rc : (suc n) →ᵣ suc (sB₂ + n)
    Rc = weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ assocSwapᵣ sB₂ 1 {n}
    chanfin-gen : ∀ (x : 𝔽 n) → Rc (suc x) ≡ suc (weaken* ⦃ Kᵣ ⦄ sB₂ x)
    chanfin-gen x = Fin.toℕ-injective
      ( toℕ-assoc-ge sB₂ 1 (weaken* ⦃ Kᵣ ⦄ sB₂ (suc x)) ge
      ■ toℕ-weaken*ᵣ sB₂ (suc x)
      ■ Nat.+-suc sB₂ (Fin.toℕ x)
      ■ sym (cong suc (toℕ-weaken*ᵣ sB₂ x)) )
      where
        ge : sB₂ + 1 Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (suc x))
        ge = subst (sB₂ + 1 Nat.≤_) (sym (toℕ-weaken*ᵣ sB₂ (suc x)))
               (Nat.+-monoʳ-≤ sB₂ (Nat.s≤s Nat.z≤n))
    inner-cc : mapᶜ (assocSwapᵣ sB₂ 1) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (` 0F , suc u , wk g2))
               ≡ (` 0F , suc (weaken* ⦃ Kᵣ ⦄ sB₂ u) , wk (g2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    inner-cc =
        mapᶜ-fusion (weaken* ⦃ Kᵣ ⦄ sB₂) (assocSwapᵣ sB₂ 1) (` 0F , suc u , wk g2)
      ■ cong₂ _,_ (cong `_ e1fin) (cong₂ _,_ (chanfin-gen u) e2fin)
      where
        e1fin : Rc 0F ≡ 0F
        e1fin = Fin.toℕ-injective
          ( toℕ-assoc-mid sB₂ 1 {n} (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = n})) ge lt
          ■ cong (Nat._∸ sB₂) w0 ■ Nat.n∸n≡0 sB₂ )
          where
            w0 : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = n})) ≡ sB₂
            w0 = toℕ-weaken*ᵣ sB₂ (Fin.zero {n = n}) ■ Nat.+-identityʳ sB₂
            ge : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = n}))
            ge = subst (sB₂ Nat.≤_) (sym w0) Nat.≤-refl
            lt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = n})) Nat.< sB₂ + 1
            lt = subst (Nat._< sB₂ + 1) (sym w0) (Nat.≤-reflexive (sym (Nat.+-comm sB₂ 1)))
        e2fin : wk g2 ⋯ Rc ≡ wk (g2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
        e2fin =
            fusion g2 (weaken ⦃ Kᵣ ⦄) Rc
          ■ ⋯-cong g2 (λ x → chanfin-gen x)
          ■ sym (fusion g2 (weaken* ⦃ Kᵣ ⦄ sB₂) (weaken ⦃ Kᵣ ⦄))
    reconcile : U.φ ϕ[ b ] ((` u) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                  (Bφ (c ∷ B₁₀) (mapᶜ (assocSwapᵣ sB₂ 1) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (` 0F , suc u , wk g2)))
                    ((X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')))
                ≡ Bφ (b ∷ c ∷ B₁₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (g1 , u , g2))
                    (X U.⋯ₚ assocSwapᵣ sB₂ (suc sA'))
    reconcile =
        cong (U.φ ϕ[ b ] ((` u) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
          (cong₂ (Bφ (c ∷ B₁₀)) inner-cc bodyEq)
      ■ sym (Bφ-cons b c B₁₀ (g1 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (g2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
               (weaken* ⦃ Kᵣ ⦄ sB₂ u) (X U.⋯ₚ assocSwapᵣ sB₂ (suc sA')))

U-ν-swap : (σ : m →ₛ n) {B₁ B₂ : BindGroup} {P : T.Proc (sum B₁ + sum B₂ + m)} →
           U[ T.ν B₁ B₂ P ] σ U.≋ U[ T.ν B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂)) ] σ
U-ν-swap {m = m} {n = n} σ {B₁} {B₂} {P} =
     ≡→≋ (Uν-flatΦ σ B₁ B₂ P)
  ◅◅ U.ν-cong (Bφ-transposeΦ B₁ B₂ (K `unit , 0F , K `unit) (K `unit , 1F , K `unit) Lf)
  ◅◅ Eq*.return U.ν-swap′
  ◅◅ U.ν-cong (≡→≋ pushEq)
  ◅◅ ≡→≋ (sym (Uν-flatΦ σ B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂))))
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Lf : U.Proc (sB₂ + (sB₁ + (2 + n)))
    Lf = U[ P ] (leafσ σ B₁ B₂)
    INNER : U.Proc (sB₂ + (2 + n))
    INNER = Bφ B₁ (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (K `unit , 0F , K `unit)) (Lf U.⋯ₚ assocSwapᵣ sB₂ sB₁)
    -- swapᵣ 1 1 sends 1F ↦ 0F.
    swap11-1 : swapᵣ 1 1 {n} (Fin.suc (Fin.zero {n = n})) ≡ Fin.zero {n = suc n}
    swap11-1 = Fin.toℕ-injective
      (toℕ-swapᵣ-mid 1 1 (Fin.suc (Fin.zero {n = n})) (Nat.s≤s Nat.z≤n) (Nat.s≤s (Nat.s≤s Nat.z≤n)))
    ccB₂eq : mapᶜ (swapᵣ 1 1) (K `unit , 1F , K `unit) ≡ (K `unit , 0F , K `unit)
    ccB₂eq = cong (λ z → (K `unit , z , K `unit)) swap11-1
    -- swapᵣ 1 1 lifted past sB₂ sends (weaken* sB₂ 0F) ↦ (weaken* sB₂ 1F).
    chanUp : (swapᵣ 1 1 {n} ↑* sB₂) (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = suc n}))
             ≡ weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.suc (Fin.zero {n = n}))
    chanUp = Fin.toℕ-injective
      ( toℕ-↑*-ge (swapᵣ 1 1 {n}) sB₂ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = suc n})) q
      ■ cong (sB₂ +_) ( cong (λ z → Fin.toℕ (swapᵣ 1 1 z)) red≡0
                      ■ toℕ-swapᵣ-lt 1 1 (Fin.zero {n = suc n}) (Nat.s≤s Nat.z≤n) )
      ■ sym (toℕ-weaken*ᵣ sB₂ (Fin.suc (Fin.zero {n = n}))) )
      where
        q : sB₂ Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = suc n}))
        q = subst (sB₂ Nat.≤_) (sym (toℕ-weaken*ᵣ sB₂ (Fin.zero {n = suc n})))
              (Nat.≤-reflexive (sym (Nat.+-identityʳ sB₂)))
        red≡0 : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = suc n})) q ≡ Fin.zero {n = suc n}
        red≡0 = Fin.toℕ-injective
          (toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ sB₂ (Fin.zero {n = suc n})) q
           ■ cong (Nat._∸ sB₂) (toℕ-weaken*ᵣ sB₂ (Fin.zero {n = suc n}) ■ Nat.+-identityʳ sB₂)
           ■ Nat.n∸n≡0 sB₂)
    ccB₁eq : mapᶜ (swapᵣ 1 1 ↑* sB₂) (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (K `unit , 0F , K `unit))
             ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₂ 1F , K `unit)
    ccB₁eq = mapᶜ-fusion (weaken* ⦃ Kᵣ ⦄ sB₂) (swapᵣ 1 1 ↑* sB₂) (K `unit , 0F , K `unit)
           ■ cong (λ z → (K `unit , z , K `unit)) chanUp
    subEq : (leafσ σ B₁ B₂ ·ₖ assocSwapᵣ sB₂ sB₁) ·ₖ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)
            ≗ swapᵣ (sum B₁) (sum B₂) ·ₖ leafσ σ B₂ B₁
    subEq = subEq-gen σ B₁ B₂
    leafEq : (Lf U.⋯ₚ assocSwapᵣ sB₂ sB₁) U.⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)
             ≡ U[ P T.⋯ₚ swapᵣ (sum B₁) (sum B₂) ] (leafσ σ B₂ B₁)
    leafEq =
        cong (U._⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)) (local-U-σ⋯ P)
      ■ local-U-σ⋯ P
      ■ U-cong P subEq
      ■ sym (U-⋯ₚ P)
    innerEq : INNER U.⋯ₚ (swapᵣ 1 1 ↑* sB₂)
              ≡ Bφ B₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₂ 1F , K `unit)
                  (U[ P T.⋯ₚ swapᵣ (sum B₁) (sum B₂) ] (leafσ σ B₂ B₁))
    innerEq =
        Bφ-⋯-c B₁ (mapᶜ (weaken* ⦃ Kᵣ ⦄ sB₂) (K `unit , 0F , K `unit))
          (Lf U.⋯ₚ assocSwapᵣ sB₂ sB₁) (swapᵣ 1 1 ↑* sB₂)
      ■ cong₂ (Bφ B₁) ccB₁eq leafEq
    pushEq : (Bφ B₂ (K `unit , 1F , K `unit) INNER) U.⋯ₚ swapᵣ 1 1
             ≡ Bφ B₂ (K `unit , 0F , K `unit)
                 (Bφ B₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₂ 1F , K `unit)
                   (U[ P T.⋯ₚ swapᵣ (sum B₁) (sum B₂) ] (leafσ σ B₂ B₁)))
    pushEq =
        Bφ-⋯-c B₂ (K `unit , 1F , K `unit) INNER (swapᵣ 1 1)
      ■ cong (λ cc → Bφ B₂ cc (INNER U.⋯ₚ (swapᵣ 1 1 ↑* sB₂))) ccB₂eq
      ■ cong (Bφ B₂ (K `unit , 0F , K `unit)) innerEq

-- a toℕ-fixing renaming stays toℕ-fixing after lifting past k inert binders.
lift-fix-ge : ∀ {a a′} (ρ : a →ᵣ a′) (k T : ℕ) →
              (∀ y → T Nat.≤ Fin.toℕ y → Fin.toℕ (ρ y) ≡ Fin.toℕ y) →
              ∀ (z : 𝔽 (k + a)) → k + T Nat.≤ Fin.toℕ z →
              Fin.toℕ ((ρ ↑* k) z) ≡ Fin.toℕ z
lift-fix-ge ρ k T h z ge =
    toℕ-↑*-ge ρ k z q1
  ■ cong (k +_) (h (Fin.reduce≥ z q1) Tred)
  ■ cong (k +_) (toℕ-reduce≥ z q1)
  ■ Nat.m+[n∸m]≡n q1
  where
    q1 : k Nat.≤ Fin.toℕ z
    q1 = Nat.≤-trans (Nat.m≤m+n k T) ge
    Tred : T Nat.≤ Fin.toℕ (Fin.reduce≥ z q1)
    Tred = subst (T Nat.≤_) (sym (toℕ-reduce≥ z q1))
             (subst (Nat._≤ Fin.toℕ z Nat.∸ k) (Nat.m+n∸m≡n k T) (Nat.∸-monoˡ-≤ k ge))

-- the inner ρb = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 ↑* sB1) fixes toℕ on indices ≥ sB1+(2+2).
ρb-fix-ge : ∀ {n} (sB1 : ℕ) (y : 𝔽 (2 + (sB1 + (2 + n)))) → 2 + (sB1 + 2) Nat.≤ Fin.toℕ y →
            Fin.toℕ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) y) ≡ Fin.toℕ y
ρb-fix-ge {n} sB1 y ge =
    lift-fix-ge (assocSwapᵣ 2 2 {n}) sB1 (2 + 2)
      (λ w q → toℕ-assoc-ge 2 2 w q) (assocSwapᵣ 2 sB1 y) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB1 y) ≡ Fin.toℕ y
    aSwN = toℕ-assoc-ge 2 sB1 y (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 2)) ge)
    geInner : sB1 + (2 + 2) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 y)
    geInner = subst (sB1 + (2 + 2) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ y) reassoc ge)
      where reassoc : 2 + (sB1 + 2) ≡ sB1 + (2 + 2)
            reassoc = solve 1 (λ s → con 2 :+ (s :+ con 2) := s :+ (con 2 :+ con 2)) refl sB1
              where open +-*-Solver

-- toℕ-preservation of the body permutation ρacc on indices at/above its prefix.
ρacc-fix-ge : ∀ {n} (sB1 sB2 : ℕ) (x : 𝔽 (2 + (sB2 + (sB1 + (2 + n))))) →
              2 + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
              Fin.toℕ ((assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)) x)
              ≡ Fin.toℕ x
ρacc-fix-ge {n} sB1 sB2 x ge =
    lift-fix-ge (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) sB2 (2 + (sB1 + 2))
      (λ w q → ρb-fix-ge sB1 w q) (assocSwapᵣ 2 sB2 x) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB2 x) ≡ Fin.toℕ x
    aSwN = toℕ-assoc-ge 2 sB2 x (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB2 (sB1 + 2))) ge)
    geInner : sB2 + (2 + (sB1 + 2)) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 x)
    geInner = subst (sB2 + (2 + (sB1 + 2)) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ x) reassoc ge)
      where reassoc : 2 + (sB2 + (sB1 + 2)) ≡ sB2 + (2 + (sB1 + 2))
            reassoc = solve 2 (λ u v → con 2 :+ (u :+ (v :+ con 2))
                               := u :+ (con 2 :+ (v :+ con 2))) refl sB2 sB1
              where open +-*-Solver

-- the inner Lf₃ = (assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2 fixes toℕ ≥ sA2+(sA1+2).
ωL3-fix-ge : ∀ {p} (sA1 sA2 : ℕ) (y : 𝔽 (sA2 + (sA1 + (2 + p)))) → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ y →
             Fin.toℕ (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2 {sA1 + p}) y) ≡ Fin.toℕ y
ωL3-fix-ge {p} sA1 sA2 y ge =
    toℕ-assoc-ge sA2 2 ((assocSwapᵣ sA1 2 {p} ↑* sA2) y)
      (subst (sA2 + 2 Nat.≤_) (sym m1N) (Nat.≤-trans le1 ge))
  ■ m1N
  where
    m1N : Fin.toℕ ((assocSwapᵣ sA1 2 {p} ↑* sA2) y) ≡ Fin.toℕ y
    m1N = toℕ-assoc↑*-fix-ge sA2 sA1 2 y ge
    le1 : sA2 + 2 Nat.≤ sA2 + (sA1 + 2)
    le1 = Nat.+-monoʳ-≤ sA2 (Nat.m≤n+m 2 sA1)

-- the body permutation ρω fixes toℕ on indices ≥ sA2+(sA1+(sB1+2)).
ρω-fix-ge : ∀ {p} (sA1 sA2 sB1 : ℕ) (x : 𝔽 (sA2 + (sA1 + (sB1 + (2 + p))))) →
            sA2 + (sA1 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
            Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                      ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                          (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x)
            ≡ Fin.toℕ x
ρω-fix-ge {p} sA1 sA2 sB1 x ge = l3N ■ z2N ■ z1N
  where
    z1 = (assocSwapᵣ sA1 sB1 ↑* sA2) x
    z1N : Fin.toℕ z1 ≡ Fin.toℕ x
    z1N = toℕ-assoc↑*-fix-ge sA2 sA1 sB1 x
            (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 2))) ge)
    z2 = assocSwapᵣ sA2 sB1 z1
    z2N : Fin.toℕ z2 ≡ Fin.toℕ z1
    z2N = toℕ-assoc-ge sA2 sB1 z1
            (subst (sA2 + sB1 Nat.≤_) (sym z1N)
              (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB1 2) (Nat.m≤n+m (sB1 + 2) sA1))) ge))
    l3N : Fin.toℕ ((((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2) ≡ Fin.toℕ z2
    l3N = lift-fix-ge ((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 (sA2 + (sA1 + 2))
            (λ w q → ωL3-fix-ge sA1 sA2 w q) z2 geL3
      where
        geL3 : sB1 + (sA2 + (sA1 + 2)) Nat.≤ Fin.toℕ z2
        geL3 = subst (sB1 + (sA2 + (sA1 + 2)) Nat.≤_) (sym (z2N ■ z1N))
                 (subst (Nat._≤ Fin.toℕ x) reassoc ge)
          where reassoc : sA2 + (sA1 + (sB1 + 2)) ≡ sB1 + (sA2 + (sA1 + 2))
                reassoc = solve 3 (λ u v w → u :+ (v :+ (w :+ con 2)) := w :+ (u :+ (v :+ con 2)))
                            refl sA2 sA1 sB1
                  where open +-*-Solver

------------------------------------------------------------------------
-- Typing crux: a msg/brn-headed borrow is never the terminal ret, so the
-- head count is >= 2, i.e. b1 >= 1 (dually b2 >= 1).
------------------------------------------------------------------------

msg-not-Bounded : ∀ {p TT} → ¬ Bounded (msg {0} p TT)
msg-not-Bounded ()

fn-send-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `send ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ∃[ Tᵐ ] (Tᵐ ⊗¹ ⟨ msg ‼ Tᵐ ⟩) ≃ Tᵈ
fn-send-dom (T-Const (`send {T = Tᵐ} _)) = Tᵐ , ≃-refl
fn-send-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let Tᵐ , eq = fn-send-dom d in Tᵐ , ≃-trans eq dom≃
fn-send-dom (T-Weaken _ d) = fn-send-dom d

fn-recv-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `recv ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ∃[ Tᵐ ] ⟨ msg ⁇ Tᵐ ⟩ ≃ Tᵈ
fn-recv-dom (T-Const (`recv {T = Tᵐ} _)) = Tᵐ , ≃-refl
fn-recv-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let Tᵐ , eq = fn-recv-dom d in Tᵐ , ≃-trans eq dom≃
fn-recv-dom (T-Weaken _ d) = fn-recv-dom d

pair1-handle : ∀ {N} {Γ : Ctx N} {β : Struct N} {ee}{x : 𝔽 N}{T ϵ}
  → Γ ; β ⊢ ((` x) ⊗ ee) ∶ T ∣ ϵ
  → ∃[ Tx ] ∃[ d ] ∃[ Te ] (T ≃ (Tx ⊗⟨ d ⟩ Te)) × (lookup Γ x ≃ Tx)
pair1-handle (T-Pair {T = Tx} {U = Te} p/s _ ⊢x ⊢e) =
  Tx , biasedDir p/s , Te , ≃-refl , arg-type ⊢x
pair1-handle (T-Conv T≃ _ d) =
  let Tx , dd , Te , Teq , Heq = pair1-handle d in
  Tx , dd , Te , ≃-trans (≃-sym T≃) Teq , Heq
pair1-handle (T-Weaken _ d) = pair1-handle d

⊗≃₁ : ∀ {Ta Ua Tb Ub d} → (Ta ⊗⟨ d ⟩ Ua) ≃ (Tb ⊗⟨ d ⟩ Ub) → Ta ≃ Tb
⊗≃₁ (eq ⊗ _) = eq

⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
⟨⟩≃ ⟨ eq ⟩ = eq

-- Invert Bounded of a sequencing whose right component Skips: the left is Bounded.
bounded-seqL : ∀ {sa sb : 𝕊 0} → Bounded (sa ; sb) → Skips sb → Bounded sa
bounded-seqL (b ;₁ _) _   = b
bounded-seqL (-;₂ b)  Sk  = ⊥-elim (skips⊥bounded Sk b)

bd-end : ∀ {n}{s : 𝕊 n}{p} → Bounded (s ; end p)
bd-end = -;₂ end

open T using (last; cons-ret/acq; cons-acq; nil; cons)

-- Off-by-one for the new (chain-aware) BindCtx: a Bounded session whose bind group
-- has head (suc b₁) and count 1 (b₁=0) forces the head channel 0F to a Bounded session.
head-bounded : ∀ {s b₁}{B₁ : BindGroup}{Γ₁ : Ctx (sum (suc b₁ ∷ B₁))}
  → Bounded s
  → BindCtx s (suc b₁ ∷ B₁) Γ₁ → b₁ ≡ 0
  → ∃[ s'' ] (lookup Γ₁ 0F ≡ ⟨ s'' ⟩) × Bounded s''
head-bounded Bs (last (cons s₁ˡ s₂ˡ ¬sk s≃ˡ (nil Skˡ))) refl =
  s₁ˡ , refl
  , bounded-seqL (≃-bounded (≃-sym s≃ˡ) Bs) Skˡ
head-bounded Bs (cons-ret/acq sh {s₂ = st} s≃ ¬sk₂
                  (cons s₁'' s₂'' ¬sk s≃' (nil Sk)) rest ah) refl =
  s₁'' , refl
  , bounded-seqL (≃-bounded (≃-sym s≃') (-;₂ ret)) Sk

-- recv handle (bare variable y): Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩.
recv-handle-≃msg : ∀ {N} {Δ : Ctx N}{α β}{y : 𝔽 N}{a Targ U ϵ₁ ϵ₂}
  → Δ ; α ⊢ K `recv ∶ Targ ⟨ a ⟩→ U ∣ ϵ₁
  → Δ ; β ⊢ (` y) ∶ Targ ∣ ϵ₂
  → ∃[ Tᵐ ] (lookup Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩)
recv-handle-≃msg {y = y} ⊢fn ⊢arg
  with fn-recv-dom ⊢fn
... | Tᵐ , dom≃ = Tᵐ , ≃-trans (arg-type ⊢arg) (≃-sym dom≃)

recv-handle-≃msg-app : ∀ {N} {Δ : Ctx N}{β}{y : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `recv ·¹ (` y) ∶ U ∣ ϵ
  → ∃[ Tᵐ ] (lookup Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩)
recv-handle-≃msg-app (T-AppUnr   _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-AppLin   _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-Conv _ _ d) = recv-handle-≃msg-app d
recv-handle-≃msg-app (T-Weaken _ d) = recv-handle-≃msg-app d

open T using (_;_⊢ₚ_)

-- Symmetric crux for the recv side: b₂ ≥ 1.
com-head≥2 : ∀ {m} {Γ : Ctx m} {γ}{b₁ b₂}{B₁ B₂ : BindGroup}{e}{E₁ E₂}{P}(V : Value e) →
    Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((T.⟪ E₁ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `send ·¹ ((e ⋯ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) ⊗ (` 0F)) ]* ⟫
        T.∥ T.⟪ E₂ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        T.∥ (P T.⋯ₚ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)))
      → ∃[ b₂' ] (b₂ ≡ suc b₂')
com-head≥2 {b₂ = suc b₂'} V ⊢P = b₂' , refl
com-head≥2 {m = m} {Γ = Γ} {b₁ = b₁} {b₂ = zero} {B₁ = B₁} {B₂ = B₂} {E₂ = E₂} V ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢sr , _
  with inv-∥ ⊢sr
... | _ , _ , _ , _ , ⊢recvT
  with strengthen-frame (E₂ ⋯ᶠ* wkₚ (b₁ + sum B₁) (zero + sum B₂)) (inv-⟪⟫ ⊢recvT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-bounded bd-end C′ refl
... | s'' , Δ0≡ , Bs''
  with recv-handle-≃msg-app ⊢plug
... | Tᵐ , Δr≃msg = ⊥-elim (msg-not-Bounded (≃-bounded (⟨⟩≃ (≃-trans (≃-reflexive (sym Δr≡)) Δr≃msg)) Bs''))
  where
    Δr≡ : lookup ((Γ₁ ⸴* Γ₂) ⸴* Γ)
            (wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ≡ ⟨ s'' ⟩
    Δr≡ =
        V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum (suc b₁ ∷ B₁) ↑ʳ 0F)
      ■ V.lookup-++ʳ Γ₁ Γ₂ 0F
      ■ Δ0≡

------------------------------------------------------------------------
-- Send-side crux: b₁ ≥ 1.  The send handle 0F is msg-typed (non-ret), so when
-- b₁ = 0 the head chain forces a Bounded session at 0F — contradiction.
------------------------------------------------------------------------

⊗≃₂ : ∀ {Ta Ua Tb Ub d} → (Ta ⊗⟨ d ⟩ Ua) ≃ (Tb ⊗⟨ d ⟩ Ub) → Ua ≃ Ub
⊗≃₂ (_ ⊗ eq) = eq

pair₂-handle : ∀ {N} {Γ : Ctx N} {β : Struct N} {ee}{x : 𝔽 N}{T ϵ}
  → Γ ; β ⊢ (ee ⊗ (` x)) ∶ T ∣ ϵ
  → ∃[ Te ] ∃[ d ] ∃[ Tx ] (T ≃ (Te ⊗⟨ d ⟩ Tx)) × (lookup Γ x ≃ Tx)
pair₂-handle (T-Pair {T = Te} {U = Tx} p/s _ ⊢e ⊢x) =
  Te , biasedDir p/s , Tx , ≃-refl , arg-type ⊢x
pair₂-handle (T-Conv T≃ _ d) =
  let Te , dd , Tx , Teq , Heq = pair₂-handle d in
  Te , dd , Tx , ≃-trans (≃-sym T≃) Teq , Heq
pair₂-handle (T-Weaken _ d) = pair₂-handle d

-- send handle (second component of the message pair): Δ x ≃ ⟨ msg ‼ Tᵐ ⟩.
send-handle-≃msg : ∀ {N} {Δ : Ctx N}{α β}{ee}{x : 𝔽 N}{a Targ U ϵ₁ ϵ₂}
  → Δ ; α ⊢ K `send ∶ Targ ⟨ a ⟩→ U ∣ ϵ₁
  → Δ ; β ⊢ (ee ⊗ (` x)) ∶ Targ ∣ ϵ₂
  → ∃[ Tᵐ ] (lookup Δ x ≃ ⟨ msg ‼ Tᵐ ⟩)
send-handle-≃msg ⊢fn ⊢arg
  with fn-send-dom ⊢fn | pair₂-handle ⊢arg
... | Tᵐ , dom≃ | Te , d , Tx , T≃ , Hx≃
  with ≃-trans (≃-sym T≃) (≃-sym dom≃)
... | (_ ⊗ eq) = Tᵐ , ≃-trans Hx≃ eq

send-handle-≃msg-app : ∀ {N} {Δ : Ctx N}{β}{ee}{x : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `send ·¹ (ee ⊗ (` x)) ∶ U ∣ ϵ
  → ∃[ Tᵐ ] (lookup Δ x ≃ ⟨ msg ‼ Tᵐ ⟩)
send-handle-≃msg-app (T-AppUnr   _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-AppLin   _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-Conv _ _ d) = send-handle-≃msg-app d
send-handle-≃msg-app (T-Weaken _ d) = send-handle-≃msg-app d

msg‼-not-Bounded : ∀ {p TT} → ¬ Bounded (msg {0} p TT)
msg‼-not-Bounded ()

com-head≥1 : ∀ {m} {Γ : Ctx m} {γ}{b₁ b₂}{B₁ B₂ : BindGroup}{e}{E₁ E₂}{P}(V : Value e) →
    Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((T.⟪ E₁ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `send ·¹ ((e ⋯ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) ⊗ (` 0F)) ]* ⟫
        T.∥ T.⟪ E₂ ⋯ᶠ* wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `recv ·¹ (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        T.∥ (P T.⋯ₚ wkₚ (b₁ + sum B₁) (b₂ + sum B₂)))
      → ∃[ b₁' ] (b₁ ≡ suc b₁')
com-head≥1 {b₁ = suc b₁'} V ⊢P = b₁' , refl
com-head≥1 {m = m} {Γ = Γ} {b₁ = zero} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} V ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , s , p , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢sr , _
  with inv-∥ ⊢sr
... | _ , _ , _ , ⊢sendT , _
  with strengthen-frame (E₁ ⋯ᶠ* wkₚ (zero + sum B₁) (b₂ + sum B₂)) (inv-⟪⟫ ⊢sendT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-bounded bd-end C refl
... | s'' , Δ0≡ , Bs''
  with send-handle-≃msg-app ⊢plug
... | Tᵐ , Δs≃msg = ⊥-elim (msg‼-not-Bounded (≃-bounded (⟨⟩≃ (≃-trans (≃-reflexive (sym Δs≡)) Δs≃msg)) Bs''))
  where
    Δs≡ : lookup ((Γ₁ ⸴* Γ₂) ⸴* Γ) 0F ≡ ⟨ s'' ⟩
    Δs≡ =
        V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ 0F
      ■ V.lookup-++ˡ Γ₁ Γ₂ 0F
      ■ Δ0≡

------------------------------------------------------------------------
-- Ported helpers (verbatim from Theorems/Choice) for the U-com assembly.
------------------------------------------------------------------------

infix 4 _UR─→ₚ*_
_UR─→ₚ*_ : {n : ℕ} → U.Proc n → U.Proc n → Set
_UR─→ₚ*_ = Star UR._─→ₚ_

wrapNE : {n : ℕ} {w x y′ z : U.Proc n} → w U.≋ x →
         {s₀tgt : U.Proc n} → x UR.─→ₚ s₀tgt → s₀tgt UR─→ₚ* y′ → y′ U.≋ z →
         w UR─→ₚ* z
wrapNE front s₀ ε        back = UR.RU-Struct front s₀ back ◅ ε
wrapNE front s₀ (t ◅ ts) back = UR.RU-Struct front s₀ ε ◅ wrapNE ε t ts back

≋-wrap-⊎ : {n : ℕ} {w x y z : U.Proc n} → w U.≋ x → x UR─→ₚ* y → y U.≋ z →
           (w UR─→ₚ* z) ⊎ (w U.≋ z)
≋-wrap-⊎ front ε        back = inj₂ (front ◅◅ back)
≋-wrap-⊎ front (s ◅ ss) back = inj₁ (wrapNE front s ss back)

Bφ-lift-step : (B : BindGroup) {n : ℕ} {cc : UChan n} {P Q : U.Proc (syncs B + n)} →
               P UR.─→ₚ Q → Bφ B cc P UR.─→ₚ Bφ B cc Q
Bφ-lift-step []            r = r
Bφ-lift-step (b ∷ [])      r = r
Bφ-lift-step (b ∷ c ∷ B) {n} {e1 , x , e2} {P} {Q} r =
  subst₂ UR._─→ₚ_ (sym (Bφ-cons b c B e1 e2 x P)) (sym (Bφ-cons b c B e1 e2 x Q))
    (UR.RU-Sync (Bφ-lift-step (c ∷ B) {cc = ` 0F , suc x , wk e2}
                  (subst-→ₚ (sym (+-suc (syncs (c ∷ B)) n)) r)))
  where
    subst-→ₚ : ∀ {a d} (eq : a ≡ d) {P Q : U.Proc a} → P UR.─→ₚ Q →
               subst U.Proc eq P UR.─→ₚ subst U.Proc eq Q
    subst-→ₚ refl r = r

VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ j → Ub-V (b + 0) e1 x e2 Ve1 Ve2 j
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ j → value-⋯ (Ub-V b (wk e1) (suc x) (` 0F) (Ve1 ⋯ᵛ weakenᵣ) V-` j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

canonₛ-head-triple : ∀ {N} (b : ℕ) (B : BindGroup) (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs (suc b ∷ B) + N) ] Σ[ c ∈ Tm (syncs (suc b ∷ B) + N) ]
  Σ[ j ∈ 𝔽 (syncs (suc b ∷ B) + N) ]
    (canonₛ (suc b ∷ B) (e1 , x , e2) 0F ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (suc b ∷ B) + Fin.toℕ x)
canonₛ-head-triple zero    []  e1 e2 x =
  e1 , e2 , x , refl , refl
canonₛ-head-triple (suc b) []  e1 e2 x =
  e1 , * , x , refl , refl
canonₛ-head-triple {N} zero (c′ ∷ B) e1 e2 x =
  ( subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq
  , junceq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc zero ∷ c′ ∷ B) (e1 , x , e2) 0F
             ≡ (subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)))
             ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl
canonₛ-head-triple {N} (suc b) (c′ ∷ B) e1 e2 x =
  ( subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq
  , junceq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc (suc b) ∷ c′ ∷ B) (e1 , x , e2) 0F
             ≡ (subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)))
             ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl

assocPush-junc : ∀ (sA sB d : ℕ) {nn} (j : 𝔽 (sB + (sA + (2 + nn)))) →
                 Fin.toℕ j ≡ sB + (sA + d) → d Nat.< 2 →
                 Fin.toℕ ((assocSwapᵣ sB 2 {sA + nn}) ((assocSwapᵣ sA 2 {nn} ↑* sB) j)) ≡ d
assocPush-junc sA sB d {nn} j jeq d<2 =
    toℕ-assoc-mid sB 2 {sA + nn} ((assocSwapᵣ sA 2 {nn} ↑* sB) j) geB ltB
  ■ aritheq
  where
    q1 : sB Nat.≤ Fin.toℕ j
    q1 = subst (sB Nat.≤_) (sym jeq) (Nat.m≤m+n sB (sA + d))
    redeq : Fin.toℕ (Fin.reduce≥ j q1) ≡ sA + d
    redeq = toℕ-reduce≥ j q1 ■ cong (Nat._∸ sB) jeq ■ Nat.m+n∸m≡n sB (sA + d)
    geA : sA Nat.≤ Fin.toℕ (Fin.reduce≥ j q1)
    geA = subst (sA Nat.≤_) (sym redeq) (Nat.m≤m+n sA d)
    ltA : Fin.toℕ (Fin.reduce≥ j q1) Nat.< sA + 2
    ltA = subst (Nat._< sA + 2) (sym redeq) (Nat.+-monoʳ-< sA d<2)
    midA : Fin.toℕ (assocSwapᵣ sA 2 {nn} (Fin.reduce≥ j q1)) ≡ d
    midA = toℕ-assoc-mid sA 2 {nn} (Fin.reduce≥ j q1) geA ltA
         ■ cong (Nat._∸ sA) redeq ■ Nat.m+n∸m≡n sA d
    step1 : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) ≡ sB + d
    step1 = toℕ-↑*-ge (assocSwapᵣ sA 2 {nn}) sB j q1 ■ cong (sB +_) midA
    geB : sB Nat.≤ Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j)
    geB = subst (sB Nat.≤_) (sym step1) (Nat.m≤m+n sB d)
    ltB : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) Nat.< sB + 2
    ltB = subst (Nat._< sB + 2) (sym step1) (Nat.+-monoʳ-< sB d<2)
    aritheq : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) Nat.∸ sB ≡ d
    aritheq = cong (Nat._∸ sB) step1 ■ Nat.m+n∸m≡n sB d

frame-plug*ᵣ : (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

