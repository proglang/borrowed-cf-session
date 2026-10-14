module BorrowedCF.Simulation.Support.NuFloat where

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
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; []φ; _◂_; plugΦ)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 public

------------------------------------------------------------------------
-- Pull a `ν` binder OUT of a channel-carrying `Bφ B` block.  This is the
-- channel-carrying port of the (channel-free) `AcqH2.Bφ-past-ν`.  The engine
-- (`Bφ`, `Bφ-cons`, `Bφ-⋯-c`, `substⱼ-⋯`, …) is inherited from ComHelpers2.
------------------------------------------------------------------------

-- subst over U.Proc commutes through a ν-binder.
subst-ν : ∀ {a b} (e : a ≡ b) (Y : U.Proc (2 + a)) →
          subst U.Proc e (U.ν Y) ≡ U.ν (subst U.Proc (cong (2 +_) e) Y)
subst-ν refl Y = refl

-- Single-cell move: float a `ν` out past a single φ cell.  This is the REVERSE
-- of the gated `νφ-comm′`, presented for a channel already in variable form.
νφ-out : ∀ {n} (f : U.Flag) (c : Tm n) (Q : U.Proc (2 + suc n)) →
   U.φ f c (U.ν Q)
     U.≋ U.ν (U.φ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) (Q U.⋯ₚ assocSwapᵣ 2 1))
νφ-out {n} f c Q =
  Eq*.symmetric _
    (subst (λ z → U.ν (U.φ f (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) (Q U.⋯ₚ assocSwapᵣ 2 1))
                    U.≋ U.φ f c (U.ν z))
           inner≡
           (Eq*.return (U.νφ-comm′ {x = f} {c = c} {P = Q U.⋯ₚ assocSwapᵣ 2 1})))
  where
    inner≡ : (Q U.⋯ₚ assocSwapᵣ 2 1) U.⋯ₚ assocSwapᵣ 1 2 ≡ Q
    inner≡ = U.fusionₚ Q (assocSwapᵣ 2 1) (assocSwapᵣ 1 2)
           ■ local-⋯ₚ-id Q (assocSwap-invol 2 1)

-- Channel reconcile: the tail block channel descends past the accumulated swap.
inner-cc-gen : ∀ {p} (k : ℕ) (u : 𝔽 p) (g2 : Tm p) →
  mapᶜ (assocSwapᵣ k 1) (mapᶜ (weaken* ⦃ Kᵣ ⦄ k) (` 0F , suc u , wk g2))
  ≡ (` 0F , suc (weaken* ⦃ Kᵣ ⦄ k u) , wk (g2 ⋯ weaken* ⦃ Kᵣ ⦄ k))
inner-cc-gen {p} k u g2 =
    mapᶜ-fusion (weaken* ⦃ Kᵣ ⦄ k) (assocSwapᵣ k 1) (` 0F , suc u , wk g2)
  ■ cong₂ _,_ (cong `_ e1fin) (cong₂ _,_ (chanfin-gen u) e2fin)
  where
    Rc : (suc p) →ᵣ suc (k + p)
    Rc = weaken* ⦃ Kᵣ ⦄ k ·ₖ assocSwapᵣ k 1 {p}
    chanfin-gen : ∀ (x : 𝔽 p) → Rc (suc x) ≡ suc (weaken* ⦃ Kᵣ ⦄ k x)
    chanfin-gen x = Fin.toℕ-injective
      ( toℕ-assoc-ge k 1 (weaken* ⦃ Kᵣ ⦄ k (suc x)) ge
      ■ toℕ-weaken*ᵣ k (suc x)
      ■ Nat.+-suc k (Fin.toℕ x)
      ■ sym (cong suc (toℕ-weaken*ᵣ k x)) )
      where
        ge : k + 1 Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ k (suc x))
        ge = subst (k + 1 Nat.≤_) (sym (toℕ-weaken*ᵣ k (suc x)))
               (Nat.+-monoʳ-≤ k (Nat.s≤s Nat.z≤n))
    e1fin : Rc 0F ≡ 0F
    e1fin = Fin.toℕ-injective
      ( toℕ-assoc-mid k 1 {p} (weaken* ⦃ Kᵣ ⦄ k (Fin.zero {n = p})) ge lt
      ■ cong (Nat._∸ k) w0 ■ Nat.n∸n≡0 k )
      where
        w0 : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ k (Fin.zero {n = p})) ≡ k
        w0 = toℕ-weaken*ᵣ k (Fin.zero {n = p}) ■ Nat.+-identityʳ k
        ge : k Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ k (Fin.zero {n = p}))
        ge = subst (k Nat.≤_) (sym w0) Nat.≤-refl
        lt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ k (Fin.zero {n = p})) Nat.< k + 1
        lt = subst (Nat._< k + 1) (sym w0) (Nat.≤-reflexive (sym (Nat.+-comm k 1)))
    e2fin : wk g2 ⋯ Rc ≡ wk (g2 ⋯ weaken* ⦃ Kᵣ ⦄ k)
    e2fin =
        fusion g2 (weaken ⦃ Kᵣ ⦄) Rc
      ■ ⋯-cong g2 (λ x → chanfin-gen x)
      ■ sym (fusion g2 (weaken* ⦃ Kᵣ ⦄ k) (weaken ⦃ Kᵣ ⦄))

-- Body reconcile: two accumulated swaps collapse to a single `assocSwapᵣ k (suc a)`.
transpose-body-gen : ∀ {p} (k a : ℕ) (Z : U.Proc (k + (suc a + p))) →
   ((subst U.Proc (cong (k +_) (sym (+-suc a p))) Z) U.⋯ₚ assocSwapᵣ k a)
     U.⋯ₚ (assocSwapᵣ k 1 ↑* a)
   ≡ subst U.Proc (sym (+-suc a (k + p))) (Z U.⋯ₚ assocSwapᵣ k (suc a))
transpose-body-gen {p} k a Z =
    cong (λ z → (z U.⋯ₚ assocSwapᵣ k a) U.⋯ₚ (assocSwapᵣ k 1 ↑* a)) Z₁≡
  ■ U.fusionₚ (subst U.Proc (sym pc) Z) (assocSwapᵣ k a) (assocSwapᵣ k 1 ↑* a)
  ■ substⱼ-⋯ pc (+-suc a (k + p)) Z ρ₂ (assocSwapᵣ k (suc a)) ptwise
  where
    pc : k + (a + suc p) ≡ k + (suc a + p)
    pc = cong (k +_) (+-suc a p)
    Z₁≡ : subst U.Proc (cong (k +_) (sym (+-suc a p))) Z ≡ subst U.Proc (sym pc) Z
    Z₁≡ = cong (λ e → subst U.Proc e Z)
            (≡-irrelevant (cong (k +_) (sym (+-suc a p))) (sym pc))
    ρ₂ : (k + (a + suc p)) →ᵣ a + (1 + (k + p))
    ρ₂ = assocSwapᵣ k a ·ₖ (assocSwapᵣ k 1 ↑* a)
    ptwise : ∀ x → ρ₂ x ≡ subst 𝔽 (sym (+-suc a (k + p)))
                         (assocSwapᵣ k (suc a) (subst 𝔽 pc x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R4 k a x
      ■ cong (λ w → Fin.toℕ (assocSwapᵣ k (suc a) w)) (cast≡subst pc x)
      ■ sym (toℕ-subst𝔽ᶜ (sym (+-suc a (k + p)))
               (assocSwapᵣ k (suc a) (subst 𝔽 pc x))) )

-- Pull a `ν` binder OUT of a channel-carrying `Bφ B` block.
Bφ-past-ν-c : ∀ {n} (B : BindGroup) (cc : UChan n) (Y : U.Proc (2 + (syncs B + n))) →
   Bφ B cc (U.ν Y)
     U.≋ U.ν (Bφ B (mapᶜ (weaken* ⦃ Kᵣ ⦄ 2) cc) (Y U.⋯ₚ assocSwapᵣ 2 (syncs B)))
Bφ-past-ν-c []       cc Y = ≡→≋ (cong U.ν (sym (local-⋯ₚ-id Y (R-base-b0 2))))
Bφ-past-ν-c (b ∷ []) cc Y = ≡→≋ (cong U.ν (sym (local-⋯ₚ-id Y (R-base-b0 2))))
Bφ-past-ν-c {n} (b ∷ c ∷ B₀) (g1 , x , g2) Y =
     ≡→≋ step1
  ◅◅ U.φ-cong (Bφ-past-ν-c {suc n} (c ∷ B₀) (` 0F , suc x , wk g2) Y′)
  ◅◅ νφ-out ϕ[ b ] (` x) Q
  ◅◅ U.ν-cong (≡→≋ reconcile)
  where
    sCB = syncs (c ∷ B₀)
    Y′ : U.Proc (2 + (sCB + suc n))
    Y′ = subst U.Proc (cong (2 +_) (sym (+-suc sCB n))) Y
    Q : U.Proc (2 + suc n)
    Q = Bφ (c ∷ B₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ 2) (` 0F , suc x , wk g2))
          (Y′ U.⋯ₚ assocSwapᵣ 2 sCB)
    step1 : Bφ (b ∷ c ∷ B₀) (g1 , x , g2) (U.ν Y)
            ≡ U.φ ϕ[ b ] (` x) (Bφ (c ∷ B₀) (` 0F , suc x , wk g2) (U.ν Y′))
    step1 =
        Bφ-cons b c B₀ g1 g2 x (U.ν Y)
      ■ cong (U.φ ϕ[ b ] (` x))
          (cong (Bφ (c ∷ B₀) (` 0F , suc x , wk g2))
            (subst-ν (sym (+-suc sCB n)) Y))
    chanA : mapᶜ (assocSwapᵣ 2 1) (mapᶜ (weaken* ⦃ Kᵣ ⦄ 2) (` 0F , suc x , wk g2))
            ≡ (` 0F , suc (weaken* ⦃ Kᵣ ⦄ 2 x) , wk (g2 ⋯ weaken* ⦃ Kᵣ ⦄ 2))
    chanA = inner-cc-gen 2 x g2
    bodyB : (Y′ U.⋯ₚ assocSwapᵣ 2 sCB) U.⋯ₚ (assocSwapᵣ 2 1 ↑* sCB)
            ≡ subst U.Proc (sym (+-suc sCB (2 + n))) (Y U.⋯ₚ assocSwapᵣ 2 (suc sCB))
    bodyB = transpose-body-gen 2 sCB Y
    reconcile : U.φ ϕ[ b ] ((` x) ⋯ weaken* ⦃ Kᵣ ⦄ 2) (Q U.⋯ₚ assocSwapᵣ 2 1)
                ≡ Bφ (b ∷ c ∷ B₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ 2) (g1 , x , g2))
                    (Y U.⋯ₚ assocSwapᵣ 2 (suc sCB))
    reconcile =
        cong (U.φ ϕ[ b ] ((` x) ⋯ weaken* ⦃ Kᵣ ⦄ 2))
          ( Bφ-⋯-c (c ∷ B₀) (mapᶜ (weaken* ⦃ Kᵣ ⦄ 2) (` 0F , suc x , wk g2))
              (Y′ U.⋯ₚ assocSwapᵣ 2 sCB) (assocSwapᵣ 2 1)
          ■ cong₂ (Bφ (c ∷ B₀)) chanA bodyB )
      ■ sym (Bφ-cons b c B₀ (g1 ⋯ weaken* ⦃ Kᵣ ⦄ 2) (g2 ⋯ weaken* ⦃ Kᵣ ⦄ 2)
               (weaken* ⦃ Kᵣ ⦄ 2 x) (Y U.⋯ₚ assocSwapᵣ 2 (suc sCB)))
