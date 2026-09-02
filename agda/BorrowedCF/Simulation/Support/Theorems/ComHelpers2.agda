module BorrowedCF.Simulation.Support.Theorems.ComHelpers2 where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.Support.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
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

-- The remaining ν-reordering lemmas reduce — via the flattening Uν-flat above —
-- to the φ-binder BLOCK-TRANSPOSE engine plus a leaf-substitution reconcile:
--
--   Bφ B₁ (Bφ B₂ X) ≋ Bφ B₂ (Bφ B₁ (X ⋯ₚ assocSwapᵣ (syncs B₁) (syncs B₂)))
--
-- proved by induction over the φ-blocks with U.φ-comm′ (each step contributes an
-- assocSwapᵣ 1 1 on the body, accumulated by the renaming laws R2/R2'), followed
-- by U.ν-swap′ / U.ν-comm′ on the two data channels and the canonₛ-naturality
-- reconciliation of the leaf U[ P ] (leafσ …) (via U-⋯ₚ + U-cong + canonₛ-nat).
-- This is exactly the old BlockSwap+BlockPermutation+NuSwap/NuComm engine
-- (~760 ln there); against the simpler new translation the φ-blocks carry no
-- flag cells, so only the binder permutation + leaf reconcile remain.
-- The infrastructure (Uν-flat, leafσ, Bφ, Bφ-cong, UB-flat, canonₛ) is in place.

U-ν-swap : (σ : m →ₛ n) {B₁ B₂ : BindGroup} {P : T.Proc (sum B₁ + sum B₂ + m)} →
           U[ T.ν B₁ B₂ P ] σ U.≋ U[ T.ν B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂)) ] σ
U-ν-swap {m = m} {n = n} σ {B₁} {B₂} {P} =
     ≡→≋ (Uν-flat σ B₁ B₂ P)
  ◅◅ U.ν-cong (Bφ-transpose B₁ B₂ (U[ P ] (leafσ σ B₁ B₂)))
  ◅◅ Eq*.return U.ν-swap′
  ◅◅ U.ν-cong (≡→≋ (Bφ-⋯ B₂ (Bφ B₁ Xs) (swapᵣ 1 1)))
  ◅◅ U.ν-cong (Bφ-cong B₂ (≡→≋ (Bφ-⋯ B₁ Xs (swapᵣ 1 1 ↑* sB₂))))
  ◅◅ U.ν-cong (Bφ-cong B₂ (Bφ-cong B₁ (≡→≋ leafEq)))
  ◅◅ ≡→≋ (sym (Uν-flat σ B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂))))
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Xs : U.Proc (sB₁ + (sB₂ + (2 + n)))
    Xs = U[ P ] (leafσ σ B₁ B₂) U.⋯ₚ assocSwapᵣ sB₂ sB₁
    leafEq : (Xs U.⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁))
             ≡ U[ P T.⋯ₚ swapᵣ (sum B₁) (sum B₂) ] (leafσ σ B₂ B₁)
    leafEq =
        cong (U._⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)) (local-U-σ⋯ P)
      ■ local-U-σ⋯ P
      ■ U-cong P subEq
      ■ sym (U-⋯ₚ P)
      where
        subEq : (leafσ σ B₁ B₂ ·ₖ assocSwapᵣ sB₂ sB₁) ·ₖ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)
                ≗ swapᵣ (sum B₁) (sum B₂) ·ₖ leafσ σ B₂ B₁
        subEq = subEq-gen σ B₁ B₂

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

-- the inner L₃ = (assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2 fixes toℕ ≥ sA2+(sA1+2).
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
head-bounded Bs (cons-ret/acq sh {s₂ = st} s≃
                  (cons s₁'' s₂'' ¬sk s≃' (nil Sk)) rest) refl =
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

Bφ-lift-step : (B : BindGroup) {n : ℕ} {P Q : U.Proc (syncs B + n)} →
               P UR.─→ₚ Q → Bφ {n} B P UR.─→ₚ Bφ B Q
Bφ-lift-step []            r = r
Bφ-lift-step (b ∷ [])      r = r
Bφ-lift-step (b ∷ B@(_ ∷ _)) {n} r =
  UR.RU-Sync (Bφ-lift-step B (subst-→ₚ (sym (+-suc (syncs B) n)) r))
  where
    subst-→ₚ : ∀ {a c} (eq : a ≡ c) {P Q : U.Proc a} → P UR.─→ₚ Q →
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

