-- | Backward simulation — the ≋-core ObsBase instance for RU-LSplit, WITHOUT
--   the slot-factorisation theory (PROBE).
--
--   Pipeline status:
--     Stage 1 (REDEX PINNING)      CLOSED — PinBase.pin-lsplit-redex: the
--       untyped lsplit thread, in an arbitrary one-hole context C, is pinned
--       to a typed prenex thread e† with the on-the-nose equation
--       e† ⋯ Bσ ≡ T ⋯ ρ (no ~ᵩ residue — `thrs` is stated on live*).
--     Stage 2 (THREAD INVERSION)   CLOSED up to the layout frontier —
--       PinConj.⊢-prenex-thread types e†; frameApp-reflect at Bσ
--       (PrenexImageVSub.Bσ-VSub) reflects the frame; lsplit-arg-chan +
--       close-arg-var force the argument to a VARIABLE x₀ of the typed
--       prenex inner scope, with
--           (` x₀) ⋯ Bσ (tel (prenexᵗ P)) σ ≡ ((e₁ ⋯ ρ) ⊗ (` ρ 0F)) ⊗ (e₂ ⋯ ρ).
--     Stage 2 (layout dichotomy)   CLOSED — PinConj.tsplit splits x₀ into
--       node-of-the-telescope vs ambient; PinConj.{Bσ-ambient,Bσ-node} compute
--       Bσ on both: ambient variables go to `σ y ⋯ BσWk`, node variables to
--       the node's canonical handle `νHandle B₁ B₂ _ z ⋯ BσWk t₂ _`.
--     Stages 2-tail/3/4            OPEN — `pin-lsplit-fire`, TWO holes:
--       NODE case: (a) the single-node handle analysis of νHandle
--            (SplitsH2.canonₛ-handleq machinery) + BσWk-middle arithmetic;
--            (b) typed firing: rearrange prenexᵗ P by typed ≋ (node-to-front
--            via ν-comm, thread-to-front via ∥ moves) to R-LSplit's rigid
--            shape, fire, wrap with R-Struct; (c) codomain: pointed
--            thread-replacement congruence of ~ plus the forward
--            U-lsplit-step image, closing with ≋⇒≈.
--       AMBIENT case: σ-escape — the redex channel appears to come from the
--            ambient σ.  NOT excludable from the Witness record alone: needs
--            precisely the boundary-preservation of the witness renaming
--            (ρ 0F telescope-bound vs BσWk-images ambient) that the slot
--            factorisation theory provides.  This is the probe's verdict on
--            the factor′ bypass: it shrinks the needed slot theory to this
--            single side condition, but does not eliminate it.
module BorrowedCF.Simulation.Backward.PinLSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR

open import BorrowedCF.Simulation.Support.StepDecomp using (Ctx*; _[_]ᴷ)
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_)
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form using (wkTel)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (BScope; BTel; Bσ)
open import BorrowedCF.Simulation.Support.Normal.PrenexImageVSub using (Bσ-VSub)
open import BorrowedCF.Simulation.Support.ReverseInv
  using (frameApp-reflect; close-arg-var)
open import BorrowedCF.Simulation.Support.InvFrame using (strengthen-frame)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug₁; frame*-⋯)
open import BorrowedCF.Simulation.Backward.LSplit using (lsplit-arg-chan)
open import BorrowedCF.Simulation.Backward.PinBound using (pin-lsplit-redex-bound)
open import BorrowedCF.Simulation.Backward.PinAmb using (σ-escape-refute)
open import BorrowedCF.Simulation.Backward.PinConj
  using (⊢-prenex-thread; tsplit; Bσ-ambient; Bσ-node)

open import Data.List.Membership.Propositional using (_∈_)

open UP using (_≋_)

-- Plugging commutes with renaming (local re-proof, as in Forward.Discard).
frame-plug*ᵣ : ∀ {m p} (E : Frame* m) {t : Tm m} (ρ : m →ᵣ p) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

------------------------------------------------------------------------
-- The OPEN residual: fire the pinned redex and reconcile the codomain.
------------------------------------------------------------------------

pin-lsplit-fire :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {k} (C : Ctx* n k) {s : 𝕊 0} {e₁ e₂ : Tm (2 + k)} {P₁ : UP.Proc (2 + k)}
    {F : Frame* (2 + k)}
  → C [ UP.ν (UP.⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁) ]ᴷ ≋ U[ P ] σ
  → (ρ : (2 + k) →ᵣ BScope (tel (prenexᵗ P)) n)
    (F₀ : Frame* (inner (prenexᵗ P))) (x₀ : 𝔽 (inner (prenexᵗ P)))
  → (F₀ [ K (`lsplit s) ·¹ (` x₀) ]*) ∈ thr (prenexᵗ P)
  → {Γ* : Ctx (inner (prenexᵗ P))} {β : Struct (inner (prenexᵗ P))}
  → ChanCx Γ*
  → Γ* ; β ⊢ F₀ [ K (`lsplit s) ·¹ (` x₀) ]* ∶ `⊤ ∣ 𝕀
  → F ⋯ᶠ* ρ ≡ frame*-⋯ F₀ (Bσ (tel (prenexᵗ P)) σ) (Bσ-VSub (tel (prenexᵗ P)) Vσ)
  → (` x₀) ⋯ Bσ (tel (prenexᵗ P)) σ ≡ ((e₁ ⋯ ρ) ⊗ (` ρ 0F)) ⊗ (e₂ ⋯ ρ)
  → (∀ z → ρ 0F ≢ wkTel (BTel (tel (prenexᵗ P)) n) z)
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′
      × C [ UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁) ]ᴷ
          ≈ U[ P′ ] σ)
pin-lsplit-fire σ Vσ Γ-S {P = P} ⊢P C c ρ F₀ x₀ m† Γ*-S ⊢e† Feq xeq bnd
  with tsplit (tel (prenexᵗ P)) x₀
... | inj₂ (a , t₁ , B₁ , B₂ , t₂ , teq , z , x₀eq) rewrite teq =
  let node-escape = sym (Bσ-node t₁ B₁ B₂ t₂ σ z)
                  ■ cong (Bσ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) σ) (sym x₀eq)
                  ■ xeq
  in
  {! OPEN (node case): x₀ sits in node (t₁ ∣ B₁ B₂ ∣ t₂) at offset z, and
     node-escape pins the triple to `νHandle B₁ B₂ (Bσ t₁ σ) z ⋯ BσWk t₂ _`
     (PinConj.Bσ-node).  Remaining:
     (a) the SINGLE-node handle analysis of νHandle (SplitsH2.canonₛ-handleq
         machinery) + BσWk-middle arithmetic, forcing z into the b₁-block at
         an lsplit-able offset and the handle components to the canonical L/R,
     (b) typed firing: rearrange plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) by typed ≋
         (RealiseBase-style moves) to R-LSplit's rigid shape, fire, R-Struct,
     (c) codomain: pointed thread-replacement congruence of ~ + the forward
         U-lsplit-step image, closed with ≋⇒≈. !}
... | inj₁ (y , x₀eq) =
  let σ-escape = sym (Bσ-ambient (tel (prenexᵗ P)) σ y)
               ■ cong (Bσ (tel (prenexᵗ P)) σ) (sym x₀eq)
               ■ xeq
  in ⊥-elim (σ-escape-refute (tel (prenexᵗ P)) σ y bnd σ-escape)

------------------------------------------------------------------------
-- The target: the ≋-core ObsBase instance for RU-LSplit, in context.
------------------------------------------------------------------------

pin-lsplit :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {k} (C : Ctx* n k) {s : 𝕊 0} {e₁ e₂ : Tm (2 + k)} {P₁ : UP.Proc (2 + k)}
    {F : Frame* (2 + k)}
  → C [ UP.ν (UP.⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁) ]ᴷ ≋ U[ P ] σ
  → Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′
      × C [ UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁) ]ᴷ
          ≈ U[ P′ ] σ)
pin-lsplit σ Vσ Γ-S {P = P} ⊢P C {s} {e₁} {e₂} {P₁} {F} c
  with ρ , e† , m† , eq , bnd ← pin-lsplit-redex-bound P σ C s F c
  with Γ* , β , Γ*-S , ⊢e† ← ⊢-prenex-thread Γ-S ⊢P m†
  with F₀ , arg₀ , refl , Feq , argeq ←
       frameApp-reflect Γ*-S e† ⊢e† (Bσ (tel (prenexᵗ P)) σ)
         (Bσ-VSub (tel (prenexᵗ P)) Vσ) (`lsplit s) (F ⋯ᶠ* ρ)
         (eq ■ frame-plug*ᵣ F ρ)
  with _ , (_ , _ , ⊢app) , _ , _ ← strengthen-frame F₀ ⊢e†
  with _ , _ , _ , _ , ⊢arg₀ , ch ← lsplit-arg-chan ⊢app
  with x₀ , refl ← close-arg-var arg₀ ⊢arg₀ ch (Bσ (tel (prenexᵗ P)) σ) (sym argeq)
  = pin-lsplit-fire σ Vσ Γ-S ⊢P C c ρ F₀ x₀ m† Γ*-S ⊢e† Feq (sym argeq) bnd
