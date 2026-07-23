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
--     Stage A (layout → rule)      CLOSED — PinFireBase: sink construction
--       (node-to-backᵗ), sink-pin, groupAt/atk-eq.
--     Stage B/C (rearrange + fire) CLOSED — PinFire.fire-node: the binding
--       node is sunk to the INNERMOST position (so the redex thread needs no
--       strengthening), the thread is fronted, `z` is split on the groups
--       (ν-swap′ for the second), and R-LSplit fires under R-Bind*/R-Struct.
--       The NODE case below returns that single typed step, star-wrapped.
--     Stage D (codomain)           ONE hole — `C[reduct] ≈ U[ P′ ] σ`.
--       PinCodomain provides the pointed thread-replacement congruence of ~
--       (`~-replace`), the pointed context presentation (`ctx-replace`), and
--       their composite `reduct-image-~ : nf (C[reduct]) ~` the image block
--       normal form with ONE entry replaced by the reduct thread.  The
--       residual gap is the reduct-image identification
--           mkNF (BTel t n) (setAt i′ (T′ ⋯ ρ)) ~ nf (U[ P′ ] σ)
--       — the νHandle/Bσ analogues of SplitsLQ's canonₛ-lwkq and
--       canonₛ-handleq(-b1) slot lemmas (grown-block handle = old handle +
--       lwk-invisibility for the other threads), plus re-deriving the fired
--       thread from `reduct-image-~`'s landing membership so the two
--       replacement sites coincide.  The image-side STEP is free:
--       sim→ σ Vσ Γ-S ⊢P st : U[ P ] σ ─→ᵤ U[ P′ ] σ.
--       AMBIENT case: CLOSED — σ-escape refuted by the boundary premise
--       (PinBound/PinAmb).
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
open import BorrowedCF.Simulation.Backward.PinFire using (fire-node)
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
pin-lsplit-fire σ Vσ Γ-S {P = P} ⊢P C {s = s} c ρ F₀ x₀ m† Γ*-S ⊢e† Feq xeq bnd
  with tsplit (tel (prenexᵗ P)) x₀
... | inj₂ (a , t₁ , B₁ , B₂ , t₂ , teq , z , x₀eq)
  with P′ , st ← fire-node t₁ B₁ B₂ t₂ (thr (prenexᵗ P))
        (subst (λ t → P TP.≋ plugᵗ t (parsᵗ (thr (prenexᵗ P)))) teq (prenex-soundᵗ P))
        s F₀ z
        (subst (λ v → (F₀ [ K (`lsplit s) ·¹ (` v) ]*) ∈ thr (prenexᵗ P)) x₀eq m†)
  = P′ , st ◅ ε ,
  {! OPEN (Stage D, codomain): C[reduct] ≈ U[ P′ ] σ.
     Stages A-C are CLOSED: `st : P ─→ₚ P′` fires the pinned redex via
     PinFire.fire-node (sink node-to-back, thread-to-front, groupAt/atk-eq,
     R-LSplit under R-Bind*/R-Struct).  Available for this hole:
       * the image-side step  sim→ σ Vσ Γ-S ⊢P st : U[ P ] σ ─→ᵤ U[ P′ ] σ
         (Simulation.Forward.sim→ is total),
       * the input ≋ `c`, the pinning equations Feq / xeq / bnd, and the
         node-escape triple  subst (λ t → (` x₀) ⋯ Bσ t σ ≡ _) teq xeq
         composed with PinConj.Bσ-node,
       * PinCodomain's pointed thread-replacement congruence for ~
         (setAt / ~-replace) for the nf-level conjugation.
     Route: nf-conjugate `c` (≋⇒~ + image-block-~), replace the pinned
     thread on both ends (~-replace), identify the replaced image list with
     `nf (U[ P′ ] σ)` via the reduct handle equations, close with ~⇒≋ / ≋⇒≈. !}
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
