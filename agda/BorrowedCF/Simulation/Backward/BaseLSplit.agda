-- | Backward simulation — the RU-LSplit constructor of the `Base` residual,
--   restricted to the pure-congruence core ≋ of ≈.  THE make-or-break probe:
--   a channel-op redex under a `ν`, reflected from a merely-≋-related image.
--
--   STATUS: OPEN (probe result — NOT closed).  One hole `?0` remains, exhibiting
--   the wall.  The whole obligation reduces to feeding the strict reflector
--   `lsplit-reflect`, whose one missing input is
--
--       ?0 : U[ P ] σ ≡ ν (⟪ F [ lsplit ·¹ 𝓒[e₁×0F×e₂] ]* ⟫ ∥ P₁)   -- =: R
--
--   from the hypothesis  c : R ≋ U[ P ] σ.  This is exactly the STRICT
--   image-inversion `Reverse-U-≋` (Support.RevUCong), which `reverse-U-≋-⊥`
--   machine-refutes.  Worse, for the given P the goal is OUTRIGHT false whenever
--   P has head `∥`: then `U[ P ] σ = U[_]σ ∥ U[_]σ` has head `∥`, never `ν = R`
--   — and such P ARE valid inputs (an lsplit redex under a ν is ≋-reachable from
--   a head-∥ image by `ν-ext′`).  So `lsplit-reflect` alone cannot prove this
--   constructor; a genuine proof must first re-inflate the (flattened) witness
--   of `R ≋ U[P]σ` into the unflattened ν-node + exposed-thread configuration
--   that the typed R-LSplit / `lsplit-go` consumes.  That re-inflation needs a
--   typed-side prenex/extrusion normalisation theory (the typed analogue of the
--   whole Support.Normal.* stack) which does not exist — the typed ≋ has NO
--   φ-moves (Congruence.U-≋), so it cannot even name the administrative φ-cell
--   reorderings the untyped witness sees through.  See the final report for the
--   full (iii) diagnosis.
module BorrowedCF.Simulation.Backward.BaseLSplit where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR

open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_)
open import BorrowedCF.Simulation.Backward.LSplit using (lsplit-reflect)

open UP using (_≋_)

base-lsplit-≋ :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
    {s : 𝕊 0} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)} {F : Frame* (2 + n)}
  → UP.ν (UP.⟪ F [ K (`lsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁) ≋ U[ P ] σ
  → Σ[ P′ ∈ TP.Proc m ]
      (Star TR._─→ₚ_ P P′
       × UP.ν (UP.⟪ F [ ((e₁ ⊗ (` 0F)) ⊗ (K `unit)) ⊗ (((K `unit) ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
           ≈ U[ P′ ] σ)
base-lsplit-≋ σ Vσ Γ-S ⊢P {s = s} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} {F = F} c =
  lsplit-reflect σ Vσ Γ-S ⊢P {s = s} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} {F = F}
    {! bridge !}
