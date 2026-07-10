-- CORRECTED probe on the ν-swap′ strict image bridge.
--
--   The bridge  (ν-swap′ reduct of U[ ν B₁ B₂ P₀ ]σ) ≡ U[ ν B₂ B₁ (P₀⋯swap) ]σ
--   holds by refl ONLY when at most ONE of B₁, B₂ has a nonempty φ-telescope
--   (syncs ≤ 0 on one side).  It is FALSE when BOTH telescopes are nonempty:
--   the untyped ν-swap′ swaps only the two ν-bound endpoints and leaves the
--   φ-telescope order (B₁-then-B₂) intact, whereas U[ ν B₂ B₁ … ]σ has them in
--   the OPPOSITE physical order, so the outer φ-cell references a different
--   endpoint on each side.  Reconciling them is a φ-telescope TRANSPOSITION
--   (φ-comm chain, length ≥ 1), NOT ≡ — confirming NonEpsRoadblock and the
--   φ-comm flag-swap obstruction (DepthDescentWall.φ-align-⊥).  So the earlier
--   "ν-swap has a strict bridge" reading was a DEGENERATE-INSTANCE artifact; the
--   multi-block ν-swap (arising from LSplit/RSplit) genuinely needs up-to-φ
--   absorption (PhiAbsorbNuSwap) — the reverse-sim roadblock stands there.
--   The general strict bridge is refuted hole-free in ImageBridges.agda.
module BorrowedCF.Simulation2.Backward.SwapBridgeGen where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Nat using (_+_)
open import Data.Nat.ListAction using (sum)
open import Data.List using (_∷_; [])
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open Fin.Patterns

-- Degenerate (B₂ has empty telescope): strict bridge holds by refl.
module _ where
  B₁ B₂ : TP.BindGroup
  B₁ = 1 ∷ 1 ∷ []          -- syncs 1
  B₂ = 1 ∷ []              -- syncs 0  (empty telescope ⇒ no transposition)

  P₀ : TP.Proc (sum B₁ + sum B₂ + 0)
  P₀ = TP.⟪ ` 0F ⟫

  σ₀ : 0 →ₛ 0
  σ₀ ()

  Simg : UP.Proc 0
  Simg = proj₁ (_,_ {A = UP.Proc 0} {B = λ S → U[ TP.ν B₁ B₂ P₀ ] σ₀ UP.≋ S}
                    _ (Eq*.return UP.ν-swap′))

  test-degenerate : Simg ≡ U[ TP.ν B₂ B₁ (P₀ TP.⋯ₚ swapᵣ (sum B₁) (sum B₂)) ] σ₀
  test-degenerate = refl

-- The two-nonempty-telescope counterexample lives (proven, machine-checked) in
-- ImageBridges.agda; reproduced here as a comment because `refl` fails to
-- typecheck (that IS the point):
--
--   D₁ = D₂ = 1 ∷ 1 ∷ []   (each syncs 1)
--   SimgD ≡ U[ ν D₂ D₁ (R₀ ⋯ swapᵣ 2 2) ] ρ
--     ⇒  suc ((swapᵣ 1 1 ↑) (weaken* 0 (weaken* (syncs (1∷[])) 0F))) != 0F
--        (the innermost sync-cell references 1F on the LHS, 0F on the RHS).
