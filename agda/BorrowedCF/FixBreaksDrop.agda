{-# OPTIONS --rewriting #-}
-- ============================================================================
--  WHAT IS WRONG WITH THE TRANSLATION FIX — machine-verified, process-level.
--
--  The "fix" = the distributing Ub leaf (origin/main 34fd35e), currently IN the
--  tree.  This module exhibits, with the REAL U[_] and the REAL reductions, a
--  concrete R-Drop redex on which the fix BREAKS the forward simulation:
--
--    typed:   src ─→ₚ reduct           (R-Drop, drops head borrow ` 0F)
--    untyped: U[src]  must step to U[reduct]  via RU-Drop.
--
--  RU-Drop fires ONLY on  φ drop (⟪ F [ drop · 𝓒[ e × suc x × ` 0F ] ]* ⟫ ∥ P):
--  the drop-target handle's triple must carry the flag var ` 0F in its
--  RIGHT-sync slot.  Under the distributing fix, a MULTI-chain group's head
--  borrow gets  *  (unit) in that slot instead of ` 0F, so RU-Drop's pattern
--  cannot match — NO untyped Drop step exists.  The Drop forward simulation
--  step is therefore unconstructible under the fix.  (The live proof shows the
--  same as Theorems/Drop.agda:779  `* != ` 0F`.)
--
--  Config:  front group  1 ∷ 1 ∷ []  (drop head of the size-1 first chain,
--  b₁ = 0, B₁ = 1 ∷ []), B₂ = [].  The first chain is a multi-chain-group head,
--  so the distributing leaf gives its handle a  *  right-sync.
-- ============================================================================

module BorrowedCF.FixBreaksDrop where

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Simulation2.Congruence

open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)

import BorrowedCF.Processes.Typed as T
import BorrowedCF.Reduction.Processes.Typed as TR
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*; _⋯ᶠ*_)

open T.Proc
open U.Proc
open TR using (_─→ₚ_)

-- The sibling thread, at the reduct scope 1.
P₀ : T.Proc 1
P₀ = ⟪ K `recv · (` 0F) ⟫

-- The R-Drop redex source (matches R-Drop's LHS: E ⋯ᶠ* weakenᵣ, P ⋯ₚ weakenᵣ).
src : T.Proc 0
src = ν (1 ∷ 1 ∷ []) []
        (⟪ ([] ⋯ᶠ* weakenᵣ) [ K `drop · (` 0F) ]* ⟫ ∥ (P₀ T.⋯ₚ weakenᵣ))

-- The typed step, constructor DEFINES the reduct.
src─→Σ : Σ[ Q ∈ T.Proc 0 ] (src ─→ₚ Q)
src─→Σ = _ , TR.R-Drop {b₁ = 0} {B₁ = 1 ∷ []} {B₂ = []} {P = P₀} {E = []}

typedReduct : T.Proc 0
typedReduct = proj₁ src─→Σ

src─→typedReduct : src ─→ₚ typedReduct
src─→typedReduct = proj₂ src─→Σ

-- The source translation under the fix.
Usrc : U.Proc 0
Usrc = U[ src ] (λ())

-- Under the fix, Usrc's drop thread is  ⟪ drop · ((* ⊗ ` 1F) ⊗ *) ⟫ :
-- the handle triple's RIGHT-sync slot is  *  (a unit constant).
Usrc-shape :
  Usrc ≡ ν (φ U.drop
             ( ⟪ K `drop · ((* ⊗ (` 1F)) ⊗ *) ⟫
             ∥ ⟪ K `recv · (((` 0F) ⊗ (` 1F)) ⊗ *) ⟫ ))
Usrc-shape = refl

-- Right-sync projector out of the ⊗-tree.
slotR : Tm n → Tm n
slotR ((a ⊗ b) ⊗ c) = c
slotR _ = *

-- Extract the drop-thread's handle triple from Usrc's skeleton.
dropTriple : U.Proc 0 → Tm 3
dropTriple (ν (φ _ (⟪ K `drop · t ⟫ ∥ _))) = t
dropTriple _ = *

dropTriple-Usrc : dropTriple Usrc ≡ ((* ⊗ (` 1F)) ⊗ *)
dropTriple-Usrc = refl

-- The drop handle's right-sync slot is the unit CONSTANT, not the flag ` 0F.
drop-right-is-unit : slotR (dropTriple Usrc) ≡ *
drop-right-is-unit = refl

-- ============================================================================
--  THE COUNTEREXAMPLE.  RU-Drop fires ONLY when the drop handle triple has the
--  shape  𝓒[ e × suc x × ` 0F ] = ((e ⊗ ` (suc x)) ⊗ ` 0F),  i.e. RIGHT-sync
--  slot = the flag variable ` 0F.  Usrc's drop handle has right-sync  *  (unit
--  constant).  No renaming/substitution/≋ turns a constant into a variable, so
--  NO RU-Drop redex matches Usrc — the untyped side is STUCK for Drop, hence the
--  R-Drop forward-simulation step  U[src] ─→ U[reduct]  cannot exist.
-- ============================================================================

-- There is no  (e , x)  making Usrc's drop handle fit RU-Drop's read shape:
no-RU-Drop-match :
  ¬ (Σ[ e ∈ Tm 3 ] Σ[ x ∈ 𝔽 2 ]
       dropTriple Usrc ≡ ((e ⊗ (` suc x)) ⊗ (` 0F)))
no-RU-Drop-match (e , x , ())

-- Contrast: the BROADCAST leaf puts the flag ` 0F in that slot, so RU-Drop DOES
-- fire — this is exactly the regression the fix introduces.  (See also the live
-- proof obstruction Theorems/Drop.agda:779  `* != ` 0F`, and the leaf-level
-- refl witnesses in RsplitDropTension.agda: dist-drophead-rightsync-is-unit vs
-- broadcast-drophead-rightsync-flag; plus dist-does-not-fix-rsplit showing the
-- fix does NOT even change the rsplit downstream sibling it was meant to fix.)
