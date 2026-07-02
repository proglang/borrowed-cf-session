{-# OPTIONS --rewriting #-}
-- ============================================================================
--  RSPLIT SIMULATION — the DECISIVE positive test, machine-checked.
--
--  For a concrete WELL-TYPED-shaped R-RSplit redex `src` at the DOWNSTREAM-
--  sibling config, we fire the untyped translation and prove the forward
--  simulation up-to-≋:
--     Σ[ Q ∈ U.Proc _ ] ( U[ srcP ] σ  UR.─→ₚ*  Q  ×  Q  U.≋  U[ typedReduct ] σ )
--  which is exactly U-rsplit's leafRec obligation, concretely.
-- ============================================================================

module BorrowedCF.Simulation2.RsplitSci where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Bisim

open import Data.List using (_∷_; [])
open import Data.Fin using (zero; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_) renaming (return to ret)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables
open Fin.Patterns

import BorrowedCF.Processes.Typed as T
import BorrowedCF.Reduction.Processes.Typed as TR
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Reduction.Processes.Untyped as UR

open T.Proc
open U.Proc
open TR using (_─→ₚ_)

-- split-renamings for  B₁ = [],  B₂ = 1 ∷ [],  B = [].
module 𝐒 = TR.SplitRenamings [] (1 ∷ []) []

-- The R-RSplit redex body at scope  sum (1 ∷ 1 ∷ []) + sum [] + 0 = 2.
-- handle = 𝐒.inj {B=[]} {n=0} 0F  (the split-chain head).
sₛ : 𝕊 0
sₛ = msg ‼ `⊤ ; skip

redexBody : T.Proc 2
redexBody =
    ⟪ K (`rsplit sₛ) · (` 𝐒.inj {1 ∷ []} {0} 0F) ⟫
  ∥ ⟪ K `recv · (` 1F) ⟫

srcP : T.Proc 0
srcP = ν (1 ∷ 1 ∷ []) [] redexBody

-- typed step: the constructor DEFINES the reduct (no hand-transcription).
srcP─→Σ : Σ[ Q ∈ T.Proc 0 ] (srcP ─→ₚ Q)
srcP─→Σ = _ , TR.R-RSplit {B₁ = []} {B₂ = 1 ∷ []} {B = []} {b₁ = 0}
                          {s = sₛ} {E = []}

typedReduct : T.Proc 0
typedReduct = proj₁ srcP─→Σ

Usrc : U.Proc 0
Usrc = U[ srcP ] (λ())

Ured : U.Proc 0
Ured = U[ typedReduct ] (λ())

-- ============================================================================
--  The concrete shapes (from `normalize`), named so we can compute on them.
-- ============================================================================

-- Usrc = ν (φ drop BODYsrc),  BODYsrc : U.Proc 3.
BODYsrc : U.Proc 3
BODYsrc =
    ⟪ K (`rsplit sₛ) · ((* ⊗ (` 1F)) ⊗ (` 0F)) ⟫
  ∥ ⟪ K `recv · (((` 0F) ⊗ (` 1F)) ⊗ *) ⟫

Usrc≡ : Usrc ≡ ν (φ U.drop BODYsrc)
Usrc≡ = refl

-- Ured = ν (φ drop (φ drop BODYred)),  BODYred : U.Proc 4.
BODYred : U.Proc 4
BODYred =
    ⟪ ((* ⊗ (` 2F)) ⊗ (` 1F)) ⊗ (((` 1F) ⊗ (` 2F)) ⊗ (` 0F)) ⟫
  ∥ ⟪ K `recv · (((` 0F) ⊗ (` 2F)) ⊗ *) ⟫

Ured≡ : Ured ≡ ν (φ U.drop (φ U.drop BODYred))
Ured≡ = refl

open U using (_≋_; _≋′_)

-- FIRE the untyped step.  Expose via νφ-comm′ (data channel goes to 0F under
-- one ν), then RU-RSplit fires under the outer φ drop (RU-Sync).
fire : Σ[ Q ∈ U.Proc 0 ] (Usrc UR.─→ₚ Q)
fire = _ , UR.RU-Struct
             (fwd U.νφ-comm′ ◅ ε)
             (UR.RU-Sync (UR.RU-RSplit []))
             ε

Qfired : U.Proc 0
Qfired = proj₁ fire

-- Concrete normal forms (verified ≡ by refl), so the ≋ renamings reduce
-- against ground terms.
QfiredC : U.Proc 0
QfiredC =
  φ U.drop
   (ν (φ U.drop
        (   ⟪ ((* ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ (` 3F)) ⟫
          ∥ ⟪ K `recv · (((` 3F) ⊗ (` 1F)) ⊗ *) ⟫ )))

Qfired≡ : Qfired ≡ QfiredC
Qfired≡ = refl

UredC : U.Proc 0
UredC = ν (φ U.drop (φ U.drop BODYred))

Ured≡C : Ured ≡ UredC
Ured≡C = refl

-- RECONCILE.  Qfired and Ured are the SAME process up to binder order:
--   Qfired nest = φ_a · ν · φ_b ,   Ured nest = ν · φ_c · φ_d
-- with role-correspondence φ_a↔φ_d, φ_b↔φ_c, ν↔ν (verified: bodies coincide
-- under this correspondence — pure binder-order artifact, no var-vs-const).
-- Forward chain from Ured (all renamings apply forward):
--   ν (φ_c (φ_d B))  ≋⟨ ν-cong (φ-comm) ⟩  ν (φ_d (φ_c (B ⋯ aS 1 1)))
--                    ≋⟨ νφ-comm ⟩          φ_d (ν ((φ_c …) ⋯ aS 1 2))
φ-comm-red : φ U.drop (φ U.drop BODYred)
             U.≋′ φ U.drop (φ U.drop (BODYred U.⋯ₚ assocSwapᵣ 1 1))
φ-comm-red = U.φ-comm′

reconC : UredC ≋ QfiredC
reconC =
     U.ν-cong (fwd φ-comm-red ◅ ε)
  ◅◅ (fwd U.νφ-comm′ ◅ ε)

-- ============================================================================
--  THE DECISIVE RESULT — rsplit forward-simulation up-to-≋, machine-checked.
--
--  U-rsplit's leafRec obligation, concretely:  the untyped translation of the
--  source rsplit-reduces (one step, up to ≋ absorbed by RU-Struct) to some Q
--  structurally-congruent to the translation of the typed reduct.
-- ============================================================================

open import Relation.Binary.Construct.Closure.Equivalence as Eq* using () renaming (symmetric to ≋sym)

_─→ₚ*_ : U.Proc 0 → U.Proc 0 → Set
_─→ₚ*_ = Star UR._─→ₚ_

Qfired≋Ured : Qfired U.≋ Ured
Qfired≋Ured =
  subst₂ U._≋_ (sym Qfired≡) (sym Ured≡C) (≋sym U._≋′_ reconC)

rsplit-simulates : Σ[ Q ∈ U.Proc 0 ] (Usrc ─→ₚ* Q × Q U.≋ Ured)
rsplit-simulates = Qfired , (proj₂ fire ◅ ε) , Qfired≋Ured
