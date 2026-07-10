-- | φ-layer inversion for the reverse simulation's simRes φ-bearing case.
--
--   simRes (Backward.agda ?1/?2) receives an untyped step `sub : X ─→ₚ X′`
--   where X = UB[ b ∷ c ∷ Bp ] … is φ-HEADED (X ≡ φ ϕ[ b ] X₀).  A φ-headed
--   untyped process reduces by EXACTLY three rules (RU-Sync / RU-Drop /
--   RU-Struct), so `sub` decomposes into the trichotomy proved here.  This is
--   the reusable first layer of the reverse telescope-descent engine.
--
--   The proof is a coverage-complete case split on `_─→ₚ_`; it is hole-free and
--   postulate-free (verified by agda-check).  It also makes the coupling to the
--   non-ε engine (Backward.agda ?0) explicit: the φ-Struct alternative delivers
--   an ARBITRARY inner reduction up to ≋, which is precisely the ≋-transport the
--   ?0 engine must supply.
module BorrowedCF.Simulation.Backward.SimResPhi where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_)

open Nat.Variables
open Fin.Patterns
open UP using (Proc; φ; ⟪_⟫; _∥_; drop; acq; Flag; _≋_)
open UR using (_─→ₚ_)

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- The three ways a φ-headed process can step.
------------------------------------------------------------------------

-- RU-Sync : the step happens strictly under the φ.
record φ-sync {n} (fl : Flag) (X₀ : Proc (1 + n)) (Y : Proc n) : Set where
  constructor mk-sync
  field
    {Y₀}  : Proc (1 + n)
    step  : X₀ ─→ₚ Y₀
    lands : Y ≡ φ fl Y₀

-- RU-Drop : the flag is `drop`, the body is a drop-redex thread ∥ P, and the
-- flag flips to `acq`.
record φ-drop {n} (fl : Flag) (X₀ : Proc (1 + n)) (Y : Proc n) : Set where
  constructor mk-drop
  field
    F      : Frame* (1 + n)
    x      : 𝔽 n
    P      : Proc (1 + n)
    isdrop : fl ≡ drop
    source : X₀ ≡ ⟪ F [ K `drop ·¹ 𝓒[ * × Fin.suc x × ` 0F ] ]* ⟫ ∥ P
    target : Y ≡ φ acq (⟪ F [ * ]* ⟫ ∥ P)

-- RU-Struct : an ADMINISTRATIVE ≋-wrapped inner reduction.  Note the inner
-- reduction `red` is on an ARBITRARY P′ ≋-equal to φ fl X₀ — reflecting it is
-- exactly the job of the non-ε ≋-transport engine (Backward.agda ?0).
record φ-struct {n} (fl : Flag) (X₀ : Proc (1 + n)) (Y : Proc n) : Set where
  constructor mk-struct
  field
    {P′ Q′} : Proc n
    pre     : φ fl X₀ ≋ P′
    red     : P′ ─→ₚ Q′
    post    : Q′ ≋ Y

φ-trichotomy : ∀ {n} (fl : Flag) (X₀ : Proc (1 + n)) {Y : Proc n}
             → φ fl X₀ ─→ₚ Y
             → φ-sync fl X₀ Y ⊎ φ-drop fl X₀ Y ⊎ φ-struct fl X₀ Y
φ-trichotomy fl X₀ (UR.RU-Sync step)         = inj₁ (mk-sync step refl)
φ-trichotomy fl X₀ (UR.RU-Drop {P = P} F {x = x}) =
  inj₂ (inj₁ (mk-drop F x P refl refl refl))
φ-trichotomy fl X₀ (UR.RU-Struct pre red post) = inj₂ (inj₂ (mk-struct pre red post))
