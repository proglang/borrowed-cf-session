module BorrowedCF.Simulation.Support.RevAdmin where

-- | Administrative (silent) untyped moves and the weak-bisimulation
--   equivalence ≈ used as the reverse-simulation codomain (and input).
--
--   ≈ is the equivalence closure of  ≋ ∪ ─→ᵃ  where ─→ᵃ is the set of
--   φ-handshake / sync-cell GC steps that have NO typed counterpart and leave
--   the U[_] image.  It is kept MINIMAL (RU-Cleanup — the spent-`done`-cell GC —
--   closed under the φ / ν / ∥ congruences) so that ≈ never relates two
--   processes differing by an OBSERVABLE step (Com/Choice/New/Fork/…): every
--   ─→ᵃ move flips or garbage-collects an administrative sync cell only.

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*; Value)
import BorrowedCF.Reduction.Processes.Untyped as UR

import Data.Sum as Sum
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)

open Nat.Variables

------------------------------------------------------------------------
-- Administrative moves.
------------------------------------------------------------------------

infix 4 _─→ᵃ_

data _─→ᵃ_ {n} : Proc n → Proc n → Set where
  -- Silent GC of a spent ⟨skip⟩ handle.  A thread-local discard has no typed
  -- counterpart when the handle is ambient (machine evidence:
  -- Simulation.DiscardProbe), so it is administrative by the definition above.
  a-discard : ∀ {e} (F : Frame* n) (V : Value e) →
              ⟪ F [ K `discard ·¹ e ]* ⟫ ─→ᵃ ⟪ F [ K `unit ]* ⟫
  a-sync    : ∀ {x} {P Q}      → P ─→ᵃ Q → φ x P ─→ᵃ φ x Q
  a-res     : ∀ {P Q}          → P ─→ᵃ Q → ν P   ─→ᵃ ν Q
  a-par     : ∀ {P Q R}        → P ─→ᵃ Q → P ∥ R ─→ᵃ Q ∥ R

-- Every administrative move IS an untyped reduction (so ≈ is a subrelation of
-- ─→ₚ*-up-to-≋, and soundness of ≈ can be checked against the reduction).
admin⇒red : ∀ {n} {P Q : Proc n} → P ─→ᵃ Q → P UR.─→ₚ Q
admin⇒red (a-discard F V) = UR.RU-Discard F V
admin⇒red (a-sync a) = UR.RU-Sync (admin⇒red a)
admin⇒red (a-res a)  = UR.RU-Res  (admin⇒red a)
admin⇒red (a-par a)  = UR.RU-Par  (admin⇒red a)

------------------------------------------------------------------------
-- The weak-bisimulation equivalence ≈ = EqClosure (≋ ∪ ─→ᵃ).
------------------------------------------------------------------------

≈rel : ∀ {n} → Rel (Proc n) _
≈rel P Q = (P ≋ Q) Sum.⊎ (P ─→ᵃ Q)

infix 4 _≈_

_≈_ : ∀ {n} → Rel (Proc n) _
_≈_ = EqClosure ≈rel

≋⇒≈ : ∀ {n} {P Q : Proc n} → P ≋ Q → P ≈ Q
≋⇒≈ pq = Eq*.return (Sum.inj₁ pq)

─→ᵃ⇒≈ : ∀ {n} {P Q : Proc n} → P ─→ᵃ Q → P ≈ Q
─→ᵃ⇒≈ a = Eq*.return (Sum.inj₂ a)

≈-refl : ∀ {n} {P : Proc n} → P ≈ P
≈-refl = ε

≈-trans : ∀ {n} {P Q R : Proc n} → P ≈ Q → Q ≈ R → P ≈ R
≈-trans = _◅◅_

≈-sym : ∀ {n} {P Q : Proc n} → P ≈ Q → Q ≈ P
≈-sym {n} = Eq*.symmetric (≈rel {n})

------------------------------------------------------------------------
-- Congruences (needed to rebuild reverse-simulation codomains).
------------------------------------------------------------------------

≈-ν-cong : ∀ {n} {P Q : Proc (2 + n)} → P ≈ Q → ν P ≈ ν Q
≈-ν-cong = Eq*.gmap ν
  λ { (Sum.inj₁ x) → Sum.inj₁ (ν-cong x)
    ; (Sum.inj₂ a) → Sum.inj₂ (a-res a) }

≈-φ-cong : ∀ {n} {x} {P Q : Proc (1 + n)} → P ≈ Q → φ x P ≈ φ x Q
≈-φ-cong {x = x} = Eq*.gmap (φ x)
  λ { (Sum.inj₁ y) → Sum.inj₁ (φ-cong y)
    ; (Sum.inj₂ a) → Sum.inj₂ (a-sync a) }

≈-∥-congˡ : ∀ {n} {P Q Rr : Proc n} → P ≈ Q → P ∥ Rr ≈ Q ∥ Rr
≈-∥-congˡ {Rr = Rr} = Eq*.gmap (_∥ Rr)
  λ { (Sum.inj₁ x) → Sum.inj₁ (∥-cong x ε)
    ; (Sum.inj₂ a) → Sum.inj₂ (a-par a) }
