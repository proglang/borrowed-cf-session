-- | ≈-congruence for the φ-telescope UB[_].
--
--   The reverse simulation rebuilds its codomain UNDER the binder nest that the
--   translation emits for a bind group: U[ ν B₁ B₂ P ] σ = ν (UB[ B₁ ] … (UB[ B₂ ] …)),
--   and UB[ b ∷ B ] cc f = φ ϕ[ b ] (UB[ B ] … ), one sync cell per non-last
--   bind-group element.  TranslationProperties supplies the ≡- and ≋-variants
--   (UB-cong-≡ / UB-cong); this is the ≈-variant, which is what the φ-bearing
--   simRes branches need, because ≈ (RevAdmin) is the reverse codomain and it is
--   strictly coarser than ≋ (it also absorbs a-discard / a-drop / a-acq).
--
--   The induction is the same as UB-cong's: the telescope hands its continuation
--   a DETERMINED substitution at each level, so the two continuations are only
--   ever compared at that one point (`h _`).
module BorrowedCF.Simulation.Backward.TelCong where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Simulation.Support.RevAdmin using (_≈_; ≈-φ-cong)

open import Data.Nat.ListAction using (sum)
open import Data.List using (_∷_; [])

open Nat.Variables

-- ≈ transports along a scope-index equality (J on the ℕ proof).
≈-subst : {a b : ℕ} (eq : a ≡ b) {x y : UP.Proc a} → x ≈ y → subst UP.Proc eq x ≈ subst UP.Proc eq y
≈-subst refl xy = xy

-- The φ-telescope respects pointwise-≈ continuations.
UB-≈ : (B : TP.BindGroup) (cc : UChan n)
       {f g : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)} →
       (∀ σ → f σ ≈ g σ) → UB[ B ] cc f ≈ UB[ B ] cc g
UB-≈ []             cc            h = h λ()
UB-≈ (b ∷ [])       cc            h = h _
UB-≈ (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) h =
  ≈-φ-cong (UB-≈ B _ (λ σ → ≈-subst (sym (+-suc (syncs B) _)) (h _)))
