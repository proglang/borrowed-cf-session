-- | φ-comm′ reflection for the reverse simulation's RU-Struct case, the
--   UP-TO-φ / EQUIVARIANCE route — the companion of RUStructDispatch's
--   νφsync-reflect for the ADJACENT-φ-cell generator.
--
--   c₁'s leading link (under the ν-telescope, via ν-cong′) is
--     φ-comm′ :  φ x (φ y body) ≋′ φ y (φ x (body ⋯ₚ assocSwapᵣ 1 1)).
--   Image φ-telescopes live INSIDE the dual-pair binder, so the relevant strict
--   image is  U[ P ] σ = ν (φ x (φ y body)).  By the SEED lemma
--   (Backward.SeedProbe: drop-head-clash / acq-head-clash) NO flag-sensitive
--   rule (RU-Drop / RU-Acquire) can fire at either swapped cell of
--   ν (φ y (φ x …)) — the outer φ wraps a φ-cell (not a thread) and the inner φ
--   sits under a φ (not a ν).  Hence the only genuine step on the swapped body is
--   the flag-POLYMORPHIC descent  RU-Res (RU-Sync (RU-Sync sub)) with
--   sub : body ⋯ₚ assocSwapᵣ 1 1 ─→ₚ T.  Transport sub back by equivariance
--   (red-⋯ₚ over the INVOLUTIVE assocSwapᵣ 1 1) and fire
--   RU-Res (RU-Sync (RU-Sync ·)) on the strict image; the re-swap
--   ν (φ x (φ y ·)) ≋ ν (φ y (φ x ·)) is absorbed by ≈.
--
--   The reflector is agnostic to whether x = y (same-flag: a pure renaming) or
--   x ≠ y (different-flag: NOT a renaming); the flag-polymorphism of RU-Sync
--   makes both uniform.  The seed lemma is what licenses, at the DISPATCH, the
--   claim that the inner step really is this descent and not a flag-sensitive
--   firing.  All results hole-free / postulate-free (relative to `rec`).
module BorrowedCF.Simulation2.Backward.PhiCommReflect where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RedRename using (red-⋯ₚ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-trans; ≋⇒≈)
open import BorrowedCF.Simulation2.Backward.RUStructDispatch using (Res; assocSwapₚ-invU)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Fin.Patterns

------------------------------------------------------------------------
-- φ-comm′ reflection (equivariance analog of νφsync-reflect, two φ cells).
------------------------------------------------------------------------

φcomm-reflect :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → (rec : ∀ {Q′} → U[ P ] σ UR.─→ₚ Q′ → Res σ P Q′)
  → {x y : UP.Flag} {body : UP.Proc (2 + (2 + n))}
  → U[ P ] σ ≡ UP.ν (UP.φ x (UP.φ y body))
  → {T : UP.Proc (2 + (2 + n))}
  → (sub : (body UP.⋯ₚ assocSwapᵣ 1 1) UR.─→ₚ T)
  → Res σ P (UP.ν (UP.φ y (UP.φ x T)))
φcomm-reflect σ {P} rec {x} {y} {body} imgeq {T} sub
  with sub′ ← subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 1 1)) (assocSwapₚ-invU {1} {1} body)
                    (red-⋯ₚ (assocSwapᵣ 1 1) sub)
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (UP.φ x (UP.φ y (T UP.⋯ₚ assocSwapᵣ 1 1)))) (sym imgeq)
               (UR.RU-Res (UR.RU-Sync (UR.RU-Sync sub′))))
  = P′ , steps
  , ≈-trans (≋⇒≈ (Eq*.symmetric _
      (subst (λ W → UP.ν (UP.φ x (UP.φ y (T UP.⋯ₚ assocSwapᵣ 1 1))) UP.≋ UP.ν (UP.φ y (UP.φ x W)))
             (assocSwapₚ-invU {1} {1} T)
             (UP.ν-cong (Eq*.return (UP.φ-comm′ {x = x} {y = y}))))))
      codom
