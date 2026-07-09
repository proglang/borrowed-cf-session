module BorrowedCF.Simulation2.Backward.PhiAbsorbNuSwap where

-- | MACHINE-CHECKED MILESTONE for the "reverse-up-to-φ" key lemma  φ-absorb,
--   ν-swap case.
--
--   Question (mission): can an OBSERVABLE (channel-op) untyped reduction on a
--   ν-SWAPPED image be reflected onto the image with the reorder ABSORBED into
--   the codomain ≋/≈, WITHOUT strict image-recognition of the swapped term and
--   WITHOUT transporting the reduction?  NonEpsRoadblock / RevCongStrongLE showed
--   the STRICT recognizer and the sc-PRESERVING transport lever both fail on the
--   ν-swap′ × RU-LSplit collision (the un-swap peel has length ≥ 1).
--
--   THIS MODULE ANSWERS: YES for the natural instance.  The key structural fact
--   (already isolated in RevCongStrongLE) is that RU-LSplit fires ONLY on the
--   hardcoded endpoint 0F, and ν-swap′ displaces the redex 0F ↦ 1F.  Hence the
--   OBSERVABLE reduction on the swapped image  Rswap = ν (body ⋯ₚ swapᵣ 1 1)  is
--   FORCED to be an  RU-Struct  whose leading link  c₁  swaps Rswap back; the MINIMAL
--   such  c₁  lands EXACTLY on the strict image  U[ P ] σ.  So the leaf reduction
--   `inner` fires on the STRICT image and the strict-image port  lsplit-reflect
--   applies DIRECTLY — we never need to recognise Rswap as an image (it is NOT one),
--   because `red` HANDS us the peel.  The trailing link  c₂  (any ν-swap of the
--   reduct) is absorbed by the codomain ≈ (≋⇒≈).
--
--   Two variants compile hole/postulate-free:
--     • φ-absorb-νswap      : c₂ = ε           (reduct = canonical image reduct)
--     • φ-absorb-νswap-fwd  : c₂ = ν-swap link (reduct carries a forward swap,
--                                                genuinely absorbed by codomain ≈)
--
--   VERDICT: the codomain-≋/≈ slack is SUFFICIENT for the ν-swap case AS LONG AS
--   the reflection CONSUMES `red`'s own RU-Struct decomposition (which, for the
--   0F-only RU-LSplit, peels to the strict image in one un-swap link).  This is
--   the weakening NonEpsRoadblock's strict recognizer lacked: there the engine
--   had to REBUILD the peel and recognise the swapped term as a strict image
--   (impossible, length ≥ 1); here the peel is DELIVERED by the RU-Struct node.
--   Reverse-up-to-φ is therefore VIABLE for ν-swap with NO calculus/rule change.

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation2.Backward.LSplit using (lsplit-reflect)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈; ≈-trans; ≈-sym)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅◅_)
open import Data.Product using (Σ-syntax; _×_; _,_)

open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- The concrete decisive instance.
--   • P is any well-typed source process whose translation U[ P ] σ IS a
--     ν-bound thread carrying a single lsplit redex at the canonical endpoint 0F
--     (this is exactly the shape the leaf port lsplit-reflect recognises).
--   • Rswap is the untyped ν-swap of that image (ν-swap′).  It is NOT itself an
--     image (NonEpsRoadblock), yet it still admits the observable reduction.
------------------------------------------------------------------------

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ)
         {Γ : Ctx m} (Γ-S : ChanCx Γ) {g : Struct m}
         {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
         {s : 𝕊 0} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
         {F : Frame* (2 + n)}
         (imgeq : U[ P ] σ
                ≡ UP.ν (UP.⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ] ]* ⟫ UP.∥ P₁))
  where

  body : UP.Proc (2 + n)
  body = UP.⟪ F [ K (`lsplit s) ·¹ 𝓒[ e₁ × 0F × e₂ ] ]* ⟫ UP.∥ P₁

  image : UP.Proc n
  image = UP.ν body

  -- the ν-swapped image: lsplit's 0F is displaced to 1F, so it is NOT an
  -- RU-LSplit redex on its own (RU-LSplit fires only on 0F).
  Rswap : UP.Proc n
  Rswap = UP.ν (body UP.⋯ₚ swapᵣ 1 1)

  swap≋ : image UP.≋ Rswap
  swap≋ = Eq*.return (UP.ν-swap′ {P = body})

  -- Rswap is a genuine ≋-variant of the image.
  R≋image : Rswap UP.≋ image
  R≋image = Eq*.symmetric _ swap≋

  -- the canonical RU-LSplit reduct of the image = the port's codomain shape.
  Qcanon : UP.Proc n
  Qcanon = UP.ν (UP.⟪ F [ 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ] ]* ⟫ UP.∥ P₁)

  ------------------------------------------------------------------------
  -- Variant 1 : c₂ = ε.  The OBSERVABLE reduction on the swapped image.
  --   It MUST be an RU-Struct (no direct 1F lsplit rule); the minimal leading
  --   link swaps Rswap back to the STRICT image, then the plain RU-LSplit fires.
  ------------------------------------------------------------------------

  red : Rswap UR.─→ₚ Qcanon
  red = UR.RU-Struct R≋image (UR.RU-LSplit F) ε

  -- The reflection.  Because `red`'s leaf fires on the strict image, the
  -- strict-image port applies to `imgeq` directly — the reorder is absorbed.
  φ-absorb-νswap :
    Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Qcanon ≈ U[ P′ ] σ)
  φ-absorb-νswap =
    lsplit-reflect σ Vσ Γ-S ⊢P {s = s} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} {F = F} imgeq

  ------------------------------------------------------------------------
  -- Variant 2 : c₂ = ν-swap link.  Now the reduct itself carries a FORWARD
  --   ν-swap; the codomain ≈ genuinely absorbs it (≋⇒≈ + ≈-trans).
  ------------------------------------------------------------------------

  Qbody : UP.Proc (2 + n)
  Qbody = UP.⟪ F [ 𝓒[ e₁ × 0F × * ] ⊗ 𝓒[ * × 0F × e₂ ] ]* ⟫ UP.∥ P₁

  Qfwd : UP.Proc n
  Qfwd = UP.ν (Qbody UP.⋯ₚ swapᵣ 1 1)

  Qcanon≋Qfwd : Qcanon UP.≋ Qfwd
  Qcanon≋Qfwd = Eq*.return (UP.ν-swap′ {P = Qbody})

  red-fwd : Rswap UR.─→ₚ Qfwd
  red-fwd = UR.RU-Struct R≋image (UR.RU-LSplit F) Qcanon≋Qfwd

  φ-absorb-νswap-fwd :
    Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Qfwd ≈ U[ P′ ] σ)
  φ-absorb-νswap-fwd with lsplit-reflect σ Vσ Γ-S ⊢P {s = s} {e₁ = e₁} {e₂ = e₂}
                            {P₁ = P₁} {F = F} imgeq
  ... | P′ , steps , Qcanon≈ =
    P′ , steps , ≈-trans (≋⇒≈ (Eq*.symmetric _ Qcanon≋Qfwd)) Qcanon≈
