-- | MACHINE-CHECKED MILESTONE for the reverse-up-to-φ residual  reflect-φescape,
--   νφ-comm φ-ESCAPE case with an OBSERVABLE φ-DROP — the SINGLE `Base`
--   obligation left open by  Backward.UpToPhiEngineWF  (its `Base`), and the case
--   DropNotAdmin proves cannot be closed by ε-absorption (a genuine drop
--   increments #acq).
--
--   RESULT: for the SIMPLEST source whose image is the canonical  ν (φ drop …),
--   the observable φ-drop on the νφ-comm ESCAPE  φ drop (ν …)  reflects to a REAL
--   typed  TR.R-Drop  step, hole/postulate-free.  The reverse is UNBLOCKED for the
--   width-1 escape.  (The width-≥2 interior-q geometry — DropInteriorProbe — is a
--   SEPARATE calculus gap and is NOT touched here.)
--
--   The concrete instance (m = n = 0, computed by  ReflectScratch  via `normalize`):
--     P₀       = ν (1 ∷ 1 ∷ []) [] (⟪ K drop · (`0F) ⟫ ∥ ⟪ K unit ⟫)
--     U[ P₀ ]σ₀  = ν (φ drop (⟪ K drop · 𝓒[ * × 1F × `0F ] ⟫ ∥ ⟪ * ⟫))   = img   (canonical)
--     P₀′      = ν (0 ∷ 1 ∷ []) [] (⟪ * ⟫ ∥ ⟪ K unit ⟫)
--     U[ P₀′]σ₀  = ν (φ acq  (⟪ * ⟫ ∥ ⟪ * ⟫))                            = img′  (drop reduct)
--   The typed R-Drop decrements the FIRST bind block  1 → 0; since  ϕ[1] = drop and
--   ϕ[0] = acq, the untyped RU-Drop flag flip  drop → acq  mirrors it EXACTLY, so
--   U[ P₀′]σ₀  IS the untyped drop reduct — no residual ≈ slack needed on the
--   canonical side.
--
--   THE ROUTE (the third route: not strict image-inversion, not the φ-head-count
--   MEASURE):
--     1. UN-ESCAPE via the KNOWN reverse νφ-comm′ link (Resc ≋ img), delivered as
--        the leading link of `red`'s own RU-Struct — exactly PhiAbsorbNuSwap's
--        "the peel is DELIVERED, not rebuilt".
--     2. the canonical (ν-scoped) drop  RU-Res (RU-Drop)  fires on the STRICT
--        image img, landing on img′.
--     3. REFLECT it to the typed  TR.R-Drop  (a REAL 𝕀 step, consistent with
--        DropNotAdmin), with  U[ P₀′]σ₀ ≡ img′.
--     4. ABSORB any trailing νφ-comm re-escape into the codomain ≈ (≋⇒≈ / ≈-trans),
--        the PhiAbsorbNuSwap variant-2 pattern.
module BorrowedCF.Simulation2.Backward.ReflectPhiEscape where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈; ≈-trans; ≈-refl)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Data.Product using (Σ-syntax; _×_; _,_)

open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- The concrete instance.
------------------------------------------------------------------------

σ₀ : 0 →ₛ 0
σ₀ ()

P₀ : TP.Proc 0
P₀ = TP.ν (1 ∷ 1 ∷ []) [] (TP.⟪ K `drop ·¹ (` 0F) ⟫ TP.∥ TP.⟪ K `unit ⟫)

P₀′ : TP.Proc 0
P₀′ = TP.ν (0 ∷ 1 ∷ []) [] (TP.⟪ * ⟫ TP.∥ TP.⟪ K `unit ⟫)

-- the drop-redex thread under the φ (canonical image body, at Proc 3).
X′ : UP.Proc 3
X′ = UP.⟪ K `drop ·¹ 𝓒[ * × 1F × ` 0F ] ⟫ UP.∥ UP.⟪ * ⟫

-- canonical image  =  U[ P₀ ] σ₀.
img : UP.Proc 0
img = UP.ν (UP.φ UP.drop X′)

img≡ : U[ P₀ ] σ₀ ≡ img
img≡ = refl

-- drop reduct  =  U[ P₀′ ] σ₀.
img′ : UP.Proc 0
img′ = UP.ν (UP.φ UP.acq (UP.⟪ * ⟫ UP.∥ UP.⟪ * ⟫))

img′≡ : U[ P₀′ ] σ₀ ≡ img′
img′≡ = refl

------------------------------------------------------------------------
-- (1) the νφ-comm ESCAPE:  φ pushed OUTSIDE the ν.
------------------------------------------------------------------------

Resc : UP.Proc 0
Resc = UP.φ UP.drop (UP.ν (X′ UP.⋯ₚ assocSwapᵣ 1 2))

-- KNOWN reverse νφ-comm′ link, un-escaping Resc back to the canonical img.
Resc≋img : Resc UP.≋ img
Resc≋img = Eq*.symmetric UP._≋′_ (Eq*.return UP.νφ-comm′)

-- Resc is NOT an image (φ-headed) — the reason strict inversion (RevUCong) fails.
-- (documented; the reflection below never needs image-recognition of Resc.)

-- Resc is ≈-related to the image, so this IS an instance of UpToPhiEngineWF.Base.
Resc≈img : Resc ≈ img
Resc≈img = ≋⇒≈ Resc≋img

------------------------------------------------------------------------
-- (2) the canonical (ν-scoped) drop, firing on the STRICT image.
------------------------------------------------------------------------

drop-canon : img UR.─→ₚ img′
drop-canon = UR.RU-Res (UR.RU-Drop {P = UP.⟪ * ⟫} [] {x = 0F})

------------------------------------------------------------------------
-- (3) the typed reflection:  a REAL R-Drop step  P₀ ─→ₚ P₀′.
------------------------------------------------------------------------

drop-typed : P₀ TR.─→ₚ P₀′
drop-typed = TR.R-Drop {b₁ = 0} {B₁ = 1 ∷ []} {B₂ = []}
                       {P = TP.⟪ K `unit ⟫} {E = []}

------------------------------------------------------------------------
-- Variant 1 :  Q = img′  (post = ε).  The observable φ-drop on the escape,
--   reflected DIRECTLY to the typed R-Drop; codomain ≈ is reflexive.
------------------------------------------------------------------------

red : Resc UR.─→ₚ img′
red = UR.RU-Struct Resc≋img drop-canon ε

reflect-φescape :
  Σ[ P′ ∈ TP.Proc 0 ] (Star TR._─→ₚ_ P₀ P′ × img′ ≈ U[ P′ ] σ₀)
reflect-φescape = P₀′ , (drop-typed ◅ ε) , ≈-refl

------------------------------------------------------------------------
-- Variant 2 :  Q = the ESCAPED reduct  φ acq (ν …)  (post = νφ-comm re-escape).
--   The trailing link is genuinely absorbed by the codomain ≈.
------------------------------------------------------------------------

Qesc : UP.Proc 0
Qesc = UP.φ UP.acq (UP.ν ((UP.⟪ * ⟫ UP.∥ UP.⟪ * ⟫) UP.⋯ₚ assocSwapᵣ 1 2))

img′≋Qesc : img′ UP.≋ Qesc
img′≋Qesc = Eq*.return UP.νφ-comm′

red-esc : Resc UR.─→ₚ Qesc
red-esc = UR.RU-Struct Resc≋img drop-canon img′≋Qesc

reflect-φescape-esc :
  Σ[ P′ ∈ TP.Proc 0 ] (Star TR._─→ₚ_ P₀ P′ × Qesc ≈ U[ P′ ] σ₀)
reflect-φescape-esc =
  P₀′ , (drop-typed ◅ ε) , ≋⇒≈ (Eq*.symmetric UP._≋′_ img′≋Qesc)
