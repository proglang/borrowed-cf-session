{-# OPTIONS --rewriting #-}
-- PROBE: is reshapeEq (Factor2.agda:2118) TRUE for a swapᴿ residue whose `t`
-- has a NON-EMPTY leading φ-run?  Shape argument says NO.
module BorrowedCF.Simulation.Support.Normal.ReshapeProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped using (Flag; acq; drop)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Image using (Slot; sν; sφ; shape; shape-renTel)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; innerOf)
open import BorrowedCF.Simulation.Support.Normal.FactorBase using (bubν⁻; Run; rnil; rφ; Block; bν)
open import BorrowedCF.Simulation.Support.Normal.FrontIndep
  using (splitRun; RunSplit; run; rest; wrun; brest; mkRS)
open import BorrowedCF.Simulation.Support.Normal.Factor using (bswapTel; FRun; frnil; frφ)
open import BorrowedCF.Simulation.Support.Normal.RealiseBase using (shape-bswapTel; runFlags)
open import BorrowedCF.Simulation.Support.Normal.Slots using (gapρ)
open import BorrowedCF.Simulation.Support.Normal.FrontIndep using (FIT; fit→FInner-seed)

open import Data.Fin.Patterns using (0F)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (∷-injectiveʳ)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_)
import Agda.Builtin.Unit as BU
open Nat.Variables

-- The concrete instance mirroring the realise/swapᴿ where-block, but with a
-- `t` that starts with a φ cell (a leading run of length 1).
sP : Tel 0 0
sP = []

aP : Tel 2 2
aP = []

wP : Run aP
wP = rnil

tP : Tel 4 7
tP = tφ acq (` 0F) (tν [])

tP′ : Tel 4 7
tP′ = shift2 aP ++ᵗ renTel tP (bubν⁻ aP)

RSP : RunSplit tP′
RSP = splitRun tP′

rstP : Tel _ 7
rstP = rest RSP

-- LHS telescope (a = []; bswapTel drags the WHOLE leading run of tP′).
telL : ∀ {b} (ζ : b →ᵣ 0)
       (fw : FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν (aP))) (wrun RSP)) → Tel 0 _
telL ζ fw = sP ++ᵗ bswapTel aP ζ fw rstP

-- RHS telescope (the swapᴿ target).
telR : Tel 0 _
telR = sP ++ᵗ tν (aP ++ᵗ tν (renTel tP (gapρ aP wP)))

-- shape of the RHS is fixed: [sν, sν, sφ acq, sν].
shapeR : shape telR ≡ sν ∷ sν ∷ sφ acq ∷ sν ∷ []
shapeR = cong (λ z → sν ∷ sν ∷ z) (shape-renTel tP (gapρ aP wP))

-- shape of the LHS, via shape-bswapTel, is [sν, sφ acq, sν, sν].
shapeL : ∀ {b} (ζ : b →ᵣ 0)
         (fw : FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν (aP))) (wrun RSP)) →
         shape (telL ζ fw) ≡ sν ∷ sφ acq ∷ sν ∷ sν ∷ []
shapeL ζ fw = shape-bswapTel aP ζ fw rstP

-- Therefore any reshapeEq-shaped equality is impossible: the shapes disagree
-- at position 1 (sφ acq vs sν).
reshapeEq-FALSE : ∀ {b} (ζ : b →ᵣ 0)
  (fw : FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν (aP))) (wrun RSP))
  {esL : List (Tm _)} {esR : List (Tm _)} →
  mkNF (telL ζ fw) esL ≡ mkNF telR esR → ⊥
reshapeEq-FALSE ζ fw eq = clash headEq
  where
    shapeEq : shape (telL ζ fw) ≡ shape telR
    shapeEq = cong (λ N → shape (NF.tel N)) eq
    chain : sν ∷ sφ acq ∷ sν ∷ sν ∷ [] ≡ sν ∷ sν ∷ sφ acq ∷ sν ∷ []
    chain = sym (shapeL ζ fw) ■ shapeEq ■ shapeR
    headEq : sφ acq ∷ sν ∷ sν ∷ [] ≡ sν ∷ sφ acq ∷ sν ∷ []
    headEq = ∷-injectiveʳ chain
    clash : (sφ acq ∷ sν ∷ sν ∷ []) ≡ (sν ∷ sφ acq ∷ sν ∷ []) → ⊥
    clash ()

------------------------------------------------------------------------
-- NON-VACUOUS version: a genuine FIT-valid residue (ambient name at n=1),
-- with the front-independence witness fw′ CONSTRUCTED via fit→FInner-seed.
-- The φ cell's channel is ambient (` 0F weakened), so FIT holds, yet the
-- telescope still has a leading φ-run — and reshapeEq's equation is ⊥.
------------------------------------------------------------------------

s1 : Tel 1 1
s1 = []

a1 : Tel 3 3
a1 = []

w1 : Run a1
w1 = rnil

ω0 : 1 →ᵣ 5
ω0 = (idₖ ⦃ Kᵣ ⦄ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2

c1 : Tm 5
c1 = ` 0F ⋯ ω0

t1 : Tel 5 8
t1 = tφ acq c1 (tν [])

t1′ : Tel 5 8
t1′ = shift2 a1 ++ᵗ renTel t1 (bubν⁻ a1)

-- FIT of the source telescope s1 ++ᵗ tν (tν t1′): the single φ cell's channel
-- is ` 0F ⋯ ω0 ⋯ idₖ, front-independent (witnessed by cf = ` 0F).
fitM1 : FIT (idₖ ⦃ Kᵣ ⦄) (s1 ++ᵗ tν (tν t1′))
fitM1 = (` 0F , refl) , BU.tt

FI1 = fit→FInner-seed s1 t1′ fitM1

ζ1 = proj₁ (proj₂ FI1)
fw1 = proj₂ (proj₂ FI1)

rst1 : Tel _ 8
rst1 = rest (splitRun t1′)

telL1 : Tel 1 _
telL1 = s1 ++ᵗ bswapTel a1 ζ1 fw1 rst1

telR1 : Tel 1 _
telR1 = s1 ++ᵗ tν (a1 ++ᵗ tν (renTel t1 (gapρ a1 w1)))

shapeR1 : shape telR1 ≡ sν ∷ sν ∷ sφ acq ∷ sν ∷ []
shapeR1 = cong (λ z → sν ∷ sν ∷ z) (shape-renTel t1 (gapρ a1 w1))

shapeL1 : shape telL1 ≡ sν ∷ sφ acq ∷ sν ∷ sν ∷ []
shapeL1 = shape-bswapTel a1 ζ1 fw1 rst1

-- A genuine, closed contradiction: reshapeEq's equation on this reachable,
-- FIT-valid residue is refuted.
bottom : telL1 ≡ telR1 → ⊥
bottom eq = clash (∷-injectiveʳ (sym shapeL1 ■ cong shape eq ■ shapeR1))
  where
    clash : (sφ acq ∷ sν ∷ sν ∷ []) ≡ (sν ∷ sφ acq ∷ sν ∷ []) → ⊥
    clash ()
