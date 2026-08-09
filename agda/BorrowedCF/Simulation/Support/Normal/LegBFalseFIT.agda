{-# OPTIONS --rewriting #-}
-- MACHINE-CHECKED DISPROOF of Factor2's `legᵇ` (M′ ~ᵇ M) for a FIT-domain
-- swapᴿ residue with a NONEMPTY run `a` AND a `t` carrying a leading φ-run.
-- Invariant: φφcount (number of adjacent φφ pairs in the shape) is preserved
-- by every ~ᵇ generator; the two legᵇ endpoints have φφcount 1 vs 0.
module BorrowedCF.Simulation.Support.Normal.LegBFalseFIT where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped using (Flag; acq; drop)
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Image
  using (Slot; sν; sφ; shape; shape-++ᵗ; shape-renTel)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; innerOf)
open import BorrowedCF.Simulation.Support.Normal.FactorBase using (bubν⁻; Run; rnil; rφ; Block; bnil; bν)
open import BorrowedCF.Simulation.Support.Normal.Factor
  using (_~ᵇ_; _~ᵇ₁_; ν1ᵇ; φφᵇ; thrᵇ; delᵇ; bswpᵇ; bswapTel)
open import BorrowedCF.Simulation.Support.Normal.RealiseBase
  using (shape-bswapTel; runFlags; shape-run)
open import BorrowedCF.Simulation.Support.Normal.Slots using (gapρ)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Empty using (⊥)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

open Nat.Variables
open import Data.Fin.Patterns using (0F)

------------------------------------------------------------------------
-- φφcount : number of adjacent (sφ,sφ) pairs in a slot list.
------------------------------------------------------------------------

φφcount : List Slot → ℕ
φφcount []                     = 0
φφcount (sν     ∷ xs)          = φφcount xs
φφcount (sφ f   ∷ [])          = 0
φφcount (sφ f   ∷ sν     ∷ xs) = φφcount (sν ∷ xs)
φφcount (sφ f   ∷ sφ g   ∷ xs) = suc (φφcount (sφ g ∷ xs))

φφ-++-ν : ∀ (S : List Slot) {R : List Slot} →
          φφcount (S ++ (sν ∷ R)) ≡ φφcount S + φφcount (sν ∷ R)
φφ-++-ν []                = refl
φφ-++-ν (sν ∷ S)          = φφ-++-ν S
φφ-++-ν (sφ f ∷ [])       = refl
φφ-++-ν (sφ f ∷ sν ∷ S)   = φφ-++-ν (sν ∷ S)
φφ-++-ν (sφ f ∷ sφ g ∷ S) = cong suc (φφ-++-ν (sφ g ∷ S))

φφ-run-ν : ∀ (fs : List Flag) {R : List Slot} →
           φφcount (map sφ fs ++ (sν ∷ R)) ≡ (length fs ∸ 1) + φφcount (sν ∷ R)
φφ-run-ν []           = refl
φφ-run-ν (f ∷ [])     = refl
φφ-run-ν (f ∷ g ∷ fs) = cong suc (φφ-run-ν (g ∷ fs))

φφ-run-[] : ∀ (fs : List Flag) → φφcount (map sφ fs) ≡ (length fs ∸ 1)
φφ-run-[] []           = refl
φφ-run-[] (f ∷ [])     = refl
φφ-run-[] (f ∷ g ∷ fs) = cong suc (φφ-run-[] (g ∷ fs))

φφ-φhd : ∀ (x y : Flag) (T : List Slot) → φφcount (sφ x ∷ T) ≡ φφcount (sφ y ∷ T)
φφ-φhd x y []          = refl
φφ-φhd x y (sν   ∷ T)  = refl
φφ-φhd x y (sφ f ∷ T)  = refl

φφ-flagswap : ∀ (S : List Slot) (x y : Flag) (T : List Slot) →
              φφcount (S ++ sφ x ∷ sφ y ∷ T) ≡ φφcount (S ++ sφ y ∷ sφ x ∷ T)
φφ-flagswap []              x y T = cong suc (φφ-φhd y x T)
φφ-flagswap (sν ∷ S)        x y T = φφ-flagswap S x y T
φφ-flagswap (sφ f ∷ [])     x y T = cong suc (φφ-flagswap [] x y T)
φφ-flagswap (sφ f ∷ sν ∷ S) x y T = φφ-flagswap (sν ∷ S) x y T
φφ-flagswap (sφ f ∷ sφ g ∷ S) x y T = cong suc (φφ-flagswap (sφ g ∷ S) x y T)

runBlock : ∀ {n k} (fs : List Flag) (t : Tel n k) → Block t →
           φφcount (map sφ fs ++ shape t) ≡ (length fs ∸ 1) + φφcount (shape t)
runBlock fs []      bnil =
  cong φφcount (++-identityʳ (map sφ fs)) ■ φφ-run-[] fs ■ sym (+-identityʳ _)
runBlock fs (tν t′) bν   = φφ-run-ν fs {R = shape t′}

------------------------------------------------------------------------
-- φφcount ∘ shape ∘ tel is invariant under every ~ᵇ generator, hence ~ᵇ.
------------------------------------------------------------------------

Φ : ∀ {n} → NF n → ℕ
Φ N = φφcount (shape (tel N))

bstep : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵇ₁ N₂ → Φ N₁ ≡ Φ N₂
bstep (ν1ᵇ s t es) =
  cong φφcount ( shape-++ᵗ s (tν t)
               ■ cong (λ z → shape s ++ (sν ∷ z)) (sym (shape-renTel t (swapᵣ 1 1)))
               ■ sym (shape-++ᵗ s (tν (renTel t (swapᵣ 1 1)))) )
bstep (φφᵇ s x y c d t es) =
    cong φφcount (shape-++ᵗ s (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t)))
  ■ φφ-flagswap (shape s) x y (shape t)
  ■ sym ( cong φφcount (shape-++ᵗ s (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t (assocSwapᵣ 1 1)))))
        ■ cong (λ z → φφcount (shape s ++ (sφ y ∷ sφ x ∷ z))) (shape-renTel t (assocSwapᵣ 1 1)) )
bstep (thrᵇ t p)  = refl
bstep (delᵇ t es) = refl
bstep (bswpᵇ s {a} ra {rb} {wb} ζ fw {t} bt es) =
    (cong φφcount shapeEq₁ ■ φφcanon₁)
  ■ cong (φφcount (shape s) +_) reassoc
  ■ sym (cong φφcount shapeEq₂ ■ φφcanon₂)
  where
    fa = runFlags ra
    fb = runFlags wb
    A = length fa ∸ 1
    B = length fb ∸ 1
    Ct = φφcount (shape t)
    canon₁ : List Slot
    canon₁ = shape s ++ (sν ∷ (map sφ fa ++ (sν ∷ (map sφ fb ++ shape t))))
    canon₂ : List Slot
    canon₂ = shape s ++ (sν ∷ (map sφ fb ++ (sν ∷ (map sφ fa ++ shape t))))
    shapeEq₁ : shape (tel (mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ t))) es)) ≡ canon₁
    shapeEq₁ =
        shape-++ᵗ s (tν (a ++ᵗ tν (rb ++ᵗ t)))
      ■ cong (λ z → shape s ++ (sν ∷ z)) (shape-++ᵗ a (tν (rb ++ᵗ t)))
      ■ cong (λ z → shape s ++ (sν ∷ (shape a ++ (sν ∷ z)))) (shape-++ᵗ rb t)
      ■ cong (λ z → shape s ++ (sν ∷ (z ++ (sν ∷ (shape rb ++ shape t))))) (shape-run ra)
      ■ cong (λ z → shape s ++ (sν ∷ (map sφ fa ++ (sν ∷ (z ++ shape t))))) (shape-run wb)
    shapeEq₂ : shape (s ++ᵗ bswapTel a ζ fw t) ≡ canon₂
    shapeEq₂ =
        shape-++ᵗ s (bswapTel a ζ fw t)
      ■ cong (shape s ++_) (shape-bswapTel a ζ fw t)
      ■ cong (λ z → shape s ++ (sν ∷ (map sφ fb ++ (sν ∷ (z ++ shape t))))) (shape-run ra)
    φφcanon₁ : φφcount canon₁ ≡ φφcount (shape s) + (A + (B + Ct))
    φφcanon₁ =
        φφ-++-ν (shape s)
      ■ cong (φφcount (shape s) +_)
          (φφ-run-ν fa ■ cong (A +_) (runBlock fb t bt))
    φφcanon₂ : φφcount canon₂ ≡ φφcount (shape s) + (B + (A + Ct))
    φφcanon₂ =
        φφ-++-ν (shape s)
      ■ cong (φφcount (shape s) +_)
          (φφ-run-ν fb ■ cong (B +_) (runBlock fa t bt))
    reassoc : A + (B + Ct) ≡ B + (A + Ct)
    reassoc = sym (+-assoc A B Ct) ■ cong (_+ Ct) (+-comm A B) ■ +-assoc B A Ct

binv : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ᵇ N₂ → Φ N₁ ≡ Φ N₂
binv ε             = refl
binv (fwd g ◅ c)   = bstep g   ■ binv c
binv (bwd g ◅ c)   = sym (bstep g) ■ binv c

------------------------------------------------------------------------
-- A GENUINE FIT-valid swapᴿ residue with a ≠ [] AND t leading-φ (n = 1,
-- ambient channels), whose legᵇ endpoints have φφcount 1 vs 0.
------------------------------------------------------------------------

import Agda.Builtin.Unit as BU
open import BorrowedCF.Simulation.Support.Normal.FrontIndep using (FIT)
open import BorrowedCF.Simulation.Support.Normal.Slots using (Res; swapᴿ)

ω1 : 1 →ᵣ 3
ω1 = idₖ ⦃ Kᵣ ⦄ ·ₖ weaken* ⦃ Kᵣ ⦄ 2

ca : Tm 3
ca = ` 0F ⋯ ω1

a1 : Tel 3 4
a1 = tφ acq ca []

w1 : Run a1
w1 = rφ rnil

ω2 : 1 →ᵣ 6
ω2 = (ω1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1) ·ₖ weaken* ⦃ Kᵣ ⦄ 2

ct : Tm 6
ct = ` 0F ⋯ ω2

t1 : Tel 6 9
t1 = tφ drop ct (tν [])

fit1 : FIT (idₖ ⦃ Kᵣ ⦄) (tν (a1 ++ᵗ tν t1))
fit1 = (` 0F , refl) , ((` 0F , refl) , BU.tt)

-- The residue exists (realise MUST be total on it):
r1 : Res (mkNF (tν (a1 ++ᵗ tν t1)) [])
         (mkNF (tν (a1 ++ᵗ tν (renTel t1 (gapρ a1 w1)))) (map (_⋯ liftRen t1 (gapρ a1 w1)) []))
r1 = swapᴿ [] {a = a1} w1 t1 {es = []} refl refl refl fit1

-- The two legᵇ endpoints (realise's output M′ and the residue target M):
Mp1 : NF 1
Mp1 = mkNF (tν (tν (shift2 a1 ++ᵗ renTel t1 (bubν⁻ a1)))) (map (_⋯ liftRen t1 (bubν⁻ a1)) [])

M1 : NF 1
M1 = mkNF (tν (a1 ++ᵗ tν (renTel t1 (gapρ a1 w1)))) (map (_⋯ liftRen t1 (gapρ a1 w1)) [])

ΦMp1 : Φ Mp1 ≡ 1
ΦMp1 = refl

ΦM1 : Φ M1 ≡ 0
ΦM1 = refl

-- Hence legᵇ (M′ ~ᵇ M) is FALSE for this in-domain residue.
legᵇ-FALSE : Mp1 ~ᵇ M1 → ⊥
legᵇ-FALSE h = 1≢0 (sym ΦMp1 ■ binv h ■ ΦM1)
  where
    1≢0 : 1 ≡ 0 → ⊥
    1≢0 ()
