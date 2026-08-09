{-# OPTIONS --rewriting #-}
-- MACHINE-CHECKED DISPROOF of the `DNM : D_N ≡ D_M` obligation inside
-- Factor2.agda's `realise`/`swapᴿ` clause (the `legᵇ` two-swap crux).
--
-- `DNM = NF-≡ leafEq telEqD thrEqD` forces, on the THREAD component,
--   thrEqD : subst leafEq (map (_⋯ σ_N) es) ≡ map (_⋯ (liftRen t gρ ·ₖ σ_M)) es
-- for the ARBITRARY thread list `es` carried by the `swapᴿ` residue.  The
-- `swapᴿ` constructor (Slots.agda:312) constrains only the TELESCOPE
-- (`FIT idₖ T`); it puts NO front-independence carrier on `es`.  So thrEqD
-- can hold only if the two thread renamings agree GLOBALLY:
--   σ_N ≗ liftRen t gρ ·ₖ σ_M   (up to the trivial leafEq transport).
--
-- Instance a = [] (the `perm-νν` seed), t = rst = tν [], run rb = [] (so the
-- drag is `frnil`, gρ = gapρ [] rnil = assocSwapᵣ 2 2, σ_N = liftId rst
-- (bubν⁻ (tν a)), σ_M = liftId (renTel rst gρ) (bubν⁻ (tν a))).  The two
-- renamings AGREE on the block-interior slots 0,1 (p0/p1) but DISAGREE at
-- slot 2 (the first ambient slot past the block): σ_N sends 2 ↦ 3 while
-- liftRen t gρ ·ₖ σ_M sends 2 ↦ 0.  Hence for any `es` mentioning variable
-- 2 (e.g. `es = [ ` 2 ]`), thrEqD FAILS — DNM is FALSE as stated.
module BorrowedCF.Simulation.Support.Normal.DNMProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; innerOf)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.FactorBase using (bubν⁻; rnil; Run)
open import BorrowedCF.Simulation.Support.Normal.Slots using (gapρ)

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ)

open Nat.Variables

-- a = [] : Tel 2 2, i = 2 ; t = rst = tν [] : Tel 4 6 ; gρ = assocSwapᵣ 2 2 on 𝔽 4.
a₀ : Tel 2 2
a₀ = []

rst₀ : Tel 4 6
rst₀ = tν []

gρ₀ : 4 →ᵣ 4
gρ₀ = gapρ a₀ rnil

bub₀ : 4 →ᵣ 4
bub₀ = bubν⁻ (tν a₀)

-- σ_N and (liftRen t gρ ·ₖ σ_M), the two thread renamings on 𝔽 6.
σN : 6 →ᵣ 6
σN = liftId rst₀ bub₀

σMcomp : 6 →ᵣ 6
σMcomp = liftRen rst₀ gρ₀ ·ₖ liftId (renTel rst₀ gρ₀) bub₀

-- Agreement on the two block-interior slots.
p0 : σN zero ≡ σMcomp zero
p0 = refl

p1 : σN (suc zero) ≡ σMcomp (suc zero)
p1 = refl

-- DISAGREEMENT at slot 2 (first ambient slot).  Read off via toℕ.
σN-2  : toℕ (σN (suc (suc zero)))     ≡ 4
σN-2  = refl

σM-2  : toℕ (σMcomp (suc (suc zero))) ≡ 2
σM-2  = refl

-- Hence the two renamings differ at 2 (4 vs 2), so `thrEqD` (and `DNM`) is
-- false for any thread list mentioning variable 2.
4≢2 : (4 ≡ 2) → ⊥
4≢2 ()

DNM-thread-FALSE : σN (suc (suc zero)) ≡ σMcomp (suc (suc zero)) → ⊥
DNM-thread-FALSE eq = 4≢2 (sym σN-2 ■ cong toℕ eq ■ σM-2)
