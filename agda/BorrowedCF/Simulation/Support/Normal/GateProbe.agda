-- | SCRATCH verify-first probe (Factor2 FI-carrier gate).  NON-authoritative:
--   confirms that a front-independence carrier `FInner` on the residue feeds
--   the FRun-parameterised `bswpᵇ` in realise's `swapᴿ` case with matching
--   telescopes/renamings.  Delete once threaded into Slots/Factor2.
module BorrowedCF.Simulation.Support.Normal.GateProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.FactorBase
open import BorrowedCF.Simulation.Support.Normal.Factor
open import BorrowedCF.Simulation.Support.Normal.Endo using (++ᵗ-idʳ)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2)

open import Data.List using (List; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

record RunSplit {n k} (t : Tel n k) : Set where
  constructor mkRS
  field
    {mid}  : ℕ
    run    : Tel n mid
    rest   : Tel mid k
    wrun   : Run run
    brest  : Block rest
    splits : t ≡ run ++ᵗ rest
open RunSplit

splitRun : ∀ {n k} (t : Tel n k) → RunSplit t
splitRun t with headView t
... | vrun r          = mkRS _ [] r bnil (sym (++ᵗ-idʳ _))
... | vν {s = s} rs u = mkRS s (tν u) rs bν refl

-- Front-independence carried by a `swapᴿ` residue: an FRun witness for the
-- inner block's leading run, front-independent w.r.t. the outer block.
FInner : ∀ {j i k} (a : Tel (2 + j) i) (t : Tel (2 + i) k) → Set
FInner {j} a t = Σ[ b ∈ ℕ ] Σ[ ζ ∈ b →ᵣ j ]
                 FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν a)) (wrun (splitRun t))

-- THE GATE: realise's swapᴿ `~ᵇ` leg — feed the carried FRun into `bswpᵇ`.
-- Phrased over the already-split inner tail (the `with splitRun t` step that
-- turns `FInner a t` into this shape is definitional in real realise).
gate-bswp : ∀ {n j i m k} (s : Tel n j) {a : Tel (2 + j) i} (w : Run a)
            {rb : Tel (2 + i) m} (wb : Run rb) {rest : Tel m k} (brest : Block rest)
            (es : List (Tm k)) (b : ℕ) (ζ : b →ᵣ j)
            (fw : FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν a)) wb) →
            mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ rest))) es
              ~ᵇ mkNF (s ++ᵗ bswapTel a ζ fw rest) (map (_⋯ bswapRen a ζ fw rest) es)
gate-bswp s w wb brest es b ζ fw = Eq*.return (bswpᵇ s w ζ fw brest es)
