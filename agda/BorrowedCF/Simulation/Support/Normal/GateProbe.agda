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
open import BorrowedCF.Simulation.Support.Normal.Endo using (++ᵗ-idʳ; liftId-liftRen)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2; shift1)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; renTel-id; innerOf)
open import BorrowedCF.Simulation.Support.Normal.Bubble using (map-⋯-id; telMidᴺ)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (map-fuse; subst-tφ; subst-++ᵗ; subst-■; NF-≡; renTel-++ᵗ; innerOf-++ᵗ;
         map-⋯-subst; innerOf-renTel)

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

dragᵩ : ∀ {b p j m k} (ω : b →ᵣ p) (S : Tel p j) {r : Tel j m} {w : Run r}
             (fw : FRun b ω S w) (t : Tel m k) (es : List (Tm k)) →
             mkNF (S ++ᵗ (r ++ᵗ t)) es ~ᵩ mkNF (dragTel ω S fw t) (map (_⋯ dragRen ω S fw t) es)
dragᵩ ω S (frnil _ _) t es =
  ≡→~ᵩ (cong (mkNF (S ++ᵗ t)) (sym (map-⋯-id (λ _ → refl) es)))
dragᵩ {b} {p} {j} ω S (frφ {f = f} _ _ cf {r = r} fw) t es =
  ~ᵩ-trans (bubbleφᵩ⁻ f (cf ⋯ ω) S (r ++ᵗ t) es)
    (~ᵩ-trans (≡→~ᵩ eqA)
      (~ᵩ-trans (~ᵩ-φNF (cf ⋯ ω)
                  (dragᵩ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) fw
                              (retail t (tailRen r (bubφ⁻ S)))
                              (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)))
               (≡→~ᵩ (cong (mkNF (dragTel ω S (frφ ω S cf fw) t))
                          (map-fuse (liftId (r ++ᵗ t) (bubφ⁻ S))
                                    (dragRen (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) fw
                                             (retail t (tailRen r (bubφ⁻ S)))) es)))))
  where
    telReconcile : subst (Tel (1 + j)) (renTel-id (r ++ᵗ t)) (renTel (r ++ᵗ t) (bubφ⁻ S))
                     ≡ r ++ᵗ retail t (tailRen r (bubφ⁻ S))
    telReconcile =
      cong (λ e → subst (Tel (1 + j)) e (renTel (r ++ᵗ t) (bubφ⁻ S)))
           (≡-irrelevant (renTel-id (r ++ᵗ t))
             (innerOf-++ᵗ r t (1 + j) ■ (cong (innerOf t) (renTel-id r) ■ renTel-id t)))
        ■ subst-■ (Tel (1 + j)) (innerOf-++ᵗ r t (1 + j))
            (cong (innerOf t) (renTel-id r) ■ renTel-id t) (renTel (r ++ᵗ t) (bubφ⁻ S))
        ■ cong (subst (Tel (1 + j)) (cong (innerOf t) (renTel-id r) ■ renTel-id t))
               (renTel-++ᵗ r t (bubφ⁻ S))
        ■ subst-■ (Tel (1 + j)) (cong (innerOf t) (renTel-id r)) (renTel-id t)
            (renTel r (bubφ⁻ S) ++ᵗ renTel t (liftRen r (bubφ⁻ S)))
        ■ cong (subst (Tel (1 + j)) (renTel-id t))
               ( telMidᴺ (renTel-id r) (renTel r (bubφ⁻ S)) t (λ y → refl)
               ■ cong (_++ᵗ renTel t (tailRen r (bubφ⁻ S)))
                      (runFixed (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) (bubφ⁻ S) (λ x → FIX S (ω x)) fw) )
        ■ subst-++ᵗ r (renTel-id t) (renTel t (tailRen r (bubφ⁻ S)))

    eqA : mkNF (tφ f (cf ⋯ ω) (shift1 S ++ᵗ renTel (r ++ᵗ t) (bubφ⁻ S)))
               (map (_⋯ liftRen (r ++ᵗ t) (bubφ⁻ S)) es)
            ≡ mkNF (tφ f (cf ⋯ ω) (shift1 S ++ᵗ (r ++ᵗ retail t (tailRen r (bubφ⁻ S)))))
                   (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)
    eqA = NF-≡ (renTel-id (r ++ᵗ t))
            ( subst-tφ (renTel-id (r ++ᵗ t)) f (cf ⋯ ω) (shift1 S ++ᵗ renTel (r ++ᵗ t) (bubφ⁻ S))
            ■ cong (tφ f (cf ⋯ ω))
                   ( subst-++ᵗ (shift1 S) (renTel-id (r ++ᵗ t)) (renTel (r ++ᵗ t) (bubφ⁻ S))
                   ■ cong (shift1 S ++ᵗ_) telReconcile ) )
            ( map-⋯-subst (renTel-id (r ++ᵗ t)) (λ x → liftId-liftRen (r ++ᵗ t) (bubφ⁻ S) x) es )
