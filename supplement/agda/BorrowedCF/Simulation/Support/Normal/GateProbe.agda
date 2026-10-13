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
open import BorrowedCF.Simulation.Support.Normal.Bubble using (map-⋯-id; telMidᴺ; wkTel-shift2-tν)
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

------------------------------------------------------------------------
-- FIT: nested per-block front-independence of a block-NF telescope.
--   `FIT ω T` (ω : b →ᵣ p the accumulated weakening from ambient base b)
--   means every φ-cell channel is an ambient-base channel `cf ⋯ ω`.
------------------------------------------------------------------------

FIT : ∀ {b p k} → (b →ᵣ p) → Tel p k → Set
FIT ω []             = ⊤
FIT {b} ω (tφ f c t) = (Σ[ cf ∈ Tm b ] c ≡ cf ⋯ ω) × FIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) t
FIT ω (tν t)         = FIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) t

FIT-cong : ∀ {b p k} {ρ ρ′ : b →ᵣ p} → ρ ≗ ρ′ → (t : Tel p k) → FIT ρ t → FIT ρ′ t
FIT-cong h []         fit            = fit
FIT-cong h (tφ f c t) ((cf , ceq) , rest) =
  (cf , (ceq ■ ⋯-cong cf h)) , FIT-cong (λ x → cong (weaken* ⦃ Kᵣ ⦄ 1) (h x)) t rest
FIT-cong h (tν t)     fit            =
  FIT-cong (λ x → cong (weaken* ⦃ Kᵣ ⦄ 2) (h x)) t fit

-- Peel a prefix telescope: FIT over `s ++ᵗ X` gives FIT over X at ω·wkTel s.
FIT-++ᵗ : ∀ {b n p k} (ω : b →ᵣ n) (s : Tel n p) (X : Tel p k) →
          FIT ω (s ++ᵗ X) → FIT (ω ·ₖ wkTel s) X
FIT-++ᵗ ω []         X fit              = fit
FIT-++ᵗ ω (tν s)     X fit              = FIT-++ᵗ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) s X fit
FIT-++ᵗ ω (tφ f c s) X (_ , rest)       = FIT-++ᵗ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) s X rest

-- Keep only the prefix: FIT over `X ++ᵗ Y` gives FIT over X.
FIT-prefix : ∀ {b p k j} (ω : b →ᵣ p) (X : Tel p k) (Y : Tel k j) →
             FIT ω (X ++ᵗ Y) → FIT ω X
FIT-prefix ω []         Y fit              = tt
FIT-prefix ω (tν X)     Y fit              = FIT-prefix (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) X Y fit
FIT-prefix ω (tφ f c X) Y ((cf , ceq) , rest) =
  (cf , ceq) , FIT-prefix (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) X Y rest

-- Build an FRun for a run whose cells are all ambient (FIT at ω·wkTel S).
fitFRun : ∀ {b p j m} (ω : b →ᵣ p) (S : Tel p j) {r : Tel j m} (w : Run r) →
          FIT (ω ·ₖ wkTel S) r → FRun b ω S w
fitFRun ω S rnil _ = frnil ω S
fitFRun {b} ω S (rφ {f = f} {c = c} {r = r′} w′) ((cf , ceq) , rest) =
  subst (λ cc → FRun b ω S (rφ {f = f} {c = cc} {r = r′} w′))
        (fusion cf ω (wkTel S) ■ sym ceq)
        (frφ ω S cf (fitFRun (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) w′ rest′))
  where
    rest′ : FIT ((ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) ·ₖ wkTel (shift1 S)) r′
    rest′ = FIT-cong (λ x → sym (N1 S (ω x))) r′ rest

-- `wkTel (shift2 (tν [])) = weaken*2` (the inner block's own-ν prefix reduces).
wkS2tν[] : ∀ {j} (y : 𝔽 (2 + j)) →
           wkTel (shift2 (tν ([] {2 + j}))) y ≡ weaken* ⦃ Kᵣ ⦄ 2 y
wkS2tν[] y = wkTel-shift2-tν [] y

-- PROJECTION (B-producer, res-seed perm-νν, a=[]): FIT of the source NF
-- telescope yields the FInner carrier for the inner block's leading run.
fit→FInner-seed : ∀ {n j k} (s : Tel n j) (t : Tel (2 + (2 + j)) k) →
                  FIT (idₖ ⦃ Kᵣ ⦄) (s ++ᵗ tν (tν t)) → FInner ([] {2 + j}) t
fit→FInner-seed {n} s t fit =
  n , wkTel s ,
  fitFRun (wkTel s ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν [])) (wrun (splitRun t)) fitRun
  where
    fit-t : FIT (((idₖ ⦃ Kᵣ ⦄ ·ₖ wkTel s) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) t
    fit-t = FIT-++ᵗ (idₖ ⦃ Kᵣ ⦄) s (tν (tν t)) fit
    fit-rr : FIT (((idₖ ⦃ Kᵣ ⦄ ·ₖ wkTel s) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2)
                 (run (splitRun t) ++ᵗ rest (splitRun t))
    fit-rr = subst (FIT (((idₖ ⦃ Kᵣ ⦄ ·ₖ wkTel s) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2))
                   (splits (splitRun t)) fit-t
    fit-run : FIT (((idₖ ⦃ Kᵣ ⦄ ·ₖ wkTel s) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2)
                  (run (splitRun t))
    fit-run = FIT-prefix _ (run (splitRun t)) (rest (splitRun t)) fit-rr
    fitRun : FIT ((wkTel s ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ wkTel (shift2 (tν [])))
                 (run (splitRun t))
    fitRun = FIT-cong (λ z → sym (wkS2tν[] (weaken* ⦃ Kᵣ ⦄ 2 (wkTel s z))))
                      (run (splitRun t)) fit-run
