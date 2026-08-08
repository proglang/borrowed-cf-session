-- | Front-independence for the linked-φ factorisation (Normal.Factor2).
--
--   Under linked-φ a `tφ` binder carries a channel, and the FRun-parameterised
--   block-swap `bswpᵇ` (Normal.Factor) may only fire when the swapped block's
--   run is FRONT-INDEPENDENT: every run cell channel points to the ambient
--   base (a real `new`-bound channel), never to a sibling block's ν.  This
--   module supplies:
--
--     * `FIT ω T` — nested per-block front-independence of a block-NF
--       telescope: every φ-cell channel is an ambient-base image `cf ⋯ ω`,
--       with `ω : b →ᵣ p` the accumulated weakening from the ambient base `b`.
--     * `fitFRun` — builds the per-run `FRun` witness from `FIT` (front cells
--       are ambient), via `fusion` and the `N1` weakening naturality.
--     * `FInner a t` — the carrier a `swapᴿ` residue must hold: an FRun for
--       the inner block's leading run (`wrun (splitRun t)`).
--     * `fit→FInner-seed` — the B-producer projection: at the `perm-νν` seed
--       position `s ++ᵗ tν (tν t)` (outer run `a = []`), `FIT` of the source
--       telescope yields `FInner [] t`.
module BorrowedCF.Simulation.Support.Normal.FrontIndep where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.FactorBase
open import BorrowedCF.Simulation.Support.Normal.Factor
open import BorrowedCF.Simulation.Support.Normal.Endo using (++ᵗ-idʳ)
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2; shift1)
open import BorrowedCF.Simulation.Support.Normal.Bubble using (wkTel-shift2-tν)

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open Nat.Variables

------------------------------------------------------------------------
-- Splitting a telescope at the end of its leading run.
------------------------------------------------------------------------

record RunSplit {n k} (t : Tel n k) : Set where
  constructor mkRS
  field
    {mid}  : ℕ
    run    : Tel n mid
    rest   : Tel mid k
    wrun   : Run run
    brest  : Block rest
    splits : t ≡ run ++ᵗ rest
open RunSplit public

splitRun : ∀ {n k} (t : Tel n k) → RunSplit t
splitRun t with headView t
... | vrun r          = mkRS _ [] r bnil (sym (++ᵗ-idʳ _))
... | vν {s = s} rs u = mkRS s (tν u) rs bν refl

------------------------------------------------------------------------
-- The front-independence carrier a `swapᴿ` residue holds.
------------------------------------------------------------------------

-- An FRun witness for the inner block's leading run, front-independent
-- w.r.t. the outer block `tν a`.
FInner : ∀ {j i k} (a : Tel (2 + j) i) (t : Tel (2 + i) k) → Set
FInner {j} a t = Σ[ b ∈ ℕ ] Σ[ ζ ∈ b →ᵣ j ]
                 FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (shift2 (tν a)) (wrun (splitRun t))

------------------------------------------------------------------------
-- FIT: nested per-block front-independence of a block-NF telescope.
------------------------------------------------------------------------

FIT : ∀ {b p k} → (b →ᵣ p) → Tel p k → Set
FIT ω []             = ⊤
FIT {b} ω (tφ f c t) = (Σ[ cf ∈ Tm b ] c ≡ cf ⋯ ω) × FIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) t
FIT ω (tν t)         = FIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) t

FIT-cong : ∀ {b p k} {ρ ρ′ : b →ᵣ p} → ρ ≗ ρ′ → (t : Tel p k) → FIT ρ t → FIT ρ′ t
FIT-cong h []         fit                  = fit
FIT-cong h (tφ f c t) ((cf , ceq) , rest)  =
  (cf , (ceq ■ ⋯-cong cf h)) , FIT-cong (λ x → cong (weaken* ⦃ Kᵣ ⦄ 1) (h x)) t rest
FIT-cong h (tν t)     fit                  =
  FIT-cong (λ x → cong (weaken* ⦃ Kᵣ ⦄ 2) (h x)) t fit

-- Peel a prefix telescope: FIT over `s ++ᵗ X` gives FIT over X at ω·wkTel s.
FIT-++ᵗ : ∀ {b n p k} (ω : b →ᵣ n) (s : Tel n p) (X : Tel p k) →
          FIT ω (s ++ᵗ X) → FIT (ω ·ₖ wkTel s) X
FIT-++ᵗ ω []         X fit        = fit
FIT-++ᵗ ω (tν s)     X fit        = FIT-++ᵗ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) s X fit
FIT-++ᵗ ω (tφ f c s) X (_ , rest) = FIT-++ᵗ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) s X rest

-- Keep only the prefix: FIT over `X ++ᵗ Y` gives FIT over X.
FIT-prefix : ∀ {b p k j} (ω : b →ᵣ p) (X : Tel p k) (Y : Tel k j) →
             FIT ω (X ++ᵗ Y) → FIT ω X
FIT-prefix ω []         Y fit                  = tt
FIT-prefix ω (tν X)     Y fit                  = FIT-prefix (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) X Y fit
FIT-prefix ω (tφ f c X) Y ((cf , ceq) , rest)  =
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

------------------------------------------------------------------------
-- The B-producer projection (res-seed perm-νν, outer run a = []).
------------------------------------------------------------------------

-- `wkTel (shift2 (tν [])) = weaken*2` (the inner block's own-ν prefix).
wkS2tν[] : ∀ {j} (y : 𝔽 (2 + j)) →
           wkTel (shift2 (tν ([] {2 + j}))) y ≡ weaken* ⦃ Kᵣ ⦄ 2 y
wkS2tν[] y = wkTel-shift2-tν [] y

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
