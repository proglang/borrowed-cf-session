-- | The witness renaming of a `~` chain preserves the bound/ambient boundary.
--
--   Every `~₁` generator's renaming is `liftId t ξ` with `ξ` a transposition
--   acting at a binder position, and each such `ξ` is the identity on the
--   `wkʳ`-range (`swap11-wk` / `aswap-wk`).  So the witness's `fwd` carries
--   ambient variables (the `wkTel`-range of one side's telescope) to ambient
--   variables of the other side — pointwise, `fwd ∘ wkTel (tel N₁) ≗
--   wkTel (tel N₂)`.  `amb` is stated against each side's OWN `wkTel`, so
--   composition along the chain is plain transitivity through the middle
--   normal form's `wkTel`, exactly as `Witness.witness-trans`.
--
--   Downstream (`Backward.PinLSplit`) the payoff is `bound-pres`: a variable
--   that is NOT ambient has a NON-ambient image, separating a telescope-bound
--   redex channel from the `BσWk`-images of ambient σ-values.
module BorrowedCF.Simulation.Support.Normal.WitnessAmb where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo using (wkTel-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Shift using (liftId-wkTel)
open import BorrowedCF.Simulation.Support.Normal.CongL using (swap11-wk; aswap-wk)
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Sound using (≋⇒~)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (Witness; mkW; fwd; bwd; inv₁; inv₂;
         witness-refl; witness-sym; witness-trans; ~₁-witness)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using ()
  renaming (fwd to sfwd; bwd to sbwd)

open Nat.Variables

------------------------------------------------------------------------
-- The enriched witness.
------------------------------------------------------------------------

record AmbWitness {n} (N₁ N₂ : NF n) : Set where
  constructor mkA
  field
    w   : Witness N₁ N₂
    amb : ∀ y → fwd w (wkTel (tel N₁) y) ≡ wkTel (tel N₂) y

open AmbWitness public

------------------------------------------------------------------------
-- The two consequences the consumers need.
------------------------------------------------------------------------

amb-bwd : ∀ {n} {N₁ N₂ : NF n} (a : AmbWitness N₁ N₂) →
          ∀ y → bwd (w a) (wkTel (tel N₂) y) ≡ wkTel (tel N₁) y
amb-bwd {N₁ = N₁} a y =
  cong (bwd (w a)) (sym (amb a y)) ■ inv₁ (w a) (wkTel (tel N₁) y)

bound-pres : ∀ {n} {N₁ N₂ : NF n} (a : AmbWitness N₁ N₂) {x} →
             (∀ y → x ≢ wkTel (tel N₁) y) →
             ∀ y → fwd (w a) x ≢ wkTel (tel N₂) y
bound-pres a nb y feq =
  nb y (sym (inv₁ (w a) _) ■ cong (bwd (w a)) feq ■ amb-bwd a y)

------------------------------------------------------------------------
-- The groupoid structure, mirroring Normal.Witness.
------------------------------------------------------------------------

ambwitness-refl : ∀ {n} {N : NF n} → AmbWitness N N
ambwitness-refl {N = mkNF t es} = mkA witness-refl (λ _ → refl)

ambwitness-sym : ∀ {n} {N₁ N₂ : NF n} → AmbWitness N₁ N₂ → AmbWitness N₂ N₁
ambwitness-sym {N₁ = mkNF t₁ es₁} {N₂ = mkNF t₂ es₂} a =
  mkA (witness-sym (w a)) (amb-bwd a)

ambwitness-trans : ∀ {n} {N₁ N₂ N₃ : NF n} →
                   AmbWitness N₁ N₂ → AmbWitness N₂ N₃ → AmbWitness N₁ N₃
ambwitness-trans {N₁ = mkNF t₁ es₁} {N₂ = mkNF t₂ es₂} {N₃ = mkNF t₃ es₃} a₁ a₂ =
  mkA (witness-trans (w a₁) (w a₂))
      (λ y → cong (fwd (w a₂)) (amb a₁ y) ■ amb a₂ y)

------------------------------------------------------------------------
-- One generator, one boundary proof.
------------------------------------------------------------------------

~₁-ambwitness : ∀ {n} {N₁ N₂ : NF n} → N₁ ~₁ N₂ → AmbWitness N₁ N₂
~₁-ambwitness (perm-ν1 s t es) = mkA (~₁-witness (perm-ν1 s t es)) fix
  where
    fix : ∀ y → liftId t (swapᵣ 1 1) (wkTel (s ++ᵗ tν t) y) ≡ wkTel (s ++ᵗ tν t) y
    fix y = cong (liftId t (swapᵣ 1 1)) (wkTel-++ᵗ s (tν t) y)
              ■ liftId-wkTel t (swapᵣ 1 1) (weaken* ⦃ Kᵣ ⦄ 2 (wkTel s y))
              ■ cong (wkTel t) (swap11-wk (wkTel s y))
              ■ sym (wkTel-++ᵗ s (tν t) y)

~₁-ambwitness (perm-νν s t es) = mkA (~₁-witness (perm-νν s t es)) fix
  where
    fix : ∀ y → liftId t (assocSwapᵣ 2 2) (wkTel (s ++ᵗ tν (tν t)) y)
                  ≡ wkTel (s ++ᵗ tν (tν t)) y
    fix y = cong (liftId t (assocSwapᵣ 2 2)) (wkTel-++ᵗ s (tν (tν t)) y)
              ■ liftId-wkTel t (assocSwapᵣ 2 2)
                  (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ 2 (wkTel s y)))
              ■ cong (wkTel t) (aswap-wk 2 2 (wkTel s y))
              ■ sym (wkTel-++ᵗ s (tν (tν t)) y)

~₁-ambwitness (perm-φφ s x y t es) = mkA (~₁-witness (perm-φφ s x y t es)) fix
  where
    fix : ∀ z → liftId t (assocSwapᵣ 1 1) (wkTel (s ++ᵗ tφ x (tφ y t)) z)
                  ≡ wkTel (s ++ᵗ tφ y (tφ x t)) z
    fix z = cong (liftId t (assocSwapᵣ 1 1)) (wkTel-++ᵗ s (tφ x (tφ y t)) z)
              ■ liftId-wkTel t (assocSwapᵣ 1 1)
                  (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 1 (wkTel s z)))
              ■ cong (wkTel t) (aswap-wk 1 1 (wkTel s z))
              ■ sym (wkTel-++ᵗ s (tφ y (tφ x t)) z)

~₁-ambwitness (perm-νφ s x t es) = mkA (~₁-witness (perm-νφ s x t es)) fix
  where
    fix : ∀ z → liftId t (assocSwapᵣ 1 2) (wkTel (s ++ᵗ tν (tφ x t)) z)
                  ≡ wkTel (s ++ᵗ tφ x (tν t)) z
    fix z = cong (liftId t (assocSwapᵣ 1 2)) (wkTel-++ᵗ s (tν (tφ x t)) z)
              ■ liftId-wkTel t (assocSwapᵣ 1 2)
                  (weaken* ⦃ Kᵣ ⦄ 1 (weaken* ⦃ Kᵣ ⦄ 2 (wkTel s z)))
              ■ cong (wkTel t) (aswap-wk 1 2 (wkTel s z))
              ■ sym (wkTel-++ᵗ s (tφ x (tν t)) z)

~₁-ambwitness (perm-thr t p)  = mkA (~₁-witness (perm-thr t p))  (λ _ → refl)
~₁-ambwitness (unit-del t es) = mkA (~₁-witness (unit-del t es)) (λ _ → refl)

------------------------------------------------------------------------
-- The payoff.
------------------------------------------------------------------------

~-ambwitness : ∀ {n} {N₁ N₂ : NF n} → N₁ ~ N₂ → AmbWitness N₁ N₂
~-ambwitness ε             = ambwitness-refl
~-ambwitness (sfwd g ◅ c) = ambwitness-trans (~₁-ambwitness g) (~-ambwitness c)
~-ambwitness (sbwd g ◅ c) =
  ambwitness-trans (ambwitness-sym (~₁-ambwitness g)) (~-ambwitness c)

≋-ambwitness : ∀ {n} {P Q : Proc n} → P ≋ Q → AmbWitness (nf P) (nf Q)
≋-ambwitness c = ~-ambwitness (≋⇒~ c)
