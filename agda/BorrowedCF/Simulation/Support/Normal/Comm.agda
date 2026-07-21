-- | `combine` commutes up to `~`.
--
--   This is the one ≋′ generator with real content at the normal-form level
--   (Normal.Sound's ∥-comm′): `combine` puts its SECOND argument's telescope
--   outermost, so swapping the two sides has to move a whole telescope past
--   another one.
--
--   The induction is on the FIRST argument's telescope, peeling one binder at a
--   time: Normal.Bubble's `combine-extrudeˡ` moves it out on the left (the hard
--   direction, up to `~`), the induction hypothesis swaps the smaller pair, and
--   `combine-ν` / `combine-φ` puts the binder back on the right (an equality).
--   The second argument varies along the way — its scope grows under each peeled
--   binder — so it stays universally quantified.
module BorrowedCF.Simulation.Support.Normal.Comm where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo
  using (++ᵗ-idʳ; renTel-idᵗ; wkTel-idᵗ; liftId-liftRen; liftId-id)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (NF-≡; subst-++; map-⋯-subst)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (≡→~; map-⋯-id; combine-ν; combine-φ; combine-extrudeˡ-ν; combine-extrudeˡ-φ)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++-comm)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Commutativity.
------------------------------------------------------------------------

comm : ∀ {n j} (t : Tel n j) (es : List (Tm j)) (N : NF n) →
       combine (mkNF t es) N ~ combine N (mkNF t es)

-- With no telescope of its own, the first argument only contributes threads, so
-- the two sides differ by a permutation of the thread list alone.
comm [] es₁ (mkNF {j₂} t₂ es₂) =
  ~-trans (≡→~ eqL)
    (~-trans (Eq*.return (perm-thr t₂ (++-comm (map (_⋯ wkTel t₂) es₁) es₂)))
             (≡→~ (sym eqR)))
  where
    eqL : combine (mkNF [] es₁) (mkNF t₂ es₂)
            ≡ mkNF t₂ (map (_⋯ wkTel t₂) es₁ ++ es₂)
    eqL = cong₂ mkNF (++ᵗ-idʳ t₂)
                     (cong (map (_⋯ wkTel t₂) es₁ ++_) (map-⋯-id (λ _ → refl) es₂))

    hh : ∀ x → subst 𝔽 (renTel-id t₂) (liftRen t₂ (wkTel []) x) ≡ idₖ ⦃ Kᵣ ⦄ x
    hh x = liftId-liftRen t₂ (wkTel []) x ■ liftId-id t₂ (λ _ → refl) x

    eqR : combine (mkNF t₂ es₂) (mkNF [] es₁)
            ≡ mkNF t₂ (es₂ ++ map (_⋯ wkTel t₂) es₁)
    eqR = NF-≡ (renTel-id t₂) (renTel-idᵗ t₂)
            ( subst-++ (renTel-id t₂)
                (map (_⋯ liftRen t₂ (wkTel [])) es₂)
                (map (_⋯ wkTel (renTel t₂ _)) es₁)
            ■ cong₂ _++_ ( map-⋯-subst (renTel-id t₂) hh es₂
                         ■ map-⋯-id (λ _ → refl) es₂ )
                         (map-⋯-subst (renTel-id t₂) (wkTel-idᵗ t₂) es₁) )

comm (tν t) es N =
  ~-trans (combine-extrudeˡ-ν (mkNF t es) N)
    (~-trans (~-νNF (comm t es (renNF N _ (weaken* ⦃ Kᵣ ⦄ 2))))
             (≡→~ (combine-ν N (mkNF t es))))

comm (tφ f t) es N =
  ~-trans (combine-extrudeˡ-φ f (mkNF t es) N)
    (~-trans (~-φNF (comm t es (renNF N _ (weaken* ⦃ Kᵣ ⦄ 1))))
             (≡→~ (combine-φ f N (mkNF t es))))

combine-comm : ∀ {n} (N₁ N₂ : NF n) → combine N₁ N₂ ~ combine N₂ N₁
combine-comm N₁ N₂ = comm (tel N₁) (thr N₁) N₂
