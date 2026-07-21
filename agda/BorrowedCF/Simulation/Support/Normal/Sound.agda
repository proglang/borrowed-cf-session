-- | Soundness of the normal form: `≋` becomes `~`.
--
--   The twelve ≋′ generators split into three kinds.
--
--     * The four binder transpositions are EXACTLY Normal.Equiv's generators,
--       once `nf-nat` (Normal.Nat) has turned the generator's body renaming into
--       `renNF` and `nf-endo` (Normal.Endo) has re-based it back — they fire at
--       the head, so the prefix telescope is `[]`.
--     * ∥-unit′ is the `unit-del` generator; ∥-assoc′, ν-ext′ and φ-ext′ are
--       outright EQUALITIES of normal forms — `combine` already associates and
--       already extrudes binders, which is what makes `nf` a normaliser at all.
--     * ∥-comm′ is the only one with real content: `combine` puts its second
--       argument's telescope outermost, so commuting the two sides has to move
--       a whole telescope past another one.
module BorrowedCF.Simulation.Support.Normal.Sound where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Endo
open import BorrowedCF.Simulation.Support.Normal.Nat using (NF-≡)

open import Data.List using (List; []; _∷_; map)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Equalities are equivalences.
------------------------------------------------------------------------

≡→~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ N₂
≡→~ refl = ~-refl

------------------------------------------------------------------------
-- The spent unit thread.
------------------------------------------------------------------------

unit-combine : ∀ {n} (N : NF n) →
               combine (mkNF [] (K `unit ∷ [])) N ≡ mkNF (tel N) (K `unit ∷ thr N)
unit-combine (mkNF t es) =
  NF-≡ refl (++ᵗ-idʳ t) (cong (K `unit ∷_) (map-id es))
  where
    map-id : ∀ {k} (xs : List (Tm k)) → map (_⋯ idₖ ⦃ Kᵣ ⦄) xs ≡ xs
    map-id []       = refl
    map-id (x ∷ xs) = cong₂ _∷_ (⋯-id x (λ _ → refl)) (map-id xs)

------------------------------------------------------------------------
-- Soundness.
------------------------------------------------------------------------

≋′⇒~ : ∀ {n} {P Q : Proc n} → P ≋′ Q → nf P ~ nf Q

≋′⇒~ (∥-unit′ {P = P}) =
  ~-trans (≡→~ (unit-combine (nf P))) (Eq*.return (unit-del (tel (nf P)) (thr (nf P))))

≋′⇒~ (ν-swap′ {P = P}) =
  ~-trans (Eq*.return (perm-ν1 [] (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong νNF (nf-endo P (swapᵣ 1 1)))))

≋′⇒~ (ν-comm′ {P = P}) =
  ~-trans (Eq*.return (perm-νν [] (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → νNF (νNF N)) (nf-endo P (assocSwapᵣ 2 2)))))

≋′⇒~ (φ-comm′ {P = P} {x} {y}) =
  ~-trans (Eq*.return (perm-φφ [] x y (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → φNF y (φNF x N)) (nf-endo P (assocSwapᵣ 1 1)))))

≋′⇒~ (νφ-comm′ {P = P} {x}) =
  ~-trans (Eq*.return (perm-νφ [] x (tel (nf P)) (thr (nf P))))
          (≡→~ (sym (cong (λ N → φNF x (νNF N)) (nf-endo P (assocSwapᵣ 1 2)))))

≋′⇒~ (ν-cong′ c) = ~-νNF (≋′⇒~ c)
≋′⇒~ (φ-cong′ c) = ~-φNF (≋′⇒~ c)

≋′⇒~ ∥-comm′  = {!   !}
≋′⇒~ ∥-assoc′ = {!   !}
≋′⇒~ ν-ext′   = {!   !}
≋′⇒~ φ-ext′   = {!   !}
≋′⇒~ (∥-cong′ c) = {!   !}
