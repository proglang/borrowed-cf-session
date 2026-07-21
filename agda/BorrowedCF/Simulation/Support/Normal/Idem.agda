-- | `nf` is idempotent up to `~`: normalising a normal form gives it back.
--
--   This is the second half of `nf-unique : ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉ → N₁ ~ N₂`.  The
--   first half sends the `≋`-chain to a `~`-chain between the normal forms of
--   the two pluggings (Normal.Sound); this module closes the gap between
--   `nf ⌈ N ⌉` and `N` itself.
--
--   The only real content is `nf-pars`, and it is an EQUALITY, not just a `~`:
--   `combine` on two binder-free normal forms degenerates to consing, because
--   every renaming it inserts is the identity.  The single `~` step is the spent
--   `unit` that `pars` puts at the end of the thread list.
module BorrowedCF.Simulation.Support.Normal.Idem where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Equiv

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (++-comm)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

≡→~ : ∀ {n} {N₁ N₂ : NF n} → N₁ ≡ N₂ → N₁ ~ N₂
≡→~ refl = ~-refl

map-idᵣ : ∀ {k} (xs : List (Tm k)) → map (_⋯ idₖ ⦃ Kᵣ ⦄) xs ≡ xs
map-idᵣ []       = refl
map-idᵣ (x ∷ xs) = cong₂ _∷_ (⋯-id x (λ _ → refl)) (map-idᵣ xs)

------------------------------------------------------------------------
-- Normalising a flat parallel composition.
------------------------------------------------------------------------

-- `pars` appends a spent `unit`, and `nf` keeps it: the two differ by exactly
-- that thread, which is what the `unit-del` generator is for.
nf-pars : ∀ {n} (es : List (Tm n)) → nf (pars es) ≡ mkNF [] (es ++ (K `unit ∷ []))
nf-pars []       = refl
nf-pars (e ∷ es) =
  cong (combine (mkNF [] (e ∷ []))) (nf-pars es)
    ■ cong₂ (λ a b → mkNF [] (a ∷ b)) (⋯-id e (λ _ → refl)) (map-idᵣ (es ++ (K `unit ∷ [])))

------------------------------------------------------------------------
-- Idempotence.
------------------------------------------------------------------------

-- Recursion is on the TELESCOPE, not on the packed normal form: `NF` is a
-- record, so `mkNF t es` is not a structurally smaller argument.
nf-plug : ∀ {n k} (t : Tel n k) (es : List (Tm k)) → nf (plug t (pars es)) ~ mkNF t es
nf-plug []       es =
  ~-trans (≡→~ (nf-pars es))
    (~-trans (Eq*.return (perm-thr [] (++-comm es (K `unit ∷ []))))
             (Eq*.return (unit-del [] es)))
nf-plug (tν t)   es = ~-νNF     (nf-plug t es)
nf-plug (tφ f t) es = ~-φNF {f = f} (nf-plug t es)

nf-⌈⌉ : ∀ {n} (N : NF n) → nf ⌈ N ⌉ ~ N
nf-⌈⌉ (mkNF t es) = nf-plug t es
