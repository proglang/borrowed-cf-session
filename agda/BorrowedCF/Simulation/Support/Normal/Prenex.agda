-- | Every untyped process is ≋-equal to a prenex normal form.
--
--   `prenex P` returns a binder telescope over a flat thread list together with
--   the ≋ witness.  The recursion is WELL-FOUNDED on `size` (Normal.Form), not
--   structural: the ∥ case renames the LEFT component by the right component's
--   telescope weakening before recursing, and `size` is renaming-invariant
--   (`size-⋯ₚ`).  No {-# TERMINATING #-} pragma.
--
--   The two extrusion generators do all the work:
--     ν-ext′ : P ∥ ν Q     ≋′ ν   ((P ⋯ₚ weaken* 2) ∥ Q)
--     φ-ext′ : P ∥ φ x Q   ≋′ φ x ((P ⋯ₚ weaken* 1) ∥ Q)
--   iterated along a telescope by `tel-ext`.
module BorrowedCF.Simulation.Support.Normal.Prenex where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _,_)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

≡→≋ : ∀ {n} {P Q : Proc n} → P ≡ Q → P ≋ Q
≡→≋ refl = ε

≋-sym : ∀ {n} {P Q : Proc n} → P ≋ Q → Q ≋ P
≋-sym = Eq*.symmetric _

⋯ₚ-idᵣ : ∀ {n} (P : Proc n) {ρ : n →ᵣ n} → ρ ≗ idₖ → P ⋯ₚ ρ ≡ P
⋯ₚ-idᵣ ⟪ e ⟫   eq = cong ⟪_⟫ (⋯-id e eq)
⋯ₚ-idᵣ (P ∥ Q) eq = cong₂ _∥_ (⋯ₚ-idᵣ P eq) (⋯ₚ-idᵣ Q eq)
⋯ₚ-idᵣ (ν P)   eq = cong ν     (⋯ₚ-idᵣ P (id↑* 2 eq))
⋯ₚ-idᵣ (φ x P) eq = cong (φ x) (⋯ₚ-idᵣ P (id↑ eq))

------------------------------------------------------------------------
-- Congruence and extrusion along a telescope.
------------------------------------------------------------------------

plug-cong : ∀ {n k} (t : Tel n k) {X Y : Proc k} → X ≋ Y → plug t X ≋ plug t Y
plug-cong []       c = c
plug-cong (tν t)   c = ν-cong (plug-cong t c)
plug-cong (tφ f t) c = φ-cong (plug-cong t c)

-- Scope extrusion along a whole telescope.
tel-ext : ∀ {n k} (t : Tel n k) (A : Proc k) (Q : Proc n) →
          Q ∥ plug t A ≋ plug t ((Q ⋯ₚ wkTel t) ∥ A)
tel-ext []       A Q = ≡→≋ (cong (_∥ A) (sym (⋯ₚ-idᵣ Q (λ _ → refl))))
tel-ext (tν t)   A Q =
  Eq*.return ν-ext′
    ◅◅ ν-cong (tel-ext t A (Q ⋯ₚ weaken* ⦃ Kᵣ ⦄ 2)
                 ◅◅ plug-cong t (≡→≋ (cong (_∥ A) (fusionₚ Q _ _))))
tel-ext (tφ f t) A Q =
  Eq*.return φ-ext′
    ◅◅ φ-cong (tel-ext t A (Q ⋯ₚ weaken* ⦃ Kᵣ ⦄ 1)
                 ◅◅ plug-cong t (≡→≋ (cong (_∥ A) (fusionₚ Q _ _))))

-- Mirror: pull a telescope out of the LEFT of a parallel composition.
tel-extˡ : ∀ {n k} (t : Tel n k) (A : Proc k) (Q : Proc n) →
           plug t A ∥ Q ≋ plug t (A ∥ (Q ⋯ₚ wkTel t))
tel-extˡ t A Q = ∥-comm ◅◅ tel-ext t A Q ◅◅ plug-cong t ∥-comm

------------------------------------------------------------------------
-- Flat thread lists concatenate.
------------------------------------------------------------------------

pars-++ : ∀ {n} (xs ys : List (Tm n)) → pars xs ∥ pars ys ≋ pars (xs ++ ys)
pars-++ []       ys = ∥-unitˡ
pars-++ (e ∷ xs) ys = ≋-sym ∥-assoc ◅◅ ∥-cong ε (pars-++ xs ys)

------------------------------------------------------------------------
-- Prenex normalisation.
------------------------------------------------------------------------

prenex-acc : ∀ {n} (P : Proc n) → Acc _<_ (size P) → Σ[ N ∈ NF n ] P ≋ ⌈ N ⌉
prenex-acc ⟪ e ⟫ _ = mkNF [] (e ∷ []) , ≋-sym ∥-unitʳ
prenex-acc (ν P) (acc rs)
  with mkNF t es , c ← prenex-acc P (rs ≤-refl) = mkNF (tν t) es , ν-cong c
prenex-acc (φ f P) (acc rs)
  with mkNF t es , c ← prenex-acc P (rs ≤-refl) = mkNF (tφ f t) es , φ-cong c
prenex-acc (P ∥ Q) (acc rs)
  with mkNF t₂ es₂ , c₂ ← prenex-acc Q (rs (Nat.s≤s (m≤n+m (size Q) (size P))))
  with mkNF t₁ es₁ , c₁ ←
         prenex-acc (P ⋯ₚ wkTel t₂)
           (rs (subst (_< suc (size P + size Q)) (sym (size-⋯ₚ P (wkTel t₂)))
                      (Nat.s≤s (m≤m+n (size P) (size Q)))))
  = mkNF (t₂ ++ᵗ t₁) (es₁ ++ map (_⋯ wkTel t₁) es₂)
  , ∥-cong ε c₂
      ◅◅ tel-ext t₂ (pars es₂) P
      ◅◅ plug-cong t₂ (∥-cong c₁ ε
           ◅◅ tel-extˡ t₁ (pars es₁) (pars es₂)
           ◅◅ plug-cong t₁ (∥-cong ε (≡→≋ (pars-⋯ₚ es₂ (wkTel t₁)))
                ◅◅ pars-++ es₁ (map (_⋯ wkTel t₁) es₂)))
      ◅◅ ≡→≋ (sym (plug-++ᵗ t₂ t₁ _))

prenex : ∀ {n} (P : Proc n) → Σ[ N ∈ NF n ] P ≋ ⌈ N ⌉
prenex P = prenex-acc P (<-wellFounded (size P))
