-- | Prenex normal forms for TYPED processes.
--
--   Every typed process is ≋-equal to one of the shape
--
--       ν B₁ B₂ … ν A₁ A₂ (⟪e₁⟫ ∥ … ∥ ⟪eₚ⟫ ∥ ⟪unit⟫)
--
--   i.e. a ν-TELESCOPE over a flat parallel composition of threads.  This is
--   the typed analogue of Simulation.Support.Normal.{Form,Prenex}; it is
--   simpler, since the typed calculus has no φ/sync cells — the only binder is
--   `ν B₁ B₂`, whose scope increment is `sum B₁ + sum B₂`.
--
--   Design note (why `TTel` carries BOTH scopes).  Indexing a telescope by its
--   total width — `TTel w n`, body at `w + n` — forces a `+-assoc` transport at
--   every `ν` step, and those transports then infect every downstream lemma.
--   Indexing by the OUTER and INNER scope instead makes `plugᵗ` definitionally
--   total with no `subst` anywhere: the constructor `tνᵗ B₁ B₂` grows the outer
--   scope by exactly the `sum B₁ + sum B₂` that `ν-ext′`'s weakening uses, so
--   the extrusion lemma needs no arithmetic at all.
module BorrowedCF.Simulation.Support.TypedPrenex where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (_<_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Properties using (≤-refl; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- Binder telescopes.
------------------------------------------------------------------------

-- `TTel n k` : a nest of ν binders that turns a body in scope k into a
-- process in scope n.  Outermost binder first.
data TTel : ℕ → ℕ → Set where
  []ᵗ : ∀ {n} → TTel n n
  tνᵗ : ∀ {n k} (B₁ B₂ : BindGroup) → TTel (sum B₁ + sum B₂ + n) k → TTel n k

plugᵗ : ∀ {n k} → TTel n k → Proc k → Proc n
plugᵗ []ᵗ           X = X
plugᵗ (tνᵗ B₁ B₂ t) X = ν B₁ B₂ (plugᵗ t X)

-- The weakening a telescope induces on its base scope.
wkTelᵗ : ∀ {n k} → TTel n k → n →ᵣ k
wkTelᵗ []ᵗ           = idₖ
wkTelᵗ (tνᵗ B₁ B₂ t) = weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂) ·ₖ wkTelᵗ t

infixr 5 _++ᵗᵗ_

_++ᵗᵗ_ : ∀ {n k j} → TTel n k → TTel k j → TTel n j
[]ᵗ           ++ᵗᵗ s = s
tνᵗ B₁ B₂ t   ++ᵗᵗ s = tνᵗ B₁ B₂ (t ++ᵗᵗ s)

plug-++ᵗᵗ : ∀ {n k j} (t : TTel n k) (s : TTel k j) (X : Proc j) →
            plugᵗ (t ++ᵗᵗ s) X ≡ plugᵗ t (plugᵗ s X)
plug-++ᵗᵗ []ᵗ           s X = refl
plug-++ᵗᵗ (tνᵗ B₁ B₂ t) s X = cong (ν B₁ B₂) (plug-++ᵗᵗ t s X)

------------------------------------------------------------------------
-- Flat thread lists.
------------------------------------------------------------------------

parsᵗ : ∀ {n} → List (Tm n) → Proc n
parsᵗ []       = ⟪ K `unit ⟫
parsᵗ (e ∷ es) = ⟪ e ⟫ ∥ parsᵗ es

pars-⋯ₚᵗ : ∀ {n m} (es : List (Tm n)) (ρ : n →ᵣ m) →
           parsᵗ es ⋯ₚ ρ ≡ parsᵗ (map (_⋯ ρ) es)
pars-⋯ₚᵗ []       ρ = refl
pars-⋯ₚᵗ (e ∷ es) ρ = cong (⟪ e ⋯ ρ ⟫ ∥_) (pars-⋯ₚᵗ es ρ)

------------------------------------------------------------------------
-- Normal forms.
------------------------------------------------------------------------

record TNF (n : ℕ) : Set where
  constructor mkTNF
  field
    {inner} : ℕ
    tel     : TTel n inner
    thr     : List (Tm inner)

open TNF public

⌈_⌉ᵗ : ∀ {n} → TNF n → Proc n
⌈ mkTNF t es ⌉ᵗ = plugᵗ t (parsᵗ es)

------------------------------------------------------------------------
-- A renaming-invariant size, for the well-founded prenex recursion.
------------------------------------------------------------------------

sizeᵗ : ∀ {n} → Proc n → ℕ
sizeᵗ ⟪ _ ⟫       = 1
sizeᵗ (P ∥ Q)     = suc (sizeᵗ P + sizeᵗ Q)
sizeᵗ (ν B₁ B₂ P) = suc (sizeᵗ P)

sizeᵗ-⋯ₚ : ∀ {n m} (P : Proc n) (ρ : n →ᵣ m) → sizeᵗ (P ⋯ₚ ρ) ≡ sizeᵗ P
sizeᵗ-⋯ₚ ⟪ _ ⟫       ρ = refl
sizeᵗ-⋯ₚ (P ∥ Q)     ρ = cong suc (cong₂ _+_ (sizeᵗ-⋯ₚ P ρ) (sizeᵗ-⋯ₚ Q ρ))
sizeᵗ-⋯ₚ (ν B₁ B₂ P) ρ = cong suc (sizeᵗ-⋯ₚ P (ρ ↑* (sum B₁ + sum B₂)))

------------------------------------------------------------------------
-- Small ≋ helpers.
------------------------------------------------------------------------

≡→≋ᵗ : ∀ {n} {P Q : Proc n} → P ≡ Q → P ≋ Q
≡→≋ᵗ refl = ε

≋ᵗ-sym : ∀ {n} {P Q : Proc n} → P ≋ Q → Q ≋ P
≋ᵗ-sym = Eq*.symmetric _

⋯ₚ-idᵣᵗ : ∀ {n} (P : Proc n) {ρ : n →ᵣ n} → ρ ≗ idₖ → P ⋯ₚ ρ ≡ P
⋯ₚ-idᵣᵗ ⟪ e ⟫       eq = cong ⟪_⟫ (⋯-id e eq)
⋯ₚ-idᵣᵗ (P ∥ Q)     eq = cong₂ _∥_ (⋯ₚ-idᵣᵗ P eq) (⋯ₚ-idᵣᵗ Q eq)
⋯ₚ-idᵣᵗ (ν B₁ B₂ P) eq = cong (ν B₁ B₂) (⋯ₚ-idᵣᵗ P (id↑* (sum B₁ + sum B₂) eq))

------------------------------------------------------------------------
-- Congruence and extrusion along a telescope.
------------------------------------------------------------------------

plug-congᵗ : ∀ {n k} (t : TTel n k) {X Y : Proc k} → X ≋ Y → plugᵗ t X ≋ plugᵗ t Y
plug-congᵗ []ᵗ           c = c
plug-congᵗ (tνᵗ B₁ B₂ t) c = ν-cong (plug-congᵗ t c)

-- Scope extrusion along a whole telescope.  The single generator ν-ext′
-- weakens by exactly `sum B₁ + sum B₂` — the same increment `tνᵗ B₁ B₂`
-- adds to the outer index, so no transport appears.
tel-extᵗ : ∀ {n k} (t : TTel n k) (A : Proc k) (Q : Proc n) →
           Q ∥ plugᵗ t A ≋ plugᵗ t ((Q ⋯ₚ wkTelᵗ t) ∥ A)
tel-extᵗ []ᵗ           A Q = ≡→≋ᵗ (cong (_∥ A) (sym (⋯ₚ-idᵣᵗ Q (λ _ → refl))))
tel-extᵗ (tνᵗ B₁ B₂ t) A Q =
  Eq*.return ν-ext′
    ◅◅ ν-cong (tel-extᵗ t A (Q ⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂))
                 ◅◅ plug-congᵗ t (≡→≋ᵗ (cong (_∥ A) (fusionₚ Q _ _))))

-- Mirror: pull a telescope out of the LEFT of a parallel composition.
tel-extˡᵗ : ∀ {n k} (t : TTel n k) (A : Proc k) (Q : Proc n) →
            plugᵗ t A ∥ Q ≋ plugᵗ t (A ∥ (Q ⋯ₚ wkTelᵗ t))
tel-extˡᵗ t A Q = ∥-comm ◅◅ tel-extᵗ t A Q ◅◅ plug-congᵗ t ∥-comm

------------------------------------------------------------------------
-- Flat thread lists concatenate.
------------------------------------------------------------------------

pars-++ᵗ : ∀ {n} (xs ys : List (Tm n)) → parsᵗ xs ∥ parsᵗ ys ≋ parsᵗ (xs ++ ys)
pars-++ᵗ []       ys = ∥-unitˡ
pars-++ᵗ (e ∷ xs) ys = ≋ᵗ-sym ∥-assoc ◅◅ ∥-cong ε (pars-++ᵗ xs ys)

------------------------------------------------------------------------
-- Prenex normalisation.
------------------------------------------------------------------------

prenex-accᵗ : ∀ {n} (P : Proc n) → Acc _<_ (sizeᵗ P) → Σ[ N ∈ TNF n ] P ≋ ⌈ N ⌉ᵗ
prenex-accᵗ ⟪ e ⟫ _ = mkTNF []ᵗ (e ∷ []) , ≋ᵗ-sym ∥-unitʳ
prenex-accᵗ (ν B₁ B₂ P) (acc rs)
  with mkTNF t es , c ← prenex-accᵗ P (rs ≤-refl) = mkTNF (tνᵗ B₁ B₂ t) es , ν-cong c
prenex-accᵗ (P ∥ Q) (acc rs)
  with mkTNF t₂ es₂ , c₂ ← prenex-accᵗ Q (rs (Nat.s≤s (m≤n+m (sizeᵗ Q) (sizeᵗ P))))
  with mkTNF t₁ es₁ , c₁ ←
         prenex-accᵗ (P ⋯ₚ wkTelᵗ t₂)
           (rs (subst (_< suc (sizeᵗ P + sizeᵗ Q)) (sym (sizeᵗ-⋯ₚ P (wkTelᵗ t₂)))
                      (Nat.s≤s (m≤m+n (sizeᵗ P) (sizeᵗ Q)))))
  = mkTNF (t₂ ++ᵗᵗ t₁) (es₁ ++ map (_⋯ wkTelᵗ t₁) es₂)
  , ∥-cong ε c₂
      ◅◅ tel-extᵗ t₂ (parsᵗ es₂) P
      ◅◅ plug-congᵗ t₂ (∥-cong c₁ ε
           ◅◅ tel-extˡᵗ t₁ (parsᵗ es₁) (parsᵗ es₂)
           ◅◅ plug-congᵗ t₁ (∥-cong ε (≡→≋ᵗ (pars-⋯ₚᵗ es₂ (wkTelᵗ t₁)))
                ◅◅ pars-++ᵗ es₁ (map (_⋯ wkTelᵗ t₁) es₂)))
      ◅◅ ≡→≋ᵗ (sym (plug-++ᵗᵗ t₂ t₁ _))

prenexᵗ : ∀ {n} (P : Proc n) → TNF n
prenexᵗ P = proj₁ (prenex-accᵗ P (<-wellFounded (sizeᵗ P)))

prenex-soundᵗ : ∀ {n} (P : Proc n) → P ≋ ⌈ prenexᵗ P ⌉ᵗ
prenex-soundᵗ P = proj₂ (prenex-accᵗ P (<-wellFounded (sizeᵗ P)))

------------------------------------------------------------------------
-- Renaming commutes with plugging.
------------------------------------------------------------------------

-- Rebasing a telescope onto a new outer scope.  The inner scope of the
-- renamed telescope is computed structurally (each tνᵗ keeps its own
-- increment), so no subtraction/transport is needed.
reScopeᵗ : ∀ {n k} → TTel n k → ℕ → ℕ
reScopeᵗ []ᵗ           m = m
reScopeᵗ (tνᵗ B₁ B₂ t) m = reScopeᵗ t (sum B₁ + sum B₂ + m)

_⋯ᵗᵉˡ_ : ∀ {n k m} (t : TTel n k) → n →ᵣ m → TTel m (reScopeᵗ t m)
[]ᵗ           ⋯ᵗᵉˡ ρ = []ᵗ
tνᵗ B₁ B₂ t   ⋯ᵗᵉˡ ρ = tνᵗ B₁ B₂ (t ⋯ᵗᵉˡ (ρ ↑* (sum B₁ + sum B₂)))

-- The renaming lifted under all the binders of a telescope.
_↑ᵗᵉˡ_ : ∀ {n k m} (t : TTel n k) → n →ᵣ m → k →ᵣ reScopeᵗ t m
[]ᵗ           ↑ᵗᵉˡ ρ = ρ
tνᵗ B₁ B₂ t   ↑ᵗᵉˡ ρ = t ↑ᵗᵉˡ (ρ ↑* (sum B₁ + sum B₂))

plug-⋯ₚᵗ : ∀ {n k m} (t : TTel n k) (X : Proc k) (ρ : n →ᵣ m) →
           plugᵗ t X ⋯ₚ ρ ≡ plugᵗ (t ⋯ᵗᵉˡ ρ) (X ⋯ₚ (t ↑ᵗᵉˡ ρ))
plug-⋯ₚᵗ []ᵗ           X ρ = refl
plug-⋯ₚᵗ (tνᵗ B₁ B₂ t) X ρ = cong (ν B₁ B₂) (plug-⋯ₚᵗ t X (ρ ↑* (sum B₁ + sum B₂)))
