-- | A CONSTRAINT-GENERATING subcontext relation (base module).
--
--   The algorithmic rules of `BorrowedCF.Algorithmic` check their structural premise
--   `Γ ∶ γ₁ ≼ γ₂` in a context whose types still contain unification variables
--   (A-LetPair / A-Let / A-Case bind the components of an INFERRED type).  The rule
--   `∥′-tm-;` of `_∶_≈′_` — and everything derived from it, `;-commMob`, `;-unit₁`,
--   `;-unit₂` — needs `MobCx`, and `Mobile` is not reflected along `subTy`:
--
--       Mobile (subTy T̂ σ)   DOES NOT IMPLY   Mobile T̂
--
--   (a uvar leaf `` `` α `` is never syntactically mobile).  The A-rules therefore
--   carry `Γ ∶ γ₁ ≼ γ₂ ↑ Δ`, which mirrors `_∶_≼_` rule by rule and EMITS
--   `allMobile Γ α` (a `C-Mob (Γ ﹫ x)` per variable of α) wherever `_∶_≈′_` demands
--   `MobCx Γ α`, and add Δ to their own output constraints.  `∥′-dup` keeps its
--   `UnrCx` premise, which IS reflected along `subTy`.
--
--   This module holds the judgments and their SOUNDNESS (`≼↑-sound`), which is what
--   `BorrowedCF.Algorithmic.sound` needs.  Completeness / transfer
--   (`≼↑-complete`, `≼⇒≼↑`, `≼↑-erase`) lives in `BorrowedCF.Completeness.Sub`.
module BorrowedCF.Context.SubConstraint where

open import Data.Fin.Subset using (Subset; ∁)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Relation.Binary.Construct.Closure.Symmetric as Sym
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain using (_↓_)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved

open Nat.Variables
open Variables

private variable
  X : Subset n

------------------------------------------------------------------------
-- The mobility constraints of a structure: one `C-Mob (Γ ﹫ x)` per variable.

allMobile : Ctx n → Struct n → List Constraint
allMobile Γ (` x) = L.[ C-Mob (Γ ﹫ x) ]
allMobile Γ [] = []
allMobile Γ (α ∥ β) = allMobile Γ α ++ allMobile Γ β
allMobile Γ (α ; β) = allMobile Γ α ++ allMobile Γ β

------------------------------------------------------------------------
-- The three judgments.  Every rule of `_∶_≈′_` / `_∶_≼_` is mirrored; the two
-- mobility premises of `∥′-tm-;` become the emitted constraint set.

infix 4 _∶_≈′_↑_ _∶_≈_↑_ _∶_≼_↑_
infixr 5 _◅ᶠ_ _◅ᵇ_

data _∶_≈′_↑_ (Γ : Ctx n) : Struct n → Struct n → CSet → Set where
  sq′-assoc↑ : Γ ∶ (α ; β) ; γ ≈′ α ; (β ; γ) ↑ []
  sq′-cong₁↑ : Γ ∶ α ≈′ α′ ↑ Δ → Γ ∶ α ; β ≈′ α′ ; β ↑ Δ
  sq′-cong₂↑ : Γ ∶ β ≈′ β′ ↑ Δ → Γ ∶ α ; β ≈′ α ; β′ ↑ Δ

  ∥′-unit↑   : Γ ∶ α ∥ [] ≈′ α ↑ []
  ∥′-assoc↑  : Γ ∶ (α ∥ β) ∥ γ ≈′ α ∥ (β ∥ γ) ↑ []
  ∥′-comm↑   : Γ ∶ α ∥ β ≈′ β ∥ α ↑ []
  ∥′-cong₁↑  : Γ ∶ α ≈′ α′ ↑ Δ → Γ ∶ α ∥ β ≈′ α′ ∥ β ↑ Δ
  ∥′-dup↑    : (U : UnrCx Γ α) → Γ ∶ α ≈′ α ∥ α ↑ []
  -- the two halves of `∥′-tm-; : MobCx Γ α ⊎ MobCx Γ β → Γ ∶ α ∥ β ≈′ α ; β`
  ∥′-tmˡ↑    : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ α
  ∥′-tmʳ↑    : Γ ∶ α ∥ β ≈′ α ; β ↑ allMobile Γ β

-- the equivalence closure, with the constraint sets of the steps concatenated
data _∶_≈_↑_ (Γ : Ctx n) : Struct n → Struct n → CSet → Set where
  ε↑   : Γ ∶ α ≈ α ↑ []
  _◅ᶠ_ : ∀ {Δ₁ Δ₂} → Γ ∶ α ≈′ β ↑ Δ₁ → Γ ∶ β ≈ γ ↑ Δ₂ → Γ ∶ α ≈ γ ↑ (Δ₁ ++ Δ₂)
  _◅ᵇ_ : ∀ {Δ₁ Δ₂} → Γ ∶ β ≈′ α ↑ Δ₁ → Γ ∶ β ≈ γ ↑ Δ₂ → Γ ∶ α ≈ γ ↑ (Δ₁ ++ Δ₂)

data _∶_≼_↑_ (Γ : Ctx n) : Struct n → Struct n → CSet → Set where
  ≼-refl↑     : Γ ∶ α ≈ β ↑ Δ → Γ ∶ α ≼ β ↑ Δ
  ≼-∅↑        : UnrCx Γ α → Γ ∶ [] ≼ α ↑ []
  ≼-wk↑       : Γ ∶ (α₁ ∥ α₂) ; (β₁ ∥ β₂) ≼ (α₁ ; β₁) ∥ (α₂ ; β₂) ↑ []
  ≼-trans↑    : ∀ {Δ₁ Δ₂} → Γ ∶ α ≼ β ↑ Δ₁ → Γ ∶ β ≼ γ ↑ Δ₂ → Γ ∶ α ≼ γ ↑ (Δ₁ ++ Δ₂)
  ≼-cong-sq↑  : ∀ {Δ₁ Δ₂} → Γ ∶ α ≼ α′ ↑ Δ₁ → Γ ∶ β ≼ β′ ↑ Δ₂ → Γ ∶ α ; β ≼ α′ ; β′ ↑ (Δ₁ ++ Δ₂)
  ≼-cong-par↑ : ∀ {Δ₁ Δ₂} → Γ ∶ α ≼ α′ ↑ Δ₁ → Γ ∶ β ≼ β′ ↑ Δ₂ → Γ ∶ α ∥ β ≼ α′ ∥ β′ ↑ (Δ₁ ++ Δ₂)

-- the A-Case premise, indexed by its constraint set
data JoinParSeq↑ (Γ : Ctx n) (γ : Struct n) (X : Subset n) : ParSeq → CSet → Set where
  par↑ : Γ ∶ (γ ↓ X) ∥ (γ ↓ ∁ X) ≼ γ ↑ Δ → JoinParSeq↑ Γ γ X par Δ
  seq↑ : Γ ∶ (γ ↓ X) ; (γ ↓ ∁ X) ≼ γ ↑ Δ → JoinParSeq↑ Γ γ X seq Δ

join-joinParSeq↑ : ∀ {p/s} → JoinParSeq↑ Γ γ X p/s Δ → Γ ∶ join p/s (γ ↓ X) (γ ↓ ∁ X) ≼ γ ↑ Δ
join-joinParSeq↑ (par↑ x) = x
join-joinParSeq↑ (seq↑ x) = x

------------------------------------------------------------------------
-- Reflection of `Unr` and the mobility constraints along the substitution.

unrCx-sub : UnrCx Γ α → UnrCx (subCtx Γ σ) α
unrCx-sub = allCx-map⁺ subTy-unr

module _ {σ : UV.Sub} (Sσ : Solving σ) where

  mobConstraints⇒MobCx : (Γ : Ctx n)(γ : Struct n) → SolvedΔ (allMobile Γ γ) σ → MobCx (subCtx Γ σ) γ
  mobConstraints⇒MobCx Γ (` x) (px ∷ Sm) =
    ` subst Mobile (sym (V.lookup-map x (λ t → subTy t σ) Γ)) px
  mobConstraints⇒MobCx Γ [] Sm = []
  mobConstraints⇒MobCx Γ (α ∥ β) Sm = mobConstraints⇒MobCx Γ α (AllP.++⁻ˡ (allMobile Γ α) Sm) ∥ mobConstraints⇒MobCx Γ β (AllP.++⁻ʳ (allMobile Γ α) Sm)
  mobConstraints⇒MobCx Γ (α ; β) Sm = mobConstraints⇒MobCx Γ α (AllP.++⁻ˡ (allMobile Γ α) Sm) ; mobConstraints⇒MobCx Γ β (AllP.++⁻ʳ (allMobile Γ α) Sm)

------------------------------------------------------------------------
-- 1. SOUNDNESS.  Solving the emitted constraints turns a ≼↑ derivation over the
--    uvar context into a plain ≼ derivation over the substituted context.

module _ {σ : UV.Sub} (Sσ : Solving σ) where

  ≈′↑-sound : SolvedΔ Δ σ → Γ ∶ α ≈′ β ↑ Δ → subCtx Γ σ ∶ α ≈′ β
  ≈′↑-sound SΔ sq′-assoc↑     = ;′-assoc
  ≈′↑-sound SΔ (sq′-cong₁↑ d) = ;′-cong₁ (≈′↑-sound SΔ d)
  ≈′↑-sound SΔ (sq′-cong₂↑ d) = ;′-cong₂ (≈′↑-sound SΔ d)
  ≈′↑-sound SΔ ∥′-unit↑       = ∥′-unit
  ≈′↑-sound SΔ ∥′-assoc↑      = ∥′-assoc
  ≈′↑-sound SΔ ∥′-comm↑       = ∥′-comm
  ≈′↑-sound SΔ (∥′-cong₁↑ d)  = ∥′-cong₁ (≈′↑-sound SΔ d)
  ≈′↑-sound SΔ (∥′-dup↑ U)    = ∥′-dup (unrCx-sub U)
  ≈′↑-sound SΔ ∥′-tmˡ↑ = ∥′-tm-; (inj₁ (mobConstraints⇒MobCx Sσ _ _ SΔ))
  ≈′↑-sound SΔ ∥′-tmʳ↑ = ∥′-tm-; (inj₂ (mobConstraints⇒MobCx Sσ _ _ SΔ))

  ≈↑-sound : SolvedΔ Δ σ → Γ ∶ α ≈ β ↑ Δ → subCtx Γ σ ∶ α ≈ β
  ≈↑-sound SΔ ε↑ = Star.ε
  ≈↑-sound SΔ (_◅ᶠ_ {Δ₁ = Δ} d ds) =
    Star._◅_ (Sym.fwd (≈′↑-sound (AllP.++⁻ˡ Δ SΔ) d)) (≈↑-sound (AllP.++⁻ʳ Δ SΔ) ds)
  ≈↑-sound SΔ (_◅ᵇ_ {Δ₁ = Δ} d ds) =
    Star._◅_ (Sym.bwd (≈′↑-sound (AllP.++⁻ˡ Δ SΔ) d)) (≈↑-sound (AllP.++⁻ʳ Δ SΔ) ds)

  ≼↑-sound : SolvedΔ Δ σ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → subCtx Γ σ ∶ γ₁ ≼ γ₂
  ≼↑-sound SΔ (≼-refl↑ d) = ≼-refl (≈↑-sound SΔ d)
  ≼↑-sound SΔ (≼-∅↑ U)    = ≼-∅ (unrCx-sub U)
  ≼↑-sound SΔ ≼-wk↑       = ≼-wk
  ≼↑-sound SΔ (≼-trans↑ {Δ₁ = Δ} d e) =
    ≼-trans (≼↑-sound (AllP.++⁻ˡ Δ SΔ) d) (≼↑-sound (AllP.++⁻ʳ Δ SΔ) e)
  ≼↑-sound SΔ (≼-cong-sq↑ {Δ₁ = Δ} d e) =
    ≼-cong-; (≼↑-sound (AllP.++⁻ˡ Δ SΔ) d) (≼↑-sound (AllP.++⁻ʳ Δ SΔ) e)
  ≼↑-sound SΔ (≼-cong-par↑ {Δ₁ = Δ} d e) =
    ≼-cong-∥ (≼↑-sound (AllP.++⁻ˡ Δ SΔ) d) (≼↑-sound (AllP.++⁻ʳ Δ SΔ) e)

  -- convenience for the A-rules, whose output constraints are `Δ₀ ++ Δ₁ ++ …`
  ≼↑-sound-++ : ∀ Δ {Δ′ γ₁ γ₂} {Γ : Ctx n} →
    Γ ∶ γ₁ ≼ γ₂ ↑ Δ → SolvedΔ (Δ ++ Δ′) σ → subCtx Γ σ ∶ γ₁ ≼ γ₂
  ≼↑-sound-++ Δ d SΔ = ≼↑-sound (AllP.++⁻ˡ Δ SΔ) d
