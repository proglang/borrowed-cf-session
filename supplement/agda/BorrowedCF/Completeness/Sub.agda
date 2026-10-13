-- | A CONSTRAINT-GENERATING subcontext relation.
--
--   The algorithmic rules of `BorrowedCF.Algorithmic` check their structural premise
--   `Γ ∶ γ₁ ≼ γ₂` in a context whose types still contain unification variables
--   (A-LetPair / A-Let / A-Case bind the components of an INFERRED type).  The rule
--   `∥′-tm-;` of `_∶_≈′_` — and everything derived from it, `;-commMob`, `;-unit₁`,
--   `;-unit₂` — needs `MobCx`, and `Mobile` is not reflected along `subTy`:
--
--       Mobile (subTy T̂ σ)   DOES NOT IMPLY   Mobile T̂
--
--   (a uvar leaf `` `` α `` is never syntactically mobile).  Completeness of the
--   algorithm is therefore FALSE as long as the premise is the plain `≼`
--   (see Completeness/Main-STATUS.md, BLOCKING FINDING 1).
--
--   This module defines `Γ ∶ γ₁ ≼ γ₂ ↑ Δ`, which mirrors `_∶_≼_` rule by rule and
--   EMITS `allMobile Γ α` (a `C-Mob (Γ ﹫ x)` per variable of α) wherever `_∶_≈′_`
--   demands `MobCx Γ α`.  `∥′-dup` keeps its `UnrCx` premise, which IS reflected.
--   Soundness (`≼↑-sound`) and transfer (`≼↑-complete`) below show that replacing
--   `≼` by `≼ ↑ Δ` in the A-rules is conservative and repairs completeness.
module BorrowedCF.Completeness.Sub where

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
open import BorrowedCF.Context.SubConstraint public
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Sub.Base

open Nat.Variables
open Variables

private variable
  Γ̂ : Ctx n
  X : Subset n

------------------------------------------------------------------------
-- The three judgments `_∶_≈′_↑_`, `_∶_≈_↑_`, `_∶_≼_↑_`, the A-Case premise
-- `JoinParSeq↑` and their soundness now live in the base module
-- `BorrowedCF.Context.SubConstraint` (the A-rules refer to them); this module
-- re-exports them and adds the derived laws, completeness and the erasure.

------------------------------------------------------------------------
-- Re-indexing along a propositional equality of constraint sets.  Genuine
-- weakening of the index (Δ ⇝ Δ ++ Δ′) is NOT derivable: the constraint set of a
-- derivation is determined by the rules it uses.  It is not needed either: each
-- A-rule carries the index of its own ≼↑ premise into its output constraints, and
-- the use site splits the resulting `SolvedΔ` with `AllP.++⁻ˡ / ++⁻ʳ`.

≈↑-cast : Δ ≡ Δ′ → Γ ∶ α ≈ β ↑ Δ → Γ ∶ α ≈ β ↑ Δ′
≈↑-cast {Γ = Γ} {α} {β} eq = subst (Γ ∶ α ≈ β ↑_) eq

≼↑-cast : Δ ≡ Δ′ → Γ ∶ α ≼ β ↑ Δ → Γ ∶ α ≼ β ↑ Δ′
≼↑-cast {Γ = Γ} {α} {β} eq = subst (Γ ∶ α ≼ β ↑_) eq

------------------------------------------------------------------------
-- Closure properties of ≈↑.

≈↑-trans : ∀ {Δ₁ Δ₂} → Γ ∶ α ≈ β ↑ Δ₁ → Γ ∶ β ≈ γ ↑ Δ₂ → Γ ∶ α ≈ γ ↑ (Δ₁ ++ Δ₂)
≈↑-trans ε↑ ys = ys
≈↑-trans (_◅ᶠ_ {Δ₁ = Δ} d xs) ys = ≈↑-cast (sym (L.++-assoc Δ _ _)) (d ◅ᶠ ≈↑-trans xs ys)
≈↑-trans (_◅ᵇ_ {Δ₁ = Δ} d xs) ys = ≈↑-cast (sym (L.++-assoc Δ _ _)) (d ◅ᵇ ≈↑-trans xs ys)

-- symmetry reverses the chain, hence reorders the constraints; the reordering is
-- reported as an implication between the two `SolvedΔ`s (it is in fact a permutation)
≈↑-sym : Γ ∶ α ≈ β ↑ Δ →
  Σ[ Δ′ ∈ CSet ] (Γ ∶ β ≈ α ↑ Δ′) × (∀ {σ} → SolvedΔ Δ σ → SolvedΔ Δ′ σ)
≈↑-sym ε↑ = [] , ε↑ , λ _ → []
≈↑-sym (_◅ᶠ_ {Δ₁ = Δ} d xs) =
  let Δ′ , ys , f = ≈↑-sym xs in
  Δ′ ++ Δ , ≈↑-trans ys (≈↑-cast (L.++-identityʳ Δ) (d ◅ᵇ ε↑))
          , λ SΔ → AllP.++⁺ (f (AllP.++⁻ʳ Δ SΔ)) (AllP.++⁻ˡ Δ SΔ)
≈↑-sym (_◅ᵇ_ {Δ₁ = Δ} d xs) =
  let Δ′ , ys , f = ≈↑-sym xs in
  Δ′ ++ Δ , ≈↑-trans ys (≈↑-cast (L.++-identityʳ Δ) (d ◅ᶠ ε↑))
          , λ SΔ → AllP.++⁺ (f (AllP.++⁻ʳ Δ SΔ)) (AllP.++⁻ˡ Δ SΔ)

≈↑-par-cong₁ : Γ ∶ α ≈ α′ ↑ Δ → Γ ∶ α ∥ β ≈ α′ ∥ β ↑ Δ
≈↑-par-cong₁ ε↑ = ε↑
≈↑-par-cong₁ (d ◅ᶠ ds) = ∥′-cong₁↑ d ◅ᶠ ≈↑-par-cong₁ ds
≈↑-par-cong₁ (d ◅ᵇ ds) = ∥′-cong₁↑ d ◅ᵇ ≈↑-par-cong₁ ds

≈↑-sq-cong₁ : Γ ∶ α ≈ α′ ↑ Δ → Γ ∶ α ; β ≈ α′ ; β ↑ Δ
≈↑-sq-cong₁ ε↑ = ε↑
≈↑-sq-cong₁ (d ◅ᶠ ds) = sq′-cong₁↑ d ◅ᶠ ≈↑-sq-cong₁ ds
≈↑-sq-cong₁ (d ◅ᵇ ds) = sq′-cong₁↑ d ◅ᵇ ≈↑-sq-cong₁ ds

≈↑-sq-cong₂ : Γ ∶ β ≈ β′ ↑ Δ → Γ ∶ α ; β ≈ α ; β′ ↑ Δ
≈↑-sq-cong₂ ε↑ = ε↑
≈↑-sq-cong₂ (d ◅ᶠ ds) = sq′-cong₂↑ d ◅ᶠ ≈↑-sq-cong₂ ds
≈↑-sq-cong₂ (d ◅ᵇ ds) = sq′-cong₂↑ d ◅ᵇ ≈↑-sq-cong₂ ds

------------------------------------------------------------------------
-- The derived equivalences of Context/Equivalence.agda, with their constraints.

∥-assoc↑ : Γ ∶ (α ∥ β) ∥ γ ≈ α ∥ (β ∥ γ) ↑ []
∥-assoc↑ = ∥′-assoc↑ ◅ᶠ ε↑

∥-comm↑ : Γ ∶ α ∥ β ≈ β ∥ α ↑ []
∥-comm↑ = ∥′-comm↑ ◅ᶠ ε↑

∥-unit₂↑ : Γ ∶ α ∥ [] ≈ α ↑ []
∥-unit₂↑ = ∥′-unit↑ ◅ᶠ ε↑

∥-unit₂↑⁻¹ : Γ ∶ α ≈ α ∥ [] ↑ []
∥-unit₂↑⁻¹ = ∥′-unit↑ ◅ᵇ ε↑

∥-unit₁↑ : Γ ∶ [] ∥ α ≈ α ↑ []
∥-unit₁↑ = ∥′-comm↑ ◅ᶠ (∥′-unit↑ ◅ᶠ ε↑)

∥-unit₁↑⁻¹ : Γ ∶ α ≈ [] ∥ α ↑ []
∥-unit₁↑⁻¹ = ∥′-unit↑ ◅ᵇ (∥′-comm↑ ◅ᵇ ε↑)

∥-dup↑ : UnrCx Γ α → Γ ∶ α ≈ α ∥ α ↑ []
∥-dup↑ U = ∥′-dup↑ U ◅ᶠ ε↑

sq-assoc↑ : Γ ∶ (α ; β) ; γ ≈ α ; (β ; γ) ↑ []
sq-assoc↑ = sq′-assoc↑ ◅ᶠ ε↑

∥-cong↑ : ∀ {Δ₁ Δ₂} → Γ ∶ α ≈ α′ ↑ Δ₁ → Γ ∶ β ≈ β′ ↑ Δ₂ → Γ ∶ α ∥ β ≈ α′ ∥ β′ ↑ (Δ₁ ++ Δ₂)
∥-cong↑ {Δ₁ = Δ₁} {Δ₂} xs ys =
  ≈↑-cast (cong (Δ₁ ++_) (L.++-identityʳ Δ₂))
    (≈↑-trans (≈↑-par-cong₁ xs)
      (≈↑-trans ∥-comm↑ (≈↑-trans (≈↑-par-cong₁ ys) ∥-comm↑)))

sq-cong↑ : ∀ {Δ₁ Δ₂} → Γ ∶ α ≈ α′ ↑ Δ₁ → Γ ∶ β ≈ β′ ↑ Δ₂ → Γ ∶ α ; β ≈ α′ ; β′ ↑ (Δ₁ ++ Δ₂)
sq-cong↑ xs ys = ≈↑-trans (≈↑-sq-cong₁ xs) (≈↑-sq-cong₂ ys)

-- `∥/;-transmute`: turning ∥ into ; costs the mobility of one side
transmuteˡ↑ : Γ ∶ α ∥ β ≈ α ; β ↑ allMobile Γ α
transmuteˡ↑ {Γ = Γ} {α = α} = ≈↑-cast (L.++-identityʳ (allMobile Γ α)) (∥′-tmˡ↑ ◅ᶠ ε↑)

transmuteʳ↑ : Γ ∶ α ∥ β ≈ α ; β ↑ allMobile Γ β
transmuteʳ↑ {Γ = Γ} {β = β} = ≈↑-cast (L.++-identityʳ (allMobile Γ β)) (∥′-tmʳ↑ ◅ᶠ ε↑)

-- the units of ; are constraint-FREE: `allMobile Γ [] = []`
sq-unit₁↑ : Γ ∶ [] ; α ≈ α ↑ []
sq-unit₁↑ = ∥′-tmˡ↑ ◅ᵇ ∥-unit₁↑

sq-unit₂↑ : Γ ∶ α ; [] ≈ α ↑ []
sq-unit₂↑ = ∥′-tmʳ↑ ◅ᵇ ∥-unit₂↑

sq-unit₁↑⁻¹ : Γ ∶ α ≈ [] ; α ↑ []
sq-unit₁↑⁻¹ = ∥′-unit↑ ◅ᵇ (∥′-comm↑ ◅ᵇ (∥′-tmˡ↑ ◅ᶠ ε↑))

sq-unit₂↑⁻¹ : Γ ∶ α ≈ α ; [] ↑ []
sq-unit₂↑⁻¹ = ∥′-unit↑ ◅ᵇ (∥′-tmʳ↑ ◅ᶠ ε↑)

-- `;-commMob`: commuting a ; costs the mobility of the side that moves, twice
sq-commMobˡ↑ : Γ ∶ α ; β ≈ β ; α ↑ (allMobile Γ α ++ allMobile Γ α)
sq-commMobˡ↑ {Γ = Γ} {α = α} =
  ≈↑-cast (cong (allMobile Γ α ++_) (L.++-identityʳ (allMobile Γ α)))
          (∥′-tmˡ↑ ◅ᵇ (∥′-comm↑ ◅ᶠ (∥′-tmʳ↑ ◅ᶠ ε↑)))

sq-commMobʳ↑ : Γ ∶ α ; β ≈ β ; α ↑ (allMobile Γ β ++ allMobile Γ β)
sq-commMobʳ↑ {Γ = Γ} {β = β} =
  ≈↑-cast (cong (allMobile Γ β ++_) (L.++-identityʳ (allMobile Γ β)))
          (∥′-tmʳ↑ ◅ᵇ (∥′-comm↑ ◅ᶠ (∥′-tmˡ↑ ◅ᶠ ε↑)))

------------------------------------------------------------------------
-- The derived subcontext facts of Context/Subcontext.agda and Context/Join.agda.
-- All of them are CONSTRAINT-FREE.

sq-≼-par↑ : Γ ∶ α ; β ≼ α ∥ β ↑ []
sq-≼-par↑ =
  ≼-trans↑ (≼-refl↑ (sq-cong↑ ∥-unit₂↑⁻¹ ∥-unit₁↑⁻¹))
    (≼-trans↑ ≼-wk↑ (≼-refl↑ (∥-cong↑ sq-unit₂↑ sq-unit₁↑)))

sq-≼-join↑ : (p/s : ParSeq) → Γ ∶ α ; β ≼ join p/s α β ↑ []
sq-≼-join↑ par = sq-≼-par↑
sq-≼-join↑ seq = ≼-refl↑ ε↑

join-≼-par↑ : (p/s : ParSeq) → Γ ∶ join p/s α β ≼ α ∥ β ↑ []
join-≼-par↑ par = ≼-refl↑ ε↑
join-≼-par↑ seq = sq-≼-par↑

≼-join↑ : ∀ {Δ₁ Δ₂} (p/s : ParSeq) →
  Γ ∶ α₁ ≼ α₂ ↑ Δ₁ → Γ ∶ β₁ ≼ β₂ ↑ Δ₂ → Γ ∶ join p/s α₁ β₁ ≼ join p/s α₂ β₂ ↑ (Δ₁ ++ Δ₂)
≼-join↑ par = ≼-cong-par↑
≼-join↑ seq = ≼-cong-sq↑

parOrSeq?↑ : Γ ∶ α ; β ≼ γ ↑ Δ → Σ[ p/s ∈ ParSeq ] Γ ∶ join p/s α β ≼ γ ↑ Δ
parOrSeq?↑ ≤γ = seq , ≤γ

------------------------------------------------------------------------
-- SOUNDNESS (`≈′↑-sound`, `≈↑-sound`, `≼↑-sound`, `≼↑-sound-++`) is what the
-- A-rules of `BorrowedCF.Algorithmic` need, so it lives in the base module
-- `BorrowedCF.Context.SubConstraint` together with the judgments; it is
-- re-exported here.

------------------------------------------------------------------------
-- 2. COMPLETENESS / TRANSFER.  A declarative ≼ over the SOLVED context lifts to a
--    ≼↑ over the uvar context whose constraints σ already solves.  This is the
--    `≼-ctx` lemma the main induction needs, without the false `mob-reflect`.

module _ {Γ̂ Γ : Ctx n} {σ : UV.Sub} (Sσ : Solving σ) (ap : Approx Γ̂ Γ σ) where

  ≈′↑-complete : Γ ∶ α ≈′ β → Σ[ Δ ∈ CSet ] (Γ̂ ∶ α ≈′ β ↑ Δ) × SolvedΔ Δ σ
  ≈′↑-complete ;′-assoc     = [] , sq′-assoc↑ , []
  ≈′↑-complete (;′-cong₁ d) = let Δ , d′ , SΔ = ≈′↑-complete d in Δ , sq′-cong₁↑ d′ , SΔ
  ≈′↑-complete (;′-cong₂ d) = let Δ , d′ , SΔ = ≈′↑-complete d in Δ , sq′-cong₂↑ d′ , SΔ
  ≈′↑-complete ∥′-unit      = [] , ∥′-unit↑  , []
  ≈′↑-complete ∥′-assoc     = [] , ∥′-assoc↑ , []
  ≈′↑-complete ∥′-comm      = [] , ∥′-comm↑  , []
  ≈′↑-complete (∥′-cong₁ d) = let Δ , d′ , SΔ = ≈′↑-complete d in Δ , ∥′-cong₁↑ d′ , SΔ
  ≈′↑-complete (∥′-dup U)   = [] , ∥′-dup↑ (unrCx-approx ap U) , []
  ≈′↑-complete (∥′-tm-; (inj₁ MH)) = _ , ∥′-tmˡ↑ , mobCx⇒solvedΔ ap MH
  ≈′↑-complete (∥′-tm-; (inj₂ MH)) = _ , ∥′-tmʳ↑ , mobCx⇒solvedΔ ap MH

  ≈↑-complete : Γ ∶ α ≈ β → Σ[ Δ ∈ CSet ] (Γ̂ ∶ α ≈ β ↑ Δ) × SolvedΔ Δ σ
  ≈↑-complete Star.ε = [] , ε↑ , []
  ≈↑-complete (Star._◅_ (Sym.fwd x) xs) =
    let Δ₁ , d , S₁ = ≈′↑-complete x
        Δ₂ , ds , S₂ = ≈↑-complete xs
    in Δ₁ ++ Δ₂ , d ◅ᶠ ds , AllP.++⁺ S₁ S₂
  ≈↑-complete (Star._◅_ (Sym.bwd x) xs) =
    let Δ₁ , d , S₁ = ≈′↑-complete x
        Δ₂ , ds , S₂ = ≈↑-complete xs
    in Δ₁ ++ Δ₂ , d ◅ᵇ ds , AllP.++⁺ S₁ S₂

  ≼↑-complete : Γ ∶ γ₁ ≼ γ₂ → Σ[ Δ ∈ CSet ] (Γ̂ ∶ γ₁ ≼ γ₂ ↑ Δ) × SolvedΔ Δ σ
  ≼↑-complete (≼-refl d) = let Δ , d′ , SΔ = ≈↑-complete d in Δ , ≼-refl↑ d′ , SΔ
  ≼↑-complete (≼-∅ U)    = [] , ≼-∅↑ (unrCx-approx ap U) , []
  ≼↑-complete ≼-wk       = [] , ≼-wk↑ , []
  ≼↑-complete (≼-trans d e) =
    let Δ₁ , d′ , S₁ = ≼↑-complete d
        Δ₂ , e′ , S₂ = ≼↑-complete e
    in Δ₁ ++ Δ₂ , ≼-trans↑ d′ e′ , AllP.++⁺ S₁ S₂
  ≼↑-complete (≼-cong-; d e) =
    let Δ₁ , d′ , S₁ = ≼↑-complete d
        Δ₂ , e′ , S₂ = ≼↑-complete e
    in Δ₁ ++ Δ₂ , ≼-cong-sq↑ d′ e′ , AllP.++⁺ S₁ S₂
  ≼↑-complete (≼-cong-∥ d e) =
    let Δ₁ , d′ , S₁ = ≼↑-complete d
        Δ₂ , e′ , S₂ = ≼↑-complete e
    in Δ₁ ++ Δ₂ , ≼-cong-par↑ d′ e′ , AllP.++⁺ S₁ S₂

-- The special case the main induction starts from: a solved context approximates
-- itself, so every declarative ≼ over a SolvedCtx lifts with solvable constraints.
≼↑-complete-solved : {Γ : Ctx n} → Solving σ → SolvedΓ Γ σ →
  subCtx Γ σ ∶ γ₁ ≼ γ₂ → Σ[ Δ ∈ CSet ] (Γ ∶ γ₁ ≼ γ₂ ↑ Δ) × SolvedΔ Δ σ
≼↑-complete-solved {Γ = Γ} Sσ SΓ = ≼↑-complete Sσ (approx-id {Γ = Γ} SΓ)

------------------------------------------------------------------------
-- 3. The embedding of ≼ into ≼↑, and its inverse.  `Γ ∶ γ₁ ≼ γ₂ → Γ ∶ γ₁ ≼ γ₂ ↑ []`
--    is FALSE whenever the derivation uses a mobility step; the honest statement is
--    that the emitted constraints hold outright in the same context Γ.

MobHolds : Constraint → Set
MobHolds (C-Eq T U) = ⊤
MobHolds (C-Mob T)  = Mobile T

allMobile-holds : MobCx Γ α → All MobHolds (allMobile Γ α)
allMobile-holds {α = ` x}   (` m)     = m ∷ []
allMobile-holds {α = []}    []        = []
allMobile-holds {α = α ∥ β} (M₁ ∥ M₂) = AllP.++⁺ (allMobile-holds M₁) (allMobile-holds M₂)
allMobile-holds {α = α ; β} (M₁ ; M₂) = AllP.++⁺ (allMobile-holds M₁) (allMobile-holds M₂)

allMobile-holds⁻¹ : ∀ {Γ : Ctx n} α → All MobHolds (allMobile Γ α) → MobCx Γ α
allMobile-holds⁻¹ (` x)   (m ∷ []) = ` m
allMobile-holds⁻¹ []      MH        = []
allMobile-holds⁻¹ {Γ = Γ} (α ∥ β) MH =
  allMobile-holds⁻¹ α (AllP.++⁻ˡ (allMobile Γ α) MH) ∥
  allMobile-holds⁻¹ β (AllP.++⁻ʳ (allMobile Γ α) MH)
allMobile-holds⁻¹ {Γ = Γ} (α ; β) MH =
  allMobile-holds⁻¹ α (AllP.++⁻ˡ (allMobile Γ α) MH) ;
  allMobile-holds⁻¹ β (AllP.++⁻ʳ (allMobile Γ α) MH)

≈′⇒≈′↑ : Γ ∶ α ≈′ β → Σ[ Δ ∈ CSet ] (Γ ∶ α ≈′ β ↑ Δ) × All MobHolds Δ
≈′⇒≈′↑ ;′-assoc     = [] , sq′-assoc↑ , []
≈′⇒≈′↑ (;′-cong₁ d) = let Δ , d′ , MH = ≈′⇒≈′↑ d in Δ , sq′-cong₁↑ d′ , MH
≈′⇒≈′↑ (;′-cong₂ d) = let Δ , d′ , MH = ≈′⇒≈′↑ d in Δ , sq′-cong₂↑ d′ , MH
≈′⇒≈′↑ ∥′-unit      = [] , ∥′-unit↑  , []
≈′⇒≈′↑ ∥′-assoc     = [] , ∥′-assoc↑ , []
≈′⇒≈′↑ ∥′-comm      = [] , ∥′-comm↑  , []
≈′⇒≈′↑ (∥′-cong₁ d) = let Δ , d′ , MH = ≈′⇒≈′↑ d in Δ , ∥′-cong₁↑ d′ , MH
≈′⇒≈′↑ (∥′-dup U)   = [] , ∥′-dup↑ U , []
≈′⇒≈′↑ (∥′-tm-; (inj₁ MH)) = _ , ∥′-tmˡ↑ , allMobile-holds MH
≈′⇒≈′↑ (∥′-tm-; (inj₂ MH)) = _ , ∥′-tmʳ↑ , allMobile-holds MH

≈⇒≈↑ : Γ ∶ α ≈ β → Σ[ Δ ∈ CSet ] (Γ ∶ α ≈ β ↑ Δ) × All MobHolds Δ
≈⇒≈↑ Star.ε = [] , ε↑ , []
≈⇒≈↑ (Star._◅_ (Sym.fwd x) xs) =
  let Δ₁ , d , M₁ = ≈′⇒≈′↑ x
      Δ₂ , ds , M₂ = ≈⇒≈↑ xs
  in Δ₁ ++ Δ₂ , d ◅ᶠ ds , AllP.++⁺ M₁ M₂
≈⇒≈↑ (Star._◅_ (Sym.bwd x) xs) =
  let Δ₁ , d , M₁ = ≈′⇒≈′↑ x
      Δ₂ , ds , M₂ = ≈⇒≈↑ xs
  in Δ₁ ++ Δ₂ , d ◅ᵇ ds , AllP.++⁺ M₁ M₂

≼⇒≼↑ : Γ ∶ γ₁ ≼ γ₂ → Σ[ Δ ∈ CSet ] (Γ ∶ γ₁ ≼ γ₂ ↑ Δ) × All MobHolds Δ
≼⇒≼↑ (≼-refl d) = let Δ , d′ , MH = ≈⇒≈↑ d in Δ , ≼-refl↑ d′ , MH
≼⇒≼↑ (≼-∅ U)    = [] , ≼-∅↑ U , []
≼⇒≼↑ ≼-wk       = [] , ≼-wk↑ , []
≼⇒≼↑ (≼-trans d e) =
  let Δ₁ , d′ , M₁ = ≼⇒≼↑ d
      Δ₂ , e′ , M₂ = ≼⇒≼↑ e
  in Δ₁ ++ Δ₂ , ≼-trans↑ d′ e′ , AllP.++⁺ M₁ M₂
≼⇒≼↑ (≼-cong-; d e) =
  let Δ₁ , d′ , M₁ = ≼⇒≼↑ d
      Δ₂ , e′ , M₂ = ≼⇒≼↑ e
  in Δ₁ ++ Δ₂ , ≼-cong-sq↑ d′ e′ , AllP.++⁺ M₁ M₂
≼⇒≼↑ (≼-cong-∥ d e) =
  let Δ₁ , d′ , M₁ = ≼⇒≼↑ d
      Δ₂ , e′ , M₂ = ≼⇒≼↑ e
  in Δ₁ ++ Δ₂ , ≼-cong-par↑ d′ e′ , AllP.++⁺ M₁ M₂

------------------------------------------------------------------------
-- The inverse: constraints that hold outright may be erased.  Together with
-- ≼⇒≼↑ this says that ≼↑ is a conservative refinement of ≼.

≈′↑-erase : All MobHolds Δ → Γ ∶ α ≈′ β ↑ Δ → Γ ∶ α ≈′ β
≈′↑-erase MH sq′-assoc↑     = ;′-assoc
≈′↑-erase MH (sq′-cong₁↑ d) = ;′-cong₁ (≈′↑-erase MH d)
≈′↑-erase MH (sq′-cong₂↑ d) = ;′-cong₂ (≈′↑-erase MH d)
≈′↑-erase MH ∥′-unit↑       = ∥′-unit
≈′↑-erase MH ∥′-assoc↑      = ∥′-assoc
≈′↑-erase MH ∥′-comm↑       = ∥′-comm
≈′↑-erase MH (∥′-cong₁↑ d)  = ∥′-cong₁ (≈′↑-erase MH d)
≈′↑-erase MH (∥′-dup↑ U)    = ∥′-dup U
≈′↑-erase MH ∥′-tmˡ↑ = ∥′-tm-; (inj₁ (allMobile-holds⁻¹ _ MH))
≈′↑-erase MH ∥′-tmʳ↑ = ∥′-tm-; (inj₂ (allMobile-holds⁻¹ _ MH))

≈↑-erase : All MobHolds Δ → Γ ∶ α ≈ β ↑ Δ → Γ ∶ α ≈ β
≈↑-erase MH ε↑ = Star.ε
≈↑-erase MH (_◅ᶠ_ {Δ₁ = Δ} d ds) =
  Star._◅_ (Sym.fwd (≈′↑-erase (AllP.++⁻ˡ Δ MH) d)) (≈↑-erase (AllP.++⁻ʳ Δ MH) ds)
≈↑-erase MH (_◅ᵇ_ {Δ₁ = Δ} d ds) =
  Star._◅_ (Sym.bwd (≈′↑-erase (AllP.++⁻ˡ Δ MH) d)) (≈↑-erase (AllP.++⁻ʳ Δ MH) ds)

≼↑-erase : All MobHolds Δ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → Γ ∶ γ₁ ≼ γ₂
≼↑-erase MH (≼-refl↑ d) = ≼-refl (≈↑-erase MH d)
≼↑-erase MH (≼-∅↑ U)    = ≼-∅ U
≼↑-erase MH ≼-wk↑       = ≼-wk
≼↑-erase MH (≼-trans↑ {Δ₁ = Δ} d e) =
  ≼-trans (≼↑-erase (AllP.++⁻ˡ Δ MH) d) (≼↑-erase (AllP.++⁻ʳ Δ MH) e)
≼↑-erase MH (≼-cong-sq↑ {Δ₁ = Δ} d e) =
  ≼-cong-; (≼↑-erase (AllP.++⁻ˡ Δ MH) d) (≼↑-erase (AllP.++⁻ʳ Δ MH) e)
≼↑-erase MH (≼-cong-par↑ {Δ₁ = Δ} d e) =
  ≼-cong-∥ (≼↑-erase (AllP.++⁻ˡ Δ MH) d) (≼↑-erase (AllP.++⁻ʳ Δ MH) e)
