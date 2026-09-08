-- | Mechanical validation of the base change proposed in `Completeness/Sub-STATUS.md`.
--   Each lemma below is exactly the obligation the corresponding case of
--   `BorrowedCF.Algorithmic.sound` has to discharge once the `≼` premise of the rule
--   becomes `≼ ↑ Δ₀` and `Δ₀` is prepended to the rule's output constraints.  Nothing
--   here is used by the rest of the development; it exists to show that the proposed
--   rule shapes type-check.
module BorrowedCF.Completeness.Sub.Probe where

open import Data.Fin.Subset using (Subset; ∁)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Context.Base using (module Variables)
open import BorrowedCF.Context.Domain using (_↓_)
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Sub

open Nat.Variables
open Variables

module _ {σ : UV.Sub} (Sσ : Solving σ) where

  -- A-Var / A-Const / A-LSplit / A-RSplit: output constraints = Δ₀
  probe-nullary : {Γ : Ctx n} → SolvedΔ Δ σ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ → subCtx Γ σ ∶ γ₁ ≼ γ₂
  probe-nullary = ≼↑-sound Sσ

  -- A-App / A-Seq / A-Pair: output constraints = Δ₀ ++ Δ₁ ++ Δ₂
  probe-binary : {Γ : Ctx n} (Δ₀ Δ₁ : CSet) {Δ₂ : CSet} →
    SolvedΔ (Δ₀ ++ Δ₁ ++ Δ₂) σ → Γ ∶ γ₁ ≼ γ₂ ↑ Δ₀ →
    (subCtx Γ σ ∶ γ₁ ≼ γ₂) × SolvedΔ Δ₁ σ × SolvedΔ Δ₂ σ
  probe-binary Δ₀ Δ₁ SΔ d =
      ≼↑-sound Sσ (AllP.++⁻ˡ Δ₀ SΔ) d
    , AllP.++⁻ˡ Δ₁ (AllP.++⁻ʳ Δ₀ SΔ)
    , AllP.++⁻ʳ Δ₁ (AllP.++⁻ʳ Δ₀ SΔ)

  -- A-LetPair / A-Let: the sequential premise still feeds `parOrSeq?`
  probe-letpair : {Γ : Ctx n} (Δ₀ : CSet) {Δ₁ Δ₂ : CSet} →
    SolvedΔ (Δ₀ ++ Δ₁ ++ Δ₂) σ → Γ ∶ α ; β ≼ γ ↑ Δ₀ →
    Σ[ p/s ∈ ParSeq ] subCtx Γ σ ∶ join p/s α β ≼ γ
  probe-letpair Δ₀ SΔ d = parOrSeq? (≼↑-sound Sσ (AllP.++⁻ˡ Δ₀ SΔ) d)

  -- A-Case: output constraints = C-Eq U₁ U₂ ∷ Δ₀ ++ Δ ++ Δ₁ ++ Δ₂
  probe-case : {Γ : Ctx n} {X : Subset n} {p/s : ParSeq} {U₁ U₂ : 𝕋}
    (Δ₀ Δ : CSet) {Δ₁ Δ₂ : CSet} →
    SolvedΔ (C-Eq U₁ U₂ L.∷ Δ₀ ++ Δ ++ Δ₁ ++ Δ₂) σ → JoinParSeq↑ Γ γ X p/s Δ₀ →
    subCtx Γ σ ∶ join p/s (γ ↓ X) (γ ↓ ∁ X) ≼ γ
  probe-case Δ₀ Δ (_ ∷ SΔ) j = ≼↑-sound Sσ (AllP.++⁻ˡ Δ₀ SΔ) (join-joinParSeq↑ j)
