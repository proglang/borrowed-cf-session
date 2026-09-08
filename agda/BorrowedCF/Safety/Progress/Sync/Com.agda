-- | The `R-Com` synchronisation: a `send` and a `recv` on the two head handles
--   of one `ν` reduce.
--
--   Two steps beyond `Sync/Choice.agda`.  `canon-pair` brings the two threads
--   under their common binder, which gives the shape of `R-Choice`; `R-Com`
--   additionally demands that the two frames, the sent value and the residual
--   all factor through `wkₚ`, the renaming that skips BOTH head handles.  That
--   is `Simulation/Support/PairConfine.agda`'s `com-confine`, and it needs the
--   typing of the canonical form -- which `Sync/Locate.plug-typing⁺` extracts
--   after `Processes/Congruence._/_⊢-≋_` has transported the typing along the
--   canonicalisation.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Com where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_; R-Com; R-Struct)

open import BorrowedCF.Safety.Progress.Expr.Plug using (⋯ᶠ*-[]*; value-⋯ᵣ⁻¹)
open import BorrowedCF.Safety.Progress.Redex.Context using (red-in-ctx)
open import BorrowedCF.Safety.Progress.Sync.Locate using (plug-typing⁺)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; plug; ≡→≋)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using (ProcessContext₂; plug₂; Binder₂; CanonPair; canonPair; canon-pair; HeadShape₂)
open import BorrowedCF.Simulation.Support.PairConfine using (com-confine)

open Nat.Variables
open Variables
open Fin.Patterns

private
  -- The canonical form is already the left-hand side of `R-Com` up to the
  -- confinement of the frames, the value and the residual.
  com-go : ∀ {mid} (above′ : ProcessContext mid 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    (F₁ F₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid))
    {w : Tm (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)} (Vw : Value w)
    (resid : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)) →
    (let hd₂ = wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))) →
    (let body = (⟪ F₁ [ K `send ·¹ (w ⊗ (` 0F)) ]* ⟫
                  ∥ ⟪ F₂ [ K `recv ·¹ (` hd₂) ]* ⟫) ∥ resid) →
    [] ; [] ⊢ₚ plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) body) →
    Σ[ P′ ∈ Proc 0 ] plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) body) ─→ₚ P′
  com-go {mid} above′ b₁ b₂ B₁ B₂ F₁ F₂ {w} Vw resid ⊢P
    with _ , _ , Γ-S , ⊢ν , _ ←
      plug-typing⁺ above′
        (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((⟪ F₁ [ K `send ·¹ (w ⊗ (` 0F)) ]* ⟫
            ∥ ⟪ F₂ [ K `recv ·¹ (` wkʳ ⦃ Kᵣ ⦄ mid
                       (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))) ]* ⟫)
            ∥ resid))
        []ᴬ ⊢P
    with E₁₀ , E₁eq , E₂₀ , E₂eq , v₀ , veq , P₀ , Peq ←
      com-confine Γ-S {E₁ = F₁} {E₂ = F₂} {v = w} {P = resid} ⊢ν =
    _ , R-Struct (≡→≋ (cong (plug above′) shapeEq)) (red-in-ctx above′ step) ≋-refl
    where
    wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂)

    hd₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)
    hd₂ = wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

    V₀ : Value v₀
    V₀ = value-⋯ᵣ⁻¹ v₀ wkρ (subst Value veq Vw)

    lhs : Proc mid
    lhs = ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
            ((⟪ (E₁₀ ⋯ᶠ* wkρ) [ K `send ·¹ ((v₀ ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
              ∥ ⟪ (E₂₀ ⋯ᶠ* wkρ) [ K `recv ·¹ (` hd₂) ]* ⟫) ∥ (P₀ ⋯ₚ wkρ))

    step : lhs ─→ₚ _
    step = R-Com {P = P₀} {E₁ = E₁₀} {E₂ = E₂₀} V₀

    shapeEq :
      ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
        ((⟪ F₁ [ K `send ·¹ (w ⊗ (` 0F)) ]* ⟫ ∥ ⟪ F₂ [ K `recv ·¹ (` hd₂) ]* ⟫) ∥ resid)
        ≡ lhs
    shapeEq = cong (ν _ _) (cong₂ _∥_ (cong₂ _∥_
        (cong ⟪_⟫ (cong₂ (λ F u → F [ K `send ·¹ (u ⊗ (` 0F)) ]*) E₁eq veq))
        (cong ⟪_⟫ (cong (λ F → F [ K `recv ·¹ (` hd₂) ]*) E₂eq)))
        Peq)

com-step : {k₁ k₂ : ℕ} {c : ProcessContext₂ k₁ k₂ 0} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd : Binder₂ c x₁ x₂) →
  HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd) (Binder₂.local₁ bnd) (Binder₂.local₂ bnd) →
  (E₁ : Frame* k₁) {v : Tm k₁} (V : Value v) (E₂ : Frame* k₂) →
  [] ; [] ⊢ₚ plug₂ c ⟪ E₁ [ K `send ·¹ (v ⊗ (` x₁)) ]* ⟫ ⟪ E₂ [ K `recv ·¹ (` x₂) ]* ⟫ →
  Σ[ P′ ∈ Proc 0 ]
    plug₂ c ⟪ E₁ [ K `send ·¹ (v ⊗ (` x₁)) ]* ⟫ ⟪ E₂ [ K `recv ·¹ (` x₂) ]* ⟫ ─→ₚ P′
com-step {x₁ = x₁} {x₂ = x₂} bnd hs E₁ {v = v} V E₂ ⊢P
  with canon-pair (E₁ [ K `send ·¹ (v ⊗ (` x₁)) ]*) (E₂ [ K `recv ·¹ (` x₂) ]*) bnd hs
... | canonPair {midᵖ = mid} b₁ b₂ B₁ B₂ above′ ρ₁ ρ₂ resid ≋c xeq₁ xeq₂ _ _ =
  let ≋all = ≋c ◅◅ ≡→≋ shapeEq₀
      _ , red = com-go above′ b₁ b₂ B₁ B₂ (E₁ ⋯ᶠ* ρ₁) (E₂ ⋯ᶠ* ρ₂) (V ⋯ᵛ ρ₁) resid
                  ([]ᴬ / ⊢P ⊢-≋ ≋all)
  in _ , R-Struct ≋all red ≋-refl
  where
  F₁ = E₁ ⋯ᶠ* ρ₁
  F₂ = E₂ ⋯ᶠ* ρ₂
  w  = v ⋯ ρ₁

  hd₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)
  hd₂ = wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

  shapeEq₀ :
    plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ (E₁ [ K `send ·¹ (v ⊗ (` x₁)) ]*) ⋯ ρ₁ ⟫
        ∥ ⟪ (E₂ [ K `recv ·¹ (` x₂) ]*) ⋯ ρ₂ ⟫) ∥ resid))
      ≡ plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((⟪ F₁ [ K `send ·¹ (w ⊗ (` 0F)) ]* ⟫
            ∥ ⟪ F₂ [ K `recv ·¹ (` hd₂) ]* ⟫) ∥ resid))
  shapeEq₀ = cong (plug above′) (cong (ν _ _) (cong₂ _∥_ (cong₂ _∥_
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₁ _ ρ₁
        ■ cong (λ z → F₁ [ K `send ·¹ (w ⊗ (` z)) ]*) xeq₁))
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₂ _ ρ₂
        ■ cong (λ z → F₂ [ K `recv ·¹ (` z) ]*) xeq₂)))
      refl))
