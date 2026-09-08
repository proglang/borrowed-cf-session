-- | The `R-Close` synchronisation: `end ‼` and `end ⁇` on the two head handles
--   of one `ν` reduce.
--
--   Three steps beyond `Sync/Com.agda`.
--     * `R-Close` fires only on `ν [ 1 ] [ 1 ]`, so `Sync/CloseShape.close-shape`
--       first collapses both binder groups (`close-handle-end` reads the two
--       head sessions off the two threads).
--     * `R-Close` has NO parallel residual, so the residual collected by
--       `canon-pair` is pushed OUT of the binder with `ν-ext′` read backwards.
--       That is legitimate because `close-pair-confine` shows the residual
--       factors through `wkₚ 0 0`, which is `weaken* 2` (`wkₚ00`), exactly the
--       renaming `ν-ext′` undoes.
--     * The two frames are then strengthened by `close-confine`, in the
--       residual-free form the rule wants.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Close where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Vec.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Processes.Congruence using (_/_⊢-≋_)
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_; R-Close; R-Struct)

open import BorrowedCF.Safety.Progress.Expr.Plug using (⋯ᶠ*-[]*)
open import BorrowedCF.Safety.Progress.Redex.Context using (red-in-ctx)
open import BorrowedCF.Safety.Progress.Sync.Locate using (plug-typing⁺)
open import BorrowedCF.Safety.Progress.Sync.CloseShape using (close-shape)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-right; plug; ≡→≋; ≋-plug)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using (ProcessContext₂; plug₂; Binder₂; CanonPair; canonPair; canon-pair; HeadShape₂)
open import BorrowedCF.Simulation.Support.PairConfine
  using (close-handle-end; close-pair-confine; close-confine)

open Nat.Variables
open Variables
open Fin.Patterns

private
  -- `wkₚ 0 0` is `weaken* 2`, the renaming `ν-ext′` introduces.
  wkₚ00 : ∀ {n} (y : 𝔽 n) → wkₚ {n} 0 0 y ≡ weaken* ⦃ Kᵣ ⦄ 2 y
  wkₚ00 {n} y =
    cong (λ z → Fin.cast (sym (+-assoc 1 1 n)) ((weakenᵣ ↑* 1) z))
         (Fin.cast-is-id (cong suc (+-assoc 0 0 n)) (suc y))
    ■ Fin.cast-is-id (sym (+-assoc 1 1 n)) (suc (suc y))
    ■ sym (weaken*~wkˡ ⦃ Kᵣ ⦄ 2 y)

  -- Both binder groups of a closing restriction are `[ 1 ]`.
  close-groups : ∀ {mid} {Γ : Ctx mid} {γ : Struct mid} (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    (F₁ F₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid))
    (resid : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)) → ChanCx Γ →
    Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
        ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` wkʳ ⦃ Kᵣ ⦄ mid
                    (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))) ]* ⟫)
       ∥ resid) →
    (b₁ ≡ 0 × B₁ ≡ []) × (b₂ ≡ 0 × B₂ ≡ [])
  close-groups {mid} {Γ} b₁ b₂ B₁ B₂ F₁ F₂ resid Γ-S ⊢ν
    with Γ₁ , Γ₂ , s , p , N , _ , _ , C , C′ , ⊢body ← inv-ν ⊢ν
    with _ , _ , _ , ⊢pair , _ ← inv-∥ ⊢body
    with _ , _ , _ , ⊢th₁ , ⊢th₂ ← inv-∥ ⊢pair
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r₁ ← ⊢[]*⁻¹ F₁ _ (inv-⟪⟫ ⊢th₁)
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r₂ ← ⊢[]*⁻¹ F₂ _ (inv-⟪⟫ ⊢th₂) =
    close-shape N C lk₁ (close-handle-end ⊢r₁ eq₁) ,
    close-shape (new-dual N) C′ lk₂ (close-handle-end ⊢r₂ eq₂)
    where
    Γ-body : ChanCx ((Γ₁ ⸴* Γ₂) ⸴* Γ)
    Γ-body = ++⁺ (++⁺ (bindCtx⇒chanCtx C) (bindCtx⇒chanCtx C′)) Γ-S

    t₁ = proj₁ (chanCx-lookup Γ-body 0F)
    eq₁ = proj₂ (chanCx-lookup Γ-body 0F)

    t₂ = proj₁ (chanCx-lookup Γ-body
                 (wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))))
    eq₂ = proj₂ (chanCx-lookup Γ-body
                 (wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))))

    lk₁ : Γ₁ ﹫ 0F ≡ ⟨ t₁ ⟩
    lk₁ = sym (V.lookup-++ˡ Γ₁ Γ₂ 0F) ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ 0F) ■ eq₁

    lk₂ : Γ₂ ﹫ 0F ≡ ⟨ t₂ ⟩
    lk₂ = sym (V.lookup-++ʳ Γ₁ Γ₂ 0F)
        ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (sum (suc b₁ ∷ B₁) ↑ʳ 0F)) ■ eq₂

  -- The residual has been pushed out; strengthen the frames and fire the rule.
  close-go₂ : ∀ {mid} (above′ : ProcessContext mid 0)
    (F₁ F₂ : Frame* (suc (suc mid))) (P₀ : Proc mid) →
    [] ; [] ⊢ₚ plug above′ (P₀ ∥ ν (1 ∷ []) (1 ∷ [])
      (⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫ ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫)) →
    Σ[ P′ ∈ Proc 0 ]
      plug above′ (P₀ ∥ ν (1 ∷ []) (1 ∷ [])
        (⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫ ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫)) ─→ₚ P′
  close-go₂ {mid} above′ F₁ F₂ P₀ ⊢P
    with _ , _ , Γ-S , ⊢par , _ ←
      plug-typing⁺ above′
        (P₀ ∥ ν (1 ∷ []) (1 ∷ [])
          (⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫ ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫))
        []ᴬ ⊢P
    with _ , _ , _ , _ , ⊢ν ← inv-∥ ⊢par
    with (E₁₀ , F₁eq) , (E₂₀ , F₂eq) ← close-confine Γ-S {E₁ = F₁} {E₂ = F₂} ⊢ν =
    _ , R-Struct (≋-plug above′ (≡→≋ (cong (P₀ ∥_) shapeEq)))
          (red-in-ctx above′ (red-in-ctx (par-right P₀ hole) step)) ≋-refl
    where
    lhs : Proc mid
    lhs = ν (1 ∷ []) (1 ∷ [])
            (⟪ (E₁₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ‼) ·¹ (` 0F) ]* ⟫
             ∥ ⟪ (E₂₀ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ K (`end ⁇) ·¹ (` 1F) ]* ⟫)

    step : lhs ─→ₚ _
    step = R-Close {E₁ = E₁₀} {E₂ = E₂₀}

    shapeEq :
      ν (1 ∷ []) (1 ∷ [])
        (⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫ ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫) ≡ lhs
    shapeEq = cong (ν _ _) (cong₂ _∥_
      (cong ⟪_⟫ (cong (λ F → F [ K (`end ‼) ·¹ (` 0F) ]*) F₁eq))
      (cong ⟪_⟫ (cong (λ F → F [ K (`end ⁇) ·¹ (` 1F) ]*) F₂eq)))

  -- The canonical form, with the residual still inside the binder.
  close-go : ∀ {mid} (above′ : ProcessContext mid 0) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup)
    (F₁ F₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid))
    (resid : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)) →
    (let body = (⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
                  ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` wkʳ ⦃ Kᵣ ⦄ mid
                             (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))) ]* ⟫)
                 ∥ resid) →
    [] ; [] ⊢ₚ plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) body) →
    Σ[ P′ ∈ Proc 0 ] plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) body) ─→ₚ P′
  close-go {mid} above′ b₁ b₂ B₁ B₂ F₁ F₂ resid ⊢P
    with _ , _ , Γ-S , ⊢ν , _ ←
      plug-typing⁺ above′
        (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
            ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` wkʳ ⦃ Kᵣ ⦄ mid
                       (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))) ]* ⟫)
           ∥ resid))
        []ᴬ ⊢P
    with (refl , refl) , (refl , refl) ← close-groups b₁ b₂ B₁ B₂ F₁ F₂ resid Γ-S ⊢ν
    with _ , _ , _ , _ , P₀ , Peq ←
      close-pair-confine Γ-S {E₁ = F₁} {E₂ = F₂} {P = resid} ⊢ν =
    let chain = ≡→≋ (cong (λ z →
                       ν (1 ∷ []) (1 ∷ [])
                         ((⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
                           ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` 1F) ]* ⟫) ∥ z))
                       (Peq ■ ⋯ₚ-cong P₀ wkₚ00))
                  ◅◅ ν-cong 𝐓.∥-comm
                  ◅◅ (bwd ν-ext′ ◅ ≋-refl)
        _ , red = close-go₂ above′ F₁ F₂ P₀ ([]ᴬ / ⊢P ⊢-≋ ≋-plug above′ chain)
    in _ , R-Struct (≋-plug above′ chain) red ≋-refl

close-step : {k₁ k₂ : ℕ} {c : ProcessContext₂ k₁ k₂ 0} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  (bnd : Binder₂ c x₁ x₂) →
  HeadShape₂ (Binder₂.C₁ bnd) (Binder₂.C₂ bnd) (Binder₂.local₁ bnd) (Binder₂.local₂ bnd) →
  (E₁ : Frame* k₁) (E₂ : Frame* k₂) →
  [] ; [] ⊢ₚ plug₂ c ⟪ E₁ [ K (`end ‼) ·¹ (` x₁) ]* ⟫ ⟪ E₂ [ K (`end ⁇) ·¹ (` x₂) ]* ⟫ →
  Σ[ P′ ∈ Proc 0 ]
    plug₂ c ⟪ E₁ [ K (`end ‼) ·¹ (` x₁) ]* ⟫ ⟪ E₂ [ K (`end ⁇) ·¹ (` x₂) ]* ⟫ ─→ₚ P′
close-step {x₁ = x₁} {x₂ = x₂} bnd hs E₁ E₂ ⊢P
  with canon-pair (E₁ [ K (`end ‼) ·¹ (` x₁) ]*) (E₂ [ K (`end ⁇) ·¹ (` x₂) ]*) bnd hs
... | canonPair {midᵖ = mid} b₁ b₂ B₁ B₂ above′ ρ₁ ρ₂ resid ≋c xeq₁ xeq₂ _ _ =
  let ≋all = ≋c ◅◅ ≡→≋ shapeEq₀
      _ , red = close-go above′ b₁ b₂ B₁ B₂ (E₁ ⋯ᶠ* ρ₁) (E₂ ⋯ᶠ* ρ₂) resid
                  ([]ᴬ / ⊢P ⊢-≋ ≋all)
  in _ , R-Struct ≋all red ≋-refl
  where
  F₁ = E₁ ⋯ᶠ* ρ₁
  F₂ = E₂ ⋯ᶠ* ρ₂

  hd₂ : 𝔽 (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + mid)
  hd₂ = wkʳ ⦃ Kᵣ ⦄ mid (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) (Fin.zero {b₂ + sum B₂}))

  shapeEq₀ :
    plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((⟪ (E₁ [ K (`end ‼) ·¹ (` x₁) ]*) ⋯ ρ₁ ⟫
        ∥ ⟪ (E₂ [ K (`end ⁇) ·¹ (` x₂) ]*) ⋯ ρ₂ ⟫) ∥ resid))
      ≡ plug above′ (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
          ((⟪ F₁ [ K (`end ‼) ·¹ (` 0F) ]* ⟫
            ∥ ⟪ F₂ [ K (`end ⁇) ·¹ (` hd₂) ]* ⟫) ∥ resid))
  shapeEq₀ = cong (plug above′) (cong (ν _ _) (cong₂ _∥_ (cong₂ _∥_
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₁ _ ρ₁
        ■ cong (λ z → F₁ [ K (`end ‼) ·¹ (` z) ]*) xeq₁))
      (cong ⟪_⟫ (⋯ᶠ*-[]* E₂ _ ρ₂
        ■ cong (λ z → F₂ [ K (`end ⁇) ·¹ (` z) ]*) xeq₂)))
      refl))
