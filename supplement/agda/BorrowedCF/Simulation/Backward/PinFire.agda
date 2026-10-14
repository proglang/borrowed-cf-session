-- | Backward simulation, RU-LSplit — Stages B/C (typed rearrangement + fire).
--
--   `fire-node` closes the typed-step half of `pin-lsplit-fire`'s NODE case:
--   given the prenex decomposition `t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂` and a redex thread
--   `F₀ [ K (`lsplit s) ·¹ (` wkTelᵗ t₂ (z ↑ˡ a)) ]*` in the thread list, it
--
--     1. sinks the binding node to the INNERMOST position (PinFireBase's
--        node-to-backᵗ — no support/strengthening analysis is needed because
--        the thread lives at the prenex inner scope, which is exactly the
--        sunk ν's body scope),
--     2. brings the redex thread to the front of the flat thread list,
--     3. splits `z` between the node's two groups (ν-swap′ for the second),
--     4. decomposes the group at `z` into R-LSplit's rigid
--        `B₁ ++ (q + suc b₁) ∷ B₂` / `𝐒.atk (q ↑ʳ 0F)` shape (groupAt/atk-eq)
--        and fires, wrapped in R-Bind through the outer telescope and
--        R-Struct for the ≋-rearrangement.
--
--   The produced typed step is SINGLE (`P ─→ₚ P′`); the caller star-wraps it.
--   The codomain reconciliation (Stage D) is NOT here — the returned `P′` is
--   concrete, so the caller can feed the step to `sim→` for the image step.
--
--   STATUS: CLOSED (no holes).  Consumed by Backward.PinLSplit.
module BorrowedCF.Simulation.Backward.PinFire where

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed as TR

open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.TypedFocus using (deleteᵗ; pars-∈ᵗ; ∈-mapᵗ)
open import BorrowedCF.Simulation.Backward.PinFireBase
open import BorrowedCF.Simulation.Backward.PinConj using (splitAt-inv₁; splitAt-inv₂)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin.Properties using (toℕ-↑ˡ)
open import Data.Product using (Σ-syntax; _,_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)

------------------------------------------------------------------------
-- The core fire: the node is innermost, the thread is leftmost.
------------------------------------------------------------------------

fire-core :
  ∀ {m a} (TT : TTel m a) (H₁ H₂ : BindGroup) (s : 𝕊 0)
    (F₁ : Frame* (sum H₁ + sum H₂ + a)) (z₁ : 𝔽 (sum H₁))
    (es : List (Tm (sum H₁ + sum H₂ + a))) →
  Σ[ P′ ∈ Proc m ]
    (plugᵗ TT (ν H₁ H₂ (⟪ F₁ [ K (`lsplit s) ·¹ (` ((z₁ ↑ˡ sum H₂) ↑ˡ a)) ]* ⟫ ∥ parsᵗ es))
       TR.─→ₚ P′)
fire-core {m} {a} TT H₁ H₂ s F₁ z₁ es
  with mkGroupAt B₁ B₂ q b₁ geq zn ← groupAt H₁ z₁
  rewrite geq
  = _ , step-plugᵗ TT
        (TR.R-Struct
          (≡→≋ᵗ (cong (λ v → ν (B₁ ++ (q + suc b₁) ∷ B₂) H₂
                                 (⟪ F₁ [ K (`lsplit s) ·¹ (` v) ]* ⟫ ∥ parsᵗ es))
                  (atk-eq B₁ B₂ q b₁ (sum H₂) a ((z₁ ↑ˡ sum H₂) ↑ˡ a)
                     (toℕ-↑ˡ (z₁ ↑ˡ sum H₂) a ■ toℕ-↑ˡ z₁ (sum H₂) ■ zn))))
          (TR.R-LSplit {B₁ = B₁} {B₂ = B₂} {q = q} {b₁ = b₁} {s = s}
             {E = F₁})
          ε)

------------------------------------------------------------------------
-- The node fire: sink, front the thread, split on the group, fire.
------------------------------------------------------------------------

fire-node :
  ∀ {m aN bN} {P : Proc m}
    (t₁ : TTel m aN) (B₁ B₂ : BindGroup)
    (t₂ : TTel (sum B₁ + sum B₂ + aN) bN)
    (es : List (Tm bN))
  → P ≋ plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) (parsᵗ es)
  → (s : 𝕊 0) (F₀ : Frame* bN) (z : 𝔽 (sum B₁ + sum B₂))
  → (F₀ [ K (`lsplit s) ·¹ (` wkTelᵗ t₂ (z ↑ˡ aN)) ]*) ∈ es
  → Σ[ P′ ∈ Proc m ] (P TR.─→ₚ P′)
fire-node {m} {aN} {bN} {P = P} t₁ B₁ B₂ t₂ es snd s F₀ z i =
  go (splitAt (sum B₁) z) refl
  where
    b   = sum B₁ + sum B₂
    Sk  = sinkN (lenᵗ t₂) b t₂ refl
    aI  = sscope Sk
    ρ★  = sρ Sk
    TT  = t₁ ++ᵗᵗ stel Sk
    es★ = map (_⋯ ρ★) es
    e†  = F₀ [ K (`lsplit s) ·¹ (` wkTelᵗ t₂ (z ↑ˡ aN)) ]*
    i★  = ∈-mapᵗ ρ★ i
    rest = deleteᵗ es★ i★
    F₁  = F₀ ⋯ᶠ* ρ★

    thr-eq : e† ⋯ ρ★ ≡ F₁ [ K (`lsplit s) ·¹ (` (z ↑ˡ aI)) ]*
    thr-eq =
        frame-plug*ᵣ′ F₀ ρ★
      ■ cong (λ v → F₁ [ K (`lsplit s) ·¹ (` v) ]*)
          (sink-pin (lenᵗ t₂) b t₂ refl z)

    chain₀ : P ≋ plugᵗ TT (ν B₁ B₂ (⟪ F₁ [ K (`lsplit s) ·¹ (` (z ↑ˡ aI)) ]* ⟫ ∥ parsᵗ rest))
    chain₀ =
        snd
      ◅◅ ≡→≋ᵗ (plug-++ᵗᵗ t₁ (tνᵗ B₁ B₂ t₂) (parsᵗ es))
      ◅◅ plug-congᵗ t₁ (node-to-backᵗ (lenᵗ t₂) B₁ B₂ t₂ refl (parsᵗ es))
      ◅◅ ≡→≋ᵗ (sym (plug-++ᵗᵗ t₁ (stel Sk) (ν B₁ B₂ (parsᵗ es ⋯ₚ ρ★))))
      ◅◅ plug-congᵗ TT
           ( ≡→≋ᵗ (cong (ν B₁ B₂) (pars-⋯ₚᵗ es ρ★))
           ◅◅ ν-cong (pars-∈ᵗ es★ i★)
           ◅◅ ≡→≋ᵗ (cong (λ e → ν B₁ B₂ (⟪ e ⟫ ∥ parsᵗ rest)) thr-eq) )

    go : (w : 𝔽 (sum B₁) ⊎ 𝔽 (sum B₂)) → splitAt (sum B₁) z ≡ w →
         Σ[ P′ ∈ Proc m ] (P TR.─→ₚ P′)
    go (inj₁ z₁) zseq =
      let P′ , st = fire-core TT B₁ B₂ s F₁ z₁ rest in
      P′ , TR.R-Struct
             (chain₀
               ◅◅ plug-congᵗ TT (≡→≋ᵗ
                    (cong (λ w → ν B₁ B₂ (⟪ F₁ [ K (`lsplit s) ·¹ (` (w ↑ˡ aI)) ]* ⟫ ∥ parsᵗ rest))
                      (splitAt-inv₁ z zseq))))
             st ε
    go (inj₂ z₂) zseq =
      let sw   = swapᵣ (sum B₁) (sum B₂) {aI}
          F₂   = F₁ ⋯ᶠ* sw
          rest₂ = map (_⋯ sw) rest
          thr-eq₂ : (F₁ [ K (`lsplit s) ·¹ (` (z ↑ˡ aI)) ]*) ⋯ sw
                      ≡ F₂ [ K (`lsplit s) ·¹ (` ((z₂ ↑ˡ sum B₁) ↑ˡ aI)) ]*
          thr-eq₂ =
              frame-plug*ᵣ′ F₁ sw
            ■ cong (λ v → F₂ [ K (`lsplit s) ·¹ (` v) ]*)
                ( cong sw (cong (_↑ˡ aI) (splitAt-inv₂ z zseq))
                ■ swap-mid (sum B₁) (sum B₂) z₂ )
          P′ , st = fire-core TT B₂ B₁ s F₂ z₂ rest₂
      in
      P′ , TR.R-Struct
             (chain₀
               ◅◅ plug-congᵗ TT
                    ( Eq*.return ν-swap′
                    ◅◅ ≡→≋ᵗ (cong₂ (λ e R → ν B₂ B₁ (⟪ e ⟫ ∥ R))
                               thr-eq₂ (pars-⋯ₚᵗ rest sw)) ))
             st ε
