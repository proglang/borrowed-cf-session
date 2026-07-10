-- | Measure-carrying variants of the RU-Struct reflectors.
--
--   Identical bodies to RUStructDispatch.{νswap,νcomm,νφsync}-reflect and
--   PhiCommReflect.φcomm-reflect, but the `rec` hypothesis carries a
--   well-founded measure bound (∣ r ∣ < N), and each reflector discharges that
--   bound for the transported reduction it fires — using RUStructWF's ∣-red /
--   ∣-substL lemmas.  This is exactly what lets  rec = sim←ᵍ (at a smaller Acc)
--   drive the reverse RU-Struct dispatch as a NON-pragma well-founded recursion.
module BorrowedCF.Simulation2.Backward.RUStructWFReflect where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RedRename using (red-⋯ₚ)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-trans; ≋⇒≈)
open import BorrowedCF.Simulation.RevCongStrong using (∣_∣)
open import BorrowedCF.Simulation2.Backward.RUStructDispatch
  using (Res; swapₚ-invU; assocSwapₚ-invU)
open import BorrowedCF.Simulation2.Backward.RUStructWF using (∣-red; ∣-substL)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Data.Nat using (_<_)

open Fin.Patterns

------------------------------------------------------------------------
-- ν-swap′
------------------------------------------------------------------------

νswap-fire-∣ : ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → {body : UP.Proc (2 + n)} (imgeq : U[ P ] σ ≡ UP.ν body)
  → {T : UP.Proc (2 + n)} (sub : (body UP.⋯ₚ swapᵣ 1 1) UR.─→ₚ T)
  → ∣ subst (λ Z → Z UR.─→ₚ UP.ν (T UP.⋯ₚ swapᵣ 1 1)) (sym imgeq)
        (UR.RU-Res (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ swapᵣ 1 1)) (swapₚ-invU body)
                          (red-⋯ₚ (swapᵣ 1 1) sub))) ∣
    ≡ suc ∣ sub ∣
νswap-fire-∣ σ imgeq sub =
  ∣-substL (sym imgeq) (UR.RU-Res _)
  ■ cong suc (∣-substL (swapₚ-invU _) (red-⋯ₚ (swapᵣ 1 1) sub) ■ ∣-red (swapᵣ 1 1) sub)

νswap-reflect-m :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m} {N : ℕ}
  → (rec : ∀ {Q′} (r : U[ P ] σ UR.─→ₚ Q′) → ∣ r ∣ < N → Res σ P Q′)
  → {body : UP.Proc (2 + n)} (imgeq : U[ P ] σ ≡ UP.ν body)
  → {T : UP.Proc (2 + n)} (sub : (body UP.⋯ₚ swapᵣ 1 1) UR.─→ₚ T)
  → suc ∣ sub ∣ < N
  → Res σ P (UP.ν T)
νswap-reflect-m σ {P} {N} rec {body} imgeq {T} sub bnd
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (T UP.⋯ₚ swapᵣ 1 1)) (sym imgeq)
          (UR.RU-Res (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ swapᵣ 1 1)) (swapₚ-invU body)
                            (red-⋯ₚ (swapᵣ 1 1) sub))))
        (subst (_< N) (sym (νswap-fire-∣ σ imgeq sub)) bnd)
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.return (UP.ν-swap′ {P = T}))) codom

------------------------------------------------------------------------
-- ν-comm′
------------------------------------------------------------------------

νcomm-fire-∣ : ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → {body : UP.Proc (2 + (2 + n))} (imgeq : U[ P ] σ ≡ UP.ν (UP.ν body))
  → {T : UP.Proc (2 + (2 + n))} (sub : (body UP.⋯ₚ assocSwapᵣ 2 2) UR.─→ₚ T)
  → ∣ subst (λ Z → Z UR.─→ₚ UP.ν (UP.ν (T UP.⋯ₚ assocSwapᵣ 2 2))) (sym imgeq)
        (UR.RU-Res (UR.RU-Res
          (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 2 2)) (assocSwapₚ-invU {2} {2} body)
                 (red-⋯ₚ (assocSwapᵣ 2 2) sub)))) ∣
    ≡ suc (suc ∣ sub ∣)
νcomm-fire-∣ σ imgeq sub =
  ∣-substL (sym imgeq) (UR.RU-Res (UR.RU-Res _))
  ■ cong suc (cong suc
      (∣-substL (assocSwapₚ-invU {2} {2} _) (red-⋯ₚ (assocSwapᵣ 2 2) sub)
       ■ ∣-red (assocSwapᵣ 2 2) sub))

νcomm-reflect-m :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m} {N : ℕ}
  → (rec : ∀ {Q′} (r : U[ P ] σ UR.─→ₚ Q′) → ∣ r ∣ < N → Res σ P Q′)
  → {body : UP.Proc (2 + (2 + n))} (imgeq : U[ P ] σ ≡ UP.ν (UP.ν body))
  → {T : UP.Proc (2 + (2 + n))} (sub : (body UP.⋯ₚ assocSwapᵣ 2 2) UR.─→ₚ T)
  → suc (suc ∣ sub ∣) < N
  → Res σ P (UP.ν (UP.ν T))
νcomm-reflect-m σ {P} {N} rec {body} imgeq {T} sub bnd
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (UP.ν (T UP.⋯ₚ assocSwapᵣ 2 2))) (sym imgeq)
          (UR.RU-Res (UR.RU-Res
            (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 2 2)) (assocSwapₚ-invU {2} {2} body)
                   (red-⋯ₚ (assocSwapᵣ 2 2) sub)))))
        (subst (_< N) (sym (νcomm-fire-∣ σ imgeq sub)) bnd)
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.return (UP.ν-comm′ {P = T}))) codom

------------------------------------------------------------------------
-- νφ-comm′ SYNC escape
------------------------------------------------------------------------

νφsync-fire-∣ : ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → {x : UP.Flag} {P′body : UP.Proc (1 + (2 + n))} (imgeq : U[ P ] σ ≡ UP.ν (UP.φ x P′body))
  → {Z : UP.Proc (2 + (1 + n))} (r : (P′body UP.⋯ₚ assocSwapᵣ 1 2) UR.─→ₚ Z)
  → ∣ subst (λ W → W UR.─→ₚ UP.ν (UP.φ x (Z UP.⋯ₚ assocSwapᵣ 2 1))) (sym imgeq)
        (UR.RU-Res (UR.RU-Sync
          (subst (λ W → W UR.─→ₚ (Z UP.⋯ₚ assocSwapᵣ 2 1)) (assocSwapₚ-invU {1} {2} P′body)
                 (red-⋯ₚ (assocSwapᵣ 2 1) r)))) ∣
    ≡ suc (suc ∣ r ∣)
νφsync-fire-∣ σ imgeq r =
  ∣-substL (sym imgeq) (UR.RU-Res (UR.RU-Sync _))
  ■ cong suc (cong suc
      (∣-substL (assocSwapₚ-invU {1} {2} _) (red-⋯ₚ (assocSwapᵣ 2 1) r)
       ■ ∣-red (assocSwapᵣ 2 1) r))

νφsync-reflect-m :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m} {N : ℕ}
  → (rec : ∀ {Q′} (rr : U[ P ] σ UR.─→ₚ Q′) → ∣ rr ∣ < N → Res σ P Q′)
  → {x : UP.Flag} {P′body : UP.Proc (1 + (2 + n))} (imgeq : U[ P ] σ ≡ UP.ν (UP.φ x P′body))
  → {Z : UP.Proc (2 + (1 + n))} (r : (P′body UP.⋯ₚ assocSwapᵣ 1 2) UR.─→ₚ Z)
  → suc (suc ∣ r ∣) < N
  → Res σ P (UP.φ x (UP.ν Z))
νφsync-reflect-m σ {P} {N} rec {x} {P′body} imgeq {Z} r bnd
  with P′ , steps , codom ←
    rec (subst (λ W → W UR.─→ₚ UP.ν (UP.φ x (Z UP.⋯ₚ assocSwapᵣ 2 1))) (sym imgeq)
          (UR.RU-Res (UR.RU-Sync
            (subst (λ W → W UR.─→ₚ (Z UP.⋯ₚ assocSwapᵣ 2 1)) (assocSwapₚ-invU {1} {2} P′body)
                   (red-⋯ₚ (assocSwapᵣ 2 1) r)))))
        (subst (_< N) (sym (νφsync-fire-∣ σ imgeq r)) bnd)
  = P′ , steps
  , ≈-trans (≋⇒≈ (Eq*.symmetric _
      (subst (λ W → UP.ν (UP.φ x (Z UP.⋯ₚ assocSwapᵣ 2 1)) UP.≋ UP.φ x (UP.ν W))
             (assocSwapₚ-invU {2} {1} Z)
             (Eq*.return (UP.νφ-comm′ {x = x})))))
      codom

------------------------------------------------------------------------
-- φ-comm′
------------------------------------------------------------------------

φcomm-fire-∣ : ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → {x y : UP.Flag} {body : UP.Proc (2 + (2 + n))}
    (imgeq : U[ P ] σ ≡ UP.ν (UP.φ x (UP.φ y body)))
  → {T : UP.Proc (2 + (2 + n))} (sub : (body UP.⋯ₚ assocSwapᵣ 1 1) UR.─→ₚ T)
  → ∣ subst (λ Z → Z UR.─→ₚ UP.ν (UP.φ x (UP.φ y (T UP.⋯ₚ assocSwapᵣ 1 1)))) (sym imgeq)
        (UR.RU-Res (UR.RU-Sync (UR.RU-Sync
          (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 1 1)) (assocSwapₚ-invU {1} {1} body)
                 (red-⋯ₚ (assocSwapᵣ 1 1) sub))))) ∣
    ≡ suc (suc (suc ∣ sub ∣))
φcomm-fire-∣ σ imgeq sub =
  ∣-substL (sym imgeq) (UR.RU-Res (UR.RU-Sync (UR.RU-Sync _)))
  ■ cong suc (cong suc (cong suc
      (∣-substL (assocSwapₚ-invU {1} {1} _) (red-⋯ₚ (assocSwapᵣ 1 1) sub)
       ■ ∣-red (assocSwapᵣ 1 1) sub)))

φcomm-reflect-m :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m} {N : ℕ}
  → (rec : ∀ {Q′} (r : U[ P ] σ UR.─→ₚ Q′) → ∣ r ∣ < N → Res σ P Q′)
  → {x y : UP.Flag} {body : UP.Proc (2 + (2 + n))}
    (imgeq : U[ P ] σ ≡ UP.ν (UP.φ x (UP.φ y body)))
  → {T : UP.Proc (2 + (2 + n))} (sub : (body UP.⋯ₚ assocSwapᵣ 1 1) UR.─→ₚ T)
  → suc (suc (suc ∣ sub ∣)) < N
  → Res σ P (UP.ν (UP.φ y (UP.φ x T)))
φcomm-reflect-m σ {P} {N} rec {x} {y} {body} imgeq {T} sub bnd
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (UP.φ x (UP.φ y (T UP.⋯ₚ assocSwapᵣ 1 1)))) (sym imgeq)
          (UR.RU-Res (UR.RU-Sync (UR.RU-Sync
            (subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 1 1)) (assocSwapₚ-invU {1} {1} body)
                   (red-⋯ₚ (assocSwapᵣ 1 1) sub))))))
        (subst (_< N) (sym (φcomm-fire-∣ σ imgeq sub)) bnd)
  = P′ , steps
  , ≈-trans (≋⇒≈ (Eq*.symmetric _
      (subst (λ W → UP.ν (UP.φ x (UP.φ y (T UP.⋯ₚ assocSwapᵣ 1 1))) UP.≋ UP.ν (UP.φ y (UP.φ x W)))
             (assocSwapₚ-invU {1} {1} T)
             (UP.ν-cong (Eq*.return (UP.φ-comm′ {x = x} {y = y}))))))
      codom
