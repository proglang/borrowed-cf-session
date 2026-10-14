-- | Reconcile core for the telescoped backward R-Choice.  Twin of
--   ComReconcile.com-back, but MUCH simpler: R-Choice does NOT consume the
--   channels (the contractum keeps the SAME bind groups B₁′ = suc b₁ ∷ B₁ /
--   B₂′ = suc b₂ ∷ B₂), so there is NO `wkₚ` weakening and NO leaf-collapse
--   (`wkρ-leafσ`) — the fired frames already live in the leaf scope of τ.  The
--   whole reconcile is `∥-assoc` + frame-plug* + `plugΦ-++` + `Uν-flatΦ`.
--   Reuses ComReconcile's Φrest / τ / Vτ verbatim (identical substitution data).
module BorrowedCF.Simulation.Backward.ChoiceReconcile where

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Simulation.Backward.ComReconcile as CR
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation.Support.Theorems.PhiTel using (Btel; leafσ; Uν-flatΦ; plugΦ-++)
open import BorrowedCF.Simulation.Support.Theorems.ComHelpers2 using (plugΦ-cong)
open import BorrowedCF.Simulation.Support.Frames using (frame-plug*; frame*-⋯)
open import BorrowedCF.Simulation.Support.TranslationProperties using (≡→≋)
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; plugΦ)

open Fin.Patterns

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) (b₁ b₂ : ℕ) (B₁ B₂ : BindGroup) where

  private
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂
    τ  = CR.τ  σ Vσ b₁ b₂ B₁ B₂
    Vτ = CR.Vτ σ Vσ b₁ b₂ B₁ B₂
    Φrest = CR.Φrest σ Vσ b₁ b₂ B₁ B₂
    cc₁ = CR.cc₁ σ Vσ b₁ b₂ B₁ B₂
    cc₂ = CR.cc₂ σ Vσ b₁ b₂ B₁ B₂

  -- The fired RU-Choice RHS leaf is ≋ to the translation of the typed R-Choice
  -- contractum.  v₁ is the select fill (` 0F); v₂ is the branch fill
  -- (`inj k (` posR)) — the injection is absorbed into v₂.
  choice-back : (E₁ E₂ : Frame* (sum B₁′ + sum B₂′ + m))
                (v₁ v₂ : Tm (sum B₁′ + sum B₂′ + m))
                (P : T.Proc (sum B₁′ + sum B₂′ + m)) →
    U.ν (plugΦ Φrest ( U.⟪ frame*-⋯ E₁ τ Vτ [ v₁ ⋯ τ ]* ⟫
         U.∥ ( U.⟪ frame*-⋯ E₂ τ Vτ [ v₂ ⋯ τ ]* ⟫
         U.∥ U[ P ] τ ) ))
      U.≋ U[ T.ν B₁′ B₂′ ((T.⟪ E₁ [ v₁ ]* ⟫ T.∥ T.⟪ E₂ [ v₂ ]* ⟫) T.∥ P) ] σ
  choice-back E₁ E₂ v₁ v₂ P = back
    where
      QR : T.Proc (sum B₁′ + sum B₂′ + m)
      QR = (T.⟪ E₁ [ v₁ ]* ⟫ T.∥ T.⟪ E₂ [ v₂ ]* ⟫) T.∥ P

      leftEq : (U.⟪ frame*-⋯ E₁ τ Vτ [ v₁ ⋯ τ ]* ⟫ U.∥ U.⟪ frame*-⋯ E₂ τ Vτ [ v₂ ⋯ τ ]* ⟫) U.∥ U[ P ] τ
             ≡ U[ QR ] τ
      leftEq = cong₂ U._∥_
                 (cong₂ U._∥_ (cong U.⟪_⟫ (sym (frame-plug* E₁ τ Vτ)))
                              (cong U.⟪_⟫ (sym (frame-plug* E₂ τ Vτ))))
                 refl

      flatBridge : U.ν (plugΦ Φrest (U[ QR ] τ)) ≡ U[ T.ν B₁′ B₂′ QR ] σ
      flatBridge = cong U.ν (plugΦ-++ (Btel B₁′ cc₁) (Btel B₂′ cc₂) (U[ QR ] τ))
                 ■ sym (Uν-flatΦ σ B₁′ B₂′ QR)

      back : U.ν (plugΦ Φrest ( U.⟪ frame*-⋯ E₁ τ Vτ [ v₁ ⋯ τ ]* ⟫
             U.∥ ( U.⟪ frame*-⋯ E₂ τ Vτ [ v₂ ⋯ τ ]* ⟫
             U.∥ U[ P ] τ ) ))
             U.≋ U[ T.ν B₁′ B₂′ QR ] σ
      back = U.ν-cong (plugΦ-cong Φrest (U.∥-assoc ◅◅ ≡→≋ leftEq)) ◅◅ ≡→≋ flatBridge
