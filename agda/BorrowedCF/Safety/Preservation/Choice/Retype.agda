-- | Re-typing a derivation across a context that changes at two handles.
--
--   `Rt-Choice` leaves both binder groups in place and only re-types the two
--   communicating handles, so the evaluation contexts `E₁`, `E₂` and the
--   parallel remainder `P` have to be re-checked in a context that differs from
--   the old one at exactly those two positions.  That is legal because neither
--   handle occurs in them (linearity, see `Choice.Count`), and because the two
--   changed positions carry handle types, which are never `Unr` and -- being
--   choices -- never `Mobile` either, so the `UnrCx` / `MobCx` side conditions
--   of `_≈_` and `_≼_` transport for free.
module BorrowedCF.Safety.Preservation.Choice.Retype where

open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆; _∪_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈p∪q⁺)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Domain using (dom; ≼⇒dom⊆)
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Choice.Count
  using (∉-join-Dir⁻; ∉-[-]𝓅-++; ∉-block; ∉-wk*)
open import BorrowedCF.Safety.Preservation.Support.ComWeaken using (⋯ᵣ∘; split3; inA; inB; inC)
open import BorrowedCF.Simulation.Support.Confine
  using (∉∪⁻; ∉∪⁺; ∉-join-PS⁻; ∉-join-biased⁻; ∉-abs-ctx-Dir; ∉-abs-ctx-PS;
         ∉-absrec-ctx; ∉-letpair-ctx)

import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables
open Fin.Patterns


private variable N : ℕ

------------------------------------------------------------------------
-- The re-typing datum.
------------------------------------------------------------------------

record Retyping {N : ℕ} (Γ Γ′ : Ctx N) (x y : 𝔽 N) : Set where
  field
    agree : ∀ z → z ≢ x → z ≢ y → Γ ﹫ z ≡ Γ′ ﹫ z
    unrOK : ∀ z → Unr (Γ ﹫ z) → Unr (Γ′ ﹫ z)
    mobOK : ∀ z → Mobile (Γ ﹫ z) → Mobile (Γ′ ﹫ z)

open Retyping public

↑Rt : ∀ {Γ Γ′ : Ctx N} {x y} {T} → Retyping Γ Γ′ x y →
  Retyping (T ⸴ Γ) (T ⸴ Γ′) (Fin.suc x) (Fin.suc y)
↑Rt Rt = record
  { agree = λ where
      0F ¬x ¬y → refl
      (Fin.suc z) ¬x ¬y → agree Rt z (¬x ∘ cong Fin.suc) (¬y ∘ cong Fin.suc)
  ; unrOK = λ where
      0F u → u
      (Fin.suc z) u → unrOK Rt z u
  ; mobOK = λ where
      0F mo → mo
      (Fin.suc z) mo → mobOK Rt z mo
  }

↑Rt* : ∀ {k} {Γ Γ′ : Ctx N} {x y} (Δ : Ctx k) → Retyping Γ Γ′ x y →
  Retyping (Δ ⸴* Γ) (Δ ⸴* Γ′) (k ↑ʳ x) (k ↑ʳ y)
↑Rt* [] Rt = Rt
↑Rt* (T ⸴ Δ) Rt = ↑Rt (↑Rt* Δ Rt)

------------------------------------------------------------------------
-- Structural side conditions transport unconditionally.
------------------------------------------------------------------------

module _ {Γ Γ′ : Ctx N} {x y : 𝔽 N} (Rt : Retyping Γ Γ′ x y) where

  unrCx-re : ∀ {γ} → UnrCx Γ γ → UnrCx Γ′ γ
  unrCx-re [] = []
  unrCx-re (u ∥ v) = unrCx-re u ∥ unrCx-re v
  unrCx-re (u ; v) = unrCx-re u ; unrCx-re v
  unrCx-re (`_ {z} u) = ` unrOK Rt z u

  mobCx-re : ∀ {γ} → MobCx Γ γ → MobCx Γ′ γ
  mobCx-re [] = []
  mobCx-re (u ∥ v) = mobCx-re u ∥ mobCx-re v
  mobCx-re (u ; v) = mobCx-re u ; mobCx-re v
  mobCx-re (`_ {z} mo) = ` mobOK Rt z mo

  ≈′-re : ∀ {α β : Struct N} → Γ ∶ α ≈′ β → Γ′ ∶ α ≈′ β
  ≈′-re ;′-assoc = ;′-assoc
  ≈′-re (;′-cong₁ e) = ;′-cong₁ (≈′-re e)
  ≈′-re (;′-cong₂ e) = ;′-cong₂ (≈′-re e)
  ≈′-re ∥′-unit = ∥′-unit
  ≈′-re ∥′-assoc = ∥′-assoc
  ≈′-re ∥′-comm = ∥′-comm
  ≈′-re (∥′-cong₁ e) = ∥′-cong₁ (≈′-re e)
  ≈′-re (∥′-dup U) = ∥′-dup (unrCx-re U)
  ≈′-re (∥′-tm-; U) = ∥′-tm-; (Sum.map mobCx-re mobCx-re U)

  ≈-re : ∀ {α β : Struct N} → Γ ∶ α ≈ β → Γ′ ∶ α ≈ β
  ≈-re = Eq*.gmap _ ≈′-re

  ≼-re : ∀ {α β : Struct N} → Γ ∶ α ≼ β → Γ′ ∶ α ≼ β
  ≼-re (≼-refl e) = ≼-refl (≈-re e)
  ≼-re (≼-∅ U) = ≼-∅ (unrCx-re U)
  ≼-re ≼-wk = ≼-wk
  ≼-re (≼-trans p q) = ≼-trans (≼-re p) (≼-re q)
  ≼-re (≼-cong-; p q) = ≼-cong-; (≼-re p) (≼-re q)
  ≼-re (≼-cong-∥ p q) = ≼-cong-∥ (≼-re p) (≼-re q)

------------------------------------------------------------------------
-- Terms: legal as soon as neither handle is used.
------------------------------------------------------------------------

Tm-re : ∀ {Γ Γ′ : Ctx N} {x y : 𝔽 N} {γ e T ϵ} → Retyping Γ Γ′ x y →
  x ∉ dom γ → y ∉ dom γ → Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ′ ; γ ⊢ e ∶ T ∣ ϵ
Tm-re Rt x∉ y∉ (T-Const ⊢c) = T-Const ⊢c
Tm-re {x = x} {y = y} Rt x∉ y∉ (T-Var z T-eq) =
  T-Var z (sym (agree Rt z z≢x z≢y) ■ T-eq)
  where
  z≢x : z ≢ x
  z≢x eq = x∉ (subst (λ w → x ∈ ⁅ w ⁆) (sym eq) (x∈⁅x⁆ x))
  z≢y : z ≢ y
  z≢y eq = y∉ (subst (λ w → y ∈ ⁅ w ⁆) (sym eq) (x∈⁅x⁆ y))
Tm-re {γ = γ} Rt x∉ y∉ (T-Abs {a = a} Γ-unr Γ-mob ⊢e) =
  T-Abs (λ u → unrCx-re Rt (Γ-unr u)) (λ mo → mobCx-re Rt (Γ-mob mo))
    (Tm-re (↑Rt Rt) (∉-abs-ctx-Dir (Arr.dir a) γ x∉) (∉-abs-ctx-Dir (Arr.dir a) γ y∉) ⊢e)
Tm-re {γ = γ} Rt x∉ y∉ (T-AbsRec Γ-unr a-unr ⊢e) =
  T-AbsRec (unrCx-re Rt Γ-unr) a-unr
    (Tm-re (↑Rt (↑Rt Rt)) (∉-absrec-ctx γ x∉) (∉-absrec-ctx γ y∉) ⊢e)
Tm-re Rt x∉ y∉ (T-AppUnr a-unr ≤ₐ ⊢e₁ ⊢e₂) =
  T-AppUnr a-unr ≤ₐ
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₁) (y∉ ∘ x∈p∪q⁺ ∘ inj₁) ⊢e₁)
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₂) (y∉ ∘ x∈p∪q⁺ ∘ inj₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-AppLin a-par ≤ₐ ⊢e₁ ⊢e₂) =
  T-AppLin a-par ≤ₐ
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₁) (y∉ ∘ x∈p∪q⁺ ∘ inj₁) ⊢e₁)
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₂) (y∉ ∘ x∈p∪q⁺ ∘ inj₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-AppLeft aL ≤ₐ ⊢e₁ ⊢e₂) =
  T-AppLeft aL ≤ₐ
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₂) (y∉ ∘ x∈p∪q⁺ ∘ inj₂) ⊢e₁)
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₁) (y∉ ∘ x∈p∪q⁺ ∘ inj₁) ⊢e₂)
Tm-re Rt x∉ y∉ (T-AppRight aR ≤ₐ ⊢e₁ ⊢e₂) =
  T-AppRight aR ≤ₐ
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₁) (y∉ ∘ x∈p∪q⁺ ∘ inj₁) ⊢e₁)
    (Tm-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₂) (y∉ ∘ x∈p∪q⁺ ∘ inj₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-Pair p/s {γ₁ = γ₁} {γ₂ = γ₂} seq⇒p ⊢e₁ ⊢e₂) =
  let x₁ , x₂ = ∉-join-biased⁻ p/s γ₁ γ₂ x∉
      y₁ , y₂ = ∉-join-biased⁻ p/s γ₁ γ₂ y∉
  in T-Pair p/s seq⇒p (Tm-re Rt x₁ y₁ ⊢e₁) (Tm-re Rt x₂ y₂ ⊢e₂)
Tm-re Rt x∉ y∉ (T-Let p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      y₁ , y₂ = ∉-join-PS⁻ p/s γ₁ γ₂ y∉
  in T-Let p/s (Tm-re Rt x₁ y₁ ⊢e₁)
       (Tm-re (↑Rt Rt) (∉-abs-ctx-PS p/s γ₂ x₂) (∉-abs-ctx-PS p/s γ₂ y₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-Seq uT ⊢e₁ ⊢e₂) =
  let x₁ , x₂ = ∉∪⁻ x∉
      y₁ , y₂ = ∉∪⁻ y∉
  in T-Seq uT (Tm-re Rt x₁ y₁ ⊢e₁) (Tm-re Rt x₂ y₂ ⊢e₂)
Tm-re Rt x∉ y∉ (T-LetPair {d = d} p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e₁ ⊢e₂) =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      y₁ , y₂ = ∉-join-PS⁻ p/s γ₁ γ₂ y∉
  in T-LetPair p/s (Tm-re Rt x₁ y₁ ⊢e₁)
       (Tm-re (↑Rt (↑Rt Rt)) (∉-letpair-ctx p/s d γ₂ x₂) (∉-letpair-ctx p/s d γ₂ y₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-Inj ⊢e) = T-Inj (Tm-re Rt x∉ y∉ ⊢e)
Tm-re Rt x∉ y∉ (T-Case p/s {γ₁ = γ₁} {γ₂ = γ₂} ⊢e ⊢e₁ ⊢e₂) =
  let x₁ , x₂ = ∉-join-PS⁻ p/s γ₁ γ₂ x∉
      y₁ , y₂ = ∉-join-PS⁻ p/s γ₁ γ₂ y∉
  in T-Case p/s (Tm-re Rt x₁ y₁ ⊢e)
       (Tm-re (↑Rt Rt) (∉-abs-ctx-PS p/s γ₂ x₂) (∉-abs-ctx-PS p/s γ₂ y₂) ⊢e₁)
       (Tm-re (↑Rt Rt) (∉-abs-ctx-PS p/s γ₂ x₂) (∉-abs-ctx-PS p/s γ₂ y₂) ⊢e₂)
Tm-re Rt x∉ y∉ (T-Conv T≃ ϵ≤ ⊢e) = T-Conv T≃ ϵ≤ (Tm-re Rt x∉ y∉ ⊢e)
Tm-re Rt x∉ y∉ (T-Weaken γ≤ ⊢e) =
  T-Weaken (≼-re Rt γ≤) (Tm-re Rt (x∉ ∘ ≼⇒dom⊆ γ≤) (y∉ ∘ ≼⇒dom⊆ γ≤) ⊢e)

------------------------------------------------------------------------
-- Frames, frame stacks and processes.
------------------------------------------------------------------------

F-re : ∀ {Γ Γ′ : Ctx N} {x y : 𝔽 N} {𝒫 : CxPat N} {E : Frame N} {T ϵ U ϵ′} →
  Retyping Γ Γ′ x y →
  x ∉ dom (𝒫 [ [] ]𝓅) → y ∉ dom (𝒫 [ [] ]𝓅) →
  Γ ; 𝒫 ⊢ E ∶ T ∣ ϵ ⟶ U ∣ ϵ′ → Γ′ ; 𝒫 ⊢ E ∶ T ∣ ϵ ⟶ U ∣ ϵ′
F-re Rt x∉ y∉ (TF-app₁ {a = a} {γ = γ} ≤ₐ pP lL rR ⊢e) =
  TF-app₁ ≤ₐ pP lL rR
    (Tm-re Rt (∉-join-Dir⁻ (Arr.dir a) γ [] x∉ .proj₁)
              (∉-join-Dir⁻ (Arr.dir a) γ [] y∉ .proj₁) ⊢e)
F-re Rt x∉ y∉ (TF-app₂ {a = a} {γ = γ} ≤ₐ pP lL rR ⊢e) =
  TF-app₂ ≤ₐ pP lL rR
    (Tm-re Rt (∉-join-Dir⁻ (flipDir (Arr.dir a)) γ [] x∉ .proj₁)
              (∉-join-Dir⁻ (flipDir (Arr.dir a)) γ [] y∉ .proj₁) ⊢e)
F-re Rt x∉ y∉ (TF-□⊗ {γ = γ} p/s seq⇒p ⊢e) =
  TF-□⊗ p/s seq⇒p
    (Tm-re Rt (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] x∉ .proj₁)
              (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] y∉ .proj₁) ⊢e)
F-re Rt x∉ y∉ (TF-⊗□ {γ = γ} p/s seq⇒p ⊢e) =
  TF-⊗□ p/s seq⇒p
    (Tm-re Rt (∉-join-Dir⁻ (biasedDir p/s) γ [] x∉ .proj₁)
              (∉-join-Dir⁻ (biasedDir p/s) γ [] y∉ .proj₁) ⊢e)
F-re Rt x∉ y∉ (TF-; {γ = γ} uT ⊢e) =
  TF-; uT (Tm-re Rt (∉-join-Dir⁻ R γ [] x∉ .proj₁) (∉-join-Dir⁻ R γ [] y∉ .proj₁) ⊢e)
F-re Rt x∉ y∉ (TF-`let γ p/s ⊢e) =
  TF-`let γ p/s
    (Tm-re (↑Rt Rt) (∉-abs-ctx-PS p/s γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] x∉ .proj₁))
                    (∉-abs-ctx-PS p/s γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] y∉ .proj₁)) ⊢e)
F-re Rt x∉ y∉ (TF-`let⊗ {d = d} γ p/s ⊢e) =
  TF-`let⊗ γ p/s
    (Tm-re (↑Rt (↑Rt Rt))
      (∉-letpair-ctx p/s d γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] x∉ .proj₁))
      (∉-letpair-ctx p/s d γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] y∉ .proj₁)) ⊢e)
F-re Rt x∉ y∉ (TF-`inj□ i) = TF-`inj□ i
F-re Rt x∉ y∉ (TF-`case□ γ p/s ⊢e₁ ⊢e₂) =
  let x₁ = ∉-abs-ctx-PS p/s γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] x∉ .proj₁)
      y₁ = ∉-abs-ctx-PS p/s γ (∉-join-Dir⁻ (flipDir (biasedDir p/s)) γ [] y∉ .proj₁)
  in TF-`case□ γ p/s (Tm-re (↑Rt Rt) x₁ y₁ ⊢e₁) (Tm-re (↑Rt Rt) x₁ y₁ ⊢e₂)

F*-re : ∀ {Γ Γ′ : Ctx N} {x y : 𝔽 N} {𝒫 : CxPat N} {E : Frame* N} {T ϵ U ϵ′} →
  Retyping Γ Γ′ x y →
  x ∉ dom (𝒫 [ [] ]𝓅) → y ∉ dom (𝒫 [ [] ]𝓅) →
  Γ ; 𝒫 ⊢* E ∶ T ∣ ϵ ⟶ U ∣ ϵ′ → Γ′ ; 𝒫 ⊢* E ∶ T ∣ ϵ ⟶ U ∣ ϵ′
F*-re Rt x∉ y∉ [] = []
F*-re Rt x∉ y∉ (_∷⟨_⟩_ {𝒫₁ = 𝒫₁} {𝒫₂ = 𝒫₂} ⊢E st ⊢E*) =
  let x₁ , x₂ = ∉-[-]𝓅-++ 𝒫₁ 𝒫₂ x∉
      y₁ , y₂ = ∉-[-]𝓅-++ 𝒫₁ 𝒫₂ y∉
  in F-re Rt x₁ y₁ ⊢E ∷⟨ st ⟩ F*-re Rt x₂ y₂ ⊢E*

P-re : ∀ {Γ Γ′ : Ctx N} {x y : 𝔽 N} {γ} {P : Proc N} → Retyping Γ Γ′ x y →
  x ∉ dom γ → y ∉ dom γ → Γ ; γ ⊢ₚ P → Γ′ ; γ ⊢ₚ P
P-re Rt x∉ y∉ (TP-Expr ⊢e) = TP-Expr (Tm-re Rt x∉ y∉ ⊢e)
P-re Rt x∉ y∉ (TP-Par p q) =
  TP-Par (P-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₁) (y∉ ∘ x∈p∪q⁺ ∘ inj₁) p)
         (P-re Rt (x∉ ∘ x∈p∪q⁺ ∘ inj₂) (y∉ ∘ x∈p∪q⁺ ∘ inj₂) q)
P-re Rt x∉ y∉ (TP-Weaken γ≤ p) =
  TP-Weaken (≼-re Rt γ≤) (P-re Rt (x∉ ∘ ≼⇒dom⊆ γ≤) (y∉ ∘ ≼⇒dom⊆ γ≤) p)
P-re {x = x} {y = y} {γ = γ} Rt x∉ y∉
     (TP-Res {s = s} {B₁ = B₁} {B₂ = B₂} N pol ⊢B₁ ⊢B₂ {Γ₁ = Γ₁} {Γ₂ = Γ₂} C C′ body) =
  TP-Res N pol ⊢B₁ ⊢B₂ C C′
    (P-re (↑Rt* (Γ₁ ⸴* Γ₂) Rt) (fr∉ x x∉) (fr∉ y y∉) body)
  where
  fr∉ : ∀ (z : 𝔽 _) → z ∉ dom γ →
    (sum B₁ + sum B₂) ↑ʳ z ∉
      dom ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ _)
         ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ _)
         ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂)))
  fr∉ z z∉ = ∉∪⁺ _ _
    (∉∪⁺ _ _
      (subst (λ w → ((sum B₁ + sum B₂) ↑ʳ z) ∉ dom w)
        (sym (⋯ᵣ∘ (structBinder B₁) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ _)))
        (∉-block (structBinder B₁) (𝐂.wkʳ (sum B₂)) z))
      (subst (λ w → ((sum B₁ + sum B₂) ↑ʳ z) ∉ dom w)
        (sym (⋯ᵣ∘ (structBinder B₂) (𝐂.wkˡ (sum B₁)) (𝐂.wkʳ _)))
        (∉-block (structBinder B₂) (𝐂.wkˡ (sum B₁)) z)))
    (∉-wk* (sum B₁ + sum B₂) γ z z∉)

------------------------------------------------------------------------
-- The concrete re-typing used by `R-Choice`: two doubly-blocked contexts
-- that differ exactly at the two block heads.
------------------------------------------------------------------------

module _ {a c kk : ℕ} (Γ₁ : Ctx a) (Γ₂ : Ctx c) (Γ : Ctx kk) {T₁ T₂ U₁ U₂ : 𝕋} where
  private
    Δ Δ′ : Ctx (suc a + suc c + kk)
    Δ  = ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) ⸴* Γ
    Δ′ = ((U₁ ⸴ Γ₁) ⸴* (U₂ ⸴ Γ₂)) ⸴* Γ

    look₁ : ∀ {V W : 𝕋} (v : 𝔽 a) →
      (((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) ⸴* Γ) ﹫ ((Fin.suc v ↑ˡ suc c) ↑ˡ kk) ≡ Γ₁ ﹫ v
    look₁ {V} {W} v =
        V.lookup-++ˡ ((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) Γ (Fin.suc v ↑ˡ suc c)
      ■ V.lookup-++ˡ Γ₁ (W ⸴ Γ₂) v

    look₂ : ∀ {V W : 𝕋} (w : 𝔽 c) →
      (((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) ⸴* Γ) ﹫ ((suc a ↑ʳ Fin.suc w) ↑ˡ kk) ≡ Γ₂ ﹫ w
    look₂ {V} {W} w =
        V.lookup-++ˡ ((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) Γ (suc a ↑ʳ Fin.suc w)
      ■ V.lookup-++ʳ Γ₁ (W ⸴ Γ₂) (Fin.suc w)

    look₃ : ∀ {V W : 𝕋} (z : 𝔽 kk) →
      (((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) ⸴* Γ) ﹫ ((suc a + suc c) ↑ʳ z) ≡ Γ ﹫ z
    look₃ {V} {W} z = V.lookup-++ʳ ((V ⸴ Γ₁) ⸴* (W ⸴ Γ₂)) Γ z

  agree-two : ∀ z → z ≢ 0F → z ≢ ((suc a ↑ʳ Fin.zero {c}) ↑ˡ kk) → Δ ﹫ z ≡ Δ′ ﹫ z
  agree-two z ¬x ¬y with split3 (suc a) (suc c) z
  ... | inC v = look₃ {T₁} {T₂} v ■ sym (look₃ {U₁} {U₂} v)
  ... | inA 0F = ⊥-elim (¬x refl)
  ... | inA (Fin.suc v) = look₁ {T₁} {T₂} v ■ sym (look₁ {U₁} {U₂} v)
  ... | inB 0F = ⊥-elim (¬y refl)
  ... | inB (Fin.suc w) = look₂ {T₁} {T₂} w ■ sym (look₂ {U₁} {U₂} w)
