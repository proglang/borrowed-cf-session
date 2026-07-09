-- | The φ-telescope reverse engine for simRes's φ-bearing case (Backward.agda
--   ?1/?2), structured by WELL-FOUNDED recursion on the INTERIOR reduction
--   measure ∣sub∣ (RevCongStrong.∣_∣) — NOT the top-level ∣RU-Res sub∣.
--
--   simRes previously deferred the φ-sync / φ-struct sub-cases to the top-level
--   engine `eng` by RE-WRAPPING the interior step as `RU-Res sub`.  Because
--   ∣RU-Res sub∣ is CONSTANT across the round trip
--     eng → sim←-base → base-from-strict → sim←ᵍ (RU-Res sub) → inv-U-ν
--         → simRes (SAME sub) → φ-trichotomy → eng (RU-Res sub) → …
--   that deferral was a measure-free infinite loop.
--
--   `tel` breaks it: it consumes the interior reduction `sub : X ─→ₚ X′`
--   DIRECTLY (X = the ν-body image), peeling every leading RU-Struct with a
--   STRICT measure descent (∣core∣ < ∣RU-Struct _ core _∣ = ∣sub∣) and absorbing
--   both ≋ links into the codomain ≈ at the ν level (≈-ν-cong ∘ ≋⇒≈).  It bottoms
--   out at the residual leaf reflection `Leaf` — a genuine φ-sync descent / drop
--   on a ≋-variant — exactly as UpToPhiEngineWF.eng-acc isolates its `Base`, but
--   here the recursion NEVER re-enters `eng`, so the loop is gone.  No
--   {-# TERMINATING #-} pragma; the Acc argument is the structural decreasing one.
module BorrowedCF.Simulation2.Backward.PhiTelescopeWF where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin
  using (_≈_; ≈-refl; ≈-sym; ≈-trans; ≋⇒≈; ≈-ν-cong)
open import BorrowedCF.Simulation.RevCongStrong using (∣_∣)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open TP using (BindGroup; _;_⊢ₚ_)

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.ListAction using (sum)
open import Data.List using (_∷_; [])
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
         {g : Struct m} (B₁ B₂ : BindGroup)
         (P₀ : TP.Proc (sum B₁ + sum B₂ + m))
         (⊢P : Γ ; g ⊢ₚ TP.ν B₁ B₂ P₀)
         (X : UP.Proc (2 + n)) where

  -- The simRes conclusion for a ν-body reduct Y.
  Resν : UP.Proc (2 + n) → Set
  Resν Y = Σ[ P′ ∈ TP.Proc m ]
             (Star TR._─→ₚ_ (TP.ν B₁ B₂ P₀) P′ × UP.ν Y ≈ U[ P′ ] σ)

  -- The residual leaf obligation the WF recursion bottoms out at: reflect a
  -- NON-RU-Struct ν-body step on a process ≈-related to the image body X.
  -- This is the genuine φ-sync descent / ≋-variant drop — strictly smaller than
  -- the original loop, and it NEVER re-enters `eng`.
  Leaf : Set
  Leaf = ∀ {R Y : UP.Proc (2 + n)} → R ≈ X → (red : R UR.─→ₚ Y) → Resν Y

  -- WF-Acc engine on ∣red∣.  Peels leading RU-Struct, absorbs ≋ links at the ν
  -- level; bottoms at Leaf.  Terminating with no TERMINATING pragma.
  tel-acc : Leaf → ∀ {R Y : UP.Proc (2 + n)}
          → R ≈ X → (red : R UR.─→ₚ Y) → Acc _<_ ∣ red ∣ → Resν Y
  tel-acc leaf R≈ (UR.RU-Struct c₁ core c₂) (acc rs)
    with P′ , steps , c ← tel-acc leaf
           (≈-trans (≈-sym (≋⇒≈ c₁)) R≈) core (rs {∣ core ∣} ≤-refl)
    = P′ , steps , ≈-trans (≈-ν-cong (≋⇒≈ (Eq*.symmetric _ c₂))) c
  tel-acc leaf R≈ red (acc rs) = leaf R≈ red

  -- Public entry: seed accessibility with <-wellFounded ∣sub∣ (X ≈ X = refl).
  tel : Leaf → ∀ {Y : UP.Proc (2 + n)} → (sub : X UR.─→ₚ Y) → Resν Y
  tel leaf sub = tel-acc leaf ≈-refl sub (<-wellFounded ∣ sub ∣)
