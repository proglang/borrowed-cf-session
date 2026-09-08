-- | The `acq` redex (agent G1, wave 2).
--
--   `R-Acq` fires only on an EXPOSED group: a binder side reading
--   `zero ∷ suc b ∷ B` whose head is the acquired handle.  That is the
--   `AcqShape` of `Simulation/BackwardSoup/Canonical.agda`, and it is exactly
--   what the `B-NuAcqˡ` / `B-NuAcqʳ` premisses of `Safety/Blocked.agda` decide,
--   so `acqBinderˡ` / `acqBinderʳ` translate one into the other and
--   `redex-acq-exposedˡ` / `redex-acq-exposedʳ` produce the reduction in the
--   form the `ν` case of process progress meets it.
module BorrowedCF.Safety.Progress.Redex.Acq where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using () renaming (ε to ≋-refl)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Context
import BorrowedCF.Processes.TranslationSoup as TranslationS
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed
  using (Proc; ⟪_⟫; _∥_; ν; BindGroup; _;_⊢ₚ_)
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_; R-Acq; R-Struct)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; bind; plug; compose; plug-compose)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (Binder; binder; resolve; weakenThrough; binderGroup; binderPos)
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (acq-non-first-group-head)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (CanonAcq; canonAcq; canon-acq; AcqShape; acq-l; acq-r)

open import BorrowedCF.Safety.Progress.Redex.Context using (red-in-ctx)
open import BorrowedCF.Safety.Blocked using (head₂)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The rule, addressed through an arbitrary binder.
--
--     `R-Acq` is applied with every index given explicitly (`acqStep`) and the
--     `CanonAcq` is consumed by an ordinary pattern match rather than by
--     `with`: a `with` on one of the `Canonical.agda` records makes Agda's
--     memory grow without bound (>20 GB), because the abstraction has to
--     generalise the `src` index as well.

private
  acqStep :
    {n : ℕ} (ba : ℕ) (D₁ D₂ : BindGroup)
    (E₀ : Frame* (sum (0 L.∷ suc ba L.∷ D₁) + sum D₂ + n))
    (Q₀ : Proc (sum (0 L.∷ suc ba L.∷ D₁) + sum D₂ + n)) →
    ν (0 L.∷ suc ba L.∷ D₁) D₂ (⟪ E₀ [ K `acq ·¹ (` 0F) ]* ⟫ ∥ Q₀)
      ─→ₚ
    ν (suc ba L.∷ D₁) D₂ (⟪ E₀ [ ` 0F ]* ⟫ ∥ Q₀)
  acqStep ba D₁ D₂ E₀ Q₀ = R-Acq {P = Q₀} {E = E₀}

  fromCanonAcq :
    {P : Proc 0} {src : 𝔽 (TranslationS.processCount P)} →
    CanonAcq P src → Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′
  fromCanonAcq (canonAcq ba D₁ D₂ ab E₀ Q₀ ≋r trk) =
    _ , R-Struct ≋r (red-in-ctx ab (acqStep ba D₁ D₂ E₀ Q₀)) ≋-refl

redex-acq :
  {k : ℕ} {ctx : ProcessContext k 0} (E : Frame* k) {x : 𝔽 k}
  (bnd : Binder ctx x) →
  AcqShape (Binder.B₁ bnd) (Binder.B₂ bnd) (Binder.local bnd) →
  Σ[ P′ ∈ Proc 0 ] plug ctx ⟪ E [ K `acq ·¹ (` x) ]* ⟫ ─→ₚ P′
redex-acq E bnd sh = fromCanonAcq (canon-acq E bnd sh)

------------------------------------------------------------------------
-- 2.  The two binders a `ν` with an exposed group provides.  `0F` is the head
--     of side 1 and `head₂ B₁ b B₂` the head of side 2, spelled exactly as in
--     `Safety/Blocked.agda`; both `index-eq`s hold by `refl`.

acqBinderˡ :
  {m k b : ℕ} {B₁ B₂ : BindGroup}
  (ctx₀ : ProcessContext m 0)
  (ctx₁ : ProcessContext k (sum (0 L.∷ suc b L.∷ B₁) + sum B₂ + m)) →
  Binder (compose ctx₀ (bind (0 L.∷ suc b L.∷ B₁) B₂ ctx₁))
         (weakenThrough ctx₁ 0F)
acqBinderˡ ctx₀ ctx₁ = binder _ _ ctx₀ ctx₁ refl 0F refl

acqBinderʳ :
  {m k b : ℕ} {B₁ B₂ : BindGroup}
  (ctx₀ : ProcessContext m 0)
  (ctx₁ : ProcessContext k (sum B₁ + sum (0 L.∷ suc b L.∷ B₂) + m)) →
  Binder (compose ctx₀ (bind B₁ (0 L.∷ suc b L.∷ B₂) ctx₁))
         (weakenThrough ctx₁ (head₂ B₁ b B₂))
acqBinderʳ {B₁ = B₁} ctx₀ ctx₁ = binder _ _ ctx₀ ctx₁ refl (sum B₁ ↑ʳ 0F) refl

------------------------------------------------------------------------
-- 3.  ... and the reductions they license.

redex-acq-exposedˡ :
  {m k b : ℕ} {B₁ B₂ : BindGroup}
  (ctx₀ : ProcessContext m 0)
  (ctx₁ : ProcessContext k (sum (0 L.∷ suc b L.∷ B₁) + sum B₂ + m))
  (E : Frame* k) →
  Σ[ P′ ∈ Proc 0 ]
    plug ctx₀ (ν (0 L.∷ suc b L.∷ B₁) B₂
      (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ 0F) ]* ⟫)) ─→ₚ P′
redex-acq-exposedˡ {b = b} {B₁ = B₁} {B₂ = B₂} ctx₀ ctx₁ E
  with P′ , red ← redex-acq E (acqBinderˡ ctx₀ ctx₁) (acq-l b B₁ B₂) =
  P′ , subst (_─→ₚ P′)
         (plug-compose ctx₀ (bind (0 L.∷ suc b L.∷ B₁) B₂ ctx₁) _) red

redex-acq-exposedʳ :
  {m k b : ℕ} {B₁ B₂ : BindGroup}
  (ctx₀ : ProcessContext m 0)
  (ctx₁ : ProcessContext k (sum B₁ + sum (0 L.∷ suc b L.∷ B₂) + m))
  (E : Frame* k) →
  Σ[ P′ ∈ Proc 0 ]
    plug ctx₀ (ν B₁ (0 L.∷ suc b L.∷ B₂)
      (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ (head₂ B₁ b B₂)) ]* ⟫))
      ─→ₚ P′
redex-acq-exposedʳ {b = b} {B₁ = B₁} {B₂ = B₂} ctx₀ ctx₁ E
  with P′ , red ← redex-acq E (acqBinderʳ ctx₀ ctx₁) (acq-r B₁ b B₂) =
  P′ , subst (_─→ₚ P′)
         (plug-compose ctx₀ (bind B₁ (0 L.∷ suc b L.∷ B₂) ctx₁) _) red

------------------------------------------------------------------------
-- 4.  The position an `acq` redex forces (`Crux.acq-non-first-group-head`):
--     the handle is the head of a NON-FIRST group of its side.

acq-position :
  {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
  [] ; [] ⊢ₚ plug ctx ⟪ E [ K `acq ·¹ (` x) ]* ⟫ →
  (0 Nat.< binderGroup (resolve ctx x)) × (binderPos (resolve ctx x) ≡ 0)
acq-position ctx E x = acq-non-first-group-head {ctx = ctx} {E = E} {x = x}
