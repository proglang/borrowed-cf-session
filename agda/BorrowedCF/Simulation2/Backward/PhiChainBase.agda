-- | The ≈-chain induction that discharges UpToPhiEngineWF.Base.
--
--   Base reflects a DIRECT untyped step  red : R ─→ₚ Q  against a process merely
--   ≈-related (NOT ≡) to an image  U[ P ] σ.  ≈ = EqClosure (≋ ∪ ─→ᵃ), so the
--   relatedness is a chain of structural-congruence (≋) links and administrative
--   (─→ᵃ, discard-GC) links, in either direction.
--
--   The proof is STRUCTURAL RECURSION ON THE ≈-CHAIN (Star), transporting `red`
--   across ONE generator link at a time toward the image, then falling into the
--   strict-image reflector (`strict` = sim←ᵍ) at ε.  Crucially:
--
--     • ≋ links (BOTH directions) transport TRIVIALLY by re-wrapping in a fresh
--       RU-Struct — the reduct Q is UNCHANGED, so no strict image-inversion is
--       needed.  This DISSOLVES the νφ-comm φ-escape "roadblock": the escape is
--       a ≋ generator, absorbed here with zero cleverness.  (The prior
--       RevUCong/DropNotAdmin obstructions refute strict image-inversion and
--       ε-absorption respectively — strategies this proof never uses.)
--
--     • ─→ᵃ links delegate to the CONTEXTUAL admin-step hypothesis `admin`,
--       which reflects `red` across ONE leading administrative link WITH the
--       tail context `Y ≈ U[ P ] σ` in scope.  The context is ESSENTIAL: the
--       context-FREE single-step admin diamond is FALSE (a bwd admin link
--       Y=⟪(discard·V);e⟫ ─→ᵃ R=⟪(*);e⟫ lets an E-Seq on R consume the ex-discard
--       unit, and the resulting reduct is ≈-related to neither Y nor a Y-reduct
--       — RevAdminTransportProbe).  With the tail context, thread-rigidity of ≋
--       plus the image being discard-free forces the offending configuration to
--       collapse, so `admin` (the residual) is TRUE.
--
--   `admin` is the residual administrative obligation, isolated as a hypothesis
--   so this file is HOLE/POSTULATE-FREE.  It is strictly SMALLER than Base
--   (only admin-headed chains; every ≋/φ-escape case is discharged here).
module BorrowedCF.Simulation2.Backward.PhiChainBase where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin
  using (_≈_; _─→ᵃ_; ≈-trans)
open import BorrowedCF.Context using (Ctx; Struct)
open TP using (_;_⊢ₚ_)
open UP using (_≋_; _≋′_)

import Data.Sum as Sum
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

-- The administrative diamond, one ─→ᵃ generator link in EITHER direction against
-- a direct reduction: transport (Q ≈ Q₁ with Y ─→ₚ Q₁) or cancel (Q ≈ Y).
ADiamond : Set
ADiamond = ∀ {n} {R Y Q : UP.Proc n}
         → (R ─→ᵃ Y) Sum.⊎ (Y ─→ᵃ R)
         → R UR.─→ₚ Q
         → (Σ[ Q₁ ∈ UP.Proc n ] (Y UR.─→ₚ Q₁) × (Q ≈ Q₁)) Sum.⊎ (Q ≈ Y)

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
         {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P) where

  Res : UP.Proc n → Set
  Res Q = Σ[ P′ ∈ TP.Proc m ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

  -- strict-image reflector (instantiated to sim←ᵍ at the call site).
  Strict : Set
  Strict = ∀ {R Q : UP.Proc n} → R ≡ U[ P ] σ → R UR.─→ₚ Q → Res Q

  base-from-strict : Strict → ADiamond
                   → ∀ {R Q : UP.Proc n} → R ≈ U[ P ] σ → R UR.─→ₚ Q → Res Q
  -- ε : R ≡ U[ P ] σ, strict reflection.
  base-from-strict strict adia ε red = strict refl red
  -- ≋ link forward (r : R ≋ Y): re-wrap, reduct unchanged.
  base-from-strict strict adia (fwd (Sum.inj₁ r) ◅ rest) red =
    base-from-strict strict adia rest (UR.RU-Struct (Eq*.symmetric _≋′_ r) red ε)
  -- ≋ link backward (r : Y ≋ R): re-wrap directly.
  base-from-strict strict adia (bwd (Sum.inj₁ r) ◅ rest) red =
    base-from-strict strict adia rest (UR.RU-Struct r red ε)
  -- ─→ᵃ link forward (a : R ─→ᵃ Y): administrative diamond.
  base-from-strict strict adia (fwd (Sum.inj₂ a) ◅ rest) red
    with adia (Sum.inj₁ a) red
  ... | Sum.inj₁ (Q₁ , red₁ , Q≈Q₁)
        with P′ , steps , c ← base-from-strict strict adia rest red₁
      = P′ , steps , ≈-trans Q≈Q₁ c
  ... | Sum.inj₂ Q≈Y = P , ε , ≈-trans Q≈Y rest
  -- ─→ᵃ link backward (a : Y ─→ᵃ R): administrative diamond, other direction.
  base-from-strict strict adia (bwd (Sum.inj₂ a) ◅ rest) red
    with adia (Sum.inj₂ a) red
  ... | Sum.inj₁ (Q₁ , red₁ , Q≈Q₁)
        with P′ , steps , c ← base-from-strict strict adia rest red₁
      = P′ , steps , ≈-trans Q≈Q₁ c
  ... | Sum.inj₂ Q≈Y = P , ε , ≈-trans Q≈Y rest
