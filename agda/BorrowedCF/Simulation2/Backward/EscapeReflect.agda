-- | GENERAL φ-ESCAPE REFLECTION for the reverse simulation's RU-Struct case.
--
--   Generalizes the width-1 milestone  Backward.ReflectPhiEscape.reflect-φescape
--   (a concrete Proc-0 drop) to the GENERAL νφ-comm′ escape.  sim←ᵍ's RU-Struct
--   case reflects a structural-congruence-wrapped reduction whose leading link
--   `c₁` is a νφ-comm′ ESCAPE:  U[P]σ ≋ Resc  with  Resc = φ x (ν Body)  a
--   φ-headed NON-image (RevUCong.U-not-φ).  Route 3 (ReflectPhiEscape): never
--   recognise Resc as an image — UN-ESCAPE first (esc is DELIVERED, not rebuilt),
--   fire on the STRICT image, reflect, ABSORB the re-escape into the codomain ≈.
--
--   This module records, machine-checked hole/postulate-free:
--
--   • escape-reflect            — the general reflection, = the reverse non-ε
--       engine `eng` run on the UN-escaped step (Resc ≈ U[P]σ via ≈-sym∘≋⇒≈ esc).
--       eng peels every leading RU-Struct with a strict ∣_∣-descent and bottoms
--       at its `Base` (= the residual primitive-on-≈-image reflection).  So the
--       general escape reflection is CLOSED relative to `Base`, exactly the hole
--       Backward.sim←-base already isolates.
--
--   • drop-escape-vacuous       — a φ-DROP can NEVER fire directly on a νφ-comm′
--       escape  φ x (ν Body):  RU-Drop needs a THREAD body (⟪…⟫ ∥ P), but the
--       escape's φ-body is a ν.  So `Base` is NEVER invoked on a drop-on-escape;
--       the observable drop only appears via an RU-Struct that un-escapes first.
--
--   • escape-reflect-struct     — the GENERAL-WIDTH route 3 for the productive
--       shape  inner = RU-Struct unesc fire post  whose leading link `unesc`
--       un-escapes Resc to the STRICT image and whose core `fire` fires there.
--       CLOSED relative to a strict-image reflector `img-reflect`
--       (= sim←ᵍ σ Vσ Γ-S ⊢P refl restricted to genuine, non-RU-Struct redexes).
--       This is precisely  reflect-φescape  with the concrete P₀/drop-typed
--       abstracted to arbitrary width.
--
--   THE RESIDUAL (reported): the ONLY primitive that fires directly on a φ-headed
--   νφ-comm′ escape and is NOT an un-escape is  RU-Sync sub  (a ν-body reduction
--   under the φ).  Reflecting it demands a νφ-comm HARMONY / push-through lemma
--   (push a ν-body reduction OUT past the φ, up to ≈), which is the same interior
--   obligation as  PhiTelescopeWF.tel's `Leaf` — see the note at `sync-residual`.
module BorrowedCF.Simulation2.Backward.EscapeReflect where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RevAdmin
  using (_≈_; ≈-refl; ≈-sym; ≈-trans; ≋⇒≈; ≈-ν-cong; ≈-φ-cong)
import BorrowedCF.Simulation2.Backward.UpToPhiEngineWF as Eng
open import BorrowedCF.Simulation2.Backward.SimResPhi
  using (φ-trichotomy; φ-sync; φ-drop; φ-struct; mk-sync; mk-drop; mk-struct)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Fin.Patterns

------------------------------------------------------------------------
-- The reflection payload.
------------------------------------------------------------------------

Res : ∀ {m n} (σ : m →ₛ n) (P : TP.Proc m) → UP.Proc n → Set
Res σ P Q = Σ[ P′ ∈ TP.Proc _ ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

------------------------------------------------------------------------
-- (A) The general escape reflection, closed relative to `Base`.
--
--   esc : U[P]σ ≋ Resc  (a νφ-comm′/ν-ext′/φ-ext′ escape link — held abstract).
--   inner : Resc ─→ₚ Q  (the step on the escaped form).
--   Un-escape  Resc ≈ U[P]σ  and hand the step to the WF engine `eng`, which
--   peels leading RU-Structs (strict ∣_∣-descent) and bottoms at `Base`.
------------------------------------------------------------------------

escape-reflect :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
  → Eng.Base σ Vσ Γ-S ⊢P
  → {Resc Q : UP.Proc n}
  → U[ P ] σ UP.≋ Resc
  → Resc UR.─→ₚ Q
  → Res σ P Q
escape-reflect σ Vσ Γ-S ⊢P base esc inner =
  Eng.eng σ Vσ Γ-S ⊢P base (≈-sym (≋⇒≈ esc)) inner

------------------------------------------------------------------------
-- (B) A φ-drop can NEVER fire directly on a νφ-comm′ escape  φ x (ν Body).
--   RU-Drop's redex is a THREAD body ⟪…⟫ ∥ P; the escape's φ-body is a ν.
------------------------------------------------------------------------

drop-escape-vacuous :
  ∀ {n x} {Body : UP.Proc (3 + n)} {Q : UP.Proc n}
  → φ-drop x (UP.ν Body) Q → ⊥
drop-escape-vacuous (mk-drop F x P isdrop () target)

------------------------------------------------------------------------
-- (C) GENERAL-WIDTH route 3 for the productive RU-Struct shape.
--
--   inner = RU-Struct unesc fire post :
--       Resc ≋ U[P]σ  ─(fire)→ Q′ ≋ Q     with the leading link the UN-ESCAPE.
--   `fire` fires on the STRICT image U[P]σ; reflect it via `img-reflect`
--   (= sim←ᵍ σ Vσ Γ-S ⊢P refl on the genuine redex), absorb `post` into ≈.
--   This is  reflect-φescape  with P₀/drop-typed abstracted to arbitrary width.
------------------------------------------------------------------------

escape-reflect-struct :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → (img-reflect : ∀ {Q′} → U[ P ] σ UR.─→ₚ Q′ → Res σ P Q′)
  → {Resc Q Q′ : UP.Proc n}
  → (fire : U[ P ] σ UR.─→ₚ Q′)
  → (post : Q′ UP.≋ Q)
  → Res σ P Q
escape-reflect-struct σ img-reflect fire post
  with P′ , steps , Q′≈ ← img-reflect fire
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.symmetric _ post)) Q′≈

------------------------------------------------------------------------
-- (D) THE RESIDUAL, isolated precisely.
--
--   The only primitive that fires directly on a φ-headed νφ-comm′ escape and is
--   NOT an un-escape is  RU-Sync sub — a reduction of the ν-body UNDER the φ:
--       inner = RU-Sync sub ,  sub : ν Body ─→ₚ Y₀ ,  Q = φ x Y₀.
--   φ-trichotomy exposes exactly this as its  φ-sync  alternative (drop is
--   vacuous by (B), struct is peeled by (C)/eng).  Reflecting it requires the
--   νφ-comm HARMONY lemma below (push a ν-body reduction out past the φ, up to
--   ≈) — the SAME interior obligation as PhiTelescopeWF.tel's `Leaf`.
------------------------------------------------------------------------

-- The precise shape of the residual, as an eng.Base-style hypothesis restricted
-- to the reachable  RU-Sync-on-νφ-comm-escape  inputs.
Sync-Residual :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P) → Set
Sync-Residual {n = n} σ Vσ Γ-S {P = P} ⊢P =
  ∀ {x : UP.Flag} {Body : UP.Proc (3 + n)} {Y₀ : UP.Proc (1 + n)}
  → U[ P ] σ UP.≋ UP.φ x (UP.ν Body)
  → (sub : UP.ν Body UR.─→ₚ Y₀)
  → Res σ P (UP.φ x Y₀)

-- The trichotomy dispatch, made explicit: given the νφ-comm′ escape and the step
-- on it, EITHER it is the productive un-escape (handled by (C)), OR it is the
-- RU-Sync residual (handled by the hypothesis), OR it is a further RU-Struct
-- (handled by eng via (A)).  Drop is impossible by (B).
escape-reflect-νφ :
  ∀ {m n} (σ : m →ₛ n) (Vσ : VSub σ) {Γ : Ctx m} (Γ-S : ChanCx Γ)
    {g : Struct m} {P : TP.Proc m} (⊢P : Γ ; g ⊢ₚ P)
  → Eng.Base σ Vσ Γ-S ⊢P
  → Sync-Residual σ Vσ Γ-S ⊢P
  → {x : UP.Flag} {Body : UP.Proc (3 + n)} {Q : UP.Proc n}
  → (esc : U[ P ] σ UP.≋ UP.φ x (UP.ν Body))
  → (inner : UP.φ x (UP.ν Body) UR.─→ₚ Q)
  → Res σ P Q
escape-reflect-νφ σ Vσ Γ-S ⊢P base sync-res {x} {Body} esc inner
  with φ-trichotomy x (UP.ν Body) inner
... | inj₁ (mk-sync {Y₀} sub lands)
      rewrite lands = sync-res esc sub
... | inj₂ (inj₁ dr) = ⊥-elim (drop-escape-vacuous dr)
... | inj₂ (inj₂ (mk-struct pre red post)) =
      escape-reflect σ Vσ Γ-S ⊢P base esc inner
