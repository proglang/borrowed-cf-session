-- | The decomposition-based reverse engine.
--
--   `StepDecomp.decomp` turns an arbitrary untyped derivation into a HEAD rule
--   fired in a one-hole context, with all RU-Struct links absorbed into ≋.
--   This engine consumes that: the three administrative heads are absorbed by
--   ≈ (in context — the ONLY thing the old engines could not do, which is why
--   they had to hand RU-Par/Res/Sync wrappers to their residual obligation
--   unanalysed), and what remains is a SINGLE hypothesis: reflect one of the
--   eight OBSERVABLE heads, in context, against a merely ≈-related target.
--
--   The engine is parameterised over the target process T rather than an image
--   U[ P ] σ: the typed data (P, its typing, the Star) lives inside `Res`, so
--   the SAME engine discharges both the top-level obligation (T = U[ P ] σ,
--   Backward.agda ?0) and the ν-body ones (T = the body X, ?1-3).  No
--   well-founded recursion is needed anywhere: `decomp` is structural, and the
--   engine makes no recursive call at all.
module BorrowedCF.Simulation.Backward.DecompEngine where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Processes.Untyped
open import BorrowedCF.Simulation.Support.StepDecomp
open import BorrowedCF.Simulation.Support.RevAdmin
  using (_≈_; ≈-sym; ≈-trans; ≋⇒≈; ─→ᵃ⇒≈; _─→ᵃ_
        ; a-discard; a-drop; a-acq; ≈-ν-cong; ≈-φ-cong; ≈-∥-congˡ)

open import Data.Product using (_×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (_◅◅_)

open Nat.Variables

------------------------------------------------------------------------
-- ≈ is a congruence for plugging.
------------------------------------------------------------------------

≈-∥-congʳ : {P Q Rr : Proc n} → P ≈ Q → Rr ∥ P ≈ Rr ∥ Q
≈-∥-congʳ c = ≋⇒≈ ∥-comm ◅◅ ≈-∥-congˡ c ◅◅ ≋⇒≈ ∥-comm

ctx-cong-≈ : (C : Ctx* n k) {X Y : Proc k} → X ≈ Y → C [ X ]ᴷ ≈ C [ Y ]ᴷ
ctx-cong-≈ ∘ᴷ       c = c
ctx-cong-≈ (C ∥ᴷ Q) c = ≈-∥-congˡ (ctx-cong-≈ C c)
ctx-cong-≈ (P ᴷ∥ C) c = ≈-∥-congʳ (ctx-cong-≈ C c)
ctx-cong-≈ (νᴷ C)   c = ≈-ν-cong (ctx-cong-≈ C c)
ctx-cong-≈ (φᴷ f C) c = ≈-φ-cong (ctx-cong-≈ C c)

------------------------------------------------------------------------
-- Administrative heads are exactly the ─→ᵃ generators.
------------------------------------------------------------------------

-- Observable heads: the eight rules that a reflector must handle.  The three
-- administrative heads instead yield the ─→ᵃ step that ≈ absorbs.
Observable : {R Q : Proc n} (red : R ─→ₚ Q) → Head red → Set
Observable (RU-Discard _ _) _ = ⊥
Observable (RU-Drop _)      _ = ⊥
Observable (RU-Acquire _)   _ = ⊥
Observable _                _ = ⊤

head-admin : {R Q : Proc n} (red : R ─→ₚ Q) (h : Head red) →
             (Observable red h → ⊥) → R ─→ᵃ Q
head-admin (RU-Discard F V) _ _ = a-discard F V
head-admin (RU-Drop F)      _ _ = a-drop F
head-admin (RU-Acquire F)   _ _ = a-acq F
head-admin (RU-Exp x)        _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-Fork _ _)     _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-New _)        _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-LSplit _)     _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-RSplit _)     _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-Close _ _)    _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-Com _ _ _)    _ ¬o = ⊥-elim (¬o tt)
head-admin (RU-Choice _ _ _) _ ¬o = ⊥-elim (¬o tt)

-- Deciding observability of a head.
observable? : {R Q : Proc n} (red : R ─→ₚ Q) (h : Head red) →
              Observable red h ⊎ (Observable red h → ⊥)
observable? (RU-Discard _ _) _ = inj₂ (λ ())
observable? (RU-Drop _)      _ = inj₂ (λ ())
observable? (RU-Acquire _)   _ = inj₂ (λ ())
observable? (RU-Exp _)        _ = inj₁ tt
observable? (RU-Fork _ _)     _ = inj₁ tt
observable? (RU-New _)        _ = inj₁ tt
observable? (RU-LSplit _)     _ = inj₁ tt
observable? (RU-RSplit _)     _ = inj₁ tt
observable? (RU-Close _ _)    _ = inj₁ tt
observable? (RU-Com _ _ _)    _ = inj₁ tt
observable? (RU-Choice _ _ _) _ = inj₁ tt

------------------------------------------------------------------------
-- The engine.
------------------------------------------------------------------------

module _ {n : ℕ} (T : Proc n) (Res : Proc n → Set)
         (res-≈ : ∀ {Q Q′} → Q′ ≈ Q → Res Q → Res Q′)
         (res-stay : ∀ {Q} → Q ≈ T → Res Q) where

  -- The single residual obligation: reflect an OBSERVABLE head, in context,
  -- against a merely ≈-related target.
  ObsBase : Set
  ObsBase = ∀ {k} (C : Ctx* n k) {src tgt : Proc k}
            (red : src ─→ₚ tgt) (h : Head red) → Observable red h →
            C [ src ]ᴷ ≈ T → Res (C [ tgt ]ᴷ)

  engine : ObsBase → ∀ {R Q : Proc n} → R ≈ T → R ─→ₚ Q → Res Q
  engine ob R≈ red with mkDecomp C h ih l r ← decomp red
    with observable? h ih
  ... | inj₁ o  = res-≈ (≈-sym (≋⇒≈ r)) (ob C h ih o (≈-trans (≈-sym (≋⇒≈ l)) R≈))
  ... | inj₂ ¬o =
    res-stay (≈-trans (≈-sym (≋⇒≈ r))
             (≈-trans (≈-sym (ctx-cong-≈ C (─→ᵃ⇒≈ (head-admin h ih ¬o))))
             (≈-trans (≈-sym (≋⇒≈ l)) R≈)))
