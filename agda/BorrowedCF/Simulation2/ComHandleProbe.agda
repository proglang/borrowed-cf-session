module BorrowedCF.Simulation2.ComHandleProbe where

-- ============================================================================
-- VERDICT (machine-checked feasibility of the reverse RU-Com/RU-Choice cases):
--   send-handle ≡ 0F HOLDS  ⟹  ?5/?6 are NOT a roadblock (unlike the PURE
--   redexes ?1 RU-LSplit / ?2 RU-RSplit / ?3 RU-Acquire, and unlike ?4 RU-Close).
--
-- Two facts settle it:
--
-- (A) [checked below]  The typing system DOES assign ⟨ msg ‼ `⊤ ⟩ to a NON-zero
--     handle (index 1F): New(s) has no `acq` constructor (msg/;/brn/mu/skip only),
--     so a com block session  s ; end p  may start with — and REPEAT — msg ‼ T,
--     and BindCtx′ peels prefixes, giving a width-3 block the handles
--       0F : ⟨ msg ‼ `⊤ ⟩ , 1F : ⟨ msg ‼ `⊤ ⟩ , 2F : ⟨ end ‼ ⟩.
--     So a ⟨msg‼T⟩ handle at 1F EXISTS in isolation.
--
-- (B) [checked in scratch SendCaptureProbe, which FAILS with ℙ != 𝕀]  An impure
--     send (send/select/recv/branch/end are all 𝕀) CANNOT be pushed ;-before a
--     live borrow: the ONLY two ;-before frame producers are T-AppRight (app₂ on
--     an R-arrow) and T-Pair seq (⊗□ seq), and BOTH require the ;-later hole to
--     be PURE (TF-app₂ appRight ⇒ ϵ₂ ≡ ℙ ; TF-⊗□ seq⇒p Seq⇒Pure seq ⇒ ϵ₂ ≡ ℙ).
--     The HeadMin counterexample crucially used `drop` (ℙ); it does NOT lift to
--     send/select.
--
-- Consequently, since block-1's handles are ;-ORDERED (structBinder [b] =
-- `0F ; `1F ; … ; and a parallel split is not ≼-typeable because ; ≼ ∥, not
-- ∥ ≼ ;), the head-redex send/select of a well-typed reverse input can only sit
-- on the ;-MINIMAL live handle, which is 0F.  Hence the confinement the reverse
-- RU-Com/RU-Choice need (send/select handle ≡ 0F) is TRUE, and the RevComConfine
-- port (mirror close-confine WITHOUT the width-1 restriction, session msg ‼ T /
-- msg ⁇ T, using impurity to rule out a ;-earlier live handle) closes ?5/?6.
-- ============================================================================

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.Equivalence
  using (_≃_; ≃-refl; ≃-sym; ≃𝕊-assoc; ≃𝕊-skipʳ)
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using ()

open Fin.Patterns

-- (A) width-3 com block: handles 0F,1F : ⟨msg‼⊤⟩, 2F : ⟨end‼⟩.
Γ1 : Ctx 3
Γ1 = ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ msg ‼ `⊤ ⟩ ⸴ ⟨ end ‼ ⟩ ⸴ λ ()

bc3 : BindCtx′ ((msg ‼ `⊤ ; msg ‼ `⊤) ; end ‼) 3 Γ1
bc3 = cons (λ { (_ ; ()) }) (≃-sym (Eq*.return ≃𝕊-assoc)) (λ _ → refl)
        (cons (λ { (() ; _) }) ≃-refl (λ _ → refl)
          (cons (λ ()) (Eq*.return ≃𝕊-skipʳ) (λ _ → refl)
            (nil skip)))

-- The inner (index 1F) handle carries the send-channel session type in isolation.
inner-handle-is-msg : Γ1 1F ≡ ⟨ msg ‼ `⊤ ⟩
inner-handle-is-msg = refl
