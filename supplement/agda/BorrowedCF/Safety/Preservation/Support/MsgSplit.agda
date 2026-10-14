-- | Peeling the leading message off a pair of dual `new` sessions.
--
--   This is the session-type content of the `R-Com` case: the sender's handle
--   carries `msg ‼ T₁` in front of the residual protocol, the receiver's
--   carries `msg ⁇ T₂` in front of the dual residual, and the two payloads
--   must agree.
module BorrowedCF.Safety.Preservation.Support.MsgSplit where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomSnoc using (ClosedAtom; end; msg; ret; acq)
open import BorrowedCF.Types.AtomCons

open import BorrowedCF.Safety.Preservation.Support.ConsMsg
open import BorrowedCF.Safety.Preservation.Support.Dual

open Nat.Variables

-- | `dual` unfolds definitionally on a leading message, so this is just a
--   re-association of `≃-dual`.
dual-msg-; : (T : 𝕋) (s : 𝕊 n) → dual (msg p T ; s) ≡ msg (dualPol p) T ; dual s
dual-msg-; T s = refl

-- | THE R-Com SESSION LEMMA.  Given a `New` session `s` whose `end`-capped
--   form starts with `msg ‼ T₁` on one side and whose dual starts with
--   `msg ⁇ T₂` on the other, the payloads agree and both residuals are the
--   `end`-capped halves of one `New` session `s*`.
com-split : New s → ∀ p →
  msg ‼ T₁ ; s₁ ≃ s ; end p →
  msg ⁇ T₂ ; s₂ ≃ dual s ; end (dualPol p) →
  ∃[ s* ] New s*
        × (T₁ ≃ T₂)
        × (s₁ ≃ s* ; end p)
        × (s₂ ≃ dual s* ; end (dualPol p))
com-split {s = s} {T₁ = T₁} {s₁ = s₁} {T₂ = T₂} {s₂ = s₂} N p eq₁ eq₂
  with msg-;-cons (≃-sym eq₁)
... | inj₁ (_ , T′ , _ , endp≃) = case msg-;-atom end endp≃ of λ where
        (_ , ())
... | inj₂ (T′ , h , T₁≃T′ , s≃ , h;end≃s₁)
  with _ ; Nh ← new-≃ s≃ N
  with T₂≃T′ , s₂≃ ← msg-cancel (≃-trans eq₂ (≃-trans (≃-; (≃-dual s≃) ≃-refl) ≃-assoc-;))
  = h , Nh , ≃-trans T₁≃T′ (≃-sym T₂≃T′)
    , ≃-sym h;end≃s₁
    , s₂≃
