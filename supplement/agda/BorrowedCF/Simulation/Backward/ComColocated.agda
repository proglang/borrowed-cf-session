-- Machine-checked resolution of the "separated firing com" question (verdict A).
--
-- The backward-com obstruction would require a well-typed source whose UNTYPED
-- image fires RU-Com on a channel b that is NOT at the typed front (0F) -- a
-- "separated firing com".  For that source send on b to typecheck IN PARALLEL
-- with the front handle a sitting before it (so the untyped can fire while the
-- typed is still ordered), the context split must turn a ; b into a || b, which
-- (via ∥′-tm-;) requires the FRONT a to be Mobile (MobCx).
--
-- This module machine-checks that this is impossible, so the com is always
-- co-located.  Three facts, over the canonical mobile-front block
-- acq ; (msg ‼ `⊤ ; end ‼) arising from a New-derived ν (New (msg ‼ `⊤)):
--
--   * bc              : an acq-HEADED front <acq> with a msg-ready channel
--                       <msg;end> behind it IS inhabited.  So the coordinator's
--                       literal lemma ("every non-front handle is acq-headed")
--                       is FALSE -- non-front handles CAN be msg-ready.
--   * β-not-acq-headed: that non-front handle is provably msg-headed, NOT acq;_.
--   * ¬mob-acq        : BUT that acq-headed front <acq> is NOT Mobile (its
--                       continuation would have to Skip, contradicting Bounded).
--   * mob-whole       : the only way to make the front Mobile is to take the
--                       WHOLE session acq;(msg;end) as a single channel -- which
--                       leaves NO channel behind it.
--
-- Hence: a genuinely MOBILE front consumes the whole block (its Bounded
-- continuation must reach the unique terminal `end`, since New excludes ret/end
-- internally), so no msg-ready channel can sit behind a Mobile front.  A merely
-- acq-headed (non-Mobile) front cannot license a parallel send behind it.
-- Either way the separated firing com is not a well-typed reachable image:
-- the com is co-located.  Verdict: (A).

module BorrowedCF.Simulation.Backward.ComColocated where

open import BorrowedCF.Prelude

open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomHead   using (atomKind≢⇒≄-;ˡ)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded; skips⊥bounded)
open import BorrowedCF.Processes.Typed using (BindCtx; BindCtx′)

open BindCtx
open BindCtx′

-- The New session carried by the ν (msg is a New constructor).
sN : 𝕊 0
sN = msg ‼ `⊤

s-New : New sN
s-New = P.msg

-- b's session = a split piece of the acq-continuation: msg-headed.
mS : 𝕊 0
mS = msg ‼ `⊤ ; end ‼

-- ¬skips side conditions: a `;` headed by acq / msg cannot Skip.
¬sk-acq : ¬ Skips (acq ; mS)
¬sk-acq (() ; _)

¬sk-msg : ¬ Skips mS
¬sk-msg (() ; _)

-- The 2-channel block discharging acq ; mS: the acq handle splits off,
-- leaving mS (the msg continuation) as its OWN, later handle.
bc′ : BindCtx′ (acq ; mS) (⟨ acq ⟩ ∷ ⟨ mS ⟩ ∷ [])
bc′ = cons acq mS ¬sk-acq ≃-refl (cons mS skip ¬sk-msg ≃-skipʳ (nil skip))

-- The full mobile-front-SHAPED bind group: 0-block (cons-acq marker) over it.
bc : BindCtx mS (0 ∷ 2 ∷ []) (⟨ acq ⟩ ∷ ⟨ mS ⟩ ∷ [])
bc = cons-acq (last bc′)

-- The non-front handle b is msg-headed, NOT acq-headed
-- (refutes the coordinator's literal lemma).
β-not-acq-headed : ¬ (∃[ s′ ] mS ≃ acq ; s′)
β-not-acq-headed (s′ , eq) = atomKind≢⇒≄-;ˡ msg acq (λ ()) eq

-- BUT the acq-headed front that admits a msg behind it is NOT Mobile:
¬mob-acq : ¬ Mobile ⟨ acq ⟩
¬mob-acq P.⟨ s′ , bnd , eq ⟩
  with atom-;-unsnoc acq (≃-trans (≃-sym eq) (≃-sym ≃-skipˡ))
... | inj₁ sk           = skips⊥bounded sk bnd
... | inj₂ (y′ , p , _) with skip≃⇒skips (≃-sym p)
...   | (() ; _)

-- The ONLY Mobile front is the whole channel acq;(msg;end): a single channel,
-- leaving no msg-ready channel behind it (⟹ the com is co-located).
mob-whole : Mobile ⟨ acq ; (msg ‼ `⊤ ; end ‼) ⟩
mob-whole = P.⟨ (msg ‼ `⊤ ; end ‼) , (P.-;₂ P.end) , ≃-refl ⟩
