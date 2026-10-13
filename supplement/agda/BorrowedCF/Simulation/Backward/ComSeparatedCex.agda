-- | MECHANIZED: at the bind-context level, typing does NOT rule out the "separated
--   firing com".  A well-typed BindCtx′ block can carry a MOBILE `acq;ret` front
--   with a msg channel genuinely BEHIND it — directly refuting the generalization of
--   ComColocated.mob-whole ("a Mobile front consumes its whole block").
--
--   Consequence: `com-xS-min`'s load-bearing hypothesis `¬ Mobile (lookup Γ 0F)`
--   genuinely FAILS at this (bind-context / confinement) level — the flat multi-block
--   `com-go` cannot be closed by bind-context confinement alone.  Whether the ν-level
--   `New` constraint excludes it is a strictly deeper ends-theory question (a com ν's
--   session is New, and New has no acq/ret; the cons-acq route to this block forces the
--   ν session `ret;mS`, which is NOT New — but the general "no route over any New s"
--   claim is the unbuilt left-cancellation/ends lemma).
module BorrowedCF.Simulation.Backward.ComSeparatedCex where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomHead using (atomKind≢⇒≄-;ˡ)
import BorrowedCF.Types.Predicates as P
open P using (New; Mobile; Bounded)
open import BorrowedCF.Processes.Typed using (BindCtx; BindCtx′)
open BindCtx
open BindCtx′

-- the msg channel that sits BEHIND the mobile front
mS : 𝕊 0
mS = msg ‼ `⊤ ; end ‼

-- the front handle: acq ; ret — MOBILE, because `ret` is Bounded (Predicates:23)
front : 𝕊 0
front = acq ; ret

¬sk-block : ¬ Skips (front ; mS)
¬sk-block ((() ; _) ; _)

¬sk-msg : ¬ Skips mS
¬sk-msg (() ; _)

-- (1) INHABITED: a well-typed block with a MOBILE front and mS a strictly-later handle.
bc′ : BindCtx′ (front ; mS) (⟨ front ⟩ ∷ ⟨ mS ⟩ ∷ [])
bc′ = cons front mS ¬sk-block ≃-refl (cons mS skip ¬sk-msg ≃-skipʳ (nil skip))

-- (2) the front IS Mobile (the shape ComColocated's ¬mob-acq / mob-whole did NOT cover):
mob-front : Mobile ⟨ front ⟩
mob-front = P.⟨ ret , P.ret , ≃-refl ⟩

-- (3) the behind channel is msg-headed, NOT acq — a genuinely later, ready com:
β-msg : ¬ (∃[ s′ ] mS ≃ acq ; s′)
β-msg (s′ , eq) = atomKind≢⇒≄-;ˡ msg acq (λ ()) eq
