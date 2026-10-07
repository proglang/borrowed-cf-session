-- | The rsplit-relaxation gap found 2026-10-07 (Splits/DECISION-local-mu.md) is
--   closed.  `NonLocal` (Types/Predicates) now has `mu : NonLocal s → NonLocal (mu s)`,
--   so the former counterexample t₂ = mu (acq ; ` zero) is NonLocal, the relaxed
--   rsplit rejects it as right part, and `skip ; t₂` (acq-headed up to ≃) can no
--   longer be split into a non-acq-headed left group.
module BorrowedCF.Safety.Probe.LocalMuGap where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomCons using (acq-;-split; acq-;-¬skips; acq-;-≄ret)

t₂ : 𝕊 0
t₂ = mu (acq ; ` zero)

NL₂ : NonLocal t₂
NL₂ = mu (acq ;₁-)

¬L₂ : ¬ Local t₂
¬L₂ Lt = Lt NL₂

¬S₂ : ¬ Skips t₂
¬S₂ (mu (() ; _))

-- t = skip ; t₂ is acq-headed (so it may head a non-first group) ...
t-acqHead : skip ; t₂ ≃ acq ; t₂
t-acqHead = ≃-trans ≃-skipˡ ≃-μ

-- ... and the left part of an rsplit with t₁ = skip would not be; NL₂ rules
-- that split out.
left-not-acqHead : ∀ {h : 𝕊 0} → ¬ (skip ; ret ≃ acq ; h)
left-not-acqHead eq with acq-;-split eq
... | inj₁ (_ , req)       = acq-;-≄ret req
... | inj₂ (_ , seq , _)   = acq-;-¬skips skip seq
