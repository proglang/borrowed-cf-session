-- | Algorithmic completeness (agent C4).
--
--   The instantiation of `Completeness/Main.agda` with the case modules.  The two theorems of
--   `Completeness/Base.agda` come out as `complete⇒` and `complete⇐`.
--
--   Unconditional: the three gaps `Main-STATUS.md` reports (FINDINGS 1, 2, 4) were repaired in
--   the base by C10 / C6b / C6c, so nothing is assumed here.
--
--   Owner: agent C4.
open import BorrowedCF.Prelude
open import BorrowedCF.Completeness.Base

module BorrowedCF.Completeness where

open import BorrowedCF.Completeness.Main.App using (app-case)
open import BorrowedCF.Completeness.Main.Bind using (let-case; letpair-case; case-case)

open import BorrowedCF.Completeness.Main app-case let-case letpair-case case-case public
  using (complete⇒ᵍ; complete⇒; complete⇐)

-- The statements, spelled out (they are the ones of `Completeness/Base.agda`).

_ : Complete⇒
_ = complete⇒

_ : Complete⇐
_ = complete⇐
