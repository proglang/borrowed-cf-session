-- | Binder-group shape forced by an acquire boundary.
module BorrowedCF.Simulation.BackwardSoup.AcqShape where

open import Data.List.Relation.Unary.All as Allᴸ
  using ([]; _∷_) renaming (All to Allᴸ)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup

open import BorrowedCF.Simulation.ForwardSoup.Local.SplitCommon
  using (bindFlags)

private
  all-positive-no-acq :
    {B : Typed.BindGroup} →
    Allᴸ NonZero B →
    (before after : List Soup.Flag) →
    bindFlags B ≢ before ++ Soup.acq ∷ after
  all-positive-no-acq {B = []} all [] after ()
  all-positive-no-acq {B = []} all (f ∷ before) after ()
  all-positive-no-acq {B = b ∷ []} all [] after ()
  all-positive-no-acq {B = b ∷ []} all (f ∷ before) after ()
  all-positive-no-acq {B = zero ∷ b ∷ B} (() ∷ all) before after
  all-positive-no-acq {B = suc a ∷ b ∷ B} (nz ∷ all) [] after ()
  all-positive-no-acq {B = suc a ∷ b ∷ B} (nz ∷ all)
    (f ∷ before) after equal =
    all-positive-no-acq all before after (L.∷-injectiveʳ equal)

-- In a well-formed binder group only the first group may have width zero.
-- Hence an `acq` boundary in its translated flag list is necessarily the
-- boundary from that first empty group to a nonempty second group.
acq-flag-shape :
  (B : Typed.BindGroup) →
  Typed.⊢ᴮ B →
  (before after : List Soup.Flag) →
  bindFlags B ≡ before ++ Soup.acq ∷ after →
  Σ[ b ∈ ℕ ] Σ[ B′ ∈ Typed.BindGroup ]
    (B ≡ zero ∷ suc b ∷ B′) × (before ≡ [])
acq-flag-shape [] typed [] after ()
acq-flag-shape [] typed (f ∷ before) after ()
acq-flag-shape (a ∷ []) typed [] after ()
acq-flag-shape (a ∷ []) typed (f ∷ before) after ()
acq-flag-shape (zero ∷ zero ∷ B) (() ∷ typed) before after equal
acq-flag-shape (zero ∷ suc b ∷ B) (nz ∷ typed) [] after equal =
  b , B , refl , refl
acq-flag-shape (suc a ∷ b ∷ B) typed [] after ()
acq-flag-shape (a ∷ b ∷ B) typed (f ∷ before) after equal =
  ⊥-elim
    (all-positive-no-acq typed before after (L.∷-injectiveʳ equal))
