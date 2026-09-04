-- | Transport a global soup image through typed structural congruence.
module BorrowedCF.Simulation.BackwardSoup.CanonicalImage where

open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.UntypedSoup as Soup

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Struct
  using (≋-image)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using (Tracks)
open import BorrowedCF.Simulation.BackwardSoup.TracksImage
  using (≋-image-slot)

open Nat.Variables

transportGlobalImage :
  {P Q : Typed.Proc 0} {C : Soup.Config n m} →
  P Typed.≋ Q → GlobalImage P C → GlobalImage Q C
transportGlobalImage derivation image = record
  { logicalChannels = proj₁ transported
  ; localImage = proj₂ transported
  }
  where
  transported = ≋-image derivation (localImage image)

transportGlobalSlot :
  {P Q : Typed.Proc 0} {C : Soup.Config n m}
  (derivation : P Typed.≋ Q) (image : GlobalImage P C)
  {source : 𝔽 _} {target : 𝔽 _} {slot : 𝔽 m} →
  Tracks derivation source target →
  threadEmbedding (localImage image) source ≡ just slot →
  threadEmbedding (localImage (transportGlobalImage derivation image)) target ≡
    just slot
transportGlobalSlot derivation image tracks slot =
  ≋-image-slot (localImage image) tracks slot
