module BorrowedCF.Simulation.ForwardSoup.Image.ThreadPermutation where

open import BorrowedCF.Prelude

import Data.Fin.Permutation as Perm

open import BorrowedCF.Simulation.ForwardSoup.Image
open import BorrowedCF.Reduction.Processes.UntypedSoup.Properties
  using (permuteConfig; lookup-permute)
open import BorrowedCF.Processes.UntypedSoup using (Config; config; threads)

import BorrowedCF.Processes.Typed as Typed

open Nat.Variables

permute-image :
  (pi : Perm.Permutation′ m) →
  {P : Typed.Proc 0} {C : Config n m} →
  SoupImage P C →
  SoupImage P (permuteConfig pi C)
permute-image pi {P} {C = config cs ts} img = record
  { channelEmbedding = channelEmbedding img
  ; channelEmbedding-injective = channelEmbedding-injective img
  ; threadEmbedding = Perm._⟨$⟩ˡ_ pi ∘ threadEmbedding img
  ; threadEmbedding-injective = λ {x} {y} eq →
      threadEmbedding-injective img
        (sym (Perm.inverseʳ pi) ■ cong (Perm._⟨$⟩ʳ_ pi) eq ■ Perm.inverseʳ pi)
  ; endpointEmbedding = endpointEmbedding img
  ; endpoint-respects-channel = endpoint-respects-channel img
  ; live-channel = live-channel img
  ; live-thread = λ j →
      lookup-permute pi ts (threadEmbedding img j) ■
      live-thread img j
  ; garbage-channel = garbage-channel img
  ; garbage-thread = λ j outside →
      let
        old-outside : ThreadOutside {P = P} (threadEmbedding img) (Perm._⟨$⟩ʳ_ pi j)
        old-outside k eq =
          outside k (cong (Perm._⟨$⟩ˡ_ pi) eq ■ Perm.inverseˡ pi)
      in
      cong (lookup (threads (permuteConfig pi (config cs ts))))
        (sym (Perm.inverseˡ pi)) ■
      lookup-permute pi ts (Perm._⟨$⟩ʳ_ pi j) ■
      garbage-thread img (Perm._⟨$⟩ʳ_ pi j) old-outside
  }

permute-image-id :
  {P : Typed.Proc 0} {C : Config n m} →
  (img : SoupImage P C) →
  threadEmbedding (permute-image Perm.id img) ≗ threadEmbedding img
permute-image-id img j = refl
