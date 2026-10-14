-- | Injectivity facts for translated channel handles.
module BorrowedCF.Simulation.BackwardSoup.Triple where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport
  using (endpoint-side-injective)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (endpoint-channel-injective)

open Nat.Variables

------------------------------------------------------------------------
-- A translated handle is a nested pair, so equality determines each of its
-- three components.

chanTriple-injective :
  {e₁ e₁′ e₂ e₂′ : SoupTerm.Tm n} {c c′ : 𝔽 n} →
  Translation.chanTriple (e₁ , c , e₂) ≡
  Translation.chanTriple (e₁′ , c′ , e₂′) →
  (e₁ ≡ e₁′) × (c ≡ c′) × (e₂ ≡ e₂′)
chanTriple-injective refl = refl , refl , refl

------------------------------------------------------------------------
-- The arithmetic endpoint encoding is injective in both coordinates.

endpoint-injective :
  {i i′ : 𝔽 n} {side side′ : 𝔽 2} →
  Soup.endpoint i side ≡ Soup.endpoint i′ side′ →
  (i ≡ i′) × (side ≡ side′)
endpoint-injective {i = i} {i′ = i′} {side = side} {side′ = side′} equal =
  channelEq , endpoint-side channelEq equal
  where
  channelEq : i ≡ i′
  channelEq = endpoint-channel-injective equal

  endpoint-side :
    {j j′ : 𝔽 n} {s s′ : 𝔽 2} →
    j ≡ j′ → Soup.endpoint j s ≡ Soup.endpoint j′ s′ → s ≡ s′
  endpoint-side {j = j} {s = s} {s′ = s′} refl endpointEq =
    endpoint-side-injective j s s′ endpointEq
