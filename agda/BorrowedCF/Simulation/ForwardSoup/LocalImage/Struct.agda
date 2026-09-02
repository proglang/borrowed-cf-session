module BorrowedCF.Simulation.ForwardSoup.LocalImage.Struct where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Vec.Properties as VecP

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric
  using (SymClosure; fwd; bwd)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Processes.Congruence using (swapₚ-inv)

open import BorrowedCF.Simulation.ForwardSoup.Renaming
  using (untransportChannels)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (channelCount-rename)

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using ( take-++ˡ; drop-++ˡ
        ; parallel-swap-image; parallel-assoc-image
        ; unit-left-elim; unit-left-intro
        )
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Restriction
  using (restriction-swap-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Commutation
  using (commutationChannels; commutation-image; commutation-image⁻)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Extrusion
  using ( extrusionRenaming; extrusionChannels
        ; extrusion-image; extrusion-image⁻
        )
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (par-split-left; par-split-right; par-join)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image; res-split-channel; res-split-not-ambient; res-join)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Small utilities

private
  variable A : Set

  -- Casting along an equality and back is the identity.
  cast-cast :
    {a b : ℕ} (equal : a ≡ b) (xs : Vec A a) →
    V.cast (sym equal) (V.cast equal xs) ≡ xs
  cast-cast equal xs =
    VecP.cast-trans equal (sym equal) xs ■
    VecP.cast-is-id (equal ■ sym equal) xs

  -- Transporting a local image along an equality of source processes.
  proc-image :
    {k n m : ℕ} {P Q : Typed.Proc k} → P ≡ Q →
    {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
    {sigma : Translation.Env k (2 *ℕ n)}
    {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
    {C : Soup.Config n m} →
    LocalImage P logicalChannels sigma ambientChannel ambientThread C →
    Σ[ targetChannels ∈
         Vec (OrientedChannel n) (Translation.channelCount Q) ]
      LocalImage Q targetChannels sigma ambientChannel ambientThread C
  proc-image refl image = -, image

------------------------------------------------------------------------
-- Transporting a local image along the typed structural congruence.

≋′-image :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  P Typed.≋′ Q →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C →
  Σ[ targetChannels ∈ Vec (OrientedChannel n) (Translation.channelCount Q) ]
    LocalImage Q targetChannels sigma ambientChannel ambientThread C

≋′-image⁻ :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount Q)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  P Typed.≋′ Q →
  LocalImage Q logicalChannels sigma ambientChannel ambientThread C →
  Σ[ sourceChannels ∈ Vec (OrientedChannel n) (Translation.channelCount P) ]
    LocalImage P sourceChannels sigma ambientChannel ambientThread C

------------------------------------------------------------------------
-- Forward direction

≋′-image Typed.∥-comm′ image = -, parallel-swap-image image
≋′-image Typed.∥-assoc′ image = -, parallel-assoc-image image
≋′-image Typed.∥-unit′ image = -, unit-left-elim image
≋′-image Typed.ν-swap′ image = -, restriction-swap-image image
≋′-image Typed.ν-comm′ image = -, commutation-image image
≋′-image Typed.ν-ext′ image = -, extrusion-image image
≋′-image (Typed.∥-cong′ e) image =
  -, par-join
       (proj₂ (≋′-image e (par-split-left image)))
       (par-split-right image)
       (λ j → inj₂ (j , refl))
       (λ {j} {l} embedded → inj₂ (j , embedded))
       (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
       (λ _ ambient → ambient) (λ _ ambient → ambient)
≋′-image {logicalChannels = channel ∷ bodyChannels} (Typed.ν-cong′ e) image =
  -, res-join
       (proj₂ (≋′-image e (res-split-image image)))
       (res-split-channel image)
       (res-split-not-ambient image)

------------------------------------------------------------------------
-- Backward direction

≋′-image⁻ Typed.∥-comm′ image = -, parallel-swap-image image

-- `(P₁ ∥ P₂) ∥ P₃ ↝ P₁ ∥ (P₂ ∥ P₃)` by three commutations and two
-- associations, all of which are already available in the forward direction.
≋′-image⁻ Typed.∥-assoc′ image =
  -, parallel-swap-image
       (parallel-assoc-image
         (parallel-swap-image
           (parallel-assoc-image
             (parallel-swap-image image))))

≋′-image⁻ Typed.∥-unit′ image = -, unit-left-intro image

-- Swapping the two binder groups twice is the identity on processes.
≋′-image⁻ (Typed.ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) image =
  proc-image
    (cong (Typed.ν B₁ B₂) (swapₚ-inv {a = sum B₁} {b = sum B₂} P))
    (restriction-swap-image image)

≋′-image⁻ {logicalChannels = inner ∷ outer ∷ bodyChannels} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  (Typed.ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) image =
  -, commutation-image⁻ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}
       {channels = sourceChannels}
       (subst
         (λ channels →
           LocalImage
             (Typed.ν A₁ A₂ (Typed.ν B₁ B₂ (P Typed.⋯ₚ rho)))
             channels sigma ambientChannel ambientThread C)
         (sym channelsEqual) image)
  where
  rho = Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)

  sourceChannels =
    outer ∷ inner ∷ V.cast (channelCount-rename P rho) bodyChannels

  channelsEqual :
    commutationChannels B₁ B₂ A₁ A₂ P sourceChannels ≡
    inner ∷ outer ∷ bodyChannels
  channelsEqual =
    cong (λ channels → inner ∷ outer ∷ channels)
      (cast-cast (channelCount-rename P rho) bodyChannels)

≋′-image⁻ {logicalChannels = bound ∷ rest} {sigma = sigma}
  {ambientChannel = ambientChannel} {ambientThread = ambientThread} {C = C}
  (Typed.ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂} {Q = Q}) image =
  -, extrusion-image⁻ {B₁ = B₁} {B₂ = B₂} {P = P} {Q = Q}
       {logicalChannels = sourceChannels}
       (subst
         (λ channels →
           LocalImage
             (Typed.ν B₁ B₂ ((P Typed.⋯ₚ extrusionRenaming B₁ B₂) Typed.∥ Q))
             channels sigma ambientChannel ambientThread C)
         (sym channelsEqual) image)
  where
  renamedCount = Translation.channelCount (P Typed.⋯ₚ extrusionRenaming B₁ B₂)

  leftChannels =
    V.cast (channelCount-rename P (extrusionRenaming B₁ B₂))
      (V.take renamedCount rest)

  rightChannels = bound ∷ V.drop renamedCount rest

  sourceChannels = leftChannels V.++ rightChannels

  channelsEqual :
    extrusionChannels B₁ B₂ P Q sourceChannels ≡ bound ∷ rest
  channelsEqual =
    cong₂
      (λ left right →
        V.head right ∷
        (untransportChannels P (extrusionRenaming B₁ B₂) left V.++
          V.tail right))
      (take-++ˡ leftChannels rightChannels)
      (drop-++ˡ leftChannels rightChannels) ■
    cong (λ left → bound ∷ (left V.++ V.drop renamedCount rest))
      (cast-cast (channelCount-rename P (extrusionRenaming B₁ B₂))
        (V.take renamedCount rest)) ■
    cong (bound ∷_) (V.take++drop≡id renamedCount rest)

≋′-image⁻ (Typed.∥-cong′ e) image =
  -, par-join
       (proj₂ (≋′-image⁻ e (par-split-left image)))
       (par-split-right image)
       (λ j → inj₂ (j , refl))
       (λ {j} {l} embedded → inj₂ (j , embedded))
       (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁) (λ _ → inj₁)
       (λ _ ambient → ambient) (λ _ ambient → ambient)

≋′-image⁻ {logicalChannels = channel ∷ bodyChannels} (Typed.ν-cong′ e) image =
  -, res-join
       (proj₂ (≋′-image⁻ e (res-split-image image)))
       (res-split-channel image)
       (res-split-not-ambient image)

------------------------------------------------------------------------
-- The equivalence closure

≋-image :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} →
  P Typed.≋ Q →
  LocalImage P logicalChannels sigma ambientChannel ambientThread C →
  Σ[ targetChannels ∈ Vec (OrientedChannel n) (Translation.channelCount Q) ]
    LocalImage Q targetChannels sigma ambientChannel ambientThread C
≋-image ε image = -, image
≋-image (fwd step ◅ steps) image =
  ≋-image steps (proj₂ (≋′-image step image))
≋-image (bwd step ◅ steps) image =
  ≋-image steps (proj₂ (≋′-image⁻ step image))
