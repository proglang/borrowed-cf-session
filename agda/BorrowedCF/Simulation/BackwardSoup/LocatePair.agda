-- | Locate two distinct expression processes in a common two-hole context.
module BorrowedCF.Simulation.BackwardSoup.LocatePair where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (just)

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm
import BorrowedCF.Types as Types

open import BorrowedCF.Reduction.Base using (ChanCx)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( Located; located; ProcessContext; plug; threadInContext; locate
        ; focusEnv; thread-content; image-thread; focusExprTyping)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; par₂; par₂ˢ; left₂; right₂; bind₂
        ; plug₂; plug-fill₂; plug-fill₁; fill₂; fill₁
        ; thread₁; thread₂; thread₁-fill₂; thread₂-fill₁)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (toℕ-substProc)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; flattenOriented; threadEmbedding)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)

open Nat.Variables
open Fin.Patterns
open Typed using (_;_⊢ₚ_)
open Source using (_;_⊢_∶_∣_)

------------------------------------------------------------------------
-- The equality-indexed presentation avoids transporting process indices
-- along a separate equation for the reconstructed process.

data LocatedPair :
  (P : Typed.Proc n) →
  𝔽 (Translation.processCount P) →
  𝔽 (Translation.processCount P) → Set where
  located-pair :
    {k₁ k₂ n : ℕ}
    (ctx : ProcessContext₂ k₁ k₂ n)
    (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
    LocatedPair
      (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
      (thread₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
      (thread₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)

private
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  retarget :
    {P : Typed.Proc n}
    {i i′ j j′ : 𝔽 (Translation.processCount P)} →
    i ≡ i′ → j ≡ j′ → LocatedPair P i j → LocatedPair P i′ j′
  retarget refl refl pair = pair

  splitAt-inl :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {l : 𝔽 p} →
    Fin.splitAt p i ≡ inj₁ l → l ↑ˡ q ≡ i
  splitAt-inl p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  splitAt-inr :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {r : 𝔽 q} →
    Fin.splitAt p i ≡ inj₂ r → p ↑ʳ r ≡ i
  splitAt-inr p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  under-left :
    {P : Typed.Proc n} {i j : 𝔽 (Translation.processCount P)}
    (Q : Typed.Proc n) → LocatedPair P i j →
    LocatedPair (P Typed.∥ Q)
      (i ↑ˡ Translation.processCount Q)
      (j ↑ˡ Translation.processCount Q)
  under-left Q (located-pair ctx e₁ e₂) =
    located-pair (left₂ ctx Q) e₁ e₂

  under-right :
    {Q : Typed.Proc n} {i j : 𝔽 (Translation.processCount Q)}
    (P : Typed.Proc n) → LocatedPair Q i j →
    LocatedPair (P Typed.∥ Q)
      (Translation.processCount P ↑ʳ i)
      (Translation.processCount P ↑ʳ j)
  under-right P (located-pair ctx e₁ e₂) =
    located-pair (right₂ P ctx) e₁ e₂

  under-bind :
    {B₁ B₂ : Typed.BindGroup}
    {P : Typed.Proc (sum B₁ + sum B₂ + n)}
    {i j : 𝔽 (Translation.processCount P)} →
    LocatedPair P i j →
    LocatedPair (Typed.ν B₁ B₂ P) i j
  under-bind (located-pair ctx e₁ e₂) =
    located-pair (bind₂ _ _ ctx) e₁ e₂

  across-lr :
    {P Q : Typed.Proc n}
    {i : 𝔽 (Translation.processCount P)}
    {j : 𝔽 (Translation.processCount Q)} →
    Located P i → Located Q j →
    LocatedPair (P Typed.∥ Q)
      (i ↑ˡ Translation.processCount Q)
      (Translation.processCount P ↑ʳ j)
  across-lr (located ctx₁ e₁) (located ctx₂ e₂) =
    located-pair (par₂ ctx₁ ctx₂) e₁ e₂

  across-rl :
    {P Q : Typed.Proc n}
    {i : 𝔽 (Translation.processCount Q)}
    {j : 𝔽 (Translation.processCount P)} →
    Located Q i → Located P j →
    LocatedPair (P Typed.∥ Q)
      (Translation.processCount P ↑ʳ i)
      (j ↑ˡ Translation.processCount Q)
  across-rl (located ctx₁ e₁) (located ctx₂ e₂) =
    located-pair (par₂ˢ ctx₂ ctx₁) e₁ e₂

------------------------------------------------------------------------
-- Distinct process indices necessarily meet at a parallel node.  Above that
-- node they move together through parallel siblings and restrictions.

locatePair :
  (P : Typed.Proc n)
  (i j : 𝔽 (Translation.processCount P)) →
  i ≢ j → LocatedPair P i j
locatePair Typed.⟪ e ⟫ 0F 0F apart = ⊥-elim (apart refl)
locatePair (P Typed.∥ Q) i j apart
  with Fin.splitAt (Translation.processCount P) i in splitI
     | Fin.splitAt (Translation.processCount P) j in splitJ
... | inj₁ l | inj₁ r =
  retarget leftI leftJ
    (under-left Q (locatePair P l r leftApart))
  where
  leftI = splitAt-inl (Translation.processCount P) splitI
  leftJ = splitAt-inl (Translation.processCount P) splitJ
  leftApart : l ≢ r
  leftApart equal =
    apart
      (sym leftI ■
       cong (_↑ˡ Translation.processCount Q) equal ■
       leftJ)
... | inj₁ l | inj₂ r =
  retarget
    (splitAt-inl (Translation.processCount P) splitI)
    (splitAt-inr (Translation.processCount P) splitJ)
    (across-lr (locate P l) (locate Q r))
... | inj₂ l | inj₁ r =
  retarget
    (splitAt-inr (Translation.processCount P) splitI)
    (splitAt-inl (Translation.processCount P) splitJ)
    (across-rl (locate Q l) (locate P r))
... | inj₂ l | inj₂ r =
  retarget rightI rightJ
    (under-right P (locatePair Q l r rightApart))
  where
  rightI = splitAt-inr (Translation.processCount P) splitI
  rightJ = splitAt-inr (Translation.processCount P) splitJ
  rightApart : l ≢ r
  rightApart equal =
    apart
      (sym rightI ■
       cong (Translation.processCount P ↑ʳ_) equal ■
       rightJ)
locatePair (Typed.ν B₁ B₂ P) i j apart =
  under-bind (locatePair P i j apart)

------------------------------------------------------------------------
-- Recover both source indices before locating their common two-hole
-- context.  Distinct physical slots imply distinct source indices because
-- a local image embeds source threads functionally.

image-thread-pair :
  {P : Typed.Proc 0} {n m : ℕ} {C : Soup.Config n m}
  (image : GlobalImage P C) (j l : 𝔽 m) →
  j ≢ l →
  lookup (Soup.threads C) j ≢ SoupTerm.K Source.`unit →
  lookup (Soup.threads C) l ≢ SoupTerm.K Source.`unit →
  Σ[ i₁ ∈ 𝔽 (Translation.processCount P) ]
  Σ[ i₂ ∈ 𝔽 (Translation.processCount P) ]
    ((threadEmbedding (localImage image) i₁ ≡ just j) ×
     (lookup (Soup.threads C) j ≡
       lookup
         (proj₂
           (flattenOriented P (logicalChannels image) (λ ())))
         i₁)) ×
    ((threadEmbedding (localImage image) i₂ ≡ just l) ×
     (lookup (Soup.threads C) l ≡
       lookup
         (proj₂
           (flattenOriented P (logicalChannels image) (λ ())))
         i₂)) ×
    LocatedPair P i₁ i₂
image-thread-pair {P = P} image j l slots-apart live₁ live₂
  with image-thread image j live₁ | image-thread image l live₂
... | i₁ , embedded₁ , content₁ | i₂ , embedded₂ , content₂ =
  i₁ , i₂ ,
  (embedded₁ , content₁) ,
  (embedded₂ , content₂) ,
  locatePair P i₁ i₂ source-apart
  where
  source-apart : i₁ ≢ i₂
  source-apart equal =
    slots-apart
      (just-injective
        (sym embedded₁
         ■ cong (threadEmbedding (localImage image)) equal
         ■ embedded₂))

------------------------------------------------------------------------
-- Type both located expressions by viewing the common two-hole context as
-- each of its two one-hole projections.

focusPairExprTyping :
  (ctx : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  {Γ : Context.Ctx n} {γ : Context.Struct n} →
  ChanCx Γ →
  Γ ; γ ⊢ₚ plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ →
  (Σ[ Γ₁ ∈ Context.Ctx k₁ ] Σ[ γ₁ ∈ Context.Struct k₁ ]
    ChanCx Γ₁ × (Γ₁ ; γ₁ ⊢ e₁ ∶ Types.`⊤ ∣ Types.𝕀)) ×
  (Σ[ Γ₂ ∈ Context.Ctx k₂ ] Σ[ γ₂ ∈ Context.Struct k₂ ]
    ChanCx Γ₂ × (Γ₂ ; γ₂ ⊢ e₂ ∶ Types.`⊤ ∣ Types.𝕀))
focusPairExprTyping ctx e₁ e₂ {Γ = Γ} {γ = γ} Γ-S ⊢P =
  focusExprTyping (fill₂ ctx Typed.⟪ e₂ ⟫) e₁ Γ-S
    (subst (Γ ; γ ⊢ₚ_)
      (sym (plug-fill₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)) ⊢P)
  ,
  focusExprTyping (fill₁ ctx Typed.⟪ e₁ ⟫) e₂ Γ-S
    (subst (Γ ; γ ⊢ₚ_)
      (sym (plug-fill₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)) ⊢P)

------------------------------------------------------------------------
-- Content of the two holes.  `plug-fill₂` and `plug-fill₁` are only
-- propositional equalities, so the logical-channel vector and thread index
-- are transported explicitly before applying the one-hole `thread-content`
-- theorem.

private
  flatten-thread-resp :
    {c : ℕ}
    {P Q : Typed.Proc n} (equal : P ≡ Q)
    (channels : Vec (OrientedChannel c) (Translation.channelCount Q))
    (sigma : Translation.Env n (2 *ℕ c))
    (i : 𝔽 (Translation.processCount P)) →
    lookup
      (proj₂ (flattenOriented Q channels sigma))
      (subst (λ R → 𝔽 (Translation.processCount R)) equal i) ≡
    lookup
      (proj₂
        (flattenOriented P
          (subst
            (λ R → Vec (OrientedChannel c) (Translation.channelCount R))
            (sym equal) channels)
          sigma))
      i
  flatten-thread-resp refl channels sigma i = refl

thread₁-content :
  {c : ℕ}
  (ctx : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels :
    Vec (OrientedChannel c)
      (Translation.channelCount
        (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  lookup
    (proj₂
      (flattenOriented
        (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma))
    (thread₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F) ≡
  Translation.T[ e₁ ]
    (focusEnv (fill₂ ctx Typed.⟪ e₂ ⟫) Typed.⟪ e₁ ⟫
      (subst
        (λ R → Vec (OrientedChannel c) (Translation.channelCount R))
        (sym (plug-fill₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)) channels)
      sigma)
thread₁-content {c = c} ctx e₁ e₂ channels sigma =
  cong
    (lookup
      (proj₂
        (flattenOriented
          (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma)))
    (sym position) ■
  flatten-thread-resp equal channels sigma local ■
  thread-content (fill₂ ctx Typed.⟪ e₂ ⟫) e₁
    (subst
      (λ R → Vec (OrientedChannel c) (Translation.channelCount R))
      (sym equal) channels)
    sigma
  where
  equal = plug-fill₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫

  local = threadInContext (fill₂ ctx Typed.⟪ e₂ ⟫) Typed.⟪ e₁ ⟫ 0F

  position :
    subst (λ R → 𝔽 (Translation.processCount R)) equal local ≡
    thread₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F
  position = Fin.toℕ-injective
    (toℕ-substProc equal local ■
     sym (thread₁-fill₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F))

thread₂-content :
  {c : ℕ}
  (ctx : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels :
    Vec (OrientedChannel c)
      (Translation.channelCount
        (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  lookup
    (proj₂
      (flattenOriented
        (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma))
    (thread₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F) ≡
  Translation.T[ e₂ ]
    (focusEnv (fill₁ ctx Typed.⟪ e₁ ⟫) Typed.⟪ e₂ ⟫
      (subst
        (λ R → Vec (OrientedChannel c) (Translation.channelCount R))
        (sym (plug-fill₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)) channels)
      sigma)
thread₂-content {c = c} ctx e₁ e₂ channels sigma =
  cong
    (lookup
      (proj₂
        (flattenOriented
          (plug₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma)))
    (sym position) ■
  flatten-thread-resp equal channels sigma local ■
  thread-content (fill₁ ctx Typed.⟪ e₁ ⟫) e₂
    (subst
      (λ R → Vec (OrientedChannel c) (Translation.channelCount R))
      (sym equal) channels)
    sigma
  where
  equal = plug-fill₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫

  local = threadInContext (fill₁ ctx Typed.⟪ e₁ ⟫) Typed.⟪ e₂ ⟫ 0F

  position :
    subst (λ R → 𝔽 (Translation.processCount R)) equal local ≡
    thread₂ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F
  position = Fin.toℕ-injective
    (toℕ-substProc equal local ■
     sym (thread₂-fill₁ ctx Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F))
