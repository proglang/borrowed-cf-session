-- | Locate two distinct expression processes in a common two-hole context.
module BorrowedCF.Simulation.BackwardSoup.LocatePair where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( Located; located; ProcessContext; plug; threadInContext; locate
        ; focusEnv; thread-content)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; par₂; par₂ˢ; left₂; right₂; bind₂
        ; plug₂; plug-fill₂; plug-fill₁; fill₂; fill₁
        ; thread₁; thread₂; thread₁-fill₂; thread₂-fill₁)
open import BorrowedCF.Simulation.BackwardSoup.Canonical
  using (toℕ-substProc)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; flattenOriented)

open Nat.Variables
open Fin.Patterns

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
