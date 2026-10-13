-- | Relate the binding positions of the two holes of a paired redex.
module BorrowedCF.Simulation.BackwardSoup.PairPosition where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( ProcessContext; hole; par-left; par-right; bind
        ; plug; threadInContext; focusEnv; focusValueEnv; focusPairEnv
        ; bindEnv-Pair)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (PairEnv)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (weakenThrough; SideOf; inl; inr; sideOf; groupOf)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; par₂; par₂ˢ; left₂; right₂; bind₂
        ; plug₂; thread₁; thread₂; compose₂; wt₁; wt₂; Binder₂; binder₂)
open import BorrowedCF.Simulation.BackwardSoup.AcqShape
  using (UB-entry-shape)
open import BorrowedCF.Simulation.BackwardSoup.Triple
  using (chanTriple-injective; endpoint-injective)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalChannel; physicalEndpoint; flattenOriented)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using ( bindEnv; bindChannel; flatten-bind-thread
        ; flatten-bind-channel; flatten-bind-channel-suc)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames
  using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using ( lookup-take; lookup-drop; flatten-par-channels
        ; flatten-par-threads)
open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (++ₛ-lookupˡ; ++ₛ-lookupʳ)

open Nat.Variables
open Fin.Patterns

private
  variable
    B₁ B₂ : Typed.BindGroup
    p : ℕ

  splitAt-inj₁ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {l : 𝔽 p} →
    Fin.splitAt p i ≡ inj₁ l → l ↑ˡ q ≡ i
  splitAt-inj₁ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  splitAt-inj₂ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {r : 𝔽 q} →
    Fin.splitAt p i ≡ inj₂ r → p ↑ʳ r ≡ i
  splitAt-inj₂ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

------------------------------------------------------------------------
-- Channel positions contributed by a process context.

contextChannels : ProcessContext k n → ℕ
contextChannels hole = 0
contextChannels (par-left c Q) = contextChannels c + Translation.channelCount Q
contextChannels (par-right Q c) = Translation.channelCount Q + contextChannels c
contextChannels (bind B₁ B₂ c) = suc (contextChannels c)

pairChannels : ProcessContext₂ k₁ k₂ n → ℕ
pairChannels (par₂ c₁ c₂) = contextChannels c₁ + contextChannels c₂
pairChannels (par₂ˢ c₂ c₁) = contextChannels c₂ + contextChannels c₁
pairChannels (left₂ c Q) = pairChannels c + Translation.channelCount Q
pairChannels (right₂ Q c) = Translation.channelCount Q + pairChannels c
pairChannels (bind₂ B₁ B₂ c) = suc (pairChannels c)

contextChannels-count :
  (c : ProcessContext k n) (e : Source.Tm k) →
  contextChannels c ≡ Translation.channelCount (plug c Typed.⟪ e ⟫)
contextChannels-count hole e = refl
contextChannels-count (par-left c Q) e =
  cong (_+ Translation.channelCount Q) (contextChannels-count c e)
contextChannels-count (par-right Q c) e =
  cong (Translation.channelCount Q +_) (contextChannels-count c e)
contextChannels-count (bind B₁ B₂ c) e =
  cong suc (contextChannels-count c e)

pairChannels-count :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  pairChannels c ≡
  Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
pairChannels-count (par₂ c₁ c₂) e₁ e₂ =
  cong₂ _+_ (contextChannels-count c₁ e₁) (contextChannels-count c₂ e₂)
pairChannels-count (par₂ˢ c₂ c₁) e₁ e₂ =
  cong₂ _+_ (contextChannels-count c₂ e₂) (contextChannels-count c₁ e₁)
pairChannels-count (left₂ c Q) e₁ e₂ =
  cong (_+ Translation.channelCount Q) (pairChannels-count c e₁ e₂)
pairChannels-count (right₂ Q c) e₁ e₂ =
  cong (Translation.channelCount Q +_) (pairChannels-count c e₁ e₂)
pairChannels-count (bind₂ B₁ B₂ c) e₁ e₂ =
  cong suc (pairChannels-count c e₁ e₂)

------------------------------------------------------------------------
-- A binding in a one-hole context, indexed by its flattened channel slot.

data Bound : (c : ProcessContext k n) →
             𝔽 k → 𝔽 (contextChannels c) → Set where
  bound-left :
    {c : ProcessContext k n} {Q : Typed.Proc n} {x : 𝔽 k}
    {i : 𝔽 (contextChannels c)} →
    Bound c x i →
    Bound (par-left c Q) x (i ↑ˡ Translation.channelCount Q)

  bound-right :
    {c : ProcessContext k n} {Q : Typed.Proc n} {x : 𝔽 k}
    {i : 𝔽 (contextChannels c)} →
    Bound c x i →
    Bound (par-right Q c) x (Translation.channelCount Q ↑ʳ i)

  bound-here :
    {c : ProcessContext k (sum B₁ + sum B₂ + n)} {x : 𝔽 k} →
    (local : 𝔽 (sum B₁ + sum B₂)) →
    weakenThrough c (local ↑ˡ n) ≡ x →
    Bound (bind B₁ B₂ c) x 0F

  bound-under :
    {c : ProcessContext k (sum B₁ + sum B₂ + n)} {x : 𝔽 k}
    {i : 𝔽 (contextChannels c)} →
    Bound c x i →
    Bound (bind B₁ B₂ c) x (suc i)

resolveBound :
  (c : ProcessContext k n) (x : 𝔽 k) →
  (Σ[ i ∈ 𝔽 (contextChannels c) ] Bound c x i) ⊎
  (Σ[ y ∈ 𝔽 n ] weakenThrough c y ≡ x)
resolveBound hole x = inj₂ (x , refl)
resolveBound (par-left c Q) x with resolveBound c x
... | inj₁ (i , found) = inj₁ (i ↑ˡ Translation.channelCount Q , bound-left found)
... | inj₂ ambient = inj₂ ambient
resolveBound (par-right Q c) x with resolveBound c x
... | inj₁ (i , found) = inj₁ (Translation.channelCount Q ↑ʳ i , bound-right found)
... | inj₂ ambient = inj₂ ambient
resolveBound (bind B₁ B₂ c) x with resolveBound c x
... | inj₁ (i , found) = inj₁ (suc i , bound-under found)
... | inj₂ (y , eq) with Fin.splitAt (sum B₁ + sum B₂) y in splitEq
...   | inj₁ local =
  inj₁
    ( 0F
    , bound-here local
        (cong (weakenThrough c) (splitAt-inj₁ (sum B₁ + sum B₂) splitEq)
         ■ eq)
    )
...   | inj₂ outer =
  inj₂ (outer ,
    (cong (weakenThrough c)
      (splitAt-inj₂ (sum B₁ + sum B₂) splitEq) ■ eq))

------------------------------------------------------------------------
-- The physical endpoint represented by a one-hole binding position.

boundChannel :
  {c : ProcessContext k n} {x : 𝔽 k} {i : 𝔽 (contextChannels c)} →
  Bound c x i → (e : Source.Tm k) →
  𝔽 (Translation.channelCount (plug c Typed.⟪ e ⟫))
boundChannel (bound-left {Q = Q} found) e =
  boundChannel found e ↑ˡ Translation.channelCount Q
boundChannel (bound-right {Q = Q} found) e =
  Translation.channelCount Q ↑ʳ boundChannel found e
boundChannel (bound-here local eq) e = 0F
boundChannel (bound-under found) e = suc (boundChannel found e)

focusEnv-ambient :
  (c : ProcessContext k n) (e : Source.Tm k)
  (channels :
    Vec (OrientedChannel p) (Translation.channelCount (plug c Typed.⟪ e ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) (y : 𝔽 n) →
  focusEnv c Typed.⟪ e ⟫ channels sigma (weakenThrough c y) ≡ sigma y
focusEnv-ambient hole e channels sigma y = refl
focusEnv-ambient (par-left c Q) e channels sigma y =
  focusEnv-ambient c e
    (V.take (Translation.channelCount (plug c Typed.⟪ e ⟫)) channels)
    sigma y
focusEnv-ambient (par-right Q c) e channels sigma y =
  focusEnv-ambient c e
    (V.drop (Translation.channelCount Q) channels) sigma y
focusEnv-ambient (bind B₁ B₂ c) e (channel ∷ channels) sigma y =
  focusEnv-ambient c e channels (bindEnv B₁ B₂ channel sigma)
    ((sum B₁ + sum B₂) ↑ʳ y)
  ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma y

bound-endpoint :
  {c : ProcessContext k n} {x : 𝔽 k} {i : 𝔽 (contextChannels c)} →
  (found : Bound c x i) (e : Source.Tm k)
  (channels :
    Vec (OrientedChannel p) (Translation.channelCount (plug c Typed.⟪ e ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) →
  Σ[ side ∈ 𝔽 2 ] Σ[ left ∈ SoupTerm.Tm (2 *ℕ p) ]
  Σ[ right ∈ SoupTerm.Tm (2 *ℕ p) ]
    focusEnv c Typed.⟪ e ⟫ channels sigma x ≡
    Translation.chanTriple
      ( left
      , physicalEndpoint (lookup channels (boundChannel found e)) side
      , right
      )
bound-endpoint (bound-left {c = c} {Q = Q} found) e channels sigma
  with bound-endpoint found e
         (V.take (Translation.channelCount (plug c Typed.⟪ e ⟫)) channels)
         sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-take
      (Translation.channelCount (plug c Typed.⟪ e ⟫)) channels
      (boundChannel found e)))
bound-endpoint (bound-right {c = c} {Q = Q} found) e channels sigma
  with bound-endpoint found e
         (V.drop (Translation.channelCount Q) channels) sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-drop (Translation.channelCount Q) channels
      (boundChannel found e)))
bound-endpoint {n = n} {c = bind B₁ B₂ c}
  (bound-here local localEq)
  e (channel ∷ channels) sigma
  with sideOf B₁ B₂ local
... | inl i
  with UB-entry-shape B₁ (physicalEndpoint channel 0F)
         (physicalEndpoint channel 0F) SoupTerm.* SoupTerm.* i (groupOf B₁ i)
... | left , right , entryEq =
  0F , left , right ,
  ( cong (focusEnv c Typed.⟪ e ⟫ channels (bindEnv B₁ B₂ channel sigma))
      (sym localEq)
  ■ focusEnv-ambient c e channels (bindEnv B₁ B₂ channel sigma)
      ((i ↑ˡ sum B₂) ↑ˡ n)
  ■ ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma (i ↑ˡ sum B₂)
  ■ ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)))
      (proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))) i
  ■ entryEq
  )
bound-endpoint {n = n} {c = bind B₁ B₂ c}
  (bound-here local localEq)
  e (channel ∷ channels) sigma
  | inr i
  with UB-entry-shape B₂ (physicalEndpoint channel 1F)
         (physicalEndpoint channel 1F) SoupTerm.* SoupTerm.* i (groupOf B₂ i)
... | left , right , entryEq =
  1F , left , right ,
  ( cong (focusEnv c Typed.⟪ e ⟫ channels (bindEnv B₁ B₂ channel sigma))
      (sym localEq)
  ■ focusEnv-ambient c e channels (bindEnv B₁ B₂ channel sigma)
      ((sum B₁ ↑ʳ i) ↑ˡ n)
  ■ ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma (sum B₁ ↑ʳ i)
  ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)))
      (proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))) i
  ■ entryEq
  )
bound-endpoint {c = bind B₁ B₂ c} (bound-under found)
  e (channel ∷ channels) sigma =
  bound-endpoint found e channels (bindEnv B₁ B₂ channel sigma)

------------------------------------------------------------------------
-- The corresponding positions for each hole of a two-hole context.

data Bound₁ : (c : ProcessContext₂ k₁ k₂ n) →
              𝔽 k₁ → 𝔽 (pairChannels c) → Set where
  bound₁-par :
    {c₁ : ProcessContext k₁ n} {c₂ : ProcessContext k₂ n}
    {x : 𝔽 k₁} {i : 𝔽 (contextChannels c₁)} →
    Bound c₁ x i →
    Bound₁ (par₂ c₁ c₂) x (i ↑ˡ contextChannels c₂)

  bound₁-parˢ :
    {c₁ : ProcessContext k₁ n} {c₂ : ProcessContext k₂ n}
    {x : 𝔽 k₁} {i : 𝔽 (contextChannels c₁)} →
    Bound c₁ x i →
    Bound₁ (par₂ˢ c₂ c₁) x (contextChannels c₂ ↑ʳ i)

  bound₁-left :
    {c : ProcessContext₂ k₁ k₂ n} {Q : Typed.Proc n}
    {x : 𝔽 k₁} {i : 𝔽 (pairChannels c)} →
    Bound₁ c x i →
    Bound₁ (left₂ c Q) x (i ↑ˡ Translation.channelCount Q)

  bound₁-right :
    {c : ProcessContext₂ k₁ k₂ n} {Q : Typed.Proc n}
    {x : 𝔽 k₁} {i : 𝔽 (pairChannels c)} →
    Bound₁ c x i →
    Bound₁ (right₂ Q c) x (Translation.channelCount Q ↑ʳ i)

  bound₁-here :
    {c : ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n)} {x : 𝔽 k₁} →
    (local : 𝔽 (sum B₁ + sum B₂)) →
    wt₁ c (local ↑ˡ n) ≡ x →
    Bound₁ (bind₂ B₁ B₂ c) x 0F

  bound₁-under :
    {c : ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n)} {x : 𝔽 k₁}
    {i : 𝔽 (pairChannels c)} →
    Bound₁ c x i →
    Bound₁ (bind₂ B₁ B₂ c) x (suc i)

data Bound₂ : (c : ProcessContext₂ k₁ k₂ n) →
              𝔽 k₂ → 𝔽 (pairChannels c) → Set where
  bound₂-par :
    {c₁ : ProcessContext k₁ n} {c₂ : ProcessContext k₂ n}
    {x : 𝔽 k₂} {i : 𝔽 (contextChannels c₂)} →
    Bound c₂ x i →
    Bound₂ (par₂ c₁ c₂) x (contextChannels c₁ ↑ʳ i)

  bound₂-parˢ :
    {c₁ : ProcessContext k₁ n} {c₂ : ProcessContext k₂ n}
    {x : 𝔽 k₂} {i : 𝔽 (contextChannels c₂)} →
    Bound c₂ x i →
    Bound₂ (par₂ˢ c₂ c₁) x (i ↑ˡ contextChannels c₁)

  bound₂-left :
    {c : ProcessContext₂ k₁ k₂ n} {Q : Typed.Proc n}
    {x : 𝔽 k₂} {i : 𝔽 (pairChannels c)} →
    Bound₂ c x i →
    Bound₂ (left₂ c Q) x (i ↑ˡ Translation.channelCount Q)

  bound₂-right :
    {c : ProcessContext₂ k₁ k₂ n} {Q : Typed.Proc n}
    {x : 𝔽 k₂} {i : 𝔽 (pairChannels c)} →
    Bound₂ c x i →
    Bound₂ (right₂ Q c) x (Translation.channelCount Q ↑ʳ i)

  bound₂-here :
    {c : ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n)} {x : 𝔽 k₂} →
    (local : 𝔽 (sum B₁ + sum B₂)) →
    wt₂ c (local ↑ˡ n) ≡ x →
    Bound₂ (bind₂ B₁ B₂ c) x 0F

  bound₂-under :
    {c : ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n)} {x : 𝔽 k₂}
    {i : 𝔽 (pairChannels c)} →
    Bound₂ c x i →
    Bound₂ (bind₂ B₁ B₂ c) x (suc i)

------------------------------------------------------------------------
-- Focused environments and physical channel slots for the two holes.

pairFocusEnv₁ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))) →
  Translation.Env n (2 *ℕ p) → Translation.Env k₁ (2 *ℕ p)
pairFocusEnv₁ (par₂ c₁ c₂) e₁ e₂ channels sigma =
  focusEnv c₁ Typed.⟪ e₁ ⟫
    (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma
pairFocusEnv₁ (par₂ˢ c₂ c₁) e₁ e₂ channels sigma =
  focusEnv c₁ Typed.⟪ e₁ ⟫
    (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma
pairFocusEnv₁ (left₂ c Q) e₁ e₂ channels sigma =
  pairFocusEnv₁ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma
pairFocusEnv₁ (right₂ Q c) e₁ e₂ channels sigma =
  pairFocusEnv₁ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma
pairFocusEnv₁ (bind₂ B₁ B₂ c) e₁ e₂ (channel ∷ channels) sigma =
  pairFocusEnv₁ c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

pairFocusEnv₂ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))) →
  Translation.Env n (2 *ℕ p) → Translation.Env k₂ (2 *ℕ p)
pairFocusEnv₂ (par₂ c₁ c₂) e₁ e₂ channels sigma =
  focusEnv c₂ Typed.⟪ e₂ ⟫
    (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma
pairFocusEnv₂ (par₂ˢ c₂ c₁) e₁ e₂ channels sigma =
  focusEnv c₂ Typed.⟪ e₂ ⟫
    (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma
pairFocusEnv₂ (left₂ c Q) e₁ e₂ channels sigma =
  pairFocusEnv₂ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma
pairFocusEnv₂ (right₂ Q c) e₁ e₂ channels sigma =
  pairFocusEnv₂ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma
pairFocusEnv₂ (bind₂ B₁ B₂ c) e₁ e₂ (channel ∷ channels) sigma =
  pairFocusEnv₂ c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

pairFocusValueEnv₁ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  {sigma : Translation.Env n (2 *ℕ p)} →
  ValueEnv sigma → ValueEnv (pairFocusEnv₁ c e₁ e₂ channels sigma)
pairFocusValueEnv₁ (par₂ c₁ c₂) e₁ e₂ channels Vsigma =
  focusValueEnv c₁ Typed.⟪ e₁ ⟫
    (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    Vsigma
pairFocusValueEnv₁ (par₂ˢ c₂ c₁) e₁ e₂ channels Vsigma =
  focusValueEnv c₁ Typed.⟪ e₁ ⟫
    (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    Vsigma
pairFocusValueEnv₁ (left₂ c Q) e₁ e₂ channels Vsigma =
  pairFocusValueEnv₁ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    Vsigma
pairFocusValueEnv₁ (right₂ Q c) e₁ e₂ channels Vsigma =
  pairFocusValueEnv₁ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) Vsigma
pairFocusValueEnv₁ (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) Vsigma =
  pairFocusValueEnv₁ c e₁ e₂ channels
    (bindEnv-Value {B₁ = B₁} {B₂ = B₂} {channel = channel} Vsigma)

pairFocusValueEnv₂ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  {sigma : Translation.Env n (2 *ℕ p)} →
  ValueEnv sigma → ValueEnv (pairFocusEnv₂ c e₁ e₂ channels sigma)
pairFocusValueEnv₂ (par₂ c₁ c₂) e₁ e₂ channels Vsigma =
  focusValueEnv c₂ Typed.⟪ e₂ ⟫
    (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    Vsigma
pairFocusValueEnv₂ (par₂ˢ c₂ c₁) e₁ e₂ channels Vsigma =
  focusValueEnv c₂ Typed.⟪ e₂ ⟫
    (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    Vsigma
pairFocusValueEnv₂ (left₂ c Q) e₁ e₂ channels Vsigma =
  pairFocusValueEnv₂ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    Vsigma
pairFocusValueEnv₂ (right₂ Q c) e₁ e₂ channels Vsigma =
  pairFocusValueEnv₂ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) Vsigma
pairFocusValueEnv₂ (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) Vsigma =
  pairFocusValueEnv₂ c e₁ e₂ channels
    (bindEnv-Value {B₁ = B₁} {B₂ = B₂} {channel = channel} Vsigma)

pairFocusPairEnv₁ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  {sigma : Translation.Env n (2 *ℕ p)} →
  PairEnv sigma → PairEnv (pairFocusEnv₁ c e₁ e₂ channels sigma)
pairFocusPairEnv₁ (par₂ c₁ c₂) e₁ e₂ channels Psigma =
  focusPairEnv c₁ Typed.⟪ e₁ ⟫
    (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    Psigma
pairFocusPairEnv₁ (par₂ˢ c₂ c₁) e₁ e₂ channels Psigma =
  focusPairEnv c₁ Typed.⟪ e₁ ⟫
    (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    Psigma
pairFocusPairEnv₁ (left₂ c Q) e₁ e₂ channels Psigma =
  pairFocusPairEnv₁ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    Psigma
pairFocusPairEnv₁ (right₂ Q c) e₁ e₂ channels Psigma =
  pairFocusPairEnv₁ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) Psigma
pairFocusPairEnv₁ (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) Psigma =
  pairFocusPairEnv₁ c e₁ e₂ channels
    (bindEnv-Pair {B₁ = B₁} {B₂ = B₂} {channel = channel} Psigma)

pairFocusPairEnv₂ :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  {sigma : Translation.Env n (2 *ℕ p)} →
  PairEnv sigma → PairEnv (pairFocusEnv₂ c e₁ e₂ channels sigma)
pairFocusPairEnv₂ (par₂ c₁ c₂) e₁ e₂ channels Psigma =
  focusPairEnv c₂ Typed.⟪ e₂ ⟫
    (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    Psigma
pairFocusPairEnv₂ (par₂ˢ c₂ c₁) e₁ e₂ channels Psigma =
  focusPairEnv c₂ Typed.⟪ e₂ ⟫
    (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    Psigma
pairFocusPairEnv₂ (left₂ c Q) e₁ e₂ channels Psigma =
  pairFocusPairEnv₂ c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    Psigma
pairFocusPairEnv₂ (right₂ Q c) e₁ e₂ channels Psigma =
  pairFocusPairEnv₂ c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) Psigma
pairFocusPairEnv₂ (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) Psigma =
  pairFocusPairEnv₂ c e₁ e₂ channels
    (bindEnv-Pair {B₁ = B₁} {B₂ = B₂} {channel = channel} Psigma)

pairThread₁-content :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) →
  lookup
    (proj₂ (flattenOriented
      (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma))
    (thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F) ≡
  Translation.T[ e₁ ] (pairFocusEnv₁ c e₁ e₂ channels sigma)
pairThread₁-content (par₂ c₁ c₂) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (threadInContext c₁ Typed.⟪ e₁ ⟫ 0F ↑ˡ
        Translation.processCount (plug c₂ Typed.⟪ e₂ ⟫)))
    (flatten-par-threads
      (plug c₁ Typed.⟪ e₁ ⟫) (plug c₂ Typed.⟪ e₂ ⟫) channels sigma)
  ■ V.lookup-++ˡ
      (proj₂ (flattenOriented (plug c₁ Typed.⟪ e₁ ⟫)
        (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
        sigma))
      (proj₂ (flattenOriented (plug c₂ Typed.⟪ e₂ ⟫)
        (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
        sigma))
      (threadInContext c₁ Typed.⟪ e₁ ⟫ 0F)
  ■ BorrowedCF.Simulation.BackwardSoup.Locate.thread-content c₁ e₁
      (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
      sigma
pairThread₁-content (par₂ˢ c₂ c₁) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (Translation.processCount (plug c₂ Typed.⟪ e₂ ⟫) ↑ʳ
        threadInContext c₁ Typed.⟪ e₁ ⟫ 0F))
    (flatten-par-threads
      (plug c₂ Typed.⟪ e₂ ⟫) (plug c₁ Typed.⟪ e₁ ⟫) channels sigma)
  ■ V.lookup-++ʳ
      (proj₂ (flattenOriented (plug c₂ Typed.⟪ e₂ ⟫)
        (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
        sigma))
      (proj₂ (flattenOriented (plug c₁ Typed.⟪ e₁ ⟫)
        (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
        sigma))
      (threadInContext c₁ Typed.⟪ e₁ ⟫ 0F)
  ■ BorrowedCF.Simulation.BackwardSoup.Locate.thread-content c₁ e₁
      (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
      sigma
pairThread₁-content (left₂ c Q) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F ↑ˡ
        Translation.processCount Q))
    (flatten-par-threads
      (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) Q channels sigma)
  ■ V.lookup-++ˡ
      (proj₂ (flattenOriented
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
        (V.take
          (Translation.channelCount
            (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels)
        sigma))
      (proj₂ (flattenOriented Q
        (V.drop
          (Translation.channelCount
            (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels)
        sigma))
      (thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₁-content c e₁ e₂
      (V.take
        (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
        channels)
      sigma
pairThread₁-content (right₂ Q c) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (Translation.processCount Q ↑ʳ
        thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F))
    (flatten-par-threads
      Q (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma)
  ■ V.lookup-++ʳ
      (proj₂ (flattenOriented Q
        (V.take (Translation.channelCount Q) channels) sigma))
      (proj₂ (flattenOriented
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
        (V.drop (Translation.channelCount Q) channels) sigma))
      (thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₁-content c e₁ e₂
      (V.drop (Translation.channelCount Q) channels) sigma
pairThread₁-content (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) sigma =
  flatten-bind-thread
    {B₁ = B₁} {B₂ = B₂}
    {P = plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫}
    {channel = channel} {logicalChannels = channels} {sigma = sigma}
    (thread₁ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₁-content c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

pairThread₂-content :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) →
  lookup
    (proj₂ (flattenOriented
      (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma))
    (thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F) ≡
  Translation.T[ e₂ ] (pairFocusEnv₂ c e₁ e₂ channels sigma)
pairThread₂-content (par₂ c₁ c₂) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (Translation.processCount (plug c₁ Typed.⟪ e₁ ⟫) ↑ʳ
        threadInContext c₂ Typed.⟪ e₂ ⟫ 0F))
    (flatten-par-threads
      (plug c₁ Typed.⟪ e₁ ⟫) (plug c₂ Typed.⟪ e₂ ⟫) channels sigma)
  ■ V.lookup-++ʳ
      (proj₂ (flattenOriented (plug c₁ Typed.⟪ e₁ ⟫)
        (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
        sigma))
      (proj₂ (flattenOriented (plug c₂ Typed.⟪ e₂ ⟫)
        (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
        sigma))
      (threadInContext c₂ Typed.⟪ e₂ ⟫ 0F)
  ■ BorrowedCF.Simulation.BackwardSoup.Locate.thread-content c₂ e₂
      (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
      sigma
pairThread₂-content (par₂ˢ c₂ c₁) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (threadInContext c₂ Typed.⟪ e₂ ⟫ 0F ↑ˡ
        Translation.processCount (plug c₁ Typed.⟪ e₁ ⟫)))
    (flatten-par-threads
      (plug c₂ Typed.⟪ e₂ ⟫) (plug c₁ Typed.⟪ e₁ ⟫) channels sigma)
  ■ V.lookup-++ˡ
      (proj₂ (flattenOriented (plug c₂ Typed.⟪ e₂ ⟫)
        (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
        sigma))
      (proj₂ (flattenOriented (plug c₁ Typed.⟪ e₁ ⟫)
        (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
        sigma))
      (threadInContext c₂ Typed.⟪ e₂ ⟫ 0F)
  ■ BorrowedCF.Simulation.BackwardSoup.Locate.thread-content c₂ e₂
      (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
      sigma
pairThread₂-content (left₂ c Q) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F ↑ˡ
        Translation.processCount Q))
    (flatten-par-threads
      (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) Q channels sigma)
  ■ V.lookup-++ˡ
      (proj₂ (flattenOriented
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
        (V.take
          (Translation.channelCount
            (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels)
        sigma))
      (proj₂ (flattenOriented Q
        (V.drop
          (Translation.channelCount
            (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels)
        sigma))
      (thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₂-content c e₁ e₂
      (V.take
        (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
        channels)
      sigma
pairThread₂-content (right₂ Q c) e₁ e₂ channels sigma =
  cong
    (λ ts → lookup ts
      (Translation.processCount Q ↑ʳ
        thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F))
    (flatten-par-threads
      Q (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma)
  ■ V.lookup-++ʳ
      (proj₂ (flattenOriented Q
        (V.take (Translation.channelCount Q) channels) sigma))
      (proj₂ (flattenOriented
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
        (V.drop (Translation.channelCount Q) channels) sigma))
      (thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₂-content c e₁ e₂
      (V.drop (Translation.channelCount Q) channels) sigma
pairThread₂-content (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) sigma =
  flatten-bind-thread
    {B₁ = B₁} {B₂ = B₂}
    {P = plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫}
    {channel = channel} {logicalChannels = channels} {sigma = sigma}
    (thread₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫ 0F)
  ■ pairThread₂-content c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

pairFocusEnv₁-ambient :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) (y : 𝔽 n) →
  pairFocusEnv₁ c e₁ e₂ channels sigma (wt₁ c y) ≡ sigma y
pairFocusEnv₁-ambient (par₂ c₁ c₂) e₁ e₂ channels sigma y =
  focusEnv-ambient c₁ e₁
    (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma y
pairFocusEnv₁-ambient (par₂ˢ c₂ c₁) e₁ e₂ channels sigma y =
  focusEnv-ambient c₁ e₁
    (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma y
pairFocusEnv₁-ambient (left₂ c Q) e₁ e₂ channels sigma y =
  pairFocusEnv₁-ambient c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma y
pairFocusEnv₁-ambient (right₂ Q c) e₁ e₂ channels sigma y =
  pairFocusEnv₁-ambient c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma y
pairFocusEnv₁-ambient (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) sigma y =
  pairFocusEnv₁-ambient c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)
    ((sum B₁ + sum B₂) ↑ʳ y)
  ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma y

pairFocusEnv₂-ambient :
  (c : ProcessContext₂ k₁ k₂ n)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) (y : 𝔽 n) →
  pairFocusEnv₂ c e₁ e₂ channels sigma (wt₂ c y) ≡ sigma y
pairFocusEnv₂-ambient (par₂ c₁ c₂) e₁ e₂ channels sigma y =
  focusEnv-ambient c₂ e₂
    (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma y
pairFocusEnv₂-ambient (par₂ˢ c₂ c₁) e₁ e₂ channels sigma y =
  focusEnv-ambient c₂ e₂
    (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma y
pairFocusEnv₂-ambient (left₂ c Q) e₁ e₂ channels sigma y =
  pairFocusEnv₂-ambient c e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma y
pairFocusEnv₂-ambient (right₂ Q c) e₁ e₂ channels sigma y =
  pairFocusEnv₂-ambient c e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma y
pairFocusEnv₂-ambient (bind₂ B₁ B₂ c) e₁ e₂
  (channel ∷ channels) sigma y =
  pairFocusEnv₂-ambient c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)
    ((sum B₁ + sum B₂) ↑ʳ y)
  ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma y

pairBoundChannel₁ :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₁} {i : 𝔽 (pairChannels c)} →
  Bound₁ c x i → (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  𝔽 (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
pairBoundChannel₁ (bound₁-par {c₂ = c₂} found) e₁ e₂ =
  boundChannel found e₁ ↑ˡ
    Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)
pairBoundChannel₁ (bound₁-parˢ {c₂ = c₂} found) e₁ e₂ =
  Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫) ↑ʳ
    boundChannel found e₁
pairBoundChannel₁ (bound₁-left {Q = Q} found) e₁ e₂ =
  pairBoundChannel₁ found e₁ e₂ ↑ˡ Translation.channelCount Q
pairBoundChannel₁ (bound₁-right {Q = Q} found) e₁ e₂ =
  Translation.channelCount Q ↑ʳ pairBoundChannel₁ found e₁ e₂
pairBoundChannel₁ (bound₁-here local eq) e₁ e₂ = 0F
pairBoundChannel₁ (bound₁-under found) e₁ e₂ =
  suc (pairBoundChannel₁ found e₁ e₂)

pairBoundChannel₂ :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₂} {i : 𝔽 (pairChannels c)} →
  Bound₂ c x i → (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  𝔽 (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
pairBoundChannel₂ (bound₂-par {c₁ = c₁} found) e₁ e₂ =
  Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫) ↑ʳ
    boundChannel found e₂
pairBoundChannel₂ (bound₂-parˢ {c₁ = c₁} found) e₁ e₂ =
  boundChannel found e₂ ↑ˡ
    Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)
pairBoundChannel₂ (bound₂-left {Q = Q} found) e₁ e₂ =
  pairBoundChannel₂ found e₁ e₂ ↑ˡ Translation.channelCount Q
pairBoundChannel₂ (bound₂-right {Q = Q} found) e₁ e₂ =
  Translation.channelCount Q ↑ʳ pairBoundChannel₂ found e₁ e₂
pairBoundChannel₂ (bound₂-here local eq) e₁ e₂ = 0F
pairBoundChannel₂ (bound₂-under found) e₁ e₂ =
  suc (pairBoundChannel₂ found e₁ e₂)

private
  boundChannel-toℕ :
    {c : ProcessContext k n} {x : 𝔽 k} {i : 𝔽 (contextChannels c)} →
    (found : Bound c x i) (e : Source.Tm k) →
    Fin.toℕ (boundChannel found e) ≡ Fin.toℕ i
  boundChannel-toℕ (bound-left found) e =
    Fin.toℕ-↑ˡ _ _ ■ boundChannel-toℕ found e ■ sym (Fin.toℕ-↑ˡ _ _)
  boundChannel-toℕ (bound-right {Q = Q} {i = i} found) e =
    Fin.toℕ-↑ʳ (Translation.channelCount Q) (boundChannel found e)
    ■ cong (Translation.channelCount Q +_) (boundChannel-toℕ found e)
    ■ sym (Fin.toℕ-↑ʳ (Translation.channelCount Q) i)
  boundChannel-toℕ (bound-here local eq) e = refl
  boundChannel-toℕ (bound-under found) e =
    cong suc (boundChannel-toℕ found e)

pairBoundChannel₁-toℕ :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₁} {i : 𝔽 (pairChannels c)} →
  (found : Bound₁ c x i) (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  Fin.toℕ (pairBoundChannel₁ found e₁ e₂) ≡ Fin.toℕ i
pairBoundChannel₁-toℕ
  (bound₁-par {c₂ = c₂} found) e₁ e₂ =
  Fin.toℕ-↑ˡ (boundChannel found e₁)
      (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫))
  ■ boundChannel-toℕ found e₁
  ■ sym (Fin.toℕ-↑ˡ _ (contextChannels c₂))
pairBoundChannel₁-toℕ
  (bound₁-parˢ {c₂ = c₂} {i = i} found) e₁ e₂ =
  Fin.toℕ-↑ʳ (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫))
    (boundChannel found e₁)
  ■ cong₂ _+_ (sym (contextChannels-count c₂ e₂))
      (boundChannel-toℕ found e₁)
  ■ sym (Fin.toℕ-↑ʳ (contextChannels c₂) i)
pairBoundChannel₁-toℕ (bound₁-left found) e₁ e₂ =
  Fin.toℕ-↑ˡ _ _ ■ pairBoundChannel₁-toℕ found e₁ e₂
  ■ sym (Fin.toℕ-↑ˡ _ _)
pairBoundChannel₁-toℕ
  (bound₁-right {Q = Q} {i = i} found) e₁ e₂ =
  Fin.toℕ-↑ʳ (Translation.channelCount Q)
      (pairBoundChannel₁ found e₁ e₂)
  ■ cong (Translation.channelCount Q +_)
      (pairBoundChannel₁-toℕ found e₁ e₂)
  ■ sym (Fin.toℕ-↑ʳ (Translation.channelCount Q) i)
pairBoundChannel₁-toℕ (bound₁-here local eq) e₁ e₂ = refl
pairBoundChannel₁-toℕ (bound₁-under found) e₁ e₂ =
  cong suc (pairBoundChannel₁-toℕ found e₁ e₂)

pairBoundChannel₂-toℕ :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₂} {i : 𝔽 (pairChannels c)} →
  (found : Bound₂ c x i) (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  Fin.toℕ (pairBoundChannel₂ found e₁ e₂) ≡ Fin.toℕ i
pairBoundChannel₂-toℕ
  (bound₂-par {c₁ = c₁} {i = i} found) e₁ e₂ =
  Fin.toℕ-↑ʳ (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫))
    (boundChannel found e₂)
  ■ cong₂ _+_ (sym (contextChannels-count c₁ e₁))
      (boundChannel-toℕ found e₂)
  ■ sym (Fin.toℕ-↑ʳ (contextChannels c₁) i)
pairBoundChannel₂-toℕ
  (bound₂-parˢ {c₁ = c₁} found) e₁ e₂ =
  Fin.toℕ-↑ˡ (boundChannel found e₂)
      (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫))
  ■ boundChannel-toℕ found e₂
  ■ sym (Fin.toℕ-↑ˡ _ (contextChannels c₁))
pairBoundChannel₂-toℕ (bound₂-left found) e₁ e₂ =
  Fin.toℕ-↑ˡ _ _ ■ pairBoundChannel₂-toℕ found e₁ e₂
  ■ sym (Fin.toℕ-↑ˡ _ _)
pairBoundChannel₂-toℕ
  (bound₂-right {Q = Q} {i = i} found) e₁ e₂ =
  Fin.toℕ-↑ʳ (Translation.channelCount Q)
      (pairBoundChannel₂ found e₁ e₂)
  ■ cong (Translation.channelCount Q +_)
      (pairBoundChannel₂-toℕ found e₁ e₂)
  ■ sym (Fin.toℕ-↑ʳ (Translation.channelCount Q) i)
pairBoundChannel₂-toℕ (bound₂-here local eq) e₁ e₂ = refl
pairBoundChannel₂-toℕ (bound₂-under found) e₁ e₂ =
  cong suc (pairBoundChannel₂-toℕ found e₁ e₂)

pairBoundChannels-equal⇒indices-equal :
  {c : ProcessContext₂ k₁ k₂ n}
  {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  {i₁ i₂ : 𝔽 (pairChannels c)}
  (found₁ : Bound₁ c x₁ i₁) (found₂ : Bound₂ c x₂ i₂)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂) →
  pairBoundChannel₁ found₁ e₁ e₂ ≡ pairBoundChannel₂ found₂ e₁ e₂ →
  i₁ ≡ i₂
pairBoundChannels-equal⇒indices-equal found₁ found₂ e₁ e₂ equal =
  Fin.toℕ-injective
    ( sym (pairBoundChannel₁-toℕ found₁ e₁ e₂)
    ■ cong Fin.toℕ equal
    ■ pairBoundChannel₂-toℕ found₂ e₁ e₂
    )

bindEnv-entry :
  (B₁ B₂ : Typed.BindGroup) (channel : OrientedChannel p)
  (sigma : Translation.Env n (2 *ℕ p))
  (local : 𝔽 (sum B₁ + sum B₂)) →
  Σ[ side ∈ 𝔽 2 ] Σ[ left ∈ SoupTerm.Tm (2 *ℕ p) ]
  Σ[ right ∈ SoupTerm.Tm (2 *ℕ p) ]
    bindEnv B₁ B₂ channel sigma (local ↑ˡ n) ≡
    Translation.chanTriple
      (left , physicalEndpoint channel side , right)
bindEnv-entry B₁ B₂ channel sigma local with sideOf B₁ B₂ local
... | inl i
  with UB-entry-shape B₁ (physicalEndpoint channel 0F)
         (physicalEndpoint channel 0F) SoupTerm.* SoupTerm.* i (groupOf B₁ i)
... | left , right , entryEq =
  0F , left , right ,
  ( ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma (i ↑ˡ sum B₂)
  ■ ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)))
      (proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))) i
  ■ entryEq
  )
bindEnv-entry B₁ B₂ channel sigma local | inr i
  with UB-entry-shape B₂ (physicalEndpoint channel 1F)
         (physicalEndpoint channel 1F) SoupTerm.* SoupTerm.* i (groupOf B₂ i)
... | left , right , entryEq =
  1F , left , right ,
  ( ++ₛ-lookupˡ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*))
       Translation.++ₛ
       proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*)))
      sigma (sum B₁ ↑ʳ i)
  ■ ++ₛ-lookupʳ
      (proj₁ (Translation.UB[ B₁ ] (physicalEndpoint channel 0F)
        (SoupTerm.* , physicalEndpoint channel 0F , SoupTerm.*)))
      (proj₁ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
        (SoupTerm.* , physicalEndpoint channel 1F , SoupTerm.*))) i
  ■ entryEq
  )

pairBound₁-endpoint :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₁} {i : 𝔽 (pairChannels c)} →
  (found : Bound₁ c x i) (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) →
  Σ[ side ∈ 𝔽 2 ] Σ[ left ∈ SoupTerm.Tm (2 *ℕ p) ]
  Σ[ right ∈ SoupTerm.Tm (2 *ℕ p) ]
    pairFocusEnv₁ c e₁ e₂ channels sigma x ≡
    Translation.chanTriple
      ( left
      , physicalEndpoint (lookup channels (pairBoundChannel₁ found e₁ e₂)) side
      , right
      )
pairBound₁-endpoint
  (bound₁-par {c₁ = c₁} {c₂ = c₂} found) e₁ e₂ channels sigma
  with bound-endpoint found e₁
    (V.take (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-take
      (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels
      (boundChannel found e₁)))
pairBound₁-endpoint
  (bound₁-parˢ {c₁ = c₁} {c₂ = c₂} found) e₁ e₂ channels sigma
  with bound-endpoint found e₁
    (V.drop (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-drop
      (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels
      (boundChannel found e₁)))
pairBound₁-endpoint
  (bound₁-left {c = c} {Q = Q} found) e₁ e₂ channels sigma
  with pairBound₁-endpoint found e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels (pairBoundChannel₁ found e₁ e₂)))
pairBound₁-endpoint
  (bound₁-right {c = c} {Q = Q} found) e₁ e₂ channels sigma
  with pairBound₁-endpoint found e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-drop (Translation.channelCount Q) channels
      (pairBoundChannel₁ found e₁ e₂)))
pairBound₁-endpoint {n = n} {c = bind₂ B₁ B₂ c}
  (bound₁-here local localEq) e₁ e₂ (channel ∷ channels) sigma
  with bindEnv-entry B₁ B₂ channel sigma local
... | side , left , right , entryEq =
  side , left , right ,
  ( cong (pairFocusEnv₁ c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma))
      (sym localEq)
  ■ pairFocusEnv₁-ambient c e₁ e₂ channels
      (bindEnv B₁ B₂ channel sigma) (local ↑ˡ n)
  ■ entryEq
  )
pairBound₁-endpoint {c = bind₂ B₁ B₂ c}
  (bound₁-under found) e₁ e₂ (channel ∷ channels) sigma =
  pairBound₁-endpoint found e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

pairBound₂-endpoint :
  {c : ProcessContext₂ k₁ k₂ n} {x : 𝔽 k₂} {i : 𝔽 (pairChannels c)} →
  (found : Bound₂ c x i) (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
  (sigma : Translation.Env n (2 *ℕ p)) →
  Σ[ side ∈ 𝔽 2 ] Σ[ left ∈ SoupTerm.Tm (2 *ℕ p) ]
  Σ[ right ∈ SoupTerm.Tm (2 *ℕ p) ]
    pairFocusEnv₂ c e₁ e₂ channels sigma x ≡
    Translation.chanTriple
      ( left
      , physicalEndpoint (lookup channels (pairBoundChannel₂ found e₁ e₂)) side
      , right
      )
pairBound₂-endpoint
  (bound₂-par {c₁ = c₁} {c₂ = c₂} found) e₁ e₂ channels sigma
  with bound-endpoint found e₂
    (V.drop (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-drop
      (Translation.channelCount (plug c₁ Typed.⟪ e₁ ⟫)) channels
      (boundChannel found e₂)))
pairBound₂-endpoint
  (bound₂-parˢ {c₁ = c₁} {c₂ = c₂} found) e₁ e₂ channels sigma
  with bound-endpoint found e₂
    (V.take (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-take
      (Translation.channelCount (plug c₂ Typed.⟪ e₂ ⟫)) channels
      (boundChannel found e₂)))
pairBound₂-endpoint
  (bound₂-left {c = c} {Q = Q} found) e₁ e₂ channels sigma
  with pairBound₂-endpoint found e₁ e₂
    (V.take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels)
    sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-take
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
      channels (pairBoundChannel₂ found e₁ e₂)))
pairBound₂-endpoint
  (bound₂-right {c = c} {Q = Q} found) e₁ e₂ channels sigma
  with pairBound₂-endpoint found e₁ e₂
    (V.drop (Translation.channelCount Q) channels) sigma
... | side , left , right , eq =
  side , left , right ,
  (eq ■ cong
    (λ channel → Translation.chanTriple
      (left , physicalEndpoint channel side , right))
    (lookup-drop (Translation.channelCount Q) channels
      (pairBoundChannel₂ found e₁ e₂)))
pairBound₂-endpoint {n = n} {c = bind₂ B₁ B₂ c}
  (bound₂-here local localEq) e₁ e₂ (channel ∷ channels) sigma
  with bindEnv-entry B₁ B₂ channel sigma local
... | side , left , right , entryEq =
  side , left , right ,
  ( cong (pairFocusEnv₂ c e₁ e₂ channels (bindEnv B₁ B₂ channel sigma))
      (sym localEq)
  ■ pairFocusEnv₂-ambient c e₁ e₂ channels
      (bindEnv B₁ B₂ channel sigma) (local ↑ˡ n)
  ■ entryEq
  )
pairBound₂-endpoint {c = bind₂ B₁ B₂ c}
  (bound₂-under found) e₁ e₂ (channel ∷ channels) sigma =
  pairBound₂-endpoint found e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

resolveBound₁ :
  (c : ProcessContext₂ k₁ k₂ n) (x : 𝔽 k₁) →
  (Σ[ i ∈ 𝔽 (pairChannels c) ] Bound₁ c x i) ⊎
  (Σ[ y ∈ 𝔽 n ] wt₁ c y ≡ x)
resolveBound₁ (par₂ c₁ c₂) x with resolveBound c₁ x
... | inj₁ (i , found) = inj₁ (i ↑ˡ contextChannels c₂ , bound₁-par found)
... | inj₂ ambient = inj₂ ambient
resolveBound₁ (par₂ˢ c₂ c₁) x with resolveBound c₁ x
... | inj₁ (i , found) = inj₁ (contextChannels c₂ ↑ʳ i , bound₁-parˢ found)
... | inj₂ ambient = inj₂ ambient
resolveBound₁ (left₂ c Q) x with resolveBound₁ c x
... | inj₁ (i , found) = inj₁ (i ↑ˡ Translation.channelCount Q , bound₁-left found)
... | inj₂ ambient = inj₂ ambient
resolveBound₁ (right₂ Q c) x with resolveBound₁ c x
... | inj₁ (i , found) = inj₁ (Translation.channelCount Q ↑ʳ i , bound₁-right found)
... | inj₂ ambient = inj₂ ambient
resolveBound₁ (bind₂ B₁ B₂ c) x with resolveBound₁ c x
... | inj₁ (i , found) = inj₁ (suc i , bound₁-under found)
... | inj₂ (y , eq) with Fin.splitAt (sum B₁ + sum B₂) y in splitEq
...   | inj₁ local =
  inj₁
    ( 0F
    , bound₁-here local
        (cong (wt₁ c) (splitAt-inj₁ (sum B₁ + sum B₂) splitEq)
         ■ eq)
    )
...   | inj₂ outer =
  inj₂ (outer ,
    (cong (wt₁ c)
      (splitAt-inj₂ (sum B₁ + sum B₂) splitEq) ■ eq))

resolveBound₂ :
  (c : ProcessContext₂ k₁ k₂ n) (x : 𝔽 k₂) →
  (Σ[ i ∈ 𝔽 (pairChannels c) ] Bound₂ c x i) ⊎
  (Σ[ y ∈ 𝔽 n ] wt₂ c y ≡ x)
resolveBound₂ (par₂ c₁ c₂) x with resolveBound c₂ x
... | inj₁ (i , found) = inj₁ (contextChannels c₁ ↑ʳ i , bound₂-par found)
... | inj₂ ambient = inj₂ ambient
resolveBound₂ (par₂ˢ c₂ c₁) x with resolveBound c₂ x
... | inj₁ (i , found) = inj₁ (i ↑ˡ contextChannels c₁ , bound₂-parˢ found)
... | inj₂ ambient = inj₂ ambient
resolveBound₂ (left₂ c Q) x with resolveBound₂ c x
... | inj₁ (i , found) = inj₁ (i ↑ˡ Translation.channelCount Q , bound₂-left found)
... | inj₂ ambient = inj₂ ambient
resolveBound₂ (right₂ Q c) x with resolveBound₂ c x
... | inj₁ (i , found) = inj₁ (Translation.channelCount Q ↑ʳ i , bound₂-right found)
... | inj₂ ambient = inj₂ ambient
resolveBound₂ (bind₂ B₁ B₂ c) x with resolveBound₂ c x
... | inj₁ (i , found) = inj₁ (suc i , bound₂-under found)
... | inj₂ (y , eq) with Fin.splitAt (sum B₁ + sum B₂) y in splitEq
...   | inj₁ local =
  inj₁
    ( 0F
    , bound₂-here local
        (cong (wt₂ c) (splitAt-inj₁ (sum B₁ + sum B₂) splitEq)
         ■ eq)
    )
...   | inj₂ outer =
  inj₂ (outer ,
    (cong (wt₂ c)
      (splitAt-inj₂ (sum B₁ + sum B₂) splitEq) ■ eq))

------------------------------------------------------------------------
-- Equal flattened channel positions identify one common restriction.

private
  lift-left :
    {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
    (Q : Typed.Proc n) → Binder₂ c x₁ x₂ → Binder₂ (left₂ c Q) x₁ x₂
  lift-left Q (binder₂ C₁ C₂ above below dec l₁ l₂ eq₁ eq₂) =
    binder₂ C₁ C₂ (par-left above Q) below
      (cong (λ z → left₂ z Q) dec) l₁ l₂ eq₁ eq₂

  lift-right :
    {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
    (Q : Typed.Proc n) → Binder₂ c x₁ x₂ → Binder₂ (right₂ Q c) x₁ x₂
  lift-right Q (binder₂ C₁ C₂ above below dec l₁ l₂ eq₁ eq₂) =
    binder₂ C₁ C₂ (par-right Q above) below
      (cong (right₂ Q) dec) l₁ l₂ eq₁ eq₂

  lift-bind :
    {c : ProcessContext₂ k₁ k₂ (sum B₁ + sum B₂ + n)}
    {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂} →
    Binder₂ c x₁ x₂ → Binder₂ (bind₂ B₁ B₂ c) x₁ x₂
  lift-bind {B₁ = B₁} {B₂ = B₂}
    (binder₂ C₁ C₂ above below dec l₁ l₂ eq₁ eq₂) =
    binder₂ C₁ C₂ (bind B₁ B₂ above) below
      (cong (bind₂ B₁ B₂) dec) l₁ l₂ eq₁ eq₂

bound-common :
  {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
  {i₁ i₂ : 𝔽 (pairChannels c)} →
  Bound₁ c x₁ i₁ → Bound₂ c x₂ i₂ → i₁ ≡ i₂ → Binder₂ c x₁ x₂
bound-common (bound₁-par b₁) (bound₂-par b₂) eq =
  ⊥-elim (Fin.↑ˡ≢↑ʳ eq)
bound-common (bound₁-parˢ b₁) (bound₂-parˢ b₂) eq =
  ⊥-elim (Fin.↑ˡ≢↑ʳ (sym eq))
bound-common (bound₁-left b₁) (bound₂-left b₂) eq =
  lift-left _
    (bound-common b₁ b₂
      (Fin.↑ˡ-injective _ _ _ eq))
bound-common (bound₁-right b₁) (bound₂-right b₂) eq =
  lift-right _
    (bound-common b₁ b₂
      (Fin.↑ʳ-injective _ _ _ eq))
bound-common (bound₁-here l₁ eq₁) (bound₂-here l₂ eq₂) refl =
  binder₂ _ _ hole _ refl l₁ l₂ eq₁ eq₂
bound-common (bound₁-here l₁ eq₁) (bound₂-under b₂) ()
bound-common (bound₁-under b₁) (bound₂-here l₂ eq₂) ()
bound-common (bound₁-under b₁) (bound₂-under b₂) eq =
  lift-bind (bound-common b₁ b₂ (Fin.suc-injective eq))

private
  bound-common-entry-equal :
    {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
    {i₁ i₂ : 𝔽 (pairChannels c)}
    (found₁ : Bound₁ c x₁ i₁) (found₂ : Bound₂ c x₂ i₂)
    (same : i₁ ≡ i₂)
    (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
    (channels : Vec (OrientedChannel p)
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
    (sigma : Translation.Env n (2 *ℕ p)) →
    Binder₂.local₁ (bound-common found₁ found₂ same) ≡
    Binder₂.local₂ (bound-common found₁ found₂ same) →
    pairFocusEnv₁ c e₁ e₂ channels sigma x₁ ≡
    pairFocusEnv₂ c e₁ e₂ channels sigma x₂
  bound-common-entry-equal (bound₁-par b₁) (bound₂-par b₂) same
    e₁ e₂ channels sigma localEq = ⊥-elim (Fin.↑ˡ≢↑ʳ same)
  bound-common-entry-equal (bound₁-parˢ b₁) (bound₂-parˢ b₂) same
    e₁ e₂ channels sigma localEq = ⊥-elim (Fin.↑ˡ≢↑ʳ (sym same))
  bound-common-entry-equal
    (bound₁-left {c = c} {Q = Q} b₁) (bound₂-left b₂) same
    e₁ e₂ channels sigma localEq =
    bound-common-entry-equal b₁ b₂
      (Fin.↑ˡ-injective _ _ _ same) e₁ e₂
      (V.take
        (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
        channels)
      sigma localEq
  bound-common-entry-equal
    (bound₁-right {Q = Q} b₁) (bound₂-right b₂) same
    e₁ e₂ channels sigma localEq =
    bound-common-entry-equal b₁ b₂
      (Fin.↑ʳ-injective _ _ _ same) e₁ e₂
      (V.drop (Translation.channelCount Q) channels) sigma localEq
  bound-common-entry-equal {n = n}
    (bound₁-here {B₁ = B₁} {B₂ = B₂} {c = c} l₁ eq₁)
    (bound₂-here l₂ eq₂) refl e₁ e₂ (channel ∷ channels) sigma localEq =
    cong (pairFocusEnv₁ c e₁ e₂ channels
      (bindEnv B₁ B₂ channel sigma)) (sym eq₁)
    ■ pairFocusEnv₁-ambient c e₁ e₂ channels
        (bindEnv B₁ B₂ channel sigma) (l₁ ↑ˡ n)
    ■ cong (bindEnv B₁ B₂ channel sigma) (cong (_↑ˡ n) localEq)
    ■ sym (pairFocusEnv₂-ambient c e₁ e₂ channels
        (bindEnv B₁ B₂ channel sigma) (l₂ ↑ˡ n))
    ■ cong (pairFocusEnv₂ c e₁ e₂ channels
        (bindEnv B₁ B₂ channel sigma)) eq₂
  bound-common-entry-equal (bound₁-here l₁ eq₁) (bound₂-under b₂) ()
    e₁ e₂ channels sigma localEq
  bound-common-entry-equal (bound₁-under b₁) (bound₂-here l₂ eq₂) ()
    e₁ e₂ channels sigma localEq
  bound-common-entry-equal
    (bound₁-under {B₁ = B₁} {B₂ = B₂} b₁) (bound₂-under b₂) same
    e₁ e₂ (channel ∷ channels) sigma localEq =
    bound-common-entry-equal b₁ b₂ (Fin.suc-injective same) e₁ e₂
      channels (bindEnv B₁ B₂ channel sigma) localEq

  bound-common-channel-content :
    {c : ProcessContext₂ k₁ k₂ n} {x₁ : 𝔽 k₁} {x₂ : 𝔽 k₂}
    {i₁ i₂ : 𝔽 (pairChannels c)}
    (found₁ : Bound₁ c x₁ i₁) (found₂ : Bound₂ c x₂ i₂)
    (same : i₁ ≡ i₂)
    (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
    (channels : Vec (OrientedChannel p)
      (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)))
    (sigma : Translation.Env n (2 *ℕ p)) →
    lookup
      (proj₁ (flattenOriented
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma))
      (pairBoundChannel₁ found₁ e₁ e₂) ≡
    bindChannel
      (Binder₂.C₁ (bound-common found₁ found₂ same))
      (Binder₂.C₂ (bound-common found₁ found₂ same))
      (lookup channels (pairBoundChannel₁ found₁ e₁ e₂))
  bound-common-channel-content (bound₁-par b₁) (bound₂-par b₂) same
    e₁ e₂ channels sigma = ⊥-elim (Fin.↑ˡ≢↑ʳ same)
  bound-common-channel-content (bound₁-parˢ b₁) (bound₂-parˢ b₂) same
    e₁ e₂ channels sigma = ⊥-elim (Fin.↑ˡ≢↑ʳ (sym same))
  bound-common-channel-content
    (bound₁-left {c = c} {Q = Q} b₁) (bound₂-left b₂) same
    e₁ e₂ channels sigma =
    cong
      (λ channels′ → lookup channels′
        (pairBoundChannel₁ b₁ e₁ e₂ ↑ˡ Translation.channelCount Q))
      (flatten-par-channels
        (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) Q channels sigma)
    ■ V.lookup-++ˡ
        (proj₁ (flattenOriented
          (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
          (V.take
            (Translation.channelCount
              (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
            channels)
          sigma))
        (proj₁ (flattenOriented Q
          (V.drop
            (Translation.channelCount
              (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
            channels)
          sigma))
        (pairBoundChannel₁ b₁ e₁ e₂)
    ■ bound-common-channel-content b₁ b₂
        (Fin.↑ˡ-injective _ _ _ same) e₁ e₂
        (V.take
          (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels)
        sigma
    ■ cong
        (bindChannel
          (Binder₂.C₁
            (bound-common b₁ b₂ (Fin.↑ˡ-injective _ _ _ same)))
          (Binder₂.C₂
            (bound-common b₁ b₂ (Fin.↑ˡ-injective _ _ _ same))))
        (lookup-take
          (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))
          channels (pairBoundChannel₁ b₁ e₁ e₂))
  bound-common-channel-content
    (bound₁-right {c = c} {Q = Q} b₁) (bound₂-right b₂) same
    e₁ e₂ channels sigma =
    cong
      (λ channels′ → lookup channels′
        (Translation.channelCount Q ↑ʳ pairBoundChannel₁ b₁ e₁ e₂))
      (flatten-par-channels
        Q (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫) channels sigma)
    ■ V.lookup-++ʳ
        (proj₁ (flattenOriented Q
          (V.take (Translation.channelCount Q) channels)
          sigma))
        (proj₁ (flattenOriented
          (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
          (V.drop (Translation.channelCount Q) channels)
          sigma))
        (pairBoundChannel₁ b₁ e₁ e₂)
    ■ bound-common-channel-content b₁ b₂
        (Fin.↑ʳ-injective _ _ _ same) e₁ e₂
        (V.drop (Translation.channelCount Q) channels) sigma
    ■ cong
        (bindChannel
          (Binder₂.C₁
            (bound-common b₁ b₂ (Fin.↑ʳ-injective _ _ _ same)))
          (Binder₂.C₂
            (bound-common b₁ b₂ (Fin.↑ʳ-injective _ _ _ same))))
        (lookup-drop (Translation.channelCount Q) channels
          (pairBoundChannel₁ b₁ e₁ e₂))
  bound-common-channel-content
    (bound₁-here {B₁ = B₁} {B₂ = B₂} {c = c} l₁ eq₁)
    (bound₂-here l₂ eq₂) refl e₁ e₂ (channel ∷ channels) sigma =
    flatten-bind-channel
      {B₁ = B₁} {B₂ = B₂}
      {P = plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫}
      {channel = channel} {logicalChannels = channels} {sigma = sigma}
  bound-common-channel-content
    (bound₁-here l₁ eq₁) (bound₂-under b₂) ()
    e₁ e₂ channels sigma
  bound-common-channel-content
    (bound₁-under b₁) (bound₂-here l₂ eq₂) ()
    e₁ e₂ channels sigma
  bound-common-channel-content
    (bound₁-under {B₁ = B₁} {B₂ = B₂} {c = c} b₁)
    (bound₂-under b₂) same
    e₁ e₂ (channel ∷ channels) sigma =
    flatten-bind-channel-suc
      {B₁ = B₁} {B₂ = B₂}
      {P = plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫}
      {channel = channel} {logicalChannels = channels} {sigma = sigma}
      (pairBoundChannel₁ b₁ e₁ e₂)
    ■ bound-common-channel-content b₁ b₂ (Fin.suc-injective same)
        e₁ e₂ channels (bindEnv B₁ B₂ channel sigma)

resolveBound₁-closed :
  (c : ProcessContext₂ k₁ k₂ 0) (x : 𝔽 k₁) →
  Σ[ i ∈ 𝔽 (pairChannels c) ] Bound₁ c x i
resolveBound₁-closed c x with resolveBound₁ c x
... | inj₁ found = found
... | inj₂ (() , _)

resolveBound₂-closed :
  (c : ProcessContext₂ k₁ k₂ 0) (x : 𝔽 k₂) →
  Σ[ i ∈ 𝔽 (pairChannels c) ] Bound₂ c x i
resolveBound₂-closed c x with resolveBound₂ c x
... | inj₁ found = found
... | inj₂ (() , _)

same-position⇒binder₂ :
  (c : ProcessContext₂ k₁ k₂ 0) (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂) →
  proj₁ (resolveBound₁-closed c x₁) ≡
  proj₁ (resolveBound₂-closed c x₂) →
  Binder₂ c x₁ x₂
same-position⇒binder₂ c x₁ x₂ same =
  bound-common
    (proj₂ (resolveBound₁-closed c x₁))
    (proj₂ (resolveBound₂-closed c x₂)) same

same-physical-channel⇒binder₂ :
  (c : ProcessContext₂ k₁ k₂ 0)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))) →
  (∀ {i j} →
    physicalChannel (lookup channels i) ≡
    physicalChannel (lookup channels j) → i ≡ j) →
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂)
  {physical : 𝔽 p} {side₁ side₂ : 𝔽 2}
  {left₁ right₁ left₂ right₂ : SoupTerm.Tm (2 *ℕ p)} →
  pairFocusEnv₁ c e₁ e₂ channels (λ ()) x₁ ≡
    Translation.chanTriple
      (left₁ , Soup.endpoint physical side₁ , right₁) →
  pairFocusEnv₂ c e₁ e₂ channels (λ ()) x₂ ≡
    Translation.chanTriple
      (left₂ , Soup.endpoint physical side₂ , right₂) →
  Binder₂ c x₁ x₂
same-physical-channel⇒binder₂ c e₁ e₂ channels channel-injective x₁ x₂
  entry₁ entry₂
  with resolveBound₁-closed c x₁ | resolveBound₂-closed c x₂
... | i₁ , found₁ | i₂ , found₂
  with pairBound₁-endpoint found₁ e₁ e₂ channels (λ ())
     | pairBound₂-endpoint found₂ e₁ e₂ channels (λ ())
... | canonicalSide₁ , canonicalLeft₁ , canonicalRight₁ , canonical₁
    | canonicalSide₂ , canonicalLeft₂ , canonicalRight₂ , canonical₂ =
  bound-common found₁ found₂
    (pairBoundChannels-equal⇒indices-equal found₁ found₂ e₁ e₂
      (channel-injective
        ( physicalEq₁ ■ sym physicalEq₂ )))
  where
  endpointEq₁ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₁ ■ entry₁)))

  endpointEq₂ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₂ ■ entry₂)))

  physicalEq₁ = proj₁ (endpoint-injective endpointEq₁)
  physicalEq₂ = proj₁ (endpoint-injective endpointEq₂)

same-physical-channel⇒binder₂-apart :
  (c : ProcessContext₂ k₁ k₂ 0)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))) →
  (∀ {i j} →
    physicalChannel (lookup channels i) ≡
    physicalChannel (lookup channels j) → i ≡ j) →
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂)
  {physical : 𝔽 p} {side₁ side₂ : 𝔽 2}
  {left₁ right₁ left₂ right₂ : SoupTerm.Tm (2 *ℕ p)} →
  side₁ ≢ side₂ →
  pairFocusEnv₁ c e₁ e₂ channels (λ ()) x₁ ≡
    Translation.chanTriple
      (left₁ , Soup.endpoint physical side₁ , right₁) →
  pairFocusEnv₂ c e₁ e₂ channels (λ ()) x₂ ≡
    Translation.chanTriple
      (left₂ , Soup.endpoint physical side₂ , right₂) →
  Σ[ bnd ∈ Binder₂ c x₁ x₂ ]
    Binder₂.local₁ bnd ≢ Binder₂.local₂ bnd
same-physical-channel⇒binder₂-apart {p = p}
  c e₁ e₂ channels channel-injective x₁ x₂ sidesApart entry₁ entry₂
  with resolveBound₁-closed c x₁ | resolveBound₂-closed c x₂
... | i₁ , found₁ | i₂ , found₂
  with pairBound₁-endpoint found₁ e₁ e₂ channels (λ ())
     | pairBound₂-endpoint found₂ e₁ e₂ channels (λ ())
... | canonicalSide₁ , canonicalLeft₁ , canonicalRight₁ , canonical₁
    | canonicalSide₂ , canonicalLeft₂ , canonicalRight₂ , canonical₂ =
  let
    samePosition =
      pairBoundChannels-equal⇒indices-equal found₁ found₂ e₁ e₂
        (channel-injective (physicalEq₁ ■ sym physicalEq₂))
    bnd = bound-common found₁ found₂ samePosition
    apart = λ localEq → sidesApart
      (proj₂ (endpoint-injective {n = p}
        (proj₁ (proj₂ (chanTriple-injective
          (sym entry₁
           ■ bound-common-entry-equal found₁ found₂ samePosition
               e₁ e₂ channels (λ ()) localEq
           ■ entry₂))))))
  in bnd , apart
  where
  endpointEq₁ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₁ ■ entry₁)))

  endpointEq₂ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₂ ■ entry₂)))

  physicalEq₁ = proj₁ (endpoint-injective endpointEq₁)
  physicalEq₂ = proj₁ (endpoint-injective endpointEq₂)

same-physical-channel⇒binder₂-data :
  (c : ProcessContext₂ k₁ k₂ 0)
  (e₁ : Source.Tm k₁) (e₂ : Source.Tm k₂)
  (channels : Vec (OrientedChannel p)
    (Translation.channelCount (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫))) →
  (∀ {i j} →
    physicalChannel (lookup channels i) ≡
    physicalChannel (lookup channels j) → i ≡ j) →
  (x₁ : 𝔽 k₁) (x₂ : 𝔽 k₂)
  {physical : 𝔽 p} {side₁ side₂ : 𝔽 2}
  {left₁ right₁ left₂ right₂ : SoupTerm.Tm (2 *ℕ p)} →
  side₁ ≢ side₂ →
  pairFocusEnv₁ c e₁ e₂ channels (λ ()) x₁ ≡
    Translation.chanTriple
      (left₁ , Soup.endpoint physical side₁ , right₁) →
  pairFocusEnv₂ c e₁ e₂ channels (λ ()) x₂ ≡
    Translation.chanTriple
      (left₂ , Soup.endpoint physical side₂ , right₂) →
  Σ[ bnd ∈ Binder₂ c x₁ x₂ ]
    (Binder₂.local₁ bnd ≢ Binder₂.local₂ bnd) ×
    Σ[ logical ∈ 𝔽 (Translation.channelCount
      (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)) ]
      (physicalChannel (lookup channels logical) ≡ physical) ×
      lookup
        (proj₁ (flattenOriented
          (plug₂ c Typed.⟪ e₁ ⟫ Typed.⟪ e₂ ⟫)
          channels (λ ())))
        logical ≡
      bindChannel (Binder₂.C₁ bnd) (Binder₂.C₂ bnd)
        (lookup channels logical)
same-physical-channel⇒binder₂-data {p = p}
  c e₁ e₂ channels channel-injective x₁ x₂ sidesApart entry₁ entry₂
  with resolveBound₁-closed c x₁ | resolveBound₂-closed c x₂
... | i₁ , found₁ | i₂ , found₂
  with pairBound₁-endpoint found₁ e₁ e₂ channels (λ ())
     | pairBound₂-endpoint found₂ e₁ e₂ channels (λ ())
... | canonicalSide₁ , canonicalLeft₁ , canonicalRight₁ , canonical₁
    | canonicalSide₂ , canonicalLeft₂ , canonicalRight₂ , canonical₂ =
  let
    samePosition =
      pairBoundChannels-equal⇒indices-equal found₁ found₂ e₁ e₂
        (channel-injective (physicalEq₁ ■ sym physicalEq₂))
    bnd = bound-common found₁ found₂ samePosition
    logical = pairBoundChannel₁ found₁ e₁ e₂
    apart = λ localEq → sidesApart
      (proj₂ (endpoint-injective {n = p}
        (proj₁ (proj₂ (chanTriple-injective
          (sym entry₁
           ■ bound-common-entry-equal found₁ found₂ samePosition
               e₁ e₂ channels (λ ()) localEq
           ■ entry₂))))))
    content = bound-common-channel-content found₁ found₂ samePosition
      e₁ e₂ channels (λ ())
  in bnd , apart , logical , physicalEq₁ , content
  where
  endpointEq₁ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₁ ■ entry₁)))

  endpointEq₂ =
    proj₁ (proj₂
      (chanTriple-injective (sym canonical₂ ■ entry₂)))

  physicalEq₁ = proj₁ (endpoint-injective endpointEq₁)
  physicalEq₂ = proj₁ (endpoint-injective endpointEq₂)
