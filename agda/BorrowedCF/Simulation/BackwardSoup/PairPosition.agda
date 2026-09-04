-- | Relate the binding positions of the two holes of a paired redex.
module BorrowedCF.Simulation.BackwardSoup.PairPosition where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( ProcessContext; hole; par-left; par-right; bind
        )
open import BorrowedCF.Simulation.BackwardSoup.Position
  using (weakenThrough)
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair
  using ( ProcessContext₂; par₂; par₂ˢ; left₂; right₂; bind₂
        ; compose₂; wt₁; wt₂; Binder₂; binder₂)

open Nat.Variables
open Fin.Patterns

private
  variable
    B₁ B₂ : Typed.BindGroup

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
