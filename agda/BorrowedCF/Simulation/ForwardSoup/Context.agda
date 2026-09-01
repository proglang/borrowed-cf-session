module BorrowedCF.Simulation.ForwardSoup.Context where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation

open Nat.Variables

variable a : ℕ

-- A left process context.  The first index is the arity of the hole and the
-- second index is the arity of the process obtained after plugging it.
data ProcessContext : ℕ → ℕ → Set where
  hole : ProcessContext n n

  par :
    ProcessContext k n →
    Typed.Proc n →
    ProcessContext k n

  bind :
    (B₁ B₂ : Typed.BindGroup) →
    ProcessContext k (sum B₁ + sum B₂ + n) →
    ProcessContext k n

plug : ProcessContext k n → Typed.Proc k → Typed.Proc n
plug hole P = P
plug (par context Q) P = plug context P Typed.∥ Q
plug (bind B₁ B₂ context) P = Typed.ν B₁ B₂ (plug context P)

channelInContext :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.channelCount P) →
  𝔽 (Translation.channelCount (plug context P))
channelInContext hole P i = i
channelInContext (par context Q) P i =
  channelInContext context P i ↑ˡ Translation.channelCount Q
channelInContext (bind B₁ B₂ context) P i =
  suc (channelInContext context P i)

threadInContext :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.processCount P) →
  𝔽 (Translation.processCount (plug context P))
threadInContext hole P i = i
threadInContext (par context Q) P i =
  threadInContext context P i ↑ˡ Translation.processCount Q
threadInContext (bind B₁ B₂ context) P i =
  threadInContext context P i

channelInContext-injective :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  ∀ {i j} →
  channelInContext context P i ≡ channelInContext context P j →
  i ≡ j
channelInContext-injective hole P equal = equal
channelInContext-injective (par context Q) P equal =
  channelInContext-injective context P
    (Fin.↑ˡ-injective (Translation.channelCount Q) _ _ equal)
channelInContext-injective (bind B₁ B₂ context) P equal =
  channelInContext-injective context P (Fin.suc-injective equal)

threadInContext-injective :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  ∀ {i j} →
  threadInContext context P i ≡ threadInContext context P j →
  i ≡ j
threadInContext-injective hole P equal = equal
threadInContext-injective (par context Q) P equal =
  threadInContext-injective context P
    (Fin.↑ˡ-injective (Translation.processCount Q) _ _ equal)
threadInContext-injective (bind B₁ B₂ context) P equal =
  threadInContext-injective context P equal

ChannelHolePosition :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.channelCount (plug context P)) → Set
ChannelHolePosition context P j =
  (Σ[ i ∈ 𝔽 (Translation.channelCount P) ]
    channelInContext context P i ≡ j) ⊎
  ((i : 𝔽 (Translation.channelCount P)) →
    channelInContext context P i ≢ j)

channelHolePosition :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (j : 𝔽 (Translation.channelCount (plug context P))) →
  ChannelHolePosition context P j
channelHolePosition hole P j = inj₁ (j , refl)
channelHolePosition (par context Q) P j
  with Fin.splitAt (Translation.channelCount (plug context P)) j in split
... | inj₁ l = lift-left (channelHolePosition context P l)
  where
  left-equal :
    l ↑ˡ Translation.channelCount Q ≡ j
  left-equal =
    sym (cong
      (Fin.join (Translation.channelCount (plug context P))
        (Translation.channelCount Q)) split) ■
    Fin.join-splitAt
      (Translation.channelCount (plug context P))
      (Translation.channelCount Q) j
  lift-left :
    ChannelHolePosition context P l →
    ChannelHolePosition (par context Q) P j
  lift-left (inj₁ (i , inside)) = inj₁
    (i , (cong (λ x → x ↑ˡ Translation.channelCount Q) inside ■
      left-equal))
  lift-left (inj₂ outside) = inj₂ (λ i equal → outside i
    (Fin.↑ˡ-injective (Translation.channelCount Q) _ _
      (equal ■ sym left-equal)))
... | inj₂ r = inj₂ (λ i equal →
  Fin.↑ˡ≢↑ʳ
    (equal ■ sym right-equal))
  where
  right-equal :
    Translation.channelCount (plug context P) ↑ʳ r ≡ j
  right-equal =
    sym (cong
      (Fin.join (Translation.channelCount (plug context P))
        (Translation.channelCount Q)) split) ■
    Fin.join-splitAt
      (Translation.channelCount (plug context P))
      (Translation.channelCount Q) j
channelHolePosition (bind B₁ B₂ context) P zero =
  inj₂ (λ _ ())
channelHolePosition (bind B₁ B₂ context) P (suc j)
  with channelHolePosition context P j
... | inj₁ (i , inside) = inj₁ (i , cong suc inside)
... | inj₂ outside = inj₂ (λ i equal →
  outside i (Fin.suc-injective equal))

ThreadHolePosition :
  (context : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.processCount (plug context P)) → Set
ThreadHolePosition context P j =
  (Σ[ i ∈ 𝔽 (Translation.processCount P) ]
    threadInContext context P i ≡ j) ⊎
  ((i : 𝔽 (Translation.processCount P)) →
    threadInContext context P i ≢ j)

threadHolePosition :
  (context : ProcessContext k n) (P : Typed.Proc k)
  (j : 𝔽 (Translation.processCount (plug context P))) →
  ThreadHolePosition context P j
threadHolePosition hole P j = inj₁ (j , refl)
threadHolePosition (par context Q) P j
  with Fin.splitAt (Translation.processCount (plug context P)) j in split
... | inj₁ l = lift-left (threadHolePosition context P l)
  where
  left-equal :
    l ↑ˡ Translation.processCount Q ≡ j
  left-equal =
    sym (cong
      (Fin.join (Translation.processCount (plug context P))
        (Translation.processCount Q)) split) ■
    Fin.join-splitAt
      (Translation.processCount (plug context P))
      (Translation.processCount Q) j
  lift-left :
    ThreadHolePosition context P l →
    ThreadHolePosition (par context Q) P j
  lift-left (inj₁ (i , inside)) = inj₁
    (i , (cong (λ x → x ↑ˡ Translation.processCount Q) inside ■
      left-equal))
  lift-left (inj₂ outside) = inj₂ (λ i equal → outside i
    (Fin.↑ˡ-injective (Translation.processCount Q) _ _
      (equal ■ sym left-equal)))
... | inj₂ r = inj₂ (λ i equal →
  Fin.↑ˡ≢↑ʳ
    (equal ■ sym right-equal))
  where
  right-equal :
    Translation.processCount (plug context P) ↑ʳ r ≡ j
  right-equal =
    sym (cong
      (Fin.join (Translation.processCount (plug context P))
        (Translation.processCount Q)) split) ■
    Fin.join-splitAt
      (Translation.processCount (plug context P))
      (Translation.processCount Q) j
threadHolePosition (bind B₁ B₂ context) P j =
  threadHolePosition context P j

channelCount-plug-cong :
  (context : ProcessContext k n) {P Q : Typed.Proc k} →
  Translation.channelCount P ≡ Translation.channelCount Q →
  Translation.channelCount (plug context P) ≡
  Translation.channelCount (plug context Q)
channelCount-plug-cong hole equal = equal
channelCount-plug-cong (par context R) equal =
  cong (_+ Translation.channelCount R)
    (channelCount-plug-cong context equal)
channelCount-plug-cong (bind B₁ B₂ context) equal =
  cong suc (channelCount-plug-cong context equal)

processCount-plug-cong :
  (context : ProcessContext k n) {P Q : Typed.Proc k} →
  Translation.processCount P ≡ Translation.processCount Q →
  Translation.processCount (plug context P) ≡
  Translation.processCount (plug context Q)
processCount-plug-cong hole equal = equal
processCount-plug-cong (par context R) equal =
  cong (_+ Translation.processCount R)
    (processCount-plug-cong context equal)
processCount-plug-cong (bind B₁ B₂ context) equal =
  processCount-plug-cong context equal

compose :
  ProcessContext a n → ProcessContext k a → ProcessContext k n
compose hole inner = inner
compose (par outer Q) inner = par (compose outer inner) Q
compose (bind B₁ B₂ outer) inner = bind B₁ B₂ (compose outer inner)

plug-compose :
  (outer : ProcessContext a n) (inner : ProcessContext k a)
  (P : Typed.Proc k) →
  plug (compose outer inner) P ≡ plug outer (plug inner P)
plug-compose hole inner P = refl
plug-compose (par outer Q) inner P =
  cong (Typed._∥ Q) (plug-compose outer inner P)
plug-compose (bind B₁ B₂ outer) inner P =
  cong (Typed.ν B₁ B₂) (plug-compose outer inner P)
