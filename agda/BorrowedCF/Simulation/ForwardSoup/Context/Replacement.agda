module BorrowedCF.Simulation.ForwardSoup.Context.Replacement where

open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation

open import BorrowedCF.Simulation.ForwardSoup.Context

open Nat.Variables

data ChannelContextPair (P Q : Typed.Proc k) :
  {n : ℕ} (context : ProcessContext k n) →
  𝔽 (Translation.channelCount (plug context Q)) →
  𝔽 (Translation.channelCount (plug context P)) → Set where

  par-left :
    ∀ {n} {context : ProcessContext k n} {R i j} →
    ChannelContextPair P Q context i j →
    ChannelContextPair P Q (par context R)
      (i ↑ˡ Translation.channelCount R)
      (j ↑ˡ Translation.channelCount R)

  par-right :
    ∀ {n} {context : ProcessContext k n} {R}
      (i : 𝔽 (Translation.channelCount R)) →
    ChannelContextPair P Q (par context R)
      (Translation.channelCount (plug context Q) ↑ʳ i)
      (Translation.channelCount (plug context P) ↑ʳ i)

  bind-head :
    ∀ {n B₁ B₂}
      {context : ProcessContext k (sum B₁ + sum B₂ + n)} →
    ChannelContextPair P Q (bind B₁ B₂ context) zero zero

  bind-tail :
    ∀ {n B₁ B₂}
      {context : ProcessContext k (sum B₁ + sum B₂ + n)}
      {i : 𝔽 (Translation.channelCount (plug context Q))}
      {j : 𝔽 (Translation.channelCount (plug context P))} →
    ChannelContextPair P Q context i j →
    ChannelContextPair P Q (bind B₁ B₂ context) (suc i) (suc j)

data ThreadContextPair (P Q : Typed.Proc k) :
  {n : ℕ} (context : ProcessContext k n) →
  𝔽 (Translation.processCount (plug context Q)) →
  𝔽 (Translation.processCount (plug context P)) → Set where

  par-left :
    ∀ {n} {context : ProcessContext k n} {R i j} →
    ThreadContextPair P Q context i j →
    ThreadContextPair P Q (par context R)
      (i ↑ˡ Translation.processCount R)
      (j ↑ˡ Translation.processCount R)

  par-right :
    ∀ {n} {context : ProcessContext k n} {R}
      (i : 𝔽 (Translation.processCount R)) →
    ThreadContextPair P Q (par context R)
      (Translation.processCount (plug context Q) ↑ʳ i)
      (Translation.processCount (plug context P) ↑ʳ i)

  bind-inner :
    ∀ {n B₁ B₂}
      {context : ProcessContext k (sum B₁ + sum B₂ + n)}
      {i : 𝔽 (Translation.processCount (plug context Q))}
      {j : 𝔽 (Translation.processCount (plug context P))} →
    ThreadContextPair P Q context i j →
    ThreadContextPair P Q (bind B₁ B₂ context) i j

ChannelTargetPosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k) →
  𝔽 (Translation.channelCount (plug context Q)) → Set
ChannelTargetPosition context P Q j =
  (Σ[ i ∈ 𝔽 (Translation.channelCount Q) ]
    channelInContext context Q i ≡ j) ⊎
  (Σ[ l ∈ 𝔽 (Translation.channelCount (plug context P)) ]
    ChannelContextPair P Q context j l)

ThreadTargetPosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k) →
  𝔽 (Translation.processCount (plug context Q)) → Set
ThreadTargetPosition context P Q j =
  (Σ[ i ∈ 𝔽 (Translation.processCount Q) ]
    threadInContext context Q i ≡ j) ⊎
  (Σ[ l ∈ 𝔽 (Translation.processCount (plug context P)) ]
    ThreadContextPair P Q context j l)

ChannelSourcePosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k) →
  𝔽 (Translation.channelCount (plug context P)) → Set
ChannelSourcePosition context P Q j =
  (Σ[ i ∈ 𝔽 (Translation.channelCount P) ]
    channelInContext context P i ≡ j) ⊎
  (Σ[ l ∈ 𝔽 (Translation.channelCount (plug context Q)) ]
    ChannelContextPair P Q context l j)

ThreadSourcePosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k) →
  𝔽 (Translation.processCount (plug context P)) → Set
ThreadSourcePosition context P Q j =
  (Σ[ i ∈ 𝔽 (Translation.processCount P) ]
    threadInContext context P i ≡ j) ⊎
  (Σ[ l ∈ 𝔽 (Translation.processCount (plug context Q)) ]
    ThreadContextPair P Q context l j)

channelTargetPosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k)
  (j : 𝔽 (Translation.channelCount (plug context Q))) →
  ChannelTargetPosition context P Q j
channelTargetPosition hole P Q j = inj₁ (j , refl)
channelTargetPosition (par context R) P Q j
  with Fin.splitAt (Translation.channelCount (plug context Q)) j in split
... | inj₁ l = lift (channelTargetPosition context P Q l)
  where
  equal : l ↑ˡ Translation.channelCount R ≡ j
  equal =
    sym (cong (Fin.join (Translation.channelCount (plug context Q))
      (Translation.channelCount R)) split) ■
    Fin.join-splitAt (Translation.channelCount (plug context Q))
      (Translation.channelCount R) j

  lift : ChannelTargetPosition context P Q l →
    ChannelTargetPosition (par context R) P Q j
  lift (inj₁ (i , inside)) = inj₁
    (i , (cong (λ z → z ↑ˡ Translation.channelCount R) inside ■ equal))
  lift (inj₂ (s , paired)) = inj₂
    (s ↑ˡ Translation.channelCount R ,
     subst (λ z → ChannelContextPair P Q (par context R) z
       (s ↑ˡ Translation.channelCount R)) equal (par-left paired))
... | inj₂ r = inj₂
  (Translation.channelCount (plug context P) ↑ʳ r ,
   subst (λ z → ChannelContextPair P Q (par context R) z
     (Translation.channelCount (plug context P) ↑ʳ r)) equal
     (par-right r))
  where
  equal : Translation.channelCount (plug context Q) ↑ʳ r ≡ j
  equal =
    sym (cong (Fin.join (Translation.channelCount (plug context Q))
      (Translation.channelCount R)) split) ■
    Fin.join-splitAt (Translation.channelCount (plug context Q))
      (Translation.channelCount R) j
channelTargetPosition (bind B₁ B₂ context) P Q zero =
  inj₂ (zero , bind-head)
channelTargetPosition (bind B₁ B₂ context) P Q (suc j)
  with channelTargetPosition context P Q j
... | inj₁ (i , inside) = inj₁ (i , cong suc inside)
... | inj₂ (l , paired) = inj₂ (suc l , bind-tail paired)

threadTargetPosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k)
  (j : 𝔽 (Translation.processCount (plug context Q))) →
  ThreadTargetPosition context P Q j
threadTargetPosition hole P Q j = inj₁ (j , refl)
threadTargetPosition (par context R) P Q j
  with Fin.splitAt (Translation.processCount (plug context Q)) j in split
... | inj₁ l = lift (threadTargetPosition context P Q l)
  where
  equal : l ↑ˡ Translation.processCount R ≡ j
  equal =
    sym (cong (Fin.join (Translation.processCount (plug context Q))
      (Translation.processCount R)) split) ■
    Fin.join-splitAt (Translation.processCount (plug context Q))
      (Translation.processCount R) j

  lift : ThreadTargetPosition context P Q l →
    ThreadTargetPosition (par context R) P Q j
  lift (inj₁ (i , inside)) = inj₁
    (i , (cong (λ z → z ↑ˡ Translation.processCount R) inside ■ equal))
  lift (inj₂ (s , paired)) = inj₂
    (s ↑ˡ Translation.processCount R ,
     subst (λ z → ThreadContextPair P Q (par context R) z
       (s ↑ˡ Translation.processCount R)) equal (par-left paired))
... | inj₂ r = inj₂
  (Translation.processCount (plug context P) ↑ʳ r ,
   subst (λ z → ThreadContextPair P Q (par context R) z
     (Translation.processCount (plug context P) ↑ʳ r)) equal
     (par-right r))
  where
  equal : Translation.processCount (plug context Q) ↑ʳ r ≡ j
  equal =
    sym (cong (Fin.join (Translation.processCount (plug context Q))
      (Translation.processCount R)) split) ■
    Fin.join-splitAt (Translation.processCount (plug context Q))
      (Translation.processCount R) j
threadTargetPosition (bind B₁ B₂ context) P Q j
  with threadTargetPosition context P Q j
... | inj₁ inside = inj₁ inside
... | inj₂ (l , paired) = inj₂ (l , bind-inner paired)

channelSourcePosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k)
  (j : 𝔽 (Translation.channelCount (plug context P))) →
  ChannelSourcePosition context P Q j
channelSourcePosition hole P Q j = inj₁ (j , refl)
channelSourcePosition (par context R) P Q j
  with Fin.splitAt (Translation.channelCount (plug context P)) j in split
... | inj₁ l = lift (channelSourcePosition context P Q l)
  where
  equal : l ↑ˡ Translation.channelCount R ≡ j
  equal =
    sym (cong (Fin.join (Translation.channelCount (plug context P))
      (Translation.channelCount R)) split) ■
    Fin.join-splitAt (Translation.channelCount (plug context P))
      (Translation.channelCount R) j

  lift : ChannelSourcePosition context P Q l →
    ChannelSourcePosition (par context R) P Q j
  lift (inj₁ (i , inside)) = inj₁
    (i , (cong (λ z → z ↑ˡ Translation.channelCount R) inside ■ equal))
  lift (inj₂ (s , paired)) = inj₂
    (s ↑ˡ Translation.channelCount R ,
     subst (λ z → ChannelContextPair P Q (par context R)
       (s ↑ˡ Translation.channelCount R) z) equal (par-left paired))
... | inj₂ r = inj₂
  (Translation.channelCount (plug context Q) ↑ʳ r ,
   subst (ChannelContextPair P Q (par context R)
     (Translation.channelCount (plug context Q) ↑ʳ r)) equal
     (par-right r))
  where
  equal : Translation.channelCount (plug context P) ↑ʳ r ≡ j
  equal =
    sym (cong (Fin.join (Translation.channelCount (plug context P))
      (Translation.channelCount R)) split) ■
    Fin.join-splitAt (Translation.channelCount (plug context P))
      (Translation.channelCount R) j
channelSourcePosition (bind B₁ B₂ context) P Q zero =
  inj₂ (zero , bind-head)
channelSourcePosition (bind B₁ B₂ context) P Q (suc j)
  with channelSourcePosition context P Q j
... | inj₁ (i , inside) = inj₁ (i , cong suc inside)
... | inj₂ (l , paired) = inj₂ (suc l , bind-tail paired)

threadSourcePosition :
  (context : ProcessContext k n) (P Q : Typed.Proc k)
  (j : 𝔽 (Translation.processCount (plug context P))) →
  ThreadSourcePosition context P Q j
threadSourcePosition hole P Q j = inj₁ (j , refl)
threadSourcePosition (par context R) P Q j
  with Fin.splitAt (Translation.processCount (plug context P)) j in split
... | inj₁ l = lift (threadSourcePosition context P Q l)
  where
  equal : l ↑ˡ Translation.processCount R ≡ j
  equal =
    sym (cong (Fin.join (Translation.processCount (plug context P))
      (Translation.processCount R)) split) ■
    Fin.join-splitAt (Translation.processCount (plug context P))
      (Translation.processCount R) j

  lift : ThreadSourcePosition context P Q l →
    ThreadSourcePosition (par context R) P Q j
  lift (inj₁ (i , inside)) = inj₁
    (i , (cong (λ z → z ↑ˡ Translation.processCount R) inside ■ equal))
  lift (inj₂ (s , paired)) = inj₂
    (s ↑ˡ Translation.processCount R ,
     subst (λ z → ThreadContextPair P Q (par context R)
       (s ↑ˡ Translation.processCount R) z) equal (par-left paired))
... | inj₂ r = inj₂
  (Translation.processCount (plug context Q) ↑ʳ r ,
   subst (ThreadContextPair P Q (par context R)
     (Translation.processCount (plug context Q) ↑ʳ r)) equal
     (par-right r))
  where
  equal : Translation.processCount (plug context P) ↑ʳ r ≡ j
  equal =
    sym (cong (Fin.join (Translation.processCount (plug context P))
      (Translation.processCount R)) split) ■
    Fin.join-splitAt (Translation.processCount (plug context P))
      (Translation.processCount R) j
threadSourcePosition (bind B₁ B₂ context) P Q j
  with threadSourcePosition context P Q j
... | inj₁ inside = inj₁ inside
... | inj₂ (l , paired) = inj₂ (l , bind-inner paired)

channelPair-source-outside :
  {context : ProcessContext k n} {P Q : Typed.Proc k}
  {i : 𝔽 (Translation.channelCount (plug context Q))}
  {j : 𝔽 (Translation.channelCount (plug context P))} →
  ChannelContextPair P Q context i j →
  (l : 𝔽 (Translation.channelCount P)) →
  channelInContext context P l ≢ j
channelPair-source-outside (par-left paired) l equal =
  channelPair-source-outside paired l
    (Fin.↑ˡ-injective _ _ _ equal)
channelPair-source-outside (par-right i) l equal =
  Fin.↑ˡ≢↑ʳ equal
channelPair-source-outside bind-head l ()
channelPair-source-outside (bind-tail paired) l equal =
  channelPair-source-outside paired l (Fin.suc-injective equal)

channelPair-target-outside :
  {context : ProcessContext k n} {P Q : Typed.Proc k}
  {i : 𝔽 (Translation.channelCount (plug context Q))}
  {j : 𝔽 (Translation.channelCount (plug context P))} →
  ChannelContextPair P Q context i j →
  (l : 𝔽 (Translation.channelCount Q)) →
  channelInContext context Q l ≢ i
channelPair-target-outside (par-left paired) l equal =
  channelPair-target-outside paired l
    (Fin.↑ˡ-injective _ _ _ equal)
channelPair-target-outside (par-right i) l equal =
  Fin.↑ˡ≢↑ʳ equal
channelPair-target-outside bind-head l ()
channelPair-target-outside (bind-tail paired) l equal =
  channelPair-target-outside paired l (Fin.suc-injective equal)

threadPair-source-outside :
  {context : ProcessContext k n} {P Q : Typed.Proc k}
  {i : 𝔽 (Translation.processCount (plug context Q))}
  {j : 𝔽 (Translation.processCount (plug context P))} →
  ThreadContextPair P Q context i j →
  (l : 𝔽 (Translation.processCount P)) →
  threadInContext context P l ≢ j
threadPair-source-outside (par-left paired) l equal =
  threadPair-source-outside paired l
    (Fin.↑ˡ-injective _ _ _ equal)
threadPair-source-outside (par-right i) l equal =
  Fin.↑ˡ≢↑ʳ equal
threadPair-source-outside (bind-inner paired) l equal =
  threadPair-source-outside paired l equal

threadPair-target-outside :
  {context : ProcessContext k n} {P Q : Typed.Proc k}
  {i : 𝔽 (Translation.processCount (plug context Q))}
  {j : 𝔽 (Translation.processCount (plug context P))} →
  ThreadContextPair P Q context i j →
  (l : 𝔽 (Translation.processCount Q)) →
  threadInContext context Q l ≢ i
threadPair-target-outside (par-left paired) l equal =
  threadPair-target-outside paired l
    (Fin.↑ˡ-injective _ _ _ equal)
threadPair-target-outside (par-right i) l equal =
  Fin.↑ˡ≢↑ʳ equal
threadPair-target-outside (bind-inner paired) l equal =
  threadPair-target-outside paired l equal
