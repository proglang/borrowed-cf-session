module BorrowedCF.Simulation.ForwardSoup.Context where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation

open Nat.Variables

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
