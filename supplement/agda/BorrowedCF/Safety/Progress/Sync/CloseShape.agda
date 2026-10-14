-- | An `end`-typed head handle forces its binder group to be a singleton and
--   to be the LAST group of its endpoint.
--
--   `R-Close` fires only on `ν [ 1 ] [ 1 ]`, so the main lemma has to turn the
--   general shape `ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)` into that one.  Width one is
--   `Simulation/Support/PairConfine.agda`'s `close-group-width`; the extra bit
--   is `B ≡ []`, i.e. no group may follow.  A following group would make the
--   chain of the first group realise `s₁ ; ret` with `s₁ ; s₂ ≃ s ; end p` and
--   `¬ Skips s₂` (`BindCtx`'s `cons-ret/acq`), while an `end`-headed handle
--   forces `Skips s` (a `New` session has no `end` at the front,
--   `new-¬end`) and hence `s₁ ; s₂ ≃ end p`, which leaves nothing for `s₂`.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.CloseShape where

open import Data.Nat.ListAction using (sum)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Processes.Typed

open import BorrowedCF.Safety.Progress.Sync.Front
open import BorrowedCF.Safety.Progress.Sync.Heads using (bindCtx′-head)

open import BorrowedCF.Simulation.Support.PairConfine using (close-group-width)

open Nat.Variables
open Variables
open Fin.Patterns

private variable
  b : ℕ
  t : 𝕊 0
  q : Pol

-- A `New` session never starts with an `end`.
new-¬end : New s → ¬ ConsK (kend q) s
new-¬end (mu N) (mu c) = new-¬end N c
new-¬end (N₁ ; N₂) (hd c) = new-¬end N₁ c
new-¬end (N₁ ; N₂) (tl _ c) = new-¬end N₂ c

close-shape : {s : 𝕊 0} {p : Pol} {B : BindGroup} {Γ : Ctx (sum (suc b ∷ B))} →
  New s → BindCtx (s ; end p) (suc b ∷ B) Γ → Γ ﹫ 0F ≡ ⟨ t ⟩ → t ≃ end q →
  b ≡ 0 × B ≡ []
close-shape N (last x) eq t≃ = close-group-width N (last x) eq t≃ , refl
close-shape {q = q} N (cons-ret/acq s₁ {s₂ = s₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ ¬skips₂ x C ah) eq t≃ =
  ⊥-elim (go (consK-;⁻ head-cons))
  where
  head-cons : ConsK (kend q) (s₁ ; ret)
  head-cons = bindCtx′-head x (sym (V.lookup-++ˡ Γ₁ Γ₂ 0F) ■ eq) (≃-consK (≃-sym t≃) hend)

  go : ConsK (kend q) s₁ ⊎ (Skips s₁ × ConsK (kend q) ret) → ⊥
  go (inj₂ (_ , ()))
  go (inj₁ c) with consK-;⁻ (≃-consK s≃ (hd c))
  ... | inj₁ cs = new-¬end N cs
  ... | inj₂ (Sks , hend)
    with atom-;⁻ end (≃-sym (≃-trans s≃ (≃-skipsˡ Sks)))
  ...  | inj₁ (_ , Sk₂) = ¬skips₂ Sk₂
  ...  | inj₂ (_ , Sk₁) = skips⊥consK Sk₁ c
