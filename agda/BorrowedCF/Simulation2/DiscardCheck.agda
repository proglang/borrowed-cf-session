-- Empirical confirmation: R-Discard (typed) vs the translation U[_].
-- R-Discard : nu (suc b :: B1) B2 (P <.>p weakenr) --> nu (b :: B1) B2 P.
--   * b>=1 (drop->drop) and single-chain B1=[] (no junction): U[LHS] == U[RHS]
--     definitionally (refl) -- R-Discard is SILENT on the untyped side.
--   * b=0 with nonempty tail: the head junction flag flips phi drop -> phi acq;
--     NOT silent, and no untyped step connects phi drop to phi acq (RU-Drop needs
--     a drop redex). So a weak-sim-up-to-Discard alone does NOT cover this case.
module BorrowedCF.Simulation2.DiscardCheck where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
import BorrowedCF.Processes.Typed as T
import BorrowedCF.Processes.Untyped as U
open import BorrowedCF.Processes.Bisim
open import Data.Maybe using (Maybe; just; nothing)
open Fin.Patterns

σ0 : 0 →ₛ 0
σ0 = λ ()

silent-bpos : U[ T.ν (2 ∷ 1 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0
            ≡ U[ T.ν (1 ∷ 1 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0
silent-bpos = refl

silent-single : U[ T.ν (1 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0
              ≡ U[ T.ν (0 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0
silent-single = refl

headFlag : U.Proc 0 -> Maybe U.Flag
headFlag (U.ν (U.φ f _)) = just f
headFlag _ = nothing

flag-lhs : headFlag (U[ T.ν (1 ∷ 1 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0) ≡ just U.drop
flag-lhs = refl

flag-rhs : headFlag (U[ T.ν (0 ∷ 1 ∷ []) (1 ∷ []) (T.⟪ K `unit ⟫) ] σ0) ≡ just U.acq
flag-rhs = refl
