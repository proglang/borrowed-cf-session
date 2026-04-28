module BorrowedCF.Processes.BindGroups where

open import Data.List.NonEmpty as L⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.Nat as Nat hiding (suc)
open import Data.Nat.ListAction using (sum)
open import Function
open import Relation.Binary.PropositionalEquality

private variable
  n : ℕ

sum⁺ = sum ∘ L⁺.toList

record Bind (n : ℕ) : Set where
  constructor bind
  field
    groups : List⁺ ℕ
    .Σgroups≡n : sum⁺ groups ≡ n

suc : Bind n → Bind (Nat.suc n)
suc (bind groups Σgroups≡n) =
  bind (Nat.suc (L⁺.head groups) ∷ L⁺.tail groups) (cong Nat.suc Σgroups≡n)

guard : Bind n → Bind n
guard (bind groups Σgroups≡n) =
  bind (0 ∷⁺ groups) Σgroups≡n

mk : (bs : List⁺ ℕ) → Bind (sum⁺ bs)
mk bs = bind bs refl

open Bind public
