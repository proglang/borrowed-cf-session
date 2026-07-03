-- Shared preamble for the Simulation2 development: re-exports the base modules
-- and the (sanctioned) function-extensionality postulate.
module BorrowedCF.Simulation.Base where

open import BorrowedCF.Prelude public
open import BorrowedCF.Terms public
open import BorrowedCF.Types public
open import BorrowedCF.Reduction.Base public
open import BorrowedCF.Reduction.Expressions public

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_; kleisliStar) public
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd) public
open import Data.Nat.ListAction using (sum) public

open import BorrowedCF.Processes.Bisim public

open Variables public
open Fin.Patterns public

postulate
  funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
