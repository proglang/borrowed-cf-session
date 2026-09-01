module BorrowedCF.Processes.UntypedSoup where

open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_<_) renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup

open Nat.Variables

data Flag : Set where
  drop acq : Flag

-- Each endpoint has its own phi-cell list.
Channel : Set
Channel = Bool × List Flag × List Flag

Thread : ℕ → Set
Thread n = Tm (2 *ℕ n)

record Config (n m : ℕ) : Set where
  constructor config
  field
    -- True means that the channel is closed.  The two lists belong to
    -- endpoints 2i and 2i+1, respectively.
    channels : Vec Channel n
    threads : Vec (Thread n) m

open Config public

endpoint : 𝔽 n → 𝔽 2 → 𝔽 (2 *ℕ n)
endpoint {n} i side = Fin.cast (Nat.*-comm n 2) (Fin.combine i side)

leftEnd : 𝔽 n → 𝔽 (2 *ℕ n)
leftEnd i = endpoint i zero

rightEnd : 𝔽 n → 𝔽 (2 *ℕ n)
rightEnd i = endpoint i (suc zero)

channelClosed : Config n m → 𝔽 n → Bool
channelClosed C i = proj₁ (lookup (channels C) i)

channelFlagLists : Channel → Vec (List Flag) 2
channelFlagLists (_ , fs₀ , fs₁) = fs₀ ∷ fs₁ ∷ []

endpointFlagLists : Config n m → Vec (List Flag) (2 *ℕ n)
endpointFlagLists {n} C =
  V.cast (Nat.*-comm n 2) (V.concat (V.map channelFlagLists (channels C)))

termAt : Config n m → 𝔽 m → Thread n
termAt C j = lookup (threads C) j

flagsAt : Config n m → 𝔽 (2 *ℕ n) → List Flag
flagsAt C x = lookup (endpointFlagLists C) x

ValidPhiRef : Config n m → PhiRef (2 *ℕ n) → Set
ValidPhiRef C (x , k) = k < L.length (flagsAt C x)

ValidResolvedPhiRef :
  Config n m → ResolvedPhiRef (2 *ℕ n) → Set
ValidResolvedPhiRef C nothing = ⊥
ValidResolvedPhiRef C (just r) = ValidPhiRef C r

record WellFormed (C : Config n m) : Set where
  field
    phiRefs-valid :
      (j : 𝔽 m) →
      All (ValidResolvedPhiRef C) (phiRefs (termAt C j))

open WellFormed public
