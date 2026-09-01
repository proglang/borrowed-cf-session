module BorrowedCF.Processes.UntypedSoup where

open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_<_) renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms.BaseSoup

open Nat.Variables

data Flag : Set where
  drop acq : Flag

-- A thread stores its expression and the phi cells hosted by that thread.
-- References may point into the flag list of any thread in the configuration.
Thread : ℕ → ℕ → Set
Thread n m = Tm (2 *ℕ n) m × List Flag

record Config (n m : ℕ) : Set where
  constructor config
  field
    -- One state bit per channel.  True means that the channel is closed;
    -- endpoint references remain 2i and 2i+1 in the term namespace.
    channels : Vec Bool n

    -- Every term shares the channel namespace and the thread namespace.
    -- Its accompanying list contains the phi cells hosted by that thread.
    threads : Vec (Thread n m) m

open Config public

endpoint : 𝔽 n → 𝔽 2 → 𝔽 (2 *ℕ n)
endpoint {n} i side = Fin.cast (Nat.*-comm n 2) (Fin.combine i side)

leftEnd : 𝔽 n → 𝔽 (2 *ℕ n)
leftEnd i = endpoint i zero

rightEnd : 𝔽 n → 𝔽 (2 *ℕ n)
rightEnd i = endpoint i (suc zero)

channelClosed : Config n m → 𝔽 n → Bool
channelClosed C i = lookup (channels C) i

termAt : Config n m → 𝔽 m → Tm (2 *ℕ n) m
termAt C j = proj₁ (lookup (threads C) j)

flagsAt : Config n m → 𝔽 m → List Flag
flagsAt C j = proj₂ (lookup (threads C) j)

-- The slot component of PhiRef is deliberately extrinsic: its upper bound is
-- stored in the configuration rather than in the indices of Tm.  This keeps
-- Config indexed only by channel and thread counts.
ValidPhiRef : Config n m → PhiRef m → Set
ValidPhiRef C (j , k) = k < L.length (flagsAt C j)

record WellFormed (C : Config n m) : Set where
  field
    phiRefs-valid :
      (j : 𝔽 m) → All (ValidPhiRef C) (phiRefs (termAt C j))

open WellFormed public
