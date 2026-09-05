-- | Aggregate interface for the soup-to-typed simulation development.
module BorrowedCF.Simulation.BackwardSoup where

open import BorrowedCF.Simulation.BackwardSoup.Statement public
open import BorrowedCF.Simulation.BackwardSoup.SlotInsert public
open import BorrowedCF.Simulation.BackwardSoup.Locate public
open import BorrowedCF.Simulation.BackwardSoup.Inversion public
open import BorrowedCF.Simulation.BackwardSoup.Position public
open import BorrowedCF.Simulation.BackwardSoup.Canonical public
open import BorrowedCF.Simulation.BackwardSoup.CanonicalPair public
open import BorrowedCF.Simulation.BackwardSoup.PairPosition public
open import BorrowedCF.Simulation.BackwardSoup.LocatePair public
open import BorrowedCF.Simulation.BackwardSoup.Tracks public
open import BorrowedCF.Simulation.BackwardSoup.TracksImage public
open import BorrowedCF.Simulation.BackwardSoup.CanonicalImage public
open import BorrowedCF.Simulation.BackwardSoup.TypedInversion public
open import BorrowedCF.Simulation.BackwardSoup.Unique public
open import BorrowedCF.Simulation.BackwardSoup.Triple public
open import BorrowedCF.Simulation.BackwardSoup.AcqShape public
open import BorrowedCF.Simulation.BackwardSoup.Lift public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Exp public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Fork public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.New public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Drop public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Discard public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Acq public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.LSplit public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.RSplit public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Close public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Com public
open import BorrowedCF.Simulation.BackwardSoup.Leaves.Choice public
open import BorrowedCF.Simulation.BackwardSoup.Main public
