module BorrowedCF where

-- Term Syntax & Declarative Typing
import BorrowedCF.Terms

-- Algorithmic typing
--
-- Defn & Soundness
import BorrowedCF.Algorithmic
-- Completeness
import BorrowedCF.Completeness

-- Expression reduction
import BorrowedCF.Reduction.Expressions

-- High-level processes
--
-- Definitions
import BorrowedCF.Processes.Typed
import BorrowedCF.Reduction.Processes.Typed  -- !! ATTENTION: --allow-unsolved-metas
-- Safety
import BorrowedCF.Safety.Preservation
import BorrowedCF.Safety.Progress

-- Low-level processes
import BorrowedCF.Processes.Untyped
import BorrowedCF.Reduction.Processes.Untyped
-- Translation
import BorrowedCF.Processes.Translation

-- Low-level processes (soup representation)
import BorrowedCF.Processes.UntypedSoup
import BorrowedCF.Reduction.Processes.UntypedSoup
-- Translation
import BorrowedCF.Processes.TranslationSoup

-- Simulation
--
-- Forwards
import BorrowedCF.Simulation.ForwardSoup.Local
-- Backwards
import BorrowedCF.Simulation.BackwardSoup
