{-# OPTIONS --rewriting #-}

-- COUNTEREXAMPLE: sim→ R-Com is FALSE at front-borrow b₁ = 0 with a non-empty tail.
--
-- The typed R-Com decrements the front chain's borrow count (suc b₁ ∷ B₁ → b₁ ∷ B₁).
-- The front chain's junction flag in the translation is ϕ[head] (Flatten.Flags), with
-- ϕ[zero] = set (true) and ϕ[suc _] = unset (false).  So when b₁ = 0 (and B₁ non-empty
-- so the junction flag EXISTS), the front flag flips unset → set.  But RU-Com does NOT
-- touch any (_ ↦ _) cell, and no untyped ≋′ rule changes a flag value — hence U[lhs]
-- cannot reduce to U[rhs].  Well-typedness cannot rule the case out: the typing only
-- sees `sum B` (BindCtx) and a struct that differs from the benign single-chain case
-- only by an ∥-unit `[] ∥ []`.

module BorrowedCF.Simulation.ComScratch where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
open import Data.List using (List; []; _∷_)

-- b₁ = b₂ = 0, B₁ = B₂ = (0 ∷ []): front chain has 1 borrow, one junction to a 0-chain.
lhs : 𝐓.Proc 0
lhs = 𝐓.ν (1 ∷ 0 ∷ []) (1 ∷ 0 ∷ [])
        ((𝐓.⟪ K `send · ((` 0F) ⊗ K `unit) ⟫ 𝐓.∥ 𝐓.⟪ K `recv · (` 1F) ⟫) 𝐓.∥ 𝐓.⟪ K `unit ⟫)

rhs : 𝐓.Proc 0
rhs = 𝐓.ν (0 ∷ 0 ∷ []) (0 ∷ 0 ∷ [])
        ((𝐓.⟪ K `unit ⟫ 𝐓.∥ 𝐓.⟪ K `unit ⟫) 𝐓.∥ 𝐓.⟪ K `unit ⟫)

-- A genuine typed R-Com reduction (typechecks cleanly):
red : lhs 𝐓R.─→ₚ rhs
red = 𝐓R.R-Com {e = K `unit} {P = 𝐓.⟪ K `unit ⟫} {E₁ = []} {E₂ = []} V-K

σ∅ : 0 →ₛ 0
σ∅ = λ ()

-- U[ lhs ] σ∅ ↝ ν(φ(0F↦false ∥ φ(0F↦false ∥ ((⟪send·…⟫ ∥ ⟪recv·…⟫) ∥ ⟪unit⟫))))  -- 2 unset
-- U[ rhs ] σ∅ ↝ ν(φ(0F↦true  ∥ φ(0F↦true  ∥ ((⟪unit⟫ ∥ ⟪unit⟫) ∥ ⟪unit⟫))))        -- 2 set
goalL : 𝐔.Proc 0
goalL = U[ lhs ] σ∅

goalR : 𝐔.Proc 0
goalR = U[ rhs ] σ∅
