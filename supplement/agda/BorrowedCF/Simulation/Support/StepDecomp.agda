-- | Step decomposition: every untyped reduction is a HEAD rule fired inside a
--   one-hole process context, with every interior RU-Struct absorbed into ≋.
--
--   The reverse engine currently peels top-level RU-Struct wrappers and hands
--   RU-Par/RU-Par-right/RU-Res/RU-Sync to its residual `Base` unanalysed — so
--   `Base` would have to re-do the same analysis, and interior RU-Structs can
--   hide arbitrarily deep under the congruence rules.  `decomp` does the whole
--   analysis once, by ONE structural induction on the derivation: the result is
--   a head rule (one of the eleven non-congruence, non-Struct rules), its
--   context, and two ≋ conjugations.  Downstream, per-rule reflectors become
--   position-agnostic consumers of (context, head rule) pairs, and the four
--   congruence constructors need no cases of their own anywhere.
module BorrowedCF.Simulation.Support.StepDecomp where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Reduction.Processes.Untyped

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- One-hole process contexts, outermost constructor first (Tel-style).
------------------------------------------------------------------------

data Ctx* : ℕ → ℕ → Set where
  ∘ᴷ    : Ctx* n n
  _∥ᴷ_  : Ctx* n k → Proc n → Ctx* n k
  _ᴷ∥_  : Proc n → Ctx* n k → Ctx* n k
  νᴷ    : Ctx* (2 + n) k → Ctx* n k
  φᴷ    : Flag → Ctx* (1 + n) k → Ctx* n k

_[_]ᴷ : Ctx* n k → Proc k → Proc n
∘ᴷ       [ X ]ᴷ = X
(C ∥ᴷ Q) [ X ]ᴷ = (C [ X ]ᴷ) ∥ Q
(P ᴷ∥ C) [ X ]ᴷ = P ∥ (C [ X ]ᴷ)
(νᴷ C)   [ X ]ᴷ = ν (C [ X ]ᴷ)
(φᴷ f C) [ X ]ᴷ = φ f (C [ X ]ᴷ)

-- ≋ is a congruence for plugging.
ctx-cong : (C : Ctx* n k) {X Y : Proc k} → X ≋ Y → C [ X ]ᴷ ≋ C [ Y ]ᴷ
ctx-cong ∘ᴷ       c = c
ctx-cong (C ∥ᴷ Q) c = ∥-cong (ctx-cong C c) ε
ctx-cong (P ᴷ∥ C) c = ∥-cong ε (ctx-cong C c)
ctx-cong (νᴷ C)   c = ν-cong (ctx-cong C c)
ctx-cong (φᴷ f C) c = φ-cong (ctx-cong C c)

------------------------------------------------------------------------
-- Head rules: everything except the four congruence rules and RU-Struct.
------------------------------------------------------------------------

Head : {R Q : Proc n} → R ─→ₚ Q → Set
Head (RU-Par _)        = ⊥
Head (RU-Par-right _)  = ⊥
Head (RU-Res _)        = ⊥
Head (RU-Sync _)       = ⊥
Head (RU-Struct _ _ _) = ⊥
Head _                 = ⊤

------------------------------------------------------------------------
-- The decomposition.
------------------------------------------------------------------------

record Decomp {n} (R Q : Proc n) : Set where
  constructor mkDecomp
  field
    {holeScope} : ℕ
    ctx    : Ctx* n holeScope
    {src}  : Proc holeScope
    {tgt}  : Proc holeScope
    head   : src ─→ₚ tgt
    isHead : Head head
    left   : R ≋ ctx [ src ]ᴷ
    right  : ctx [ tgt ]ᴷ ≋ Q

decomp : {R Q : Proc n} (red : R ─→ₚ Q) → Decomp R Q
decomp (RU-Par red) with mkDecomp C h ih l r ← decomp red =
  mkDecomp (C ∥ᴷ _) h ih (∥-cong l ε) (∥-cong r ε)
decomp (RU-Par-right red) with mkDecomp C h ih l r ← decomp red =
  mkDecomp (_ ᴷ∥ C) h ih (∥-cong ε l) (∥-cong ε r)
decomp (RU-Res red) with mkDecomp C h ih l r ← decomp red =
  mkDecomp (νᴷ C) h ih (ν-cong l) (ν-cong r)
decomp (RU-Sync red) with mkDecomp C h ih l r ← decomp red =
  mkDecomp (φᴷ _ C) h ih (φ-cong l) (φ-cong r)
decomp (RU-Struct c₁ red c₂) with mkDecomp C h ih l r ← decomp red =
  mkDecomp C h ih (c₁ ◅◅ l) (r ◅◅ c₂)
decomp red@(RU-Exp _)        = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Fork _ _)     = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-New _)        = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-LSplit _)     = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-RSplit _)     = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Drop _)       = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Discard _ _)  = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Acquire _)    = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Close _ _)    = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Com _ _ _)    = mkDecomp ∘ᴷ red tt ε ε
decomp red@(RU-Choice _ _ _) = mkDecomp ∘ᴷ red tt ε ε
