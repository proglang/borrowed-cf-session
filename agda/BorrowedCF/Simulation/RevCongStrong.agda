module BorrowedCF.Simulation.RevCongStrong where

-- | STRONG congruence/reduction harmony for the untyped calculus.
--
--   The trivial ≋-bisimulation (BorrowedCF.Simulation.CongBisim) matches a
--   step R ─→ Q past a congruence move R ≋ R′ by re-WRAPPING it in a fresh
--   RU-Struct:  R′ ─→ Q  =  RU-Struct (sym c) red ε.  That typechecks, but it
--   GROWS the derivation, so the reverse-simulation recursion (Reverse.sim←)
--   that bounces sim←ᵍ(RU-Struct) → sim← → … has no descent metric.
--
--   This module tries to REPLAY the reduction's own constructor past the ≋′
--   generator (RU-Par ↦ RU-Par, RU-Res ↦ RU-Res, …) so the returned reduction
--   introduces NO new RU-Struct node.  We measure "RU-Struct nodes" with `sc`
--   and prove the sharpest bound that actually holds:  each ≋′-generator step
--   introduces AT MOST ONE RU-Struct  (`sc red′ ≤ suc (sc red)`), with the good
--   cases (congruence generators, the ∥-associativity reshuffle, and absorbing
--   into an EXISTING RU-Struct) staying at `sc red′ ≡ sc red`.
--
--   Which cases force the +1 — i.e. where a genuine constructor CANNOT be
--   replayed — is pinned down by `∥-red-inv` below and discussed in the header
--   note at the bottom.

open import BorrowedCF.Prelude
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR

import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)

open import Data.Product using (Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open Nat using (_≤_; ≤-refl; n≤1+n)

open UP using (Proc; _≋′_; _≋_; _∥_;
               ∥-comm′; ∥-assoc′; ∥-cong′; ν-cong′; φ-cong′;
               ∥-comm; ∥-assoc; ∥-cong; ν-cong; φ-cong)
open UR using (_─→ₚ_; RU-Par; RU-Par-right; RU-Res; RU-Sync; RU-Struct)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Derivation measures.
------------------------------------------------------------------------

-- Total number of ─→ₚ constructor nodes (RU-Struct counts its inner one + 1).
∣_∣ : {R Q : Proc n} → R ─→ₚ Q → ℕ
∣ RU-Par r       ∣ = suc ∣ r ∣
∣ RU-Par-right r ∣ = suc ∣ r ∣
∣ RU-Res r       ∣ = suc ∣ r ∣
∣ RU-Sync r      ∣ = suc ∣ r ∣
∣ RU-Struct _ r _ ∣ = suc ∣ r ∣
∣ _              ∣ = 1

-- Number of RU-Struct nodes on the derivation.  This is the caller-relevant
-- measure: RU-Struct is exactly the constructor that bounces control back to
-- sim←; RU-Par / RU-Res / RU-Sync recurse structurally inside sim←ᵍ and always
-- terminate, so they are "free".
sc : {R Q : Proc n} → R ─→ₚ Q → ℕ
sc (RU-Par r)        = sc r
sc (RU-Par-right r)  = sc r
sc (RU-Res r)        = sc r
sc (RU-Sync r)       = sc r
sc (RU-Struct _ r _) = suc (sc r)
sc _                 = 0

------------------------------------------------------------------------
-- The wrapping fallback (= CongBisim.≋-step): always available, +1 to sc.
------------------------------------------------------------------------

≋-step : {R R′ Q : Proc n} → R ≋ R′ → R ─→ₚ Q → R′ ─→ₚ Q
≋-step c red = RU-Struct (Eq*.symmetric _ c) red ε

------------------------------------------------------------------------
-- Strong single-step harmony, forward orientation, carrying the sc bound.
------------------------------------------------------------------------

≋′-sim-strongᵐ : {R R′ Q : Proc n}
               → R ≋′ R′ → (red : R ─→ₚ Q)
               → Σ[ Q′ ∈ Proc n ] Σ[ red′ ∈ R′ ─→ₚ Q′ ]
                   (sc red′ ≤ suc (sc red)) × (Q ≋ Q′)

-- (1) red = RU-Struct : absorb the generator into the EXISTING chain, keeping
--     the inner reduction.  No new RU-Struct: sc preserved.
≋′-sim-strongᵐ c (RU-Struct c₁ inner c₂) =
  _ , RU-Struct (Eq*.symmetric _ (Eq*.return c) ◅◅ c₁) inner c₂ , n≤1+n _ , ε

-- (2) congruence generators meeting the matching congruence reduction: recurse.
--     No new RU-Struct beyond the inductive one.
≋′-sim-strongᵐ (∥-cong′ g) (RU-Par sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strongᵐ g sub =
  _ , RU-Par sub′ , bnd , ∥-cong cc ε
≋′-sim-strongᵐ (ν-cong′ g) (RU-Res sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strongᵐ g sub =
  _ , RU-Res sub′ , bnd , ν-cong cc
≋′-sim-strongᵐ (φ-cong′ g) (RU-Sync sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strongᵐ g sub =
  _ , RU-Sync sub′ , bnd , φ-cong cc

-- (3) ∥-associativity meeting a left reduction: genuinely replay by nesting the
--     RU-Par one level deeper.  No RU-Struct.
≋′-sim-strongᵐ ∥-assoc′ (RU-Par sub) =
  _ , RU-Par (RU-Par sub) , n≤1+n _ , ∥-assoc

-- (3b) ∥-commutativity, either orientation of the reduction: genuinely replay
--      by swapping RU-Par ↔ RU-Par-right.  No RU-Struct, sc preserved.  (This
--      is what the newly-added RU-Par-right rule unblocks; the old note at the
--      bottom claiming ∥-comm forces a +1 is now STALE.)
≋′-sim-strongᵐ ∥-comm′ (RU-Par sub) =
  _ , RU-Par-right sub , n≤1+n _ , ∥-comm
≋′-sim-strongᵐ ∥-comm′ (RU-Par-right sub) =
  _ , RU-Par sub , n≤1+n _ , ∥-comm

-- (4) everything else: no genuine constructor is available (see note), so the
--     only witness is the wrapping fallback, costing +1 RU-Struct.
≋′-sim-strongᵐ c red = _ , ≋-step (Eq*.return c) red , ≤-refl , ε

-- Bare forward lemma (the requested signature).
≋′-sim-strong : {R R′ Q : Proc n}
              → R ≋′ R′ → R ─→ₚ Q
              → Σ[ Q′ ∈ Proc n ] (R′ ─→ₚ Q′) × (Q ≋ Q′)
≋′-sim-strong c red
  with Q′ , red′ , _ , cc ← ≋′-sim-strongᵐ c red = Q′ , red′ , cc

------------------------------------------------------------------------
-- Mirror orientation:  R′ ≋′ R → R ─→ Q → …  (the bwd leg of SymClosure).
------------------------------------------------------------------------

≋′-sim-strong-revᵐ : {R R′ Q : Proc n}
                   → R′ ≋′ R → (red : R ─→ₚ Q)
                   → Σ[ Q′ ∈ Proc n ] Σ[ red′ ∈ R′ ─→ₚ Q′ ]
                       (sc red′ ≤ suc (sc red)) × (Q ≋ Q′)

-- (1) absorb into an existing RU-Struct.
≋′-sim-strong-revᵐ g (RU-Struct c₁ inner c₂) =
  _ , RU-Struct (Eq*.return g ◅◅ c₁) inner c₂ , n≤1+n _ , ε

-- (2) congruence generators, matching reductions: recurse.
≋′-sim-strong-revᵐ (∥-cong′ g) (RU-Par sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strong-revᵐ g sub =
  _ , RU-Par sub′ , bnd , ∥-cong cc ε
≋′-sim-strong-revᵐ (ν-cong′ g) (RU-Res sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strong-revᵐ g sub =
  _ , RU-Res sub′ , bnd , ν-cong cc
≋′-sim-strong-revᵐ (φ-cong′ g) (RU-Sync sub)
  with _ , sub′ , bnd , cc ← ≋′-sim-strong-revᵐ g sub =
  _ , RU-Sync sub′ , bnd , φ-cong cc

-- (3) ∥-associativity, mirror: R′ = P₁∥(P₂∥P₃), R = (P₁∥P₂)∥P₃.  A left
--     reduction of R that itself is a left reduction of P₁∥P₂ un-nests.
≋′-sim-strong-revᵐ ∥-assoc′ (RU-Par (RU-Par sub)) =
  _ , RU-Par sub , n≤1+n _ , Eq*.symmetric _ ∥-assoc

-- (3b) ∥-commutativity, mirror: swap RU-Par ↔ RU-Par-right.  No RU-Struct.
≋′-sim-strong-revᵐ ∥-comm′ (RU-Par sub) =
  _ , RU-Par-right sub , n≤1+n _ , ∥-comm
≋′-sim-strong-revᵐ ∥-comm′ (RU-Par-right sub) =
  _ , RU-Par sub , n≤1+n _ , ∥-comm

-- (4) fallback wrapper.  R′ ≋ R (return g) then R ─→ Q, so R′ ─→ Q directly.
≋′-sim-strong-revᵐ g red = _ , RU-Struct (Eq*.return g) red ε , ≤-refl , ε

≋′-sim-strong-rev : {R R′ Q : Proc n}
                  → R′ ≋′ R → R ─→ₚ Q
                  → Σ[ Q′ ∈ Proc n ] (R′ ─→ₚ Q′) × (Q ≋ Q′)
≋′-sim-strong-rev g red
  with Q′ , red′ , _ , cc ← ≋′-sim-strong-revᵐ g red = Q′ , red′ , cc

------------------------------------------------------------------------
-- Combined form over one SymClosure generator (what sim←'s `c ◅ cs` splits to).
------------------------------------------------------------------------

≋′±-sim-strong : {R R′ Q : Proc n}
               → SymClosure _≋′_ R R′
               → R ─→ₚ Q
               → Σ[ Q′ ∈ Proc n ] (R′ ─→ₚ Q′) × (Q ≋ Q′)
≋′±-sim-strong (fwd g) red = ≋′-sim-strong g red
≋′±-sim-strong (bwd g) red = ≋′-sim-strong-rev g red

------------------------------------------------------------------------
-- Reduction inversion for  _∥_.  With RU-Par-right now in the calculus,
-- BOTH sides of a  A ∥ B  reduction are genuinely reachable, so the old
-- "left-only" obstruction (that forced ∥-comm to a +1 RU-Struct) is GONE:
-- the right disjunct below now feeds off  ∥-comm + RU-Par, not a fresh
-- RU-Struct wrapper.
------------------------------------------------------------------------

∥-red-inv : {A B C : Proc n} → A ∥ B ─→ₚ C
          → (∃[ A′ ] Σ[ r ∈ A ─→ₚ A′ ] C ≡ A′ ∥ B)
          ⊎ (∃[ R′ ] ∃[ P′ ] Σ[ c₁ ∈ (A ∥ B) ≋ R′ ] Σ[ r ∈ R′ ─→ₚ P′ ] P′ ≋ C)
∥-red-inv (RU-Par r)          = inj₁ (_ , r , refl)
∥-red-inv (RU-Par-right r)    = inj₂ (_ , _ , ∥-comm , RU-Par r , ∥-comm)
∥-red-inv (RU-Struct c₁ r c₂) = inj₂ (_ , _ , c₁ , r , c₂)
