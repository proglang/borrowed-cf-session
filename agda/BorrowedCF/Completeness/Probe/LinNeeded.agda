-- | Red-team probe: the `LinStruct` hypothesis of Complete⇐/Complete⇒ is
--   NECESSARY, and the invariant that shows it is `count` EQUALITY (not the
--   inequality `≼⇒count≤` of Simulation.Support.Confine).
--
--   `≼` never changes the multiplicity of a non-unrestricted variable:
--   `≼-refl` is `≈` (count-≈), `≼-∅` has an UnrCx on the right (count 0 on both
--   sides), `≼-wk` permutes a sum of four counts, and the congruences add.
--   Hence `` ` x ≼ ` x ∥ ` x `` is underivable for a linear x, while the
--   declarative system types `x ⊗ x` under `` ` x ∥ ` x `` by T-Pair.
module BorrowedCF.Completeness.Probe.LinNeeded where

open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Simulation.Support.Confine using (count)
open import BorrowedCF.Simulation.Support.BeforeOrder using (count-≼-eq)
open import BorrowedCF.Completeness.Base

open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- 1.  The invariant that does it: `≼` PRESERVES the count of a linear variable.
--     Already in the development as `count-≼-eq`
--     (Simulation/Support/BeforeOrder.agda:114) — NOT the inequality
--     `≼⇒count≤` (Simulation/Support/Confine.agda) that Base.agda's comment
--     appeals to; the inequality does not refute `` ` x ≼ ` x ∥ ` x ``
--     (1 ≤ 2 holds), the equality does (1 ≢ 2).

≼⇒count≡ : ∀ {n} {Γ : Ctx n} {x : 𝔽 n} {α β : Struct n} →
           ¬ Unr (Γ ﹫ x) → Γ ∶ α ≼ β → count x α ≡ count x β
≼⇒count≡ = count-≼-eq

------------------------------------------------------------------------
-- 2.  The witness: one LINEAR variable h : ⟨ end ‼ ⟩ used twice.

Γ₀ : Ctx 1
Γ₀ = ⟨ end ‼ ⟩ ⸴ []

γ₀ : Struct 1
γ₀ = ` 0F ∥ ` 0F

¬unr-h : ¬ Unr (Γ₀ ﹫ 0F)
¬unr-h ⟨ () ⟩

e₀ : Tm 1
e₀ = (` 0F) ⊗ (` 0F)

T₀ : 𝕋
T₀ = ⟨ end ‼ ⟩ ⊗¹ ⟨ end ‼ ⟩

decl : Γ₀ ; γ₀ ⊢ e₀ ∶ T₀ ∣ ℙ
decl = T-Pair par par (T-Var 0F refl) (T-Var 0F refl)

-- LinStruct FAILS here, as it must: count 0F γ₀ = 2.
¬linear : ¬ LinStruct Γ₀ γ₀
¬linear lin with lin 0F ¬unr-h
... | Nat.s≤s ()

------------------------------------------------------------------------
-- 3.  No algorithmic derivation exists.

var-≼ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {ξ m T ϵ Δ k} →
        Γ ; γ / m ⊢[ ξ ] ` x ∶ T ∣ ϵ ↑ Δ / k → Γ ∶ ` x ≼ γ
var-≼ (A-Var ≤γ)  = ≤γ
var-≼ (A-Check d) = var-≼ d
var-≼ (A-Ann d)   = var-≼ d

bad : Γ₀ ∶ ` 0F ≼ γ₀ → ⊥
bad ≤ with ≼⇒count≡ {x = 0F} ¬unr-h ≤
... | ()

no-alg : ∀ {ξ m T ϵ Δ k} → Γ₀ ; γ₀ / m ⊢[ ξ ] e₀ ∶ T ∣ ϵ ↑ Δ / k → ⊥
no-alg (A-Pair par _ _ d₁ _) = bad (var-≼ d₁)
no-alg (A-Pair seq _ _ d₁ _) = bad (var-≼ d₁)
no-alg (A-Check d) = no-alg d
no-alg (A-Ann d)   = no-alg d

------------------------------------------------------------------------
-- 4.  Completeness WITHOUT the linearity hypothesis is false.

Complete⇐-noLin : Set
Complete⇐-noLin = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
    Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ e ⇐ T ∣ ϵ′ ↑ Δ / k)

solvedCtx : SolvedCtx Γ₀
solvedCtx 0F = ⟨ end ⟩

refute-noLin : ¬ Complete⇐-noLin
refute-noLin compl
  with compl solvedCtx ((` 0F) ⊗ (` 0F)) (⟨ end ⟩ ⊗⟨ 𝟙 ⟩ ⟨ end ⟩) decl 0
... | _ , _ , _ , _ , _ , _ , _ , alg = no-alg alg
