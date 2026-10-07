-- | Red-team probe: the `LinStruct` hypothesis of Complete⇐/Complete⇒ is
--   NECESSARY, and the invariant that shows it is `count` EQUALITY (not the
--   inequality `≼⇒count≤` of Simulation.Support.Confine).
--
--   `≼` never changes the multiplicity of a non-unrestricted variable:
--   `≼-refl` is `≈` (count-≈), `≼-∅` has an UnrCx on the right (count 0 on both
--   sides), `≼-wk` permutes a sum of four counts, and the congruences add.
--   Hence `` ` x ≼ ` x ∥ ` x `` is underivable for a linear x, while the
--   declarative system types `x ⊗ x` under `` ` x ∥ ` x `` by T-Pair.
--   Since 2026-10-07 the refutation covers every annotated ê ⊒ x ⊗ x
--   (`Complete⇐` concludes with an annotated term), and the count invariant is
--   proved for the constraint-emitting `_∶_≼_↑_` the algorithmic rules use.
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
open import BorrowedCF.Simulation.Support.Confine using (count; count-≈′; unrCx⇒count0)
open import BorrowedCF.Simulation.Support.BeforeOrder using (count-≼-eq; swap-mid)
open import BorrowedCF.Completeness.Sub using (≈′↑-erase)
open import Data.List.Relation.Unary.All using ([])
open import BorrowedCF.Context.Domain using (_↓_)
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
-- 3.  No algorithmic derivation exists, for e₀ or for any annotated ê ⊒ e₀.
--     The algorithmic rules use the constraint-emitting `_∶_≼_↑_`; the count
--     invariant holds for it as well (the mobility steps ∥′-tm emit constraints
--     but do not change any count).

count-≈′↑ : ∀ {n} {Γ : Ctx n} {α β : Struct n} {Δ} (x : 𝔽 n) →
            ¬ Unr (Γ ﹫ x) → Γ ∶ α ≈′ β ↑ Δ → count x α ≡ count x β
count-≈′↑ x ¬u d@sq′-assoc↑   = count-≈′ {x = x} ¬u (≈′↑-erase [] d)
count-≈′↑ x ¬u (sq′-cong₁↑ d) = cong (_+ _) (count-≈′↑ x ¬u d)
count-≈′↑ x ¬u (sq′-cong₂↑ d) = cong (_ +_) (count-≈′↑ x ¬u d)
count-≈′↑ x ¬u d@∥′-unit↑     = count-≈′ {x = x} ¬u (≈′↑-erase [] d)
count-≈′↑ x ¬u d@∥′-assoc↑    = count-≈′ {x = x} ¬u (≈′↑-erase [] d)
count-≈′↑ x ¬u d@∥′-comm↑     = count-≈′ {x = x} ¬u (≈′↑-erase [] d)
count-≈′↑ x ¬u (∥′-cong₁↑ d)  = cong (_+ _) (count-≈′↑ x ¬u d)
count-≈′↑ x ¬u d@(∥′-dup↑ U)  = count-≈′ {x = x} ¬u (≈′↑-erase [] d)
count-≈′↑ x ¬u ∥′-tmˡ↑        = refl
count-≈′↑ x ¬u ∥′-tmʳ↑        = refl

count-≈↑ : ∀ {n} {Γ : Ctx n} {α β : Struct n} {Δ} (x : 𝔽 n) →
           ¬ Unr (Γ ﹫ x) → Γ ∶ α ≈ β ↑ Δ → count x α ≡ count x β
count-≈↑ x ¬u ε↑ = refl
count-≈↑ x ¬u (d ◅ᶠ ds) = count-≈′↑ x ¬u d ■ count-≈↑ x ¬u ds
count-≈↑ x ¬u (d ◅ᵇ ds) = sym (count-≈′↑ x ¬u d) ■ count-≈↑ x ¬u ds

count-≼↑-eq : ∀ {n} {Γ : Ctx n} {α β : Struct n} {Δ} (x : 𝔽 n) →
              ¬ Unr (Γ ﹫ x) → Γ ∶ α ≼ β ↑ Δ → count x α ≡ count x β
count-≼↑-eq x ¬u (≼-refl↑ d) = count-≈↑ x ¬u d
count-≼↑-eq x ¬u (≼-∅↑ U) = sym (unrCx⇒count0 {x = x} ¬u U)
count-≼↑-eq x ¬u (≼-wk↑ {α₁ = a1} {α₂ = a2} {β₁ = b1} {β₂ = b2}) =
  swap-mid (count x a1) (count x a2) (count x b1) (count x b2)
count-≼↑-eq x ¬u (≼-trans↑ p q) = count-≼↑-eq x ¬u p ■ count-≼↑-eq x ¬u q
count-≼↑-eq x ¬u (≼-cong-sq↑ p q) = cong₂ _+_ (count-≼↑-eq x ¬u p) (count-≼↑-eq x ¬u q)
count-≼↑-eq x ¬u (≼-cong-par↑ p q) = cong₂ _+_ (count-≼↑-eq x ¬u p) (count-≼↑-eq x ¬u q)

var-≼ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {ê : Tm n} {ξ m T ϵ Δ k} →
        ` x ⊑ ê → Γ ; γ / m ⊢[ ξ ] ê ∶ T ∣ ϵ ↑ Δ / k → Σ[ Δ′ ∈ CSet ] Γ ∶ ` x ≼ γ ↑ Δ′
var-≼ ⊑-var (A-Var ≤γ)      = _ , ≤γ
var-≼ ⊑-var (A-Check d)     = var-≼ ⊑-var d
var-≼ (ann p T) (A-Ann d)   = var-≼ p d
var-≼ (ann p T) (A-Check d) = var-≼ (ann p T) d

bad : ∀ {Δ} → Γ₀ ∶ ` 0F ≼ γ₀ ↑ Δ → ⊥
bad ≤ with count-≼↑-eq 0F ¬unr-h ≤
... | ()

-- the A-Pair premise restricts γ₀ to the free variables of the ANNOTATED
-- component; `fv-⊑` brings them back to those of ` 0F.
bad-⊑ : ∀ {ê : Tm 1} {Δ} → ` 0F ⊑ ê → Γ₀ ∶ ` 0F ≼ (γ₀ ↓ fv ê) ↑ Δ → ⊥
bad-⊑ {Δ = Δ} p ≤ = bad (subst (λ X → Γ₀ ∶ ` 0F ≼ (γ₀ ↓ X) ↑ Δ) (fv-⊑ p) ≤)

no-alg : ∀ {ê ξ m T ϵ Δ k} → e₀ ⊑ ê → Γ₀ ; γ₀ / m ⊢[ ξ ] ê ∶ T ∣ ϵ ↑ Δ / k → ⊥
no-alg (⊑-⊗ p₁ p₂) (A-Pair par _ _ d₁ _) = bad-⊑ p₁ (proj₂ (var-≼ p₁ d₁))
no-alg (⊑-⊗ p₁ p₂) (A-Pair seq _ _ d₁ _) = bad-⊑ p₁ (proj₂ (var-≼ p₁ d₁))
no-alg (⊑-⊗ p₁ p₂) (A-Check d) = no-alg (⊑-⊗ p₁ p₂) d
no-alg (ann p T) (A-Ann d)   = no-alg p d
no-alg (ann p T) (A-Check d) = no-alg (ann p T) d

------------------------------------------------------------------------
-- 4.  Completeness WITHOUT the linearity hypothesis is false.

Complete⇐-noLin : Set
Complete⇐-noLin = ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} →
  SolvedCtx Γ → SolvedTm e → SolvedTy T →
  Γ ; γ ⊢ e ∶ T ∣ ϵ →
  ∀ m → Σ[ ê ∈ Tm n ] e ⊑ ê ×
    (Σ[ ϵ′ ∈ Eff ] Σ[ Δ ∈ CSet ] Σ[ k ∈ ℕ ] Σ[ σ ∈ UV.Sub ]
      Solving σ × SolvedΔ Δ σ × ϵ′ ≤ϵ ϵ × (Γ ; γ / m ⊢ ê ⇐ T ∣ ϵ′ ↑ Δ / k))

solvedCtx : SolvedCtx Γ₀
solvedCtx 0F = ⟨ end ⟩

refute-noLin : ¬ Complete⇐-noLin
refute-noLin compl
  with compl solvedCtx ((` 0F) ⊗ (` 0F)) (⟨ end ⟩ ⊗⟨ 𝟙 ⟩ ⟨ end ⟩) decl 0
... | _ , p , _ , _ , _ , _ , _ , _ , _ , alg = no-alg p alg
