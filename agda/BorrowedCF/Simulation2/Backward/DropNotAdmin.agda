-- | MACHINE-CHECKED obstruction for the "reverse-up-to-φ" ε-ABSORPTION route
--   at the νφ-comm φ-ESCAPE (the residual gap of Backward.agda ?0 that the
--   PhiAbsorbNuSwap ν-swap milestone does NOT cover).
--
--   BACKGROUND.  The non-ε engine (Backward.agda ?0) must reflect an untyped
--   step  red : R ─→ₚ Q  where  R ≈ U[ P ] σ.  The generator  νφ-comm′  pulls a
--   sync cell OUT of the dual-pair binder, sending an image  ν (φ drop body)  to
--   a φ-HEADED process  φ drop (ν …)  that is provably NOT any image
--   (Simulation.RevUCong.U-not-φ), yet is ≈-related to the image and REACHABLE
--   (RevUCong: the R-New source ν (1∷1∷…) is well-typed and its image is this
--   φ-bearing shape).  RevUCong already refutes the STRICT-image reflection.
--
--   The proposed "up-to-φ" workaround absorbs such administrative φ-moves into
--   the codomain ≈ with a ZERO typed step (P′ = P, ε), relying on  Q ≈ U[ P ] σ
--   whenever  red  is administrative.  THIS MODULE MACHINE-CHECKS that the
--   workaround CANNOT apply when  red  is a genuine φ-DROP: the drop reduct is
--   NOT ≈-related to its redex, because the drop FLIPS a sync flag drop→acq and
--   ≈ = EqClosure(≋ ∪ ─→ᵃ) preserves the acq-flag count  #acq  (only the
--   a-discard generator is administrative, and it touches no φ-flag).
--
--   CONSEQUENCE.  At a top-level φ-drop escape the engine can neither (i) absorb
--   the step into ≈ with ε typed steps (this module), nor (ii) reflect it to a
--   typed step by strict image inversion (RevUCong: R is not an image), because
--   the only typed drop rule (TR.R-Drop) is ν-scoped while R is φ-headed.
--   Closing ?0 therefore needs a φ-telescope-aware reverse inversion that
--   recovers the ν-scoped image from the νφ-comm escape — a design-level engine
--   the ν-swap absorption template does not provide.  All results below are
--   hole-free and postulate-free.
module BorrowedCF.Simulation2.Backward.DropNotAdmin where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Reduction.Base using (Frame*; _[_]*)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; _─→ᵃ_)
import BorrowedCF.Simulation.RevAdmin as RA

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc; 1+n≢n)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open Nat.Variables
open Fin.Patterns

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ ⊗ (` x)) ⊗ e₂

------------------------------------------------------------------------
-- (1) The acq-flag count: number of φ-cells flagged `acq`.
------------------------------------------------------------------------

#acq : ∀ {n} → UP.Proc n → ℕ
#acq UP.⟪ e ⟫          = 0
#acq (P UP.∥ Q)        = #acq P + #acq Q
#acq (UP.ν P)          = #acq P
#acq (UP.φ UP.drop P)  = #acq P
#acq (UP.φ UP.acq  P)  = suc (#acq P)

-- Renaming/substitution is flag-blind, so #acq is invariant under any ⋯ₚ.
#acq-⋯ₚ : ∀ ⦃ K : Kit 𝓕 ⦄ {m n} (P : UP.Proc m) (ϕ : m –[ K ]→ n)
        → #acq (P UP.⋯ₚ ϕ) ≡ #acq P
#acq-⋯ₚ UP.⟪ e ⟫         ϕ = refl
#acq-⋯ₚ (P UP.∥ Q)       ϕ = cong₂ _+_ (#acq-⋯ₚ P ϕ) (#acq-⋯ₚ Q ϕ)
#acq-⋯ₚ (UP.ν P)         ϕ = #acq-⋯ₚ P (ϕ ↑* 2)
#acq-⋯ₚ (UP.φ UP.drop P) ϕ = #acq-⋯ₚ P (ϕ ↑)
#acq-⋯ₚ (UP.φ UP.acq  P) ϕ = cong suc (#acq-⋯ₚ P (ϕ ↑))

------------------------------------------------------------------------
-- (2) #acq is a structural-congruence invariant.
------------------------------------------------------------------------

-- φ-ext′ has three implicits {P}{x}{Q}; naming the non-adjacent {x}{Q} trips
-- this Agda's implicit-arity check, so we match the constructor bare and route
-- through a flag-EXPLICIT helper (the flag is a plain argument here).
#acq-φext : ∀ {n} (x : UP.Flag) {P : UP.Proc n} {Q : UP.Proc (1 + n)}
          → #acq (P UP.∥ UP.φ x Q) ≡ #acq (UP.φ x ((P UP.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) UP.∥ Q))
#acq-φext UP.drop {P} {Q} = cong (_+ #acq Q) (sym (#acq-⋯ₚ P (weaken* ⦃ Kᵣ ⦄ 1)))
#acq-φext UP.acq  {P} {Q} =
  Eq.trans (+-suc (#acq P) (#acq Q))
           (cong (λ z → suc (z + #acq Q)) (sym (#acq-⋯ₚ P (weaken* ⦃ Kᵣ ⦄ 1))))

-- νφ-comm′ likewise: two named implicits {x}{P} overflow this Agda's arity
-- check, so match bare + flag-explicit helper.
#acq-νφ : ∀ {n} (x : UP.Flag) {P : UP.Proc (3 + n)}
        → #acq (UP.ν (UP.φ x P)) ≡ #acq (UP.φ x (UP.ν (P UP.⋯ₚ assocSwapᵣ 1 2)))
#acq-νφ UP.drop {P} = sym (#acq-⋯ₚ P (assocSwapᵣ 1 2))
#acq-νφ UP.acq  {P} = cong suc (sym (#acq-⋯ₚ P (assocSwapᵣ 1 2)))

#acq-φcomm : ∀ {n} (x y : UP.Flag) {P : UP.Proc (2 + n)}
           → #acq (UP.φ x (UP.φ y P)) ≡ #acq (UP.φ y (UP.φ x (P UP.⋯ₚ assocSwapᵣ 1 1)))
#acq-φcomm UP.drop UP.drop {P} = sym (#acq-⋯ₚ P (assocSwapᵣ 1 1))
#acq-φcomm UP.drop UP.acq  {P} = cong suc (sym (#acq-⋯ₚ P (assocSwapᵣ 1 1)))
#acq-φcomm UP.acq  UP.drop {P} = cong suc (sym (#acq-⋯ₚ P (assocSwapᵣ 1 1)))
#acq-φcomm UP.acq  UP.acq  {P} = cong (λ z → suc (suc z)) (sym (#acq-⋯ₚ P (assocSwapᵣ 1 1)))

#acq-≋′ : ∀ {n} {P Q : UP.Proc n} → P UP.≋′ Q → #acq P ≡ #acq Q
#acq-≋′ (UP.∥-comm′  {P = P} {Q = Q})            = +-comm (#acq P) (#acq Q)
#acq-≋′ (UP.∥-assoc′ {P₁ = A} {P₂ = B} {P₃ = C}) = sym (+-assoc (#acq A) (#acq B) (#acq C))
#acq-≋′ UP.∥-unit′                                = refl
#acq-≋′ (UP.ν-swap′  {P = P})                     = sym (#acq-⋯ₚ P (swapᵣ 1 1))
#acq-≋′ (UP.ν-comm′  {P = P})                     = sym (#acq-⋯ₚ P (assocSwapᵣ 2 2))
#acq-≋′ (UP.φ-comm′ {x = x} {y = y})              = #acq-φcomm x y
#acq-≋′ (UP.νφ-comm′ {x = x})                     = #acq-νφ x
#acq-≋′ (UP.ν-ext′  {P = P} {Q = Q})             = cong (_+ #acq Q) (sym (#acq-⋯ₚ P (weaken* ⦃ Kᵣ ⦄ 2)))
#acq-≋′ (UP.φ-ext′ {x = x})                       = #acq-φext x
#acq-≋′ (UP.∥-cong′ {Q = Q} d)                    = cong (_+ #acq Q) (#acq-≋′ d)
#acq-≋′ (UP.ν-cong′ d)                             = #acq-≋′ d
#acq-≋′ (UP.φ-cong′ {x = UP.drop} d)              = #acq-≋′ d
#acq-≋′ (UP.φ-cong′ {x = UP.acq}  d)              = cong suc (#acq-≋′ d)

#acq-≋ : ∀ {n} {P Q : UP.Proc n} → P UP.≋ Q → #acq P ≡ #acq Q
#acq-≋ ε              = refl
#acq-≋ (fwd d ◅ rest) = Eq.trans (#acq-≋′ d)       (#acq-≋ rest)
#acq-≋ (bwd d ◅ rest) = Eq.trans (sym (#acq-≋′ d)) (#acq-≋ rest)

------------------------------------------------------------------------
-- (3) #acq is preserved by the administrative reduction ─→ᵃ, hence by ≈.
------------------------------------------------------------------------

#acq-─→ᵃ : ∀ {n} {P Q : UP.Proc n} → P ─→ᵃ Q → #acq P ≡ #acq Q
#acq-─→ᵃ (RA.a-discard F V)         = refl
#acq-─→ᵃ (RA.a-sync {x = UP.drop} d) = #acq-─→ᵃ d
#acq-─→ᵃ (RA.a-sync {x = UP.acq}  d) = cong suc (#acq-─→ᵃ d)
#acq-─→ᵃ (RA.a-res d)                = #acq-─→ᵃ d
#acq-─→ᵃ (RA.a-par {R = Rr} d)       = cong (_+ #acq Rr) (#acq-─→ᵃ d)

#acq-≈ : ∀ {n} {P Q : UP.Proc n} → P ≈ Q → #acq P ≡ #acq Q
#acq-≈ ε                     = refl
#acq-≈ (fwd (inj₁ c) ◅ rest) = Eq.trans (#acq-≋ c)        (#acq-≈ rest)
#acq-≈ (fwd (inj₂ a) ◅ rest) = Eq.trans (#acq-─→ᵃ a)      (#acq-≈ rest)
#acq-≈ (bwd (inj₁ c) ◅ rest) = Eq.trans (sym (#acq-≋ c))  (#acq-≈ rest)
#acq-≈ (bwd (inj₂ a) ◅ rest) = Eq.trans (sym (#acq-─→ᵃ a)) (#acq-≈ rest)

------------------------------------------------------------------------
-- (4) A genuine φ-drop strictly increments #acq — so its redex and reduct
--     are NOT ≈-related.  The up-to-φ ε-absorption (P′ = P, Q ≈ U[ P ] σ)
--     is therefore unavailable for the νφ-comm φ-escape's drop step.
------------------------------------------------------------------------

-- exact RU-Drop redex / reduct (Reduction.Processes.Untyped.RU-Drop).
drop-redex : ∀ {n} (F : Frame* (1 + n)) (x : 𝔽 n) (P : UP.Proc (1 + n)) → UP.Proc n
drop-redex F x P = UP.φ UP.drop (UP.⟪ F [ K `drop ·¹ 𝓒[ * × suc x × ` 0F ] ]* ⟫ UP.∥ P)

drop-reduct : ∀ {n} (F : Frame* (1 + n)) (P : UP.Proc (1 + n)) → UP.Proc n
drop-reduct F P = UP.φ UP.acq (UP.⟪ F [ * ]* ⟫ UP.∥ P)

RU-Drop-#acq : ∀ {n} (F : Frame* (1 + n)) (x : 𝔽 n) (P : UP.Proc (1 + n))
             → #acq (drop-reduct F P) ≡ suc (#acq (drop-redex F x P))
RU-Drop-#acq F x P = refl

-- The redex and the reduct of a φ-drop are not ≈-related.
drop-not-≈ : ∀ {n} (F : Frame* (1 + n)) (x : 𝔽 n) (P : UP.Proc (1 + n))
           → ¬ (drop-redex F x P ≈ drop-reduct F P)
drop-not-≈ F x P rel = 1+n≢n (sym (Eq.trans (#acq-≈ rel) (RU-Drop-#acq F x P)))

-- Packaged for the engine: if  R ≈ U[P]σ  and  R  φ-drops to  Q, then
-- Q ≉ U[P]σ, so the reflection CANNOT be closed with ε typed steps (P′ = P).
ε-reflection-unavailable :
    ∀ {m n} {σ : m →ₛ n} {image : UP.Proc n}
      (F : Frame* (1 + n)) (x : 𝔽 n) (P₀ : UP.Proc (1 + n))
  → drop-redex F x P₀ ≈ image
  → ¬ (drop-reduct F P₀ ≈ image)
ε-reflection-unavailable F x P₀ R≈img Q≈img =
  1+n≢n (Eq.trans (sym (RU-Drop-#acq F x P₀))
                  (Eq.trans (#acq-≈ Q≈img) (sym (#acq-≈ R≈img))))
