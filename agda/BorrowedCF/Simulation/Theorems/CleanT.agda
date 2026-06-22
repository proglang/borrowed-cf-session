module BorrowedCF.Simulation.Theorems.CleanT where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.Untyped as 𝐔
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import BorrowedCF.Reduction.Processes.Typed as 𝐓R
import BorrowedCF.Reduction.Processes.Untyped as 𝐔R
open import BorrowedCF.Simulation.SubstLemmas
open import BorrowedCF.Simulation.BlockSwap
open import BorrowedCF.Simulation.Frames
open import BorrowedCF.Simulation.TranslationProperties
open import BorrowedCF.Simulation.Flatten
open import BorrowedCF.Simulation.BlockPermutation
open import BorrowedCF.Simulation.NuExtrusion
open import Data.Nat.Solver using (module +-*-Solver)
open import BorrowedCF.Simulation.Theorems.Toolkit

castDom-comm : ∀ sB₁ sB₂ sA₁ sA₂ {nn} →
  sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))) ≡ (sA₂ + (sA₁ + 2)) + ((sB₂ + (sB₁ + 2)) + nn)
castDom-comm sB₁ sB₂ sA₁ sA₂ {nn} =
  solve 5 (λ a b d e g →
    a :+ (b :+ (con 2 :+ (d :+ (e :+ (con 2 :+ g)))))
    := (a :+ (b :+ con 2)) :+ ((d :+ (e :+ con 2)) :+ g)) refl sA₂ sA₁ sB₂ sB₁ nn
  where open +-*-Solver

castCod-comm : ∀ sB₁ sB₂ sA₁ sA₂ {nn} →
  (sB₂ + (sB₁ + 2)) + ((sA₂ + (sA₁ + 2)) + nn) ≡ sB₂ + (sB₁ + (2 + (sA₂ + (sA₁ + (2 + nn)))))
castCod-comm sB₁ sB₂ sA₁ sA₂ {nn} =
  solve 5 (λ a b d e g →
    (d :+ (e :+ con 2)) :+ ((a :+ (b :+ con 2)) :+ g)
    := d :+ (e :+ (con 2 :+ (a :+ (b :+ (con 2 :+ g)))))) refl sA₂ sA₁ sB₂ sB₁ nn
  where open +-*-Solver

cleanT-comm : ∀ sB₁ sB₂ sA₁ sA₂ {nn} →
  sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))) →ᵣ sB₂ + (sB₁ + (2 + (sA₂ + (sA₁ + (2 + nn)))))
cleanT-comm sB₁ sB₂ sA₁ sA₂ {nn} =
  Fin.cast (castCod-comm sB₁ sB₂ sA₁ sA₂)
  ∘ assocSwapᵣ (sA₂ + (sA₁ + 2)) (sB₂ + (sB₁ + 2)) {nn}
  ∘ Fin.cast (castDom-comm sB₁ sB₂ sA₁ sA₂)

-- cleanT-comm's toℕ action (the block transpose), for reuse in the body reconciliation.
cleanTℕ-lt : ∀ sB₁ sB₂ sA₁ sA₂ {nn} (z : 𝔽 (sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))))) →
  Fin.toℕ z Nat.< sA₂ + (sA₁ + 2) →
  Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ z) ≡ (sB₂ + (sB₁ + 2)) + Fin.toℕ z
cleanTℕ-lt sB₁ sB₂ sA₁ sA₂ z lt =
    Fin.toℕ-cast (castCod-comm sB₁ sB₂ sA₁ sA₂) _
  ■ toℕ-assoc-lt (sA₂ + (sA₁ + 2)) (sB₂ + (sB₁ + 2)) (Fin.cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)
      (subst (Nat._< sA₂ + (sA₁ + 2)) (sym (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)) lt)
  ■ cong ((sB₂ + (sB₁ + 2)) +_) (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)

cleanTℕ-mid : ∀ sB₁ sB₂ sA₁ sA₂ {nn} (z : 𝔽 (sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))))) →
  sA₂ + (sA₁ + 2) Nat.≤ Fin.toℕ z → Fin.toℕ z Nat.< (sA₂ + (sA₁ + 2)) + (sB₂ + (sB₁ + 2)) →
  Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ z) ≡ Fin.toℕ z Nat.∸ (sA₂ + (sA₁ + 2))
cleanTℕ-mid sB₁ sB₂ sA₁ sA₂ z ge lt =
    Fin.toℕ-cast (castCod-comm sB₁ sB₂ sA₁ sA₂) _
  ■ toℕ-assoc-mid (sA₂ + (sA₁ + 2)) (sB₂ + (sB₁ + 2)) (Fin.cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)
      (subst (sA₂ + (sA₁ + 2) Nat.≤_) (sym (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)) ge)
      (subst (Nat._< (sA₂ + (sA₁ + 2)) + (sB₂ + (sB₁ + 2))) (sym (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)) lt)
  ■ cong (Nat._∸ (sA₂ + (sA₁ + 2))) (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)

cleanTℕ-ge : ∀ sB₁ sB₂ sA₁ sA₂ {nn} (z : 𝔽 (sA₂ + (sA₁ + (2 + (sB₂ + (sB₁ + (2 + nn))))))) →
  (sA₂ + (sA₁ + 2)) + (sB₂ + (sB₁ + 2)) Nat.≤ Fin.toℕ z →
  Fin.toℕ (cleanT-comm sB₁ sB₂ sA₁ sA₂ z) ≡ Fin.toℕ z
cleanTℕ-ge sB₁ sB₂ sA₁ sA₂ z ge =
    Fin.toℕ-cast (castCod-comm sB₁ sB₂ sA₁ sA₂) _
  ■ toℕ-assoc-ge (sA₂ + (sA₁ + 2)) (sB₂ + (sB₁ + 2)) (Fin.cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)
      (subst ((sA₂ + (sA₁ + 2)) + (sB₂ + (sB₁ + 2)) Nat.≤_) (sym (Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z)) ge)
  ■ Fin.toℕ-cast (castDom-comm sB₁ sB₂ sA₁ sA₂) z

-- ++ₛ reassociation under the +-assoc cast (for the leaf data permutation).
castˡˡ : ∀ a b {mm} (p : 𝔽 a) → Fin.cast (+-assoc a b mm) ((p ↑ˡ b) ↑ˡ mm) ≡ p ↑ˡ (b + mm)
castˡˡ a b {mm} p = Fin.toℕ-injective
  (Fin.toℕ-cast (+-assoc a b mm) ((p ↑ˡ b) ↑ˡ mm) ■ Fin.toℕ-↑ˡ (p ↑ˡ b) mm ■ Fin.toℕ-↑ˡ p b
   ■ sym (Fin.toℕ-↑ˡ p (b + mm)))

castˡʳ : ∀ a b {mm} (q : 𝔽 b) → Fin.cast (+-assoc a b mm) ((a ↑ʳ q) ↑ˡ mm) ≡ a ↑ʳ (q ↑ˡ mm)
castˡʳ a b {mm} q = Fin.toℕ-injective
  (Fin.toℕ-cast (+-assoc a b mm) ((a ↑ʳ q) ↑ˡ mm) ■ Fin.toℕ-↑ˡ (a ↑ʳ q) mm ■ Fin.toℕ-↑ʳ a q
   ■ sym (Fin.toℕ-↑ʳ a (q ↑ˡ mm) ■ cong (a +_) (Fin.toℕ-↑ˡ q mm)))

castʳ : ∀ a b {mm} (v : 𝔽 mm) → Fin.cast (+-assoc a b mm) ((a + b) ↑ʳ v) ≡ a ↑ʳ (b ↑ʳ v)
castʳ a b {mm} v = Fin.toℕ-injective
  (Fin.toℕ-cast (+-assoc a b mm) ((a + b) ↑ʳ v) ■ Fin.toℕ-↑ʳ (a + b) v ■ Nat.+-assoc a b (Fin.toℕ v)
   ■ sym (Fin.toℕ-↑ʳ a (b ↑ʳ v) ■ cong (a +_) (Fin.toℕ-↑ʳ b v)))

reassoc++ₛ : ∀ a b {mm} {D : ℕ} (Wa : a →ₛ D) (Wb : b →ₛ D) (Wm : mm →ₛ D) (k : 𝔽 ((a + b) + mm)) →
             ((Wa ++ₛ Wb) ++ₛ Wm) k ≡ (Wa ++ₛ (Wb ++ₛ Wm)) (Fin.cast (+-assoc a b mm) k)
reassoc++ₛ a b {mm} Wa Wb Wm k = helper (Fin.splitAt (a + b) k) (Fin.join-splitAt (a + b) mm k)
  where
    motive : 𝔽 ((a + b) + mm) → Set
    motive k = ((Wa ++ₛ Wb) ++ₛ Wm) k ≡ (Wa ++ₛ (Wb ++ₛ Wm)) (Fin.cast (+-assoc a b mm) k)
    helper : (s : 𝔽 (a + b) ⊎ 𝔽 mm) → Fin.join (a + b) mm s ≡ k → motive k
    helper (inj₂ v) jk = subst motive jk
      ( cong [ Wa ++ₛ Wb , Wm ]′ (Fin.splitAt-↑ʳ (a + b) mm v)
      ■ sym ( cong (Wa ++ₛ (Wb ++ₛ Wm)) (castʳ a b v)
            ■ cong [ Wa , Wb ++ₛ Wm ]′ (Fin.splitAt-↑ʳ a (b + mm) (b ↑ʳ v))
            ■ cong [ Wb , Wm ]′ (Fin.splitAt-↑ʳ b mm v) ) )
    helper (inj₁ u) jk = inner (Fin.splitAt a u) (Fin.join-splitAt a b u)
      where
        inner : (s′ : 𝔽 a ⊎ 𝔽 b) → Fin.join a b s′ ≡ u → motive k
        inner (inj₁ p) ju = subst motive (cong (_↑ˡ mm) ju ■ jk)
          ( cong [ Wa ++ₛ Wb , Wm ]′ (Fin.splitAt-↑ˡ (a + b) (p ↑ˡ b) mm)
          ■ cong [ Wa , Wb ]′ (Fin.splitAt-↑ˡ a p b)
          ■ sym ( cong (Wa ++ₛ (Wb ++ₛ Wm)) (castˡˡ a b p)
                ■ cong [ Wa , Wb ++ₛ Wm ]′ (Fin.splitAt-↑ˡ a p (b + mm)) ) )
        inner (inj₂ q) ju = subst motive (cong (_↑ˡ mm) ju ■ jk)
          ( cong [ Wa ++ₛ Wb , Wm ]′ (Fin.splitAt-↑ˡ (a + b) (a ↑ʳ q) mm)
          ■ cong [ Wa , Wb ]′ (Fin.splitAt-↑ʳ a b q)
          ■ sym ( cong (Wa ++ₛ (Wb ++ₛ Wm)) (castˡʳ a b q)
                ■ cong [ Wa , Wb ++ₛ Wm ]′ (Fin.splitAt-↑ʳ a (b + mm) (q ↑ˡ mm))
                ■ cong [ Wb , Wm ]′ (Fin.splitAt-↑ˡ b q mm) ) )

-- assocSwapᵣ permutes the first two ++ₛ blocks (right-nested), the leaf-permutation core.
assocSwap-++ₛ : ∀ a b {mm} {D : ℕ} (Wa : a →ₛ D) (Wb : b →ₛ D) (Wm : mm →ₛ D) →
                (assocSwapᵣ a b {mm} ·ₖ (Wb ++ₛ (Wa ++ₛ Wm))) ≗ (Wa ++ₛ (Wb ++ₛ Wm))
assocSwap-++ₛ a b {mm} Wa Wb Wm j =
    sym (reassoc++ₛ b a Wb Wa Wm (swapᵣ a b (Fin.cast (sym (+-assoc a b mm)) j)))
  ■ swap-++ₛ a b Wb Wa Wm (Fin.cast (sym (+-assoc a b mm)) j)
  ■ reassoc++ₛ a b Wa Wb Wm (Fin.cast (sym (+-assoc a b mm)) j)
  ■ cong (Wa ++ₛ (Wb ++ₛ Wm))
         (Fin.cast-trans (sym (+-assoc a b mm)) (+-assoc a b mm) j ■ Fin.cast-is-id _ j)

-- Transpose two ν-φ^-φ^ binder telescopes (engine-only).  COMPLETE & hole-free.
-- The body renaming TRANSP (the `_` in the conclusion) is inferred to the composite
--   r1 ·ₖ (r2 ·ₖ (r3 ·ₖ r4′))   (a 9-assocSwap block transpose; see the where-block).
-- PROOF SHAPE: phase-1 (φ^-ν-comm sB₂ ; φ^-ν-comm sB₁ ; ν-comm′ — bubble ν_A out and
-- swap ν_A/ν_B) → `consolidate` (push the 3 stacked assocSwaps onto X via φ^-⋯ₚ+fusionₚ)
-- → lift φ^sA₁ out (φ^-swap sB₂ sA₁ ; φ^-swap sB₁ sA₁ ; ν-φ^-comm sA₁) → `consolidate-2`
-- → lift φ^sA₂ out (φ^-swap sB₂ sA₂ ; φ^-swap sB₁ sA₂ ; ν-φ^-comm sA₂) → `consolidate-3`
-- → 3× fusionₚ to collapse the 4 stacked renamings on X into the single composite TRANSP.
-- NOTE for the caller (U-ν-comm phase 3): TRANSP is the RAW COMPOSITE — to reconcile
-- BODY ⋯ TRANSP you will first want `TRANSP ≗ assocSwapᵣ (sA₂+sA₁+2) (sB₂+sB₁+2)` (clean
-- block transpose, modulo +-assoc casts); a ~50-80 line toℕ proof.  See the handoff notes.
