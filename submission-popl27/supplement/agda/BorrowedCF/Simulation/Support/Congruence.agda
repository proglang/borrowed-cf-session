module BorrowedCF.Simulation.Support.Congruence where

-- | The (reworked) translation U[_] respects the typed structural congruence ≋.
--   Ported to the NEW (simpler) translation on git main: φ is a single Flag
--   binder; the heavy φ^ engine of the old development is gone.

open import BorrowedCF.Simulation.Support.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation.Support.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.Support.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; R2; R2'; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; wk·assocSwap; toℕ-weaken*ᵣ; weaken*ᵣ~↑ʳ
        ; toℕ-swapᵣ-lt; toℕ-swapᵣ-mid; toℕ-swapᵣ-ge
        ; toℕ-assoc-lt; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-reduce≥
        ; swap-place-A; swap-place-B; swap-place-tail; R'-fix-ge; toℕ-↑*-ge; toℕ-↑*-lt
        ; commuteS; wkSwap-cancel; assocSwap-invol
        ; toℕ-assoc↑*-fix-ge; toℕ-assoc↑*-lt; toℕ-wk↑*-lt; toℕ-wk↑*-ge; toℕ-swap↑*-ge
        ; assoc-place-lo; assoc-place-mid; assoc-place-tail )

open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import BorrowedCF.Simulation.Support.CongruenceH2 public

-- leaf reconcile for the ν-comm case (the nested analogue of subEq-gen).
subEqComm-gen : ∀ {m n} (σ : m →ₛ n) (A₁ A₂ B₁ B₂ : BindGroup) →
  let sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
      ρacc = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ω = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
  in (((leafσ (leafσ σ B₁ B₂) A₁ A₂ ·ₖ ((ρacc ↑* sA1) ↑* sA2))
         ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω
     ≗ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂) ·ₖ leafσ (leafσ σ A₁ A₂) B₁ B₂
subEqComm-gen {m} {n} σ A₁ A₂ B₁ B₂ i = body
  where
    a1 = sum A₁ ; a2 = sum A₂ ; b1 = sum B₁ ; b2 = sum B₂
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
    ρacc = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
    Ω = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
    -- the full body-renaming chain as a single composite
    Φ : (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
        →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
    Φ = (((((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω)
    -- Φ fixes the toℕ of any index that lies at or above the whole permuted prefix.
    Φ-fix-ge : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
               → sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ x
               → Fin.toℕ (Φ x) ≡ Fin.toℕ x
    Φ-fix-ge x ge = lΩ ■ l3 ■ l2 ■ l1
      where
        x1 = ((ρacc ↑* sA1) ↑* sA2) x
        x1N : Fin.toℕ x1 ≡ Fin.toℕ x
        x1N = lift-fix-ge (ρacc ↑* sA1) sA2 (sA1 + (2 + (sB2 + (sB1 + 2))))
                (λ w q → lift-fix-ge ρacc sA1 (2 + (sB2 + (sB1 + 2)))
                           (λ u q′ → ρacc-fix-ge sB1 sB2 u q′) w q) x ge
        x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
        x2N : Fin.toℕ x2 ≡ Fin.toℕ x1
        x2N = toℕ-assoc↑*-fix-ge sA2 sA1 sB2 x1
                (subst (sA2 + (sA1 + sB2) Nat.≤_) (sym x1N)
                  (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1
                    (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2)) (Nat.m≤n+m (sB2 + (sB1 + 2)) 2)))) ge))
        x3 = assocSwapᵣ sA2 sB2 x2
        x3N : Fin.toℕ x3 ≡ Fin.toℕ x2
        x3N = toℕ-assoc-ge sA2 sB2 x2
                (subst (sA2 + sB2 Nat.≤_) (sym (x2N ■ x1N))
                  (Nat.≤-trans (Nat.+-monoʳ-≤ sA2
                    (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2))
                      (Nat.≤-trans (Nat.m≤n+m (sB2 + (sB1 + 2)) 2) (Nat.m≤n+m _ sA1)))) ge))
        lΩ : Fin.toℕ (Ω x3) ≡ Fin.toℕ x3
        lΩ = lift-fix-ge _ sB2 (sA2 + (sA1 + (sB1 + 2)))
               (λ w q → ρω-fix-ge sA1 sA2 sB1 w q) x3 geΩ
          where
            geΩ : sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤ Fin.toℕ x3
            geΩ = subst (sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤_) (sym (x3N ■ x2N ■ x1N))
                    (Nat.≤-trans (Nat.≤-reflexive reassoc) (Nat.≤-trans bump ge))
              where reassoc : sB2 + (sA2 + (sA1 + (sB1 + 2))) ≡ sA2 + (sA1 + (sB2 + (sB1 + 2)))
                    reassoc = solve 4 (λ w u v t →
                                w :+ (u :+ (v :+ (t :+ con 2)))
                                := u :+ (v :+ (w :+ (t :+ con 2)))) refl sB2 sA2 sA1 sB1
                      where open +-*-Solver
                    bump : sA2 + (sA1 + (sB2 + (sB1 + 2))) Nat.≤ sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                    bump = Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.m≤n+m (sB2 + (sB1 + 2)) 2))
        l1 : Fin.toℕ x1 ≡ Fin.toℕ x
        l1 = x1N
        l2 : Fin.toℕ x2 ≡ Fin.toℕ x1
        l2 = x2N
        l3 : Fin.toℕ x3 ≡ Fin.toℕ x2
        l3 = x3N
    -- Φ reuses the module-level positional lemmas Φᵗ-A / Φᵗ-B.
    Φ-toℕ-A : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
              → Fin.toℕ x Nat.< sA2 + sA1
              → Fin.toℕ (Φ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
    Φ-toℕ-A x lt = Φᵗ-A sA1 sA2 sB1 sB2 x lt
    Φ-toℕ-B : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
              → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ x
              → Fin.toℕ x Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
              → Fin.toℕ (Φ x) ≡ Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
    Φ-toℕ-B x ge lt = Φᵗ-B sA1 sA2 sB1 sB2 x ge lt
    Φ-toℕ-Adata : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
                  → sA2 + sA1 Nat.≤ Fin.toℕ x
                  → Fin.toℕ x Nat.< sA2 + sA1 + 2
                  → Fin.toℕ (Φ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
    Φ-toℕ-Adata x ge lt = Φᵗ-Adata sA1 sA2 sB1 sB2 x ge lt
    -- fuse the four body-renaming factors applied to a term into a single Φ.
    fuseΦ : (t : Tm (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
            → t ⋯ ((ρacc ↑* sA1) ↑* sA2) ⋯ (assocSwapᵣ sA1 sB2 ↑* sA2) ⋯ assocSwapᵣ sA2 sB2 ⋯ Ω
            ≡ t ⋯ Φ
    fuseΦ t =
        cong (λ z → z ⋯ assocSwapᵣ sA2 sB2 ⋯ Ω)
          (fusion t ((ρacc ↑* sA1) ↑* sA2) (assocSwapᵣ sA1 sB2 ↑* sA2))
      ■ cong (_⋯ Ω)
          (fusion t (((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) (assocSwapᵣ sA2 sB2))
      ■ fusion t ((((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) Ω
    body : ((((leafσ (leafσ σ B₁ B₂) A₁ A₂ ·ₖ ((ρacc ↑* sA1) ↑* sA2))
               ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω) i
           ≡ (assocSwapᵣ (a1 + a2) (b1 + b2) ·ₖ leafσ (leafσ σ A₁ A₂) B₁ B₂) i
    body with Fin.splitAt (a1 + a2) i in eqo
    ... | inj₂ ii with Fin.splitAt (b1 + b2) ii in eqt
    ...   | inj₁ w with Fin.splitAt b1 w in eqw
    ...     | inj₁ jb =
                fuseΦ cB1t
              ■ midB1
              ■ sym rhsB1
              where
                cc₀ : UChan (2 + n)
                cc₀ = (K `unit , 0F , K `unit)
                cB1t = canonₛ B₁ cc₀ jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                         ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsB1 : leafσ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m))
                        ≡ canonₛ B₁ (K `unit , 0F , K `unit) jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsB1 =
                  leafσ-A₁ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m)) w jb
                    (Fin.splitAt-↑ˡ (b1 + b2) w (a1 + a2 + m)) eqw
                c₁ = canonₛ B₁ cc₀ jb
                assoc3 : (sA2 + (sA1 + 2)) + n ≡ sA2 + (sA1 + (2 + n))
                assoc3 = Nat.+-assoc sA2 (sA1 + 2) n ■ cong (sA2 +_) (Nat.+-assoc sA1 2 n)
                ρ₁ : (2 + n) →ᵣ (2 + (sA2 + (sA1 + (2 + n))))
                ρ₁ = λ y → Fin.cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) y)
                ρ₁0F : ρ₁ 0F ≡ 0F
                ρ₁0F = Fin.toℕ-injective (Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) 0F))
                ρ₁tailN : ∀ (k : 𝔽 n) → Fin.toℕ (ρ₁ (2 ↑ʳ k)) ≡ 2 + ((sA2 + (sA1 + 2)) + Fin.toℕ k)
                ρ₁tailN k = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) (2 ↑ʳ k))
                          ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 (2 ↑ʳ k) q2
                          ■ cong (2 +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ (2 ↑ʳ k) q2) ■ cong ((sA2 + (sA1 + 2)) +_) redk)
                  where q2 : 2 Nat.≤ Fin.toℕ (2 ↑ʳ k)
                        q2 = subst (2 Nat.≤_) (sym (Fin.toℕ-↑ʳ 2 k)) (Nat.m≤m+n 2 (Fin.toℕ k))
                        redk : Fin.toℕ (Fin.reduce≥ (2 ↑ʳ k) q2) ≡ Fin.toℕ k
                        redk = toℕ-reduce≥ (2 ↑ʳ k) q2 ■ cong (Nat._∸ 2) (Fin.toℕ-↑ʳ 2 k) ■ Nat.m+n∸m≡n 2 (Fin.toℕ k)
                wk4c : (sB1 + (2 + n)) →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
                wk4c = (((weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                Λ : (sB1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ = wk4c ·ₖ Φ
                wkc4eq : cB1t ≡ c₁ ⋯ wk4c
                wkc4eq =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
                  ■ fusion c₁ ((weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2)
                fuseΛ : cB1t ⋯ Φ ≡ c₁ ⋯ Λ
                fuseΛ = cong (_⋯ Φ) wkc4eq ■ fusion c₁ wk4c Φ
                ΛEq : Λ ≗ (ρ₁ ↑* sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
                ΛEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    wk4cN : Fin.toℕ (wk4c y) ≡ sA2 + (sA1 + (2 + (sB2 + Fin.toℕ y)))
                    wk4cN = toℕ-weaken*ᵣ sA2 _
                          ■ cong (sA2 +_) (toℕ-weaken*ᵣ sA1 _
                          ■ cong (sA1 +_) (cong (2 +_) (toℕ-weaken*ᵣ sB2 y)))
                    rhsN : Fin.toℕ (((ρ₁ ↑* sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) y)
                           ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    rhsN = toℕ-weaken*ᵣ sB2 ((ρ₁ ↑* sB1) y)
                    assocB : ∀ X → sA2 + (sA1 + (2 + X)) ≡ (sA2 + (sA1 + 2)) + X
                    assocB X = cong (sA2 +_) (sym (Nat.+-assoc sA1 2 X)) ■ sym (Nat.+-assoc sA2 (sA1 + 2) X)
                    ρ₁liftData : Fin.toℕ y Nat.< sB1 + 2 → sB1 Nat.≤ Fin.toℕ y → Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ Fin.toℕ y
                    ρ₁liftData ylt ge1 = toℕ-↑*-ge ρ₁ sB1 y ge1 ■ cong (sB1 +_) ρ₁red ■ Nat.m+[n∸m]≡n ge1
                      where
                        dd = Fin.toℕ y Nat.∸ sB1
                        dlt2 : dd Nat.< 2
                        dlt2 = Nat.+-cancelˡ-< sB1 dd 2 (subst (Nat._< sB1 + 2) (sym (Nat.m+[n∸m]≡n ge1)) ylt)
                        ρ₁red : Fin.toℕ (ρ₁ (Fin.reduce≥ y ge1)) ≡ dd
                        ρ₁red = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) (Fin.reduce≥ y ge1))
                              ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 (Fin.reduce≥ y ge1)
                                  (subst (Nat._< 2) (sym redy) dlt2)
                              ■ redy
                          where redy : Fin.toℕ (Fin.reduce≥ y ge1) ≡ dd
                                redy = toℕ-reduce≥ y ge1
                    ρ₁liftLow : Fin.toℕ y Nat.< sB1 + 2 → Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ Fin.toℕ y
                    ρ₁liftLow ylt with Nat.<-cmp (Fin.toℕ y) sB1
                    ... | tri< ylt1 _ _ = toℕ-↑*-lt ρ₁ sB1 y ylt1
                    ... | tri≈ _ yeq1 _ = ρ₁liftData ylt (Nat.≤-reflexive (sym yeq1))
                    ... | tri> _ _ ygt1 = ρ₁liftData ylt (Nat.<⇒≤ ygt1)
                    tailEq : sB1 + 2 Nat.≤ Fin.toℕ y → Fin.toℕ (Λ y) ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    tailEq ge2 = Φ-fix-ge (wk4c y) geΦ ■ wk4cN ■ assocFinal ■ sym (cong (sB2 +_) ρ₁high)
                      where
                        d2 = Fin.toℕ y Nat.∸ (sB1 + 2)
                        yd : (sB1 + 2) + d2 ≡ Fin.toℕ y
                        yd = Nat.m+[n∸m]≡n ge2
                        ge1 : sB1 Nat.≤ Fin.toℕ y
                        ge1 = Nat.≤-trans (Nat.m≤m+n sB1 2) ge2
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (wk4c y)
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wk4cN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2
                                  (Nat.+-monoʳ-≤ sB2 ge2))))
                        z = Fin.reduce≥ y ge1
                        zN : Fin.toℕ z ≡ 2 + d2
                        zN = toℕ-reduce≥ y ge1 ■ red2
                          where red2 : Fin.toℕ y Nat.∸ sB1 ≡ 2 + d2
                                red2 = cong (Nat._∸ sB1) (sym yd) ■ cong (Nat._∸ sB1) (Nat.+-assoc sB1 2 d2) ■ Nat.m+n∸m≡n sB1 (2 + d2)
                        z2 : 2 Nat.≤ Fin.toℕ z
                        z2 = subst (2 Nat.≤_) (sym zN) (Nat.m≤m+n 2 d2)
                        ρ₁zN : Fin.toℕ (ρ₁ z) ≡ 2 + ((sA2 + (sA1 + 2)) + d2)
                        ρ₁zN = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) z)
                             ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 z z2
                             ■ cong (2 +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ z z2)
                                 ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ z z2 ■ cong (Nat._∸ 2) zN ■ Nat.m+n∸m≡n 2 d2))
                        ρ₁high : Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ sB1 + (2 + ((sA2 + (sA1 + 2)) + d2))
                        ρ₁high = toℕ-↑*-ge ρ₁ sB1 y ge1 ■ cong (sB1 +_) ρ₁zN
                        assocFinal : sA2 + (sA1 + (2 + (sB2 + Fin.toℕ y))) ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d2)))
                        assocFinal = cong (λ w → sA2 + (sA1 + (2 + (sB2 + w)))) (sym yd) ■ solveFinal
                          where open +-*-Solver
                                solveFinal : sA2 + (sA1 + (2 + (sB2 + ((sB1 + 2) + d2))))
                                             ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d2)))
                                solveFinal = solve 5 (λ a2 a1 b2 b1 t →
                                                a2 :+ (a1 :+ (con 2 :+ (b2 :+ ((b1 :+ con 2) :+ t))))
                                                := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ t))))
                                              refl sA2 sA1 sB2 sB1 d2
                    lhsN : Fin.toℕ (Λ y) ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    lhsN with Nat.<-cmp (Fin.toℕ y) (sB1 + 2)
                    ... | tri< ylt _ _ =
                            Φ-toℕ-B (wk4c y) geB ltB
                          ■ cong (Nat._∸ (sA2 + (sA1 + 2))) (wk4cN ■ assocB (sB2 + Fin.toℕ y))
                          ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ y)
                          ■ sym (cong (sB2 +_) (ρ₁liftLow ylt))
                      where
                        geB : sA2 + (sA1 + 2) Nat.≤ Fin.toℕ (wk4c y)
                        geB = subst (sA2 + (sA1 + 2) Nat.≤_) (sym wk4cN)
                                (subst (sA2 + (sA1 + 2) Nat.≤_) (sym (assocB (sB2 + Fin.toℕ y)))
                                  (Nat.m≤m+n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ y)))
                        ltB : Fin.toℕ (wk4c y) Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                        ltB = subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) (sym wk4cN)
                                (Nat.+-monoʳ-< sA2 (Nat.+-monoʳ-< sA1 (Nat.+-monoʳ-< 2
                                  (Nat.+-monoʳ-< sB2 ylt))))
                    ... | tri≈ _ yeq _ = tailEq (Nat.≤-reflexive (sym yeq))
                    ... | tri> _ _ ygt = tailEq (Nat.<⇒≤ ygt)
                mapcc : mapᶜ ρ₁ cc₀ ≡ (K `unit , 0F , K `unit)
                mapcc = cong₂ _,_ refl (cong₂ _,_ ρ₁0F refl)
                midB1 : cB1t ⋯ Φ ≡ canonₛ B₁ (K `unit , 0F , K `unit) jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midB1 =
                    fuseΛ
                  ■ ⋯-cong (canonₛ B₁ cc₀ jb) ΛEq
                  ■ sym (fusion (canonₛ B₁ cc₀ jb) (ρ₁ ↑* sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2) (canonₛ-nat B₁ cc₀ ρ₁ jb)
                  ■ cong (λ c → canonₛ B₁ c jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2) mapcc
    ...     | inj₂ kb =
                fuseΦ cB2t
              ■ midB2
              ■ sym rhsB2
              where
                flagIdx : 𝔽 (sB1 + (2 + n))
                flagIdx = weaken* ⦃ Kᵣ ⦄ sB1 1F
                cc₂ : UChan (sB1 + (2 + n))
                cc₂ = (K `unit , flagIdx , K `unit)
                c₂ = canonₛ B₂ cc₂ kb
                cB2t = c₂ ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsB2 : leafσ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m))
                        ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) kb
                rhsB2 =
                  leafσ-B₁ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m)) w kb
                    (Fin.splitAt-↑ˡ (b1 + b2) w (a1 + a2 + m)) eqw
                assoc3 : (sA2 + (sA1 + 2)) + n ≡ sA2 + (sA1 + (2 + n))
                assoc3 = Nat.+-assoc sA2 (sA1 + 2) n ■ cong (sA2 +_) (Nat.+-assoc sA1 2 n)
                assocIn : (sB1 + 2) + n ≡ sB1 + (2 + n)
                assocIn = Nat.+-assoc sB1 2 n
                assocOut : (sB1 + 2) + ((sA2 + (sA1 + 2)) + n) ≡ sB1 + (2 + (sA2 + (sA1 + (2 + n))))
                assocOut = Nat.+-assoc sB1 2 ((sA2 + (sA1 + 2)) + n) ■ cong (sB1 +_) (cong (2 +_) assoc3)
                ρ₂ : (sB1 + (2 + n)) →ᵣ (sB1 + (2 + (sA2 + (sA1 + (2 + n)))))
                ρ₂ = λ y → Fin.cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) y))
                flagN : Fin.toℕ flagIdx ≡ sB1 + 1
                flagN = toℕ-weaken*ᵣ sB1 1F
                ρ₂flag : ρ₂ flagIdx ≡ weaken* ⦃ Kᵣ ⦄ sB1 1F
                ρ₂flag = Fin.toℕ-injective
                  ( Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) flagIdx))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) flagIdx) flagLt
                  ■ castN
                  ■ sym (toℕ-weaken*ᵣ sB1 1F) )
                  where castN : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) ≡ sB1 + 1
                        castN = Fin.toℕ-cast (sym assocIn) flagIdx ■ flagN
                        flagLt : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) Nat.< sB1 + 2
                        flagLt = subst (Nat._< sB1 + 2) (sym castN) (Nat.+-monoʳ-< sB1 (Nat.s≤s (Nat.s≤s Nat.z≤n)))
                wk3c : (sB2 + (sB1 + (2 + n))) →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
                wk3c = ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                Λ₂ : (sB2 + (sB1 + (2 + n))) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ₂ = wk3c ·ₖ Φ
                wkc3eq : cB2t ≡ c₂ ⋯ wk3c
                wkc3eq =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
                  ■ fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2)
                fuseΛ₂ : cB2t ⋯ Φ ≡ c₂ ⋯ Λ₂
                fuseΛ₂ = cong (_⋯ Φ) wkc3eq ■ fusion c₂ wk3c Φ
                ρ₂N-low : ∀ (z : 𝔽 (sB1 + (2 + n))) → Fin.toℕ z Nat.< sB1 + 2 → Fin.toℕ (ρ₂ z) ≡ Fin.toℕ z
                ρ₂N-low z zlt =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) z))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) z)
                      (subst (Nat._< sB1 + 2) (sym (Fin.toℕ-cast (sym assocIn) z)) zlt)
                  ■ Fin.toℕ-cast (sym assocIn) z
                ρ₂N-high : ∀ (z : 𝔽 (sB1 + (2 + n))) → sB1 + 2 Nat.≤ Fin.toℕ z →
                           Fin.toℕ (ρ₂ z) ≡ sB1 + (2 + ((sA2 + (sA1 + 2)) + (Fin.toℕ z Nat.∸ (sB1 + 2))))
                ρ₂N-high z zge =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) z))
                  ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) z) zge'
                  ■ cong ((sB1 + 2) +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ (Fin.cast (sym assocIn) z) zge')
                      ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ (Fin.cast (sym assocIn) z) zge' ■ cong (Nat._∸ (sB1 + 2)) (Fin.toℕ-cast (sym assocIn) z)))
                  ■ Nat.+-assoc sB1 2 ((sA2 + (sA1 + 2)) + (Fin.toℕ z Nat.∸ (sB1 + 2)))
                  where zge' : sB1 + 2 Nat.≤ Fin.toℕ (Fin.cast (sym assocIn) z)
                        zge' = subst (sB1 + 2 Nat.≤_) (sym (Fin.toℕ-cast (sym assocIn) z)) zge
                Λ₂Eq : Λ₂ ≗ ρ₂ ↑* sB2
                Λ₂Eq y = Fin.toℕ-injective lhsN
                  where
                    wk3cN : Fin.toℕ (wk3c y) ≡ sA2 + (sA1 + (2 + Fin.toℕ y))
                    wk3cN = toℕ-weaken*ᵣ sA2 _
                          ■ cong (sA2 +_) (toℕ-weaken*ᵣ sA1 _ ■ cong (sA1 +_) (toℕ-weaken*ᵣ 2 y))
                    assocB : ∀ X → sA2 + (sA1 + (2 + X)) ≡ (sA2 + (sA1 + 2)) + X
                    assocB X = cong (sA2 +_) (sym (Nat.+-assoc sA1 2 X)) ■ sym (Nat.+-assoc sA2 (sA1 + 2) X)
                    ρ₂liftData : Fin.toℕ y Nat.< sB2 + (sB1 + 2) → sB2 Nat.≤ Fin.toℕ y → Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ Fin.toℕ y
                    ρ₂liftData ylt ge1 = toℕ-↑*-ge ρ₂ sB2 y ge1 ■ cong (sB2 +_) (ρ₂N-low (Fin.reduce≥ y ge1) redlt ■ toℕ-reduce≥ y ge1) ■ Nat.m+[n∸m]≡n ge1
                      where redlt : Fin.toℕ (Fin.reduce≥ y ge1) Nat.< sB1 + 2
                            redlt = subst (Nat._< sB1 + 2) (sym (toℕ-reduce≥ y ge1))
                                      (Nat.+-cancelˡ-< sB2 _ (sB1 + 2)
                                        (subst (Nat._< sB2 + (sB1 + 2)) (sym (Nat.m+[n∸m]≡n ge1)) ylt))
                    ρ₂liftLow : Fin.toℕ y Nat.< sB2 + (sB1 + 2) → Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ Fin.toℕ y
                    ρ₂liftLow ylt with Nat.<-cmp (Fin.toℕ y) sB2
                    ... | tri< ylt1 _ _ = toℕ-↑*-lt ρ₂ sB2 y ylt1
                    ... | tri≈ _ yeq1 _ = ρ₂liftData ylt (Nat.≤-reflexive (sym yeq1))
                    ... | tri> _ _ ygt1 = ρ₂liftData ylt (Nat.<⇒≤ ygt1)
                    tailEq : sB2 + (sB1 + 2) Nat.≤ Fin.toℕ y → Fin.toℕ (Λ₂ y) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                    tailEq ge3 = Φ-fix-ge (wk3c y) geΦ ■ wk3cN ■ tailEq2
                      where
                        d3 = Fin.toℕ y Nat.∸ (sB2 + (sB1 + 2))
                        yd : (sB2 + (sB1 + 2)) + d3 ≡ Fin.toℕ y
                        yd = Nat.m+[n∸m]≡n ge3
                        ge2 : sB2 Nat.≤ Fin.toℕ y
                        ge2 = Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2)) ge3
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (wk3c y)
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wk3cN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 ge3)))
                        z = Fin.reduce≥ y ge2
                        zN : Fin.toℕ z ≡ (sB1 + 2) + d3
                        zN = toℕ-reduce≥ y ge2 ■ red2
                          where red2 : Fin.toℕ y Nat.∸ sB2 ≡ (sB1 + 2) + d3
                                red2 = cong (Nat._∸ sB2) (sym yd) ■ cong (Nat._∸ sB2) (Nat.+-assoc sB2 (sB1 + 2) d3) ■ Nat.m+n∸m≡n sB2 ((sB1 + 2) + d3)
                        zge : sB1 + 2 Nat.≤ Fin.toℕ z
                        zge = subst (sB1 + 2 Nat.≤_) (sym zN) (Nat.m≤m+n (sB1 + 2) d3)
                        ρ₂high : Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d3)))
                        ρ₂high = toℕ-↑*-ge ρ₂ sB2 y ge2 ■ cong (sB2 +_) (ρ₂N-high z zge ■ cong (λ w → sB1 + (2 + ((sA2 + (sA1 + 2)) + w))) zd3)
                          where zd3 : Fin.toℕ z Nat.∸ (sB1 + 2) ≡ d3
                                zd3 = cong (Nat._∸ (sB1 + 2)) zN ■ Nat.m+n∸m≡n (sB1 + 2) d3
                        tailEq2 : sA2 + (sA1 + (2 + Fin.toℕ y)) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                        tailEq2 = cong (λ w → sA2 + (sA1 + (2 + w))) (sym yd) ■ solveT ■ sym ρ₂high
                          where open +-*-Solver
                                solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + d3)))
                                         ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d3)))
                                solveT = solve 5 (λ a2 a1 b2 b1 t →
                                            a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ t)))
                                            := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ t))))
                                          refl sA2 sA1 sB2 sB1 d3
                    lhsN : Fin.toℕ (Λ₂ y) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                    lhsN with Nat.<-cmp (Fin.toℕ y) (sB2 + (sB1 + 2))
                    ... | tri< ylt _ _ =
                            Φ-toℕ-B (wk3c y) geB ltB
                          ■ cong (Nat._∸ (sA2 + (sA1 + 2))) (wk3cN ■ assocB (Fin.toℕ y))
                          ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (Fin.toℕ y)
                          ■ sym (ρ₂liftLow ylt)
                      where
                        geB : sA2 + (sA1 + 2) Nat.≤ Fin.toℕ (wk3c y)
                        geB = subst (sA2 + (sA1 + 2) Nat.≤_) (sym wk3cN)
                                (subst (sA2 + (sA1 + 2) Nat.≤_) (sym (assocB (Fin.toℕ y)))
                                  (Nat.m≤m+n (sA2 + (sA1 + 2)) (Fin.toℕ y)))
                        ltB : Fin.toℕ (wk3c y) Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                        ltB = subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) (sym wk3cN)
                                (Nat.+-monoʳ-< sA2 (Nat.+-monoʳ-< sA1 (Nat.+-monoʳ-< 2 ylt)))
                    ... | tri≈ _ yeq _ = tailEq (Nat.≤-reflexive (sym yeq))
                    ... | tri> _ _ ygt = tailEq (Nat.<⇒≤ ygt)
                mapcc2 : mapᶜ ρ₂ cc₂ ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit)
                mapcc2 = cong₂ _,_ refl (cong₂ _,_ ρ₂flag refl)
                midB2 : cB2t ⋯ Φ ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) kb
                midB2 =
                    fuseΛ₂
                  ■ ⋯-cong c₂ Λ₂Eq
                  ■ canonₛ-nat B₂ cc₂ ρ₂ kb
                  ■ cong (λ c → canonₛ B₂ c kb) mapcc2
    body | inj₂ ii | inj₂ jj =
        fuseΦ wk6t
      ■ fuseWk
      ■ ⋯-cong (σ jj) renEq
      ■ sym fuseSmall
      ■ sym rhsσ
      where
        wk6t = σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                      ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
        wk6c : n →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
        wk6c = (((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
                 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
        renSmall : n →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
        renSmall = ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                   ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
        -- fuse the 6 weakens into wk6c (so wk6t ⋯ Φ = σ jj ⋯ (wk6c ·ₖ Φ))
        fuseWk : wk6t ⋯ Φ ≡ σ jj ⋯ (wk6c ·ₖ Φ)
        fuseWk =
            cong (λ t → t ⋯ Φ)
              ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
              ■ fusion (σ jj) ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) )
          ■ fusion (σ jj) wk6c Φ
        -- the key renaming identity (all images land high; Φ fixes them).
        renEq : (wk6c ·ₖ Φ) ≗ renSmall
        renEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
          where
            w6 = wk6c y
            highw6 : Fin.toℕ w6 ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            highw6 =
                toℕ-weaken*ᵣ sA2 _
              ■ cong (sA2 +_) ( toℕ-weaken*ᵣ sA1 _
              ■ cong (sA1 +_) (cong (2 +_) ( toℕ-weaken*ᵣ sB2 _
              ■ cong (sB2 +_) ( toℕ-weaken*ᵣ sB1 _
              ■ cong (sB1 +_) refl ) )) )
            geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ w6
            geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym highw6)
                    (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2
                      (Nat.+-monoʳ-≤ sB2 (Nat.+-monoʳ-≤ sB1 (Nat.+-monoʳ-≤ 2 Nat.z≤n))))))
            lhsN : Fin.toℕ ((wk6c ·ₖ Φ) y) ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            lhsN = Φ-fix-ge w6 geΦ ■ highw6
            rhsN : Fin.toℕ (renSmall y) ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            rhsN =
                ( toℕ-weaken*ᵣ sB2 _
                ■ cong (sB2 +_) ( toℕ-weaken*ᵣ sB1 _
                ■ cong (sB1 +_) (cong (2 +_) ( toℕ-weaken*ᵣ sA2 _
                ■ cong (sA2 +_) ( toℕ-weaken*ᵣ sA1 _
                ■ cong (sA1 +_) refl ) )) ) )
              ■ blockComm sB2 sB1 sA2 sA1 (Fin.toℕ y)
        fuseSmall : σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                    ≡ σ jj ⋯ renSmall
        fuseSmall =
            cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
          ■ fusion (σ jj) ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2)
        rhsσ : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ ((a1 + a2) ↑ʳ jj))
               ≡ σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                       ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
        rhsσ =
            leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ ((a1 + a2) ↑ʳ jj)) ((a1 + a2) ↑ʳ jj)
              (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) ((a1 + a2) ↑ʳ jj))
          ■ cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (leafσ-tail σ A₁ A₂ ((a1 + a2) ↑ʳ jj) jj (Fin.splitAt-↑ʳ (a1 + a2) m jj))
    body | inj₁ z with Fin.splitAt a1 z in eqi
    ...   | inj₁ j =
                fuseΦ cA1t
              ■ midA1
              ■ sym rhsA1
              where
                cc₀ : UChan (2 + n)
                cc₀ = (K `unit , 0F , K `unit)
                cc₀big : UChan (2 + (sB2 + (sB1 + (2 + n))))
                cc₀big = (K `unit , 0F , K `unit)
                cA1t = canonₛ A₁ cc₀big j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsA1 : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m))
                        ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsA1 =
                    leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m)) (z ↑ˡ m)
                      (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) (z ↑ˡ m))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                      (leafσ-A₁ σ A₁ A₂ (z ↑ˡ m) z j (Fin.splitAt-↑ˡ (a1 + a2) z m) eqi)
                c₁ = canonₛ A₁ cc₀ j
                assoc-A : (sB2 + (sB1 + 2)) + n ≡ sB2 + (sB1 + (2 + n))
                assoc-A = Nat.+-assoc sB2 (sB1 + 2) n ■ cong (sB2 +_) (Nat.+-assoc sB1 2 n)
                ρA : (2 + n) →ᵣ (2 + (sB2 + (sB1 + (2 + n))))
                ρA = λ y → Fin.cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) y)
                ρA0F : ρA 0F ≡ 0F
                ρA0F = Fin.toℕ-injective (Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) 0F))
                mapcc : mapᶜ ρA cc₀ ≡ (K `unit , 0F , K `unit)
                mapcc = cong₂ _,_ refl (cong₂ _,_ ρA0F refl)
                ΨLHS : (sA1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                ΨLHS = ((ρA ↑* sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ Φ
                ΨRHS : (sA1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                ΨRHS = ((weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
                fuseL : cA1t ⋯ Φ ≡ c₁ ⋯ ΨLHS
                fuseL =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ Φ)
                      (sym (canonₛ-nat A₁ cc₀ ρA j ■ cong (λ c → canonₛ A₁ c j) mapcc))
                  ■ cong (_⋯ Φ) (fusion c₁ (ρA ↑* sA1) (weaken* ⦃ Kᵣ ⦄ sA2))
                  ■ fusion c₁ ((ρA ↑* sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) Φ
                fuseR : c₁ ⋯ ΨRHS
                        ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                fuseR =
                    sym ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                            (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2))
                        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                            (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
                        ■ fusion c₁ ((weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2) )
                ΨEq : ΨLHS ≗ ΨRHS
                ΨEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    t = Fin.toℕ y
                    rhsN : Fin.toℕ (ΨRHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    rhsN = toℕ-weaken*ᵣ sB2 _
                         ■ cong (sB2 +_) (toℕ-weaken*ᵣ sB1 _
                         ■ cong (sB1 +_) (toℕ-weaken*ᵣ 2 _
                         ■ cong (2 +_) (toℕ-weaken*ᵣ sA2 y)))
                    dataEq : sA1 Nat.≤ t → t Nat.< sA1 + 2 → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    dataEq ge2 lt2 = Φ-toℕ-Adata (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) wge wlt
                                   ■ cong ((sB2 + (sB1 + 2)) +_) wN
                                   ■ solveD
                      where
                        dd = t Nat.∸ sA1
                        td : sA1 + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge2
                        ddlt2 : dd Nat.< 2
                        ddlt2 = Nat.+-cancelˡ-< sA1 dd 2 (subst (Nat._< sA1 + 2) (sym td) lt2)
                        ρAred : Fin.toℕ (ρA (Fin.reduce≥ y ge2)) ≡ dd
                        ρAred = Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) (Fin.reduce≥ y ge2))
                              ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) 2 (Fin.reduce≥ y ge2)
                                  (subst (Nat._< 2) (sym redy) ddlt2)
                              ■ redy
                          where redy : Fin.toℕ (Fin.reduce≥ y ge2) ≡ dd
                                redy = toℕ-reduce≥ y ge2
                        ρAhigh : Fin.toℕ ((ρA ↑* sA1) y) ≡ t
                        ρAhigh = toℕ-↑*-ge ρA sA1 y ge2 ■ cong (sA1 +_) ρAred ■ td
                        wN : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + t
                        wN = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) ρAhigh
                        wge : sA2 + sA1 Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y))
                        wge = subst (sA2 + sA1 Nat.≤_) (sym wN) (Nat.+-monoʳ-≤ sA2 ge2)
                        wlt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) Nat.< sA2 + sA1 + 2
                        wlt = subst (Nat._< sA2 + sA1 + 2) (sym wN)
                                (subst (Nat._< sA2 + sA1 + 2) (Nat.+-assoc sA2 sA1 dd ■ cong (sA2 +_) td)
                                  (Nat.+-monoʳ-< (sA2 + sA1) ddlt2))
                        open +-*-Solver
                        solveD : (sB2 + (sB1 + 2)) + (sA2 + t) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        solveD = solve 4 (λ b2 b1 a2 s →
                                    (b2 :+ (b1 :+ con 2)) :+ (a2 :+ s)
                                    := b2 :+ (b1 :+ (con 2 :+ (a2 :+ s)))) refl sB2 sB1 sA2 t
                    tailEq : sA1 + 2 Nat.≤ t → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    tailEq ge2 = Φ-fix-ge (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) geΦ ■ wN ■ solveT
                      where
                        dd = t Nat.∸ (sA1 + 2)
                        td : (sA1 + 2) + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge2
                        ge1 : sA1 Nat.≤ t
                        ge1 = Nat.≤-trans (Nat.m≤m+n sA1 2) ge2
                        red0 = Fin.reduce≥ y ge1
                        red0N : Fin.toℕ red0 ≡ 2 + dd
                        red0N = toℕ-reduce≥ y ge1 ■ red2
                          where red2 : t Nat.∸ sA1 ≡ 2 + dd
                                red2 = cong (Nat._∸ sA1) (sym td) ■ cong (Nat._∸ sA1) (Nat.+-assoc sA1 2 dd) ■ Nat.m+n∸m≡n sA1 (2 + dd)
                        red0ge2 : 2 Nat.≤ Fin.toℕ red0
                        red0ge2 = subst (2 Nat.≤_) (sym red0N) (Nat.m≤m+n 2 dd)
                        ρAred : Fin.toℕ (ρA red0) ≡ 2 + ((sB2 + (sB1 + 2)) + dd)
                        ρAred = Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) red0)
                              ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) 2 red0 red0ge2
                              ■ cong (2 +_) (toℕ-weaken*ᵣ (sB2 + (sB1 + 2)) (Fin.reduce≥ red0 red0ge2)
                                  ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ red0 red0ge2 ■ cong (Nat._∸ 2) red0N ■ Nat.m+n∸m≡n 2 dd))
                        ρAhigh : Fin.toℕ ((ρA ↑* sA1) y) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))
                        ρAhigh = toℕ-↑*-ge ρA sA1 y ge1 ■ cong (sA1 +_) ρAred
                        wN : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd)))
                        wN = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) ρAhigh
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y))
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n (sB2 + (sB1 + 2)) dd))))
                        open +-*-Solver
                        solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        solveT = solve 5 (λ a2 a1 b2 b1 w →
                                    a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ w)))
                                    := b2 :+ (b1 :+ (con 2 :+ (a2 :+ ((a1 :+ con 2) :+ w))))) refl sA2 sA1 sB2 sB1 dd
                               ■ cong (λ w → sB2 + (sB1 + (2 + (sA2 + w)))) td
                    lhsN : Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    lhsN with Nat.<-cmp t sA1
                    ... | tri< tlt _ _ = lowEq
                      where
                        lA : Fin.toℕ ((ρA ↑* sA1) y) ≡ t
                        lA = toℕ-↑*-lt ρA sA1 y tlt
                        wA : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + t
                        wA = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) lA
                        wlt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) Nat.< sA2 + sA1
                        wlt = subst (Nat._< sA2 + sA1) (sym wA) (Nat.+-monoʳ-< sA2 tlt)
                        lowEq : Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        lowEq = Φ-toℕ-A (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) wlt
                              ■ cong ((sB2 + (sB1 + 2)) +_) wA
                              ■ solveLow
                          where open +-*-Solver
                                solveLow : (sB2 + (sB1 + 2)) + (sA2 + t) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                                solveLow = solve 4 (λ b2 b1 a2 s →
                                              (b2 :+ (b1 :+ con 2)) :+ (a2 :+ s)
                                              := b2 :+ (b1 :+ (con 2 :+ (a2 :+ s)))) refl sB2 sB1 sA2 t
                    ... | tri≈ _ teq _ = dataEq (Nat.≤-reflexive (sym teq))
                                          (subst (Nat._< sA1 + 2) (sym teq) sA1<sA1+2)
                      where sA1<sA1+2 : sA1 Nat.< sA1 + 2
                            sA1<sA1+2 = Nat.≤-<-trans (Nat.≤-reflexive (sym (Nat.+-identityʳ sA1))) (Nat.+-monoʳ-< sA1 (Nat.s≤s Nat.z≤n))
                    ... | tri> _ _ tgt = highEq tgt
                      where
                        highEq : sA1 Nat.< t → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        highEq tg with Nat.<-cmp t (sA1 + 2)
                        ... | tri< tlt2 _ _ = dataEq (Nat.<⇒≤ tg) tlt2
                        ... | tri≈ _ teq2 _ = tailEq (Nat.≤-reflexive (sym teq2))
                        ... | tri> _ _ tgt2 = tailEq (Nat.<⇒≤ tgt2)
                midA1 : cA1t ⋯ Φ ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midA1 = fuseL ■ ⋯-cong c₁ ΨEq ■ fuseR
    ...   | inj₂ k =
                fuseΦ cA2t
              ■ midA2
              ■ sym rhsA2
              where
                flagIdx : 𝔽 (sA1 + (2 + n))
                flagIdx = weaken* ⦃ Kᵣ ⦄ sA1 1F
                cc₂big : UChan (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
                cc₂big = (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                cc₂ : UChan (sA1 + (2 + n))
                cc₂ = (K `unit , flagIdx , K `unit)
                c₂ = canonₛ A₂ cc₂ k
                cA2t = canonₛ A₂ cc₂big k
                rhsA2 : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m))
                        ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) k
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsA2 =
                    leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m)) (z ↑ˡ m)
                      (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) (z ↑ˡ m))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                      (leafσ-B₁ σ A₁ A₂ (z ↑ˡ m) z k (Fin.splitAt-↑ˡ (a1 + a2) z m) eqi)
                assocIn : (sA1 + 2) + n ≡ sA1 + (2 + n)
                assocIn = Nat.+-assoc sA1 2 n
                assocOut : (sA1 + 2) + ((sB2 + (sB1 + 2)) + n) ≡ sA1 + (2 + (sB2 + (sB1 + (2 + n))))
                assocOut = Nat.+-assoc sA1 2 ((sB2 + (sB1 + 2)) + n)
                         ■ cong (sA1 +_) (cong (2 +_) (Nat.+-assoc sB2 (sB1 + 2) n ■ cong (sB2 +_) (Nat.+-assoc sB1 2 n)))
                ρ₂ : (sA1 + (2 + n)) →ᵣ (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
                ρ₂ = λ y → Fin.cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) y))
                flagN : Fin.toℕ flagIdx ≡ sA1 + 1
                flagN = toℕ-weaken*ᵣ sA1 1F
                ρ₂flag : ρ₂ flagIdx ≡ weaken* ⦃ Kᵣ ⦄ sA1 1F
                ρ₂flag = Fin.toℕ-injective
                  ( Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) flagIdx))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) flagIdx) flagLt
                  ■ castN
                  ■ sym (toℕ-weaken*ᵣ sA1 1F) )
                  where castN : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) ≡ sA1 + 1
                        castN = Fin.toℕ-cast (sym assocIn) flagIdx ■ flagN
                        flagLt : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) Nat.< sA1 + 2
                        flagLt = subst (Nat._< sA1 + 2) (sym castN) (Nat.+-monoʳ-< sA1 (Nat.s≤s (Nat.s≤s Nat.z≤n)))
                mapcc2 : mapᶜ ρ₂ cc₂ ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                mapcc2 = cong₂ _,_ refl (cong₂ _,_ ρ₂flag refl)
                Λ₂ : (sA2 + (sA1 + (2 + n))) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ₂ = (ρ₂ ↑* sA2) ·ₖ Φ
                fuseL : cA2t ⋯ Φ ≡ c₂ ⋯ Λ₂
                fuseL =
                    cong (_⋯ Φ)
                      (sym (canonₛ-nat A₂ cc₂ ρ₂ k ■ cong (λ c → canonₛ A₂ c k) mapcc2))
                  ■ fusion c₂ (ρ₂ ↑* sA2) Φ
                ρ₂N-low : ∀ (z′ : 𝔽 (sA1 + (2 + n))) → Fin.toℕ z′ Nat.< sA1 + 2 → Fin.toℕ (ρ₂ z′) ≡ Fin.toℕ z′
                ρ₂N-low z′ zlt =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) z′))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) z′)
                      (subst (Nat._< sA1 + 2) (sym (Fin.toℕ-cast (sym assocIn) z′)) zlt)
                  ■ Fin.toℕ-cast (sym assocIn) z′
                ρ₂N-high : ∀ (z′ : 𝔽 (sA1 + (2 + n))) → sA1 + 2 Nat.≤ Fin.toℕ z′ →
                           Fin.toℕ (ρ₂ z′) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z′ Nat.∸ (sA1 + 2))))
                ρ₂N-high z′ zge =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) z′))
                  ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) z′) zge'
                  ■ cong ((sA1 + 2) +_) (toℕ-weaken*ᵣ (sB2 + (sB1 + 2)) (Fin.reduce≥ (Fin.cast (sym assocIn) z′) zge')
                      ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ (Fin.cast (sym assocIn) z′) zge' ■ cong (Nat._∸ (sA1 + 2)) (Fin.toℕ-cast (sym assocIn) z′)))
                  ■ Nat.+-assoc sA1 2 ((sB2 + (sB1 + 2)) + (Fin.toℕ z′ Nat.∸ (sA1 + 2)))
                  where zge' : sA1 + 2 Nat.≤ Fin.toℕ (Fin.cast (sym assocIn) z′)
                        zge' = subst (sA1 + 2 Nat.≤_) (sym (Fin.toℕ-cast (sym assocIn) z′)) zge
                Λ₂Eq : Λ₂ ≗ ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
                Λ₂Eq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    t = Fin.toℕ y
                    v = (ρ₂ ↑* sA2) y
                    rhsN : Fin.toℕ (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) y)
                           ≡ sB2 + (sB1 + (2 + t))
                    rhsN = toℕ-weaken*ᵣ sB2 _ ■ cong (sB2 +_) (toℕ-weaken*ᵣ sB1 _ ■ cong (sB1 +_) (toℕ-weaken*ᵣ 2 y))
                    -- v fixes toℕ for the low region (t < sA2+(sA1+2)).
                    vlowGe : t Nat.< sA2 + (sA1 + 2) → sA2 Nat.≤ t → Fin.toℕ v ≡ t
                    vlowGe tlt tge = toℕ-↑*-ge ρ₂ sA2 y tge ■ cong (sA2 +_) (ρ₂N-low (Fin.reduce≥ y tge) redlt ■ redN) ■ Nat.m+[n∸m]≡n tge
                      where redN : Fin.toℕ (Fin.reduce≥ y tge) ≡ t Nat.∸ sA2
                            redN = toℕ-reduce≥ y tge
                            redlt : Fin.toℕ (Fin.reduce≥ y tge) Nat.< sA1 + 2
                            redlt = subst (Nat._< sA1 + 2) (sym redN)
                                      (Nat.+-cancelˡ-< sA2 (t Nat.∸ sA2) (sA1 + 2)
                                        (subst (Nat._< sA2 + (sA1 + 2)) (sym (Nat.m+[n∸m]≡n tge)) tlt))
                    vlow : t Nat.< sA2 + (sA1 + 2) → Fin.toℕ v ≡ t
                    vlow tlt with Nat.<-cmp t sA2
                    ... | tri< tlt1 _ _ = toℕ-↑*-lt ρ₂ sA2 y tlt1
                    ... | tri≈ _ teq1 _ = vlowGe tlt (Nat.≤-reflexive (sym teq1))
                    ... | tri> _ _ tgt1 = vlowGe tlt (Nat.<⇒≤ tgt1)
                    dataEq : sA2 + sA1 Nat.≤ t → t Nat.< sA2 + sA1 + 2 → Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    dataEq ge2 lt2 = Φ-toℕ-Adata v (subst (sA2 + sA1 Nat.≤_) (sym vN) ge2) (subst (Nat._< sA2 + sA1 + 2) (sym vN) lt2)
                                   ■ cong ((sB2 + (sB1 + 2)) +_) vN ■ solveD
                      where vN : Fin.toℕ v ≡ t
                            vN = vlow (Nat.<-≤-trans lt2 (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 2)))
                            open +-*-Solver
                            solveD : (sB2 + (sB1 + 2)) + t ≡ sB2 + (sB1 + (2 + t))
                            solveD = solve 3 (λ b2 b1 s →
                                        (b2 :+ (b1 :+ con 2)) :+ s := b2 :+ (b1 :+ (con 2 :+ s))) refl sB2 sB1 t
                    tailEq : sA2 + sA1 + 2 Nat.≤ t → Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    tailEq ge2 = Φ-fix-ge v geΦ ■ vN ■ solveT
                      where
                        ge1 : sA2 + (sA1 + 2) Nat.≤ t
                        ge1 = subst (Nat._≤ t) (Nat.+-assoc sA2 sA1 2) ge2
                        dd = t Nat.∸ (sA2 + (sA1 + 2))
                        td : (sA2 + (sA1 + 2)) + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge1
                        tge2 : sA2 Nat.≤ t
                        tge2 = Nat.≤-trans (Nat.m≤m+n sA2 (sA1 + 2)) ge1
                        red = Fin.reduce≥ y tge2
                        redN : Fin.toℕ red ≡ sA1 + 2 + dd
                        redN = toℕ-reduce≥ y tge2 ■ red2
                          where red2 : t Nat.∸ sA2 ≡ sA1 + 2 + dd
                                red2 = cong (Nat._∸ sA2) (sym td)
                                     ■ cong (Nat._∸ sA2) (Nat.+-assoc sA2 (sA1 + 2) dd)
                                     ■ Nat.m+n∸m≡n sA2 (sA1 + 2 + dd)
                        redge : sA1 + 2 Nat.≤ Fin.toℕ red
                        redge = subst (sA1 + 2 Nat.≤_) (sym redN) (Nat.m≤m+n (sA1 + 2) dd)
                        ρ₂redN : Fin.toℕ (ρ₂ red) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))
                        ρ₂redN = ρ₂N-high red redge ■ cong (λ w → sA1 + (2 + ((sB2 + (sB1 + 2)) + w))) redd
                          where redd : Fin.toℕ red Nat.∸ (sA1 + 2) ≡ dd
                                redd = cong (Nat._∸ (sA1 + 2)) redN ■ Nat.m+n∸m≡n (sA1 + 2) dd
                        vN : Fin.toℕ v ≡ sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd)))
                        vN = toℕ-↑*-ge ρ₂ sA2 y tge2 ■ cong (sA2 +_) ρ₂redN
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ v
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym vN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n (sB2 + (sB1 + 2)) dd))))
                        open +-*-Solver
                        solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))) ≡ sB2 + (sB1 + (2 + t))
                        solveT = solve 5 (λ a2 a1 b2 b1 w →
                                    a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ w)))
                                    := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ w)))) refl sA2 sA1 sB2 sB1 dd
                               ■ cong (λ w → sB2 + (sB1 + (2 + w))) td
                    lhsN : Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    lhsN with Nat.<-cmp t (sA2 + sA1)
                    ... | tri< tlt _ _ =
                            Φ-toℕ-A v (subst (Nat._< sA2 + sA1) (sym vN) tlt)
                          ■ cong ((sB2 + (sB1 + 2)) +_) vN
                          ■ solveLow
                      where vlt : t Nat.< sA2 + (sA1 + 2)
                            vlt = Nat.<-≤-trans tlt (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sA1 2))
                            vN : Fin.toℕ v ≡ t
                            vN = vlow vlt
                            open +-*-Solver
                            solveLow : (sB2 + (sB1 + 2)) + t ≡ sB2 + (sB1 + (2 + t))
                            solveLow = solve 3 (λ b2 b1 s →
                                          (b2 :+ (b1 :+ con 2)) :+ s := b2 :+ (b1 :+ (con 2 :+ s))) refl sB2 sB1 t
                    ... | tri≈ _ teq _ = dataEq (Nat.≤-reflexive (sym teq)) (subst (Nat._< sA2 + sA1 + 2) (sym teq) data<)
                      where data< : sA2 + sA1 Nat.< sA2 + sA1 + 2
                            data< = Nat.≤-<-trans (Nat.≤-reflexive (sym (Nat.+-identityʳ (sA2 + sA1)))) (Nat.+-monoʳ-< (sA2 + sA1) (Nat.s≤s Nat.z≤n))
                    ... | tri> _ _ tgt with Nat.<-cmp t (sA2 + sA1 + 2)
                    ...   | tri< tlt2 _ _ = dataEq (Nat.<⇒≤ tgt) tlt2
                    ...   | tri≈ _ teq2 _ = tailEq (Nat.≤-reflexive (sym teq2))
                    ...   | tri> _ _ tgt2 = tailEq (Nat.<⇒≤ tgt2)
                midA2 : cA2t ⋯ Φ ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) k
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midA2 =
                    fuseL
                  ■ ⋯-cong c₂ Λ₂Eq
                  ■ sym (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2) (sym (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1)))

U-ν-comm : (σ : m →ₛ n) {B₁ B₂ A₁ A₂ : BindGroup} {P : T.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + m))} →
           U[ T.ν B₁ B₂ (T.ν A₁ A₂ P) ] σ U.≋
           U[ T.ν A₁ A₂ (T.ν B₁ B₂ (P T.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))) ] σ
U-ν-comm {m = m} {n = n} σ {B₁} {B₂} {A₁} {A₂} {P} =
     ≡→≋ (Uν-flat σ B₁ B₂ (T.ν A₁ A₂ P))
  ◅◅ U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (Uν-flat (leafσ σ B₁ B₂) A₁ A₂ P))))
  ◅◅ U.ν-cong (Bφ-cong B₁ (Bφ-past-ν B₂ YA))
  ◅◅ U.ν-cong (Bφ-past-ν B₁ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2)))
  ◅◅ Eq*.return U.ν-comm′
  ◅◅ U.ν-cong (U.ν-cong (≡→≋ (Bφ-⋯ B₁ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2) U.⋯ₚ assocSwapᵣ 2 sB1) (assocSwapᵣ 2 2 {n}))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (≡→≋ (U.fusionₚ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2)) (assocSwapᵣ 2 sB1) (assocSwapᵣ 2 2 {n} ↑* sB1)))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (≡→≋ (Bφ-⋯ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2) (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (U.fusionₚ YA (assocSwapᵣ 2 sB2) (ρ2 ↑* sB2))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (Bφ-⋯ A₁ (Bφ A₂ LeafL) ρacc)))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (Bφ-cong A₁ (≡→≋ (Bφ-⋯ A₂ LeafL (ρacc ↑* sA1)))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-transpose B₂ A₁ (Bφ A₂ LeafL'))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong A₁ (Bφ-cong B₂ (≡→≋ (Bφ-⋯ A₂ LeafL' (assocSwapᵣ sA1 sB2)))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong A₁ (Bφ-transpose B₂ A₂ (LeafL' U.⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-transpose B₁ A₁ (Bφ A₂ (Bφ B₂ W2))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong A₁ (Bφ-cong B₁ (≡→≋ (Bφ-⋯ A₂ (Bφ B₂ W2) (assocSwapᵣ sA1 sB1))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong A₁ (Bφ-transpose B₁ A₂ (Bφ B₂ W2 U.⋯ₚ (assocSwapᵣ sA1 sB1 ↑* sA2)))))
  ◅◅ U.ν-cong (ν-past-Bφ A₁ _)
  ◅◅ U.ν-cong (Bφ-cong A₁ (U.ν-cong (≡→≋ (Bφ-⋯ A₂ _ (assocSwapᵣ sA1 2)))))
  ◅◅ U.ν-cong (Bφ-cong A₁ (ν-past-Bφ A₂ _))
  ◅◅ U.ν-cong (Bφ-cong A₁ (Bφ-cong A₂ (U.ν-cong bodyReconcile)))
  ◅◅ ≡→≋ (sym flatR)
  where
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
    LeafL = U[ P ] (leafσ (leafσ σ B₁ B₂) A₁ A₂)
    YA = Bφ A₁ (Bφ A₂ LeafL)
    ρ2 = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)
    ρacc = assocSwapᵣ 2 sB2 ·ₖ (ρ2 ↑* sB2)
    LeafL' = LeafL U.⋯ₚ ((ρacc ↑* sA1) ↑* sA2)
    W2 = (LeafL' U.⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2)) U.⋯ₚ assocSwapᵣ sA2 sB2
    P′ = P T.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)
    flatR : U[ T.ν A₁ A₂ (T.ν B₁ B₂ P′) ] σ
            ≡ U.ν (Bφ A₁ (Bφ A₂ (U.ν (Bφ B₁ (Bφ B₂ (U[ P′ ] (leafσ (leafσ σ A₁ A₂) B₁ B₂)))))))
    flatR = Uν-flat σ A₁ A₂ (T.ν B₁ B₂ P′)
          ■ cong U.ν (cong (Bφ A₁) (cong (Bφ A₂) (Uν-flat (leafσ σ A₁ A₂) B₁ B₂ P′)))
    Q₁ = assocSwapᵣ sA1 sB1 ↑* sA2
    Q₂ = assocSwapᵣ sA2 sB1
    Q₃ = assocSwapᵣ sA1 2 ↑* sA2
    Q₄ = assocSwapᵣ sA2 2
    Ω = (Q₁ ·ₖ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))) ↑* sB2
    leafEqComm : W2 U.⋯ₚ Ω ≡ U[ P′ ] (leafσ (leafσ σ A₁ A₂) B₁ B₂)
    leafEqComm =
        cong (U._⋯ₚ Ω) ( cong (U._⋯ₚ assocSwapᵣ sA2 sB2)
                           (cong (U._⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2)) (local-U-σ⋯ P)
                            ■ local-U-σ⋯ P)
                       ■ local-U-σ⋯ P )
      ■ local-U-σ⋯ P
      ■ U-cong P (subEqComm-gen σ A₁ A₂ B₁ B₂)
      ■ sym (U-⋯ₚ P)
    bodyReconcile =
         ≡→≋ ( U.fusionₚ (Bφ B₁ ((Bφ B₂ W2 U.⋯ₚ Q₁) U.⋯ₚ Q₂)) Q₃ Q₄
             ■ Bφ-⋯ B₁ ((Bφ B₂ W2 U.⋯ₚ Q₁) U.⋯ₚ Q₂) (Q₃ ·ₖ Q₄)
             ■ cong (Bφ B₁) ( U.fusionₚ (Bφ B₂ W2 U.⋯ₚ Q₁) Q₂ ((Q₃ ·ₖ Q₄) ↑* sB1)
                            ■ U.fusionₚ (Bφ B₂ W2) Q₁ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))
                            ■ Bφ-⋯ B₂ W2 (Q₁ ·ₖ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))) ) )
      ◅◅ Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ leafEqComm))

U-ν-ext : (σ : m →ₛ n) (P : T.Proc m) (B₁ B₂ : BindGroup) (Q : T.Proc (sum B₁ + sum B₂ + m)) →
          U[ P T.∥ T.ν B₁ B₂ Q ] σ U.≋
          U[ T.ν B₁ B₂ ((P T.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) T.∥ Q) ] σ
U-ν-ext {m = m} {n = n} σ P B₁ B₂ Q =
  Eq*.return U.ν-ext′
  ◅◅ U.ν-cong
       ( UB-ext B₁ (K `unit , 0F , K `unit) (U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) _
       ◅◅ local-UB-≋ B₁ _ (λ τ₁ →
            UB-ext B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
              ((U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) _)
       ◅◅ local-UB-≋ B₁ _ (λ τ₁ → local-UB-≋ B₂ _ (λ τ₂ →
            ≡→≋ (cong (U._∥ U[ Q ] (σ′ τ₁ τ₂)) (step4eq τ₁ τ₂)))) )
  where
    wkK = weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)
    Bσ : m →ₛ syncs B₂ + (syncs B₁ + (2 + n))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
    σ′ : (sum B₁ →ₛ syncs B₁ + (2 + n)) → (sum B₂ →ₛ syncs B₂ + (syncs B₁ + (2 + n))) →
         (sum B₁ + sum B₂ + m →ₛ syncs B₂ + (syncs B₁ + (2 + n)))
    σ′ τ₁ τ₂ = ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂) ++ₛ Bσ
    wkσ′≗Bσ : ∀ τ₁ τ₂ → wkK ·ₖ σ′ τ₁ τ₂ ≗ Bσ
    wkσ′≗Bσ τ₁ τ₂ i =
        cong (σ′ τ₁ τ₂) (weaken*~↑ʳ (sum B₁ + sum B₂) i)
      ■ cong [ _ , _ ]′ (splitAt-↑ʳ (sum B₁ + sum B₂) _ i)
    step4eq : ∀ τ₁ τ₂ →
              ((U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁))
                U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
              ≡ U[ P T.⋯ₚ wkK ] (σ′ τ₁ τ₂)
    step4eq τ₁ τ₂ =
        ( cong (λ z → z U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (local-U-σ⋯ P)
        ■ cong (λ z → z U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (local-U-σ⋯ P)
        ■ local-U-σ⋯ P )
      ■ sym (U-⋯ₚ P ■ U-cong P (wkσ′≗Bσ τ₁ τ₂))

------------------------------------------------------------------------
-- the dispatcher
------------------------------------------------------------------------

U-≋′ : (σ : m →ₛ n) {P Q : T.Proc m} → P T.≋′ Q → U[ P ] σ U.≋ U[ Q ] σ
U-≋′ σ T.∥-comm′        = U.∥-comm
U-≋′ σ T.∥-assoc′       = U.∥-assoc
U-≋′ σ T.∥-unit′        = U.∥-unitˡ
U-≋′ σ (T.∥-cong′ x)    = U.∥-cong (U-≋′ σ x) ε
U-≋′ σ (T.ν-cong′ {B₁} {B₂} x) =
  Eq*.gmap U.ν U.ν-cong′ (local-UB-≋ B₁ _ (λ τ1 → local-UB-≋ B₂ _ (λ τ2 → U-≋′ _ x)))
U-≋′ σ (T.ν-swap′ {B₁} {B₂} {P}) = U-ν-swap σ {B₁} {B₂} {P}
U-≋′ σ (T.ν-comm′ {B₁} {B₂} {A₁} {A₂} {P}) = U-ν-comm σ {B₁} {B₂} {A₁} {A₂} {P}
U-≋′ σ (T.ν-ext′ {P} {B₁} {B₂} {Q}) = U-ν-ext σ P B₁ B₂ Q

U-≋ : (σ : m →ₛ n) {P Q : T.Proc m} → P T.≋ Q → U[ P ] σ U.≋ U[ Q ] σ
U-≋ σ = kleisliStar (λ P → U[ P ] σ)
          λ { (fwd s) → U-≋′ σ s ; (bwd s) → Eq*.symmetric _ (U-≋′ σ s) }
