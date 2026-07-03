module BorrowedCF.Simulation2.CongruenceH2 where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation2.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation2.BlockPerm
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

open import BorrowedCF.Simulation2.CongruenceH1 public

-- a toℕ-fixing renaming stays toℕ-fixing after lifting past k inert binders.
lift-fix-ge : ∀ {a a′} (ρ : a →ᵣ a′) (k T : ℕ) →
              (∀ y → T Nat.≤ Fin.toℕ y → Fin.toℕ (ρ y) ≡ Fin.toℕ y) →
              ∀ (z : 𝔽 (k + a)) → k + T Nat.≤ Fin.toℕ z →
              Fin.toℕ ((ρ ↑* k) z) ≡ Fin.toℕ z
lift-fix-ge ρ k T h z ge =
    toℕ-↑*-ge ρ k z q1
  ■ cong (k +_) (h (Fin.reduce≥ z q1) Tred)
  ■ cong (k +_) (toℕ-reduce≥ z q1)
  ■ Nat.m+[n∸m]≡n q1
  where
    q1 : k Nat.≤ Fin.toℕ z
    q1 = Nat.≤-trans (Nat.m≤m+n k T) ge
    Tred : T Nat.≤ Fin.toℕ (Fin.reduce≥ z q1)
    Tred = subst (T Nat.≤_) (sym (toℕ-reduce≥ z q1))
             (subst (Nat._≤ Fin.toℕ z Nat.∸ k) (Nat.m+n∸m≡n k T) (Nat.∸-monoˡ-≤ k ge))

-- the inner ρb = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 ↑* sB1) fixes toℕ on indices ≥ sB1+(2+2).
ρb-fix-ge : ∀ {n} (sB1 : ℕ) (y : 𝔽 (2 + (sB1 + (2 + n)))) → 2 + (sB1 + 2) Nat.≤ Fin.toℕ y →
            Fin.toℕ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) y) ≡ Fin.toℕ y
ρb-fix-ge {n} sB1 y ge =
    lift-fix-ge (assocSwapᵣ 2 2 {n}) sB1 (2 + 2)
      (λ w q → toℕ-assoc-ge 2 2 w q) (assocSwapᵣ 2 sB1 y) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB1 y) ≡ Fin.toℕ y
    aSwN = toℕ-assoc-ge 2 sB1 y (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 2)) ge)
    geInner : sB1 + (2 + 2) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 y)
    geInner = subst (sB1 + (2 + 2) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ y) reassoc ge)
      where reassoc : 2 + (sB1 + 2) ≡ sB1 + (2 + 2)
            reassoc = solve 1 (λ s → con 2 :+ (s :+ con 2) := s :+ (con 2 :+ con 2)) refl sB1
              where open +-*-Solver

-- toℕ-preservation of the body permutation ρacc on indices at/above its prefix.
ρacc-fix-ge : ∀ {n} (sB1 sB2 : ℕ) (x : 𝔽 (2 + (sB2 + (sB1 + (2 + n))))) →
              2 + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
              Fin.toℕ ((assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)) x)
              ≡ Fin.toℕ x
ρacc-fix-ge {n} sB1 sB2 x ge =
    lift-fix-ge (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) sB2 (2 + (sB1 + 2))
      (λ w q → ρb-fix-ge sB1 w q) (assocSwapᵣ 2 sB2 x) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB2 x) ≡ Fin.toℕ x
    aSwN = toℕ-assoc-ge 2 sB2 x (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB2 (sB1 + 2))) ge)
    geInner : sB2 + (2 + (sB1 + 2)) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 x)
    geInner = subst (sB2 + (2 + (sB1 + 2)) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ x) reassoc ge)
      where reassoc : 2 + (sB2 + (sB1 + 2)) ≡ sB2 + (2 + (sB1 + 2))
            reassoc = solve 2 (λ u v → con 2 :+ (u :+ (v :+ con 2))
                               := u :+ (con 2 :+ (v :+ con 2))) refl sB2 sB1
              where open +-*-Solver

-- the inner L₃ = (assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2 fixes toℕ ≥ sA2+(sA1+2).
ωL3-fix-ge : ∀ {p} (sA1 sA2 : ℕ) (y : 𝔽 (sA2 + (sA1 + (2 + p)))) → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ y →
             Fin.toℕ (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2 {sA1 + p}) y) ≡ Fin.toℕ y
ωL3-fix-ge {p} sA1 sA2 y ge =
    toℕ-assoc-ge sA2 2 ((assocSwapᵣ sA1 2 {p} ↑* sA2) y)
      (subst (sA2 + 2 Nat.≤_) (sym m1N) (Nat.≤-trans le1 ge))
  ■ m1N
  where
    m1N : Fin.toℕ ((assocSwapᵣ sA1 2 {p} ↑* sA2) y) ≡ Fin.toℕ y
    m1N = toℕ-assoc↑*-fix-ge sA2 sA1 2 y ge
    le1 : sA2 + 2 Nat.≤ sA2 + (sA1 + 2)
    le1 = Nat.+-monoʳ-≤ sA2 (Nat.m≤n+m 2 sA1)

-- the body permutation ρω fixes toℕ on indices ≥ sA2+(sA1+(sB1+2)).
ρω-fix-ge : ∀ {p} (sA1 sA2 sB1 : ℕ) (x : 𝔽 (sA2 + (sA1 + (sB1 + (2 + p))))) →
            sA2 + (sA1 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
            Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                      ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                          (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x)
            ≡ Fin.toℕ x
ρω-fix-ge {p} sA1 sA2 sB1 x ge = l3N ■ z2N ■ z1N
  where
    z1 = (assocSwapᵣ sA1 sB1 ↑* sA2) x
    z1N : Fin.toℕ z1 ≡ Fin.toℕ x
    z1N = toℕ-assoc↑*-fix-ge sA2 sA1 sB1 x
            (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 2))) ge)
    z2 = assocSwapᵣ sA2 sB1 z1
    z2N : Fin.toℕ z2 ≡ Fin.toℕ z1
    z2N = toℕ-assoc-ge sA2 sB1 z1
            (subst (sA2 + sB1 Nat.≤_) (sym z1N)
              (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB1 2) (Nat.m≤n+m (sB1 + 2) sA1))) ge))
    l3N : Fin.toℕ ((((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2) ≡ Fin.toℕ z2
    l3N = lift-fix-ge ((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 (sA2 + (sA1 + 2))
            (λ w q → ωL3-fix-ge sA1 sA2 w q) z2 geL3
      where
        geL3 : sB1 + (sA2 + (sA1 + 2)) Nat.≤ Fin.toℕ z2
        geL3 = subst (sB1 + (sA2 + (sA1 + 2)) Nat.≤_) (sym (z2N ■ z1N))
                 (subst (Nat._≤ Fin.toℕ x) reassoc ge)
          where reassoc : sA2 + (sA1 + (sB1 + 2)) ≡ sB1 + (sA2 + (sA1 + 2))
                reassoc = solve 3 (λ u v w → u :+ (v :+ (w :+ con 2)) := w :+ (u :+ (v :+ con 2)))
                            refl sA2 sA1 sB1
                  where open +-*-Solver

-- top-level rebuild of the composite body permutation Φ of subEqComm-gen,
-- parameterised purely by the four syncs counts.  (Definitionally equal to the
-- in-where Φ once the counts are instantiated.)
module _ (sA1 sA2 sB1 sB2 : ℕ) {n : ℕ} where
  Φᵗ : (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
       →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
  Φᵗ = (((((ρaccᵗ ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ωᵗ)
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2

  -- A-region: an index strictly below the A sync-prefix (sA2+sA1) is shifted
  -- right by the whole B-prefix (sB2+sB1+2).  (The two A data channels at
  -- [sA2+sA1, sA2+sA1+2) do NOT follow this flat shift; they are reconciled
  -- separately at the leaf level, so they are deliberately excluded here.)
  Φᵗ-A : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
         → Fin.toℕ x Nat.< sA2 + sA1
         → Fin.toℕ (Φᵗ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
  Φᵗ-A x lt = bridge ■ Φ-A-body
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      -- the two A data channels (sA2+sA1 ≤ toℕ x) are excluded by Φᵗ-A's
      -- hypothesis lt : toℕ x < sA2+sA1, so this case is vacuous.
      A3 : sA2 + sA1 Nat.≤ Fin.toℕ x → Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      A3 ge = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans lt ge))
      A23 : sA2 Nat.≤ Fin.toℕ x → Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      A23 a2le with Nat.<-cmp (Fin.toℕ x) (sA2 + sA1)
      ... | tri< xltA21 _ _ = A2
        where
          dx = Fin.toℕ x Nat.∸ sA2
          xd : sA2 + dx ≡ Fin.toℕ x
          xd = Nat.m+[n∸m]≡n a2le
          dltA1 : dx Nat.< sA1
          dltA1 = Nat.+-cancelˡ-< sA2 dx sA1 (subst (Nat._< sA2 + sA1) (sym xd) xltA21)
          xr = Fin.reduce≥ x a2le
          xrd : Fin.toℕ xr ≡ dx
          xrd = toℕ-reduce≥ x a2le
          -- x1 : F1 fixes (inner lift sA1 lt)
          x1N : Fin.toℕ x1 ≡ Fin.toℕ x
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-lt ρaccᵗ sA1 xr (subst (Nat._< sA1) (sym xrd) dltA1) ■ xrd)
              ■ xd
          x2N : Fin.toℕ x2 ≡ sA2 + (sB2 + dx)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 sB2 {sB1 + (2 + (2 + n))} (Fin.reduce≥ x1 a2lex1) dltA1r ■ cong (sB2 +_) reddx)
            where a2lex1 : sA2 Nat.≤ Fin.toℕ x1
                  a2lex1 = subst (sA2 Nat.≤_) (sym x1N) a2le
                  reddx : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ dx
                  reddx = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ cong (Nat._∸ sA2) (sym xd) ■ Nat.m+n∸m≡n sA2 dx
                  dltA1r : Fin.toℕ (Fin.reduce≥ x1 a2lex1) Nat.< sA1
                  dltA1r = subst (Nat._< sA1) (sym reddx) dltA1
          x3N : Fin.toℕ x3 ≡ sA2 + (sB2 + dx)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sB2 dx))) ■ x2N
          q : sB2 Nat.≤ Fin.toℕ x3
          q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤m+n sB2 dx) (Nat.m≤n+m (sB2 + dx) sA2))
          r = Fin.reduce≥ x3 q
          rN : Fin.toℕ r ≡ sA2 + dx
          rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sB2 + dx)) Nat.∸ sB2 ≡ sA2 + dx
                  reassoc = cong (Nat._∸ sB2) (solve 3 (λ a b e → a :+ (b :+ e) := b :+ (a :+ e)) refl sA2 sB2 dx) ■ Nat.m+n∸m≡n sB2 (sA2 + dx)
          rge : sA2 Nat.≤ Fin.toℕ r
          rge = subst (sA2 Nat.≤_) (sym rN) (Nat.m≤m+n sA2 dx)
          rr = Fin.reduce≥ r rge
          rrN : Fin.toℕ rr ≡ dx
          rrN = toℕ-reduce≥ r rge ■ cong (Nat._∸ sA2) rN ■ Nat.m+n∸m≡n sA2 dx
          rrltA1 : Fin.toℕ rr Nat.< sA1
          rrltA1 = subst (Nat._< sA1) (sym rrN) dltA1
          -- Omega_inner r : g1 ge(aS lt), g2 ge, g3 ge(L3: ge then aS ge)
          g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
          g1N : Fin.toℕ g1 ≡ sA2 + (sB1 + dx)
          g1N = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 r rge
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 sB1 rr rrltA1 ■ cong (sB1 +_) rrN)
          g2 = assocSwapᵣ sA2 sB1 g1
          g2N : Fin.toℕ g2 ≡ sA2 + (sB1 + dx)
          g2N = toℕ-assoc-ge sA2 sB1 g1 (subst (sA2 + sB1 Nat.≤_) (sym g1N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sB1 dx))) ■ g1N
          g3q : sB1 Nat.≤ Fin.toℕ g2
          g3q = subst (sB1 Nat.≤_) (sym g2N) (Nat.≤-trans (Nat.m≤m+n sB1 dx) (Nat.m≤n+m (sB1 + dx) sA2))
          g3r = Fin.reduce≥ g2 g3q
          g3rN : Fin.toℕ g3r ≡ sA2 + dx
          g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sB1 + dx)) Nat.∸ sB1 ≡ sA2 + dx
                  reassoc = cong (Nat._∸ sB1) (solve 3 (λ a b e → a :+ (b :+ e) := b :+ (a :+ e)) refl sA2 sB1 dx) ■ Nat.m+n∸m≡n sB1 (sA2 + dx)
          g3rge : sA2 Nat.≤ Fin.toℕ g3r
          g3rge = subst (sA2 Nat.≤_) (sym g3rN) (Nat.m≤m+n sA2 dx)
          g3rr = Fin.reduce≥ g3r g3rge
          g3rrN : Fin.toℕ g3rr ≡ dx
          g3rrN = toℕ-reduce≥ g3r g3rge ■ cong (Nat._∸ sA2) g3rN ■ Nat.m+n∸m≡n sA2 dx
          g3rrltA1 : Fin.toℕ g3rr Nat.< sA1
          g3rrltA1 = subst (Nat._< sA1) (sym g3rrN) dltA1
          -- L3 g3r = aS(sA2,2)((aS(sA1,2)↑*sA2) g3r) ; both ge -> sA2+(2+dx)
          l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
          l1N : Fin.toℕ l1 ≡ sA2 + (2 + dx)
          l1N = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 g3r g3rge
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 2 g3rr g3rrltA1 ■ cong (2 +_) g3rrN)
          l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ sA2 + (2 + dx)
          l2N = toℕ-assoc-ge sA2 2 l1 (subst (sA2 + 2 Nat.≤_) (sym l1N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n 2 dx))) ■ l1N
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                 ≡ sB1 + (sA2 + (2 + dx))
          omN = toℕ-↑*-ge _ sB1 g2 g3q ■ cong (sB1 +_) l2N
          A2 : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          A2 = toℕ-↑*-ge _ sB2 x3 q
             ■ cong (sB2 +_) omN
             ■ final
            where open +-*-Solver
                  final : sB2 + (sB1 + (sA2 + (2 + dx))) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
                  final = (solve 4 (λ b2 b1 a2 e → b2 :+ (b1 :+ (a2 :+ (con 2 :+ e))) := (b2 :+ (b1 :+ con 2)) :+ (a2 :+ e)) refl sB2 sB1 sA2 dx) ■ cong ((sB2 + (sB1 + 2)) +_) xd
      ... | tri≈ _ xeqA21 _ = A3 (Nat.≤-reflexive (sym xeqA21))
      ... | tri> _ _ xgtA21 = A3 (Nat.<⇒≤ xgtA21)
      Φ-A-body : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      Φ-A-body with Nat.<-cmp (Fin.toℕ x) sA2
      ... | tri< xltA2 _ _ = A1
        where
          -- x < sA2
          x1N : Fin.toℕ x1 ≡ Fin.toℕ x
          x1N = toℕ-↑*-lt (ρaccᵗ ↑* sA1) sA2 x xltA2
          x2N : Fin.toℕ x2 ≡ Fin.toℕ x
          x2N = toℕ-↑*-lt (assocSwapᵣ sA1 sB2) sA2 x1 (subst (Nat._< sA2) (sym x1N) xltA2) ■ x1N
          x3N : Fin.toℕ x3 ≡ sB2 + Fin.toℕ x
          x3N = toℕ-assoc-lt sA2 sB2 x2 (subst (Nat._< sA2) (sym x2N) xltA2) ■ cong (sB2 +_) x2N
          A1 : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          A1 = toℕ-↑*-ge _ sB2 x3 q
             ■ cong (sB2 +_) omN
             ■ sym (Nat.+-assoc sB2 (sB1 + 2) (Fin.toℕ x))
            where
              q : sB2 Nat.≤ Fin.toℕ x3
              q = subst (sB2 Nat.≤_) (sym x3N) (Nat.m≤m+n sB2 (Fin.toℕ x))
              r = Fin.reduce≥ x3 q
              rN : Fin.toℕ r ≡ Fin.toℕ x
              rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ Nat.m+n∸m≡n sB2 (Fin.toℕ x)
              rltA2 : Fin.toℕ r Nat.< sA2
              rltA2 = subst (Nat._< sA2) (sym rN) xltA2
              -- Omega_inner r : g1 lt, g2 lt, g3 ge(reduce L3 lt then aS lt)
              g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
              g1N : Fin.toℕ g1 ≡ Fin.toℕ x
              g1N = toℕ-↑*-lt (assocSwapᵣ sA1 sB1) sA2 r rltA2 ■ rN
              g2 = assocSwapᵣ sA2 sB1 g1
              g2N : Fin.toℕ g2 ≡ sB1 + Fin.toℕ x
              g2N = toℕ-assoc-lt sA2 sB1 g1 (subst (Nat._< sA2) (sym g1N) xltA2) ■ cong (sB1 +_) g1N
              g3q : sB1 Nat.≤ Fin.toℕ g2
              g3q = subst (sB1 Nat.≤_) (sym g2N) (Nat.m≤m+n sB1 (Fin.toℕ x))
              g3r = Fin.reduce≥ g2 g3q
              g3rN : Fin.toℕ g3r ≡ Fin.toℕ x
              g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ Nat.m+n∸m≡n sB1 (Fin.toℕ x)
              g3rltA2 : Fin.toℕ g3r Nat.< sA2
              g3rltA2 = subst (Nat._< sA2) (sym g3rN) xltA2
              l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
              l1N : Fin.toℕ l1 ≡ Fin.toℕ x
              l1N = toℕ-↑*-lt (assocSwapᵣ sA1 2) sA2 g3r g3rltA2 ■ g3rN
              l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ 2 + Fin.toℕ x
              l2N = toℕ-assoc-lt sA2 2 l1 (subst (Nat._< sA2) (sym l1N) xltA2) ■ cong (2 +_) l1N
              omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                              ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                                  (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                     ≡ (sB1 + 2) + Fin.toℕ x
              omN = toℕ-↑*-ge _ sB1 g2 g3q
                  ■ cong (sB1 +_) l2N
                  ■ sym (Nat.+-assoc sB1 2 (Fin.toℕ x))
      ... | tri≈ _ xeqA2 _ = A23 (Nat.≤-reflexive (sym xeqA2))
      ... | tri> _ _ xgtA2 = A23 (Nat.<⇒≤ xgtA2)

  -- A-data region: the two A data channels at [sA2+sA1, sA2+sA1+2) follow the
  -- SAME flat shift as the A sync prefix (right by sB2+sB1+2).
  Φᵗ-Adata : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
             → sA2 + sA1 Nat.≤ Fin.toℕ x
             → Fin.toℕ x Nat.< sA2 + sA1 + 2
             → Fin.toℕ (Φᵗ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
  Φᵗ-Adata x age alt = bridge ■ body
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      de = Fin.toℕ x Nat.∸ (sA2 + sA1)
      a2le : sA2 Nat.≤ Fin.toℕ x
      a2le = Nat.≤-trans (Nat.m≤m+n sA2 sA1) age
      dx = sA1 + de
      xd : Fin.toℕ x ≡ sA2 + dx
      xd = sym (Nat.m+[n∸m]≡n a2le) ■ cong (sA2 +_) red-dx
        where red-dx : Fin.toℕ x Nat.∸ sA2 ≡ sA1 + de
              red-dx = cong (Nat._∸ sA2) (sym (Nat.m+[n∸m]≡n age))
                     ■ cong (Nat._∸ sA2) (Nat.+-assoc sA2 sA1 de) ■ Nat.m+n∸m≡n sA2 (sA1 + de)
      elt2 : de Nat.< 2
      elt2 = Nat.+-cancelˡ-< (sA2 + sA1) de 2
               (subst (Nat._< sA2 + sA1 + 2) (sym (Nat.m+[n∸m]≡n age)) alt)
      dxge : sA1 Nat.≤ dx
      dxge = Nat.m≤m+n sA1 de
      dxlt2 : dx Nat.< sA1 + 2
      dxlt2 = Nat.+-monoʳ-< sA1 elt2
      -- F1: ρaccᵗ fires on the data channel index w (toℕ w < 2).
      ρae : ∀ (w : 𝔽 (2 + (sB2 + (sB1 + (2 + n))))) → Fin.toℕ w Nat.< 2
            → Fin.toℕ (ρaccᵗ w) ≡ sB2 + (sB1 + (2 + Fin.toℕ w))
      ρae w wlt =
          toℕ-↑*-ge (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) sB2 (assocSwapᵣ 2 sB2 w) sb2le
        ■ cong (sB2 +_) inner
        where
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 w) ≡ sB2 + Fin.toℕ w
          asN = toℕ-assoc-lt 2 sB2 w wlt
          sb2le : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 w)
          sb2le = subst (sB2 Nat.≤_) (sym asN) (Nat.m≤m+n sB2 (Fin.toℕ w))
          r0 = Fin.reduce≥ (assocSwapᵣ 2 sB2 w) sb2le
          r0N : Fin.toℕ r0 ≡ Fin.toℕ w
          r0N = toℕ-reduce≥ (assocSwapᵣ 2 sB2 w) sb2le ■ cong (Nat._∸ sB2) asN ■ Nat.m+n∸m≡n sB2 (Fin.toℕ w)
          r0lt : Fin.toℕ r0 Nat.< 2
          r0lt = subst (Nat._< 2) (sym r0N) wlt
          inner : Fin.toℕ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) r0) ≡ sB1 + (2 + Fin.toℕ w)
          inner = toℕ-↑*-ge (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 r0) sb1le
                ■ cong (sB1 +_) inner2
            where
              as2N : Fin.toℕ (assocSwapᵣ 2 sB1 r0) ≡ sB1 + Fin.toℕ r0
              as2N = toℕ-assoc-lt 2 sB1 r0 r0lt
              sb1le : sB1 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 r0)
              sb1le = subst (sB1 Nat.≤_) (sym as2N) (Nat.m≤m+n sB1 (Fin.toℕ r0))
              r1 = Fin.reduce≥ (assocSwapᵣ 2 sB1 r0) sb1le
              r1N : Fin.toℕ r1 ≡ Fin.toℕ w
              r1N = toℕ-reduce≥ (assocSwapᵣ 2 sB1 r0) sb1le ■ cong (Nat._∸ sB1) as2N ■ Nat.m+n∸m≡n sB1 (Fin.toℕ r0) ■ r0N
              r1lt : Fin.toℕ r1 Nat.< 2
              r1lt = subst (Nat._< 2) (sym r1N) wlt
              inner2 : Fin.toℕ (assocSwapᵣ 2 2 {n} r1) ≡ 2 + Fin.toℕ w
              inner2 = toℕ-assoc-lt 2 2 r1 r1lt ■ cong (2 +_) r1N
      -- F1: x1
      x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
          ■ cong (sA2 +_) inner1
        where
          xr = Fin.reduce≥ x a2le
          xrN : Fin.toℕ xr ≡ dx
          xrN = toℕ-reduce≥ x a2le ■ cong (Nat._∸ sA2) xd ■ Nat.m+n∸m≡n sA2 dx
          xrge : sA1 Nat.≤ Fin.toℕ xr
          xrge = subst (sA1 Nat.≤_) (sym xrN) dxge
          inner1 : Fin.toℕ ((ρaccᵗ ↑* sA1) xr) ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          inner1 = toℕ-↑*-ge ρaccᵗ sA1 xr xrge ■ cong (sA1 +_) (ρae r2 r2lt ■ cong (λ z → sB2 + (sB1 + (2 + z))) r2N)
            where
              r2 = Fin.reduce≥ xr xrge
              r2N : Fin.toℕ r2 ≡ de
              r2N = toℕ-reduce≥ xr xrge ■ cong (Nat._∸ sA1) xrN ■ Nat.m+n∸m≡n sA1 de
              r2lt : Fin.toℕ r2 Nat.< 2
              r2lt = subst (Nat._< 2) (sym r2N) elt2
      x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1 ■ cong (sA2 +_) inner2
        where
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 _)
          r1 = Fin.reduce≥ x1 a2lex1
          r1N : Fin.toℕ r1 ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          r1N = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + (sB2 + (sB1 + (2 + de))))
          r1ge : sA1 + sB2 Nat.≤ Fin.toℕ r1
          r1ge = subst (sA1 + sB2 Nat.≤_) (sym r1N) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB2 (sB1 + (2 + de))))
          inner2 : Fin.toℕ (assocSwapᵣ sA1 sB2 r1) ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          inner2 = toℕ-assoc-ge sA1 sB2 r1 r1ge ■ r1N
      x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
              (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + (2 + de))) (Nat.m≤n+m _ sA1)))) ■ x2N
      body : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      body = toℕ-↑*-ge _ sB2 x3 q ■ cong (sB2 +_) omN ■ final
        where
          q : sB2 Nat.≤ Fin.toℕ x3
          q = subst (sB2 Nat.≤_) (sym x3N)
                (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + (2 + de)))
                  (Nat.≤-trans (Nat.m≤n+m _ sA1) (Nat.m≤n+m _ sA2)))
          r = Fin.reduce≥ x3 q
          rN : Fin.toℕ r ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))) Nat.∸ sB2 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
                  reassoc = cong (Nat._∸ sB2) (solve 5 (λ a2 a1 b2 b1 t →
                                a2 :+ (a1 :+ (b2 :+ (b1 :+ (con 2 :+ t))))
                                := b2 :+ (a2 :+ (a1 :+ (b1 :+ (con 2 :+ t))))) refl sA2 sA1 sB2 sB1 de)
                          ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + (sB1 + (2 + de))))
          rge : sA2 Nat.≤ Fin.toℕ r
          rge = subst (sA2 Nat.≤_) (sym rN) (Nat.m≤m+n sA2 _)
          g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
          g1N : Fin.toℕ g1 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          g1N = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 r rge ■ cong (sA2 +_) inner-g1
            where
              rr = Fin.reduce≥ r rge
              rrN : Fin.toℕ rr ≡ sA1 + (sB1 + (2 + de))
              rrN = toℕ-reduce≥ r rge ■ cong (Nat._∸ sA2) rN ■ Nat.m+n∸m≡n sA2 (sA1 + (sB1 + (2 + de)))
              rrge : sA1 + sB1 Nat.≤ Fin.toℕ rr
              rrge = subst (sA1 + sB1 Nat.≤_) (sym rrN) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 (2 + de)))
              inner-g1 : Fin.toℕ (assocSwapᵣ sA1 sB1 rr) ≡ sA1 + (sB1 + (2 + de))
              inner-g1 = toℕ-assoc-ge sA1 sB1 rr rrge ■ rrN
          g2 = assocSwapᵣ sA2 sB1 g1
          g2N : Fin.toℕ g2 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          g2N = toℕ-assoc-ge sA2 sB1 g1 (subst (sA2 + sB1 Nat.≤_) (sym g1N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB1 (2 + de)) (Nat.m≤n+m _ sA1)))) ■ g1N
          g3q : sB1 Nat.≤ Fin.toℕ g2
          g3q = subst (sB1 Nat.≤_) (sym g2N)
                  (Nat.≤-trans (Nat.m≤m+n sB1 (2 + de))
                    (Nat.≤-trans (Nat.m≤n+m _ sA1) (Nat.m≤n+m _ sA2)))
          g3r = Fin.reduce≥ g2 g3q
          g3rN : Fin.toℕ g3r ≡ sA2 + (sA1 + (2 + de))
          g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + (sB1 + (2 + de)))) Nat.∸ sB1 ≡ sA2 + (sA1 + (2 + de))
                  reassoc = cong (Nat._∸ sB1) (solve 4 (λ a2 a1 b1 t →
                                a2 :+ (a1 :+ (b1 :+ (con 2 :+ t)))
                                := b1 :+ (a2 :+ (a1 :+ (con 2 :+ t)))) refl sA2 sA1 sB1 de)
                          ■ Nat.m+n∸m≡n sB1 (sA2 + (sA1 + (2 + de)))
          g3rge : sA2 Nat.≤ Fin.toℕ g3r
          g3rge = subst (sA2 Nat.≤_) (sym g3rN) (Nat.m≤m+n sA2 _)
          l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
          l1N : Fin.toℕ l1 ≡ sA2 + (sA1 + (2 + de))
          l1N = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 g3r g3rge ■ cong (sA2 +_) inner-l1
            where
              gg = Fin.reduce≥ g3r g3rge
              ggN : Fin.toℕ gg ≡ sA1 + (2 + de)
              ggN = toℕ-reduce≥ g3r g3rge ■ cong (Nat._∸ sA2) g3rN ■ Nat.m+n∸m≡n sA2 (sA1 + (2 + de))
              ggge : sA1 + 2 Nat.≤ Fin.toℕ gg
              ggge = subst (sA1 + 2 Nat.≤_) (sym ggN) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n 2 de))
              inner-l1 : Fin.toℕ (assocSwapᵣ sA1 2 gg) ≡ sA1 + (2 + de)
              inner-l1 = toℕ-assoc-ge sA1 2 gg ggge ■ ggN
          l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ sA2 + (sA1 + (2 + de))
          l2N = toℕ-assoc-ge sA2 2 l1 (subst (sA2 + 2 Nat.≤_) (sym l1N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n 2 de) (Nat.m≤n+m _ sA1)))) ■ l1N
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                 ≡ sB1 + (sA2 + (sA1 + (2 + de)))
          omN = toℕ-↑*-ge _ sB1 g2 g3q ■ cong (sB1 +_) l2N
          final : sB2 + (sB1 + (sA2 + (sA1 + (2 + de)))) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          final = solveF ■ cong ((sB2 + (sB1 + 2)) +_) (sym xd)
            where open +-*-Solver
                  solveF : sB2 + (sB1 + (sA2 + (sA1 + (2 + de)))) ≡ (sB2 + (sB1 + 2)) + (sA2 + (sA1 + de))
                  solveF = solve 5 (λ b2 b1 a2 a1 t →
                      b2 :+ (b1 :+ (a2 :+ (a1 :+ (con 2 :+ t))))
                      := (b2 :+ (b1 :+ con 2)) :+ (a2 :+ (a1 :+ t))) refl sB2 sB1 sA2 sA1 de

  -- B-region: an index in [sA2+sA1+2, sA2+sA1+2 + (sB2+sB1+2)) is shifted left
  -- by the whole A-prefix.
  Φᵗ-B : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
         → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ x
         → Fin.toℕ x Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
         → Fin.toℕ (Φᵗ x) ≡ Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
  Φᵗ-B x ge lt = bridge ■ Φ-B-body
    where
      ra-inner = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ (ra-inner ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      f = Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
      a2le : sA2 Nat.≤ Fin.toℕ x
      a2le = Nat.≤-trans (Nat.m≤m+n sA2 (sA1 + 2)) ge
      -- toℕ x = sA2 + (sA1 + (2 + f))
      xeq : Fin.toℕ x ≡ sA2 + (sA1 + (2 + f))
      xeq = sym (Nat.m+[n∸m]≡n ge) ■ Nat.+-assoc sA2 (sA1 + 2) f ■ cong (sA2 +_) (Nat.+-assoc sA1 2 f)
      fltBpre : f Nat.< sB2 + (sB1 + 2)
      fltBpre = Nat.+-cancelˡ-< sA2 f (sB2 + (sB1 + 2))
                  (Nat.+-cancelˡ-< sA1 (sA2 + f) _
                    (Nat.+-cancelˡ-< 2 (sA1 + (sA2 + f)) _ goal2))
        where -- 2 + (sA1 + (sA2 + f)) < 2 + (sA1 + (sA2 + (sB2+sB1+2)))  (= toℕx-region reassociated)
              goal2 : 2 + (sA1 + (sA2 + f)) Nat.< 2 + (sA1 + (sA2 + (sB2 + (sB1 + 2))))
              goal2 = subst₂ Nat._<_ lhseq rhseq (subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) xeq lt)
                where lhseq : sA2 + (sA1 + (2 + f)) ≡ 2 + (sA1 + (sA2 + f))
                      lhseq = solve 3 (λ a2 a1 t → a2 :+ (a1 :+ (con 2 :+ t)) := con 2 :+ (a1 :+ (a2 :+ t))) refl sA2 sA1 f
                        where open +-*-Solver
                      rhseq : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) ≡ 2 + (sA1 + (sA2 + (sB2 + (sB1 + 2))))
                      rhseq = solve 4 (λ a2 a1 b2 b1 → a2 :+ (a1 :+ (con 2 :+ (b2 :+ (b1 :+ con 2)))) := con 2 :+ (a1 :+ (a2 :+ (b2 :+ (b1 :+ con 2))))) refl sA2 sA1 sB2 sB1
                        where open +-*-Solver
      -- common reduction of F1 down to the "2"-block: xr = reduce x past sA2 then sA1
      xrA = Fin.reduce≥ x a2le
      xrAN : Fin.toℕ xrA ≡ sA1 + (2 + f)
      xrAN = toℕ-reduce≥ x a2le ■ cong (Nat._∸ sA2) xeq ■ Nat.m+n∸m≡n sA2 (sA1 + (2 + f))
      xrAge : sA1 Nat.≤ Fin.toℕ xrA
      xrAge = subst (sA1 Nat.≤_) (sym xrAN) (Nat.m≤m+n sA1 (2 + f))
      xrB = Fin.reduce≥ xrA xrAge
      xrBN : Fin.toℕ xrB ≡ 2 + f
      xrBN = toℕ-reduce≥ xrA xrAge ■ cong (Nat._∸ sA1) xrAN ■ Nat.m+n∸m≡n sA1 (2 + f)
      B1 : f Nat.< sB2 → Fin.toℕ (Ωᵗ x3) ≡ f
      B1 flt2 = toℕ-↑*-lt _ sB2 x3 (subst (Nat._< sB2) (sym x3N) flt2) ■ x3N
        where
          -- ρaccᵗ on xrB (toℕ = 2+f) with f<sB2: aS(2,sB2) mid -> f ; lift sB2 lt -> f
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-lt _ sB2 (assocSwapᵣ 2 sB2 xrB) red
             ■ asN
            where asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ f
                  asN = toℕ-assoc-mid 2 sB2 xrB
                          (subst (2 Nat.≤_) (sym xrBN) (Nat.m≤m+n 2 f))
                          (subst (Nat._< 2 + sB2) (sym xrBN) (Nat.+-monoʳ-< 2 flt2))
                      ■ cong (Nat._∸ 2) xrBN ■ Nat.m+n∸m≡n 2 f
                  red : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) Nat.< sB2
                  red = subst (Nat._< sB2) (sym asN) flt2
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          -- x2 : F2 aS(sA1,sB2) on (sA1+f) mid -> f ; toℕ x2 = sA2 + f
          x2N : Fin.toℕ x2 ≡ sA2 + f
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-mid sA1 sB2 (Fin.reduce≥ x1 a2lex1) midlo midhi ■ cong (Nat._∸ sA1) redf ■ Nat.m+n∸m≡n sA1 f)
            where a2lex1 : sA2 Nat.≤ Fin.toℕ x1
                  a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
                  redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
                  redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
                  midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ x1 a2lex1)
                  midlo = subst (sA1 Nat.≤_) (sym redf) (Nat.m≤m+n sA1 f)
                  midhi : Fin.toℕ (Fin.reduce≥ x1 a2lex1) Nat.< sA1 + sB2
                  midhi = subst (Nat._< sA1 + sB2) (sym redf) (Nat.+-monoʳ-< sA1 flt2)
          x3N : Fin.toℕ x3 ≡ f
          x3N = toℕ-assoc-mid sA2 sB2 x2 (subst (sA2 Nat.≤_) (sym x2N) (Nat.m≤m+n sA2 f))
                  (subst (Nat._< sA2 + sB2) (sym x2N) (Nat.+-monoʳ-< sA2 flt2))
              ■ cong (Nat._∸ sA2) x2N ■ Nat.m+n∸m≡n sA2 f
      B2 : sB2 Nat.≤ f → f Nat.< sB2 + sB1 → Fin.toℕ (Ωᵗ x3) ≡ f
      B2 ge2 flt21 = toℕ-↑*-ge _ sB2 x3 x3q ■ cong (sB2 +_) omN ■ Nat.m+[n∸m]≡n ge2
        where
          f1 = f Nat.∸ sB2
          f1eq : sB2 + f1 ≡ f
          f1eq = Nat.m+[n∸m]≡n ge2
          f1ltB1 : f1 Nat.< sB1
          f1ltB1 = Nat.+-cancelˡ-< sB2 f1 sB1 (subst (Nat._< sB2 + sB1) (sym f1eq) flt21)
          -- ρaccᵗ on xrB (=2+f) ; sB2≤f<sB2+sB1 -> f
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ 2 + f
          asN = toℕ-assoc-ge 2 sB2 xrB (subst (2 + sB2 Nat.≤_) (sym xrBN) (Nat.+-monoʳ-≤ 2 ge2)) ■ xrBN
          asge : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 xrB)
          asge = subst (sB2 Nat.≤_) (sym asN) (Nat.≤-trans (Nat.m≤n+m sB2 2) (Nat.+-monoʳ-≤ 2 ge2))
          asr = Fin.reduce≥ (assocSwapᵣ 2 sB2 xrB) asge
          asrN : Fin.toℕ asr ≡ 2 + f1
          asrN = toℕ-reduce≥ (assocSwapᵣ 2 sB2 xrB) asge ■ cong (Nat._∸ sB2) asN ■ reassoc
            where reassoc : (2 + f) Nat.∸ sB2 ≡ 2 + f1
                  reassoc = cong (Nat._∸ sB2) (cong (2 +_) (sym f1eq) ■ sym (Nat.+-assoc 2 sB2 f1) ■ cong (Nat._+ f1) (Nat.+-comm 2 sB2) ■ Nat.+-assoc sB2 2 f1) ■ Nat.m+n∸m≡n sB2 (2 + f1)
          -- ra_inner on (2+f1) = aS(2,sB1)·ₖ(aS(2,2)↑*sB1) ; aS(2,sB1) mid -> f1 ; lift lt -> f1
          rai-asN : Fin.toℕ (assocSwapᵣ 2 sB1 asr) ≡ f1
          rai-asN = toℕ-assoc-mid 2 sB1 asr (subst (2 Nat.≤_) (sym asrN) (Nat.m≤m+n 2 f1))
                      (subst (Nat._< 2 + sB1) (sym asrN) (Nat.+-monoʳ-< 2 f1ltB1))
                  ■ cong (Nat._∸ 2) asrN ■ Nat.m+n∸m≡n 2 f1
          raiN : Fin.toℕ (ra-inner asr) ≡ f1
          raiN = toℕ-↑*-lt (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 asr) (subst (Nat._< sB1) (sym rai-asN) f1ltB1) ■ rai-asN
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-ge ra-inner sB2 (assocSwapᵣ 2 sB2 xrB) asge ■ cong (sB2 +_) raiN ■ f1eq
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          -- F2 aS(sA1,sB2) on (sA1+f) ge (f≥sB2) -> unchanged ; x2 = sA2+(sA1+f)
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
          redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
          redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
          x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + f)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB2 (Fin.reduce≥ x1 a2lex1)
                  (subst (sA1 + sB2 Nat.≤_) (sym redf) (Nat.+-monoʳ-≤ sA1 ge2)) ■ redf)
          x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + f)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB2 sA1) (Nat.+-monoʳ-≤ sA1 ge2)))) ■ x2N
          x3q : sB2 Nat.≤ Fin.toℕ x3
          x3q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤n+m sB2 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) ge2) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 f))))
          x3r = Fin.reduce≥ x3 x3q
          x3rN : Fin.toℕ x3r ≡ sA2 + (sA1 + f1)
          x3rN = toℕ-reduce≥ x3 x3q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + f)) Nat.∸ sB2 ≡ sA2 + (sA1 + f1)
                  reassoc = cong (Nat._∸ sB2) (cong (λ z → sA2 + (sA1 + z)) (sym f1eq) ■ solve 4 (λ a2 a1 b2 t → a2 :+ (a1 :+ (b2 :+ t)) := b2 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB2 f1) ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + f1))
          -- Omega_inner x3r : g1 aS(sA1,sB1) mid -> f1 ; g2 aS(sA2,sB1) mid -> f1 ; g3 lift lt
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x3r)
                 ≡ f1
          omN = z3 ■ z2
            where
              z1f = (assocSwapᵣ sA1 sB1 ↑* sA2) x3r
              z1 : Fin.toℕ z1f ≡ sA2 + f1
              z1 = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 x3r x3rge
                 ■ cong (sA2 +_) (toℕ-assoc-mid sA1 sB1 (Fin.reduce≥ x3r x3rge) midlo midhi ■ cong (Nat._∸ sA1) redx3 ■ Nat.m+n∸m≡n sA1 f1)
                where x3rge : sA2 Nat.≤ Fin.toℕ x3r
                      x3rge = subst (sA2 Nat.≤_) (sym x3rN) (Nat.m≤m+n sA2 (sA1 + f1))
                      redx3 : Fin.toℕ (Fin.reduce≥ x3r x3rge) ≡ sA1 + f1
                      redx3 = toℕ-reduce≥ x3r x3rge ■ cong (Nat._∸ sA2) x3rN ■ Nat.m+n∸m≡n sA2 (sA1 + f1)
                      midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ x3r x3rge)
                      midlo = subst (sA1 Nat.≤_) (sym redx3) (Nat.m≤m+n sA1 f1)
                      midhi : Fin.toℕ (Fin.reduce≥ x3r x3rge) Nat.< sA1 + sB1
                      midhi = subst (Nat._< sA1 + sB1) (sym redx3) (Nat.+-monoʳ-< sA1 f1ltB1)
              z2f = assocSwapᵣ sA2 sB1 z1f
              z2 : Fin.toℕ z2f ≡ f1
              z2 = toℕ-assoc-mid sA2 sB1 z1f (subst (sA2 Nat.≤_) (sym z1) (Nat.m≤m+n sA2 f1))
                     (subst (Nat._< sA2 + sB1) (sym z1) (Nat.+-monoʳ-< sA2 f1ltB1))
                 ■ cong (Nat._∸ sA2) z1 ■ Nat.m+n∸m≡n sA2 f1
              z3 : Fin.toℕ ((((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2f) ≡ Fin.toℕ z2f
              z3 = toℕ-↑*-lt ((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 z2f (subst (Nat._< sB1) (sym z2) f1ltB1)
      B3 : sB2 + sB1 Nat.≤ f → Fin.toℕ (Ωᵗ x3) ≡ f
      B3 ge21 = toℕ-↑*-ge _ sB2 x3 x3q ■ cong (sB2 +_) omN ■ f2eq
        where
          f2 = f Nat.∸ (sB2 + sB1)
          f2eqB : (sB2 + sB1) + f2 ≡ f
          f2eqB = Nat.m+[n∸m]≡n ge21
          f2lt2 : f2 Nat.< 2
          f2lt2 = Nat.+-cancelˡ-< (sB2 + sB1) f2 2 (subst (Nat._< (sB2 + sB1) + 2) (sym f2eqB)
                    (subst (f Nat.<_) (sym (Nat.+-assoc sB2 sB1 2)) fltBpre))
          ge2 : sB2 Nat.≤ f
          ge2 = Nat.≤-trans (Nat.m≤m+n sB2 sB1) ge21
          f2eq : sB2 + (sB1 + f2) ≡ f
          f2eq = sym (Nat.+-assoc sB2 sB1 f2) ■ f2eqB
          -- ρaccᵗ on xrB (=2+f) ; f≥sB2+sB1 -> f
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ 2 + f
          asN = toℕ-assoc-ge 2 sB2 xrB (subst (2 + sB2 Nat.≤_) (sym xrBN) (Nat.+-monoʳ-≤ 2 ge2)) ■ xrBN
          asge : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 xrB)
          asge = subst (sB2 Nat.≤_) (sym asN) (Nat.≤-trans (Nat.m≤n+m sB2 2) (Nat.+-monoʳ-≤ 2 ge2))
          asr = Fin.reduce≥ (assocSwapᵣ 2 sB2 xrB) asge
          asrN : Fin.toℕ asr ≡ 2 + (sB1 + f2)
          asrN = toℕ-reduce≥ (assocSwapᵣ 2 sB2 xrB) asge ■ cong (Nat._∸ sB2) asN ■ reassoc
            where open +-*-Solver
                  reassoc : (2 + f) Nat.∸ sB2 ≡ 2 + (sB1 + f2)
                  reassoc = cong (Nat._∸ sB2) (cong (2 +_) (sym f2eq) ■ solve 3 (λ b2 b1 t → con 2 :+ (b2 :+ (b1 :+ t)) := b2 :+ (con 2 :+ (b1 :+ t))) refl sB2 sB1 f2) ■ Nat.m+n∸m≡n sB2 (2 + (sB1 + f2))
          -- ra_inner on (2+(sB1+f2)) : aS(2,sB1) ge ; (aS(2,2)↑sB1) ge reduce ; aS(2,2) mid -> sB1+f2
          rai-asN : Fin.toℕ (assocSwapᵣ 2 sB1 asr) ≡ 2 + (sB1 + f2)
          rai-asN = toℕ-assoc-ge 2 sB1 asr (subst (2 + sB1 Nat.≤_) (sym asrN) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 f2))) ■ asrN
          raisge : sB1 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 asr)
          raisge = subst (sB1 Nat.≤_) (sym rai-asN) (Nat.≤-trans (Nat.m≤n+m sB1 2) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 f2)))
          raisr = Fin.reduce≥ (assocSwapᵣ 2 sB1 asr) raisge
          raisrN : Fin.toℕ raisr ≡ 2 + f2
          raisrN = toℕ-reduce≥ (assocSwapᵣ 2 sB1 asr) raisge ■ cong (Nat._∸ sB1) rai-asN ■ reassoc
            where open +-*-Solver
                  reassoc : (2 + (sB1 + f2)) Nat.∸ sB1 ≡ 2 + f2
                  reassoc = cong (Nat._∸ sB1) (solve 2 (λ b1 t → con 2 :+ (b1 :+ t) := b1 :+ (con 2 :+ t)) refl sB1 f2) ■ Nat.m+n∸m≡n sB1 (2 + f2)
          raiN : Fin.toℕ (ra-inner asr) ≡ sB1 + f2
          raiN = toℕ-↑*-ge (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 asr) raisge
               ■ cong (sB1 +_) (toℕ-assoc-mid 2 2 raisr (subst (2 Nat.≤_) (sym raisrN) (Nat.m≤m+n 2 f2)) (subst (Nat._< 2 + 2) (sym raisrN) (Nat.+-monoʳ-< 2 f2lt2)) ■ cong (Nat._∸ 2) raisrN ■ Nat.m+n∸m≡n 2 f2)
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-ge ra-inner sB2 (assocSwapᵣ 2 sB2 xrB) asge ■ cong (sB2 +_) raiN ■ f2eq
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
          redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
          redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
          x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + f)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB2 (Fin.reduce≥ x1 a2lex1)
                  (subst (sA1 + sB2 Nat.≤_) (sym redf) (Nat.+-monoʳ-≤ sA1 ge2)) ■ redf)
          x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + f)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB2 sA1) (Nat.+-monoʳ-≤ sA1 ge2)))) ■ x2N
          x3q : sB2 Nat.≤ Fin.toℕ x3
          x3q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤n+m sB2 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) ge2) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 f))))
          x3r = Fin.reduce≥ x3 x3q
          x3rN : Fin.toℕ x3r ≡ sA2 + (sA1 + (sB1 + f2))
          x3rN = toℕ-reduce≥ x3 x3q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + f)) Nat.∸ sB2 ≡ sA2 + (sA1 + (sB1 + f2))
                  reassoc = cong (Nat._∸ sB2) (cong (λ z → sA2 + (sA1 + z)) (sym f2eq) ■ solve 4 (λ a2 a1 b2 t → a2 :+ (a1 :+ (b2 :+ t)) := b2 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB2 (sB1 + f2)) ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + (sB1 + f2)))
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x3r)
                 ≡ sB1 + f2
          omN = z3 ■ cong (sB1 +_) l2
            where
              x3rge : sA2 Nat.≤ Fin.toℕ x3r
              x3rge = subst (sA2 Nat.≤_) (sym x3rN) (Nat.m≤m+n sA2 (sA1 + (sB1 + f2)))
              z1f = (assocSwapᵣ sA1 sB1 ↑* sA2) x3r
              z1 : Fin.toℕ z1f ≡ sA2 + (sA1 + (sB1 + f2))
              z1 = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 x3r x3rge
                 ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB1 (Fin.reduce≥ x3r x3rge)
                     (subst (sA1 + sB1 Nat.≤_) (sym redx3) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 f2))) ■ redx3)
                where redx3 : Fin.toℕ (Fin.reduce≥ x3r x3rge) ≡ sA1 + (sB1 + f2)
                      redx3 = toℕ-reduce≥ x3r x3rge ■ cong (Nat._∸ sA2) x3rN ■ Nat.m+n∸m≡n sA2 (sA1 + (sB1 + f2))
              z2f = assocSwapᵣ sA2 sB1 z1f
              z2 : Fin.toℕ z2f ≡ sA2 + (sA1 + (sB1 + f2))
              z2 = toℕ-assoc-ge sA2 sB1 z1f (subst (sA2 + sB1 Nat.≤_) (sym z1)
                     (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB1 sA1) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 f2))))) ■ z1
              z2q : sB1 Nat.≤ Fin.toℕ z2f
              z2q = subst (sB1 Nat.≤_) (sym z2) (Nat.≤-trans (Nat.m≤n+m sB1 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) (Nat.m≤m+n sB1 f2)) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 (sB1 + f2)))))
              z2r = Fin.reduce≥ z2f z2q
              z2rN : Fin.toℕ z2r ≡ sA2 + (sA1 + f2)
              z2rN = toℕ-reduce≥ z2f z2q ■ cong (Nat._∸ sB1) z2 ■ reassoc
                where open +-*-Solver
                      reassoc : (sA2 + (sA1 + (sB1 + f2))) Nat.∸ sB1 ≡ sA2 + (sA1 + f2)
                      reassoc = cong (Nat._∸ sB1) (solve 4 (λ a2 a1 b1 t → a2 :+ (a1 :+ (b1 :+ t)) := b1 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB1 f2) ■ Nat.m+n∸m≡n sB1 (sA2 + (sA1 + f2))
              -- L3 on z2r (= sA2+(sA1+f2)) : aS(sA1,2) mid -> f2 ; aS(sA2,2) mid -> f2
              z2rge : sA2 Nat.≤ Fin.toℕ z2r
              z2rge = subst (sA2 Nat.≤_) (sym z2rN) (Nat.m≤m+n sA2 (sA1 + f2))
              l1f = (assocSwapᵣ sA1 2 ↑* sA2) z2r
              l1 : Fin.toℕ l1f ≡ sA2 + f2
              l1 = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 z2r z2rge
                 ■ cong (sA2 +_) (toℕ-assoc-mid sA1 2 (Fin.reduce≥ z2r z2rge) midlo midhi ■ cong (Nat._∸ sA1) redz ■ Nat.m+n∸m≡n sA1 f2)
                where redz : Fin.toℕ (Fin.reduce≥ z2r z2rge) ≡ sA1 + f2
                      redz = toℕ-reduce≥ z2r z2rge ■ cong (Nat._∸ sA2) z2rN ■ Nat.m+n∸m≡n sA2 (sA1 + f2)
                      midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ z2r z2rge)
                      midlo = subst (sA1 Nat.≤_) (sym redz) (Nat.m≤m+n sA1 f2)
                      midhi : Fin.toℕ (Fin.reduce≥ z2r z2rge) Nat.< sA1 + 2
                      midhi = subst (Nat._< sA1 + 2) (sym redz) (Nat.+-monoʳ-< sA1 f2lt2)
              l2 : Fin.toℕ (assocSwapᵣ sA2 2 l1f) ≡ f2
              l2 = toℕ-assoc-mid sA2 2 l1f (subst (sA2 Nat.≤_) (sym l1) (Nat.m≤m+n sA2 f2))
                     (subst (Nat._< sA2 + 2) (sym l1) (Nat.+-monoʳ-< sA2 f2lt2))
                 ■ cong (Nat._∸ sA2) l1 ■ Nat.m+n∸m≡n sA2 f2
              z3 : Fin.toℕ ((((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2f) ≡ sB1 + Fin.toℕ (assocSwapᵣ sA2 2 l1f)
              z3 = toℕ-↑*-ge ((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 z2f z2q
      Φ-B-body : Fin.toℕ (Ωᵗ x3) ≡ f
      Φ-B-body with Nat.<-cmp f sB2 | Nat.<-cmp f (sB2 + sB1)
      ... | tri< flt2 _ _ | _ = B1 flt2
      ... | tri≈ _ feq2 _ | tri< flt21 _ _ = B2 (Nat.≤-reflexive (sym feq2)) flt21
      ... | tri> _ _ fgt2 | tri< flt21 _ _ = B2 (Nat.<⇒≤ fgt2) flt21
      ... | tri≈ _ feq2 _ | tri≈ _ feq21 _ = B3 (Nat.≤-reflexive (sym feq21))
      ... | tri≈ _ feq2 _ | tri> _ _ fgt21 = B3 (Nat.<⇒≤ fgt21)
      ... | tri> _ _ fgt2 | tri≈ _ feq21 _ = B3 (Nat.≤-reflexive (sym feq21))
      ... | tri> _ _ fgt2 | tri> _ _ fgt21 = B3 (Nat.<⇒≤ fgt21)

