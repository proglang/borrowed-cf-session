-- | The REPAIRED factorisation: `factor′`, without `BlockBridge`.
--
--   `Bridge.blockBridge-refuted` shows the old cut (`Factor.factor`'s
--   hypothesis) is FALSE: two `~`-related block forms need not be
--   `~ᵇ`-related, because a `perm-νφ` under a `tν` prefix migrates a φ cell
--   between blocks while `~ᵇ` is parity-locked.  The factorisation THEOREM
--   survives with the cut moved to the M side:
--
--     factor′ : Block (tel M) → N ~ M →
--               Σ[ M′ ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
--
--   Proof shape (chain induction, right to left):
--     * a φ-only generator joins the `~ᵩ` leg;
--     * a ν-reindexing generator becomes a RESIDUE (Normal.Slots) that is
--       pushed through the remaining `~ᵩ` leg (`resolve`, via `push`) and
--       discharged against the block form (`realise`): a pair flip is
--       `ν1ᵇ` verbatim, and a gap transposition is one `bswpᵇ` — the two
--       blocks swap WITH their runs, and the run mismatch is repaid by a
--       `~ᵩ` run-exchange (`exchange`), which is precisely the move the
--       Bridge counterexample showed `~ᵇ` cannot make and `~ᵩ` can.
--
--   Linked-φ: `Res` targets are ABSTRACT (Normal.Slots) and carry the
--   defining `_++ᵗ_` equations plus a front-independence witness `FIT`, so
--   `push` aligns the residue's region against a `~ᵩ` step by `cmpᵗ`, and
--   `realise` feeds `FIT` through `fit→FInner` into the FRun-parameterised
--   `bswpᵇ` (Normal.Factor).
module BorrowedCF.Simulation.Support.Normal.Factor2 where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv
open import BorrowedCF.Simulation.Support.Normal.Shift using (shift2; shift1; liftId-·; liftId-++ᵗ; liftId-cong)
open import BorrowedCF.Simulation.Support.Normal.Witness
  using (aswap-11-inv; aswap-12-21; aswap-22-inv; swap-11-inv)
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id; ++ᵗ-idʳ; ++ᵗ-assoc; liftId-liftRen; renTel-idᵗ)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (map-⋯-cong; map-⋯-id; ≡→~; telMidᴺ; wkTel-shift2-tν;
         liftMid; liftRen-substⁱ; innerOf-substⁱ; renTel-substⁱ; liftId-subst)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel; liftRen; renTel-id; innerOf)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (map-fuse; NF-≡; subst-tν; subst-tφ; subst-++ᵗ; subst-■; renTel-++ᵗ; liftRen-++ᵗ; innerOf-++ᵗ;
         renTel-renTel; renTel-cong; innerOf-renTel; innerOf-id; map-⋯-subst; liftRen-·; liftRen-cong)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
open import BorrowedCF.Simulation.Support.Normal.Factor
open import BorrowedCF.Simulation.Support.Normal.FrontIndep
open import BorrowedCF.Simulation.Support.Normal.Slots

open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Nat.Variables

------------------------------------------------------------------------
-- `~ᵩ` congruence for telescope prefixes (clone of Factor.~-prefix).
------------------------------------------------------------------------

~ᵩ-prefix : ∀ {n j} (s : Tel n j) {N₁ N₂ : NF j} → N₁ ~ᵩ N₂ →
            prefixNF s N₁ ~ᵩ prefixNF s N₂
~ᵩ-prefix []          c = c
~ᵩ-prefix (tν s)      c = ~ᵩ-νNF (~ᵩ-prefix s c)
~ᵩ-prefix (tφ f cc s) c = ~ᵩ-φNF cc (~ᵩ-prefix s c)

------------------------------------------------------------------------
-- Dragging a run outward, inside `~ᵩ` (FRun twin of Factor.drag-sound).
------------------------------------------------------------------------

dragᵩ : ∀ {b p j m k} (ω : b →ᵣ p) (S : Tel p j) {r : Tel j m} {w : Run r}
        (fw : FRun b ω S w) (t : Tel m k) (es : List (Tm k)) →
        mkNF (S ++ᵗ (r ++ᵗ t)) es ~ᵩ mkNF (dragTel ω S fw t) (map (_⋯ dragRen ω S fw t) es)
dragᵩ ω S (frnil _ _) t es =
  ≡→~ᵩ (cong (mkNF (S ++ᵗ t)) (sym (map-⋯-id (λ _ → refl) es)))
dragᵩ {b} {p} {j} ω S (frφ {f = f} _ _ cf {r = r} fw) t es =
  ~ᵩ-trans (bubbleφᵩ⁻ f (cf ⋯ ω) S (r ++ᵗ t) es)
    (~ᵩ-trans (≡→~ᵩ eqA)
      (~ᵩ-trans (~ᵩ-φNF (cf ⋯ ω)
                  (dragᵩ (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) fw
                              (retail t (tailRen r (bubφ⁻ S)))
                              (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)))
               (≡→~ᵩ (cong (mkNF (dragTel ω S (frφ ω S cf fw) t))
                          (map-fuse (liftId (r ++ᵗ t) (bubφ⁻ S))
                                    (dragRen (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) fw
                                             (retail t (tailRen r (bubφ⁻ S)))) es)))))
  where
    telReconcile : subst (Tel (1 + j)) (renTel-id (r ++ᵗ t)) (renTel (r ++ᵗ t) (bubφ⁻ S))
                     ≡ r ++ᵗ retail t (tailRen r (bubφ⁻ S))
    telReconcile =
      cong (λ e → subst (Tel (1 + j)) e (renTel (r ++ᵗ t) (bubφ⁻ S)))
           (≡-irrelevant (renTel-id (r ++ᵗ t))
             (innerOf-++ᵗ r t (1 + j) ■ (cong (innerOf t) (renTel-id r) ■ renTel-id t)))
        ■ subst-■ (Tel (1 + j)) (innerOf-++ᵗ r t (1 + j))
            (cong (innerOf t) (renTel-id r) ■ renTel-id t) (renTel (r ++ᵗ t) (bubφ⁻ S))
        ■ cong (subst (Tel (1 + j)) (cong (innerOf t) (renTel-id r) ■ renTel-id t))
               (renTel-++ᵗ r t (bubφ⁻ S))
        ■ subst-■ (Tel (1 + j)) (cong (innerOf t) (renTel-id r)) (renTel-id t)
            (renTel r (bubφ⁻ S) ++ᵗ renTel t (liftRen r (bubφ⁻ S)))
        ■ cong (subst (Tel (1 + j)) (renTel-id t))
               ( telMidᴺ (renTel-id r) (renTel r (bubφ⁻ S)) t (λ y → refl)
               ■ cong (_++ᵗ renTel t (tailRen r (bubφ⁻ S)))
                      (runFixed (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) (shift1 S) (bubφ⁻ S) (λ x → FIX S (ω x)) fw) )
        ■ subst-++ᵗ r (renTel-id t) (renTel t (tailRen r (bubφ⁻ S)))

    eqA : mkNF (tφ f (cf ⋯ ω) (shift1 S ++ᵗ renTel (r ++ᵗ t) (bubφ⁻ S)))
               (map (_⋯ liftRen (r ++ᵗ t) (bubφ⁻ S)) es)
            ≡ mkNF (tφ f (cf ⋯ ω) (shift1 S ++ᵗ (r ++ᵗ retail t (tailRen r (bubφ⁻ S)))))
                   (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)
    eqA = NF-≡ (renTel-id (r ++ᵗ t))
            ( subst-tφ (renTel-id (r ++ᵗ t)) f (cf ⋯ ω) (shift1 S ++ᵗ renTel (r ++ᵗ t) (bubφ⁻ S))
            ■ cong (tφ f (cf ⋯ ω))
                   ( subst-++ᵗ (shift1 S) (renTel-id (r ++ᵗ t)) (renTel (r ++ᵗ t) (bubφ⁻ S))
                   ■ cong (shift1 S ++ᵗ_) telReconcile ) )
            ( map-⋯-subst (renTel-id (r ++ᵗ t)) (λ x → liftId-liftRen (r ++ᵗ t) (bubφ⁻ S) x) es )

------------------------------------------------------------------------
-- General lift/swap commutations (arbitrary scopes).
------------------------------------------------------------------------

comm-↑²-swap11-gen : ∀ {m m′} (ρ : m →ᵣ m′) (z : 𝔽 (2 + m)) →
                     swapᵣ 1 1 ((ρ ↑* 2) z) ≡ (ρ ↑* 2) (swapᵣ 1 1 z)
comm-↑²-swap11-gen ρ zero          = refl
comm-↑²-swap11-gen ρ (suc zero)    = refl
comm-↑²-swap11-gen ρ (suc (suc z)) = refl

-- The pair-flip and a lifted endo commute on a telescope, up to the two
-- innerOf-scope realignments (the heterogeneity the recipe flags).
swap-comm-tel : ∀ {p p′ k} (ρ : p →ᵣ p′) (t : Tel (2 + p) k) →
                subst (Tel (2 + p′)) (innerOf-renTel t (swapᵣ 1 1) (2 + p′))
                      (renTel (renTel t (swapᵣ 1 1)) (ρ ↑* 2))
                  ≡ subst (Tel (2 + p′)) (innerOf-renTel t (ρ ↑* 2) (2 + p′))
                          (renTel (renTel t (ρ ↑* 2)) (swapᵣ 1 1))
swap-comm-tel ρ t =
  renTel-renTel t (swapᵣ 1 1) (ρ ↑* 2)
    ■ renTel-cong t (λ z → sym (comm-↑²-swap11-gen ρ z))
    ■ sym (renTel-renTel t (ρ ↑* 2) (swapᵣ 1 1))

-- The thread-level twin of `swap-comm-tel` (via `liftRen-·`).
swap-comm-thr : ∀ {p p′ k} (ρ : p →ᵣ p′) (t : Tel (2 + p) k) (x : 𝔽 k) →
                subst 𝔽 (innerOf-renTel t (swapᵣ 1 1) (2 + p′))
                      (liftRen (renTel t (swapᵣ 1 1)) (ρ ↑* 2) (liftRen t (swapᵣ 1 1) x))
                  ≡ subst 𝔽 (innerOf-renTel t (ρ ↑* 2) (2 + p′))
                          (liftRen (renTel t (ρ ↑* 2)) (swapᵣ 1 1) (liftRen t (ρ ↑* 2) x))
swap-comm-thr ρ t x =
  liftRen-· t (swapᵣ 1 1) (ρ ↑* 2) x
    ■ liftRen-cong t (λ z → sym (comm-↑²-swap11-gen ρ z)) x
    ■ sym (liftRen-· t (ρ ↑* 2) (swapᵣ 1 1) x)

subst-symˡ : ∀ {A : Set} {P : A → Set} {x y} (e : x ≡ y) (p : P x) →
             subst P (sym e) (subst P e p) ≡ p
subst-symˡ refl p = refl

-- `liftRen` ignores the renaming baked into a `renTel` (leaf renaming is
-- shape-only); twin of `liftId-renTel-cong` at the liftRen level.
liftRen-ig : ∀ {n m m′ k} (t : Tel n k) (ρ₀ ρ₁ : n →ᵣ m) (σ : m →ᵣ m′)
             (x : 𝔽 (innerOf t m)) →
             subst 𝔽 (innerOf-renTel t ρ₀ m′) (liftRen (renTel t ρ₀) σ x)
               ≡ subst 𝔽 (innerOf-renTel t ρ₁ m′) (liftRen (renTel t ρ₁) σ x)
liftRen-ig []         ρ₀ ρ₁ σ x = refl
liftRen-ig (tν s)     ρ₀ ρ₁ σ x = liftRen-ig s (ρ₀ ↑* 2) (ρ₁ ↑* 2) (σ ↑* 2) x
liftRen-ig (tφ f c s) ρ₀ ρ₁ σ x = liftRen-ig s (ρ₀ ↑)   (ρ₁ ↑)   (σ ↑)   x

-- Renaming a telescope by a pure ambient transport is a transport.
renTel-coe : ∀ {n m k} (e : n ≡ m) (t : Tel n k) →
             renTel t (λ x → subst 𝔽 e x)
               ≡ subst (λ z → Tel z (innerOf t z)) e (subst (Tel n) (sym (renTel-id t)) t)
renTel-coe refl t = sym (subst-symˡ (renTel-id t) _) ■ cong (subst (Tel _) (sym (renTel-id t))) (renTel-idᵗ t)

-- Lifting a pure ambient scope-transport by `↑* 2` is the congruent transport.
↑*2-substᵃ : ∀ {n m} (e : n ≡ m) (x : 𝔽 (2 + n)) →
             ((λ z → subst 𝔽 e z) ↑* 2) x ≡ subst 𝔽 (cong (λ z → 2 + z) e) x
↑*2-substᵃ refl x = id↑* 2 (λ z → refl) x

↑-substᵃ : ∀ {n m} (e : n ≡ m) (x : 𝔽 (1 + n)) →
           ((λ z → subst 𝔽 e z) ↑) x ≡ subst 𝔽 (cong (λ z → 1 + z) e) x
↑-substᵃ refl x = id↑ (λ z → refl) x

subst-symʳ : ∀ {A : Set} {P : A → Set} {x y} (e : x ≡ y) (v : P y) →
             subst P e (subst P (sym e) v) ≡ v
subst-symʳ refl v = refl

-- `assocSwapᵣ 1 1` is natural under a scope transport (J-trivial).
aswap-nat : ∀ {a b} (e : 2 + a ≡ 2 + b) (x : 𝔽 (2 + a)) →
            assocSwapᵣ 1 1 (subst 𝔽 e x) ≡ subst 𝔽 e (assocSwapᵣ 1 1 x)
aswap-nat refl x = refl

-- Collapse three nested 𝔽-substs into a single one (endpoints determine the path).
subst3≡ : ∀ {a b c d} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (w : a ≡ d) (x : 𝔽 a) →
          subst 𝔽 r (subst 𝔽 q (subst 𝔽 p x)) ≡ subst 𝔽 w x
subst3≡ refl refl refl w x = cong (λ e → subst 𝔽 e x) (≡-irrelevant refl w)

-- Six nested 𝔽-substs whose composite is a loop collapse to the identity.
subst6-id : ∀ {a b c d e f} (p₁ : a ≡ b) (p₂ : b ≡ c) (p₃ : c ≡ d) (p₄ : d ≡ e)
            (p₅ : e ≡ f) (p₆ : f ≡ a) (x : 𝔽 a) →
            subst 𝔽 p₆ (subst 𝔽 p₅ (subst 𝔽 p₄ (subst 𝔽 p₃ (subst 𝔽 p₂ (subst 𝔽 p₁ x))))) ≡ x
subst6-id refl refl refl refl refl p₆ x = cong (λ e → subst 𝔽 e x) (≡-irrelevant p₆ refl)

-- Crossing a renTel scope-shift under `liftRen`: the baked ρ (a pure ambient
-- transport) is absorbed into leaf-scope substs, and the applied renaming σ
-- realigns from the shifted scope q back to the base scope n.
glueG : ∀ {n q m₁ m₂ k} (e : n ≡ q) (eN : m₁ ≡ m₂) (t : Tel n k)
        (ρ : n →ᵣ q) (he : ∀ x → ρ x ≡ subst 𝔽 e x)
        (σj : n →ᵣ m₁) (σq : q →ᵣ m₂) (hσ : ∀ x → σq (subst 𝔽 e x) ≡ subst 𝔽 eN (σj x))
        (v : 𝔽 (innerOf t q)) →
        subst 𝔽 (innerOf-renTel t ρ m₂) (liftRen (renTel t ρ) σq v)
          ≡ subst 𝔽 (cong (innerOf t) eN)
                   (liftRen t σj (subst 𝔽 (sym (cong (innerOf t) e) ■ renTel-id t) v))
glueG {n = n} e eN [] ρ he σj σq hσ v =
  cong σq (sym (subst-symʳ e v)) ■ hσ (subst 𝔽 (sym e) v)
    ■ cong (λ p → subst 𝔽 p (σj (subst 𝔽 (sym e) v))) (≡-irrelevant eN (cong (innerOf ([] {n})) eN))
    ■ cong (λ p → subst 𝔽 (cong (innerOf ([] {n})) eN) (σj (subst 𝔽 p v)))
           (≡-irrelevant (sym e) (sym (cong (innerOf ([] {n})) e) ■ renTel-id ([] {n})))
glueG e eN (tν t) ρ he σj σq hσ v =
  glueG (cong (λ z → 2 + z) e) (cong (λ z → 2 + z) eN) t (ρ ↑* 2) he' (σj ↑* 2) (σq ↑* 2) hσ' v
    ■ cong₂ (λ p₁ p₂ → subst 𝔽 p₁ (liftRen t (σj ↑* 2) (subst 𝔽 p₂ v)))
            (≡-irrelevant (cong (innerOf t) (cong (λ z → 2 + z) eN)) (cong (innerOf (tν t)) eN))
            (≡-irrelevant (sym (cong (innerOf t) (cong (λ z → 2 + z) e)) ■ renTel-id t)
                          (sym (cong (innerOf (tν t)) e) ■ renTel-id (tν t)))
  where
    he' : ∀ x → (ρ ↑* 2) x ≡ subst 𝔽 (cong (λ z → 2 + z) e) x
    he' x = (he ~↑* 2) x ■ ↑*2-substᵃ e x
    hσ' : ∀ x → (σq ↑* 2) (subst 𝔽 (cong (λ z → 2 + z) e) x)
                  ≡ subst 𝔽 (cong (λ z → 2 + z) eN) ((σj ↑* 2) x)
    hσ' x = cong (σq ↑* 2) (sym (↑*2-substᵃ e x))
          ■ sym (dist-↑*-· 2 (λ z → subst 𝔽 e z) σq x)
          ■ (hσ ~↑* 2) x
          ■ dist-↑*-· 2 σj (λ z → subst 𝔽 eN z) x
          ■ ↑*2-substᵃ eN ((σj ↑* 2) x)
glueG e eN (tφ f c t) ρ he σj σq hσ v =
  glueG (cong (λ z → 1 + z) e) (cong (λ z → 1 + z) eN) t (ρ ↑) he' (σj ↑) (σq ↑) hσ' v
    ■ cong₂ (λ p₁ p₂ → subst 𝔽 p₁ (liftRen t (σj ↑) (subst 𝔽 p₂ v)))
            (≡-irrelevant (cong (innerOf t) (cong (λ z → 1 + z) eN)) (cong (innerOf (tφ f c t)) eN))
            (≡-irrelevant (sym (cong (innerOf t) (cong (λ z → 1 + z) e)) ■ renTel-id t)
                          (sym (cong (innerOf (tφ f c t)) e) ■ renTel-id (tφ f c t)))
  where
    he' : ∀ x → (ρ ↑) x ≡ subst 𝔽 (cong (λ z → 1 + z) e) x
    he' x = (he ~↑) x ■ ↑-substᵃ e x
    hσ' : ∀ x → (σq ↑) (subst 𝔽 (cong (λ z → 1 + z) e) x)
                  ≡ subst 𝔽 (cong (λ z → 1 + z) eN) ((σj ↑) x)
    hσ' x = cong (σq ↑) (sym (↑-substᵃ e x))
          ■ sym (dist-↑-· (λ z → subst 𝔽 e z) σq x)
          ■ (hσ ~↑) x
          ■ dist-↑-· σj (λ z → subst 𝔽 eN z) x
          ■ ↑-substᵃ eN ((σj ↑) x)

-- The double-renTel twin of `glueG`: the ambient transport is the COMPOSITE ρ₁·ρ₂.
glueG2 : ∀ {n p q m₁ m₂ k} (e : n ≡ q) (eN : m₁ ≡ m₂) (t : Tel n k)
         (ρ₁ : n →ᵣ p) (ρ₂ : p →ᵣ q) (he : ∀ x → ρ₂ (ρ₁ x) ≡ subst 𝔽 e x)
         (σj : n →ᵣ m₁) (σq : q →ᵣ m₂) (hσ : ∀ x → σq (subst 𝔽 e x) ≡ subst 𝔽 eN (σj x))
         (v : 𝔽 (innerOf (renTel t ρ₁) q)) →
         subst 𝔽 (innerOf-renTel (renTel t ρ₁) ρ₂ m₂ ■ innerOf-renTel t ρ₁ m₂)
               (liftRen (renTel (renTel t ρ₁) ρ₂) σq v)
           ≡ subst 𝔽 (cong (innerOf t) eN)
                    (liftRen t σj (subst 𝔽 (innerOf-renTel t ρ₁ q ■ sym (cong (innerOf t) e) ■ renTel-id t) v))
glueG2 {n = n} e eN [] ρ₁ ρ₂ he σj σq hσ v =
  cong σq (sym (subst-symʳ e v)) ■ hσ (subst 𝔽 (sym e) v)
    ■ cong (λ p → subst 𝔽 p (σj (subst 𝔽 (sym e) v))) (≡-irrelevant eN (cong (innerOf ([] {n})) eN))
    ■ cong (λ p → subst 𝔽 (cong (innerOf ([] {n})) eN) (σj (subst 𝔽 p v)))
           (≡-irrelevant (sym e)
             (innerOf-renTel ([] {n}) ρ₁ _ ■ sym (cong (innerOf ([] {n})) e) ■ renTel-id ([] {n})))
glueG2 e eN (tν t) ρ₁ ρ₂ he σj σq hσ v =
  glueG2 (cong (λ z → 2 + z) e) (cong (λ z → 2 + z) eN) t (ρ₁ ↑* 2) (ρ₂ ↑* 2) he' (σj ↑* 2) (σq ↑* 2) hσ' v
    ■ cong₂ (λ p₁ p₂ → subst 𝔽 p₁ (liftRen t (σj ↑* 2) (subst 𝔽 p₂ v)))
            (≡-irrelevant (cong (innerOf t) (cong (λ z → 2 + z) eN)) (cong (innerOf (tν t)) eN))
            (≡-irrelevant (innerOf-renTel t (ρ₁ ↑* 2) _ ■ sym (cong (innerOf t) (cong (λ z → 2 + z) e)) ■ renTel-id t)
                          (innerOf-renTel (tν t) ρ₁ _ ■ sym (cong (innerOf (tν t)) e) ■ renTel-id (tν t)))
  where
    he' : ∀ x → (ρ₂ ↑* 2) ((ρ₁ ↑* 2) x) ≡ subst 𝔽 (cong (λ z → 2 + z) e) x
    he' x = sym (dist-↑*-· 2 ρ₁ ρ₂ x) ■ (he ~↑* 2) x ■ ↑*2-substᵃ e x
    hσ' : ∀ x → (σq ↑* 2) (subst 𝔽 (cong (λ z → 2 + z) e) x)
                  ≡ subst 𝔽 (cong (λ z → 2 + z) eN) ((σj ↑* 2) x)
    hσ' x = cong (σq ↑* 2) (sym (↑*2-substᵃ e x))
          ■ sym (dist-↑*-· 2 (λ z → subst 𝔽 e z) σq x)
          ■ (hσ ~↑* 2) x
          ■ dist-↑*-· 2 σj (λ z → subst 𝔽 eN z) x
          ■ ↑*2-substᵃ eN ((σj ↑* 2) x)
glueG2 e eN (tφ f c t) ρ₁ ρ₂ he σj σq hσ v =
  glueG2 (cong (λ z → 1 + z) e) (cong (λ z → 1 + z) eN) t (ρ₁ ↑) (ρ₂ ↑) he' (σj ↑) (σq ↑) hσ' v
    ■ cong₂ (λ p₁ p₂ → subst 𝔽 p₁ (liftRen t (σj ↑) (subst 𝔽 p₂ v)))
            (≡-irrelevant (cong (innerOf t) (cong (λ z → 1 + z) eN)) (cong (innerOf (tφ f c t)) eN))
            (≡-irrelevant (innerOf-renTel t (ρ₁ ↑) _ ■ sym (cong (innerOf t) (cong (λ z → 1 + z) e)) ■ renTel-id t)
                          (innerOf-renTel (tφ f c t) ρ₁ _ ■ sym (cong (innerOf (tφ f c t)) e) ■ renTel-id (tφ f c t)))
  where
    he' : ∀ x → (ρ₂ ↑) ((ρ₁ ↑) x) ≡ subst 𝔽 (cong (λ z → 1 + z) e) x
    he' x = sym (dist-↑-· ρ₁ ρ₂ x) ■ (he ~↑) x ■ ↑-substᵃ e x
    hσ' : ∀ x → (σq ↑) (subst 𝔽 (cong (λ z → 1 + z) e) x)
                  ≡ subst 𝔽 (cong (λ z → 1 + z) eN) ((σj ↑) x)
    hσ' x = cong (σq ↑) (sym (↑-substᵃ e x))
          ■ sym (dist-↑-· (λ z → subst 𝔽 e z) σq x)
          ■ (hσ ~↑) x
          ■ dist-↑-· σj (λ z → subst 𝔽 eN z) x
          ■ ↑-substᵃ eN ((σj ↑) x)

-- `liftRen` through a telescope carried along a pure ambient scope-transport
-- (J-trivial: the transport collapses on the refl-index).
-- `liftRen (renTel t ρ) σ` reads only the shape of `t` (endo ρ drops, up to the
-- leaf-scope realignment `renTel-id t`).
liftRen-renId : ∀ {n m k} (t : Tel n k) (ρ : n →ᵣ n) (σ : n →ᵣ m) (v : 𝔽 k) →
                subst 𝔽 (innerOf-renTel t ρ m)
                      (liftRen (renTel t ρ) σ (subst 𝔽 (sym (renTel-id t)) v)) ≡ liftRen t σ v
liftRen-renId []         ρ σ v = refl
liftRen-renId (tν t)     ρ σ v = liftRen-renId t (ρ ↑* 2) (σ ↑* 2) v
liftRen-renId (tφ f c t) ρ σ v = liftRen-renId t (ρ ↑)    (σ ↑)   v

liftRen-substᵃ : ∀ {n m k} (e : 2 + n ≡ 2 + m) (t : Tel (2 + n) k) (v : 𝔽 k) →
                 subst 𝔽 (innerOf-renTel t (λ x → subst 𝔽 e x) (2 + m))
                       (liftRen (renTel t (λ x → subst 𝔽 e x)) (assocSwapᵣ 1 1)
                                (subst 𝔽 (sym (renTel-id t) ■ cong (innerOf t) e) v))
                   ≡ subst 𝔽 (cong (innerOf t) e) (liftRen t (assocSwapᵣ 1 1) v)
liftRen-substᵃ refl t v =
  cong (λ p → subst 𝔽 (innerOf-renTel t (idₖ ⦃ Kᵣ ⦄) _)
                    (liftRen (renTel t (idₖ ⦃ Kᵣ ⦄)) (assocSwapᵣ 1 1) (subst 𝔽 p v)))
       (≡-irrelevant (sym (renTel-id t) ■ cong (innerOf t) refl) (sym (renTel-id t)))
    ■ liftRen-renId t (idₖ ⦃ Kᵣ ⦄) (assocSwapᵣ 1 1) v

-- Pushing a leaf-scope transport of a list out through a `map (_⋯ σ)`.
map-⋯-substTm : ∀ {a b k} (e : k ≡ a) (σ : a →ᵣ b) (xs : List (Tm k)) →
                map (_⋯ σ) (subst (λ z → List (Tm z)) e xs)
                  ≡ map (_⋯ (λ y → σ (subst 𝔽 e y))) xs
map-⋯-substTm refl σ xs = refl

-- swapᵣ 1 1 and assocSwapᵣ 1 1 agree pointwise.
swap11≗aswap11 : ∀ {m} (z : 𝔽 (2 + m)) → swapᵣ 1 1 z ≡ assocSwapᵣ 1 1 z
swap11≗aswap11 zero          = refl
swap11≗aswap11 (suc zero)    = refl
swap11≗aswap11 (suc (suc z)) = refl

comm-↑²-aswap11-gen : ∀ {m m′} (ρ : m →ᵣ m′) (z : 𝔽 (2 + m)) →
                      assocSwapᵣ 1 1 ((ρ ↑* 2) z) ≡ (ρ ↑* 2) (assocSwapᵣ 1 1 z)
comm-↑²-aswap11-gen ρ zero          = refl
comm-↑²-aswap11-gen ρ (suc zero)    = refl
comm-↑²-aswap11-gen ρ (suc (suc z)) = refl

-- aswap-11 and a lifted endo commute on a telescope / on threads.
aswap-comm-tel : ∀ {p p′ k} (ρ : p →ᵣ p′) (t : Tel (2 + p) k) →
                 subst (Tel (2 + p′)) (innerOf-renTel t (assocSwapᵣ 1 1) (2 + p′))
                       (renTel (renTel t (assocSwapᵣ 1 1)) (ρ ↑* 2))
                   ≡ subst (Tel (2 + p′)) (innerOf-renTel t (ρ ↑* 2) (2 + p′))
                           (renTel (renTel t (ρ ↑* 2)) (assocSwapᵣ 1 1))
aswap-comm-tel ρ t =
  renTel-renTel t (assocSwapᵣ 1 1) (ρ ↑* 2)
    ■ renTel-cong t (λ z → sym (comm-↑²-aswap11-gen ρ z))
    ■ sym (renTel-renTel t (ρ ↑* 2) (assocSwapᵣ 1 1))

aswap-comm-thr : ∀ {p p′ k} (ρ : p →ᵣ p′) (t : Tel (2 + p) k) (x : 𝔽 k) →
                 subst 𝔽 (innerOf-renTel t (assocSwapᵣ 1 1) (2 + p′))
                       (liftRen (renTel t (assocSwapᵣ 1 1)) (ρ ↑* 2) (liftRen t (assocSwapᵣ 1 1) x))
                   ≡ subst 𝔽 (innerOf-renTel t (ρ ↑* 2) (2 + p′))
                           (liftRen (renTel t (ρ ↑* 2)) (assocSwapᵣ 1 1) (liftRen t (ρ ↑* 2) x))
aswap-comm-thr ρ t x =
  liftRen-· t (assocSwapᵣ 1 1) (ρ ↑* 2) x
    ■ liftRen-cong t (λ z → sym (comm-↑²-aswap11-gen ρ z)) x
    ■ sym (liftRen-· t (ρ ↑* 2) (assocSwapᵣ 1 1) x)

------------------------------------------------------------------------
-- Heterogeneous `gapρ` commutation (for the swap-residue cmp cases).
------------------------------------------------------------------------

-- `assocSwapᵣ 2 2` commutes with a doubly-lifted renaming (fixes the two
-- ν pairs, renames the remainder).
gcomm22 : ∀ {a b} (ρ : a →ᵣ b) (y : 𝔽 (2 + (2 + a))) →
          assocSwapᵣ 2 2 ((ρ ↑* 2 ↑* 2) y) ≡ (ρ ↑* 2 ↑* 2) (assocSwapᵣ 2 2 y)
gcomm22 ρ zero                      = refl
gcomm22 ρ (suc zero)                = refl
gcomm22 ρ (suc (suc zero))          = refl
gcomm22 ρ (suc (suc (suc zero)))    = refl
gcomm22 ρ (suc (suc (suc (suc y)))) = refl

-- gen versions of the Slots `comm-↑³` lemmas (arbitrary target scope).
comm-↑³-aswap12-gen : ∀ {m m′} (ζ : m →ᵣ m′) (y : 𝔽 (1 + (2 + m))) →
                      assocSwapᵣ 1 2 ((ζ ↑* 3) y) ≡ (ζ ↑* 3) (assocSwapᵣ 1 2 y)
comm-↑³-aswap12-gen ζ zero                = refl
comm-↑³-aswap12-gen ζ (suc zero)          = refl
comm-↑³-aswap12-gen ζ (suc (suc zero))    = refl
comm-↑³-aswap12-gen ζ (suc (suc (suc y))) = refl

comm-↑³-aswap21-gen : ∀ {m m′} (ζ : m →ᵣ m′) (y : 𝔽 (2 + (1 + m))) →
                      assocSwapᵣ 2 1 ((ζ ↑* 3) y) ≡ (ζ ↑* 3) (assocSwapᵣ 2 1 y)
comm-↑³-aswap21-gen ζ zero                = refl
comm-↑³-aswap21-gen ζ (suc zero)          = refl
comm-↑³-aswap21-gen ζ (suc (suc zero))    = refl
comm-↑³-aswap21-gen ζ (suc (suc (suc y))) = refl

-- Naturality of a leaf-endo `liftId t ρ₀` against an ambient renaming
-- `liftRen t τ`: transport-free, since both land at `innerOf t n′`.
liftRen-liftId-nat : ∀ {n k n′} (t : Tel n k) (ρ₀ : n →ᵣ n) (τ : n →ᵣ n′) (τ′ : n′ →ᵣ n′)
                     (h : ∀ z → τ (ρ₀ z) ≡ τ′ (τ z)) (v : 𝔽 k) →
                     liftRen t τ (liftId t ρ₀ v) ≡ liftId (renTel t τ) τ′ (liftRen t τ v)
liftRen-liftId-nat []         ρ₀ τ τ′ h v = h v
liftRen-liftId-nat (tν t)     ρ₀ τ τ′ h v =
  liftRen-liftId-nat t (ρ₀ ↑* 2) (τ ↑* 2) (τ′ ↑* 2)
    (λ z → sym (dist-↑*-· 2 ρ₀ τ z) ■ (h ~↑* 2) z ■ dist-↑*-· 2 τ τ′ z) v
liftRen-liftId-nat (tφ f c t) ρ₀ τ τ′ h v =
  liftRen-liftId-nat t (ρ₀ ↑) (τ ↑) (τ′ ↑)
    (λ z → sym (dist-↑-· ρ₀ τ z) ■ (h ~↑) z ■ dist-↑-· τ τ′ z) v

-- The `↑* 2`-lifted form of `liftRen-liftId-nat` (over one ν pair).
LLcomm : ∀ {n k n′} (t : Tel n k) (ρ₀ : n →ᵣ n) (τ : n →ᵣ n′) (τ′ : n′ →ᵣ n′)
         (h : ∀ z → τ (ρ₀ z) ≡ τ′ (τ z)) (y : 𝔽 (2 + k)) →
         (liftRen t τ ↑* 2) ((liftId t ρ₀ ↑* 2) y)
           ≡ (liftId (renTel t τ) τ′ ↑* 2) ((liftRen t τ ↑* 2) y)
LLcomm t ρ₀ τ τ′ h y =
  sym (dist-↑*-· 2 (liftId t ρ₀) (liftRen t τ) y)
    ■ (pw ~↑* 2) y
    ■ dist-↑*-· 2 (liftRen t τ) (liftId (renTel t τ) τ′) y
  where
    pw : (liftId t ρ₀ ·ₖ liftRen t τ) ≗ (liftRen t τ ·ₖ liftId (renTel t τ) τ′)
    pw z = liftRen-liftId-nat t ρ₀ τ τ′ h z

-- The commutation of `gapρ a w` with `liftRen a (ρ ↑* 2) ↑* 2`.  The two
-- `gapρ`s are for different telescopes/runs (`a` vs `renTel a (ρ↑*2)`);
-- both act on `𝔽 (2 + innerOf a (2 + j′))` after the leaf renaming, so the
-- pointwise statement is homogeneous.
gapρ-comm-pt : ∀ {j j′ i} (a : Tel (2 + j) i) (w : Run a) (ρ : j →ᵣ j′) (x : 𝔽 (2 + i)) →
  (liftRen a (ρ ↑* 2) ↑* 2) (gapρ a w x)
    ≡ gapρ (renTel a (ρ ↑* 2)) (runRen w (ρ ↑* 2)) ((liftRen a (ρ ↑* 2) ↑* 2) x)
gapρ-comm-pt [] rnil ρ x = sym (gcomm22 ρ x)
gapρ-comm-pt (tφ f c a′) (rφ w′) ρ x =
  LLcomm a′ (assocSwapᵣ 2 1) (ρ ↑* 3) (assocSwapᵣ 2 1)
         (λ z → sym (comm-↑³-aswap21-gen ρ z)) (gapρ a′ w′ ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
    ■ cong (liftId (renTel a′ (ρ ↑* 3)) (assocSwapᵣ 2 1) ↑* 2)
           (gapρ-comm-pt a′ w′ (ρ ↑) ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
    ■ cong (λ u → (liftId (renTel a′ (ρ ↑* 3)) (assocSwapᵣ 2 1) ↑* 2)
                    (gapρ (renTel a′ (ρ ↑* 3)) (runRen w′ (ρ ↑* 3)) u))
           (LLcomm a′ (assocSwapᵣ 1 2) (ρ ↑* 3) (assocSwapᵣ 1 2)
                   (λ z → sym (comm-↑³-aswap12-gen ρ z)) x)

-- Telescope / thread level packaging of `gapρ-comm-pt` (aswap-comm twins).
gapρ-comm-tel : ∀ {j j′ i k} (a : Tel (2 + j) i) (w : Run a) (ρ : j →ᵣ j′) (t : Tel (2 + i) k) →
  subst (Tel (2 + innerOf a (2 + j′))) (innerOf-renTel t (gapρ a w) (2 + innerOf a (2 + j′)))
        (renTel (renTel t (gapρ a w)) (liftRen a (ρ ↑* 2) ↑* 2))
    ≡ subst (Tel (2 + innerOf a (2 + j′)))
            (innerOf-renTel t (liftRen a (ρ ↑* 2) ↑* 2) (2 + innerOf a (2 + j′)))
            (renTel (renTel t (liftRen a (ρ ↑* 2) ↑* 2))
                    (gapρ (renTel a (ρ ↑* 2)) (runRen w (ρ ↑* 2))))
gapρ-comm-tel a w ρ t =
  renTel-renTel t (gapρ a w) (liftRen a (ρ ↑* 2) ↑* 2)
    ■ renTel-cong t (λ z → gapρ-comm-pt a w ρ z)
    ■ sym (renTel-renTel t (liftRen a (ρ ↑* 2) ↑* 2)
                         (gapρ (renTel a (ρ ↑* 2)) (runRen w (ρ ↑* 2))))

gapρ-comm-thr : ∀ {j j′ i k} (a : Tel (2 + j) i) (w : Run a) (ρ : j →ᵣ j′) (t : Tel (2 + i) k)
                (x : 𝔽 k) →
  subst 𝔽 (innerOf-renTel t (gapρ a w) (2 + innerOf a (2 + j′)))
        (liftRen (renTel t (gapρ a w)) (liftRen a (ρ ↑* 2) ↑* 2) (liftRen t (gapρ a w) x))
    ≡ subst 𝔽 (innerOf-renTel t (liftRen a (ρ ↑* 2) ↑* 2) (2 + innerOf a (2 + j′)))
            (liftRen (renTel t (liftRen a (ρ ↑* 2) ↑* 2))
                     (gapρ (renTel a (ρ ↑* 2)) (runRen w (ρ ↑* 2)))
                     (liftRen t (liftRen a (ρ ↑* 2) ↑* 2) x))
gapρ-comm-thr a w ρ t x =
  liftRen-· t (gapρ a w) (liftRen a (ρ ↑* 2) ↑* 2) x
    ■ liftRen-cong t (λ z → gapρ-comm-pt a w ρ z) x
    ■ sym (liftRen-· t (liftRen a (ρ ↑* 2) ↑* 2)
                     (gapρ (renTel a (ρ ↑* 2)) (runRen w (ρ ↑* 2))) x)

-- Two `↑* 2`-lifted leaf endos over the same telescope commute whenever their
-- base renamings commute pointwise.
liftId-commAmb : ∀ {n k} (t : Tel n k) (ρ₁ ρ₂ : n →ᵣ n)
                 (h : ∀ y → ρ₁ (ρ₂ y) ≡ ρ₂ (ρ₁ y)) (x : 𝔽 (2 + k)) →
                 (liftId t ρ₁ ↑* 2) ((liftId t ρ₂ ↑* 2) x)
                   ≡ (liftId t ρ₂ ↑* 2) ((liftId t ρ₁ ↑* 2) x)
liftId-commAmb t ρ₁ ρ₂ h x =
    sym (dist-↑*-· 2 (liftId t ρ₂) (liftId t ρ₁) x)
  ■ (commPw ~↑* 2) x
  ■ dist-↑*-· 2 (liftId t ρ₁) (liftId t ρ₂) x
  where
    commPw : (liftId t ρ₂ ·ₖ liftId t ρ₁) ≗ (liftId t ρ₁ ·ₖ liftId t ρ₂)
    commPw z = liftId-· t ρ₂ ρ₁ z
             ■ liftId-cong t (λ y → h y) z
             ■ sym (liftId-· t ρ₁ ρ₂ z)

-- `gapρ a w` commutes with any leaf endo `liftId a (σ ↑* 2) ↑* 2` whose base
-- renaming fixes the innermost ν pair (guaranteed by the `σ ↑* 2` shape).  The
-- two window conjugations commute with `σ ↑* 3` (aswap12/21-gen) and the base
-- with `σ ↑* 4` (gcomm22); the run cell recurses on `σ ↑ᵣ`.
gapρ-comm-amb : ∀ {j i} (a : Tel (2 + j) i) (w : Run a) (σ : j →ᵣ j) (x : 𝔽 (2 + i)) →
  gapρ a w ((liftId a (σ ↑* 2) ↑* 2) x) ≡ (liftId a (σ ↑* 2) ↑* 2) (gapρ a w x)
gapρ-comm-amb []          rnil    σ x = gcomm22 σ x
gapρ-comm-amb (tφ f c a′) (rφ w′) σ x =
    cong (λ u → (liftId a′ (assocSwapᵣ 2 1) ↑* 2) (gapρ a′ w′ u))
         (liftId-commAmb a′ (assocSwapᵣ 1 2) ((σ ↑ᵣ) ↑* 2)
                         (λ y → comm-↑³-aswap12-gen σ y) x)
  ■ cong (liftId a′ (assocSwapᵣ 2 1) ↑* 2)
         (gapρ-comm-amb a′ w′ (σ ↑ᵣ) ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))
  ■ liftId-commAmb a′ (assocSwapᵣ 2 1) ((σ ↑ᵣ) ↑* 2)
                   (λ y → comm-↑³-aswap21-gen σ y)
                   (gapρ a′ w′ ((liftId a′ (assocSwapᵣ 1 2) ↑* 2) x))

-- `↑* 2` transports a `subst`-conjugation.
conj-↑*2 : ∀ {n m} (e : n ≡ m) (f : n →ᵣ n) (g : m →ᵣ m) →
           (∀ u → subst 𝔽 e (f u) ≡ g (subst 𝔽 e u)) → ∀ v →
           subst 𝔽 (cong (2 +_) e) ((f ↑* 2) v) ≡ (g ↑* 2) (subst 𝔽 (cong (2 +_) e) v)
conj-↑*2 refl f g h v = (h ~↑* 2) v

-- `liftId (renTel t ρ)` is `liftId t` up to the leaf transport (shape-only).
liftId-renTel-nat : ∀ {n k} (t : Tel n k) (ρ σ : n →ᵣ n) (v : 𝔽 (innerOf t n)) →
   subst 𝔽 (renTel-id t) (liftId (renTel t ρ) σ v) ≡ liftId t σ (subst 𝔽 (renTel-id t) v)
liftId-renTel-nat []         ρ σ v = refl
liftId-renTel-nat (tν t)     ρ σ v = liftId-renTel-nat t (ρ ↑* 2) (σ ↑* 2) v
liftId-renTel-nat (tφ f c t) ρ σ v = liftId-renTel-nat t (ρ ↑ᵣ)   (σ ↑ᵣ)   v

liftId-renTel-nat2 : ∀ {n k} (t : Tel n k) (ρ σ : n →ᵣ n) (v : 𝔽 (2 + innerOf t n)) →
   subst 𝔽 (cong (2 +_) (renTel-id t)) ((liftId (renTel t ρ) σ ↑* 2) v)
     ≡ (liftId t σ ↑* 2) (subst 𝔽 (cong (2 +_) (renTel-id t)) v)
liftId-renTel-nat2 t ρ σ =
  conj-↑*2 (renTel-id t) (liftId (renTel t ρ) σ) (liftId t σ) (liftId-renTel-nat t ρ σ)

-- `gapρ` only depends on a telescope's shape: renaming the telescope (and the
-- run) by `ρ` leaves `gapρ` unchanged, up to the leaf transport `renTel-id`.
gapρ-renTel-cong : ∀ {j i} (a : Tel (2 + j) i) (w : Run a) (ρ : (2 + j) →ᵣ (2 + j)) (v : 𝔽 (2 + i)) →
   subst 𝔽 (cong (2 +_) (renTel-id a))
         (gapρ (renTel a ρ) (runRen w ρ) (subst 𝔽 (sym (cong (2 +_) (renTel-id a))) v))
     ≡ gapρ a w v
gapρ-renTel-cong []          rnil    ρ v = refl
gapρ-renTel-cong (tφ f c a′) (rφ w′) ρ v =
    liftId-renTel-nat2 a′ (ρ ↑ᵣ) (assocSwapᵣ 2 1)
      (gapρ (renTel a′ (ρ ↑ᵣ)) (runRen w′ (ρ ↑ᵣ)) W)
  ■ cong (liftId a′ (assocSwapᵣ 2 1) ↑* 2)
      ( cong (λ u → subst 𝔽 e2 (gapρ (renTel a′ (ρ ↑ᵣ)) (runRen w′ (ρ ↑ᵣ)) u))
             (sym (subst-symˡ e2 W))
      ■ gapρ-renTel-cong a′ w′ (ρ ↑ᵣ) (subst 𝔽 e2 W)
      ■ cong (gapρ a′ w′)
          ( liftId-renTel-nat2 a′ (ρ ↑ᵣ) (assocSwapᵣ 1 2) (subst 𝔽 (sym e2) v)
          ■ cong (liftId a′ (assocSwapᵣ 1 2) ↑* 2) (subst-symʳ e2 v) ) )
  where
    e2 = cong (2 +_) (renTel-id a′)
    W = (liftId (renTel a′ (ρ ↑ᵣ)) (assocSwapᵣ 1 2) ↑* 2) (subst 𝔽 (sym e2) v)

-- Fusing / congruence / cancellation of `↑* 2`-lifted leaf endos.
private
  Lfuse : ∀ {j i} (t : Tel (2 + j) i) (τ σ : (2 + j) →ᵣ (2 + j)) (u : 𝔽 (2 + i)) →
          (liftId t σ ↑* 2) ((liftId t τ ↑* 2) u) ≡ (liftId t (τ ·ₖ σ) ↑* 2) u
  Lfuse t τ σ u = sym (dist-↑*-· 2 (liftId t τ) (liftId t σ) u)
                ■ ((λ y → liftId-· t τ σ y) ~↑* 2) u

  Lcong : ∀ {j i} (t : Tel (2 + j) i) {β β′ : (2 + j) →ᵣ (2 + j)} → β ≗ β′ → (u : 𝔽 (2 + i)) →
          (liftId t β ↑* 2) u ≡ (liftId t β′ ↑* 2) u
  Lcong t hβ u = ((λ y → liftId-cong t hβ y) ~↑* 2) u

  Lid : ∀ {j i} (t : Tel (2 + j) i) {β : (2 + j) →ᵣ (2 + j)} → β ≗ idₖ ⦃ Kᵣ ⦄ → (u : 𝔽 (2 + i)) →
        (liftId t β ↑* 2) u ≡ u
  Lid t hβ u = id↑* 2 (λ y → liftId-id t hβ y) u

-- `M ∘ S = S ∘ M` where `M` is the peel composite around `gapρ` and `S` is the
-- head-φ swap `liftId t (assocSwapᵣ 1 1) ↑* 2`.  The two conjugating leaf bundles
-- are mutually inverse, so `S` crosses `gapρ` by a single `gapρ-comm-amb`.
private
  Mcomm : ∀ {m i} (t : Tel (2 + (2 + m)) i) (w : Run t) (z : 𝔽 (2 + i)) →
    (liftId t (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
      ((liftId t (assocSwapᵣ 2 1) ↑* 2)
        (gapρ t w
          ((liftId t (assocSwapᵣ 1 2) ↑* 2)
            ((liftId t (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2)
              ((liftId t (assocSwapᵣ 1 1) ↑* 2) z)))))
      ≡ (liftId t (assocSwapᵣ 1 1) ↑* 2)
          ((liftId t (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
            ((liftId t (assocSwapᵣ 2 1) ↑* 2)
              (gapρ t w
                ((liftId t (assocSwapᵣ 1 2) ↑* 2)
                  ((liftId t (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z)))))
  Mcomm t w z =
      Lfuse t (assocSwapᵣ 2 1) (assocSwapᵣ 2 1 ↑ᵣ) (Gzz)
    ■ cong (λ X → (liftId t γL ↑* 2) (gapρ t w X)) (Lfuse t (assocSwapᵣ 1 2 ↑ᵣ) (assocSwapᵣ 1 2) (LaZ))
    ■ cong (λ z0 → (liftId t γL ↑* 2)
                     (gapρ t w ((liftId t δR ↑* 2) ((liftId t (assocSwapᵣ 1 1) ↑* 2) z0))))
           (sym (INV z))
    ■ cong (λ Y → (liftId t γL ↑* 2) (gapρ t w Y)) (KFUSE (LδRz))
    ■ cong (liftId t γL ↑* 2) (gapρ-comm-amb t w (assocSwapᵣ 1 1) (LδRz))
    ■ ABKFUSE (gapρ t w LδRz)
    ■ cong (λ Y → (liftId t (assocSwapᵣ 1 1) ↑* 2) ((liftId t γL ↑* 2) (gapρ t w Y)))
           (sym (Lfuse t (assocSwapᵣ 1 2 ↑ᵣ) (assocSwapᵣ 1 2) z))
    ■ cong (liftId t (assocSwapᵣ 1 1) ↑* 2)
           (sym (Lfuse t (assocSwapᵣ 2 1) (assocSwapᵣ 2 1 ↑ᵣ) (gapρ t w LcdZ)))
    where
      γL = assocSwapᵣ 2 1 ·ₖ (assocSwapᵣ 2 1 ↑ᵣ)
      δR = (assocSwapᵣ 1 2 ↑ᵣ) ·ₖ assocSwapᵣ 1 2
      LaZ  = (liftId t (assocSwapᵣ 1 1) ↑* 2) z
      LcdZ = (liftId t (assocSwapᵣ 1 2) ↑* 2) ((liftId t (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z)
      LδRz = (liftId t δR ↑* 2) z
      Gzz  = gapρ t w ((liftId t (assocSwapᵣ 1 2) ↑* 2)
                        ((liftId t (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) LaZ))

      b-inv : (δR ·ₖ γL) ≗ idₖ ⦃ Kᵣ ⦄
      b-inv zero = refl
      b-inv (suc zero) = refl
      b-inv (suc (suc zero)) = refl
      b-inv (suc (suc (suc zero))) = refl
      b-inv (suc (suc (suc (suc x)))) = refl

      b-k : ((γL ·ₖ assocSwapᵣ 1 1) ·ₖ δR) ≗ (assocSwapᵣ 1 1 ↑* 2)
      b-k zero = refl
      b-k (suc zero) = refl
      b-k (suc (suc zero)) = refl
      b-k (suc (suc (suc zero))) = refl
      b-k (suc (suc (suc (suc x)))) = refl

      b-abk : ((assocSwapᵣ 1 1 ↑* 2) ·ₖ γL) ≗ (γL ·ₖ assocSwapᵣ 1 1)
      b-abk zero = refl
      b-abk (suc zero) = refl
      b-abk (suc (suc zero)) = refl
      b-abk (suc (suc (suc zero))) = refl
      b-abk (suc (suc (suc (suc x)))) = refl

      INV : ∀ z0 → (liftId t γL ↑* 2) ((liftId t δR ↑* 2) z0) ≡ z0
      INV z0 = Lfuse t δR γL z0 ■ Lid t b-inv z0

      KFUSE : ∀ u → (liftId t δR ↑* 2)
                      ((liftId t (assocSwapᵣ 1 1) ↑* 2) ((liftId t γL ↑* 2) u))
                    ≡ (liftId t (assocSwapᵣ 1 1 ↑* 2) ↑* 2) u
      KFUSE u = cong (liftId t δR ↑* 2) (Lfuse t γL (assocSwapᵣ 1 1) u)
              ■ Lfuse t (γL ·ₖ assocSwapᵣ 1 1) δR u
              ■ Lcong t b-k u

      ABKFUSE : ∀ v → (liftId t γL ↑* 2) ((liftId t (assocSwapᵣ 1 1 ↑* 2) ↑* 2) v)
                      ≡ (liftId t (assocSwapᵣ 1 1) ↑* 2) ((liftId t γL ↑* 2) v)
      ABKFUSE v = Lfuse t (assocSwapᵣ 1 1 ↑* 2) γL v
                ■ Lcong t b-abk v
                ■ sym (Lfuse t γL (assocSwapᵣ 1 1) v)

-- `subst` by an equality path is injective.
subst-inj : ∀ {A : Set} {P : A → Set} {x y} (e : x ≡ y) {a b : P x} →
            subst P e a ≡ subst P e b → a ≡ b
subst-inj refl q = q

-- `↑* 2` transports a one-sided (codomain-only) `subst`-conjugation.
lift-cod-↑*2 : ∀ {n m} (e : n ≡ m) (f : m →ᵣ n) (g : m →ᵣ m) →
               (∀ x → subst 𝔽 e (f x) ≡ g x) → ∀ z →
               subst 𝔽 (cong (2 +_) e) ((f ↑* 2) z) ≡ (g ↑* 2) z
lift-cod-↑*2 refl f g h z = (h ~↑* 2) z

-- `↑* 2` form of `liftId-liftRen`: `liftRen t ρ ↑* 2` is `liftId t ρ ↑* 2`
-- after the leaf transport.
liftId-liftRen2 : ∀ {n k} (t : Tel n k) (ρ : n →ᵣ n) (z : 𝔽 (2 + k)) →
                  subst 𝔽 (cong (2 +_) (renTel-id t)) ((liftRen t ρ ↑* 2) z) ≡ (liftId t ρ ↑* 2) z
liftId-liftRen2 t ρ = lift-cod-↑*2 (renTel-id t) (liftRen t ρ) (liftId t ρ) (liftId-liftRen t ρ)

-- FIT is invariant under a leaf-scope transport of its telescope.
FIT-leaf-subst : ∀ {b n k₁ k₂} (ω : b →ᵣ n) (e : k₁ ≡ k₂) (X : Tel n k₁) →
                 FIT ω X → FIT ω (subst (Tel n) e X)
FIT-leaf-subst ω refl X fit = fit

-- Gate preservation: pushing a weakened gate through a lifted renaming
-- commutes the weakening past the renaming (pure ⋯-fusion / N2).
gate-pres : ∀ {j j′} (d : Tm j) (σ : j →ᵣ j′) →
            (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (σ ↑) ≡ (d ⋯ σ) ⋯ weaken* ⦃ Kᵣ ⦄ 1
gate-pres d σ =
  fusion d (weaken* ⦃ Kᵣ ⦄ 1) (σ ↑)
    ■ ⋯-cong d (λ x → N2 σ x)
    ■ sym (fusion d σ (weaken* ⦃ Kᵣ ⦄ 1))

-- Dependent cong: transport a dependent function's value along an equation.
substf : ∀ {A : Set} {P : A → Set} (f : (x : A) → P x) {a b} (e : a ≡ b) →
         subst P e (f a) ≡ f b
substf f refl = refl

-- Re-index a subst through a function of the index.
subst-reix : ∀ {A B : Set} {P : B → Set} (g : A → B) {a b} (e : a ≡ b) (x : P (g a)) →
             subst (λ z → P (g z)) e x ≡ subst P (cong g e) x
subst-reix g refl x = refl

-- Move a `subst` across an equation.
subst-swap : ∀ {A : Set} {P : A → Set} {x y} (e : x ≡ y) {a : P x} {b : P y} →
             subst P e a ≡ b → a ≡ subst P (sym e) b
subst-swap refl q = q

------------------------------------------------------------------------
-- Renaming reflects the spent unit (needed by `pushDel`).
------------------------------------------------------------------------

unit-⋯⁻¹ : ∀ {a b} (e : Tm a) (ρ : a →ᵣ b) → e ⋯ ρ ≡ K `unit → e ≡ K `unit
unit-⋯⁻¹ (K `unit) ρ eq = refl
unit-⋯⁻¹ (K `fork) ρ ()
unit-⋯⁻¹ (K `send) ρ ()
unit-⋯⁻¹ (K `recv) ρ ()
unit-⋯⁻¹ (K `drop) ρ ()
unit-⋯⁻¹ (K `acq) ρ ()
unit-⋯⁻¹ (K `discard) ρ ()
unit-⋯⁻¹ (K (`end p)) ρ ()
unit-⋯⁻¹ (K (`new s)) ρ ()
unit-⋯⁻¹ (K (`lsplit s)) ρ ()
unit-⋯⁻¹ (K (`rsplit s)) ρ ()
unit-⋯⁻¹ (K (`select b)) ρ ()
unit-⋯⁻¹ (K `branch) ρ ()
unit-⋯⁻¹ (` x) ρ ()
unit-⋯⁻¹ (ƛ e) ρ ()
unit-⋯⁻¹ (μ e) ρ ()
unit-⋯⁻¹ (e₁ ·⟨ d ⟩ e₂) ρ ()
unit-⋯⁻¹ (e₁ ; e₂) ρ ()
unit-⋯⁻¹ (e₁ ⊗ e₂) ρ ()
unit-⋯⁻¹ (`let e₁ `in e₂) ρ ()
unit-⋯⁻¹ (`let⊗ e₁ `in e₂) ρ ()
unit-⋯⁻¹ (`inj i e) ρ ()
unit-⋯⁻¹ (`case e `of⟨ e₁ ; e₂ ⟩) ρ ()

------------------------------------------------------------------------
-- Pushing a residue past one `~ᵩ` step.
------------------------------------------------------------------------

private
  ↭-substᵗ : ∀ {k k′} (e : k ≡ k′) {xs ys : List (Tm k)} → xs ↭ ys →
             subst (λ z → List (Tm z)) e xs ↭ subst (λ z → List (Tm z)) e ys
  ↭-substᵗ refl q = q

  endo-undo : ∀ {j k} (t : Tel (2 + j) k) (ρ : (2 + j) →ᵣ (2 + j)) →
              (∀ z → ρ (ρ z) ≡ z) → (es : List (Tm k)) →
              map (_⋯ liftId t ρ) (map (_⋯ liftId t ρ) es) ≡ es
  endo-undo t ρ inv es =
    map-fuse (liftId t ρ) (liftId t ρ) es
      ■ map-⋯-id (λ x → liftId-· t ρ ρ x ■ liftId-id t (λ y → inv y) x) es

  -- Conjugating a codomain thread-permutation to the source of a residue
  -- with an involutive endo renaming `ρ` on its ν-scope.
  conjThr : ∀ {j k₀} (ρ : (2 + j) →ᵣ (2 + j)) → (∀ z → ρ (ρ z) ≡ z) →
            (t : Tel (2 + j) k₀) (es : List (Tm k₀))
            (es₂ : List (Tm (innerOf t (2 + j)))) →
            map (_⋯ liftRen t ρ) es ↭ es₂ →
            Σ[ es_src ∈ List (Tm k₀) ]
              (es ↭ es_src) × (es₂ ≡ map (_⋯ liftRen t ρ) es_src)
  conjThr {j} ρ inv t es es₂ p = es_src , perm , eqE′
    where
      eid : innerOf t (2 + j) ≡ _
      eid = renTel-id t
      es₂₀ : List (Tm _)
      es₂₀ = subst (λ z → List (Tm z)) eid es₂
      es_src : List (Tm _)
      es_src = map (_⋯ liftId t ρ) es₂₀
      es₁₀ : List (Tm _)
      es₁₀ = map (_⋯ liftId t ρ) es
      fact0 : es₁₀ ≡ subst (λ z → List (Tm z)) eid (map (_⋯ liftRen t ρ) es)
      fact0 = sym (map-⋯-subst eid (λ x → liftId-liftRen t ρ x) es)
      q : es₁₀ ↭ es₂₀
      q = ↭-trans (↭-reflexive fact0) (↭-substᵗ eid p)
      perm : es ↭ es_src
      perm = ↭-trans (↭-reflexive (sym (endo-undo t ρ inv es)))
                     (map⁺ (_⋯ liftId t ρ) q)
      κ : _ →ᵣ _
      κ = liftId t ρ ·ₖ liftRen t ρ
      bridgeR : ∀ y → liftRen t ρ y ≡ subst 𝔽 (sym eid) (liftId t ρ y)
      bridgeR y = sym (subst-symˡ eid (liftRen t ρ y))
                    ■ cong (subst 𝔽 (sym eid)) (liftId-liftRen t ρ y)
      hh : ∀ x → subst 𝔽 (sym eid) x ≡ κ x
      hh x = sym ( bridgeR (liftId t ρ x)
                 ■ cong (subst 𝔽 (sym eid)) (liftId-· t ρ ρ x ■ liftId-id t (λ y → inv y) x) )
      step : map (_⋯ κ) es₂₀ ≡ es₂
      step = sym ( sym (subst-symˡ eid es₂)
                 ■ cong (subst (λ z → List (Tm z)) (sym eid))
                        (sym (map-⋯-id (λ _ → refl) es₂₀))
                 ■ map-⋯-subst (sym eid) hh es₂₀ )
      eqE′ : es₂ ≡ map (_⋯ liftRen t ρ) es_src
      eqE′ = sym (map-fuse (liftId t ρ) (liftRen t ρ) es₂₀ ■ step)

  -- Double-renaming of an involution collapses (telescope + threads); clones
  -- of Slots.res-sym's νReconTel/νReconThr for an arbitrary involutive endo.
  invTel : ∀ {p k} (t : Tel p k) (ρ : p →ᵣ p) → (∀ x → ρ (ρ x) ≡ x) →
           subst (Tel p) (innerOf-renTel t ρ p ■ renTel-id t) (renTel (renTel t ρ) ρ) ≡ t
  invTel t ρ inv =
    subst-■ (Tel _) (innerOf-renTel t ρ _) (renTel-id t) (renTel (renTel t ρ) ρ)
      ■ cong (subst (Tel _) (renTel-id t)) (renTel-renTel t ρ ρ ■ renTel-cong t (λ x → inv x))
      ■ renTel-idᵗ t

  invThr : ∀ {p k} (t : Tel p k) (ρ : p →ᵣ p) → (∀ x → ρ (ρ x) ≡ x) → (x : 𝔽 k) →
           subst 𝔽 (innerOf-renTel t ρ p ■ renTel-id t) (liftRen (renTel t ρ) ρ (liftRen t ρ x)) ≡ x
  invThr t ρ inv x =
    subst-■ 𝔽 (innerOf-renTel t ρ _) (renTel-id t) (liftRen (renTel t ρ) ρ (liftRen t ρ x))
      ■ cong (subst 𝔽 (renTel-id t)) (liftRen-· t ρ ρ x ■ liftRen-cong t (λ y → inv y) x)
      ■ liftId-liftRen t (idₖ ⦃ Kᵣ ⦄) x
      ■ liftId-id t (λ _ → refl) x

-- A `~ᵩ` step that does not touch the telescope crosses a residue by
-- conjugation with the residue's (involutive) renaming.
pushThr : ∀ {n k} {N : NF n} (T : Tel n k) (es₁ es₂ : List (Tm k)) → es₁ ↭ es₂ →
          Res N (mkNF T es₁) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushThr T es₁ es₂ p (flipᴿ s t {es = es} refl refl refl fit)
  with conjThr (swapᵣ 1 1) (λ z → swap-11-inv z) t es es₂ p
... | es_src , perm , eqE′ =
      mkNF (s ++ᵗ tν t) es_src , Eq*.return (thrᵩ (s ++ᵗ tν t) perm) ,
      flipᴿ s t {es = es_src} refl refl eqE′ fit
pushThr T es₁ es₂ p (swapᴿ s {a} w t {es = es} refl refl refl fit)
  with conjThr (gapρ a w) (λ z → gapρ-invol a w z) t es es₂ p
... | es_src , perm , eqE′ =
      mkNF (s ++ᵗ tν (a ++ᵗ tν t)) es_src ,
      Eq*.return (thrᵩ (s ++ᵗ tν (a ++ᵗ tν t)) perm) ,
      swapᴿ s w t {es = es_src} refl refl eqE′ fit

pushDel : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T (K `unit ∷ es₂)) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushDel T es₂ (flipᴿ s t {es = []} refl refl () fit)
pushDel T es₂ (flipᴿ s t {es = e₀ ∷ es_rest} refl refl eqE fit) =
  mkNF (s ++ᵗ tν t) es_rest ,
  ~ᵩ-trans (≡→~ᵩ (cong (λ h → mkNF (s ++ᵗ tν t) (h ∷ es_rest)) e0unit))
           (Eq*.return (delᵩ (s ++ᵗ tν t) es_rest)) ,
  flipᴿ s t {es = es_rest} refl refl (∷-injectiveʳ eqE) fit
  where
    e0unit : e₀ ≡ K `unit
    e0unit = unit-⋯⁻¹ e₀ (liftRen t (swapᵣ 1 1)) (sym (∷-injectiveˡ eqE))
pushDel T es₂ (swapᴿ s {a} w t {es = []} refl refl () fit)
pushDel T es₂ (swapᴿ s {a} w t {es = e₀ ∷ es_rest} refl refl eqE fit) =
  mkNF (s ++ᵗ tν (a ++ᵗ tν t)) es_rest ,
  ~ᵩ-trans (≡→~ᵩ (cong (λ h → mkNF (s ++ᵗ tν (a ++ᵗ tν t)) (h ∷ es_rest)) e0unit))
           (Eq*.return (delᵩ (s ++ᵗ tν (a ++ᵗ tν t)) es_rest)) ,
  swapᴿ s w t {es = es_rest} refl refl (∷-injectiveʳ eqE) fit
  where
    e0unit : e₀ ≡ K `unit
    e0unit = unit-⋯⁻¹ e₀ (liftRen t (gapρ a w)) (sym (∷-injectiveˡ eqE))

pushIns : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T es₂) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T (K `unit ∷ es₂))
pushIns T es₂ (flipᴿ s t {es = es} refl refl refl fit) =
  mkNF (s ++ᵗ tν t) (K `unit ∷ es) ,
  ~ᵩ-sym (Eq*.return (delᵩ (s ++ᵗ tν t) es)) ,
  flipᴿ s t {es = K `unit ∷ es} refl refl refl fit
pushIns T es₂ (swapᴿ s {a} w t {es = es} refl refl refl fit) =
  mkNF (s ++ᵗ tν (a ++ᵗ tν t)) (K `unit ∷ es) ,
  ~ᵩ-sym (Eq*.return (delᵩ (s ++ᵗ tν (a ++ᵗ tν t)) es)) ,
  swapᴿ s w t {es = K `unit ∷ es} refl refl refl fit

private
  buildW′ : ∀ {n′ j i} (dg : Tel n′ j) (x y : Flag) (c d : Tm j) (e₃ : Tel (2 + j) i) →
            Run (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) →
            Run (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1))))
  buildW′ []           x y c d e₃ (rφ (rφ we₃)) = rφ (rφ (runRen we₃ (assocSwapᵣ 1 1)))
  buildW′ (tφ f cc dg) x y c d e₃ (rφ w)         = rφ (buildW′ dg x y c d e₃ w)
  buildW′ (tν dg)      x y c d e₃ ()

  -- The leaf renaming `Φ = liftRen e₃ aswap11 ↑* 2` commutes through a single
  -- run-cell conjugation of `gapρ`, reconciling the window-swapped tail `dg ++ᵗ W′`
  -- with the original `dg ++ᵗ W` (LLcomm at the deep window, since aswap11 commutes
  -- with the `↑*2`-lifted prefix endo pointwise).
  gapComm : ∀ {n′ j i} (dg : Tel n′ j) (x y : Flag) (c d : Tm j)
              (e₃ : Tel (2 + j) i) (SW : n′ →ᵣ n′) (u : 𝔽 (2 + i)) →
            (liftId (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))) SW ↑* 2)
              ((liftRen e₃ (assocSwapᵣ 1 1) ↑* 2) u)
              ≡ (liftRen e₃ (assocSwapᵣ 1 1) ↑* 2)
                ((liftId (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) SW ↑* 2) u)
  gapComm dg x y c d e₃ SW u =
      ((λ z → liftId-++ᵗ dg (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))) SW z) ~↑* 2)
        ((liftRen e₃ (assocSwapᵣ 1 1) ↑* 2) u)
    ■ sym (LLcomm e₃ (liftId dg SW ↑* 2) (assocSwapᵣ 1 1) (liftId dg SW ↑* 2)
             (λ z → comm-↑²-aswap11-gen (liftId dg SW) z) u)
    ■ cong (liftRen e₃ (assocSwapᵣ 1 1) ↑* 2)
           (((λ z → sym (liftId-++ᵗ dg (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) SW z)) ~↑* 2) u)

  -- `gapρ` of the window-swapped, run-rebuilt gap commutes with the leaf swap `Φ`.
  -- BESPOKE induction on the run prefix `dg`; the two window cells peel in swapped
  -- order (W peels x-then-y, W′ peels y-then-x), which supplies the transposition
  -- reconciling the leaf against `assocSwapᵣ 2 2`.
  F : ∀ {n′ j i} (dg : Tel (2 + n′) j) (x y : Flag) (c d : Tm j) (e₃ : Tel (2 + j) i)
        (w : Run (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃))) (z : 𝔽 (2 + i)) →
      gapρ (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1))))
           (buildW′ dg x y c d e₃ w)
           ((liftRen e₃ (assocSwapᵣ 1 1) ↑* 2) z)
        ≡ (liftRen e₃ (assocSwapᵣ 1 1) ↑* 2)
           (gapρ (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) w z)
  Fbase : ∀ {m k} (e₃ : Tel (2 + (2 + m)) k) (we₃ : Run e₃) (z : 𝔽 (2 + k)) →
      (liftId (renTel e₃ (assocSwapᵣ 1 1)) (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
        ((liftId (renTel e₃ (assocSwapᵣ 1 1)) (assocSwapᵣ 2 1) ↑* 2)
          (gapρ (renTel e₃ (assocSwapᵣ 1 1)) (runRen we₃ (assocSwapᵣ 1 1))
            ((liftId (renTel e₃ (assocSwapᵣ 1 1)) (assocSwapᵣ 1 2) ↑* 2)
              ((liftId (renTel e₃ (assocSwapᵣ 1 1)) (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2)
                ((liftRen e₃ (assocSwapᵣ 1 1) ↑* 2) z)))))
        ≡ (liftRen e₃ (assocSwapᵣ 1 1) ↑* 2)
            ((liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
              ((liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
                (gapρ e₃ we₃
                  ((liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                    ((liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z)))))
  Fbase e₃ we₃ z =
    subst-inj {P = 𝔽} E (conv-LHS ■ Mcomm e₃ we₃ z ■ sym conv-RHS)
    where
      E = cong (2 +_) (renTel-id e₃)
      ê = renTel e₃ (assocSwapᵣ 1 1)
      Sz = (liftRen e₃ (assocSwapᵣ 1 1) ↑* 2) z
      U4 = (liftId ê (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) Sz
      U3 = (liftId ê (assocSwapᵣ 1 2) ↑* 2) U4
      U2 = gapρ ê (runRen we₃ (assocSwapᵣ 1 1)) U3
      U1 = (liftId ê (assocSwapᵣ 2 1) ↑* 2) U2
      pushGê : ∀ u → subst 𝔽 E (gapρ ê (runRen we₃ (assocSwapᵣ 1 1)) u)
                     ≡ gapρ e₃ we₃ (subst 𝔽 E u)
      pushGê u =
          cong (λ v → subst 𝔽 E (gapρ ê (runRen we₃ (assocSwapᵣ 1 1)) v))
               (sym (subst-symˡ E u))
        ■ gapρ-renTel-cong e₃ we₃ (assocSwapᵣ 1 1) (subst 𝔽 E u)
      conv-LHS : subst 𝔽 E
                   ((liftId ê (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
                     ((liftId ê (assocSwapᵣ 2 1) ↑* 2)
                       (gapρ ê (runRen we₃ (assocSwapᵣ 1 1))
                         ((liftId ê (assocSwapᵣ 1 2) ↑* 2)
                           ((liftId ê (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) Sz)))))
                 ≡ (liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
                     ((liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
                       (gapρ e₃ we₃
                         ((liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                           ((liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2)
                             ((liftId e₃ (assocSwapᵣ 1 1) ↑* 2) z)))))
      conv-LHS =
          liftId-renTel-nat2 e₃ (assocSwapᵣ 1 1) (assocSwapᵣ 2 1 ↑ᵣ) U1
        ■ cong (liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
            ( liftId-renTel-nat2 e₃ (assocSwapᵣ 1 1) (assocSwapᵣ 2 1) U2
            ■ cong (liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
                ( pushGê U3
                ■ cong (gapρ e₃ we₃)
                    ( liftId-renTel-nat2 e₃ (assocSwapᵣ 1 1) (assocSwapᵣ 1 2) U4
                    ■ cong (liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                        ( liftId-renTel-nat2 e₃ (assocSwapᵣ 1 1) (assocSwapᵣ 1 2 ↑ᵣ) Sz
                        ■ cong (liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2)
                               (liftId-liftRen2 e₃ (assocSwapᵣ 1 1) z) ))))
      conv-RHS : subst 𝔽 E
                   ((liftRen e₃ (assocSwapᵣ 1 1) ↑* 2)
                     ((liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
                       ((liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
                         (gapρ e₃ we₃
                           ((liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                             ((liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z))))))
                 ≡ (liftId e₃ (assocSwapᵣ 1 1) ↑* 2)
                     ((liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
                       ((liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
                         (gapρ e₃ we₃
                           ((liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                             ((liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z)))))
      conv-RHS =
        liftId-liftRen2 e₃ (assocSwapᵣ 1 1)
          ((liftId e₃ (assocSwapᵣ 2 1 ↑ᵣ) ↑* 2)
            ((liftId e₃ (assocSwapᵣ 2 1) ↑* 2)
              (gapρ e₃ we₃
                ((liftId e₃ (assocSwapᵣ 1 2) ↑* 2)
                  ((liftId e₃ (assocSwapᵣ 1 2 ↑ᵣ) ↑* 2) z)))))

  F [] x y c d e₃ (rφ (rφ we₃)) z = Fbase e₃ we₃ z
  F (tφ f cc dg) x y c d e₃ (rφ w) z =
      cong (liftId (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))) (assocSwapᵣ 2 1) ↑* 2)
           (cong (gapρ (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1))))
                       (buildW′ dg x y c d e₃ w))
                 (gapComm dg x y c d e₃ (assocSwapᵣ 1 2) z))
    ■ cong (liftId (dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))) (assocSwapᵣ 2 1) ↑* 2)
           (F dg x y c d e₃ w
              ((liftId (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) (assocSwapᵣ 1 2) ↑* 2) z))
    ■ gapComm dg x y c d e₃ (assocSwapᵣ 2 1)
        (gapρ (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) w
              ((liftId (dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)) (assocSwapᵣ 1 2) ↑* 2) z))
  F (tν dg) x y c d e₃ () z

pushφφ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x y : Flag) (c d : Tm j)
         (t₂ : Tel (2 + j) k) (es₂ : List (Tm k)) →
         Res N (mkNF (s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)) es₂) →
         Σ[ N′ ∈ NF n ] (N ~ᵩ N′) ×
           Res N′ (mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂ (assocSwapᵣ 1 1))))
                        (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) es₂))
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  with cmpᵗ s (tν (renTel t (swapᵣ 1 1))) s₂ (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)) (sym eqTᵗ)
... | cmpʳ [] p ()
... | cmpʳ (tν dg) p ()
... | cmpʳ (tφ x′ c′ []) p q with tφ-inj₂ q
...   | ()
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpʳ (tφ x′ c′ (tν dg)) p q with tφ-inj₂ q
...   | ()
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpʳ (tφ x′ c′ (tφ y′ d″ dgap₂)) p q
    with tφ-inj₁ q | tφ-inj-c q | tφ-inj₁ (tφ-inj₂ q) | tφ-inj-c (tφ-inj₂ q) | tφ-inj₂ (tφ-inj₂ q)
...   | refl | refl | refl | refl | refl =
        _ , cleg ,
        subst (λ b → Res (φφRHS) b) reshapeM-NF
          (subst (λ a → Res a flipTarget) reshapeN-NF
             (flipᴿ s′ t′ refl refl refl fit′))
  where
    aswap11 : _ →ᵣ _
    aswap11 = assocSwapᵣ 1 1
    s′ : Tel _ _
    s′ = s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11))
    t′ : Tel (2 + _) _
    t′ = renTel t (liftRen dgap₂ aswap11 ↑* 2)
    esN′ : List (Tm _)
    esN′ = map (_⋯ liftRen (tν t) (liftRen dgap₂ aswap11)) esˢ
    φφRHS : NF _
    φφRHS = mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)))
                 (map (_⋯ liftRen (dgap₂ ++ᵗ tν t) aswap11) esˢ)
    flipTarget : NF _
    flipTarget = mkNF (s′ ++ᵗ tν (renTel t′ (swapᵣ 1 1))) (map (_⋯ liftRen t′ (swapᵣ 1 1)) esN′)
    chain : T ≡ s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (dgap₂ ++ᵗ tν t))
    chain = eqT ■ cong (_++ᵗ tν t) p
                ■ ++ᵗ-assoc s₂ (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) dgap₂)) (tν t)
    cleg : mkNF T esˢ ~ᵩ φφRHS
    cleg = ~ᵩ-trans (≡→~ᵩ (cong (λ z → mkNF z esˢ) chain))
                    (Eq*.return (φφᵩ s₂ x y c d (dgap₂ ++ᵗ tν t) esˢ))
    kEqN : innerOf (dgap₂ ++ᵗ tν t) (2 + _) ≡ _
    kEqN = innerOf-++ᵗ dgap₂ (tν t) (2 + _)
    telEqN : subst (Tel _) kEqN
               (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)))
               ≡ s′ ++ᵗ tν t′
    telEqN = subst-++ᵗ s₂ kEqN (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)))
           ■ cong (s₂ ++ᵗ_)
               ( subst-tφ kEqN y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11))
               ■ cong (tφ y d)
                   ( subst-tφ kEqN x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)
                   ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)) (renTel-++ᵗ dgap₂ (tν t) aswap11) ) )
           ■ sym (++ᵗ-assoc s₂ (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11))) (tν t′))
    thrEqN : subst (λ z → List (Tm z)) kEqN (map (_⋯ liftRen (dgap₂ ++ᵗ tν t) aswap11) esˢ) ≡ esN′
    thrEqN = map-⋯-subst kEqN (λ x₀ → liftRen-++ᵗ dgap₂ (tν t) aswap11 x₀) esˢ
    reshapeN-NF : mkNF (s′ ++ᵗ tν t′) esN′ ≡ φφRHS
    reshapeN-NF = sym (NF-≡ kEqN telEqN thrEqN)
    fitφφ : FIT (idₖ ⦃ Kᵣ ⦄) (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)))
    fitφφ = FIT-pres₁ (perm-φφ s₂ x y c d (dgap₂ ++ᵗ tν t) esˢ)
                      (subst (FIT (idₖ ⦃ Kᵣ ⦄)) chain fit)
    fit′ : FIT (idₖ ⦃ Kᵣ ⦄) (s′ ++ᵗ tν t′)
    fit′ = subst (FIT (idₖ ⦃ Kᵣ ⦄)) telEqN
                 (FIT-leaf-subst (idₖ ⦃ Kᵣ ⦄) kEqN
                    (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ tν t) aswap11)))
                    fitφφ)
    t″ : Tel (2 + _) _
    t″ = renTel (renTel t (swapᵣ 1 1)) (liftRen dgap₂ aswap11 ↑* 2)
    esM″ : List (Tm _)
    esM″ = map (_⋯ liftRen (tν (renTel t (swapᵣ 1 1))) (liftRen dgap₂ aswap11)) es₂
    αB : innerOf (renTel t (swapᵣ 1 1)) (2 + _) ≡ _
    αB = innerOf-renTel t (swapᵣ 1 1) (2 + _)
    βB : innerOf (renTel t (liftRen dgap₂ aswap11 ↑* 2)) (2 + _) ≡ _
    βB = innerOf-renTel t (liftRen dgap₂ aswap11 ↑* 2) (2 + _)
    kEqB : _ ≡ _
    kEqB = βB ■ sym αB
    kEqM : innerOf (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) (2 + _) ≡ _
    kEqM = innerOf-++ᵗ dgap₂ (tν (renTel t (swapᵣ 1 1))) (2 + _)
    telEqM : subst (Tel _) kEqM
               (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                  (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)))
               ≡ s′ ++ᵗ tν t″
    telEqM = subst-++ᵗ s₂ kEqM (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                  (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)))
           ■ cong (s₂ ++ᵗ_)
               ( subst-tφ kEqM y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                    (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11))
               ■ cong (tφ y d)
                   ( subst-tφ kEqM x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                        (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)
                   ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1))
                          (renTel-++ᵗ dgap₂ (tν (renTel t (swapᵣ 1 1))) aswap11) ) )
           ■ sym (++ᵗ-assoc s₂ (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11))) (tν t″))
    thrEqM : subst (λ z → List (Tm z)) kEqM
               (map (_⋯ liftRen (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11) es₂) ≡ esM″
    thrEqM = map-⋯-subst kEqM (λ x₀ → liftRen-++ᵗ dgap₂ (tν (renTel t (swapᵣ 1 1))) aswap11 x₀) es₂
    reshapeM-aux : mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                          (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)))
                       (map (_⋯ liftRen (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11) es₂)
                     ≡ mkNF (s′ ++ᵗ tν t″) esM″
    reshapeM-aux = NF-≡ kEqM telEqM thrEqM
    deepTelB : subst (Tel _) kEqB (renTel t′ (swapᵣ 1 1)) ≡ t″
    deepTelB = subst-■ (Tel _) βB (sym αB) (renTel t′ (swapᵣ 1 1))
             ■ cong (subst (Tel _) (sym αB)) (sym (swap-comm-tel (liftRen dgap₂ aswap11) t))
             ■ subst-symˡ αB t″
    telEqB : subst (Tel _) kEqB (s′ ++ᵗ tν (renTel t′ (swapᵣ 1 1))) ≡ s′ ++ᵗ tν t″
    telEqB = subst-++ᵗ s′ kEqB (tν (renTel t′ (swapᵣ 1 1)))
           ■ cong (s′ ++ᵗ_) (subst-tν kEqB (renTel t′ (swapᵣ 1 1)) ■ cong tν deepTelB)
    pointwiseB : ∀ x₀ →
                 subst 𝔽 kEqB (liftRen t′ (swapᵣ 1 1) (liftRen (tν t) (liftRen dgap₂ aswap11) x₀))
                   ≡ liftRen (tν (renTel t (swapᵣ 1 1))) (liftRen dgap₂ aswap11) (liftRen t (swapᵣ 1 1) x₀)
    pointwiseB x₀ =
      subst-■ 𝔽 βB (sym αB)
        (liftRen t′ (swapᵣ 1 1) (liftRen (tν t) (liftRen dgap₂ aswap11) x₀))
      ■ cong (subst 𝔽 (sym αB)) (sym (swap-comm-thr (liftRen dgap₂ aswap11) t x₀))
      ■ subst-symˡ αB (liftRen (renTel t (swapᵣ 1 1)) (liftRen dgap₂ aswap11 ↑* 2)
                               (liftRen t (swapᵣ 1 1) x₀))
    thrEqB : subst (λ z → List (Tm z)) kEqB (map (_⋯ liftRen t′ (swapᵣ 1 1)) esN′) ≡ esM″
    thrEqB = cong (subst (λ z → List (Tm z)) kEqB)
                  (map-fuse (liftRen (tν t) (liftRen dgap₂ aswap11)) (liftRen t′ (swapᵣ 1 1)) esˢ)
           ■ map-⋯-subst kEqB pointwiseB esˢ
           ■ sym (map-fuse (liftRen t (swapᵣ 1 1))
                           (liftRen (tν (renTel t (swapᵣ 1 1))) (liftRen dgap₂ aswap11)) esˢ)
           ■ cong (map (_⋯ liftRen (tν (renTel t (swapᵣ 1 1))) (liftRen dgap₂ aswap11))) (sym eqE)
    bridge : flipTarget ≡ mkNF (s′ ++ᵗ tν t″) esM″
    bridge = NF-≡ kEqB telEqB thrEqB
    reshapeM-NF : flipTarget ≡
                  mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                          (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)))
                       (map (_⋯ liftRen (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11) es₂)
    reshapeM-NF = bridge ■ sym reshapeM-aux
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ [] p ()
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tφ f′ c′ dg) p ()
pushφφ {n = n} {j = j} s₂ x y c d t₂ es₂ (flipᴿ {j = j₁} {k = k} s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q =
      φφRHS , cleg ,
      subst (Res φφRHS) reshapeM-NF (flipᴿ s t′ refl refl refl fit′)
  where
    q1 : renTel t (swapᵣ 1 1) ≡ dg ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)
    q1 = tν-inj q
    σ : j →ᵣ innerOf dg (2 + j₁)
    σ = liftRen dg (swapᵣ 1 1)
    dg″ : Tel (2 + j₁) (innerOf dg (2 + j₁))
    dg″ = renTel dg (swapᵣ 1 1)
    c′ d′ : Tm (innerOf dg (2 + j₁))
    c′ = c ⋯ σ
    d′ = d ⋯ σ
    t₂′ : Tel (2 + innerOf dg (2 + j₁)) (innerOf t₂ (2 + innerOf dg (2 + j₁)))
    t₂′ = renTel t₂ (σ ↑* 2)
    φφwin : Tel j (innerOf t (2 + j₁))
    φφwin = tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)
    srcWin : Tel (innerOf dg (2 + j₁)) (innerOf t₂ (2 + innerOf dg (2 + j₁)))
    srcWin = tφ x c′ (tφ y (d′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂′)
    firWin : Tel (innerOf dg (2 + j₁)) (innerOf t₂′ (2 + innerOf dg (2 + j₁)))
    firWin = tφ y d′ (tφ x (c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂′ (assocSwapᵣ 1 1)))
    t′ : Tel (2 + j₁) (innerOf t₂′ (2 + innerOf dg (2 + j₁)))
    t′ = dg″ ++ᵗ firWin
    kEq : innerOf t₂ (2 + innerOf dg (2 + j₁)) ≡ innerOf t (2 + j₁)
    kEq = cong (λ z → innerOf t₂ (2 + z)) (renTel-id dg) ■ renTel-id t₂
    kEqk = kEq ■ renTel-id t
    esˢ″ : List (Tm (innerOf t₂ (2 + innerOf dg (2 + j₁))))
    esˢ″ = subst (λ z → List (Tm z)) (sym kEqk) esˢ
    esFired : List (Tm (innerOf t₂′ (2 + innerOf dg (2 + j₁))))
    esFired = map (_⋯ liftRen t₂′ (assocSwapᵣ 1 1)) esˢ″
    φφRHS : NF n
    φφRHS = mkNF (s ++ᵗ tν t′) esFired
    -- source telescope reconstruction (undo the ν-flip on `t`)
    winEq : renTel φφwin σ ≡ srcWin
    winEq = cong (λ g → tφ x (c ⋯ σ) (tφ y g (renTel t₂ (σ ↑* 2)))) (gate-pres d σ)
    einv = innerOf-renTel t (swapᵣ 1 1) (2 + j₁) ■ renTel-id t
    invT = invTel t (swapᵣ 1 1) (λ z → swap-11-inv z)
    cInner : innerOf (renTel t (swapᵣ 1 1)) (2 + j₁) ≡ innerOf (dg ++ᵗ φφwin) (2 + j₁)
    cInner = cong (λ Z → innerOf Z (2 + j₁)) q1
    A₀ : subst (Tel (2 + j₁)) cInner (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1))
           ≡ renTel (dg ++ᵗ φφwin) (swapᵣ 1 1)
    A₀ = sym (subst-reix (λ Z → innerOf Z (2 + j₁)) q1 (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1)))
           ■ substf (λ Z → renTel Z (swapᵣ 1 1)) q1
    deepRev : subst (Tel (2 + j₁)) kEqk (dg″ ++ᵗ srcWin) ≡ t
    deepRev =
      cong (subst (Tel (2 + j₁)) kEqk) (cong (dg″ ++ᵗ_) (sym winEq))
        ■ cong (subst (Tel (2 + j₁)) kEqk) (sym (renTel-++ᵗ dg φφwin (swapᵣ 1 1)))
        ■ sym (subst-■ (Tel (2 + j₁)) (innerOf-++ᵗ dg φφwin (2 + j₁)) kEqk
                       (renTel (dg ++ᵗ φφwin) (swapᵣ 1 1)))
        ■ cong (subst (Tel (2 + j₁)) (innerOf-++ᵗ dg φφwin (2 + j₁) ■ kEqk)) (sym A₀)
        ■ sym (subst-■ (Tel (2 + j₁)) cInner (innerOf-++ᵗ dg φφwin (2 + j₁) ■ kEqk)
                       (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1)))
        ■ cong (λ e → subst (Tel (2 + j₁)) e (renTel (renTel t (swapᵣ 1 1)) (swapᵣ 1 1)))
               (≡-irrelevant (cInner ■ (innerOf-++ᵗ dg φφwin (2 + j₁) ■ kEqk)) einv)
        ■ invT
    deepEq : subst (Tel (2 + j₁)) (sym kEqk) t ≡ dg″ ++ᵗ srcWin
    deepEq = cong (subst (Tel (2 + j₁)) (sym kEqk)) (sym deepRev)
               ■ subst-symˡ kEqk (dg″ ++ᵗ srcWin)
    srcTelEq : subst (Tel n) (sym kEqk) (s ++ᵗ tν t) ≡ s ++ᵗ tν (dg″ ++ᵗ srcWin)
    srcTelEq = subst-++ᵗ s (sym kEqk) (tν t)
                 ■ cong (s ++ᵗ_) (subst-tν (sym kEqk) t ■ cong tν deepEq)
    srcEq : mkNF (s ++ᵗ tν t) esˢ ≡ mkNF (s ++ᵗ tν (dg″ ++ᵗ srcWin)) esˢ″
    srcEq = NF-≡ (sym kEqk) srcTelEq refl
    cleg : mkNF T esˢ ~ᵩ φφRHS
    cleg = ~ᵩ-trans (≡→~ᵩ (cong (λ z → mkNF z esˢ) eqT ■ srcEq
                              ■ cong (λ z → mkNF z esˢ″) (sym (++ᵗ-assoc s (tν dg″) srcWin))))
             (~ᵩ-trans (Eq*.return (φφᵩ (s ++ᵗ tν dg″) x y c′ d′ t₂′ esˢ″))
                       (≡→~ᵩ (cong (λ z → mkNF z esFired) (++ᵗ-assoc s (tν dg″) firWin))))
    fit′ : FIT (idₖ ⦃ Kᵣ ⦄) (s ++ᵗ tν t′)
    fit′ = subst (FIT (idₖ ⦃ Kᵣ ⦄)) (++ᵗ-assoc s (tν dg″) firWin)
             (FIT-pres-φφ (idₖ ⦃ Kᵣ ⦄) (s ++ᵗ tν dg″) x y c′ d′ t₂′
                (subst (FIT (idₖ ⦃ Kᵣ ⦄)) (sym (++ᵗ-assoc s (tν dg″) srcWin))
                   (subst (FIT (idₖ ⦃ Kᵣ ⦄)) srcTelEq
                      (FIT-leaf-subst (idₖ ⦃ Kᵣ ⦄) (sym kEqk) (s ++ᵗ tν t)
                         (subst (FIT (idₖ ⦃ Kᵣ ⦄)) eqT fit)))))
    reshapeM-NF : mkNF (s ++ᵗ tν (renTel t′ (swapᵣ 1 1))) (map (_⋯ liftRen t′ (swapᵣ 1 1)) esFired)
                    ≡ mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂ (assocSwapᵣ 1 1))))
                           (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) es₂)
    Lwin : Tel j (innerOf t₂ (2 + j))
    Lwin = tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂ (assocSwapᵣ 1 1)))
    mkΦ : (ss : Tel n j) (ee : List (Tm (innerOf t (2 + j₁)))) → NF n
    mkΦ ss ee = mkNF (ss ++ᵗ Lwin) (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) ee)
    eM : innerOf t′ (2 + j₁) ≡ innerOf t₂ (2 + j)
    eM = renTel-id t′ ■ renTel-id t₂′ ■ cong (λ z → innerOf t₂ (2 + z)) (renTel-id dg)
    deepM : subst (Tel (2 + j₁)) eM (renTel t′ (swapᵣ 1 1)) ≡ dg ++ᵗ Lwin
    σ″ : innerOf dg (2 + j₁) →ᵣ innerOf dg″ (2 + j₁)
    σ″ = liftRen dg″ (swapᵣ 1 1)
    pL : innerOf dg″ (2 + j₁) ≡ j
    pL = innerOf-renTel dg (swapᵣ 1 1) (2 + j₁) ■ renTel-id dg
    ρ′ : innerOf dg (2 + j₁) →ᵣ j
    ρ′ y = subst 𝔽 pL (σ″ y)
    collapse : ∀ y → ρ′ (σ y) ≡ y
    collapse y = invThr dg (swapᵣ 1 1) (λ z → swap-11-inv z) y
    g1 : d′ ⋯ ρ′ ≡ d
    g1 = fusion d σ ρ′ ■ ⋯-id d (λ y → collapse y)
    g2 : (c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑) ≡ c ⋯ weaken* ⦃ Kᵣ ⦄ 1
    g2 = gate-pres c′ ρ′ ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 1) (fusion c σ ρ′ ■ ⋯-id c (λ y → collapse y))
    LEAF : innerOf firWin j ≡ innerOf t₂ (2 + j)
    LEAF = cong (innerOf firWin) (sym (renTel-id dg)) ■ renTel-id firWin ■ renTel-id t₂′
         ■ cong (λ z → innerOf t₂ (2 + z)) (renTel-id dg)
    gpt : ∀ z → ((σ ↑* 2) ·ₖ (assocSwapᵣ 1 1 ·ₖ (ρ′ ↑* 2))) z ≡ assocSwapᵣ 1 1 z
    gpt z = cong (ρ′ ↑* 2) (comm-↑²-aswap11-gen σ z)
          ■ sym (dist-↑*-· 2 σ ρ′ (assocSwapᵣ 1 1 z))
          ■ id↑* 2 (λ w → collapse w) (assocSwapᵣ 1 1 z)
    g3 : subst (Tel (2 + j)) LEAF (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2)) ≡ renTel t₂ (assocSwapᵣ 1 1)
    g3 = cong (λ e → subst (Tel (2 + j)) e (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2)))
              (≡-irrelevant LEAF (innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + j)
                                  ■ innerOf-renTel t₂ (σ ↑* 2) (2 + j)))
       ■ subst-■ (Tel (2 + j)) (innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + j))
                 (innerOf-renTel t₂ (σ ↑* 2) (2 + j))
                 (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2))
       ■ cong (subst (Tel (2 + j)) (innerOf-renTel t₂ (σ ↑* 2) (2 + j)))
              (renTel-renTel t₂′ (assocSwapᵣ 1 1) (ρ′ ↑* 2))
       ■ renTel-renTel t₂ (σ ↑* 2) (assocSwapᵣ 1 1 ·ₖ (ρ′ ↑* 2))
       ■ renTel-cong t₂ (λ z → gpt z)
    tailLwin : subst (Tel j) LEAF (renTel firWin ρ′) ≡ Lwin
    tailLwin = subst-tφ LEAF y (d′ ⋯ ρ′) _
             ■ cong (tφ y (d′ ⋯ ρ′))
                    (subst-tφ LEAF x ((c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑)) _
                     ■ cong (tφ x ((c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑))) g3)
             ■ cong₂ (tφ y) g1 (cong₂ (tφ x) g2 refl)
    SCOPE : innerOf t′ (2 + j₁) ≡ innerOf t₂ (2 + j)
    SCOPE = innerOf-++ᵗ dg″ firWin (2 + j₁) ■ cong (innerOf firWin) pL ■ LEAF
    E2 : subst (Tel (2 + j₁)) (cong (innerOf firWin) pL)
             (renTel dg″ (swapᵣ 1 1) ++ᵗ renTel firWin σ″)
           ≡ dg ++ᵗ renTel firWin ρ′
    E2 = telMidᴺ pL (renTel dg″ (swapᵣ 1 1)) firWin (λ y → refl)
       ■ cong (_++ᵗ renTel firWin ρ′) (invTel dg (swapᵣ 1 1) (λ z → swap-11-inv z))
    E3 : subst (Tel (2 + j₁)) LEAF (dg ++ᵗ renTel firWin ρ′) ≡ dg ++ᵗ Lwin
    E3 = subst-++ᵗ dg LEAF (renTel firWin ρ′) ■ cong (dg ++ᵗ_) tailLwin
    deepM =
      cong (λ e → subst (Tel (2 + j₁)) e (renTel t′ (swapᵣ 1 1))) (≡-irrelevant eM SCOPE)
      ■ subst-■ (Tel (2 + j₁)) (innerOf-++ᵗ dg″ firWin (2 + j₁)) (cong (innerOf firWin) pL ■ LEAF)
                (renTel t′ (swapᵣ 1 1))
      ■ cong (subst (Tel (2 + j₁)) (cong (innerOf firWin) pL ■ LEAF))
             (renTel-++ᵗ dg″ firWin (swapᵣ 1 1))
      ■ subst-■ (Tel (2 + j₁)) (cong (innerOf firWin) pL) LEAF
                (renTel dg″ (swapᵣ 1 1) ++ᵗ renTel firWin σ″)
      ■ cong (subst (Tel (2 + j₁)) LEAF) E2
      ■ E3
    telM : subst (Tel n) eM (s ++ᵗ tν (renTel t′ (swapᵣ 1 1))) ≡ (s ++ᵗ tν dg) ++ᵗ Lwin
    telM = subst-++ᵗ s eM (tν (renTel t′ (swapᵣ 1 1)))
         ■ cong (s ++ᵗ_) (subst-tν eM (renTel t′ (swapᵣ 1 1)) ■ cong tν deepM)
         ■ sym (++ᵗ-assoc s (tν dg) Lwin)
    thrM : subst (λ z → List (Tm z)) eM (map (_⋯ liftRen t′ (swapᵣ 1 1)) esFired)
             ≡ map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) (map (_⋯ liftRen t (swapᵣ 1 1)) esˢ)
    hPt : ∀ y →
          subst 𝔽 eM ((liftRen t₂′ (assocSwapᵣ 1 1) ·ₖ liftRen t′ (swapᵣ 1 1))
                        (subst 𝔽 (sym kEqk) y))
            ≡ (liftRen t (swapᵣ 1 1) ·ₖ liftRen t₂ (assocSwapᵣ 1 1)) y
    hPt y =
        cong (subst 𝔽 eM) LHScoreExp
      ■ cong (λ w → subst 𝔽 eM (subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) w)))
             (A3toX ■ cong (subst 𝔽 pp3) Xexp)
      ■ mergeCollapse
      ■ sym (cong (liftRen t₂ (assocSwapᵣ 1 1)) hZ)
      where
        V : 𝔽 (innerOf t₂ (2 + innerOf dg (2 + j₁)))
        V = subst 𝔽 (sym kEqk) y
        z₀ : 𝔽 (innerOf t₂′ (2 + innerOf dg″ (2 + j₁)))
        z₀ = liftRen t₂′ (σ″ ↑* 2) V
        qq1 : innerOf (dg″ ++ᵗ firWin) (2 + j₁) ≡ innerOf firWin (innerOf dg″ (2 + j₁))
        qq1 = innerOf-++ᵗ dg″ firWin (2 + j₁)
        qq2 : innerOf (renTel t₂′ (assocSwapᵣ 1 1)) (2 + innerOf dg″ (2 + j₁))
               ≡ innerOf t₂′ (2 + innerOf dg″ (2 + j₁))
        qq2 = innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + innerOf dg″ (2 + j₁))
        -- LHS core reduces to A3 = liftRen t₂′ (aswap11 ·ₖ σ″↑*2) V
        redA : subst 𝔽 qq2 (subst 𝔽 qq1 (liftRen t′ (swapᵣ 1 1) (liftRen t₂′ (assocSwapᵣ 1 1) V)))
                 ≡ liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V
        redA = cong (subst 𝔽 qq2) (liftRen-++ᵗ dg″ firWin (swapᵣ 1 1) (liftRen t₂′ (assocSwapᵣ 1 1) V))
             ■ liftRen-· t₂′ (assocSwapᵣ 1 1) (σ″ ↑* 2) V
        -- RHS: reduce liftRen t (swap11) y to the σ″-window form.
        gT : Tel (2 + j₁) (innerOf t₂ (2 + innerOf dg (2 + j₁))) → ℕ
        gT T = innerOf T (2 + j₁)
        wa : subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + j₁))
               (liftRen (subst (Tel (2 + j₁)) (sym kEqk) t) (swapᵣ 1 1) V)
               ≡ liftRen t (swapᵣ 1 1) y
        wa = liftRen-substⁱ (sym kEqk) t (swapᵣ 1 1) V
           ■ cong (liftRen t (swapᵣ 1 1)) (subst-symˡ (sym kEqk) y)
        wb : subst 𝔽 (cong gT deepEq)
               (liftRen (subst (Tel (2 + j₁)) (sym kEqk) t) (swapᵣ 1 1) V)
               ≡ liftRen (dg″ ++ᵗ srcWin) (swapᵣ 1 1) V
        wb = sym (subst-reix gT deepEq (liftRen (subst (Tel (2 + j₁)) (sym kEqk) t) (swapᵣ 1 1) V))
           ■ substf (λ T → liftRen T (swapᵣ 1 1) V) deepEq
        wc : subst 𝔽 (innerOf-++ᵗ dg″ srcWin (2 + j₁))
               (liftRen (dg″ ++ᵗ srcWin) (swapᵣ 1 1) V) ≡ liftRen t₂′ (σ″ ↑* 2) V
        wc = liftRen-++ᵗ dg″ srcWin (swapᵣ 1 1) V
        wc' : liftRen (dg″ ++ᵗ srcWin) (swapᵣ 1 1) V
                ≡ subst 𝔽 (sym (innerOf-++ᵗ dg″ srcWin (2 + j₁))) (liftRen t₂′ (σ″ ↑* 2) V)
        wc' = sym (subst-symˡ (innerOf-++ᵗ dg″ srcWin (2 + j₁)) (liftRen (dg″ ++ᵗ srcWin) (swapᵣ 1 1) V))
            ■ cong (subst 𝔽 (sym (innerOf-++ᵗ dg″ srcWin (2 + j₁)))) wc
        wb' : liftRen (subst (Tel (2 + j₁)) (sym kEqk) t) (swapᵣ 1 1) V
                ≡ subst 𝔽 (sym (cong gT deepEq)) (liftRen (dg″ ++ᵗ srcWin) (swapᵣ 1 1) V)
        wb' = sym (subst-symˡ (cong gT deepEq) (liftRen (subst (Tel (2 + j₁)) (sym kEqk) t) (swapᵣ 1 1) V))
            ■ cong (subst 𝔽 (sym (cong gT deepEq))) wb
        wRed : liftRen t (swapᵣ 1 1) y
                 ≡ subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + j₁))
                     (subst 𝔽 (sym (cong gT deepEq))
                       (subst 𝔽 (sym (innerOf-++ᵗ dg″ srcWin (2 + j₁)))
                         (liftRen t₂′ (σ″ ↑* 2) V)))
        wRed = sym wa
             ■ cong (subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + j₁)))
                    (wb' ■ cong (subst 𝔽 (sym (cong gT deepEq))) wc')
        -- Glue via glueG2: cross the σ↑*2 / σ″↑*2 double renTel to bare t₂.
        eG : 2 + j ≡ 2 + innerOf dg″ (2 + j₁)
        eG = cong (λ z → 2 + z) (sym pL)
        σσ″ : ∀ w → (σ ·ₖ σ″) w ≡ subst 𝔽 (sym pL) w
        σσ″ w = sym (subst-symˡ pL ((σ ·ₖ σ″) w)) ■ cong (subst 𝔽 (sym pL)) (collapse w)
        heκ : ∀ x → (σ″ ↑* 2) ((σ ↑* 2) x) ≡ subst 𝔽 eG x
        heκ x = sym (dist-↑*-· 2 σ σ″ x) ■ (σσ″ ~↑* 2) x ■ ↑*2-substᵃ (sym pL) x
        gApp : subst 𝔽 (innerOf-renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2) (2 + innerOf dg″ (2 + j₁))
                        ■ innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf dg″ (2 + j₁)))
                     (liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀)
                 ≡ subst 𝔽 (cong (innerOf t₂) eG)
                          (liftRen t₂ (assocSwapᵣ 1 1)
                            (subst 𝔽 (innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf dg″ (2 + j₁))
                                       ■ sym (cong (innerOf t₂) eG) ■ renTel-id t₂) z₀))
        gApp = glueG2 eG eG t₂ (σ ↑* 2) (σ″ ↑* 2) heκ (assocSwapᵣ 1 1) (assocSwapᵣ 1 1)
                      (aswap-nat eG) z₀
        pp3 : innerOf (renTel t₂′ (σ″ ↑* 2)) (2 + innerOf dg″ (2 + j₁))
               ≡ innerOf t₂′ (2 + innerOf dg″ (2 + j₁))
        pp3 = innerOf-renTel t₂′ (σ″ ↑* 2) (2 + innerOf dg″ (2 + j₁))
        QQ : innerOf (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (2 + innerOf dg″ (2 + j₁))
               ≡ innerOf t₂ (2 + innerOf dg″ (2 + j₁))
        QQ = innerOf-renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2) (2 + innerOf dg″ (2 + j₁))
           ■ innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf dg″ (2 + j₁))
        W₂ : innerOf t₂′ (2 + innerOf dg″ (2 + j₁)) ≡ innerOf t (2 + j₁)
        W₂ = innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf dg″ (2 + j₁))
           ■ sym (cong (innerOf t₂) eG) ■ renTel-id t₂
        RHSg : 𝔽 (innerOf t₂ (2 + innerOf dg″ (2 + j₁)))
        RHSg = subst 𝔽 (cong (innerOf t₂) eG)
                     (liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀))
        LHScoreExp : liftRen t′ (swapᵣ 1 1) (liftRen t₂′ (assocSwapᵣ 1 1) V)
                       ≡ subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) (liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V))
        LHScoreExp = sym (subst-symˡ qq1 _)
                   ■ cong (subst 𝔽 (sym qq1)) (sym (subst-symˡ qq2 _))
                   ■ cong (λ w → subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) w)) redA
        A3toX : liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V
                  ≡ subst 𝔽 pp3 (liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀)
        A3toX = liftRen-cong t₂′ (λ z → sym (comm-↑²-aswap11-gen σ″ z)) V
              ■ sym (liftRen-· t₂′ (σ″ ↑* 2) (assocSwapᵣ 1 1) V)
        Xexp : liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀
                 ≡ subst 𝔽 (sym QQ) RHSg
        Xexp = sym (subst-symˡ QQ _) ■ cong (subst 𝔽 (sym QQ)) gApp
        hZ : liftRen t (swapᵣ 1 1) y ≡ subst 𝔽 W₂ z₀
        hZ = wRed
           ■ subst3≡ (sym (innerOf-++ᵗ dg″ srcWin (2 + j₁))) (sym (cong gT deepEq))
                     (innerOf-substⁱ (sym kEqk) t (2 + j₁)) W₂ z₀
        mergeCollapse : subst 𝔽 eM (subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2)
                          (subst 𝔽 pp3 (subst 𝔽 (sym QQ) RHSg))))
                          ≡ liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀)
        mergeCollapse =
          subst6-id (cong (innerOf t₂) eG) (sym QQ) pp3 (sym qq2) (sym qq1) eM
                    (liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀))
    thrM = cong (subst (λ z → List (Tm z)) eM)
                (map-fuse (liftRen t₂′ (assocSwapᵣ 1 1)) (liftRen t′ (swapᵣ 1 1)) esˢ″)
         ■ cong (subst (λ z → List (Tm z)) eM)
                (map-⋯-substTm (sym kEqk)
                   (liftRen t₂′ (assocSwapᵣ 1 1) ·ₖ liftRen t′ (swapᵣ 1 1)) esˢ)
         ■ map-⋯-subst eM hPt esˢ
         ■ sym (map-fuse (liftRen t (swapᵣ 1 1)) (liftRen t₂ (assocSwapᵣ 1 1)) esˢ)
    reshapeM-NF = NF-≡ eM telM thrM ■ sym (cong₂ mkΦ p eqE)
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  with cmpᵗ s (tν (a ++ᵗ tν (renTel t (gapρ a w)))) s₂ (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)) (sym eqTᵗ)
... | cmpʳ [] p ()
... | cmpʳ (tν dg) p ()
... | cmpʳ (tφ x′ c′ []) p q with tφ-inj₂ q
...   | ()
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpʳ (tφ x′ c′ (tν dg)) p q with tφ-inj₂ q
...   | ()
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpʳ (tφ x′ c′ (tφ y′ d″ dgap₂)) p q
    with tφ-inj₁ q | tφ-inj-c q | tφ-inj₁ (tφ-inj₂ q) | tφ-inj-c (tφ-inj₂ q) | tφ-inj₂ (tφ-inj₂ q)
...   | refl | refl | refl | refl | refl =
        φφRHS , cleg ,
        subst (λ b → Res φφRHS b) reshapeM-NF
          (subst (λ a₀ → Res a₀ swapTarget) reshapeN-NF
             (swapᴿ s′ {aN} wN tN {es = esN′} refl refl refl fit′))
  where
    aswap11 : _ →ᵣ _
    aswap11 = assocSwapᵣ 1 1
    mv : _ →ᵣ _
    mv = liftRen dgap₂ aswap11
    s′ : Tel _ _
    s′ = s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11))
    aN : Tel _ _
    aN = renTel a (mv ↑* 2)
    wN : Run aN
    wN = runRen w (mv ↑* 2)
    tN : Tel (2 + _) _
    tN = renTel t (liftRen a (mv ↑* 2) ↑* 2)
    Dwin : Tel _ _
    Dwin = tν (a ++ᵗ tν t)
    esN′ : List (Tm _)
    esN′ = map (_⋯ liftRen t (liftRen a (mv ↑* 2) ↑* 2)) esˢ
    φφRHS : NF _
    φφRHS = mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)))
                 (map (_⋯ liftRen (dgap₂ ++ᵗ Dwin) aswap11) esˢ)
    swapTarget : NF _
    swapTarget = mkNF (s′ ++ᵗ tν (aN ++ᵗ tν (renTel tN (gapρ aN wN))))
                      (map (_⋯ liftRen tN (gapρ aN wN)) esN′)
    chain : T ≡ s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (dgap₂ ++ᵗ Dwin))
    chain = eqT ■ cong (_++ᵗ Dwin) p
                ■ ++ᵗ-assoc s₂ (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) dgap₂)) Dwin
    cleg : mkNF T esˢ ~ᵩ φφRHS
    cleg = ~ᵩ-trans (≡→~ᵩ (cong (λ z → mkNF z esˢ) chain))
                    (Eq*.return (φφᵩ s₂ x y c d (dgap₂ ++ᵗ Dwin) esˢ))
    kA : innerOf (dgap₂ ++ᵗ Dwin) _ ≡ innerOf Dwin (innerOf dgap₂ _)
    kA = innerOf-++ᵗ dgap₂ Dwin _
    kB : innerOf Dwin (innerOf dgap₂ _) ≡ innerOf t (2 + innerOf a (2 + innerOf dgap₂ _))
    kB = innerOf-++ᵗ a (tν t) (2 + innerOf dgap₂ _)
    kEqN : innerOf (dgap₂ ++ᵗ Dwin) _ ≡ innerOf t (2 + innerOf a (2 + innerOf dgap₂ _))
    kEqN = kA ■ kB
    INNER : subst (Tel _) kB (renTel Dwin mv) ≡ tν (aN ++ᵗ tν tN)
    INNER = subst-tν kB (renTel (a ++ᵗ tν t) (mv ↑* 2))
          ■ cong tν (renTel-++ᵗ a (tν t) (mv ↑* 2))
    LEAF : subst (Tel _) kEqN (renTel (dgap₂ ++ᵗ Dwin) aswap11)
             ≡ renTel dgap₂ aswap11 ++ᵗ tν (aN ++ᵗ tν tN)
    LEAF = subst-■ (Tel _) kA kB (renTel (dgap₂ ++ᵗ Dwin) aswap11)
         ■ cong (subst (Tel _) kB) (renTel-++ᵗ dgap₂ Dwin aswap11)
         ■ subst-++ᵗ (renTel dgap₂ aswap11) kB (renTel Dwin mv)
         ■ cong (renTel dgap₂ aswap11 ++ᵗ_) INNER
    telEqN : subst (Tel _) kEqN
               (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)))
               ≡ s′ ++ᵗ tν (aN ++ᵗ tν tN)
    telEqN = subst-++ᵗ s₂ kEqN (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)))
           ■ cong (s₂ ++ᵗ_)
               ( subst-tφ kEqN y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11))
               ■ cong (tφ y d)
                   ( subst-tφ kEqN x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)
                   ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)) LEAF ) )
           ■ sym (++ᵗ-assoc s₂ (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11)))
                             (tν (aN ++ᵗ tν tN)))
    PW : ∀ x₀ → subst 𝔽 kEqN (liftRen (dgap₂ ++ᵗ Dwin) aswap11 x₀)
                  ≡ liftRen t (liftRen a (mv ↑* 2) ↑* 2) x₀
    PW x₀ = subst-■ 𝔽 kA kB (liftRen (dgap₂ ++ᵗ Dwin) aswap11 x₀)
          ■ cong (subst 𝔽 kB) (liftRen-++ᵗ dgap₂ Dwin aswap11 x₀)
          ■ liftRen-++ᵗ a (tν t) (mv ↑* 2) x₀
    thrEqN : subst (λ z → List (Tm z)) kEqN (map (_⋯ liftRen (dgap₂ ++ᵗ Dwin) aswap11) esˢ) ≡ esN′
    thrEqN = map-⋯-subst kEqN PW esˢ
    reshapeN-NF : mkNF (s′ ++ᵗ tν (aN ++ᵗ tν tN)) esN′ ≡ φφRHS
    reshapeN-NF = sym (NF-≡ kEqN telEqN thrEqN)
    fitφφ : FIT (idₖ ⦃ Kᵣ ⦄) (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)))
    fitφφ = FIT-pres₁ (perm-φφ s₂ x y c d (dgap₂ ++ᵗ Dwin) esˢ)
                      (subst (FIT (idₖ ⦃ Kᵣ ⦄)) chain fit)
    fit′ : FIT (idₖ ⦃ Kᵣ ⦄) (s′ ++ᵗ tν (aN ++ᵗ tν tN))
    fit′ = subst (FIT (idₖ ⦃ Kᵣ ⦄)) telEqN
                 (FIT-leaf-subst (idₖ ⦃ Kᵣ ⦄) kEqN
                    (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (dgap₂ ++ᵗ Dwin) aswap11)))
                    fitφφ)
    LL : Tel (2 + _) _
    LL = renTel t (gapρ a w)
    LN : Tel (2 + _) _
    LN = renTel LL (liftRen a (mv ↑* 2) ↑* 2)
    esM″ : List (Tm _)
    esM″ = map (_⋯ liftRen LL (liftRen a (mv ↑* 2) ↑* 2)) es₂
    -- M-side reassociation (mirror of reshapeN, inner leaf = LL).
    kAM : innerOf (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) _ ≡ innerOf (tν (a ++ᵗ tν LL)) (innerOf dgap₂ _)
    kAM = innerOf-++ᵗ dgap₂ (tν (a ++ᵗ tν LL)) _
    kBM : innerOf (tν (a ++ᵗ tν LL)) (innerOf dgap₂ _) ≡ innerOf LL (2 + innerOf a (2 + innerOf dgap₂ _))
    kBM = innerOf-++ᵗ a (tν LL) (2 + innerOf dgap₂ _)
    kEqM : innerOf (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) _ ≡ innerOf LL (2 + innerOf a (2 + innerOf dgap₂ _))
    kEqM = kAM ■ kBM
    INNERM : subst (Tel _) kBM (renTel (tν (a ++ᵗ tν LL)) mv) ≡ tν (aN ++ᵗ tν LN)
    INNERM = subst-tν kBM (renTel (a ++ᵗ tν LL) (mv ↑* 2))
           ■ cong tν (renTel-++ᵗ a (tν LL) (mv ↑* 2))
    LEAFM : subst (Tel _) kEqM (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)
              ≡ renTel dgap₂ aswap11 ++ᵗ tν (aN ++ᵗ tν LN)
    LEAFM = subst-■ (Tel _) kAM kBM (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)
          ■ cong (subst (Tel _) kBM) (renTel-++ᵗ dgap₂ (tν (a ++ᵗ tν LL)) aswap11)
          ■ subst-++ᵗ (renTel dgap₂ aswap11) kBM (renTel (tν (a ++ᵗ tν LL)) mv)
          ■ cong (renTel dgap₂ aswap11 ++ᵗ_) INNERM
    telEqM : subst (Tel _) kEqM
               (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                  (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)))
               ≡ s′ ++ᵗ tν (aN ++ᵗ tν LN)
    telEqM = subst-++ᵗ s₂ kEqM (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)))
           ■ cong (s₂ ++ᵗ_)
               ( subst-tφ kEqM y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                    (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11))
               ■ cong (tφ y d)
                   ( subst-tφ kEqM x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                        (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)
                   ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)) LEAFM ) )
           ■ sym (++ᵗ-assoc s₂ (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel dgap₂ aswap11)))
                             (tν (aN ++ᵗ tν LN)))
    PWM : ∀ x₀ → subst 𝔽 kEqM (liftRen (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11 x₀)
                  ≡ liftRen LL (liftRen a (mv ↑* 2) ↑* 2) x₀
    PWM x₀ = subst-■ 𝔽 kAM kBM (liftRen (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11 x₀)
           ■ cong (subst 𝔽 kBM) (liftRen-++ᵗ dgap₂ (tν (a ++ᵗ tν LL)) aswap11 x₀)
           ■ liftRen-++ᵗ a (tν LL) (mv ↑* 2) x₀
    thrEqM : subst (λ z → List (Tm z)) kEqM
               (map (_⋯ liftRen (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11) es₂) ≡ esM″
    thrEqM = map-⋯-subst kEqM PWM es₂
    reshapeM-aux : mkNF (s′ ++ᵗ tν (aN ++ᵗ tν LN)) esM″
                     ≡ mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                              (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11)))
                            (map (_⋯ liftRen (dgap₂ ++ᵗ tν (a ++ᵗ tν LL)) aswap11) es₂)
    reshapeM-aux = sym (NF-≡ kEqM telEqM thrEqM)
    -- bridge: swap-residue codomain ≡ M-aux source (via gapρ-comm-tel/thr).
    αB-s : innerOf (renTel t (gapρ a w)) _ ≡ innerOf t _
    αB-s = innerOf-renTel t (gapρ a w) _
    βB-s : innerOf (renTel t (liftRen a (mv ↑* 2) ↑* 2)) _ ≡ innerOf t _
    βB-s = innerOf-renTel t (liftRen a (mv ↑* 2) ↑* 2) _
    kEqBr : innerOf tN _ ≡ innerOf LL _
    kEqBr = βB-s ■ sym αB-s
    deepTelBr : subst (Tel _) kEqBr (renTel tN (gapρ aN wN)) ≡ LN
    deepTelBr = subst-■ (Tel _) βB-s (sym αB-s) (renTel tN (gapρ aN wN))
              ■ cong (subst (Tel _) (sym αB-s)) (sym (gapρ-comm-tel a w mv t))
              ■ subst-symˡ αB-s LN
    telEqBr : subst (Tel _) kEqBr (s′ ++ᵗ tν (aN ++ᵗ tν (renTel tN (gapρ aN wN))))
                ≡ s′ ++ᵗ tν (aN ++ᵗ tν LN)
    telEqBr = subst-++ᵗ s′ kEqBr (tν (aN ++ᵗ tν (renTel tN (gapρ aN wN))))
            ■ cong (s′ ++ᵗ_)
                ( subst-tν kEqBr (aN ++ᵗ tν (renTel tN (gapρ aN wN)))
                ■ cong tν ( subst-++ᵗ aN kEqBr (tν (renTel tN (gapρ aN wN)))
                          ■ cong (aN ++ᵗ_)
                              (subst-tν kEqBr (renTel tN (gapρ aN wN)) ■ cong tν deepTelBr) ) )
    pointwiseBr : ∀ x₀ →
      subst 𝔽 kEqBr (liftRen tN (gapρ aN wN) (liftRen t (liftRen a (mv ↑* 2) ↑* 2) x₀))
        ≡ liftRen LL (liftRen a (mv ↑* 2) ↑* 2) (liftRen t (gapρ a w) x₀)
    pointwiseBr x₀ =
      subst-■ 𝔽 βB-s (sym αB-s) (liftRen tN (gapρ aN wN) (liftRen t (liftRen a (mv ↑* 2) ↑* 2) x₀))
      ■ cong (subst 𝔽 (sym αB-s)) (sym (gapρ-comm-thr a w mv t x₀))
      ■ subst-symˡ αB-s (liftRen LL (liftRen a (mv ↑* 2) ↑* 2) (liftRen t (gapρ a w) x₀))
    thrEqBr : subst (λ z → List (Tm z)) kEqBr (map (_⋯ liftRen tN (gapρ aN wN)) esN′) ≡ esM″
    thrEqBr = cong (subst (λ z → List (Tm z)) kEqBr)
                   (map-fuse (liftRen t (liftRen a (mv ↑* 2) ↑* 2)) (liftRen tN (gapρ aN wN)) esˢ)
            ■ map-⋯-subst kEqBr pointwiseBr esˢ
            ■ sym (map-fuse (liftRen t (gapρ a w)) (liftRen LL (liftRen a (mv ↑* 2) ↑* 2)) esˢ)
            ■ cong (map (_⋯ liftRen LL (liftRen a (mv ↑* 2) ↑* 2))) (sym eqE)
    bridge : swapTarget ≡ mkNF (s′ ++ᵗ tν (aN ++ᵗ tν LN)) esM″
    bridge = NF-≡ kEqBr telEqBr thrEqBr
    reshapeM-NF : swapTarget ≡
                  mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                          (renTel (dgap₂ ++ᵗ tν (a ++ᵗ tν (renTel t (gapρ a w)))) aswap11)))
                       (map (_⋯ liftRen (dgap₂ ++ᵗ tν (a ++ᵗ tν (renTel t (gapρ a w)))) aswap11) es₂)
    reshapeM-NF = bridge ■ reshapeM-aux
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ [] p ()
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tφ f′ c′ dg) p ()
pushφφ {n = n} {j = j} s₂ x y c d t₂ es₂ (swapᴿ {j = j₁} {i = i} s {a} w t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q
    with cmpᵗ a (tν (renTel t (gapρ a w))) dg (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)) (tν-inj q)
...   | cmpˡ [] p′ ()
...   | cmpˡ (tφ f′ c′ e′) p′ ()
...   | cmpʳ [] p′ ()
...   | cmpʳ (tν e′) p′ ()
pushφφ {n = n} {j = j} s₂ x y c d t₂ es₂ (swapᴿ {j = j₁} {i = i} s {a} w t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q
  | cmpˡ (tν e′) p′ q′ =
      φφRHS , cleg ,
      subst (Res φφRHS) reshapeM-NF
        (swapᴿ s {a = a} w t′ {T = ŝ ++ᵗ tν t′} {es = esFired}
          (++ᵗ-assoc s (tν a) (tν t′))
          (++ᵗ-assoc s (tν a) (tν (renTel t′ (gapρ a w))))
          refl fit′)
  where
    ŝ : Tel n i
    ŝ = s ++ᵗ tν a
    p̂ : s₂ ≡ ŝ ++ᵗ tν e′
    p̂ = p ■ cong (s ++ᵗ_) (cong tν p′) ■ sym (++ᵗ-assoc s (tν a) (tν e′))
    eqT̂ : T ≡ ŝ ++ᵗ tν t
    eqT̂ = eqT ■ sym (++ᵗ-assoc s (tν a) (tν t))
    q1 : renTel t (gapρ a w) ≡ e′ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)
    q1 = tν-inj q′
    σ : j →ᵣ innerOf e′ (2 + i)
    σ = liftRen e′ (gapρ a w)
    e″ : Tel (2 + i) (innerOf e′ (2 + i))
    e″ = renTel e′ (gapρ a w)
    c′ d′ : Tm (innerOf e′ (2 + i))
    c′ = c ⋯ σ
    d′ = d ⋯ σ
    t₂′ : Tel (2 + innerOf e′ (2 + i)) (innerOf t₂ (2 + innerOf e′ (2 + i)))
    t₂′ = renTel t₂ (σ ↑* 2)
    φφwin : Tel j (innerOf t (2 + i))
    φφwin = tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)
    srcWin : Tel (innerOf e′ (2 + i)) (innerOf t₂ (2 + innerOf e′ (2 + i)))
    srcWin = tφ x c′ (tφ y (d′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂′)
    firWin : Tel (innerOf e′ (2 + i)) (innerOf t₂′ (2 + innerOf e′ (2 + i)))
    firWin = tφ y d′ (tφ x (c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂′ (assocSwapᵣ 1 1)))
    t′ : Tel (2 + i) (innerOf t₂′ (2 + innerOf e′ (2 + i)))
    t′ = e″ ++ᵗ firWin
    kEq : innerOf t₂ (2 + innerOf e′ (2 + i)) ≡ innerOf t (2 + i)
    kEq = cong (λ z → innerOf t₂ (2 + z)) (renTel-id e′) ■ renTel-id t₂
    kEqk = kEq ■ renTel-id t
    esˢ″ : List (Tm (innerOf t₂ (2 + innerOf e′ (2 + i))))
    esˢ″ = subst (λ z → List (Tm z)) (sym kEqk) esˢ
    esFired : List (Tm (innerOf t₂′ (2 + innerOf e′ (2 + i))))
    esFired = map (_⋯ liftRen t₂′ (assocSwapᵣ 1 1)) esˢ″
    φφRHS : NF n
    φφRHS = mkNF (ŝ ++ᵗ tν t′) esFired
    -- source telescope reconstruction (undo the ν-flip on `t`)
    winEq : renTel φφwin σ ≡ srcWin
    winEq = cong (λ g → tφ x (c ⋯ σ) (tφ y g (renTel t₂ (σ ↑* 2)))) (gate-pres d σ)
    einv = innerOf-renTel t (gapρ a w) (2 + i) ■ renTel-id t
    invT = invTel t (gapρ a w) (λ z → gapρ-invol a w z)
    cInner : innerOf (renTel t (gapρ a w)) (2 + i) ≡ innerOf (e′ ++ᵗ φφwin) (2 + i)
    cInner = cong (λ Z → innerOf Z (2 + i)) q1
    A₀ : subst (Tel (2 + i)) cInner (renTel (renTel t (gapρ a w)) (gapρ a w))
           ≡ renTel (e′ ++ᵗ φφwin) (gapρ a w)
    A₀ = sym (subst-reix (λ Z → innerOf Z (2 + i)) q1 (renTel (renTel t (gapρ a w)) (gapρ a w)))
           ■ substf (λ Z → renTel Z (gapρ a w)) q1
    deepRev : subst (Tel (2 + i)) kEqk (e″ ++ᵗ srcWin) ≡ t
    deepRev =
      cong (subst (Tel (2 + i)) kEqk) (cong (e″ ++ᵗ_) (sym winEq))
        ■ cong (subst (Tel (2 + i)) kEqk) (sym (renTel-++ᵗ e′ φφwin (gapρ a w)))
        ■ sym (subst-■ (Tel (2 + i)) (innerOf-++ᵗ e′ φφwin (2 + i)) kEqk
                       (renTel (e′ ++ᵗ φφwin) (gapρ a w)))
        ■ cong (subst (Tel (2 + i)) (innerOf-++ᵗ e′ φφwin (2 + i) ■ kEqk)) (sym A₀)
        ■ sym (subst-■ (Tel (2 + i)) cInner (innerOf-++ᵗ e′ φφwin (2 + i) ■ kEqk)
                       (renTel (renTel t (gapρ a w)) (gapρ a w)))
        ■ cong (λ e → subst (Tel (2 + i)) e (renTel (renTel t (gapρ a w)) (gapρ a w)))
               (≡-irrelevant (cInner ■ (innerOf-++ᵗ e′ φφwin (2 + i) ■ kEqk)) einv)
        ■ invT
    deepEq : subst (Tel (2 + i)) (sym kEqk) t ≡ e″ ++ᵗ srcWin
    deepEq = cong (subst (Tel (2 + i)) (sym kEqk)) (sym deepRev)
               ■ subst-symˡ kEqk (e″ ++ᵗ srcWin)
    srcTelEq : subst (Tel n) (sym kEqk) (ŝ ++ᵗ tν t) ≡ ŝ ++ᵗ tν (e″ ++ᵗ srcWin)
    srcTelEq = subst-++ᵗ ŝ (sym kEqk) (tν t)
                 ■ cong (ŝ ++ᵗ_) (subst-tν (sym kEqk) t ■ cong tν deepEq)
    srcEq : mkNF (ŝ ++ᵗ tν t) esˢ ≡ mkNF (ŝ ++ᵗ tν (e″ ++ᵗ srcWin)) esˢ″
    srcEq = NF-≡ (sym kEqk) srcTelEq refl
    cleg : mkNF T esˢ ~ᵩ φφRHS
    cleg = ~ᵩ-trans (≡→~ᵩ (cong (λ z → mkNF z esˢ) eqT̂ ■ srcEq
                              ■ cong (λ z → mkNF z esˢ″) (sym (++ᵗ-assoc ŝ (tν e″) srcWin))))
             (~ᵩ-trans (Eq*.return (φφᵩ (ŝ ++ᵗ tν e″) x y c′ d′ t₂′ esˢ″))
                       (≡→~ᵩ (cong (λ z → mkNF z esFired) (++ᵗ-assoc ŝ (tν e″) firWin))))
    fit′ : FIT (idₖ ⦃ Kᵣ ⦄) (ŝ ++ᵗ tν t′)
    fit′ = subst (FIT (idₖ ⦃ Kᵣ ⦄)) (++ᵗ-assoc ŝ (tν e″) firWin)
             (FIT-pres-φφ (idₖ ⦃ Kᵣ ⦄) (ŝ ++ᵗ tν e″) x y c′ d′ t₂′
                (subst (FIT (idₖ ⦃ Kᵣ ⦄)) (sym (++ᵗ-assoc ŝ (tν e″) srcWin))
                   (subst (FIT (idₖ ⦃ Kᵣ ⦄)) srcTelEq
                      (FIT-leaf-subst (idₖ ⦃ Kᵣ ⦄) (sym kEqk) (ŝ ++ᵗ tν t)
                         (subst (FIT (idₖ ⦃ Kᵣ ⦄)) eqT̂ fit)))))
    reshapeM-NF : mkNF (ŝ ++ᵗ tν (renTel t′ (gapρ a w))) (map (_⋯ liftRen t′ (gapρ a w)) esFired)
                    ≡ mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂ (assocSwapᵣ 1 1))))
                           (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) es₂)
    Lwin : Tel j (innerOf t₂ (2 + j))
    Lwin = tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel t₂ (assocSwapᵣ 1 1)))
    mkΦ : (ss : Tel n j) (ee : List (Tm (innerOf t (2 + i)))) → NF n
    mkΦ ss ee = mkNF (ss ++ᵗ Lwin) (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) ee)
    eM : innerOf t′ (2 + i) ≡ innerOf t₂ (2 + j)
    eM = renTel-id t′ ■ renTel-id t₂′ ■ cong (λ z → innerOf t₂ (2 + z)) (renTel-id e′)
    deepM : subst (Tel (2 + i)) eM (renTel t′ (gapρ a w)) ≡ e′ ++ᵗ Lwin
    σ″ : innerOf e′ (2 + i) →ᵣ innerOf e″ (2 + i)
    σ″ = liftRen e″ (gapρ a w)
    pL : innerOf e″ (2 + i) ≡ j
    pL = innerOf-renTel e′ (gapρ a w) (2 + i) ■ renTel-id e′
    ρ′ : innerOf e′ (2 + i) →ᵣ j
    ρ′ y = subst 𝔽 pL (σ″ y)
    collapse : ∀ y → ρ′ (σ y) ≡ y
    collapse y = invThr e′ (gapρ a w) (λ z → gapρ-invol a w z) y
    g1 : d′ ⋯ ρ′ ≡ d
    g1 = fusion d σ ρ′ ■ ⋯-id d (λ y → collapse y)
    g2 : (c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑) ≡ c ⋯ weaken* ⦃ Kᵣ ⦄ 1
    g2 = gate-pres c′ ρ′ ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 1) (fusion c σ ρ′ ■ ⋯-id c (λ y → collapse y))
    LEAF : innerOf firWin j ≡ innerOf t₂ (2 + j)
    LEAF = cong (innerOf firWin) (sym (renTel-id e′)) ■ renTel-id firWin ■ renTel-id t₂′
         ■ cong (λ z → innerOf t₂ (2 + z)) (renTel-id e′)
    gpt : ∀ z → ((σ ↑* 2) ·ₖ (assocSwapᵣ 1 1 ·ₖ (ρ′ ↑* 2))) z ≡ assocSwapᵣ 1 1 z
    gpt z = cong (ρ′ ↑* 2) (comm-↑²-aswap11-gen σ z)
          ■ sym (dist-↑*-· 2 σ ρ′ (assocSwapᵣ 1 1 z))
          ■ id↑* 2 (λ w → collapse w) (assocSwapᵣ 1 1 z)
    g3 : subst (Tel (2 + j)) LEAF (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2)) ≡ renTel t₂ (assocSwapᵣ 1 1)
    g3 = cong (λ e → subst (Tel (2 + j)) e (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2)))
              (≡-irrelevant LEAF (innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + j)
                                  ■ innerOf-renTel t₂ (σ ↑* 2) (2 + j)))
       ■ subst-■ (Tel (2 + j)) (innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + j))
                 (innerOf-renTel t₂ (σ ↑* 2) (2 + j))
                 (renTel (renTel t₂′ (assocSwapᵣ 1 1)) (ρ′ ↑* 2))
       ■ cong (subst (Tel (2 + j)) (innerOf-renTel t₂ (σ ↑* 2) (2 + j)))
              (renTel-renTel t₂′ (assocSwapᵣ 1 1) (ρ′ ↑* 2))
       ■ renTel-renTel t₂ (σ ↑* 2) (assocSwapᵣ 1 1 ·ₖ (ρ′ ↑* 2))
       ■ renTel-cong t₂ (λ z → gpt z)
    tailLwin : subst (Tel j) LEAF (renTel firWin ρ′) ≡ Lwin
    tailLwin = subst-tφ LEAF y (d′ ⋯ ρ′) _
             ■ cong (tφ y (d′ ⋯ ρ′))
                    (subst-tφ LEAF x ((c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑)) _
                     ■ cong (tφ x ((c′ ⋯ weaken* ⦃ Kᵣ ⦄ 1) ⋯ (ρ′ ↑))) g3)
             ■ cong₂ (tφ y) g1 (cong₂ (tφ x) g2 refl)
    SCOPE : innerOf t′ (2 + i) ≡ innerOf t₂ (2 + j)
    SCOPE = innerOf-++ᵗ e″ firWin (2 + i) ■ cong (innerOf firWin) pL ■ LEAF
    E2 : subst (Tel (2 + i)) (cong (innerOf firWin) pL)
             (renTel e″ (gapρ a w) ++ᵗ renTel firWin σ″)
           ≡ e′ ++ᵗ renTel firWin ρ′
    E2 = telMidᴺ pL (renTel e″ (gapρ a w)) firWin (λ y → refl)
       ■ cong (_++ᵗ renTel firWin ρ′) (invTel e′ (gapρ a w) (λ z → gapρ-invol a w z))
    E3 : subst (Tel (2 + i)) LEAF (e′ ++ᵗ renTel firWin ρ′) ≡ e′ ++ᵗ Lwin
    E3 = subst-++ᵗ e′ LEAF (renTel firWin ρ′) ■ cong (e′ ++ᵗ_) tailLwin
    deepM =
      cong (λ e → subst (Tel (2 + i)) e (renTel t′ (gapρ a w))) (≡-irrelevant eM SCOPE)
      ■ subst-■ (Tel (2 + i)) (innerOf-++ᵗ e″ firWin (2 + i)) (cong (innerOf firWin) pL ■ LEAF)
                (renTel t′ (gapρ a w))
      ■ cong (subst (Tel (2 + i)) (cong (innerOf firWin) pL ■ LEAF))
             (renTel-++ᵗ e″ firWin (gapρ a w))
      ■ subst-■ (Tel (2 + i)) (cong (innerOf firWin) pL) LEAF
                (renTel e″ (gapρ a w) ++ᵗ renTel firWin σ″)
      ■ cong (subst (Tel (2 + i)) LEAF) E2
      ■ E3
    telM : subst (Tel n) eM (ŝ ++ᵗ tν (renTel t′ (gapρ a w))) ≡ (ŝ ++ᵗ tν e′) ++ᵗ Lwin
    telM = subst-++ᵗ ŝ eM (tν (renTel t′ (gapρ a w)))
         ■ cong (ŝ ++ᵗ_) (subst-tν eM (renTel t′ (gapρ a w)) ■ cong tν deepM)
         ■ sym (++ᵗ-assoc ŝ (tν e′) Lwin)
    thrM : subst (λ z → List (Tm z)) eM (map (_⋯ liftRen t′ (gapρ a w)) esFired)
             ≡ map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) (map (_⋯ liftRen t (gapρ a w)) esˢ)
    hPt : ∀ y →
          subst 𝔽 eM ((liftRen t₂′ (assocSwapᵣ 1 1) ·ₖ liftRen t′ (gapρ a w))
                        (subst 𝔽 (sym kEqk) y))
            ≡ (liftRen t (gapρ a w) ·ₖ liftRen t₂ (assocSwapᵣ 1 1)) y
    hPt y =
        cong (subst 𝔽 eM) LHScoreExp
      ■ cong (λ w → subst 𝔽 eM (subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) w)))
             (A3toX ■ cong (subst 𝔽 pp3) Xexp)
      ■ mergeCollapse
      ■ sym (cong (liftRen t₂ (assocSwapᵣ 1 1)) hZ)
      where
        V : 𝔽 (innerOf t₂ (2 + innerOf e′ (2 + i)))
        V = subst 𝔽 (sym kEqk) y
        z₀ : 𝔽 (innerOf t₂′ (2 + innerOf e″ (2 + i)))
        z₀ = liftRen t₂′ (σ″ ↑* 2) V
        qq1 : innerOf (e″ ++ᵗ firWin) (2 + i) ≡ innerOf firWin (innerOf e″ (2 + i))
        qq1 = innerOf-++ᵗ e″ firWin (2 + i)
        qq2 : innerOf (renTel t₂′ (assocSwapᵣ 1 1)) (2 + innerOf e″ (2 + i))
               ≡ innerOf t₂′ (2 + innerOf e″ (2 + i))
        qq2 = innerOf-renTel t₂′ (assocSwapᵣ 1 1) (2 + innerOf e″ (2 + i))
        -- LHS core reduces to A3 = liftRen t₂′ (aswap11 ·ₖ σ″↑*2) V
        redA : subst 𝔽 qq2 (subst 𝔽 qq1 (liftRen t′ (gapρ a w) (liftRen t₂′ (assocSwapᵣ 1 1) V)))
                 ≡ liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V
        redA = cong (subst 𝔽 qq2) (liftRen-++ᵗ e″ firWin (gapρ a w) (liftRen t₂′ (assocSwapᵣ 1 1) V))
             ■ liftRen-· t₂′ (assocSwapᵣ 1 1) (σ″ ↑* 2) V
        -- RHS: reduce liftRen t (swap11) y to the σ″-window form.
        gT : Tel (2 + i) (innerOf t₂ (2 + innerOf e′ (2 + i))) → ℕ
        gT T = innerOf T (2 + i)
        wa : subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + i))
               (liftRen (subst (Tel (2 + i)) (sym kEqk) t) (gapρ a w) V)
               ≡ liftRen t (gapρ a w) y
        wa = liftRen-substⁱ (sym kEqk) t (gapρ a w) V
           ■ cong (liftRen t (gapρ a w)) (subst-symˡ (sym kEqk) y)
        wb : subst 𝔽 (cong gT deepEq)
               (liftRen (subst (Tel (2 + i)) (sym kEqk) t) (gapρ a w) V)
               ≡ liftRen (e″ ++ᵗ srcWin) (gapρ a w) V
        wb = sym (subst-reix gT deepEq (liftRen (subst (Tel (2 + i)) (sym kEqk) t) (gapρ a w) V))
           ■ substf (λ T → liftRen T (gapρ a w) V) deepEq
        wc : subst 𝔽 (innerOf-++ᵗ e″ srcWin (2 + i))
               (liftRen (e″ ++ᵗ srcWin) (gapρ a w) V) ≡ liftRen t₂′ (σ″ ↑* 2) V
        wc = liftRen-++ᵗ e″ srcWin (gapρ a w) V
        wc' : liftRen (e″ ++ᵗ srcWin) (gapρ a w) V
                ≡ subst 𝔽 (sym (innerOf-++ᵗ e″ srcWin (2 + i))) (liftRen t₂′ (σ″ ↑* 2) V)
        wc' = sym (subst-symˡ (innerOf-++ᵗ e″ srcWin (2 + i)) (liftRen (e″ ++ᵗ srcWin) (gapρ a w) V))
            ■ cong (subst 𝔽 (sym (innerOf-++ᵗ e″ srcWin (2 + i)))) wc
        wb' : liftRen (subst (Tel (2 + i)) (sym kEqk) t) (gapρ a w) V
                ≡ subst 𝔽 (sym (cong gT deepEq)) (liftRen (e″ ++ᵗ srcWin) (gapρ a w) V)
        wb' = sym (subst-symˡ (cong gT deepEq) (liftRen (subst (Tel (2 + i)) (sym kEqk) t) (gapρ a w) V))
            ■ cong (subst 𝔽 (sym (cong gT deepEq))) wb
        wRed : liftRen t (gapρ a w) y
                 ≡ subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + i))
                     (subst 𝔽 (sym (cong gT deepEq))
                       (subst 𝔽 (sym (innerOf-++ᵗ e″ srcWin (2 + i)))
                         (liftRen t₂′ (σ″ ↑* 2) V)))
        wRed = sym wa
             ■ cong (subst 𝔽 (innerOf-substⁱ (sym kEqk) t (2 + i)))
                    (wb' ■ cong (subst 𝔽 (sym (cong gT deepEq))) wc')
        -- Glue via glueG2: cross the σ↑*2 / σ″↑*2 double renTel to bare t₂.
        eG : 2 + j ≡ 2 + innerOf e″ (2 + i)
        eG = cong (λ z → 2 + z) (sym pL)
        σσ″ : ∀ w → (σ ·ₖ σ″) w ≡ subst 𝔽 (sym pL) w
        σσ″ w = sym (subst-symˡ pL ((σ ·ₖ σ″) w)) ■ cong (subst 𝔽 (sym pL)) (collapse w)
        heκ : ∀ x → (σ″ ↑* 2) ((σ ↑* 2) x) ≡ subst 𝔽 eG x
        heκ x = sym (dist-↑*-· 2 σ σ″ x) ■ (σσ″ ~↑* 2) x ■ ↑*2-substᵃ (sym pL) x
        gApp : subst 𝔽 (innerOf-renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2) (2 + innerOf e″ (2 + i))
                        ■ innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf e″ (2 + i)))
                     (liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀)
                 ≡ subst 𝔽 (cong (innerOf t₂) eG)
                          (liftRen t₂ (assocSwapᵣ 1 1)
                            (subst 𝔽 (innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf e″ (2 + i))
                                       ■ sym (cong (innerOf t₂) eG) ■ renTel-id t₂) z₀))
        gApp = glueG2 eG eG t₂ (σ ↑* 2) (σ″ ↑* 2) heκ (assocSwapᵣ 1 1) (assocSwapᵣ 1 1)
                      (aswap-nat eG) z₀
        pp3 : innerOf (renTel t₂′ (σ″ ↑* 2)) (2 + innerOf e″ (2 + i))
               ≡ innerOf t₂′ (2 + innerOf e″ (2 + i))
        pp3 = innerOf-renTel t₂′ (σ″ ↑* 2) (2 + innerOf e″ (2 + i))
        QQ : innerOf (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (2 + innerOf e″ (2 + i))
               ≡ innerOf t₂ (2 + innerOf e″ (2 + i))
        QQ = innerOf-renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2) (2 + innerOf e″ (2 + i))
           ■ innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf e″ (2 + i))
        W₂ : innerOf t₂′ (2 + innerOf e″ (2 + i)) ≡ innerOf t (2 + i)
        W₂ = innerOf-renTel t₂ (σ ↑* 2) (2 + innerOf e″ (2 + i))
           ■ sym (cong (innerOf t₂) eG) ■ renTel-id t₂
        RHSg : 𝔽 (innerOf t₂ (2 + innerOf e″ (2 + i)))
        RHSg = subst 𝔽 (cong (innerOf t₂) eG)
                     (liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀))
        LHScoreExp : liftRen t′ (gapρ a w) (liftRen t₂′ (assocSwapᵣ 1 1) V)
                       ≡ subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) (liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V))
        LHScoreExp = sym (subst-symˡ qq1 _)
                   ■ cong (subst 𝔽 (sym qq1)) (sym (subst-symˡ qq2 _))
                   ■ cong (λ w → subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2) w)) redA
        A3toX : liftRen t₂′ (assocSwapᵣ 1 1 ·ₖ (σ″ ↑* 2)) V
                  ≡ subst 𝔽 pp3 (liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀)
        A3toX = liftRen-cong t₂′ (λ z → sym (comm-↑²-aswap11-gen σ″ z)) V
              ■ sym (liftRen-· t₂′ (σ″ ↑* 2) (assocSwapᵣ 1 1) V)
        Xexp : liftRen (renTel (renTel t₂ (σ ↑* 2)) (σ″ ↑* 2)) (assocSwapᵣ 1 1) z₀
                 ≡ subst 𝔽 (sym QQ) RHSg
        Xexp = sym (subst-symˡ QQ _) ■ cong (subst 𝔽 (sym QQ)) gApp
        hZ : liftRen t (gapρ a w) y ≡ subst 𝔽 W₂ z₀
        hZ = wRed
           ■ subst3≡ (sym (innerOf-++ᵗ e″ srcWin (2 + i))) (sym (cong gT deepEq))
                     (innerOf-substⁱ (sym kEqk) t (2 + i)) W₂ z₀
        mergeCollapse : subst 𝔽 eM (subst 𝔽 (sym qq1) (subst 𝔽 (sym qq2)
                          (subst 𝔽 pp3 (subst 𝔽 (sym QQ) RHSg))))
                          ≡ liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀)
        mergeCollapse =
          subst6-id (cong (innerOf t₂) eG) (sym QQ) pp3 (sym qq2) (sym qq1) eM
                    (liftRen t₂ (assocSwapᵣ 1 1) (subst 𝔽 W₂ z₀))
    thrM = cong (subst (λ z → List (Tm z)) eM)
                (map-fuse (liftRen t₂′ (assocSwapᵣ 1 1)) (liftRen t′ (gapρ a w)) esˢ″)
         ■ cong (subst (λ z → List (Tm z)) eM)
                (map-⋯-substTm (sym kEqk)
                   (liftRen t₂′ (assocSwapᵣ 1 1) ·ₖ liftRen t′ (gapρ a w)) esˢ)
         ■ map-⋯-subst eM hPt esˢ
         ■ sym (map-fuse (liftRen t (gapρ a w)) (liftRen t₂ (assocSwapᵣ 1 1)) esˢ)
    reshapeM-NF = NF-≡ eM telM thrM ■ sym (cong₂ mkΦ p̂ eqE)
pushφφ {n = n} {j = j} s₂ x y c d t₂ es₂ (swapᴿ {j = j₁} {i = i} s {a} w t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q
  | cmpʳ (tφ x′ c′ (tφ y′ d′ e₃)) p′ q′
    with tφ-inj₁ q′ | tφ-inj-c q′ | tφ-inj₁ (tφ-inj₂ q′) | tφ-inj-c (tφ-inj₂ q′) | tφ-inj₂ (tφ-inj₂ q′)
...  | refl | refl | refl | refl | refl =
       φφRHS , cleg ,
       subst (Res φφRHS) reshapeM-NF
         (swapᴿ s {a = a′} w′ t′ {T = ŝ′ ++ᵗ tν t′} {es = esFired}
           (++ᵗ-assoc s (tν a′) (tν t′))
           (++ᵗ-assoc s (tν a′) (tν (renTel t′ (gapρ a′ w′))))
           refl fit′)
  where
    Φ = liftRen e₃ (assocSwapᵣ 1 1) ↑* 2
    t′ = renTel t Φ
    a′ = dg ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))
    w′ = buildW′ dg x y c d e₃ (subst Run p′ w)
    ŝ′ = s ++ᵗ tν a′
    κ : innerOf (e₃ ++ᵗ tν t) (2 + j) ≡ innerOf t (2 + innerOf e₃ (2 + j))
    κ = innerOf-++ᵗ e₃ (tν t) (2 + j)
    esFired : List (Tm (innerOf t (2 + innerOf e₃ (2 + j))))
    esFired = subst (λ z → List (Tm z)) κ
                (map (_⋯ liftRen (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1)) esˢ)
    φφRHS : NF n
    φφRHS = mkNF (ŝ′ ++ᵗ tν t′) esFired
    W₁ = tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) e₃)
    V₁ = tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel e₃ (assocSwapᵣ 1 1)))
    srcTelEq : T ≡ (s ++ᵗ tν dg) ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (e₃ ++ᵗ tν t))
    srcTelEq = eqT
             ■ cong (λ z → s ++ᵗ tν (z ++ᵗ tν t)) p′
             ■ cong (λ z → s ++ᵗ tν z) (++ᵗ-assoc dg W₁ (tν t))
             ■ sym (++ᵗ-assoc s (tν dg) (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (e₃ ++ᵗ tν t))))
    TGT = (s ++ᵗ tν dg) ++ᵗ
            tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1)))
    leafκ : subst (Tel (2 + j)) κ (renTel (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1))
              ≡ renTel e₃ (assocSwapᵣ 1 1) ++ᵗ tν t′
    leafκ = renTel-++ᵗ e₃ (tν t) (assocSwapᵣ 1 1)
    telκ : subst (Tel n) κ TGT ≡ ŝ′ ++ᵗ tν t′
    telκ = subst-++ᵗ (s ++ᵗ tν dg) κ
             (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1))))
         ■ cong ((s ++ᵗ tν dg) ++ᵗ_)
             ( subst-tφ κ y d _
             ■ cong (tφ y d)
                 ( subst-tφ κ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) _
                 ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)) leafκ ) )
         ■ sym (++ᵗ-assoc (s ++ᵗ tν dg) V₁ (tν t′))
         ■ cong (_++ᵗ tν t′) (++ᵗ-assoc s (tν dg) V₁)
    cleg : mkNF T esˢ ~ᵩ φφRHS
    cleg = ~ᵩ-trans (≡→~ᵩ (cong (λ z → mkNF z esˢ) srcTelEq))
             (~ᵩ-trans (Eq*.return (φφᵩ (s ++ᵗ tν dg) x y c d (e₃ ++ᵗ tν t) esˢ))
                       (≡→~ᵩ (NF-≡ κ telκ refl)))
    fit′ : FIT (idₖ ⦃ Kᵣ ⦄) (ŝ′ ++ᵗ tν t′)
    fit′ = subst (FIT (idₖ ⦃ Kᵣ ⦄)) telκ
             (FIT-leaf-subst (idₖ ⦃ Kᵣ ⦄) κ TGT
                (FIT-pres-φφ (idₖ ⦃ Kᵣ ⦄) (s ++ᵗ tν dg) x y c d (e₃ ++ᵗ tν t)
                   (subst (FIT (idₖ ⦃ Kᵣ ⦄)) srcTelEq fit)))
    tG = renTel t (gapρ a w)
    gcast : ∀ {a₂ : Tel (2 + j₁) i} (eq : a ≡ a₂) (w₀ : Run a) →
            gapρ a₂ (subst Run eq w₀) ≡ gapρ a w₀
    gcast refl w₀ = refl
    Fz : ∀ (z : 𝔽 (2 + i)) → gapρ a′ w′ (Φ z) ≡ Φ (gapρ a w z)
    Fz z = F dg x y c d e₃ (subst Run p′ w) z
         ■ cong (λ f → Φ (f z)) (gcast p′ w)
    deepLeaf-tel :
      subst (Tel (2 + innerOf e₃ (2 + j))) (innerOf-renTel t Φ (2 + innerOf e₃ (2 + j)))
            (renTel (renTel t Φ) (gapρ a′ w′))
        ≡ subst (Tel (2 + innerOf e₃ (2 + j))) (innerOf-renTel t (gapρ a w) (2 + innerOf e₃ (2 + j)))
            (renTel (renTel t (gapρ a w)) Φ)
    deepLeaf-tel = renTel-renTel t Φ (gapρ a′ w′)
                 ■ renTel-cong t (λ z → Fz z)
                 ■ sym (renTel-renTel t (gapρ a w) Φ)
    deepLeaf-thr : ∀ x₀ →
      subst 𝔽 (innerOf-renTel t Φ (2 + innerOf e₃ (2 + j)))
            (liftRen (renTel t Φ) (gapρ a′ w′) (liftRen t Φ x₀))
        ≡ subst 𝔽 (innerOf-renTel t (gapρ a w) (2 + innerOf e₃ (2 + j)))
            (liftRen (renTel t (gapρ a w)) Φ (liftRen t (gapρ a w) x₀))
    deepLeaf-thr x₀ = liftRen-· t Φ (gapρ a′ w′) x₀
                    ■ liftRen-cong t (λ z → Fz z) x₀
                    ■ sym (liftRen-· t (gapρ a w) Φ x₀)
    mkΦ : (ss : Tel n j) (ee : List (Tm (innerOf t (2 + i)))) → NF n
    mkΦ ss ee = mkNF (ss ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1))))
                     (map (_⋯ liftRen (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1)) ee)
    eM : innerOf (renTel t Φ) (2 + innerOf e₃ (2 + j)) ≡ innerOf (e₃ ++ᵗ tν tG) (2 + j)
    eM = innerOf-renTel t Φ (2 + innerOf e₃ (2 + j))
       ■ sym (innerOf-renTel t (gapρ a w) (2 + innerOf e₃ (2 + j)))
       ■ sym (innerOf-++ᵗ e₃ (tν tG) (2 + j))
    α₁ = innerOf-renTel t Φ (2 + innerOf e₃ (2 + j))
    α₂ = innerOf-renTel t (gapρ a w) (2 + innerOf e₃ (2 + j))
    κ₂ = innerOf-++ᵗ e₃ (tν tG) (2 + j)
    leafκ-tG : subst (Tel (2 + j)) κ₂ (renTel (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1))
                 ≡ renTel e₃ (assocSwapᵣ 1 1) ++ᵗ tν (renTel tG Φ)
    leafκ-tG = renTel-++ᵗ e₃ (tν tG) (assocSwapᵣ 1 1)
    telκ-tG : subst (Tel n) κ₂
                ((s ++ᵗ tν dg) ++ᵗ
                  tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1))))
                ≡ ŝ′ ++ᵗ tν (renTel tG Φ)
    telκ-tG = subst-++ᵗ (s ++ᵗ tν dg) κ₂
                (tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1))))
            ■ cong ((s ++ᵗ tν dg) ++ᵗ_)
                ( subst-tφ κ₂ y d _
                ■ cong (tφ y d)
                    ( subst-tφ κ₂ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) _
                    ■ cong (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)) leafκ-tG ) )
            ■ sym (++ᵗ-assoc (s ++ᵗ tν dg) V₁ (tν (renTel tG Φ)))
            ■ cong (_++ᵗ tν (renTel tG Φ)) (++ᵗ-assoc s (tν dg) V₁)
    telM : subst (Tel n) eM (ŝ′ ++ᵗ tν (renTel t′ (gapρ a′ w′)))
             ≡ (s ++ᵗ tν dg) ++ᵗ
                 tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1)))
    telM = subst-■ (Tel n) α₁ (sym α₂ ■ sym κ₂) (ŝ′ ++ᵗ tν (renTel t′ (gapρ a′ w′)))
         ■ subst-■ (Tel n) (sym α₂) (sym κ₂)
             (subst (Tel n) α₁ (ŝ′ ++ᵗ tν (renTel t′ (gapρ a′ w′))))
         ■ cong (subst (Tel n) (sym κ₂))
             ( cong (subst (Tel n) (sym α₂))
                 ( subst-++ᵗ ŝ′ α₁ (tν (renTel t′ (gapρ a′ w′)))
                 ■ cong (ŝ′ ++ᵗ_) (subst-tν α₁ (renTel t′ (gapρ a′ w′))) )
             ■ subst-++ᵗ ŝ′ (sym α₂)
                 (tν (subst (Tel (2 + innerOf e₃ (2 + j))) α₁ (renTel t′ (gapρ a′ w′))))
             ■ cong (ŝ′ ++ᵗ_)
                 ( subst-tν (sym α₂)
                     (subst (Tel (2 + innerOf e₃ (2 + j))) α₁ (renTel t′ (gapρ a′ w′)))
                 ■ cong tν
                     ( cong (subst (Tel (2 + innerOf e₃ (2 + j))) (sym α₂)) deepLeaf-tel
                     ■ subst-symˡ α₂ (renTel (renTel t (gapρ a w)) Φ) ) ) )
         ■ sym (subst-swap κ₂ telκ-tG)
    hThr : ∀ x →
      subst 𝔽 eM (liftRen t′ (gapρ a′ w′) (subst 𝔽 κ (liftRen (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1) x)))
        ≡ liftRen (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1) (liftRen t (gapρ a w) x)
    hThr x =
        cong (λ w → subst 𝔽 eM (liftRen t′ (gapρ a′ w′) w))
             (liftRen-++ᵗ e₃ (tν t) (assocSwapᵣ 1 1) x)
      ■ cong (subst 𝔽 eM) (subst-swap α₁ (liftRen-· t Φ (gapρ a′ w′) x))
      ■ sym (subst-■ 𝔽 (sym α₁) eM (liftRen t (Φ ·ₖ gapρ a′ w′) x))
      ■ cong (λ e → subst 𝔽 e (liftRen t (Φ ·ₖ gapρ a′ w′) x))
             (≡-irrelevant (sym α₁ ■ eM) (sym α₂ ■ sym κ₂))
      ■ subst-■ 𝔽 (sym α₂) (sym κ₂) (liftRen t (Φ ·ₖ gapρ a′ w′) x)
      ■ cong (λ w → subst 𝔽 (sym κ₂) (subst 𝔽 (sym α₂) w))
             (liftRen-cong t (λ z → Fz z) x)
      ■ cong (subst 𝔽 (sym κ₂)) (sym (subst-swap α₂ (liftRen-· t (gapρ a w) Φ x)))
      ■ sym (subst-swap κ₂ (liftRen-++ᵗ e₃ (tν tG) (assocSwapᵣ 1 1) (liftRen t (gapρ a w) x)))
    thrM : subst (λ z → List (Tm z)) eM (map (_⋯ liftRen t′ (gapρ a′ w′)) esFired)
             ≡ map (_⋯ liftRen (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1)) (map (_⋯ liftRen t (gapρ a w)) esˢ)
    thrM = cong (subst (λ z → List (Tm z)) eM)
                ( map-⋯-substTm κ (liftRen t′ (gapρ a′ w′))
                    (map (_⋯ liftRen (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1)) esˢ)
                ■ map-fuse (liftRen (e₃ ++ᵗ tν t) (assocSwapᵣ 1 1))
                    (λ y → liftRen t′ (gapρ a′ w′) (subst 𝔽 κ y)) esˢ )
         ■ map-⋯-subst eM hThr esˢ
         ■ sym (map-fuse (liftRen t (gapρ a w)) (liftRen (e₃ ++ᵗ tν tG) (assocSwapᵣ 1 1)) esˢ)
    reshapeM-NF : mkNF (ŝ′ ++ᵗ tν (renTel t′ (gapρ a′ w′)))
                       (map (_⋯ liftRen t′ (gapρ a′ w′)) esFired)
                    ≡ mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                             (renTel (e₃ ++ᵗ tν (renTel t (gapρ a w))) (assocSwapᵣ 1 1))))
                           (map (_⋯ liftRen (e₃ ++ᵗ tν (renTel t (gapρ a w))) (assocSwapᵣ 1 1)) es₂)
    reshapeM-NF = NF-≡ eM telM thrM ■ sym (cong₂ mkΦ p eqE)
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q
  | cmpʳ (tφ x′ c′ []) p′ q′ with tφ-inj₂ q′
... | ()
pushφφ s₂ x y c d t₂ es₂ (swapᴿ s {a} w t {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ (tν dg) p q
  | cmpʳ (tφ x′ c′ (tν e′)) p′ q′ with tφ-inj₂ q′
... | ()

pushνφ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x : Flag) (c : Tm j)
         (t₂ : Tel (1 + (2 + j)) k) (es₂ : List (Tm k)) →
         Res N (mkNF (s₂ ++ᵗ tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t₂)) es₂) →
         Σ[ N′ ∈ NF n ] (N ~ᵩ N′) ×
           Res N′ (mkNF (s₂ ++ᵗ tφ x c (tν (renTel t₂ (assocSwapᵣ 1 2))))
                        (map (_⋯ liftRen t₂ (assocSwapᵣ 1 2)) es₂))
pushνφ s₂ x c t₂ es₂ r = {!!}

pushνφ⁻ : ∀ {n j k} {N : NF n} (s₂ : Tel n j) (x : Flag) (c : Tm j)
          (t₂ : Tel (1 + (2 + j)) k) (es₂ : List (Tm k)) →
          Res N (mkNF (s₂ ++ᵗ tφ x c (tν (renTel t₂ (assocSwapᵣ 1 2))))
                      (map (_⋯ liftRen t₂ (assocSwapᵣ 1 2)) es₂)) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF (s₂ ++ᵗ tν (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 2) t₂)) es₂)
pushνφ⁻ s₂ x c t₂ es₂ r = {!!}

private
  aswap11-undo : ∀ {j k} (t₂ : Tel (2 + j) k) (es : List (Tm k)) →
                 map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) (map (_⋯ liftId t₂ (assocSwapᵣ 1 1)) es) ≡ es
  aswap11-undo t₂ es =
    map-fuse (liftId t₂ (assocSwapᵣ 1 1)) (liftId t₂ (assocSwapᵣ 1 1)) es
      ■ map-⋯-id (λ x → liftId-· t₂ (assocSwapᵣ 1 1) (assocSwapᵣ 1 1) x
                          ■ liftId-id t₂ (λ y → aswap-11-inv y) x) es

push : ∀ {n} {N K L : NF n} → Res N K → K ~ᵩ₁ L →
       Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ L
push r (φφᵩ s₂ x y c d t₂ es₂) = pushφφ s₂ x y c d t₂ es₂ r
push r (νφᵩ s₂ x c t₂ es₂)     = pushνφ s₂ x c t₂ es₂ r
push r (thrᵩ T {es₁} {es₂} p)  = pushThr T es₁ es₂ p r
push r (delᵩ T es₂)            = pushDel T es₂ r

push⁻ : ∀ {n} {N K L : NF n} → Res N K → L ~ᵩ₁ K →
        Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ L
push⁻ r (φφᵩ s₂ x y c d t₂ es₃)
  with pushφφ s₂ y x d c (renTel t₂ (assocSwapᵣ 1 1))
                (map (_⋯ liftRen t₂ (assocSwapᵣ 1 1)) es₃) r
... | N′ , cN , r′ = N′ , cN , subst (Res N′) reshapeL r′
  where
    ρ⁰ : _ →ᵣ _
    ρ⁰ = assocSwapᵣ 1 1
    kE : innerOf (renTel t₂ ρ⁰) (2 + _) ≡ _
    kE = innerOf-renTel t₂ ρ⁰ (2 + _) ■ renTel-id t₂
    telEq : subst (Tel _) kE
              (s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (renTel t₂ ρ⁰) ρ⁰)))
              ≡ s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)
    telEq = subst-++ᵗ s₂ kE (tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (renTel t₂ ρ⁰) ρ⁰)))
          ■ cong (s₂ ++ᵗ_)
              ( subst-tφ kE x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (renTel t₂ ρ⁰) ρ⁰))
              ■ cong (tφ x c)
                  ( subst-tφ kE y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (renTel t₂ ρ⁰) ρ⁰)
                  ■ cong (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1)) (invTel t₂ ρ⁰ (λ z → aswap-11-inv z)) ) )
    thrEq : subst (λ z → List (Tm z)) kE
              (map (_⋯ liftRen (renTel t₂ ρ⁰) ρ⁰) (map (_⋯ liftRen t₂ ρ⁰) es₃)) ≡ es₃
    thrEq = cong (subst (λ z → List (Tm z)) kE)
                 (map-fuse (liftRen t₂ ρ⁰) (liftRen (renTel t₂ ρ⁰) ρ⁰) es₃)
          ■ map-⋯-subst kE (λ z → invThr t₂ ρ⁰ (λ w → aswap-11-inv w) z) es₃
          ■ map-⋯-id (λ _ → refl) es₃
    reshapeL : mkNF (s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) (renTel (renTel t₂ ρ⁰) ρ⁰)))
                    (map (_⋯ liftRen (renTel t₂ ρ⁰) ρ⁰) (map (_⋯ liftRen t₂ ρ⁰) es₃))
                 ≡ mkNF (s₂ ++ᵗ tφ x c (tφ y (d ⋯ weaken* ⦃ Kᵣ ⦄ 1) t₂)) es₃
    reshapeL = NF-≡ kE telEq thrEq
push⁻ r (νφᵩ s₂ x c t₂ es₃)     = pushνφ⁻ s₂ x c t₂ es₃ r
push⁻ r (thrᵩ T {es₁} {es₂} p)  = pushThr T es₂ es₁ (↭-sym p) r
push⁻ r (delᵩ T es₃)            = pushIns T es₃ r

------------------------------------------------------------------------
-- Discharging a residue against a block form.
------------------------------------------------------------------------

Block-swaptel : ∀ {n j k k′} (s : Tel n j) (X : Tel (2 + j) k) (Y : Tel (2 + j) k′) →
                Block (s ++ᵗ tν X) → Block (s ++ᵗ tν Y)
Block-swaptel []         X Y bν = bν
Block-swaptel (tν s)     X Y bν = bν
Block-swaptel (tφ f c s) X Y ()

-- `renTel` preserves the head constructor, hence block form.
Block-renTel : ∀ {n k n′} {t : Tel n k} (ρ : n →ᵣ n′) → Block t → Block (renTel t ρ)
Block-renTel ρ bnil = bnil
Block-renTel ρ bν   = bν

-- Support-aware congruence for `renTel`: two base renamings that agree on the
-- ambient images `ω x` (the only names FIT-front-independent channels read)
-- produce the same re-based telescope.  The agreement propagates through
-- every binder because `renTel` under a ν/φ only ever touches weaken-images
-- of `ω`, on which `↑*`/`↑` commute with the shared agreement (N2ν/N2).
renFIT : ∀ {b n n′ k} (ω : b →ᵣ n) {σ σ′ : n →ᵣ n′} (t : Tel n k) →
         FIT ω t → (∀ x → σ (ω x) ≡ σ′ (ω x)) →
         renTel t σ ≡ renTel t σ′
renFIT ω []         fit               h = refl
renFIT ω {σ = σ} {σ′ = σ′} (tν t)     fit               h =
  cong tν (renFIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 2) {σ = σ ↑* 2} {σ′ = σ′ ↑* 2} t fit
             (λ x → N2ν σ (ω x) ■ cong (weaken* ⦃ Kᵣ ⦄ 2) (h x) ■ sym (N2ν σ′ (ω x))))
renFIT ω {σ = σ} {σ′ = σ′} (tφ f c t) ((cf , ceq) , rest) h =
  cong₂ (tφ f) chEq
    (renFIT (ω ·ₖ weaken* ⦃ Kᵣ ⦄ 1) {σ = σ ↑} {σ′ = σ′ ↑} t rest
       (λ x → N2 σ (ω x) ■ cong (weaken* ⦃ Kᵣ ⦄ 1) (h x) ■ sym (N2 σ′ (ω x))))
  where
    chEq : c ⋯ σ ≡ c ⋯ σ′
    chEq = cong (_⋯ σ) ceq ■ fusion cf ω σ ■ ⋯-cong cf (λ x → h x)
         ■ sym (fusion cf ω σ′) ■ sym (cong (_⋯ σ′) ceq)

realise : ∀ {n} {N M : NF n} → Res N M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
realise (flipᴿ s t {es = esˢ} refl refl refl fit) bM =
  mkNF (s ++ᵗ tν t) esˢ ,
  Block-swaptel s (renTel t (swapᵣ 1 1)) t bM ,
  ~ᵩ-refl ,
  Eq*.return (ν1ᵇ s t esˢ)
realise {n = n} (swapᴿ {j = j} {i = i} {k = k} s {a} w t {es = esˢ} refl refl refl fit) bM =
  mkNF (s ++ᵗ tν (a ++ᵗ tν t)) esˢ ,
  Block-swaptel s (a ++ᵗ tν (renTel t (gapρ a w))) (a ++ᵗ tν t) bM ,
  ~ᵩ-refl ,
  legᵇ
  where
    FI  = fit→FInner s a t fit
    ζ0  = proj₁ (proj₂ FI)
    fw0 = proj₂ (proj₂ FI)
    legᵇ : mkNF (s ++ᵗ tν (a ++ᵗ tν t)) esˢ
             ~ᵇ mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel t (gapρ a w))))
                     (map (_⋯ liftRen t (gapρ a w)) esˢ)
    legᵇ = ~ᵇ-trans stepN (~ᵇ-trans (≡→~ᵇ DNM) (~ᵇ-sym stepM))
      where
        RS  = splitRun t
        rb  = run RS
        rst = rest RS
        wb  = wrun RS
        brb = brest RS
        gρ  = gapρ a w
        ω0  = ζ0 ·ₖ weaken* ⦃ Kᵣ ⦄ 2
        fixc : ∀ x → gρ (wkTel (shift2 (tν a)) (ω0 x)) ≡ wkTel (shift2 (tν a)) (ω0 x)
        fixc x = cong gρ (wkS2tν-gen a (ω0 x)) ■ gapρ-fix a w (ζ0 x) ■ sym (wkS2tν-gen a (ω0 x))
        fwM : FRun _ ω0 (shift2 (tν a)) (runRen wb gρ)
        fwM = frunFix ω0 (shift2 (tν a)) gρ fixc fw0
        tM : Tel (innerOf rb (2 + i)) (innerOf rst (innerOf rb (2 + i)))
        tM = renTel rst (liftRen rb gρ)
        btM : Block tM
        btM = Block-renTel (liftRen rb gρ) brb
        kM : innerOf t (2 + i) ≡ innerOf rst (innerOf rb (2 + i))
        kM = cong (λ z → innerOf z (2 + i)) (splits RS) ■ innerOf-++ᵗ rb rst (2 + i)
        esM : List (Tm (innerOf rst (innerOf rb (2 + i))))
        esM = subst (λ z → List (Tm z)) kM (map (_⋯ liftRen t gρ) esˢ)
        D_N : NF _
        D_N = mkNF (s ++ᵗ bswapTel a ζ0 fw0 rst) (map (_⋯ bswapRen a ζ0 fw0 rst) esˢ)
        D_M : NF _
        D_M = mkNF (s ++ᵗ bswapTel a ζ0 fwM tM) (map (_⋯ bswapRen a ζ0 fwM tM) esM)
        reshapeN : mkNF (s ++ᵗ tν (a ++ᵗ tν t)) esˢ
                     ≡ mkNF (s ++ᵗ tν (a ++ᵗ tν (rb ++ᵗ rst))) esˢ
        reshapeN = cong (λ z → mkNF (s ++ᵗ tν (a ++ᵗ tν z)) esˢ) (splits RS)
        stepN : mkNF (s ++ᵗ tν (a ++ᵗ tν t)) esˢ ~ᵇ D_N
        stepN = ~ᵇ-trans (≡→~ᵇ reshapeN) (Eq*.return (bswpᵇ s w ζ0 fw0 brb esˢ))
        coreM : subst (Tel (2 + i)) kM (renTel t gρ) ≡ renTel rb gρ ++ᵗ tM
        coreM = subst-■ (Tel (2 + i)) (cong (λ z → innerOf z (2 + i)) (splits RS))
                        (innerOf-++ᵗ rb rst (2 + i)) (renTel t gρ)
              ■ cong (subst (Tel (2 + i)) (innerOf-++ᵗ rb rst (2 + i)))
                     ( sym (subst-reix (λ z → innerOf z (2 + i)) (splits RS) (renTel t gρ))
                     ■ substf (λ z → renTel z gρ) (splits RS) )
              ■ renTel-++ᵗ rb rst gρ
        telEqM : subst (Tel n) kM (s ++ᵗ tν (a ++ᵗ tν (renTel t gρ)))
                   ≡ s ++ᵗ tν (a ++ᵗ tν (renTel rb gρ ++ᵗ tM))
        telEqM = subst-++ᵗ s kM (tν (a ++ᵗ tν (renTel t gρ)))
               ■ cong (s ++ᵗ_)
                  ( subst-tν kM (a ++ᵗ tν (renTel t gρ))
                  ■ cong tν
                     ( subst-++ᵗ a kM (tν (renTel t gρ))
                     ■ cong (a ++ᵗ_)
                        ( subst-tν kM (renTel t gρ) ■ cong tν coreM ) ) )
        reshapeM : mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel t gρ))) (map (_⋯ liftRen t gρ) esˢ)
                     ≡ mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel rb gρ ++ᵗ tM))) esM
        reshapeM = NF-≡ kM telEqM refl
        stepM : mkNF (s ++ᵗ tν (a ++ᵗ tν (renTel t gρ))) (map (_⋯ liftRen t gρ) esˢ) ~ᵇ D_M
        stepM = ~ᵇ-trans (≡→~ᵇ reshapeM) (Eq*.return (bswpᵇ s w ζ0 fwM btM esM))
        -- The two swap-targets coincide.  `DNM = NF-≡ leafEq telEqD thrEqD`
        -- with `leafEq = sym (renTel-id t) ■ kM`.  After peeling `s`
        -- (`subst-++ᵗ`) and the outer `tν` (`subst-tν`) both subgoals reduce
        -- to a `dragTel`/`dragRen` ABSORPTION identity, by induction on `fw0`:
        --   subst (Tel (2+j)) leafEq
        --     (dragTel ω0 (shift2 (tν a)) fw0 (retail rst (tailRen rb (bubν⁻ (tν a)))))
        --     ≡ dragTel ω0 (shift2 (tν a)) fwM (retail tM (tailRen (renTel rb gρ) (bubν⁻ (tν a))))
        -- The tails differ by `renTel rst (liftRen rb gρ)` (= tM); this
        -- gρ-reindex is compensated by the difference between the two drag
        -- renamings, i.e. `drag_N ≗ liftRen rb gρ ·ₖ drag_M` on rst's leaf
        -- (front-independence of the run `rb`: `runFixed`/`gapρ-fix`).  Base
        -- case (rb = []) is the renaming identity `bubν⁻ (tν a) ≗ gρ ·ₖ …`
        -- (finite-perm-check first); the `frφ` step adds a `bubφ⁻ S` layer.
        DNM : D_N ≡ D_M
        DNM = NF-≡ leafEq telEqD thrEqD
          where
            leafEq : NF.inner D_N ≡ NF.inner D_M
            leafEq = sym (renTel-id t) ■ kM
            telEqD : subst (Tel n) leafEq (tel D_N) ≡ tel D_M
            telEqD = {!telEqD!}
            thrEqD : subst (λ z → List (Tm z)) leafEq (thr D_N) ≡ thr D_M
            thrEqD = {!thrEqD!}

------------------------------------------------------------------------
-- Pushing a residue down a `~ᵩ` chain, and the theorem.
------------------------------------------------------------------------

resolve : ∀ {n} {N K M : NF n} → Res N K → K ~ᵩ M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
resolve r ε           bM = realise r bM
resolve r (fwd h ◅ c) bM with push r h
... | N′ , cN , r′ with resolve r′ c bM
...   | M′ , b′ , c′ , cb = M′ , b′ , ~ᵩ-trans cN c′ , cb
resolve r (bwd h ◅ c) bM with push⁻ r h
... | N′ , cN , r′ with resolve r′ c bM
...   | M′ , b′ , c′ , cb = M′ , b′ , ~ᵩ-trans cN c′ , cb

factor′ : ∀ {n} {N M : NF n} → FIT (idₖ ⦃ Kᵣ ⦄) (tel N) → Block (tel M) → N ~ M →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
factor′ {M = M} fit bM ε = M , bM , ~ᵩ-refl , ~ᵇ-refl
factor′ fit bM (fwd g ◅ c) with factor′ (FIT-pres₁ g fit) bM c
... | M₁ , b₁ , cφ , cb with res-seed fit g
...   | inj₁ h = M₁ , b₁ , ~ᵩ-trans (Eq*.return h) cφ , cb
...   | inj₂ r with resolve r cφ b₁
...     | M₂ , b₂ , c₂ , cb₂ = M₂ , b₂ , c₂ , ~ᵇ-trans cb₂ cb
factor′ fit bM (bwd g ◅ c) with factor′ (FIT-pres₁⁻ g fit) bM c
... | M₁ , b₁ , cφ , cb with res-seed (FIT-pres₁⁻ g fit) g
...   | inj₁ h = M₁ , b₁ , ~ᵩ-trans (~ᵩ-sym (Eq*.return h)) cφ , cb
...   | inj₂ r with resolve (res-sym r) cφ b₁
...     | M₂ , b₂ , c₂ , cb₂ = M₂ , b₂ , c₂ , ~ᵇ-trans cb₂ cb
