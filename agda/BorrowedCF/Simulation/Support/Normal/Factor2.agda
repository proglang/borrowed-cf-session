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
    hPt y = {!hPt!}
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
... | cmpʳ dgap p q = {!cmpʳ-swap!}
... | cmpˡ dgap p q = {!cmpˡ-swap!}

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

realise : ∀ {n} {N M : NF n} → Res N M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
realise (flipᴿ s t {es = esˢ} refl refl refl fit) bM =
  mkNF (s ++ᵗ tν t) esˢ ,
  Block-swaptel s (renTel t (swapᵣ 1 1)) t bM ,
  ~ᵩ-refl ,
  Eq*.return (ν1ᵇ s t esˢ)
realise (swapᴿ s {a} w t {es = esˢ} refl refl refl fit) bM = {!swapᴿ!}

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
