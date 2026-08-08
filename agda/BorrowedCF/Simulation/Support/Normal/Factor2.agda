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
open import BorrowedCF.Simulation.Support.Normal.Endo using (liftId-id; ++ᵗ-idʳ; ++ᵗ-assoc; liftId-liftRen)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (map-⋯-cong; map-⋯-id; ≡→~; telMidᴺ; wkTel-shift2-tν)
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

-- FIT is invariant under a leaf-scope transport of its telescope.
FIT-leaf-subst : ∀ {b n k₁ k₂} (ω : b →ᵣ n) (e : k₁ ≡ k₂) (X : Tel n k₁) →
                 FIT ω X → FIT ω (subst (Tel n) e X)
FIT-leaf-subst ω refl X fit = fit

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

-- A `~ᵩ` step that does not touch the telescope crosses a residue by
-- conjugation with the residue's (involutive) renaming.
pushThr : ∀ {n k} {N : NF n} (T : Tel n k) (es₁ es₂ : List (Tm k)) → es₁ ↭ es₂ →
          Res N (mkNF T es₁) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushThr T es₁ es₂ p r = {!!}

pushDel : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T (K `unit ∷ es₂)) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T es₂)
pushDel T es₂ r = {!!}

pushIns : ∀ {n k} {N : NF n} (T : Tel n k) (es₂ : List (Tm k)) →
          Res N (mkNF T es₂) →
          Σ[ N′ ∈ NF n ] (N ~ᵩ N′) × Res N′ (mkNF T (K `unit ∷ es₂))
pushIns T es₂ r = {!!}

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
    reshapeM-NF : flipTarget ≡
                  mkNF (s₂ ++ᵗ tφ y d (tφ x (c ⋯ weaken* ⦃ Kᵣ ⦄ 1)
                          (renTel (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11)))
                       (map (_⋯ liftRen (dgap₂ ++ᵗ tν (renTel t (swapᵣ 1 1))) aswap11) es₂)
    reshapeM-NF = {!reshapeM!}
pushφφ s₂ x y c d t₂ es₂ (flipᴿ s t {T = T} {es = esˢ} eqT eqTᵗ eqE fit)
  | cmpˡ dgap p q = {!cmpˡ-flip!}
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
push⁻ r (φφᵩ s₂ x y c d t₂ es₃) = {!!}
push⁻ r (νφᵩ s₂ x c t₂ es₃)     = pushνφ⁻ s₂ x c t₂ es₃ r
push⁻ r (thrᵩ T {es₁} {es₂} p)  = pushThr T es₂ es₁ (↭-sym p) r
push⁻ r (delᵩ T es₃)            = pushIns T es₃ r

------------------------------------------------------------------------
-- Discharging a residue against a block form.
------------------------------------------------------------------------

realise : ∀ {n} {N M : NF n} → Res N M → Block (tel M) →
          Σ[ M′ ∈ NF n ] Block (tel M′) × (N ~ᵩ M′) × (M′ ~ᵇ M)
realise r bM = {!!}

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
