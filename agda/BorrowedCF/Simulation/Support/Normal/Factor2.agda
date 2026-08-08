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
    reshapeM-NF = {!reshapeM!}
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
