module BorrowedCF.Simulation.Theorems.DropQH where

-- | Helpers for the q-generalized R-Drop forward case (Theorems/DropQ.agda):
--   Bw-slide, the ϕ[ w ]-general interior-cell slide (SplitsH3's Brwk-slide is
--   the w = 1 / U.drop instance), plus the width-general syncs lemma it needs.
--   Lives entirely in the Splits Bφ family (SplitsH1 … SplitsRQ2 public chain).

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open T using (BindGroup)

open import BorrowedCF.Simulation.Theorems.SplitsRQ2 public

-- syncs ignores block widths: a width-w block before a nonempty tail adds
-- exactly one cell, whatever w is (syncs-rwk is the w = 1 reading).
syncs-insW : ∀ (w : ℕ) (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} →
             syncs (B₁ ++ w ∷ suc b₁ ∷ B₂) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂))
syncs-insW w []            {b₁} {B₂} = refl
syncs-insW w (a ∷ [])      {b₁} {B₂} = cong suc (syncs-insW w [] {b₁} {B₂})
syncs-insW w (a ∷ d ∷ B₁″) {b₁} {B₂} = cong suc (syncs-insW w (d ∷ B₁″) {b₁} {B₂})

-- the interior cell of the width-w block at list position ∣B₁∣ slides down to
-- the leaf (ϕ[ w ]-general Brwk-slide; proof structure copied verbatim).
Bw-slide : ∀ (w : ℕ) (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
           (Z : U.Proc (syncs (B₁ ++ w ∷ suc b₁ ∷ B₂) + a)) →
           Bφ (B₁ ++ w ∷ suc b₁ ∷ B₂) Z
           U.≋ Bφ (B₁ ++ suc b₁ ∷ B₂)
                 (U.φ ϕ[ w ] (subst U.Proc (cong (_+ a) (syncs-insW w B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                               U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
Bw-slide w B₁ {b₁} {B₂} {a} Z =
     ≡→≋ (Bφ-peel B₁ w (suc b₁ ∷ B₂) {a} Z)
  ◅◅ Pfx-cong B₁ (φ-past-Bφ (suc b₁ ∷ B₂) ϕ[ w ] {L.length B₁ + a} bodyW)
  ◅◅ ≡→≋
       ( cong (Pfx B₁) (cong (Bφ (suc b₁ ∷ B₂)) reconcile)
       ■ sym (Bφ-peel B₁ (suc b₁) B₂ {a}
                (U.φ ϕ[ w ] (subst U.Proc (cong (_+ a) (syncs-insW w B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                              U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    W0 : U.Proc (syncs (w ∷ suc b₁ ∷ B₂) + (L.length B₁ + a))
    W0 = subst U.Proc (peel-eq B₁ w (suc b₁ ∷ B₂) {a}) Z
    bodyW : U.Proc (sD + suc (L.length B₁ + a))
    bodyW = subst U.Proc (sym (+-suc sD (L.length B₁ + a))) W0
    reconcile : U.φ ϕ[ w ] (bodyW U.⋯ₚ assocSwapᵣ sD 1 {L.length B₁ + a})
                ≡ subst U.Proc (peel-eq B₁ (suc b₁) B₂ {a})
                    (U.φ ϕ[ w ] (subst U.Proc (cong (_+ a) (syncs-insW w B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                                  U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
    reconcile =
        cong (U.φ ϕ[ w ]) reconcileBody
      ■ sym (subst-φ (peel-eq B₁ (suc b₁) B₂ {a})
               (subst U.Proc (cong (_+ a) (syncs-insW w B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                 U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
      where
        raw : (sD + (1 + (L.length B₁ + a))) →ᵣ (1 + (sD + (L.length B₁ + a)))
        raw = assocSwapᵣ sD 1 {L.length B₁ + a}
        EQ : syncs (B₁ ++ w ∷ suc b₁ ∷ B₂) + a ≡ syncs (B₁ ++ suc b₁ ∷ B₂) + suc a
        EQ = cong (_+ a) (syncs-insW w B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)
        rhs≡ : subst U.Proc EQ Z U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}
               ≡ subst U.Proc (sw-cod B₁ {b₁} {B₂} {a})
                   (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)
        rhs≡ = cast-⋯2 (sw-dom B₁ {b₁} {B₂} {a}) (sw-cod B₁ {b₁} {B₂} {a}) (subst U.Proc EQ Z) raw
             ■ cong (λ w′ → subst U.Proc (sw-cod B₁ {b₁} {B₂} {a}) (w′ U.⋯ₚ raw))
                 (ss-U EQ (sw-dom B₁ {b₁} {B₂} {a}) {t = Z})
        bodyW≡ : bodyW ≡ subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z
        bodyW≡ = ss-U (peel-eq B₁ w (suc b₁ ∷ B₂) {a}) (sym (+-suc sD (L.length B₁ + a))) {t = Z}
               ■ cong (λ e → subst U.Proc e Z) (uipℕ _ (EQ ■ sw-dom B₁ {b₁} {B₂} {a}))
        reconcileBody =
            cong (U._⋯ₚ raw) bodyW≡
          ■ sym ( cong (subst U.Proc (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))) rhs≡
                ■ ss-U (sw-cod B₁ {b₁} {B₂} {a}) (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))
                       {t = subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw}
                ■ cong (λ e → subst U.Proc e (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)) (uipℕ _ refl) )

------------------------------------------------------------------------
-- The dropped-handle index map: R-Drop's dwk inserts ONE binder at the
-- front of the width-0 block at list position ∣B₁∣.  ddwk is its
-- structural restriction to the group-1 region (mirror of SplitsLQ.dlwkq).
------------------------------------------------------------------------

ddwk : ∀ (B₁ : BindGroup) (W : BindGroup) → sum (B₁ ++ 0 ∷ W) →ᵣ sum (B₁ ++ 1 ∷ W)
ddwk []        W i = Fin.suc i
ddwk (a ∷ B₁') W i =
  [ (λ p → p ↑ˡ sum (B₁' ++ 1 ∷ W)) , (λ r → a ↑ʳ ddwk B₁' W r) ]′ (Fin.splitAt a i)

-- syncs is width-blind: 0- and 1-width block lists have equal syncs
-- (definition mirrors syncs-lwk so the cons case is literally `cong suc`).
syncs-dw10 : ∀ (B₁ : BindGroup) {c' : ℕ} {B₂' : BindGroup} →
             syncs (B₁ ++ 0 ∷ suc c' ∷ B₂') ≡ syncs (B₁ ++ 1 ∷ suc c' ∷ B₂')
syncs-dw10 []            = refl
syncs-dw10 (a ∷ [])      = cong suc (syncs-dw10 [])
syncs-dw10 (a ∷ d ∷ B₁″) = cong suc (syncs-dw10 (d ∷ B₁″))

-- canonₛ collapse across the dropped handle: every width-0-list index is a
-- non-handle index of the width-1 list with an identical triple (mirror of
-- SplitsH1.canonₛ-lwk, without the handle-exclusion premise: the width-0
-- block has no indices at all).
canonₛ-dwk : ∀ (B₁ : BindGroup) {c' : ℕ} {B₂' : BindGroup} {N} (cc : UChan N)
             (j : 𝔽 (sum (B₁ ++ 0 ∷ suc c' ∷ B₂'))) →
             subst Tm (cong (_+ N) (syncs-dw10 B₁ {c'} {B₂'}))
               (canonₛ (B₁ ++ 0 ∷ suc c' ∷ B₂') cc j)
             ≡ canonₛ (B₁ ++ 1 ∷ suc c' ∷ B₂') cc (ddwk B₁ (suc c' ∷ B₂') j)
canonₛ-dwk [] {c'} {B₂'} cc j = refl
canonₛ-dwk (a ∷ []) {c'} {B₂'} {N} (e₁ , x , e₂) j
  with canonₛ-dwk ([]) {c'} {B₂'} (` 0F , suc x , wk e₂)
... | rec with Fin.splitAt a j in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum (([]) ++ 1 ∷ W)))))
  where
    W   = suc c' ∷ B₂'
    sT  = syncs (([]) ++ 0 ∷ W)
    sT′ = syncs (([]) ++ 1 ∷ W)
    sl  = syncs-dw10 ([]) {c'} {B₂'}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ 0 ∷ W) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ 1 ∷ W) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (ddwk ([]) W r)) (rec r)
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum (([]) ++ 1 ∷ W)) (ddwk ([]) W r))))
  where
    W   = suc c' ∷ B₂'
    sT  = syncs (([]) ++ 0 ∷ W)
    sT′ = syncs (([]) ++ 1 ∷ W)
    sl  = syncs-dw10 ([]) {c'} {B₂'}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ 0 ∷ W) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ 1 ∷ W) cc-r ]′
canonₛ-dwk (a ∷ d ∷ B₁″) {c'} {B₂'} {N} (e₁ , x , e₂) j
  with canonₛ-dwk (d ∷ B₁″) {c'} {B₂'} (` 0F , suc x , wk e₂)
... | rec with Fin.splitAt a j in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ 1 ∷ W)))))
  where
    W   = suc c' ∷ B₂'
    sT  = syncs ((d ∷ B₁″) ++ 0 ∷ W)
    sT′ = syncs ((d ∷ B₁″) ++ 1 ∷ W)
    sl  = syncs-dw10 (d ∷ B₁″) {c'} {B₂'}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ 0 ∷ W) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ 1 ∷ W) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (ddwk (d ∷ B₁″) W r)) (rec r)
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ 1 ∷ W)) (ddwk (d ∷ B₁″) W r))))
  where
    W   = suc c' ∷ B₂'
    sT  = syncs ((d ∷ B₁″) ++ 0 ∷ W)
    sT′ = syncs ((d ∷ B₁″) ++ 1 ∷ W)
    sl  = syncs-dw10 (d ∷ B₁″) {c'} {B₂'}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ 0 ∷ W) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ 1 ∷ W) cc-r ]′


------------------------------------------------------------------------
-- Vacuity walk: reach the drop block at list position ∣Bp∣ through the
-- BindCtx chain.  (a) last block: its front-handle session is NoRet, so
-- it is never ⟨ ret ⟩.  (b) width ≥ 2 non-last block: front ≃ ret forces
-- the ret-tipped borrow slice to Skips — contradicting the second cons.
------------------------------------------------------------------------

open T using (BindCtx; BindCtx′; last; cons-ret/acq; cons-acq; cons; nil)
open import BorrowedCF.Context using (Ctx; _⸴*_; _⸴_)
open import Data.Nat.ListAction.Properties using (sum-++)
open import BorrowedCF.Simulation.Theorems.B1VacProbe as VP
  using (NoRet; new⇒noRet; noRet-≃; ¬noRet-ret; noRet-;-snd;
         retTip-Sc-skips; noRet-front-cons; retTip-≃)
open import BorrowedCF.Simulation.Theorems.Drop
  using (head-noRet-last; ⟨⟩≃; noRet⇒≄ret; drop-handle-≃ret; fn-drop-dom)
open import BorrowedCF.Types.Equivalence using (_≃𝕊_)
import Relation.Binary.Construct.Closure.Equivalence as EqC

private
  -- Γ-navigation for one cons-ret/acq step of the walk.
  idx-step : ∀ (a : ℕ) (Bp' X : BindGroup) {Γ₁ : Ctx a} {Γ₂ : Ctx (sum (Bp' ++ X))}
             {Γ : Ctx (sum ((a ∷ Bp') ++ X))} →
             (Γ₁ ⸴* Γ₂) ≗ Γ → (k : 𝔽 (sum X)) →
             Γ (Fin.cast (sym (sum-++ (a ∷ Bp') X)) (sum (a ∷ Bp') ↑ʳ k))
             ≡ Γ₂ (Fin.cast (sym (sum-++ Bp' X)) (sum Bp' ↑ʳ k))
  idx-step a Bp' X {Γ₁} {Γ₂} {Γ} Γ≗ k =
      sym (Γ≗ idxA)
    ■ cong (Γ₁ ⸴* Γ₂) (Fin.toℕ-injective tn)
    ■ cong [ Γ₁ , Γ₂ ]′ (Fin.splitAt-↑ʳ a (sum (Bp' ++ X)) idxB)
    where
      idxA = Fin.cast (sym (sum-++ (a ∷ Bp') X)) (sum (a ∷ Bp') ↑ʳ k)
      idxB = Fin.cast (sym (sum-++ Bp' X)) (sum Bp' ↑ʳ k)
      tn : Fin.toℕ idxA ≡ Fin.toℕ (a ↑ʳ idxB)
      tn = Fin.toℕ-cast (sym (sum-++ (a ∷ Bp') X)) (sum (a ∷ Bp') ↑ʳ k)
         ■ Fin.toℕ-↑ʳ (sum (a ∷ Bp')) k
         ■ Nat.+-assoc a (sum Bp') (Fin.toℕ k)
         ■ sym ( Fin.toℕ-↑ʳ a idxB
               ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ Bp' X)) (sum Bp' ↑ʳ k)
                             ■ Fin.toℕ-↑ʳ (sum Bp') k ) )

  -- same-index bridge across the (definitionally equal) 0-block prefix.
  idx-zero : ∀ (Bp' X : BindGroup) {Γ : Ctx (sum ((0 ∷ Bp') ++ X))} → (k : 𝔽 (sum X)) →
             Γ (Fin.cast (sym (sum-++ (0 ∷ Bp') X)) (sum (0 ∷ Bp') ↑ʳ k))
             ≡ Γ (Fin.cast (sym (sum-++ Bp' X)) (sum Bp' ↑ʳ k))
  idx-zero Bp' X {Γ} k = cong Γ (Fin.toℕ-injective
    ( Fin.toℕ-cast (sym (sum-++ (0 ∷ Bp') X)) (sum (0 ∷ Bp') ↑ʳ k)
    ■ sym (Fin.toℕ-cast (sym (sum-++ Bp' X)) (sum Bp' ↑ʳ k)) ))

dropVac-last : ∀ (Bp : BindGroup) {b : ℕ} {s : 𝕊 0} {Γ : Ctx (sum (Bp ++ suc b ∷ []))} →
  NoRet s → BindCtx s (Bp ++ suc b ∷ []) Γ →
  Σ[ s'' ∈ 𝕊 0 ]
    (Γ (Fin.cast (sym (sum-++ Bp (suc b ∷ []))) (sum Bp ↑ʳ 0F)) ≡ ⟨ s'' ⟩) × NoRet s''
dropVac-last [] {b} nr bc = head-noRet-last nr bc
dropVac-last (a ∷ []) {b} nr (cons-ret/acq {Γ₁ = Γ₁} {Γ₂ = Γ₂} scra Γ≗ bc′ rest)
  with s'' , eq , nr'' ← dropVac-last []
         (VP._;_ VP.acq (VP.noRet-;-snd (noRet-≃ (EqC.symmetric _≃𝕊_ scra) nr))) rest
  = s'' , (idx-step a [] (suc b ∷ []) Γ≗ 0F ■ eq) , nr''
dropVac-last (.0 ∷ []) {b} {Γ = Γ} nr (cons-acq rest)
  with s'' , eq , nr'' ← dropVac-last [] (VP._;_ VP.acq nr) rest
  = s'' , (idx-zero [] (suc b ∷ []) {Γ = Γ} 0F ■ eq) , nr''
dropVac-last (a ∷ d ∷ Bp″) {b} nr (cons-ret/acq {Γ₁ = Γ₁} {Γ₂ = Γ₂} scra Γ≗ bc′ rest)
  with s'' , eq , nr'' ← dropVac-last (d ∷ Bp″)
         (VP._;_ VP.acq (VP.noRet-;-snd (noRet-≃ (EqC.symmetric _≃𝕊_ scra) nr))) rest
  = s'' , (idx-step a (d ∷ Bp″) (suc b ∷ []) Γ≗ 0F ■ eq) , nr''
dropVac-last (.0 ∷ d ∷ Bp″) {b} {Γ = Γ} nr (cons-acq rest)
  with s'' , eq , nr'' ← dropVac-last (d ∷ Bp″) (VP._;_ VP.acq nr) rest
  = s'' , (idx-zero (d ∷ Bp″) (suc b ∷ []) {Γ = Γ} 0F ■ eq) , nr''

dropVac-mid : ∀ (Bp : BindGroup) {b′ c : ℕ} {Bsuf : BindGroup} {s : 𝕊 0}
  {Γ : Ctx (sum (Bp ++ suc (suc b′) ∷ c ∷ Bsuf))} →
  NoRet s → BindCtx s (Bp ++ suc (suc b′) ∷ c ∷ Bsuf) Γ →
  Γ (Fin.cast (sym (sum-++ Bp (suc (suc b′) ∷ c ∷ Bsuf))) (sum Bp ↑ʳ 0F)) ≃ ⟨ ret ⟩ → ⊥
dropVac-mid [] {b′} {c} {Bsuf} nr
  (cons-ret/acq {Γ₁ = Γ₁} {Γ₂ = Γ₂} scra Γ≗
    (cons {s₁ = s1h} {s₂ = s2h} ¬sk1 s≃1 Γ≗1 (cons ¬Ss s≃2 _ _)) rest) h≃
  = ¬Ss (retTip-Sc-skips rt-borrow head≃ret)
  where
    noRet-sh = VP.noRet-;-fst (noRet-≃ (EqC.symmetric _≃𝕊_ scra) nr)
    head≃ret : s1h ≃ ret
    head≃ret = ⟨⟩≃ (≃-trans (≃-reflexive (sym (sym (Γ≗ 0F) ■ sym (Γ≗1 0F)))) h≃)
    rt-borrow = retTip-≃ (EqC.symmetric _≃𝕊_ s≃1) (noRet-front-cons noRet-sh)
dropVac-mid (a ∷ []) {b′} {c} {Bsuf} nr (cons-ret/acq scra Γ≗ bc′ rest) h≃ =
  dropVac-mid []
    (VP._;_ VP.acq (VP.noRet-;-snd (noRet-≃ (EqC.symmetric _≃𝕊_ scra) nr))) rest
    (≃-trans (≃-reflexive (sym (idx-step a [] (suc (suc b′) ∷ c ∷ Bsuf) Γ≗ 0F))) h≃)
dropVac-mid (.0 ∷ []) {b′} {c} {Bsuf} {Γ = Γ} nr (cons-acq rest) h≃ =
  dropVac-mid [] (VP._;_ VP.acq nr) rest
    (≃-trans (≃-reflexive (sym (idx-zero [] (suc (suc b′) ∷ c ∷ Bsuf) {Γ = Γ} 0F))) h≃)
dropVac-mid (a ∷ d ∷ Bp″) {b′} {c} {Bsuf} nr (cons-ret/acq scra Γ≗ bc′ rest) h≃ =
  dropVac-mid (d ∷ Bp″)
    (VP._;_ VP.acq (VP.noRet-;-snd (noRet-≃ (EqC.symmetric _≃𝕊_ scra) nr))) rest
    (≃-trans (≃-reflexive (sym (idx-step a (d ∷ Bp″) (suc (suc b′) ∷ c ∷ Bsuf) Γ≗ 0F))) h≃)
dropVac-mid (.0 ∷ d ∷ Bp″) {b′} {c} {Bsuf} {Γ = Γ} nr (cons-acq rest) h≃ =
  dropVac-mid (d ∷ Bp″) (VP._;_ VP.acq nr) rest
    (≃-trans (≃-reflexive (sym (idx-zero (d ∷ Bp″) (suc (suc b′) ∷ c ∷ Bsuf) {Γ = Γ} 0F))) h≃)

------------------------------------------------------------------------
-- toℕ characterization of R-Drop's dwk (Fin.cast ∘ ins (sum B₁) ∘ Fin.cast)
-- and its three-region navigation against the structural ddwk.
------------------------------------------------------------------------

open import Data.Nat.Base using (NonZero)
open import Data.List.Relation.Unary.All as All using (All)
open import BorrowedCF.Simulation.BlockPerm
  using (toℕ-↑*-lt; toℕ-↑*-ge; toℕ-reduce≥; toℕ-assoc-mid; toℕ-assoc-lt; toℕ-assoc-ge; toℕ-weaken*ᵣ)
open import BorrowedCF.Simulation.RsplitTransport using (toℕ-subst₂ᵣ)

toℕ-wkᵣ : ∀ {k} (v : 𝔽 k) → Fin.toℕ (weakenᵣ v) ≡ suc (Fin.toℕ v)
toℕ-wkᵣ v = refl

sum-dw : ∀ (B₁ W : BindGroup) → sum (B₁ ++ 1 ∷ W) ≡ suc (sum (B₁ ++ 0 ∷ W))
sum-dw []        W = refl
sum-dw (a ∷ B₁') W = cong (a +_) (sum-dw B₁' W) ■ Nat.+-suc a (sum (B₁' ++ 0 ∷ W))

ddwk-lo : ∀ (B₁ W : BindGroup) (j : 𝔽 (sum (B₁ ++ 0 ∷ W))) →
          Fin.toℕ j Nat.< sum B₁ → Fin.toℕ (ddwk B₁ W j) ≡ Fin.toℕ j
ddwk-lo []        W j ()
ddwk-lo (a ∷ B₁') W j lt with Fin.splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p (sum (B₁' ++ 1 ∷ W)) ■ sym jeq
  where
    jeq : Fin.toℕ j ≡ Fin.toℕ p
    jeq = cong Fin.toℕ (sym (Fin.join-splitAt a _ j) ■ cong (Fin.join a _) seq)
        ■ Fin.toℕ-↑ˡ p _
... | inj₂ r =
    Fin.toℕ-↑ʳ a (ddwk B₁' W r)
  ■ cong (a +_) (ddwk-lo B₁' W r lt′)
  ■ sym jeq
  where
    jeq : Fin.toℕ j ≡ a + Fin.toℕ r
    jeq = cong Fin.toℕ (sym (Fin.join-splitAt a _ j) ■ cong (Fin.join a _) seq)
        ■ Fin.toℕ-↑ʳ a r
    lt′ : Fin.toℕ r Nat.< sum B₁'
    lt′ = Nat.+-cancelˡ-< a _ _ (subst (Nat._< a + sum B₁') jeq lt)

ddwk-hi : ∀ (B₁ W : BindGroup) (j : 𝔽 (sum (B₁ ++ 0 ∷ W))) →
          sum B₁ Nat.≤ Fin.toℕ j → Fin.toℕ (ddwk B₁ W j) ≡ suc (Fin.toℕ j)
ddwk-hi []        W j ge = refl
ddwk-hi (a ∷ B₁') W j ge with Fin.splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<⇒≱ (Nat.<-≤-trans p< (Nat.m≤m+n a (sum B₁'))) ge)
  where
    p< : Fin.toℕ j Nat.< a
    p< = subst (Nat._< a)
           (sym (cong Fin.toℕ (sym (Fin.join-splitAt a _ j) ■ cong (Fin.join a _) seq)
                 ■ Fin.toℕ-↑ˡ p _))
           (Fin.toℕ<n p)
... | inj₂ r =
    Fin.toℕ-↑ʳ a (ddwk B₁' W r)
  ■ cong (a +_) (ddwk-hi B₁' W r ge′)
  ■ Nat.+-suc a (Fin.toℕ r)
  ■ cong suc (sym jeq)
  where
    jeq : Fin.toℕ j ≡ a + Fin.toℕ r
    jeq = cong Fin.toℕ (sym (Fin.join-splitAt a _ j) ■ cong (Fin.join a _) seq)
        ■ Fin.toℕ-↑ʳ a r
    ge′ : sum B₁' Nat.≤ Fin.toℕ r
    ge′ = Nat.+-cancelˡ-≤ a _ _ (subst (a + sum B₁' Nat.≤_) jeq ge)

-- NonZero extraction for the block after the drop block.
nonZero⇒sucℕ : ∀ {c} → NonZero c → Σ[ c' ∈ ℕ ] c ≡ suc c'
nonZero⇒sucℕ {suc c'} _ = c' , refl

allNZ-mem : ∀ (Bp : BindGroup) {w c : ℕ} {X : BindGroup} →
            All NonZero (Bp ++ w ∷ c ∷ X) → NonZero c
allNZ-mem []        (_ All.∷ hc All.∷ _) = hc
allNZ-mem (a ∷ Bp') (_ All.∷ rest)       = allNZ-mem Bp' rest

allNZ-drop1 : ∀ (Bp : BindGroup) {w c : ℕ} {X : BindGroup} →
              All NonZero (L.drop 1 (Bp ++ w ∷ c ∷ X)) → NonZero c
allNZ-drop1 []        (hc All.∷ _) = hc
allNZ-drop1 (a ∷ Bp') all          = allNZ-mem Bp' all

suc-view : ∀ {k} (f : 𝔽 (suc k)) {d : ℕ} → Fin.toℕ f ≡ suc d → Σ[ f′ ∈ 𝔽 k ] f ≡ Fin.suc f′
suc-view 0F        ()
suc-view (Fin.suc f′) eq = f′ , refl

module DwkNav (B₁ W Bg : BindGroup) {m : ℕ} where
  private
    L0 = B₁ ++ 0 ∷ W
    L1 = B₁ ++ 1 ∷ W
    dwk′ : sum L0 + sum Bg + m →ᵣ sum L1 + sum Bg + m
    dwk′ = TR.SplitRenamings.dwk B₁ W Bg {b = 0} {n = m}

  dwk-toℕ-lo : (x : 𝔽 (sum L0 + sum Bg + m)) → Fin.toℕ x Nat.< sum B₁ →
               Fin.toℕ (dwk′ x) ≡ Fin.toℕ x
  dwk-toℕ-lo x lt =
      Fin.toℕ-cast _ (TR.ins (sum B₁) (Fin.cast _ x))
    ■ toℕ-↑*-lt weakenᵣ (sum B₁) (Fin.cast _ x) (subst (Nat._< sum B₁) (sym (Fin.toℕ-cast _ x)) lt)
    ■ Fin.toℕ-cast _ x

  dwk-toℕ-hi : (x : 𝔽 (sum L0 + sum Bg + m)) → sum B₁ Nat.≤ Fin.toℕ x →
               Fin.toℕ (dwk′ x) ≡ suc (Fin.toℕ x)
  dwk-toℕ-hi x ge =
      Fin.toℕ-cast _ (TR.ins (sum B₁) (Fin.cast _ x))
    ■ toℕ-↑*-ge weakenᵣ (sum B₁) (Fin.cast _ x) ge′
    ■ cong (sum B₁ +_)
        ( toℕ-wkᵣ (Fin.reduce≥ (Fin.cast _ x) ge′)
        ■ cong suc (toℕ-reduce≥ (Fin.cast _ x) ge′ ■ cong (Nat._∸ sum B₁) (Fin.toℕ-cast _ x)) )
    ■ Nat.+-suc (sum B₁) (Fin.toℕ x Nat.∸ sum B₁)
    ■ cong suc (Nat.m+[n∸m]≡n ge)
    where
      ge′ : sum B₁ Nat.≤ Fin.toℕ (Fin.cast _ x)
      ge′ = subst (sum B₁ Nat.≤_) (sym (Fin.toℕ-cast _ x)) ge


  dwk-r1 : (g1 : 𝔽 (sum L0)) →
           dwk′ ((g1 ↑ˡ sum Bg) ↑ˡ m) ≡ ((ddwk B₁ W g1 ↑ˡ sum Bg) ↑ˡ m)
  dwk-r1 g1 with Fin.toℕ g1 Nat.<? sum B₁
  ... | yes lt = Fin.toℕ-injective
      ( dwk-toℕ-lo _ (subst (Nat._< sum B₁) (sym emb) lt)
      ■ emb
      ■ sym (ddwk-lo B₁ W g1 lt)
      ■ sym embR )
    where
      emb  = Fin.toℕ-↑ˡ (g1 ↑ˡ sum Bg) m ■ Fin.toℕ-↑ˡ g1 (sum Bg)
      embR = Fin.toℕ-↑ˡ (ddwk B₁ W g1 ↑ˡ sum Bg) m ■ Fin.toℕ-↑ˡ (ddwk B₁ W g1) (sum Bg)
  ... | no ¬lt = Fin.toℕ-injective
      ( dwk-toℕ-hi _ (subst (sum B₁ Nat.≤_) (sym emb) (Nat.≮⇒≥ ¬lt))
      ■ cong suc emb
      ■ sym (ddwk-hi B₁ W g1 (Nat.≮⇒≥ ¬lt))
      ■ sym embR )
    where
      emb  = Fin.toℕ-↑ˡ (g1 ↑ˡ sum Bg) m ■ Fin.toℕ-↑ˡ g1 (sum Bg)
      embR = Fin.toℕ-↑ˡ (ddwk B₁ W g1 ↑ˡ sum Bg) m ■ Fin.toℕ-↑ˡ (ddwk B₁ W g1) (sum Bg)

  dwk-r2 : (g2 : 𝔽 (sum Bg)) →
           dwk′ ((sum L0 ↑ʳ g2) ↑ˡ m) ≡ ((sum L1 ↑ʳ g2) ↑ˡ m)
  dwk-r2 g2 = Fin.toℕ-injective
      ( dwk-toℕ-hi _ geE
      ■ cong suc emb
      ■ sym embR )
    where
      emb : Fin.toℕ ((sum L0 ↑ʳ g2) ↑ˡ m) ≡ sum L0 + Fin.toℕ g2
      emb = Fin.toℕ-↑ˡ (sum L0 ↑ʳ g2) m ■ Fin.toℕ-↑ʳ (sum L0) g2
      geB : sum B₁ Nat.≤ sum L0
      geB = subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ (0 ∷ W))) (Nat.m≤m+n (sum B₁) (sum (0 ∷ W)))
      geE : sum B₁ Nat.≤ Fin.toℕ ((sum L0 ↑ʳ g2) ↑ˡ m)
      geE = subst (sum B₁ Nat.≤_) (sym emb) (Nat.≤-trans geB (Nat.m≤m+n (sum L0) (Fin.toℕ g2)))
      embR : Fin.toℕ ((sum L1 ↑ʳ g2) ↑ˡ m) ≡ suc (sum L0 + Fin.toℕ g2)
      embR = Fin.toℕ-↑ˡ (sum L1 ↑ʳ g2) m ■ Fin.toℕ-↑ʳ (sum L1) g2
           ■ cong (_+ Fin.toℕ g2) (sum-dw B₁ W)

  dwk-tail : (u : 𝔽 m) →
             dwk′ ((sum L0 + sum Bg) ↑ʳ u) ≡ ((sum L1 + sum Bg) ↑ʳ u)
  dwk-tail u = Fin.toℕ-injective
      ( dwk-toℕ-hi _ geE
      ■ cong suc emb
      ■ sym embR )
    where
      emb : Fin.toℕ ((sum L0 + sum Bg) ↑ʳ u) ≡ (sum L0 + sum Bg) + Fin.toℕ u
      emb = Fin.toℕ-↑ʳ (sum L0 + sum Bg) u
      geB : sum B₁ Nat.≤ sum L0 + sum Bg
      geB = Nat.≤-trans (subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ (0 ∷ W))) (Nat.m≤m+n (sum B₁) (sum (0 ∷ W)))) (Nat.m≤m+n (sum L0) (sum Bg))
      geE : sum B₁ Nat.≤ Fin.toℕ ((sum L0 + sum Bg) ↑ʳ u)
      geE = subst (sum B₁ Nat.≤_) (sym emb) (Nat.≤-trans geB (Nat.m≤m+n (sum L0 + sum Bg) (Fin.toℕ u)))
      embR : Fin.toℕ ((sum L1 + sum Bg) ↑ʳ u) ≡ suc ((sum L0 + sum Bg) + Fin.toℕ u)
      embR = Fin.toℕ-↑ʳ (sum L1 + sum Bg) u
           ■ cong (λ z → z + sum Bg + Fin.toℕ u) (sum-dw B₁ W)

------------------------------------------------------------------------
-- leafσ agreement across the dropped handle: the full-scope dwk image of
-- every RHS index carries the SAME leaf entry (up to the width-blind
-- syncs transport).
------------------------------------------------------------------------

module LeafDwk {m n : ℕ} (σ : m →ₛ n) (B₁ : BindGroup) (c' : ℕ) (B₂' Bg : BindGroup) where
  W : BindGroup
  W  = suc c' ∷ B₂'
  L0 : BindGroup
  L0 = B₁ ++ 0 ∷ W
  L1 : BindGroup
  L1 = B₁ ++ 1 ∷ W
  dwk′ : sum L0 + sum Bg + m →ᵣ sum L1 + sum Bg + m
  dwk′ = TR.SplitRenamings.dwk B₁ W Bg {b = 0} {n = m}
  EQs : syncs L0 ≡ syncs L1
  EQs = syncs-dw10 B₁ {c'} {B₂'}
  EQL : syncs Bg + (syncs L0 + (2 + n)) ≡ syncs Bg + (syncs L1 + (2 + n))
  EQL = cong (λ z → syncs Bg + (z + (2 + n))) EQs

  ccg : UChan (2 + n)
  ccg = (K `unit , 0F , K `unit)

  inner0 : sum L0 + sum Bg →ₛ syncs Bg + (syncs L0 + (2 + n))
  inner0 = (λ j → canonₛ L0 ccg j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
           ++ₛ canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs L0) 1F , K `unit)
  tail0 : m →ₛ syncs Bg + (syncs L0 + (2 + n))
  tail0 = λ u → σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs L0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
  inner1 : sum L1 + sum Bg →ₛ syncs Bg + (syncs L1 + (2 + n))
  inner1 = (λ j → canonₛ L1 ccg j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
           ++ₛ canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs L1) 1F , K `unit)
  tail1 : m →ₛ syncs Bg + (syncs L1 + (2 + n))
  tail1 = λ u → σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs L1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)

  leafσ0-def : (i : 𝔽 (sum L0 + sum Bg + m)) →
               leafσ σ L0 Bg i ≡ [ inner0 , tail0 ]′ (Fin.splitAt (sum L0 + sum Bg) i)
  leafσ0-def i = refl
  leafσ1-def : (i : 𝔽 (sum L1 + sum Bg + m)) →
               leafσ σ L1 Bg i ≡ [ inner1 , tail1 ]′ (Fin.splitAt (sum L1 + sum Bg) i)
  leafσ1-def i = refl

  leaf-dwk : (i : 𝔽 (sum L0 + sum Bg + m)) →
             leafσ σ L1 Bg (dwk′ i) ≡ subst Tm EQL (leafσ σ L0 Bg i)
  leaf-dwk i with Fin.splitAt (sum L0 + sum Bg) i in seqO
  ... | inj₂ u =
        cong (leafσ σ L1 Bg) (cong dwk′ ieq ■ DwkNav.dwk-tail B₁ W Bg u)
      ■ cong [ inner1 , tail1 ]′ (Fin.splitAt-↑ʳ (sum L1 + sum Bg) m u)
      ■ tailCoh EQs (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2)
    where
      ieq : i ≡ (sum L0 + sum Bg) ↑ʳ u
      ieq = sym (Fin.join-splitAt (sum L0 + sum Bg) m i) ■ cong (Fin.join (sum L0 + sum Bg) m) seqO
      tailCoh : ∀ {s0 s1} (e : s0 ≡ s1) (t : Tm (2 + n)) →
                t ⋯ weaken* ⦃ Kᵣ ⦄ s1 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
                ≡ subst Tm (cong (λ z → syncs Bg + (z + (2 + n))) e)
                    (t ⋯ weaken* ⦃ Kᵣ ⦄ s0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
      tailCoh refl t = refl
  ... | inj₁ d with Fin.splitAt (sum L0) d in seqI
  ...   | inj₂ g2 =
        cong (leafσ σ L1 Bg) (cong dwk′ ieq ■ DwkNav.dwk-r2 B₁ W Bg g2)
      ■ cong [ inner1 , tail1 ]′ (Fin.splitAt-↑ˡ (sum L1 + sum Bg) (sum L1 ↑ʳ g2) m)
      ■ cong [ (λ j → canonₛ L1 ccg j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
             , canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs L1) 1F , K `unit) ]′
             (Fin.splitAt-↑ʳ (sum L1) (sum Bg) g2)
      ■ midCoh EQs g2
    where
      ieq : i ≡ ((sum L0 ↑ʳ g2) ↑ˡ m)
      ieq = sym (Fin.join-splitAt (sum L0 + sum Bg) m i)
          ■ cong (Fin.join (sum L0 + sum Bg) m) seqO
          ■ cong (_↑ˡ m)
              ( sym (Fin.join-splitAt (sum L0) (sum Bg) d)
              ■ cong (Fin.join (sum L0) (sum Bg)) seqI )
      midCoh : ∀ {s0 s1} (e : s0 ≡ s1) (g : 𝔽 (sum Bg)) →
               canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ s1 1F , K `unit) g
               ≡ subst Tm (cong (λ z → syncs Bg + (z + (2 + n))) e)
                   (canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ s0 1F , K `unit) g)
      midCoh refl g = refl
  ...   | inj₁ g1 =
        cong (leafσ σ L1 Bg) (cong dwk′ ieq ■ DwkNav.dwk-r1 B₁ W Bg g1)
      ■ cong [ inner1 , tail1 ]′ (Fin.splitAt-↑ˡ (sum L1 + sum Bg) (ddwk B₁ W g1 ↑ˡ sum Bg) m)
      ■ cong [ (λ j → canonₛ L1 ccg j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
             , canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs L1) 1F , K `unit) ]′
             (Fin.splitAt-↑ˡ (sum L1) (ddwk B₁ W g1) (sum Bg))
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (sym (canonₛ-dwk B₁ {c'} {B₂'} ccg g1))
      ■ r1Coh EQs (canonₛ L0 ccg g1)
    where
      ieq : i ≡ ((g1 ↑ˡ sum Bg) ↑ˡ m)
      ieq = sym (Fin.join-splitAt (sum L0 + sum Bg) m i)
          ■ cong (Fin.join (sum L0 + sum Bg) m) seqO
          ■ cong (_↑ˡ m)
              ( sym (Fin.join-splitAt (sum L0) (sum Bg) d)
              ■ cong (Fin.join (sum L0) (sum Bg)) seqI )
      r1Coh : ∀ {s0 s1} (e : s0 ≡ s1) (t0 : Tm (s0 + (2 + n))) →
              subst Tm (cong (_+ (2 + n)) e) t0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
              ≡ subst Tm (cong (λ z → syncs Bg + (z + (2 + n))) e)
                  (t0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))
      r1Coh refl t0 = refl

  ------------------------------------------------------------------------
  -- Handle characterization: the dropped handle's leaf triple, pushed
  -- through the slide chain, is  (e ⊗ ` suc x̂) ⊗ ` 0F  — RU-Drop's shape.
  ------------------------------------------------------------------------

  LW : BindGroup
  LW = B₁ ++ W
  sD : ℕ
  sD = syncs W
  sBg : ℕ
  sBg = syncs Bg

  EQ1 : syncs L1 + (2 + n) ≡ syncs LW + suc (2 + n)
  EQ1 = cong (_+ (2 + n)) (syncs-insW 1 B₁ {c'} {B₂'}) ■ sym (+-suc (syncs LW) (2 + n))
  EQ0 : syncs L0 + (2 + n) ≡ syncs LW + suc (2 + n)
  EQ0 = cong (_+ (2 + n)) (syncs-insW 0 B₁ {c'} {B₂'}) ■ sym (+-suc (syncs LW) (2 + n))

  ρ₁ : (sBg + (syncs LW + suc (2 + n))) →ᵣ (sBg + suc (syncs LW + (2 + n)))
  ρ₁ = sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n} ↑* sBg
  ρ₂ : (sBg + suc (syncs LW + (2 + n))) →ᵣ suc (sBg + (syncs LW + (2 + n)))
  ρ₂ = assocSwapᵣ sBg 1 {syncs LW + (2 + n)}

  g1h : 𝔽 (sum L1)
  g1h = Fin.cast (sym (sum-++ B₁ (1 ∷ W))) (sum B₁ ↑ʳ ((Fin.zero {n = 0}) ↑ˡ sum W))
  atk0 : 𝔽 (sum L1 + sum Bg + m)
  atk0 = TR.SplitRenamings.atk B₁ W Bg {w = 1} {n = m} (Fin.zero {n = 0})

  private
    hq = canonₛ-handleq B₁ {N = 2 + n} (K `unit) 0F (K `unit) 0 0 W
    hRv = handle-R0-varq B₁ {N = 2 + n} (K `unit) 0F (K `unit) 0 c' B₂'
    hA = proj₁ hq
    hJ = proj₁ (proj₂ (proj₂ hq))
    hV = proj₁ hRv

    leafσ-atk0 : leafσ σ L1 Bg atk0 ≡ canonₛ L1 ccg g1h ⋯ weaken* ⦃ Kᵣ ⦄ sBg
    leafσ-atk0 =
        cong [ inner1 , tail1 ]′ (Fin.splitAt-↑ˡ (sum L1 + sum Bg) (g1h ↑ˡ sum Bg) m)
      ■ cong [ (λ j → canonₛ L1 ccg j ⋯ weaken* ⦃ Kᵣ ⦄ sBg)
             , canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs L1) 1F , K `unit) ]′
             (Fin.splitAt-↑ˡ (sum L1) g1h (sum Bg))

    triple-eq : canonₛ L1 ccg g1h ≡ (hA ⊗ (` hJ)) ⊗ (` hV)
    triple-eq = proj₁ (proj₂ (proj₂ (proj₂ hq)))
              ■ cong (λ z → (hA ⊗ (` hJ)) ⊗ z) (proj₁ (proj₂ hRv))

    hJℕ : Fin.toℕ hJ ≡ syncs L1 + 0
    hJℕ = proj₂ (proj₂ (proj₂ (proj₂ hq)))
    hVℕ : Fin.toℕ hV ≡ sD
    hVℕ = proj₂ (proj₂ hRv)

    subst-⊗L : ∀ {a b} (eq : a ≡ b) (p r : Tm a) →
               subst Tm eq (p ⊗ r) ≡ subst Tm eq p ⊗ subst Tm eq r
    subst-⊗L refl p r = refl
    subst-`L : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
    subst-`L refl q = refl

    -- the chained variable-image map on leaf variables.
    chainV : 𝔽 (sBg + (syncs L1 + (2 + n))) → 𝔽 (suc (sBg + (syncs LW + (2 + n))))
    chainV k = ρ₂ (ρ₁ (subst 𝔽 (cong (sBg +_) EQ1) k))

    -- generic toℕ of the chain on inputs ≥ sBg whose reduced part is t.
    chain-ge : (k : 𝔽 (sBg + (syncs L1 + (2 + n)))) (t : ℕ) →
               Fin.toℕ k ≡ sBg + t → sD + 1 Nat.≤ t →
               Fin.toℕ (chainV k) ≡ sBg + t
    chain-ge k t kℕ tge = body
      where
        sk = subst 𝔽 (cong (sBg +_) EQ1) k
        skℕ : Fin.toℕ sk ≡ sBg + t
        skℕ = toℕ-substᶠ (cong (sBg +_) EQ1) k ■ kℕ
        ge₁ : sBg Nat.≤ Fin.toℕ sk
        ge₁ = subst (sBg Nat.≤_) (sym skℕ) (Nat.m≤m+n sBg t)
        red = Fin.reduce≥ sk ge₁
        redℕ : Fin.toℕ red ≡ t
        redℕ = toℕ-reduce≥ sk ge₁ ■ cong (Nat._∸ sBg) skℕ ■ Nat.m+n∸m≡n sBg t
        sw-in = subst 𝔽 (sym (sym (sw-dom B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}))) red
        sw-inℕ : Fin.toℕ sw-in ≡ t
        sw-inℕ = toℕ-substᶠ _ red ■ redℕ
        ge₂ : sD + 1 Nat.≤ Fin.toℕ sw-in
        ge₂ = subst (sD + 1 Nat.≤_) (sym sw-inℕ) tge
        swℕ : Fin.toℕ (sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n} red) ≡ t
        swℕ = toℕ-subst₂ᵣ (sym (sw-dom B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}))
                          (sw-cod B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n})
                          (assocSwapᵣ sD 1 {L.length B₁ + (2 + n)}) red
            ■ toℕ-assoc-ge sD 1 sw-in ge₂
            ■ sw-inℕ
        ρ₁ℕ : Fin.toℕ (ρ₁ sk) ≡ sBg + t
        ρ₁ℕ = toℕ-↑*-ge (sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}) sBg sk ge₁
            ■ cong (sBg +_) (cong Fin.toℕ (cong (sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}) refl) ■ swℕ)
        ge₃ : sBg + 1 Nat.≤ Fin.toℕ (ρ₁ sk)
        ge₃ = subst (sBg + 1 Nat.≤_) (sym ρ₁ℕ)
                (Nat.+-monoʳ-≤ sBg (Nat.≤-trans (Nat.m≤n+m 1 sD) tge))
        body : Fin.toℕ (chainV k) ≡ sBg + t
        body = toℕ-assoc-ge sBg 1 (ρ₁ sk) ge₃ ■ ρ₁ℕ

    -- the chain sends the cell variable (reduced part = sD) to 0F.
    chain-cell : (k : 𝔽 (sBg + (syncs L1 + (2 + n)))) →
                 Fin.toℕ k ≡ sBg + sD → Fin.toℕ (chainV k) ≡ 0
    chain-cell k kℕ = body
      where
        sk = subst 𝔽 (cong (sBg +_) EQ1) k
        skℕ : Fin.toℕ sk ≡ sBg + sD
        skℕ = toℕ-substᶠ (cong (sBg +_) EQ1) k ■ kℕ
        ge₁ : sBg Nat.≤ Fin.toℕ sk
        ge₁ = subst (sBg Nat.≤_) (sym skℕ) (Nat.m≤m+n sBg sD)
        red = Fin.reduce≥ sk ge₁
        redℕ : Fin.toℕ red ≡ sD
        redℕ = toℕ-reduce≥ sk ge₁ ■ cong (Nat._∸ sBg) skℕ ■ Nat.m+n∸m≡n sBg sD
        sw-in = subst 𝔽 (sym (sym (sw-dom B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}))) red
        sw-inℕ : Fin.toℕ sw-in ≡ sD
        sw-inℕ = toℕ-substᶠ _ red ■ redℕ
        swℕ : Fin.toℕ (sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n} red) ≡ 0
        swℕ = toℕ-subst₂ᵣ (sym (sw-dom B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}))
                          (sw-cod B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n})
                          (assocSwapᵣ sD 1 {L.length B₁ + (2 + n)}) red
            ■ toℕ-assoc-mid sD 1 sw-in
                (subst (sD Nat.≤_) (sym sw-inℕ) Nat.≤-refl)
                (subst (Nat._< sD + 1) (sym sw-inℕ)
                  (subst (sD Nat.<_) (Nat.+-comm 1 sD) Nat.≤-refl))
            ■ cong (Nat._∸ sD) sw-inℕ
            ■ Nat.n∸n≡0 sD
        ρ₁ℕ : Fin.toℕ (ρ₁ sk) ≡ sBg + 0
        ρ₁ℕ = toℕ-↑*-ge (sw-cast B₁ {b₁ = c'} {B₂ = B₂'} {a = 2 + n}) sBg sk ge₁
            ■ cong (sBg +_) swℕ
        body : Fin.toℕ (chainV k) ≡ 0
        body = toℕ-assoc-mid sBg 1 (ρ₁ sk)
                 (subst (sBg Nat.≤_) (sym ρ₁ℕ) (Nat.≤-reflexive (sym (Nat.+-identityʳ sBg))))
                 (subst (Nat._< sBg + 1) (sym ρ₁ℕ)
                   (subst (Nat._< sBg + 1) (sym (Nat.+-identityʳ sBg))
                     (subst (sBg Nat.<_) (Nat.+-comm 1 sBg) Nat.≤-refl)))
             ■ cong (Nat._∸ sBg) ρ₁ℕ
             ■ cong (Nat._∸ sBg) (Nat.+-identityʳ sBg)
             ■ Nat.n∸n≡0 sBg

  handleθ : Σ[ e ∈ Tm (suc (sBg + (syncs LW + (2 + n)))) ]
            Σ[ x̂ ∈ 𝔽 (sBg + (syncs LW + (2 + n))) ]
            (subst Tm (cong (sBg +_) EQ1) (leafσ σ L1 Bg atk0) ⋯ ρ₁ ⋯ ρ₂
             ≡ ((e ⊗ (` Fin.suc x̂)) ⊗ (` 0F)))
  handleθ = eH , x̂ , eqn
    where
      wj = weaken* ⦃ Kᵣ ⦄ sBg hJ
      wv = weaken* ⦃ Kᵣ ⦄ sBg hV
      sj = subst 𝔽 (cong (sBg +_) EQ1) wj
      sv = subst 𝔽 (cong (sBg +_) EQ1) wv
      eH = subst Tm (cong (sBg +_) EQ1) (hA ⋯ weaken* ⦃ Kᵣ ⦄ sBg) ⋯ ρ₁ ⋯ ρ₂
      wjℕ : Fin.toℕ wj ≡ sBg + (syncs L1 + 0)
      wjℕ = toℕ-weaken*ᵣ sBg hJ ■ cong (sBg +_) hJℕ
      midT : ℕ
      midT = syncs L1 + 0
      midge : sD + 1 Nat.≤ midT
      midge = Nat.≤-trans
                (Nat.≤-reflexive (Nat.+-comm sD 1))
                (Nat.≤-trans (Nat.+-monoʳ-≤ 1 Nat.≤-refl)
                  (subst (suc sD Nat.≤_)
                    (sym (cong (_+ 0) (syncs-split-gen B₁ 1 W)))
                    (Nat.≤-trans (Nat.m≤n+m (suc sD) (L.length B₁))
                      (Nat.m≤m+n (L.length B₁ + suc sD) 0))))
      midℕ : Fin.toℕ (chainV wj) ≡ sBg + midT
      midℕ = chain-ge wj midT wjℕ midge
      sucd : Σ[ d ∈ ℕ ] sBg + midT ≡ suc d
      sucd = sBg + (L.length B₁ + sD + 0)
           , ( cong (sBg +_) (cong (_+ 0) (syncs-split-gen B₁ 1 W))
             ■ cong (sBg +_) (cong (_+ 0) (Nat.+-suc (L.length B₁) sD))
             ■ Nat.+-suc sBg (L.length B₁ + sD + 0) )
      x̂view = suc-view (chainV wj) {proj₁ sucd} (midℕ ■ proj₂ sucd)
      x̂ = proj₁ x̂view
      wvℕ : Fin.toℕ wv ≡ sBg + sD
      wvℕ = toℕ-weaken*ᵣ sBg hV ■ cong (sBg +_) hVℕ
      lastEq : chainV wv ≡ 0F
      lastEq = Fin.toℕ-injective (chain-cell wv wvℕ)
      eqn : subst Tm (cong (sBg +_) EQ1) (leafσ σ L1 Bg atk0) ⋯ ρ₁ ⋯ ρ₂
            ≡ ((eH ⊗ (` Fin.suc x̂)) ⊗ (` 0F))
      eqn =
          cong (λ z → subst Tm (cong (sBg +_) EQ1) z ⋯ ρ₁ ⋯ ρ₂)
            ( leafσ-atk0
            ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sBg) triple-eq )
        ■ cong (λ z → z ⋯ ρ₁ ⋯ ρ₂)
            ( subst-⊗L (cong (sBg +_) EQ1) ((hA ⊗ (` hJ)) ⋯ weaken* ⦃ Kᵣ ⦄ sBg) ((` hV) ⋯ weaken* ⦃ Kᵣ ⦄ sBg)
            ■ cong₂ _⊗_
                ( subst-⊗L (cong (sBg +_) EQ1) (hA ⋯ weaken* ⦃ Kᵣ ⦄ sBg) ((` hJ) ⋯ weaken* ⦃ Kᵣ ⦄ sBg)
                ■ cong (subst Tm (cong (sBg +_) EQ1) (hA ⋯ weaken* ⦃ Kᵣ ⦄ sBg) ⊗_)
                    (subst-`L (cong (sBg +_) EQ1) wj) )
                (subst-`L (cong (sBg +_) EQ1) wv) )
        ■ cong₂ _⊗_
            (cong₂ _⊗_ refl (cong `_ (proj₂ x̂view)))
            (cong `_ lastEq)
