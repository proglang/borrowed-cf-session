module BorrowedCF.Simulation3.Support.Theorems.SplitsRQ2 where

-- | q-generalized φ-side rsplit helpers: the sync-level (φ) reconciliation for
--   the interior remote split at block position q.  Ports the position-0
--   helpers of SplitsH3 (handle-L-rwk / handle-R-rwk / sw-* / Brwk-slide /
--   leafσ-rwk-id) to general q, threading the q-data-renaming drwkq and the
--   q-sync-insertion sinsq from SplitsRQ.

open import BorrowedCF.Simulation3.Support.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Terms using (module SplitRenamings)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import BorrowedCF.Processes.Bisim using (syncs)
open import Data.List.Properties using (++-assoc)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Simulation3.Support.BlockPerm
  using ( toℕ-weaken*ᵣ; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt )
open import BorrowedCF.Simulation3.Support.TranslationProperties
  using (Ub-nat)
  renaming ( subst-⋯-cod to subst-⋯-cod-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation3.Support.RsplitTransport
  using (⋯-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)

open import BorrowedCF.Simulation3.Support.Theorems.SplitsRQ public
open import BorrowedCF.Simulation3.Support.Theorems.SplitsH2
  using (Ub-R-last; Ub-R-far; Ub-L-pos0; Ub-L-pos>0; Ub-L-*)

-- ============================================================================
--   syncs-split-genq : syncs of a q-block append splits as its length prefix
--   plus the leaf-block sync count, independent of the head width.
-- ============================================================================
syncs-split-genq : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) →
                   syncs (B₁ ++ (q + suc b₁) ∷ B₂) ≡ L.length B₁ + syncs (suc b₁ ∷ B₂)
syncs-split-genq B₁ q b₁ B₂ =
    syncs-split-gen B₁ (q + suc b₁) B₂
  ■ cong (L.length B₁ +_) (syncs-head-irrel (q + suc b₁) (suc b₁) B₂)

-- ============================================================================
--   sw-domq / sw-codq / sw-castq : q-generalized leaf-swap coercions (the fresh
--   φ-drop binder sliding to the leaf).  syncs is head-agnostic, so the shape
--   is exactly sw-* with syncs-split-genq for syncs-split.
-- ============================================================================
sw-domq : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
          syncs (B₁ ++ (q + suc b₁) ∷ B₂) + suc a ≡ syncs ((q + suc b₁) ∷ B₂) + (1 + (L.length B₁ + a))
sw-domq B₁ {q} {b₁} {B₂} {a} =
    cong (_+ suc a) (syncs-split-gen B₁ (q + suc b₁) B₂)
  ■ +-suc (L.length B₁ + syncs ((q + suc b₁) ∷ B₂)) a
  ■ cong suc (+-assoc (L.length B₁) (syncs ((q + suc b₁) ∷ B₂)) a ■ comm3 (L.length B₁) (syncs ((q + suc b₁) ∷ B₂)) a)
  ■ sym (+-suc (syncs ((q + suc b₁) ∷ B₂)) (L.length B₁ + a))

sw-codq : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
          1 + (syncs ((q + suc b₁) ∷ B₂) + (L.length B₁ + a)) ≡ suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + a)
sw-codq B₁ {q} {b₁} {B₂} {a} =
  cong suc (comm3 (syncs ((q + suc b₁) ∷ B₂)) (L.length B₁) a
           ■ sym (+-assoc (L.length B₁) (syncs ((q + suc b₁) ∷ B₂)) a)
           ■ cong (_+ a) (sym (syncs-split-gen B₁ (q + suc b₁) B₂)))

sw-castq : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
           (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + suc a) →ᵣ suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + a)
sw-castq B₁ {q} {b₁} {B₂} {a} =
  subst₂ _→ᵣ_ (sym (sw-domq B₁ {q} {b₁} {B₂} {a})) (sw-codq B₁ {q} {b₁} {B₂} {a})
    (assocSwapᵣ (syncs ((q + suc b₁) ∷ B₂)) 1 {L.length B₁ + a})

-- ============================================================================
--   Brwk-slideq : the inserted φ-drop (from splitting block (q+suc b₁) →
--   (q+1) ∷ suc b₁) descends to the leaf.  Same route as Brwk-slide, with the
--   head flag ϕ[q+1] converted to drop and the q-sync coercions.
-- ============================================================================
Brwk-slideq : ∀ (B₁ : BindGroup) {q b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
              (Z : U.Proc (syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + a)) →
              Bφ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) Z
              U.≋ Bφ (B₁ ++ (q + suc b₁) ∷ B₂)
                    (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwkq B₁ q) ■ sym (+-suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) a)) Z
                                  U.⋯ₚ sw-castq B₁ {q} {b₁} {B₂} {a}))
Bφ-hd : ∀ (b₁ q : ℕ) (B₂ : BindGroup) {a}
        (Y : U.Proc (syncs (suc b₁ ∷ B₂) + a)) →
        Bφ (suc b₁ ∷ B₂) Y
        ≡ Bφ ((q + suc b₁) ∷ B₂) (subst (λ z → U.Proc (z + a)) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂) Y)
Bφ-hd b₁ q []       Y = refl
Bφ-hd b₁ q (c ∷ D) {a} Y =
  cong (λ f → U.φ f (Bφ (c ∷ D) (subst U.Proc (sym (+-suc (syncs (c ∷ D)) a)) Y)))
       (sym (ϕqsb-drop q b₁))

subst-φ-out : ∀ {p q A} (e : p ≡ q) (z : U.Flag) (Y : U.Proc (suc p + A)) →
              subst (λ w → U.Proc (w + A)) e (U.φ z Y)
              ≡ U.φ z (subst (λ w → U.Proc (suc w + A)) e Y)
subst-φ-out refl z Y = refl

swap-hd : ∀ {sD sDq A} (e : sD ≡ sDq) (Y : U.Proc (sD + suc A)) →
          subst (λ z → U.Proc (suc (z + A))) e (Y U.⋯ₚ assocSwapᵣ sD 1 {A})
          ≡ (subst (λ z → U.Proc (z + suc A)) e Y) U.⋯ₚ assocSwapᵣ sDq 1 {A}
swap-hd refl Y = refl

subst-cong+U : ∀ {K a b} (e : a ≡ b) (t : U.Proc (a + K)) →
               subst (λ z → U.Proc (z + K)) e t ≡ subst U.Proc (cong (_+ K) e) t
subst-cong+U refl t = refl

Brwk-slideq B₁ {q} {b₁} {B₂} {a} Z =
     ≡→≋ (Bφ-peel B₁ (q + 1) (suc b₁ ∷ B₂) {a} Z)
  ◅◅ Pfx-cong B₁ (≡→≋ flagconv)
  ◅◅ Pfx-cong B₁ (φ-past-Bφ (suc b₁ ∷ B₂) U.drop {L.length B₁ + a} bodyW)
  ◅◅ Pfx-cong B₁ (≡→≋ (Bφ-hd b₁ q B₂ (U.φ U.drop (bodyW U.⋯ₚ assocSwapᵣ sD 1 {L.length B₁ + a}))))
  ◅◅ ≡→≋
       ( cong (Pfx B₁) (cong (Bφ ((q + suc b₁) ∷ B₂)) reconcile)
       ■ sym (Bφ-peel B₁ (q + suc b₁) B₂ {a}
                (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwkq B₁ q) ■ sym (+-suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) a)) Z
                              U.⋯ₚ sw-castq B₁ {q} {b₁} {B₂} {a}))) )
  where
    sD  = syncs (suc b₁ ∷ B₂)
    sDq = syncs ((q + suc b₁) ∷ B₂)
    W0 : U.Proc (syncs ((q + 1) ∷ suc b₁ ∷ B₂) + (L.length B₁ + a))
    W0 = subst U.Proc (peel-eq B₁ (q + 1) (suc b₁ ∷ B₂) {a}) Z
    bodyW : U.Proc (sD + suc (L.length B₁ + a))
    bodyW = subst U.Proc (sym (+-suc sD (L.length B₁ + a))) W0
    flagconv : Bφ ((q + 1) ∷ suc b₁ ∷ B₂) W0 ≡ U.φ U.drop (Bφ (suc b₁ ∷ B₂) bodyW)
    flagconv = cong (λ f → U.φ f (Bφ (suc b₁ ∷ B₂) bodyW)) (ϕq1-drop q)
    raw : (sD + (1 + (L.length B₁ + a))) →ᵣ (1 + (sD + (L.length B₁ + a)))
    raw = assocSwapᵣ sD 1 {L.length B₁ + a}
    -- the head-irrel transport of the pushed φ-drop body.
    hiᵤ : U.Proc (sDq + (L.length B₁ + a))
    hiᵤ = subst (λ z → U.Proc (z + (L.length B₁ + a))) (syncs-head-irrel (suc b₁) (q + suc b₁) B₂)
            (U.φ U.drop (bodyW U.⋯ₚ raw))
    A = L.length B₁ + a
    HI = syncs-head-irrel (suc b₁) (q + suc b₁) B₂
    raw′ : (sDq + (1 + A)) →ᵣ (1 + (sDq + A))
    raw′ = assocSwapᵣ sDq 1 {A}
    EQ : syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + a ≡ syncs (B₁ ++ (q + suc b₁) ∷ B₂) + suc a
    EQ = cong (_+ a) (syncs-rwkq B₁ q) ■ sym (+-suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) a)
    TARGETbody : U.Proc (suc (syncs (B₁ ++ (q + suc b₁) ∷ B₂) + a))
    TARGETbody = subst U.Proc EQ Z U.⋯ₚ sw-castq B₁ {q} {b₁} {B₂} {a}
    bodyW-hd : subst (λ z → U.Proc (z + suc A)) HI bodyW ≡ subst U.Proc (EQ ■ sw-domq B₁ {q} {b₁} {B₂} {a}) Z
    bodyW-hd =
        subst-cong+U HI bodyW
      ■ cong (subst U.Proc (cong (_+ suc A) HI))
          (ss-U (peel-eq B₁ (q + 1) (suc b₁ ∷ B₂) {a}) (sym (+-suc sD A)) {t = Z})
      ■ ss-U (peel-eq B₁ (q + 1) (suc b₁ ∷ B₂) {a} ■ sym (+-suc sD A)) (cong (_+ suc A) HI) {t = Z}
      ■ cong (λ e → subst U.Proc e Z) (uipℕ _ (EQ ■ sw-domq B₁ {q} {b₁} {B₂} {a}))
    rhs≡ : subst U.Proc EQ Z U.⋯ₚ sw-castq B₁ {q} {b₁} {B₂} {a}
           ≡ subst U.Proc (sw-codq B₁ {q} {b₁} {B₂} {a})
               (subst U.Proc (EQ ■ sw-domq B₁ {q} {b₁} {B₂} {a}) Z U.⋯ₚ raw′)
    rhs≡ = cast-⋯2 (sw-domq B₁ {q} {b₁} {B₂} {a}) (sw-codq B₁ {q} {b₁} {B₂} {a}) (subst U.Proc EQ Z) raw′
         ■ cong (λ w → subst U.Proc (sw-codq B₁ {q} {b₁} {B₂} {a}) (w U.⋯ₚ raw′))
             (ss-U EQ (sw-domq B₁ {q} {b₁} {B₂} {a}) {t = Z})
    reconcileBody : subst (λ z → U.Proc (suc (z + A))) HI (bodyW U.⋯ₚ raw)
                    ≡ subst U.Proc (cong suc (peel-eq B₁ (q + suc b₁) B₂ {a})) TARGETbody
    reconcileBody =
        swap-hd HI bodyW
      ■ cong (U._⋯ₚ raw′) bodyW-hd
      ■ sym ( cong (subst U.Proc (cong suc (peel-eq B₁ (q + suc b₁) B₂ {a}))) rhs≡
            ■ ss-U (sw-codq B₁ {q} {b₁} {B₂} {a}) (cong suc (peel-eq B₁ (q + suc b₁) B₂ {a}))
                   {t = subst U.Proc (EQ ■ sw-domq B₁ {q} {b₁} {B₂} {a}) Z U.⋯ₚ raw′}
            ■ cong (λ e → subst U.Proc e (subst U.Proc (EQ ■ sw-domq B₁ {q} {b₁} {B₂} {a}) Z U.⋯ₚ raw′)) (uipℕ _ refl) )
    reconcile : hiᵤ ≡ subst U.Proc (peel-eq B₁ (q + suc b₁) B₂ {a})
                        (U.φ U.drop TARGETbody)
    reconcile =
        subst-φ-out HI U.drop (bodyW U.⋯ₚ raw)
      ■ cong (U.φ U.drop) reconcileBody
      ■ sym (subst-φ (peel-eq B₁ (q + suc b₁) B₂ {a}) TARGETbody)

-- ============================================================================
--   handle-L1-varq : L-slot of the residual acq-handle (prefix B₁ ++ (q+1) ∷ [])
--   is a variable at syncs (suc b₁ ∷ B₂).  Width-agnostic reuse of handle-L-var.
-- ============================================================================
handle-L1-varq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs ((B₁ ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂) + N) ]
    (proj₁ (canonₛ-handle (B₁ ++ (q + 1) ∷ []) e₁ x e₂ b₁ B₂) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
handle-L1-varq []         {N} e₁ x e₂ q b₁ B₂ = handle-L-var (q + 1) [] e₁ x e₂ b₁ B₂
handle-L1-varq (c ∷ B₁')  {N} e₁ x e₂ q b₁ B₂ = handle-L-var c (B₁' ++ (q + 1) ∷ []) e₁ x e₂ b₁ B₂

-- ============================================================================
--   handle-R0-varq : R-slot of the fresh ret-handle canonₛ-handleq B₁ q 0 is a
--   variable at syncs (suc b₁ ∷ B₂).  Base uses Ub-R-last (position q is last of
--   the width-(q+1) fresh block).  Cons cases mirror handle-R0-var.
-- ============================================================================
q+1-last : ∀ q → suc (Fin.toℕ (q ↑ʳ (Fin.zero {n = 0}))) ≡ q + 1
q+1-last q = cong suc (Fin.toℕ-↑ʳ q Fin.zero ■ Nat.+-identityʳ q) ■ Nat.+-comm 1 q

handle-R0-varq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + N) ]
    (proj₁ (proj₂ (canonₛ-handleq B₁ e₁ x e₂ q 0 (suc b₁ ∷ B₂))) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
handle-R0-varq [] {N} e₁ x e₂ q b₁ B₂ =
    subst 𝔽 (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F)
  , ( cong (subst Tm (+-suc sD N)) (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sD) e2'≡ ■ Ub-nat′)
    ■ subst-`v (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F) )
  , (toℕ-substᶠ (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F)
      ■ toℕ-weaken*ᵣ sD 0F ■ Nat.+-identityʳ sD)
  where
    sD = syncs (suc b₁ ∷ B₂)
    e2'≡ : proj₁ (proj₂ (Ub-triple (q + suc 0) (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F))) ≡ ` 0F
    e2'≡ = Ub-R-last (q + suc 0) (wk e₁) (` 0F) (suc x) (q ↑ʳ 0F) (q+1-last q)
    Ub-nat′ : (` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sD ≡ ` (weaken* ⦃ Kᵣ ⦄ sD 0F)
    Ub-nat′ = refl
handle-R0-varq (a ∷ []) {N} e₁ x e₂ q b₁ B₂ with handle-R0-varq [] (` 0F) (suc x) (wk e₂) q b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs ((q + 1) ∷ suc b₁ ∷ B₂)
handle-R0-varq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ with handle-R0-varq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)

-- ============================================================================
--   Ub-L-wk : the L-slot (proj₁) of a handle triple whose e₁ is already weakened
--   equals the ungrown L-slot (any width/e₂/c at the same toℕ position) then
--   weakened.  proj₁ ignores e₂ and c, so only e₁ and the position parity
--   (=0 → e₁, >0 → *) matter; each is stable under weakenᵣ.
-- ============================================================================
Ub-L-wk : ∀ (w1 w2 : ℕ) {N} (e1 e2 : Tm N) (e2' : Tm (suc N)) (c : 𝔽 N) (c' : 𝔽 (suc N)) (p1 : 𝔽 w1) (p2 : 𝔽 w2) →
          Fin.toℕ p1 ≡ Fin.toℕ p2 →
          proj₁ (Ub-triple w1 (e1 ⋯ weakenᵣ) e2' c' p1)
          ≡ proj₁ (Ub-triple w2 e1 e2 c p2) ⋯ weakenᵣ
Ub-L-wk (suc zero)     (suc zero)     e1 e2 e2' c c' zero     zero     eq = refl
Ub-L-wk (suc zero)     (suc (suc w2)) e1 e2 e2' c c' zero     zero     eq = refl
Ub-L-wk (suc (suc w1)) (suc zero)     e1 e2 e2' c c' zero     zero     eq = refl
Ub-L-wk (suc (suc w1)) (suc (suc w2)) e1 e2 e2' c c' zero     zero     eq = refl
Ub-L-wk (suc (suc w1)) (suc (suc w2)) e1 e2 e2' c c' zero     (suc p2) ()
Ub-L-wk (suc (suc w1)) (suc (suc w2)) e1 e2 e2' c c' (suc p1) zero     ()
Ub-L-wk (suc zero)     w2             e1 e2 e2' c c' (suc ()) p2       eq
Ub-L-wk (suc (suc w1)) (suc zero)     e1 e2 e2' c c' (suc p1) (suc ()) eq
Ub-L-wk (suc (suc w1)) (suc (suc w2)) e1 e2 e2' c c' (suc p1) (suc p2) eq =
  Ub-L-wk (suc w1) (suc w2) * e2 e2' c c' p1 p2 (Nat.suc-injective eq)

-- ============================================================================
--   handle-L-rwkq / handle-R-rwkq : the ret/acq handle slots equal the original
--   position-q handle slots post-composed with sinsq.
-- ============================================================================
handle-L-rwkq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (canonₛ-handleq B₁ e₁ x e₂ q 0 (suc b₁ ∷ B₂))
  ≡ proj₁ (canonₛ-handleq B₁ e₁ x e₂ q b₁ B₂) ⋯ sinsq B₁ q b₁ B₂ {N}
handle-L-rwkq [] {N} e₁ x e₂ q b₁ []       =
    ⋯-id _ (λ _ → refl)
  ■ Ub-L-wk (q + 1) (q + suc b₁ + 0) e₁ e₂ (` 0F) x (suc x) p1 p2 eqp
  where
    p1 : 𝔽 (q + 1)
    p1 = q ↑ʳ 0F
    p2 : 𝔽 (q + suc b₁ + 0)
    p2 = (q ↑ʳ 0F) ↑ˡ 0
    eqp : Fin.toℕ p1 ≡ Fin.toℕ p2
    eqp = (Fin.toℕ-↑ʳ q (Fin.zero {n = 0}) ■ Nat.+-identityʳ q)
        ■ sym (Fin.toℕ-↑ˡ (q ↑ʳ (Fin.zero {n = b₁})) 0 ■ Fin.toℕ-↑ʳ q (Fin.zero {n = b₁}) ■ Nat.+-identityʳ q)
handle-L-rwkq [] {N} e₁ x e₂ q b₁ (c′ ∷ B) =
    cong (λ z → subst Tm (cong suc (+-suc sB N)) (z ⋯ weaken* ⦃ Kᵣ ⦄ (suc sB))) aLwk
  ■ cong (subst Tm (cong suc (+-suc sB N))) (weaken-suc-shift A' sB)
  ■ subst-Tm-uip (cong suc (+-suc sB N)) SINSQCOD Y
  ■ sym (subst-⋯-cod-local SINSQCOD RR (weakenᵣ ↑* (suc sB)))
  ■ cong (λ z → subst Tm (+-suc sB N) (z ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ sinsq [] q b₁ (c′ ∷ B)) (sym aRwk)
  where
    sB = syncs (c′ ∷ B)
    A' = proj₁ (Ub-triple (q + suc b₁) e₁ e₂ x (q ↑ʳ 0F))
    aLwk = Ub-L-wk (q + 1) (q + suc b₁) e₁ e₂ (` 0F) x (suc x) (q ↑ʳ 0F) (q ↑ʳ 0F)
             (Fin.toℕ-↑ʳ q (Fin.zero {n = 0}) ■ sym (Fin.toℕ-↑ʳ q (Fin.zero {n = b₁})))
    aRwk = Ub-L-wk (q + suc b₁) (q + suc b₁) e₁ e₂ (` 0F) x (suc x) (q ↑ʳ 0F) (q ↑ʳ 0F) refl
    RR = subst Tm (+-suc sB N) (A' ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    Y  = RR ⋯ (weakenᵣ ↑* (suc sB))
    SINSQCOD = +-suc (syncs ((q + suc b₁) ∷ c′ ∷ B)) N
             ■ cong (_+ N) (cong suc (syncs-head-irrel (q + suc b₁) (suc b₁) (c′ ∷ B)))
handle-L-rwkq (a ∷ []) {N} e₁ x e₂ q b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwkq [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ sym ( cong (_⋯ sinsq (a ∷ []) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ([] ++ (q + suc b₁) ∷ B₂)
    sBᴿ = syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)
    ρ   = sinsq [] q b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handleq [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (q + suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] (q + 1) (suc b₁ ∷ B₂)))
handle-L-rwkq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwkq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ sym ( cong (_⋯ sinsq (a ∷ d ∷ B₁″) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sBᴿ = syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)
    ρ   = sinsq (d ∷ B₁″) q b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handleq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + 1) (suc b₁ ∷ B₂)))

handle-R-rwkq : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (q b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (λ z → syncs z + N) (++-assoc B₁ ((q + 1) ∷ []) (suc b₁ ∷ B₂)))
    (proj₁ (proj₂ (canonₛ-handle (B₁ ++ (q + 1) ∷ []) e₁ x e₂ b₁ B₂)))
  ≡ proj₁ (proj₂ (canonₛ-handleq B₁ e₁ x e₂ q b₁ B₂)) ⋯ sinsq B₁ q b₁ B₂ {N}
handle-R-rwkq [] {N} e₁ x e₂ q zero     []       =
  sym (cong (_⋯ weakenᵣ)
    (Ub-R-last (q + 1 + 0) e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0)
      (cong suc (Fin.toℕ-↑ˡ (q ↑ʳ 0F) 0 ■ Fin.toℕ-↑ʳ q (Fin.zero {n = zero}) ■ Nat.+-identityʳ q)
       ■ sym (Nat.+-identityʳ (q + 1) ■ Nat.+-comm q 1))))
handle-R-rwkq [] {N} e₁ x e₂ q (suc b₁) []       =
  sym (cong (_⋯ weakenᵣ)
    (Ub-R-far (q + suc (suc b₁) + 0) e₁ e₂ x ((q ↑ʳ 0F) ↑ˡ 0)
      (subst (λ z → suc (suc z) Nat.≤ q + suc (suc b₁) + 0)
        (sym (Fin.toℕ-↑ˡ (q ↑ʳ 0F) 0 ■ Fin.toℕ-↑ʳ q (Fin.zero {n = suc b₁}) ■ Nat.+-identityʳ q))
        (Nat.≤-trans (Nat.m≤m+n (suc (suc q)) b₁)
          (Nat.≤-reflexive (solve 2 (λ a b → (con 2 :+ a) :+ b := (a :+ (con 2 :+ b)) :+ con 0) refl q b₁))))))
handle-R-rwkq [] {N} e₁ x e₂ q zero     (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc sB N))) (subst-`v (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB 0F))
  ■ subst-`v (cong suc (+-suc sB N)) (subst 𝔽 (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB 0F))
  ■ cong `_ (Fin.toℕ-injective (toℕVL ■ sym toℕVR))
  ■ sym rhs≡
  where
    sB = syncs (c′ ∷ B)
    w  = subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F)
    toℕw : Fin.toℕ w ≡ sB
    toℕw = toℕ-substᶠ (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F) ■ toℕ-weaken*ᵣ sB 0F ■ Nat.+-identityʳ sB
    rhs≡ : subst Tm (+-suc sB N)
             (Ub-triple (q + 1) (e₁ ⋯ weakenᵣ) (` 0F) (suc x) (q ↑ʳ 0F) .proj₂ .proj₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
             ⋯ sinsq [] q zero (c′ ∷ B)
           ≡ ` (sinsq [] q zero (c′ ∷ B) w)
    rhs≡ = cong (_⋯ sinsq [] q zero (c′ ∷ B))
             ( cong (subst Tm (+-suc sB N))
                 (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB)
                   (Ub-R-last (q + 1) (e₁ ⋯ weakenᵣ) (` 0F) (suc x) (q ↑ʳ 0F) (q+1-last q)))
             ■ subst-`v (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB 0F) )
    toℕVL : Fin.toℕ (subst 𝔽 (cong suc (+-suc sB N)) (subst 𝔽 (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB 0F))) ≡ sB
    toℕVL = toℕ-substᶠ (cong suc (+-suc sB N)) _
          ■ toℕ-substᶠ (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB 0F)
          ■ toℕ-weaken*ᵣ sB 0F ■ Nat.+-identityʳ sB
    toℕVR : Fin.toℕ (sinsq [] q zero (c′ ∷ B) w) ≡ sB
    toℕVR = sins-toℕ-loq [] q zero (c′ ∷ B) w (subst (Nat._< suc sB) (sym toℕw) (Nat.n<1+n sB)) ■ toℕw
handle-R-rwkq [] {N} e₁ x e₂ q (suc b₁) (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc sB N))) (subst-Kunit (+-suc sB (suc N)))
  ■ subst-Kunit (cong suc (+-suc sB N))
  ■ sym ( cong (_⋯ sinsq [] q (suc b₁) (c′ ∷ B))
            ( cong (subst Tm (+-suc sB N))
                (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB)
                  (Ub-R-far (q + suc (suc b₁)) (e₁ ⋯ weakenᵣ) (` 0F) (suc x) (q ↑ʳ 0F) farLt))
            ■ subst-Kunit (+-suc sB N) ) )
  where
    sB = syncs (c′ ∷ B)
    farLt : suc (Fin.toℕ (q ↑ʳ 0F)) Nat.< q + suc (suc b₁)
    farLt = subst (λ z → suc (suc z) Nat.≤ q + suc (suc b₁))
              (sym (Fin.toℕ-↑ʳ q (Fin.zero {n = suc b₁}) ■ Nat.+-identityʳ q))
              (Nat.≤-trans (Nat.m≤m+n (suc (suc q)) b₁)
                (Nat.≤-reflexive (solve 2 (λ a b → (con 2 :+ a) :+ b := a :+ (con 2 :+ b)) refl q b₁)))
handle-R-rwkq (a ∷ []) {N} e₁ x e₂ q b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwkq [] (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ sym ( cong (_⋯ sinsq (a ∷ []) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ([] ++ (q + suc b₁) ∷ B₂)
    sBᴿ' = syncs (([] ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ([] ++ (q + 1) ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ([] ++ (q + 1) ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handleq [] (` 0F) (suc x) (wk e₂) q b₁ B₂))
    ρ    = sinsq [] q b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc [] ((q + 1) ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ []) ((q + 1) ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (q + suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] (q + 1) (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')
handle-R-rwkq (a ∷ d ∷ B₁″) {N} e₁ x e₂ q b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwkq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂)
  ■ sym ( cong (_⋯ sinsq (a ∷ d ∷ B₁″) q b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ((d ∷ B₁″) ++ (q + suc b₁) ∷ B₂)
    sBᴿ' = syncs (((d ∷ B₁″) ++ (q + 1) ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ((d ∷ B₁″) ++ (q + 1) ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ((d ∷ B₁″) ++ (q + 1) ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handleq (d ∷ B₁″) (` 0F) (suc x) (wk e₂) q b₁ B₂))
    ρ    = sinsq (d ∷ B₁″) q b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc (d ∷ B₁″) ((q + 1) ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ d ∷ B₁″) ((q + 1) ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (q + 1) (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')

-- ============================================================================
--   leafσ-rwk-idq : the grown leaf-substitution agrees with the ungrown one
--   post-composed with sinsq (lifted over the B-block binders), off the handle.
--   Port of the dropped SplitsH3.leafσ-rwk-id to general q.
-- ============================================================================
leafσ-rwk-idq : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ B : BindGroup) (q b₁ : ℕ)
               (i : 𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B + m)) →
               i ≢ SplitRenamings.atk B₁ B₂ (sum B) {q + suc b₁} {m} (q ↑ʳ 0F) →
               leafσ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i ⋯ (sinsq B₁ q b₁ B₂ {2 + n} ↑* syncs B)
               ≡ leafσ σ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} i)
leafσ-rwk-idq {m} {n} σ B₁ B₂ B q b₁ i i≢
  with Fin.splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) i in seqo
... | inj₂ u
  rewrite leafσ-tail {n = n} σ (B₁ ++ (q + suc b₁) ∷ B₂) B i u seqo
        | leafσ-tail {n = n} σ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} i) u
            (cong (Fin.splitAt (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B))
               (cong (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo) ■ P3rq B₁ B₂ B {q} {b₁} {m} u)
            ■ Fin.splitAt-↑ʳ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) m u) =
      sym (⋯-↑*-wk (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂))) (sinsq B₁ q b₁ B₂ {2 + n}) (syncs B))
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) tCore
  where
    tCore : (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂))) ⋯ sinsq B₁ q b₁ B₂ {2 + n}
            ≡ σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂))
    tCore = fusion (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂))) (sinsq B₁ q b₁ B₂ {2 + n})
          ■ ⋯-cong (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2) (λ v → sins-wkq B₁ q b₁ B₂ {2 + n} v)
... | inj₁ db with Fin.splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) db in seqi
...   | inj₂ w
  rewrite leafσ-B₁ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i db w seqo seqi
        | leafσ-B₁ σ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} i) (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w) w
            (cong (Fin.splitAt (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B)) (cong (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ P2rq B₁ B₂ B {q} {b₁} {m} w)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) ↑ʳ w) m)
            (Fin.splitAt-↑ʳ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) (sum B) w) =
      canonₛ-nat B (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ (q + suc b₁) ∷ B₂)) 1F , K `unit) (sinsq B₁ q b₁ B₂ {2 + n}) w
    ■ cong (λ z → canonₛ B (K `unit , z , K `unit) w) (sins-wkq B₁ q b₁ B₂ {2 + n} 1F)
...   | inj₁ d
  rewrite leafσ-A₁ σ (B₁ ++ (q + suc b₁) ∷ B₂) B i db d seqo seqi
        | leafσ-A₁ σ (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) B (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m} i) (drwkq B₁ q b₁ B₂ d ↑ˡ sum B) (drwkq B₁ q b₁ B₂ d)
            (cong (Fin.splitAt (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B)) (cong (SplitRenamings.rwk B₁ B₂ (sum B) {q} {b₁} {m}) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ P1rq B₁ B₂ B {q} {b₁} {m} d)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂) + sum B) (drwkq B₁ q b₁ B₂ d ↑ˡ sum B) m)
            (Fin.splitAt-↑ˡ (sum (B₁ ++ (q + 1) ∷ suc b₁ ∷ B₂)) (drwkq B₁ q b₁ B₂ d) (sum B)) =
      sym (⋯-↑*-wk (canonₛ (B₁ ++ (q + suc b₁) ∷ B₂) (K `unit , 0F , K `unit) d) (sinsq B₁ q b₁ B₂ {2 + n}) (syncs B))
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
        (sym (canonₛ-rwkq B₁ (K `unit , 0F , K `unit) q b₁ B₂ d
          (λ d≡ → i≢ ((sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ (q + suc b₁) ∷ B₂)) (sum B)) seqi)) ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡))))
