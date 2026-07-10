-- | Per-generator reflection for the reverse simulation's RU-Struct case, the
--   UP-TO-φ / EQUIVARIANCE route.
--
--   The RU-Struct case of sim←ᵍ receives  red = RU-Struct c₁ inner c₂  on a
--   STRICT image  U[ P ] σ.  Rather than trying to recognise the reduct of c₁'s
--   leading link as ANOTHER translation image (the strict-recognizer route, which
--   fails at the νφ-comm φ-escape — RevUCong.reverse-U-≋-⊥), we push the reduction
--   BACK across the leading ≋′ generator by EQUIVARIANCE (RedRename.red-⋯ₚ) and
--   fire it on the strict image itself.
--
--   ν-swap′ is the crux.  Its reduct is  ν (body ⋯ₚ swapᵣ 1 1) — the ν-BOUND
--   variables of U[ P ] σ = ν body renamed by the INVOLUTIVE  swapᵣ 1 1, NOT the
--   flag-transposing φ-telescope reindexing that the multi-block strict bridge
--   needs (DepthDescentWall.φ-align-⊥).  So a body reduction  sub : body⋯swap ─→ T
--   is transported by  red-⋯ₚ (swapᵣ 1 1)  — using  swapᵣ 1 1 ∘ swapᵣ 1 1 ≡ id —
--   to a reduction  body ─→ T⋯swap  which fires ON the strict image via RU-Res.
--   The residual forward swap  ν T ≋ ν (T⋯swap)  is absorbed into the codomain ≈.
--
--   Each reflection lemma is CLOSED relative to a strict-image reflector `rec`
--   ( = sim←ᵍ σ Vσ Γ-S ⊢P refl restricted to a genuine step on U[ P ] σ ), the
--   role played by the WF engine's dispatch once wired into Backward.sim←ᵍ.
module BorrowedCF.Simulation2.Backward.RUStructDispatch where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.RedRename using (red-⋯ₚ)
open import BorrowedCF.Simulation.CongruenceH1 using (local-⋯ₚ-id)
open import BorrowedCF.Simulation.RevSwapInv using (swap-swap)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≈-trans; ≋⇒≈)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Sum as Sum
import Data.Fin as Fin

open Fin.Patterns

------------------------------------------------------------------------
-- The reflection payload.
------------------------------------------------------------------------

Res : ∀ {m n} (σ : m →ₛ n) (P : TP.Proc m) → UP.Proc n → Set
Res σ P Q = Σ[ P′ ∈ TP.Proc _ ] (Star TR._─→ₚ_ P P′ × Q ≈ U[ P′ ] σ)

------------------------------------------------------------------------
-- swapᵣ 1 1 is involutive on untyped processes.
------------------------------------------------------------------------

swapₚ-invU : ∀ {n} (P : UP.Proc (2 + n)) → (P UP.⋯ₚ swapᵣ 1 1) UP.⋯ₚ swapᵣ 1 1 ≡ P
swapₚ-invU P = UP.fusionₚ P (swapᵣ 1 1) (swapᵣ 1 1) ■ local-⋯ₚ-id P (swap-swap 1 1)

------------------------------------------------------------------------
-- ν-swap′ reflection (the crux).
--
--   c₁'s leading link is  ν-swap′ :  U[ P ] σ = ν body ≋′ ν (body ⋯ₚ swapᵣ 1 1).
--   A ν-headed step on the swapped form is (up to further RU-Structs, peeled by
--   the engine) an  RU-Res sub  with  sub : body ⋯ₚ swapᵣ 1 1 ─→ₚ T.  Transport
--   sub back by equivariance and fire on the strict image.
------------------------------------------------------------------------

νswap-reflect :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → (rec : ∀ {Q′} → U[ P ] σ UR.─→ₚ Q′ → Res σ P Q′)
  → {body : UP.Proc (2 + n)}
  → U[ P ] σ ≡ UP.ν body
  → {T : UP.Proc (2 + n)}
  → (sub : (body UP.⋯ₚ swapᵣ 1 1) UR.─→ₚ T)
  → Res σ P (UP.ν T)
νswap-reflect σ {P} rec {body} imgeq {T} sub
  with sub′ ← subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ swapᵣ 1 1)) (swapₚ-invU body)
                    (red-⋯ₚ (swapᵣ 1 1) sub)
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (T UP.⋯ₚ swapᵣ 1 1)) (sym imgeq) (UR.RU-Res sub′))
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.return (UP.ν-swap′ {P = T}))) codom

------------------------------------------------------------------------
-- assocSwapᵣ 2 2 is involutive on untyped processes.
--   (assocSwap-swap is Fin-level; kept local so this module does not pull in the
--    heavy BorrowedCF.TypedEq that houses it.)
------------------------------------------------------------------------

assocSwap-swap : ∀ a b {n} (x : 𝔽 (a + (b + n))) → assocSwapᵣ b a (assocSwapᵣ a b x) ≡ x
assocSwap-swap a b {n} x with Fin.splitAt a x in eqa
... | Sum.inj₁ p rewrite Fin.splitAt-↑ʳ b (a + n) (p ↑ˡ n) | Fin.splitAt-↑ˡ a p n
      = sym (sym (Fin.join-splitAt a (b + n) x) ■ cong (Fin.join a (b + n)) eqa)
... | Sum.inj₂ q with Fin.splitAt b q in eqb
...   | Sum.inj₁ r rewrite Fin.splitAt-↑ˡ b r (a + n)
        = sym (sym (Fin.join-splitAt a (b + n) x)
               ■ cong (Fin.join a (b + n)) eqa
               ■ cong (a ↑ʳ_) (sym (Fin.join-splitAt b n q) ■ cong (Fin.join b n) eqb))
...   | Sum.inj₂ s rewrite Fin.splitAt-↑ʳ b (a + n) (a ↑ʳ s) | Fin.splitAt-↑ʳ a n s
        = sym (sym (Fin.join-splitAt a (b + n) x)
               ■ cong (Fin.join a (b + n)) eqa
               ■ cong (a ↑ʳ_) (sym (Fin.join-splitAt b n q) ■ cong (Fin.join b n) eqb))

assocSwapₚ-invU : ∀ {n} (P : UP.Proc (2 + (2 + n)))
               → (P UP.⋯ₚ assocSwapᵣ 2 2) UP.⋯ₚ assocSwapᵣ 2 2 ≡ P
assocSwapₚ-invU P = UP.fusionₚ P (assocSwapᵣ 2 2) (assocSwapᵣ 2 2)
                  ■ local-⋯ₚ-id P (assocSwap-swap 2 2)

------------------------------------------------------------------------
-- ν-comm′ reflection (equivariance analog of ν-swap′, with assocSwapᵣ 2 2).
--
--   c₁'s leading link is  ν-comm′ :  U[ P ] σ = ν (ν body) ≋′
--   ν (ν (body ⋯ₚ assocSwapᵣ 2 2)).  A ν-ν-headed step on the reduct is (up to
--   RU-Structs peeled by the engine) an  RU-Res (RU-Res sub) with
--   sub : body ⋯ₚ assocSwapᵣ 2 2 ─→ₚ T.  Transport back and fire on the image.
------------------------------------------------------------------------

νcomm-reflect :
  ∀ {m n} (σ : m →ₛ n) {P : TP.Proc m}
  → (rec : ∀ {Q′} → U[ P ] σ UR.─→ₚ Q′ → Res σ P Q′)
  → {body : UP.Proc (2 + (2 + n))}
  → U[ P ] σ ≡ UP.ν (UP.ν body)
  → {T : UP.Proc (2 + (2 + n))}
  → (sub : (body UP.⋯ₚ assocSwapᵣ 2 2) UR.─→ₚ T)
  → Res σ P (UP.ν (UP.ν T))
νcomm-reflect σ {P} rec {body} imgeq {T} sub
  with sub′ ← subst (λ Z → Z UR.─→ₚ (T UP.⋯ₚ assocSwapᵣ 2 2)) (assocSwapₚ-invU body)
                    (red-⋯ₚ (assocSwapᵣ 2 2) sub)
  with P′ , steps , codom ←
    rec (subst (λ Z → Z UR.─→ₚ UP.ν (UP.ν (T UP.⋯ₚ assocSwapᵣ 2 2))) (sym imgeq)
               (UR.RU-Res (UR.RU-Res sub′)))
  = P′ , steps , ≈-trans (≋⇒≈ (Eq*.return (UP.ν-comm′ {P = T}))) codom
