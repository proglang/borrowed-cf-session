-- | The channel-carrying φ-telescope of a translated bind group.
--
--   Replaces the channel-free `Bφ` engine (and its now-dead float-out transpose
--   lemmas) used across the forward image-step proofs.  Under the linked-φ
--   design a cell cannot commute out of its ν, so the image-step proofs no
--   longer transpose a cell to the leaf; instead they flatten the image to
--   `ν (plugΦ (Btel B c) leaf)` and fire the (now telescoped) channel rule
--   IN PLACE under `Btel B c`.
--
--   `Btel B c` is exactly the `Φ*` telescope `UB[ B ] c` builds — one
--   `φ ϕ[b] (` x)` cell per non-last bind-group element, channels descending
--   `x, suc x, …` — and `UB-flatΦ` is the channel-carrying `UB-flat`.
module BorrowedCF.Simulation.Support.Theorems.PhiTel where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Translation
open import BorrowedCF.Reduction.Processes.Untyped using (Φ*; []φ; _◂_; plugΦ; wkΦ)
import BorrowedCF.Processes.Untyped as U
import BorrowedCF.Processes.Typed as TP

open import Data.Nat.ListAction using (sum)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- The canonical leaf substitution of a bind group (channel-carrying).
------------------------------------------------------------------------

canonₛ : ∀ {n} (B : TP.BindGroup) → UChan n → (sum B →ₛ syncs B + n)
canonₛ []            cc = λ ()
canonₛ (b ∷ [])      cc = Ub[ b + 0 ] cc
canonₛ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)
           , canonₛ B (` 0F , suc x , wk e2) ]′ (Fin.splitAt b y))

------------------------------------------------------------------------
-- The φ-telescope of a bind group.
------------------------------------------------------------------------

Btel : ∀ {n} (B : TP.BindGroup) → UChan n → Φ* n (syncs B + n)
Btel []            cc            = []φ
Btel (b ∷ [])      cc            = []φ
Btel {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  (ϕ[ b ] , ` x) ◂ subst (Φ* (1 + n)) (+-suc (syncs B) n) (Btel B (` 0F , suc x , wk e2))

-- Plugging the telescope: the channel-carrying `Bφ`.
Bφ : ∀ {n} (B : TP.BindGroup) → UChan n → U.Proc (syncs B + n) → U.Proc n
Bφ B cc P = plugΦ (Btel B cc) P

------------------------------------------------------------------------
-- `plugΦ` commutes with the scope transport `Btel` inserts.
------------------------------------------------------------------------

plugΦ-subst : ∀ {n k k′} (eq : k ≡ k′) (t : Φ* n k) (P : U.Proc k′) →
              plugΦ (subst (Φ* n) eq t) P ≡ plugΦ t (subst U.Proc (sym eq) P)
plugΦ-subst refl t P = refl

------------------------------------------------------------------------
-- UB[ B ] unfolds to its φ-telescope wrapped around the leaf.
------------------------------------------------------------------------

UB-flatΦ : ∀ {n} (B : TP.BindGroup) (cc : UChan n)
           (f : (sum B →ₛ syncs B + n) → U.Proc (syncs B + n)) →
           UB[ B ] cc f ≡ Bφ B cc (f (canonₛ B cc))
UB-flatΦ []            cc f = refl
UB-flatΦ (b ∷ [])      cc f = refl
UB-flatΦ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) f =
  cong (U.φ ϕ[ b ] (` x))
    ( UB-flatΦ B (` 0F , suc x , wk e2) leaffn
    ■ sym (plugΦ-subst (+-suc (syncs B) n) (Btel B (` 0F , suc x , wk e2))
             (f (canonₛ (b ∷ B) (e1 , x , e2)))) )
  where
    sB = syncs B
    leaffn : (sum B →ₛ sB + suc n) → U.Proc (sB + suc n)
    leaffn = λ τ → subst U.Proc (sym (+-suc sB n))
               (f (λ y → subst Tm (+-suc sB n)
                     ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB , τ ]′ (Fin.splitAt b y))))
