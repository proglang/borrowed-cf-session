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

------------------------------------------------------------------------
-- Substitution helpers on the reduct triples.
------------------------------------------------------------------------

subst-⊗ : ∀ {a b} (eq : a ≡ b) (p q : Tm a) → subst Tm eq (p ⊗ q) ≡ subst Tm eq p ⊗ subst Tm eq q
subst-⊗ refl p q = refl

subst-`F : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
subst-`F refl q = refl

subst-K : ∀ {a b} (eq : a ≡ b) (c : _) → subst Tm eq (K c) ≡ K c
subst-K refl c = refl

------------------------------------------------------------------------
-- φ-telescope concatenation and the width / wkΦ arithmetic.
------------------------------------------------------------------------

infixr 6 _++Φ_
_++Φ_ : ∀ {a b c} → Φ* a b → Φ* b c → Φ* a c
[]φ      ++Φ Ψ = Ψ
(fc ◂ Φ) ++Φ Ψ = fc ◂ (Φ ++Φ Ψ)

plugΦ-++ : ∀ {a b c} (Φ : Φ* a b) (Ψ : Φ* b c) (P : U.Proc c) →
           plugΦ (Φ ++Φ Ψ) P ≡ plugΦ Φ (plugΦ Ψ P)
plugΦ-++ []φ      Ψ P = refl
plugΦ-++ (fc ◂ Φ) Ψ P = cong (U.φ (proj₁ fc) (proj₂ fc)) (plugΦ-++ Φ Ψ P)

widthΦ : ∀ {a b} → Φ* a b → ℕ
widthΦ []φ      = 0
widthΦ (_ ◂ Φ)  = suc (widthΦ Φ)

toℕ-wkΦ : ∀ {a b} (Φ : Φ* a b) (j : 𝔽 a) → Fin.toℕ (wkΦ Φ j) ≡ widthΦ Φ + Fin.toℕ j
toℕ-wkΦ []φ      j = refl
toℕ-wkΦ (fc ◂ Φ) j = toℕ-wkΦ Φ (Fin.suc j) ■ Nat.+-suc (widthΦ Φ) (Fin.toℕ j)

widthΦ-subst : ∀ {a b b′} (eq : b ≡ b′) (t : Φ* a b) → widthΦ (subst (Φ* a) eq t) ≡ widthΦ t
widthΦ-subst refl t = refl

widthΦ-Btel : ∀ {n} (B : TP.BindGroup) (cc : UChan n) → widthΦ (Btel {n} B cc) ≡ syncs B
widthΦ-Btel []            cc = refl
widthΦ-Btel (b ∷ [])      cc = refl
widthΦ-Btel {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  cong suc (widthΦ-subst (+-suc (syncs B) n) (Btel B (` 0F , suc x , wk e2))
            ■ widthΦ-Btel B (` 0F , suc x , wk e2))

widthΦ-++ : ∀ {a b c} (Φ : Φ* a b) (Ψ : Φ* b c) → widthΦ (Φ ++Φ Ψ) ≡ widthΦ Φ + widthΦ Ψ
widthΦ-++ []φ      Ψ = refl
widthΦ-++ (fc ◂ Φ) Ψ = cong suc (widthΦ-++ Φ Ψ)

------------------------------------------------------------------------
-- The leaf substitution of a flattened ν-block, and the flat equation.
------------------------------------------------------------------------

leafσ : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : TP.BindGroup) →
        (sum B₁ + sum B₂ + m →ₛ syncs B₂ + (syncs B₁ + (2 + n)))
leafσ {m} {n} σ B₁ B₂ =
  ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ
    canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit))
   ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))

Uν-flatΦ : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : TP.BindGroup) (P : TP.Proc (sum B₁ + sum B₂ + m)) →
  U[ TP.ν B₁ B₂ P ] σ
  ≡ U.ν (Bφ B₁ (K `unit , 0F , K `unit)
           (Bφ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
             (U[ P ] (leafσ σ B₁ B₂))))
Uν-flatΦ {m} {n} σ B₁ B₂ P =
  cong U.ν
    ( UB-flatΦ B₁ (K `unit , 0F , K `unit) g
    ■ cong (Bφ B₁ (K `unit , 0F , K `unit))
        (UB-flatΦ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
           (leaf (canonₛ B₁ (K `unit , 0F , K `unit)))) )
  where
    leaf : (sum B₁ →ₛ syncs B₁ + (2 + n)) → (sum B₂ →ₛ syncs B₂ + (syncs B₁ + (2 + n))) →
           U.Proc (syncs B₂ + (syncs B₁ + (2 + n)))
    leaf τ₁ τ₂ = U[ P ] (((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂)
                   ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)))
    g : (sum B₁ →ₛ syncs B₁ + (2 + n)) → U.Proc (syncs B₁ + (2 + n))
    g τ₁ = UB[ B₂ ] (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) (leaf τ₁)
