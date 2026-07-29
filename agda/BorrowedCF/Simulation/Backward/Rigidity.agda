-- | Backward-simulation RIGIDITY (linked-φ port of Experiment/LinkedPhi).
--
--   Every φ-cell in a translation image guards an INTERNALLY-bound channel
--   (a variable pointing at an enclosing ν).  This module defines that
--   invariant (`Grounded`) over the REAL channel-carrying Untyped calculus and
--   proves it is a ≋-invariant, hence images stay non-φ-headed under the whole
--   gated structural congruence — the keystone that replaces the old up-to-φ
--   engine in the two hard backward cases.
module BorrowedCF.Simulation.Backward.Rigidity where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped

open import Relation.Nullary using (yes; no)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import BorrowedCF.Simulation.Support.BlockPerm
  using ( toℕ-swapᵣ-lt; toℕ-swapᵣ-mid; toℕ-swapᵣ-ge
        ; toℕ-assoc-lt; toℕ-assoc-mid; toℕ-assoc-ge
        ; toℕ-weaken*ᵣ )

open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Processes.Translation using (U[_]; UB[_]; Ub[_]; syncs)
import BorrowedCF.Processes.Typed as 𝐓

open Nat.Variables
open Fin.Patterns

private variable
  t t₁ t₂ : ℕ

------------------------------------------------------------------------
-- The channel-below-threshold predicate on the Tm-valued channel.
--   `ChanBelow t c` holds iff c is a variable strictly below t.
------------------------------------------------------------------------

data ChanBelow {n : ℕ} (t : ℕ) : Tm n → Set where
  chanvar : (x : 𝔽 n) → Fin.toℕ x Nat.< t → ChanBelow t (` x)

------------------------------------------------------------------------
-- Grounded: every φ guards an INTERNALLY-bound channel.  `t` counts the
--   internally-bound channels in scope; a ν adds 2, a φ adds 1.  An image at
--   ambient scope is `Grounded = Grounded′ 0`.
------------------------------------------------------------------------

Grounded′ : ℕ → Proc n → Set
Grounded′ t ⟪ e ⟫     = ⊤
Grounded′ t (P ∥ Q)   = Grounded′ t P × Grounded′ t Q
Grounded′ t (ν P)     = Grounded′ (2 + t) P
Grounded′ t (φ f c P) = ChanBelow t c × Grounded′ (1 + t) P

Grounded : Proc n → Set
Grounded = Grounded′ 0

------------------------------------------------------------------------
-- Renamings bounded below a threshold (two-threshold form so weakenings,
-- which shift the threshold, are covered by the same machinery).
------------------------------------------------------------------------

Below : ∀ {m n} → ℕ → ℕ → (m →ᵣ n) → Set
Below {m} t₁ t₂ ρ = (x : 𝔽 m) → Fin.toℕ x Nat.< t₁ → Fin.toℕ (ρ x) Nat.< t₂

Below⁻ : ∀ {m n} → ℕ → ℕ → (m →ᵣ n) → Set
Below⁻ {m} t₁ t₂ ρ = (x : 𝔽 m) → Fin.toℕ (ρ x) Nat.< t₂ → Fin.toℕ x Nat.< t₁

↑-Below : ∀ {m n} {ρ : m →ᵣ n} → Below t₁ t₂ ρ → Below (1 + t₁) (1 + t₂) (ρ ↑)
↑-Below bρ 0F          _            = Nat.s≤s Nat.z≤n
↑-Below bρ (Fin.suc x) (Nat.s≤s p)  = Nat.s≤s (bρ x p)

↑-Below⁻ : ∀ {m n} {ρ : m →ᵣ n} → Below⁻ t₁ t₂ ρ → Below⁻ (1 + t₁) (1 + t₂) (ρ ↑)
↑-Below⁻ bρ 0F          _            = Nat.s≤s Nat.z≤n
↑-Below⁻ bρ (Fin.suc x) (Nat.s≤s p)  = Nat.s≤s (bρ x p)

------------------------------------------------------------------------
-- Concrete Below/Below⁻ facts for the renamings occurring in the congruence.
------------------------------------------------------------------------

below-block : ∀ {dom cod} (f : dom →ᵣ cod) a b t →
  (fl : (x : 𝔽 dom) → Fin.toℕ x Nat.< a → Fin.toℕ (f x) ≡ b + Fin.toℕ x) →
  (fm : (x : 𝔽 dom) → a Nat.≤ Fin.toℕ x → Fin.toℕ x Nat.< a + b →
        Fin.toℕ (f x) ≡ Fin.toℕ x Nat.∸ a) →
  (fg : (x : 𝔽 dom) → a + b Nat.≤ Fin.toℕ x → Fin.toℕ (f x) ≡ Fin.toℕ x) →
  Below (a + b + t) (a + b + t) f
below-block f a b t fl fm fg x lt with Fin.toℕ x Nat.<? a
... | yes p = subst (Nat._< a + b + t) (sym (fl x p))
                (Nat.<-≤-trans (subst (b + Fin.toℕ x Nat.<_) (Nat.+-comm b a) (Nat.+-monoʳ-< b p))
                               (Nat.m≤m+n (a + b) t))
... | no ¬p with Fin.toℕ x Nat.<? (a + b)
...   | yes q = subst (Nat._< a + b + t) (sym (fm x (Nat.≮⇒≥ ¬p) q))
                  (Nat.≤-<-trans (Nat.m∸n≤m (Fin.toℕ x) a) lt)
...   | no ¬q = subst (Nat._< a + b + t) (sym (fg x (Nat.≮⇒≥ ¬q))) lt

below-block⁻ : ∀ {dom cod} (f : dom →ᵣ cod) a b t →
  (fg : (x : 𝔽 dom) → a + b Nat.≤ Fin.toℕ x → Fin.toℕ (f x) ≡ Fin.toℕ x) →
  Below⁻ (a + b + t) (a + b + t) f
below-block⁻ f a b t fg x hyp with Fin.toℕ x Nat.<? (a + b)
... | yes q = Nat.<-≤-trans q (Nat.m≤m+n (a + b) t)
... | no ¬q = subst (Nat._< a + b + t) (fg x (Nat.≮⇒≥ ¬q)) hyp

below-swap : ∀ a b {n} (t : ℕ) → Below (a + b + t) (a + b + t) (swapᵣ a b {n})
below-swap a b {n} t = below-block (swapᵣ a b {n}) a b t (toℕ-swapᵣ-lt a b) (toℕ-swapᵣ-mid a b) (toℕ-swapᵣ-ge a b)

below-swap⁻ : ∀ a b {n} (t : ℕ) → Below⁻ (a + b + t) (a + b + t) (swapᵣ a b {n})
below-swap⁻ a b {n} t = below-block⁻ (swapᵣ a b {n}) a b t (toℕ-swapᵣ-ge a b)

below-assoc : ∀ a b {m} (t : ℕ) → Below (a + b + t) (a + b + t) (assocSwapᵣ a b {m})
below-assoc a b {m} t = below-block (assocSwapᵣ a b {m}) a b t (toℕ-assoc-lt a b) (toℕ-assoc-mid a b) (toℕ-assoc-ge a b)

below-assoc⁻ : ∀ a b {m} (t : ℕ) → Below⁻ (a + b + t) (a + b + t) (assocSwapᵣ a b {m})
below-assoc⁻ a b {m} t = below-block⁻ (assocSwapᵣ a b {m}) a b t (toℕ-assoc-ge a b)

below-wk : ∀ (k : ℕ) {m} (t : ℕ) → Below t (k + t) (weaken* ⦃ Kᵣ ⦄ k {m})
below-wk k {m} t x px = subst (Nat._< k + t) (sym (toℕ-weaken*ᵣ k x)) (Nat.+-monoʳ-< k px)

below-wk⁻ : ∀ (k : ℕ) {m} (t : ℕ) → Below⁻ t (k + t) (weaken* ⦃ Kᵣ ⦄ k {m})
below-wk⁻ k {m} t x q = Nat.+-cancelˡ-< k (Fin.toℕ x) t (subst (Nat._< k + t) (toℕ-weaken*ᵣ k x) q)

------------------------------------------------------------------------
-- The channel invariant is preserved / reflected by bounded renamings.
------------------------------------------------------------------------

chanBelow-⋯ : ∀ {m n} {ρ : m →ᵣ n} (c : Tm m) → Below t₁ t₂ ρ →
              ChanBelow t₁ c → ChanBelow t₂ (c ⋯ ρ)
chanBelow-⋯ {ρ = ρ} c bρ (chanvar x px) = chanvar (ρ x) (bρ x px)

chanBelow-⋯⁻ : ∀ {m n} {ρ : m →ᵣ n} (c : Tm m) → Below⁻ t₁ t₂ ρ →
               ChanBelow t₂ (c ⋯ ρ) → ChanBelow t₁ c
chanBelow-⋯⁻ (` x)                    bρ (chanvar _ qy) = chanvar x (bρ x qy)
chanBelow-⋯⁻ (K _)                    bρ ()
chanBelow-⋯⁻ (ƛ _)                    bρ ()
chanBelow-⋯⁻ (μ _)                    bρ ()
chanBelow-⋯⁻ (_ ·⟨ _ ⟩ _)            bρ ()
chanBelow-⋯⁻ (_ ; _)               bρ ()
chanBelow-⋯⁻ (_ ⊗ _)                  bρ ()
chanBelow-⋯⁻ (`let _ `in _)           bρ ()
chanBelow-⋯⁻ (`let⊗ _ `in _)          bρ ()
chanBelow-⋯⁻ (`inj _ _)               bρ ()
chanBelow-⋯⁻ (`case _ `of⟨ _ ; _ ⟩) bρ ()

------------------------------------------------------------------------
-- Grounded is preserved / reflected by bounded renamings of processes.
------------------------------------------------------------------------

gr-⋯ₚ : ∀ {m n} {ρ : m →ᵣ n} (P : Proc m) → Below t₁ t₂ ρ →
        Grounded′ t₁ P → Grounded′ t₂ (P ⋯ₚ ρ)
gr-⋯ₚ ⟪ e ⟫     bρ _         = tt
gr-⋯ₚ (P ∥ Q)   bρ (gp , gq) = gr-⋯ₚ P bρ gp , gr-⋯ₚ Q bρ gq
gr-⋯ₚ (ν P)     bρ g         = gr-⋯ₚ P (↑-Below (↑-Below bρ)) g
gr-⋯ₚ (φ f c P) bρ (cb , g)  = chanBelow-⋯ c bρ cb , gr-⋯ₚ P (↑-Below bρ) g

gr-⋯ₚ⁻ : ∀ {m n} {ρ : m →ᵣ n} (P : Proc m) → Below⁻ t₁ t₂ ρ →
         Grounded′ t₂ (P ⋯ₚ ρ) → Grounded′ t₁ P
gr-⋯ₚ⁻ ⟪ e ⟫     bρ _         = tt
gr-⋯ₚ⁻ (P ∥ Q)   bρ (gp , gq) = gr-⋯ₚ⁻ P bρ gp , gr-⋯ₚ⁻ Q bρ gq
gr-⋯ₚ⁻ (ν P)     bρ g         = gr-⋯ₚ⁻ P (↑-Below⁻ (↑-Below⁻ bρ)) g
gr-⋯ₚ⁻ (φ f c P) bρ (cb , g)  = chanBelow-⋯⁻ c bρ cb , gr-⋯ₚ⁻ P (↑-Below⁻ bρ) g

------------------------------------------------------------------------
-- ≋′ preserves Grounded in both directions, hence ≋ does.  The gated
-- νφ-comm′ is where rigidity bites: the channel-scope gate (`c ⋯ weaken* 2`)
-- delivers the `2 +`-threshold bound that the strict inversion needs.
------------------------------------------------------------------------

gr′ : ∀ {n t} {P Q : Proc n} → P ≋′ Q → Grounded′ t P → Grounded′ t Q
gr′ ∥-comm′               (gp , gq)       = gq , gp
gr′ ∥-assoc′              (g1 , g2 , g3)  = (g1 , g2) , g3
gr′ ∥-unit′               (_ , gp)        = gp
gr′ (ν-swap′ {P = P})     g               = gr-⋯ₚ P (below-swap 1 1 _) g
gr′ (ν-comm′ {P = P})     g               = gr-⋯ₚ P (below-assoc 2 2 _) g
gr′ (φ-comm′ {P = P} {c = c} {d = d}) (cbc , cbd1 , gp) =
      chanBelow-⋯⁻ d (below-wk⁻ 1 _) cbd1
    , chanBelow-⋯ c (below-wk 1 _) cbc
    , gr-⋯ₚ P (below-assoc 1 1 _) gp
gr′ (νφ-comm′ {c = c} {P = P}) (cb2 , gp) =
      chanBelow-⋯⁻ c (below-wk⁻ 2 _) cb2
    , gr-⋯ₚ P (below-assoc 1 2 _) gp
gr′ (ν-ext′ {P = P})      (gp , gq)       = gr-⋯ₚ P (below-wk 2 _) gp , gq
gr′ (φ-ext′ {P = P})      (gp , cbc , gq) = cbc , gr-⋯ₚ P (below-wk 1 _) gp , gq
gr′ (∥-cong′ r)           (gp , gq)       = gr′ r gp , gq
gr′ (ν-cong′ r)           g               = gr′ r g
gr′ (φ-cong′ r)           (cb , g)        = cb , gr′ r g

gr′⁻ : ∀ {n t} {P Q : Proc n} → P ≋′ Q → Grounded′ t Q → Grounded′ t P
gr′⁻ ∥-comm′               (gq , gp)          = gp , gq
gr′⁻ ∥-assoc′              ((g1 , g2) , g3)   = g1 , g2 , g3
gr′⁻ ∥-unit′               gp                 = tt , gp
gr′⁻ (ν-swap′ {P = P})     g                  = gr-⋯ₚ⁻ P (below-swap⁻ 1 1 _) g
gr′⁻ (ν-comm′ {P = P})     g                  = gr-⋯ₚ⁻ P (below-assoc⁻ 2 2 _) g
gr′⁻ (φ-comm′ {P = P} {c = c} {d = d}) (cbd , cbc1 , gp) =
      chanBelow-⋯⁻ c (below-wk⁻ 1 _) cbc1
    , chanBelow-⋯ d (below-wk 1 _) cbd
    , gr-⋯ₚ⁻ P (below-assoc⁻ 1 1 _) gp
gr′⁻ (νφ-comm′ {c = c} {P = P}) (cb , gp)     =
      chanBelow-⋯ c (below-wk 2 _) cb
    , gr-⋯ₚ⁻ P (below-assoc⁻ 1 2 _) gp
gr′⁻ (ν-ext′ {P = P})      (gp , gq)          = gr-⋯ₚ⁻ P (below-wk⁻ 2 _) gp , gq
gr′⁻ (φ-ext′ {P = P})      (cbc , gp , gq)    = gr-⋯ₚ⁻ P (below-wk⁻ 1 _) gp , cbc , gq
gr′⁻ (∥-cong′ r)           (gp , gq)          = gr′⁻ r gp , gq
gr′⁻ (ν-cong′ r)           g                  = gr′⁻ r g
gr′⁻ (φ-cong′ r)           (cb , g)           = cb , gr′⁻ r g

gr : ∀ {n t} {P Q : Proc n} → P ≋ Q → Grounded′ t P → Grounded′ t Q
gr ε           g = g
gr (fwd r ◅ c) g = gr c (gr′ r g)
gr (bwd r ◅ c) g = gr c (gr′⁻ r g)

------------------------------------------------------------------------
-- PAYOFF: Grounded ⇒ not φ-headed, and it is a ≋-invariant.
------------------------------------------------------------------------

φHead : Proc n → Set
φHead (φ _ _ _) = ⊤
φHead _         = ⊥

grounded-¬φHead : (P : Proc n) → Grounded P → ¬ φHead P
grounded-¬φHead ⟪ e ⟫     _                   ()
grounded-¬φHead (P ∥ Q)   _                   ()
grounded-¬φHead (ν P)     _                   ()
grounded-¬φHead (φ f c P) (chanvar x () , _)

image-stays-¬φHead : (P Q : Proc n) → Grounded P → P ≋ Q → ¬ φHead Q
image-stays-¬φHead P Q gP r = grounded-¬φHead Q (gr r gP)

------------------------------------------------------------------------
-- U-Grounded: every translation image is Grounded.  Each φ-cell UB[_]
-- emits guards `` ` x `` with x an internally-bound handle (0F / 1F under
-- the ν, shifted up as the φ-nest grows), so the whole image is Grounded.
------------------------------------------------------------------------

subst-Grounded : ∀ {a b} (t : ℕ) (eq : a ≡ b) (X : Proc a) →
                 Grounded′ t X → Grounded′ t (subst Proc eq X)
subst-Grounded t refl X g = g

Grounded-thr : ∀ {n} {a b : ℕ} → a ≡ b → (X : Proc n) → Grounded′ a X → Grounded′ b X
Grounded-thr refl X g = g

UB-Grounded : ∀ {n} (t : ℕ) (B : 𝐓.BindGroup) {e₁ : Tm n} (x : 𝔽 n) {e₂ : Tm n}
              (f : (sum B →ₛ syncs B + n) → Proc (syncs B + n)) →
              Fin.toℕ x Nat.< t →
              ((σ : sum B →ₛ syncs B + n) → Grounded′ (syncs B + t) (f σ)) →
              Grounded′ t (UB[ B ] (e₁ , x , e₂) f)
UB-Grounded t []              x f px hf = hf λ()
UB-Grounded t (b ∷ [])        x f px hf = hf (Ub[ b + 0 ] (_ , x , _))
UB-Grounded {n} t (b ∷ B@(_ ∷ _)) {e₁ = e₁} x f px hf =
    chanvar x px
  , UB-Grounded (1 + t) B (Fin.suc x) _ (Nat.s≤s px)
      (λ σ →
        let σ″ : sum (b ∷ B) →ₛ syncs (b ∷ B) + n
            σ″ = λ y → subst Tm (+-suc (syncs B) n)
                         ([ Ub[ b ] (wk e₁ , Fin.suc x , ` 0F) ·ₖ weaken* (syncs B)
                          , σ ]′ (splitAt b y))
        in Grounded-thr (sym (+-suc (syncs B) t))
             (subst Proc (sym (+-suc (syncs B) n)) (f σ″))
             (subst-Grounded (suc (syncs B + t)) (sym (+-suc (syncs B) n)) (f σ″) (hf σ″)))

U-Grounded : ∀ {m n} (t : ℕ) (P : 𝐓.Proc m) (σ : m →ₛ n) → Grounded′ t (U[ P ] σ)
U-Grounded t 𝐓.⟪ e ⟫    σ = tt
U-Grounded t (P 𝐓.∥ Q)  σ = U-Grounded t P σ , U-Grounded t Q σ
U-Grounded t (𝐓.ν B₁ B₂ P) σ =
  UB-Grounded (2 + t) B₁ 0F _ (Nat.s≤s Nat.z≤n)
    (λ σ₁ → UB-Grounded (syncs B₁ + (2 + t)) B₂ (weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F) _
              (subst (Nat._< syncs B₁ + (2 + t)) (sym (toℕ-weaken*ᵣ (syncs B₁) 1F))
                     (Nat.+-monoʳ-< (syncs B₁) (Nat.s≤s (Nat.s≤s Nat.z≤n))))
              (λ σ₂ → U-Grounded (syncs B₂ + (syncs B₁ + (2 + t))) P _))
