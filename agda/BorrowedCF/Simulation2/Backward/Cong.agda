-- | Reverse structural-congruence reflection for the backward simulation.
--
--   GOAL.  Reflect an untyped ≋ between a process R and a translation image
--   U[ P ] σ back to R being ITSELF an image U[ P† ] σ of a typed-≋-related
--   source P†, so that the non-ε RU-Struct engine of `sim←` (Backward.agda) can
--   consume a ≋-link off the U[ P ] σ end instead of transporting the reduction
--   across it (the non-terminating naïve route, RevPhiNest).
--
--   WHAT IS AND IS NOT REFLECTABLE.
--     • The associative–commutative ∥-fragment {∥-comm′, ∥-assoc′, ∥-cong′} of
--       the untyped congruence reflects STRICTLY and in BOTH directions: the
--       head of an image determines the head of the source (Inversions), and
--       U[_] is a ∥-homomorphism, so every ∥-rearrangement of an image is again
--       an image of the same ∥-rearrangement of the source.  This is closed
--       here, hole-free, as `reverse-U-◈` over `_◈_ = EqClosure _◈′_`.
--     • `∥-unit′` reflects only in the INTRODUCTION direction (⟪unit⟫ appears on
--       the R side).  The ELIMINATION direction (⟪unit⟫ on the image side) is
--       NOT reflectable: U[ Pl ] σ ≡ ⟪ K `unit ⟫ forces only  Pl ≡ ⟪ e₀ ⟫ with
--       e₀ ⋯ σ ≡ K `unit, and under a value substitution (VSub ϕ = ∀ x → Value
--       (`/id (ϕ x)), Reduction.Base) a variable MAY map to the value K `unit
--       (V-K), so e₀ need not be K `unit and ⟪ e₀ ⟫ ∥ Pr ≋ Pr is not a typed
--       congruence.  It is therefore excluded from `_◈′_`.
--     • The ν-links {ν-swap′, ν-comm′, ν-ext′, ν-cong′} are ν-headed on images
--       (U[ ν … ] σ is always ν-headed, the φ-telescope sits INSIDE the ν), but
--       reflecting them recurses into the φ-telescope body UB[ B ] …, which is
--       φ-headed as soon as syncs B ≥ 1 — the same φ obstruction below.  They
--       reflect only over φ-free bind groups (syncs ≡ 0), a source-shape side
--       condition not expressible on a bare untyped `_◈′_`; they are handled
--       elsewhere (simRes, U-ν-φfree-eq) and excluded here.
--     • The φ-permutation links {φ-comm′, νφ-comm′, φ-ext′} are genuinely
--       IRREDUCIBLE: `νφ-comm′` sends an image to a φ-headed process that is NOT
--       any image (machine-refuted in Simulation.RevUCong: U-not-φ /
--       U-≋-escapes).  No reflection exists for them.
module BorrowedCF.Simulation2.Backward.Cong where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Simulation2.Backward.Inversions using (inv-U-∥)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

-- ── The reflectable fragment: associative–commutative ∥-rearrangement ──
--   (a genuine sub-congruence of the untyped ≋ — see ◈′⇒≋′ / ◈⇒≋ below).

infix 4 _◈′_

data _◈′_ {n} : Rel (UP.Proc n) 0ℓ where
  ∥-comm′  : ∀ {P Q}      → (P UP.∥ Q) ◈′ (Q UP.∥ P)
  ∥-assoc′ : ∀ {P₁ P₂ P₃} → (P₁ UP.∥ (P₂ UP.∥ P₃)) ◈′ ((P₁ UP.∥ P₂) UP.∥ P₃)
  ∥-cong′  : ∀ {P₁ P₂ Q}  → P₁ ◈′ P₂ → (P₁ UP.∥ Q) ◈′ (P₂ UP.∥ Q)

infix 4 _◈_

_◈_ : ∀ {n} → Rel (UP.Proc n) 0ℓ
_◈_ = Eq*.EqClosure _◈′_

-- `_◈_` is a sub-relation of the full untyped structural congruence `_≋_`.
◈′⇒≋′ : ∀ {n} {P Q : UP.Proc n} → P ◈′ Q → P UP.≋′ Q
◈′⇒≋′ ∥-comm′     = UP.∥-comm′
◈′⇒≋′ ∥-assoc′    = UP.∥-assoc′
◈′⇒≋′ (∥-cong′ d) = UP.∥-cong′ (◈′⇒≋′ d)

◈⇒≋ : ∀ {n} {P Q : UP.Proc n} → P ◈ Q → P UP.≋ Q
◈⇒≋ = Eq*.gmap (λ z → z) ◈′⇒≋′

-- ── Single-step reflection, both directions ──
--   ◈-refl-r : image on the RIGHT of the ◈′-step; ◈-refl-l : on the LEFT.

◈-refl-r : ∀ {m n} {σ : m →ₛ n} {R Y : UP.Proc n} (P : TP.Proc m)
         → R ◈′ Y → Y ≡ U[ P ] σ
         → Σ[ P† ∈ TP.Proc m ] (P TP.≋ P† × R ≡ U[ P† ] σ)
◈-refl-l : ∀ {m n} {σ : m →ₛ n} {R Y : UP.Proc n} (P : TP.Proc m)
         → Y ◈′ R → Y ≡ U[ P ] σ
         → Σ[ P† ∈ TP.Proc m ] (P TP.≋ P† × R ≡ U[ P† ] σ)

◈-refl-r {σ = σ} P (∥-comm′ {P = Pa} {Q = Qa}) eq
  with P₁ , P₂ , P≡ , Qa≡ , Pa≡ ← inv-U-∥ P σ (sym eq) =
  P₂ TP.∥ P₁
  , subst (λ z → z TP.≋ (P₂ TP.∥ P₁)) (sym P≡) TP.∥-comm
  , cong₂ UP._∥_ Pa≡ Qa≡
◈-refl-r {σ = σ} P (∥-assoc′ {P₁ = A} {P₂ = B} {P₃ = C}) eq
  with X , Pc , P≡ , AB≡ , C≡ ← inv-U-∥ P σ (sym eq)
  with Pa , Pb , X≡ , A≡ , B≡ ← inv-U-∥ X σ (sym AB≡) =
  Pa TP.∥ (Pb TP.∥ Pc)
  , subst (λ z → z TP.≋ (Pa TP.∥ (Pb TP.∥ Pc)))
          (sym (≡.trans P≡ (cong (TP._∥ Pc) X≡)))
          (Eq*.symmetric _ TP.∥-assoc)
  , cong₂ UP._∥_ A≡ (cong₂ UP._∥_ B≡ C≡)
◈-refl-r {σ = σ} P (∥-cong′ {Q = Q} d) eq
  with Pb , Pq , P≡ , B≡ , Q≡ ← inv-U-∥ P σ (sym eq)
  with Pb† , Pb≋ , A≡ ← ◈-refl-r Pb d B≡ =
  Pb† TP.∥ Pq
  , subst (λ z → z TP.≋ (Pb† TP.∥ Pq)) (sym P≡) (TP.∥-cong Pb≋ ε)
  , cong₂ UP._∥_ A≡ Q≡

◈-refl-l {σ = σ} P (∥-comm′ {P = Pa} {Q = Qa}) eq
  with P₁ , P₂ , P≡ , Pa≡ , Qa≡ ← inv-U-∥ P σ (sym eq) =
  P₂ TP.∥ P₁
  , subst (λ z → z TP.≋ (P₂ TP.∥ P₁)) (sym P≡) TP.∥-comm
  , cong₂ UP._∥_ Qa≡ Pa≡
◈-refl-l {σ = σ} P (∥-assoc′ {P₁ = A} {P₂ = B} {P₃ = C}) eq
  with Pa , Pt , P≡ , A≡ , BC≡ ← inv-U-∥ P σ (sym eq)
  with Pb , Pc , Pt≡ , B≡ , C≡ ← inv-U-∥ Pt σ (sym BC≡) =
  (Pa TP.∥ Pb) TP.∥ Pc
  , subst (λ z → z TP.≋ ((Pa TP.∥ Pb) TP.∥ Pc))
          (sym (≡.trans P≡ (cong (Pa TP.∥_) Pt≡)))
          TP.∥-assoc
  , cong₂ UP._∥_ (cong₂ UP._∥_ A≡ B≡) C≡
◈-refl-l {σ = σ} P (∥-cong′ {Q = Q} d) eq
  with Pa , Pq , P≡ , A≡ , Q≡ ← inv-U-∥ P σ (sym eq)
  with Pa† , Pa≋ , B≡ ← ◈-refl-l Pa d A≡ =
  Pa† TP.∥ Pq
  , subst (λ z → z TP.≋ (Pa† TP.∥ Pq)) (sym P≡) (TP.∥-cong Pa≋ ε)
  , cong₂ UP._∥_ B≡ Q≡

-- ── One symmetric-closure link ──

reflect1 : ∀ {m n} {σ : m →ₛ n} {R Y : UP.Proc n} (P : TP.Proc m)
         → SymClosure _◈′_ R Y → Y ≡ U[ P ] σ
         → Σ[ P† ∈ TP.Proc m ] (P TP.≋ P† × R ≡ U[ P† ] σ)
reflect1 P (fwd d) eq = ◈-refl-r P d eq
reflect1 P (bwd d) eq = ◈-refl-l P d eq

-- ── The whole chain, folded from the U[ P ] σ end ──

reflectStar : ∀ {m n} {σ : m →ₛ n} {R Y : UP.Proc n} (P : TP.Proc m)
            → Star (SymClosure _◈′_) R Y → Y ≡ U[ P ] σ
            → Σ[ P† ∈ TP.Proc m ] (P TP.≋ P† × R ≡ U[ P† ] σ)
reflectStar P ε        eq = P , ε , eq
reflectStar P (s ◅ rest) eq
  with P₁ , P≋P₁ , y≡ ← reflectStar P rest eq
  with P₂ , P₁≋P₂ , R≡ ← reflect1 P₁ s y≡ =
  P₂ , P≋P₁ ◅◅ P₁≋P₂ , R≡

-- ── Public entry: the reflectable form of reverse-U-≋ ──
--
--   reverse-U-◈ : R ◈ U[ P ] σ
--               → Σ[ P† ] (P TP.≋ P† × R ≡ U[ P† ] σ)
--
--   Feed the RU-Struct engine a ≋-link that lives in the reflectable fragment
--   `_◈_` (∥ associativity/commutativity/congruence); it returns a rearranged
--   SOURCE P† with a typed ≋ witness and a STRICT image equation R ≡ U[ P† ] σ,
--   so `sim←ᵍ` can recurse on the image of P† directly.

reverse-U-◈ : ∀ {m n} {σ : m →ₛ n} {P : TP.Proc m} {R : UP.Proc n}
            → R ◈ U[ P ] σ
            → Σ[ P† ∈ TP.Proc m ] (P TP.≋ P† × R ≡ U[ P† ] σ)
reverse-U-◈ {P = P} chain = reflectStar P chain refl
