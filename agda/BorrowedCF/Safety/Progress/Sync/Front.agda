-- | The FRONT KIND of a session type, and its behaviour under duality.
--
--   `Types/AtomCons.agda` peels a leading ATOM off a session (`Cons a w z`,
--   `atom-;-cons`), but it is defined only for closed atoms other than `msg`
--   (the payload of a `msg` moves under `_≃_`) and it cannot speak about a
--   leading `brn` at all: `Types/Atoms.agda` says so explicitly, its `Cat`
--   relation has a `brn` constructor but the `_≃_` transport for it was
--   abandoned.  Process progress needs precisely the missing cases: at a
--   synchronising `ν` the two head handles carry `msg`, `brn` or `end`, and
--   the point is that the two KINDS are dual.
--
--   `ConsK hk₁ w` below is the front-peel with the *payload and the branches
--   forgotten*: it records only that `w` starts with a `msg p`, a `brn p` or
--   an `end p`.  Dropping the payload is what makes the development go
--   through where `AtomCons` stops -- `≃𝕊-msg` rewrites the payload but not
--   the kind, and `≃𝕊-brn₁/₂`/`≃𝕊-distr` rewrite the branches but not the
--   polarity -- and dropping the suffix removes every `subst` from the
--   substitution lemmas.  What is left is
--
--     * `≃-consK`, the transport along `_≃_` (the μ step, `consK-unfold⁻¹`,
--       is the only real work, and it is the mirror of `AtomCons`'s
--       `cons-unfold⁻¹` without the atom bookkeeping);
--     * `consK-unique`, the front kind is unique;
--     * `consK-dual`, duality flips it;
--     * `front-dual`, THE PAYOFF: the two endpoints of one `ν` present dual
--       front kinds.
--
--   Owner: agent G2.
module BorrowedCF.Safety.Progress.Sync.Front where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence

open Nat.Variables

private variable
  w w₁ w₂ z : 𝕊 n

------------------------------------------------------------------------
-- 1.  Head kinds.

data HKind : Set where
  kmsg : Pol → HKind
  kbrn : Pol → HKind
  kend : Pol → HKind

dualKind : HKind → HKind
dualKind (kmsg p) = kmsg (dualPol p)
dualKind (kbrn p) = kbrn (dualPol p)
dualKind (kend p) = kend (dualPol p)

dualKind-involutive : (k : HKind) → dualKind (dualKind k) ≡ k
dualKind-involutive (kmsg p) = cong kmsg (dualPol-involutive p)
dualKind-involutive (kbrn p) = cong kbrn (dualPol-involutive p)
dualKind-involutive (kend p) = cong kend (dualPol-involutive p)

------------------------------------------------------------------------
-- 2.  `ConsK hk₁ w`: `w` starts with a head of kind `k`.

data ConsK {n} : HKind → 𝕊 n → Set where
  hmsg : ConsK (kmsg p) (msg p T)
  hbrn : ConsK (kbrn p) (brn p s₁ s₂)
  hend : ConsK (kend p) (end p)
  hd   : ∀ {hk₁} → ConsK hk₁ s₁ → ConsK hk₁ (s₁ ; s₂)
  tl   : ∀ {hk₁} → Skips s₁ → ConsK hk₁ s₂ → ConsK hk₁ (s₁ ; s₂)
  mu   : ∀ {hk₁} {s : 𝕊 (suc n)} → ConsK hk₁ s → ConsK hk₁ (mu s)

private variable hk₁ hk₂ hk₃ : HKind

-- A skipping session has no head.
skips⊥consK : Skips w → ConsK hk₁ w → ⊥
skips⊥consK (Sk₁ ; Sk₂) (hd c)   = skips⊥consK Sk₁ c
skips⊥consK (Sk₁ ; Sk₂) (tl _ c) = skips⊥consK Sk₂ c
skips⊥consK (mu Sk)    (mu c)   = skips⊥consK Sk c

-- The head kind is unique.
consK-unique : ConsK hk₁ w → ConsK hk₂ w → hk₁ ≡ hk₂
consK-unique hmsg hmsg = ≡.refl
consK-unique hbrn hbrn = ≡.refl
consK-unique hend hend = ≡.refl
consK-unique (hd c₁) (hd c₂) = consK-unique c₁ c₂
consK-unique (hd c₁) (tl Sk c₂) = ⊥-elim (skips⊥consK Sk c₁)
consK-unique (tl Sk c₁) (hd c₂) = ⊥-elim (skips⊥consK Sk c₂)
consK-unique (tl _ c₁) (tl _ c₂) = consK-unique c₁ c₂
consK-unique (mu c₁) (mu c₂) = consK-unique c₁ c₂

-- Peeling a `_;_`.
consK-;⁻ : ConsK hk₁ (s₁ ; s₂) → ConsK hk₁ s₁ ⊎ (Skips s₁ × ConsK hk₁ s₂)
consK-;⁻ (hd c) = inj₁ c
consK-;⁻ (tl Sk c) = inj₂ (Sk , c)

-- Duality flips the head kind.
consK-dual : ConsK hk₁ w → ConsK (dualKind hk₁) (dual w)
consK-dual hmsg = hmsg
consK-dual hbrn = hbrn
consK-dual hend = hend
consK-dual (hd c) = hd (consK-dual c)
consK-dual (tl Sk c) = tl (skips-dual⁺ Sk) (consK-dual c)
consK-dual (mu c) = mu (consK-dual c)

------------------------------------------------------------------------
-- 3.  Substitution.

consK-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → ConsK hk₁ s → ConsK hk₁ (s ⋯ ϕ)
consK-⋯ hmsg = hmsg
consK-⋯ hbrn = hbrn
consK-⋯ hend = hend
consK-⋯ (hd c) = hd (consK-⋯ c)
consK-⋯ (tl Sk c) = tl (skips-⋯ Sk) (consK-⋯ c)
consK-⋯ (mu c) = mu (consK-⋯ c)

consK-⋯ᵣ⁻¹ : {ρ : m →ᵣ n} (s : 𝕊 m) → ConsK hk₁ (s ⋯ ρ) → ConsK hk₁ s
consK-⋯ᵣ⁻¹ (` x) ()
consK-⋯ᵣ⁻¹ (msg p t) hmsg = hmsg
consK-⋯ᵣ⁻¹ (brn p s₁ s₂) hbrn = hbrn
consK-⋯ᵣ⁻¹ (end p) hend = hend
consK-⋯ᵣ⁻¹ (s₁ ; s₂) (hd c) = hd (consK-⋯ᵣ⁻¹ s₁ c)
consK-⋯ᵣ⁻¹ (s₁ ; s₂) (tl Sk c) = tl (skips-⋯ᵣ⁻¹ Sk) (consK-⋯ᵣ⁻¹ s₂ c)
consK-⋯ᵣ⁻¹ (mu s) (mu c) = mu (consK-⋯ᵣ⁻¹ s c)

-- The backward direction: either the head comes from `s`, or `s` starts with
-- a variable and the head comes from that variable's image.
consK-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} (s : 𝕊 m) →
  ConsK hk₁ (s ⋯ ϕ) → (∀ x → ¬ Skips (`/id (ϕ x))) →
  ConsK hk₁ s ⊎ ∃[ y ] ConsK hk₁ (`/id (ϕ y))
consK-⋯⁻¹ (` x) c ∀¬Sk = inj₂ (x , c)
consK-⋯⁻¹ (msg p t) hmsg ∀¬Sk = inj₁ hmsg
consK-⋯⁻¹ (brn p s₁ s₂) hbrn ∀¬Sk = inj₁ hbrn
consK-⋯⁻¹ (end p) hend ∀¬Sk = inj₁ hend
consK-⋯⁻¹ (s₁ ; s₂) (hd c) ∀¬Sk =
  Sum.map hd id (consK-⋯⁻¹ s₁ c ∀¬Sk)
consK-⋯⁻¹ (s₁ ; s₂) (tl Sk c) ∀¬Sk =
  Sum.map (tl (skips-⋯⁻¹ Sk ∀¬Sk)) id (consK-⋯⁻¹ s₂ c ∀¬Sk)
consK-⋯⁻¹ ⦃ K ⦄ {ϕ = ϕ} (mu s) (mu c) ∀¬Sk
  with consK-⋯⁻¹ s c ∀¬Sk′
  where
  ∀¬Sk′ : ∀ x → ¬ Skips (`/id ((ϕ ↑) x))
  ∀¬Sk′ zero = ¬skips-`/` K
  ∀¬Sk′ (suc x) = ∀¬Sk x ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ x)))
... | inj₁ c₀ = inj₁ (mu c₀)
... | inj₂ (zero , c₀) =
  ⊥-elim (case subst (ConsK _) (`/`-is-` ⦃ K ⦄ zero) c₀ of λ ())
... | inj₂ (suc y , c₀) =
  inj₂ (y , consK-⋯ᵣ⁻¹ (`/id (ϕ y)) (subst (ConsK _) (sym (wk-`/id (ϕ y))) c₀))

------------------------------------------------------------------------
-- 4.  Unfolding.

consK-unfold : ConsK hk₁ (mu s) → ConsK hk₁ (unfold s)
consK-unfold (mu c) = consK-⋯ c

private
  ¬skips-⦅mu⦆ : (s : 𝕊 (suc n)) → ¬ Skips s → ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
  ¬skips-⦅mu⦆ s ¬Ss zero (mu Sk) = ¬Ss Sk
  ¬skips-⦅mu⦆ s ¬Ss (suc x) = ¬skips-`

consK-unfold⁻¹ : {s : 𝕊 (suc n)} → ConsK hk₁ (unfold s) → ConsK hk₁ (mu s)
consK-unfold⁻¹ {s = s} c with skips? s
... | yes Ss = ⊥-elim (skips⊥consK (skips-⋯ Ss) c)
... | no ¬Ss with consK-⋯⁻¹ s c (¬skips-⦅mu⦆ s ¬Ss)
...   | inj₁ c₀ = mu c₀
...   | inj₂ (zero , c₀) = c₀
...   | inj₂ (suc y , c₀) = case c₀ of λ ()

------------------------------------------------------------------------
-- 5.  Transport along `_≃_`.

≃-consK : w₁ ≃ w₂ → ConsK hk₁ w₁ → ConsK hk₁ w₂
≃-consK refl c = c
≃-consK (x ◅ xs) c = ≃-consK xs (go x c)
  where
  go : SymClosure _≃𝕊_ w₁ w₂ → ConsK hk₁ w₁ → ConsK hk₁ w₂
  go (fwd (≃𝕊-;₁ x)) (hd c) = hd (go (fwd x) c)
  go (fwd (≃𝕊-;₁ x)) (tl Sk c) = tl (≃-skips (Eq*.return x) Sk) c
  go (bwd (≃𝕊-;₁ x)) (hd c) = hd (go (bwd x) c)
  go (bwd (≃𝕊-;₁ x)) (tl Sk c) = tl (≃-skips (≃-sym (Eq*.return x)) Sk) c
  go (fwd (≃𝕊-;₂ x)) (hd c) = hd c
  go (fwd (≃𝕊-;₂ x)) (tl Sk c) = tl Sk (go (fwd x) c)
  go (bwd (≃𝕊-;₂ x)) (hd c) = hd c
  go (bwd (≃𝕊-;₂ x)) (tl Sk c) = tl Sk (go (bwd x) c)
  go (fwd ≃𝕊-skipˡ) (hd ())
  go (fwd ≃𝕊-skipˡ) (tl _ c) = c
  go (bwd ≃𝕊-skipˡ) c = tl skip c
  go (fwd ≃𝕊-skipʳ) (hd c) = c
  go (fwd ≃𝕊-skipʳ) (tl _ ())
  go (bwd ≃𝕊-skipʳ) c = hd c
  go (fwd ≃𝕊-μ) c = consK-unfold c
  go (bwd ≃𝕊-μ) c = consK-unfold⁻¹ c
  go (fwd ≃𝕊-assoc) (hd (hd c)) = hd c
  go (fwd ≃𝕊-assoc) (hd (tl Sk c)) = tl Sk (hd c)
  go (fwd ≃𝕊-assoc) (tl (Sk₁ ; Sk₂) c) = tl Sk₁ (tl Sk₂ c)
  go (bwd ≃𝕊-assoc) (hd c) = hd (hd c)
  go (bwd ≃𝕊-assoc) (tl Sk (hd c)) = hd (tl Sk c)
  go (bwd ≃𝕊-assoc) (tl Sk₁ (tl Sk₂ c)) = tl (Sk₁ ; Sk₂) c
  go (fwd ≃𝕊-distr) (hd hbrn) = hbrn
  go (fwd ≃𝕊-distr) (tl () _)
  go (bwd ≃𝕊-distr) hbrn = hd hbrn
  go (fwd (≃𝕊-msg x)) hmsg = hmsg
  go (bwd (≃𝕊-msg x)) hmsg = hmsg
  go (fwd (≃𝕊-brn₁ x)) hbrn = hbrn
  go (bwd (≃𝕊-brn₁ x)) hbrn = hbrn
  go (fwd (≃𝕊-brn₂ x)) hbrn = hbrn
  go (bwd (≃𝕊-brn₂ x)) hbrn = hbrn

------------------------------------------------------------------------
-- 6.  THE PAYOFF: the two endpoints of a restriction present dual heads.

front-dual : {s : 𝕊 0} {p : Pol} →
  ConsK hk₁ (s ; end p) → ConsK hk₂ (dual s ; end (dualPol p)) → hk₂ ≡ dualKind hk₁
front-dual {hk₁ = hk₁} {hk₂ = hk₂} {s = s} {p = p} c₁ c₂ =
  sym (dualKind-involutive hk₂) ■ sym (cong dualKind (consK-unique c₁ c₂′))
  where
  c₂′ : ConsK (dualKind hk₂) (s ; end p)
  c₂′ = subst (ConsK (dualKind hk₂))
          (cong₂ _;_ (dual-involutive s) (cong end (dualPol-involutive p)))
          (consK-dual c₂)
