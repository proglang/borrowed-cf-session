-- | ContainsEnd (HasT): a session "contains an end or ret atom somewhere".
--   These are exactly the TERMINAL atoms that Bounded introduces and New
--   forbids, so `bounded⇒hasT` and `new⇒¬hasT` are duals, and HasT is
--   ~-invariant (`≃-hasT`).  This is the long-missing ends lemma: it lets a
--   Bounded prefix contradict a New continuation across ANY session
--   equivalence (see Backward.ComBackwardFails.bad), replacing the finite
--   atom-;-unsnoc cascade that only worked for a fixed com session.
module BorrowedCF.Types.ContainsEnd where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Syntax
import BorrowedCF.Types.Predicates as P

open Bin using (_Respects_)
open Nat.Variables

------------------------------------------------------------------------
-- HasT : contains a terminal (end / ret) atom.
------------------------------------------------------------------------

data HasT {n} : 𝕊 n → Set where
  end  : HasT (end p)
  ret  : HasT ret
  seqˡ : HasT s₁ → HasT (s₁ ; s₂)
  seqʳ : HasT s₂ → HasT (s₁ ; s₂)
  mu   : HasT s → HasT (mu s)
  brnˡ : HasT s₁ → HasT (brn p s₁ s₂)
  brnʳ : HasT s₂ → HasT (brn p s₁ s₂)

¬hasT-var : {x : 𝔽 n} → ¬ (HasT (` x))
¬hasT-var ()

hasT-mu⁻ : HasT (mu s) → HasT s
hasT-mu⁻ (mu h) = h

------------------------------------------------------------------------
-- Bounded => HasT ;  New => ~ HasT   (the two-sided characterisation).
------------------------------------------------------------------------

bounded⇒hasT : P.Bounded s → HasT s
bounded⇒hasT P.end = end
bounded⇒hasT P.ret = ret
bounded⇒hasT (P._;₁_ B _) = seqˡ (bounded⇒hasT B)
bounded⇒hasT (P.-;₂_ B)   = seqʳ (bounded⇒hasT B)
bounded⇒hasT (P.mu B)     = mu (bounded⇒hasT B)
bounded⇒hasT (P.brn B1 _) = brnˡ (bounded⇒hasT B1)

new⇒¬hasT : P.New s → ¬ (HasT s)
new⇒¬hasT P.`- ()
new⇒¬hasT P.msg ()
new⇒¬hasT P.skip ()
new⇒¬hasT (P._;_ N1 _) (seqˡ h) = new⇒¬hasT N1 h
new⇒¬hasT (P._;_ _ N2) (seqʳ h) = new⇒¬hasT N2 h
new⇒¬hasT (P.mu N)     (mu h)   = new⇒¬hasT N h
new⇒¬hasT (P.brn N1 _) (brnˡ h) = new⇒¬hasT N1 h
new⇒¬hasT (P.brn _ N2) (brnʳ h) = new⇒¬hasT N2 h

------------------------------------------------------------------------
-- HasT under substitution: preserved forward (no var leaves), and
-- reflected by renaming.  Both are structural (HasT never touches a var).
------------------------------------------------------------------------

hasT-⋯ : ⦃ K : Kit 𝓕 ⦄ → ⦃ W : WkKit K ⦄ → {ϕ : m –[ K ]→ n} → HasT s → HasT (s ⋯ ϕ)
hasT-⋯ end = end
hasT-⋯ ret = ret
hasT-⋯ (seqˡ h) = seqˡ (hasT-⋯ h)
hasT-⋯ (seqʳ h) = seqʳ (hasT-⋯ h)
hasT-⋯ (mu h)   = mu (hasT-⋯ h)
hasT-⋯ (brnˡ h) = brnˡ (hasT-⋯ h)
hasT-⋯ (brnʳ h) = brnʳ (hasT-⋯ h)

hasT-⋯ᵣ⁻¹ : {rho : m →ᵣ n} → HasT (s ⋯ rho) → HasT s
hasT-⋯ᵣ⁻¹ {s = end p} end = end
hasT-⋯ᵣ⁻¹ {s = ret} ret = ret
hasT-⋯ᵣ⁻¹ {s = s₁ ; s₂} (seqˡ h) = seqˡ (hasT-⋯ᵣ⁻¹ h)
hasT-⋯ᵣ⁻¹ {s = s₁ ; s₂} (seqʳ h) = seqʳ (hasT-⋯ᵣ⁻¹ h)
hasT-⋯ᵣ⁻¹ {s = mu s} (mu h) = mu (hasT-⋯ᵣ⁻¹ h)
hasT-⋯ᵣ⁻¹ {s = brn p s₁ s₂} (brnˡ h) = brnˡ (hasT-⋯ᵣ⁻¹ h)
hasT-⋯ᵣ⁻¹ {s = brn p s₁ s₂} (brnʳ h) = brnʳ (hasT-⋯ᵣ⁻¹ h)

hasT-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ → ⦃ W : WkKit K ⦄ → {ϕ : m –[ K ]→ n} {s : 𝕊 m} →
  HasT (s ⋯ ϕ) → HasT s ⊎ (Σ[ x ∈ 𝔽 m ] HasT (`/id (ϕ x)))
hasT-⋯⁻¹ {s = ` x} h = inj₂ (x , h)
hasT-⋯⁻¹ {s = end p} end = inj₁ end
hasT-⋯⁻¹ {s = ret} ret = inj₁ ret
hasT-⋯⁻¹ {s = s₁ ; s₂} (seqˡ h) = Sum.map seqˡ id (hasT-⋯⁻¹ {s = s₁} h)
hasT-⋯⁻¹ {s = s₁ ; s₂} (seqʳ h) = Sum.map seqʳ id (hasT-⋯⁻¹ {s = s₂} h)
hasT-⋯⁻¹ {s = brn p s₁ s₂} (brnˡ h) = Sum.map brnˡ id (hasT-⋯⁻¹ {s = s₁} h)
hasT-⋯⁻¹ {s = brn p s₁ s₂} (brnʳ h) = Sum.map brnʳ id (hasT-⋯⁻¹ {s = s₂} h)
hasT-⋯⁻¹ ⦃ K ⦄ ⦃ W ⦄ {s = mu s0} (mu h) with hasT-⋯⁻¹ {s = s0} h
... | inj₁ hs = inj₁ (mu hs)
... | inj₂ (zero , hz)  = ⊥-elim (¬hasT-var (subst HasT (`/`-is-` ⦃ K ⦄ _) hz))
... | inj₂ (suc y , hy) = inj₂ (y , hasT-⋯ᵣ⁻¹ (subst HasT (sym (wk-`/id _)) hy))

------------------------------------------------------------------------
-- HasT respects unfolding (the mu equation) in the reflecting direction.
------------------------------------------------------------------------

hasT-unfold⁻¹ : HasT (unfold s) → HasT s
hasT-unfold⁻¹ {s = s} h with hasT-⋯⁻¹ {s = s} h
... | inj₁ hs = hs
... | inj₂ (zero , hz)  = hasT-mu⁻ hz
... | inj₂ (suc y , hy) = ⊥-elim (¬hasT-var hy)

------------------------------------------------------------------------
-- HasT is ~-invariant.  Mirror of AtomHead.~-startskind's go.
------------------------------------------------------------------------

≃-hasT : HasT {n} Respects _≃_
≃-hasT refl = id
≃-hasT (x ◅ xs) = ≃-hasT xs ∘ go x where
  go : SymClosure _≃𝕊_ s₁ s₂ → HasT s₁ → HasT s₂
  go (fwd (≃𝕊-;₁ x)) (seqˡ h) = seqˡ (go (fwd x) h)
  go (fwd (≃𝕊-;₁ x)) (seqʳ h) = seqʳ h
  go (fwd (≃𝕊-;₂ x)) (seqˡ h) = seqˡ h
  go (fwd (≃𝕊-;₂ x)) (seqʳ h) = seqʳ (go (fwd x) h)
  go (fwd ≃𝕊-skipˡ) (seqˡ ())
  go (fwd ≃𝕊-skipˡ) (seqʳ h) = h
  go (fwd ≃𝕊-skipʳ) (seqˡ h) = h
  go (fwd ≃𝕊-skipʳ) (seqʳ ())
  go (fwd ≃𝕊-μ) (mu h) = hasT-⋯ h
  go (fwd ≃𝕊-assoc) (seqˡ (seqˡ h)) = seqˡ h
  go (fwd ≃𝕊-assoc) (seqˡ (seqʳ h)) = seqʳ (seqˡ h)
  go (fwd ≃𝕊-assoc) (seqʳ h) = seqʳ (seqʳ h)
  go (fwd ≃𝕊-distr) (seqˡ (brnˡ h)) = brnˡ (seqˡ h)
  go (fwd ≃𝕊-distr) (seqˡ (brnʳ h)) = brnʳ (seqˡ h)
  go (fwd ≃𝕊-distr) (seqʳ h) = brnˡ (seqʳ h)
  go (fwd (≃𝕊-msg x)) ()
  go (fwd (≃𝕊-brn₁ x)) (brnˡ h) = brnˡ (go (fwd x) h)
  go (fwd (≃𝕊-brn₁ x)) (brnʳ h) = brnʳ h
  go (fwd (≃𝕊-brn₂ x)) (brnˡ h) = brnˡ h
  go (fwd (≃𝕊-brn₂ x)) (brnʳ h) = brnʳ (go (fwd x) h)
  go (bwd (≃𝕊-;₁ x)) (seqˡ h) = seqˡ (go (bwd x) h)
  go (bwd (≃𝕊-;₁ x)) (seqʳ h) = seqʳ h
  go (bwd (≃𝕊-;₂ x)) (seqˡ h) = seqˡ h
  go (bwd (≃𝕊-;₂ x)) (seqʳ h) = seqʳ (go (bwd x) h)
  go (bwd ≃𝕊-skipˡ) h = seqʳ h
  go (bwd ≃𝕊-skipʳ) h = seqˡ h
  go (bwd ≃𝕊-μ) h = mu (hasT-unfold⁻¹ h)
  go (bwd ≃𝕊-assoc) (seqˡ h) = seqˡ (seqˡ h)
  go (bwd ≃𝕊-assoc) (seqʳ (seqˡ h)) = seqˡ (seqʳ h)
  go (bwd ≃𝕊-assoc) (seqʳ (seqʳ h)) = seqʳ h
  go (bwd ≃𝕊-distr) (brnˡ (seqˡ h)) = seqˡ (brnˡ h)
  go (bwd ≃𝕊-distr) (brnˡ (seqʳ h)) = seqʳ h
  go (bwd ≃𝕊-distr) (brnʳ (seqˡ h)) = seqˡ (brnʳ h)
  go (bwd ≃𝕊-distr) (brnʳ (seqʳ h)) = seqʳ h
  go (bwd (≃𝕊-msg x)) ()
  go (bwd (≃𝕊-brn₁ x)) (brnˡ h) = brnˡ (go (bwd x) h)
  go (bwd (≃𝕊-brn₁ x)) (brnʳ h) = brnʳ h
  go (bwd (≃𝕊-brn₂ x)) (brnˡ h) = brnˡ h
  go (bwd (≃𝕊-brn₂ x)) (brnʳ h) = brnʳ (go (bwd x) h)
