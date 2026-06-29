module BorrowedCF.Simulation2.Theorems.B1VacProbe where

open import BorrowedCF.Prelude
open import BorrowedCF.Kits
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open Un hiding (U)
open Bin using (_Respects_)
open Nat.Variables

------------------------------------------------------------------------
-- NoRet : a session that contains no `ret` leaf (allows end / acq /
-- msg / brn / var / mu / ; / skip).  Mirrors `New`, but with end + acq.
------------------------------------------------------------------------

data NoRet {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoRet (` x)
  end  : NoRet (end {n} p)
  acq  : NoRet (acq {n})
  skip : NoRet (skip {n})
  msg  : NoRet (msg {n} p T)
  brn  : NoRet s₁ → NoRet s₂ → NoRet (brn p s₁ s₂)
  mu   : NoRet s → NoRet (mu s)
  _;_  : NoRet s₁ → NoRet s₂ → NoRet (s₁ ; s₂)

¬noRet-ret : ¬ NoRet (ret {n})
¬noRet-ret ()

new⇒noRet : New s → NoRet s
new⇒noRet New.`-          = `-
new⇒noRet New.msg         = msg
new⇒noRet (New.brn x y)   = brn (new⇒noRet x) (new⇒noRet y)
new⇒noRet (New.mu x)      = mu (new⇒noRet x)
new⇒noRet (x New.; y)     = new⇒noRet x ; new⇒noRet y
new⇒noRet New.skip        = skip

noRet-⋯ᵣ : NoRet s → {ρ : m →ᵣ n} → NoRet (s ⋯ ρ)
noRet-⋯ᵣ `-          = `-
noRet-⋯ᵣ end         = end
noRet-⋯ᵣ acq         = acq
noRet-⋯ᵣ skip        = skip
noRet-⋯ᵣ msg         = msg
noRet-⋯ᵣ (brn x y)   = brn (noRet-⋯ᵣ x) (noRet-⋯ᵣ y)
noRet-⋯ᵣ (mu x)      = mu (noRet-⋯ᵣ x)
noRet-⋯ᵣ (x ; y)     = noRet-⋯ᵣ x ; noRet-⋯ᵣ y

noRet-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoRet s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoRet (`/id (ϕ x))) → NoRet (s ⋯ ϕ)
noRet-⋯ `- ∀ϕ = ∀ϕ _
noRet-⋯ end ∀ϕ = end
noRet-⋯ acq ∀ϕ = acq
noRet-⋯ skip ∀ϕ = skip
noRet-⋯ msg ∀ϕ = msg
noRet-⋯ (brn x y) ∀ϕ = brn (noRet-⋯ x ∀ϕ) (noRet-⋯ y ∀ϕ)
noRet-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noRet-⋯ x λ where
  zero    → subst NoRet (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoRet (wk-`/id _) (noRet-⋯ᵣ (∀ϕ z))
noRet-⋯ (x ; y) ∀ϕ = noRet-⋯ x ∀ϕ ; noRet-⋯ y ∀ϕ

noRet-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoRet (s ⋯ ϕ) → NoRet s
noRet-⋯⁻¹ {s = ` _} x = `-
noRet-⋯⁻¹ {s = end p} x = end
noRet-⋯⁻¹ {s = acq} x = acq
noRet-⋯⁻¹ {s = skip} x = skip
noRet-⋯⁻¹ {s = msg p t} x = msg
noRet-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noRet-⋯⁻¹ x) (noRet-⋯⁻¹ y)
noRet-⋯⁻¹ {s = mu s} (mu x) = mu (noRet-⋯⁻¹ x)
noRet-⋯⁻¹ {s = _ ; _} (x ; y) = noRet-⋯⁻¹ x ; noRet-⋯⁻¹ y

noRet-≃ : NoRet {n} Respects _≃_
noRet-≃ refl = id
noRet-≃ (x ◅ xs) = noRet-≃ xs ∘ go x where
  go : NoRet {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noRet-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noRet-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y

------------------------------------------------------------------------
-- The decisive obstruction:  a New-derived front session s ; end ⁇ is
-- NoRet, so its first borrow (≃ ⟨ ret ⟩) cannot exist.
------------------------------------------------------------------------

noRet-;-fst : NoRet (s₁ ; s₂) → NoRet s₁
noRet-;-fst (x ; _) = x

noRet-;-snd : NoRet (s₁ ; s₂) → NoRet s₂
noRet-;-snd (_ ; y) = y

-- BindCtx′ over a NoRet session forces the first borrow to be NoRet;
-- combined with "borrow ≃ ret" this is absurd.  Hence the first borrow
-- can NEVER be ret -> the dropped handle 0F : ⟨ ret ⟩ forces b₁ = 0
-- (there is no place for a second cons because there is no ret to peel).

first-borrow-noRet : ∀ {b Γ} → NoRet s → BindCtx′ s (suc b) Γ →
                     ∃[ s₁ ] ∃[ s₂ ] (s₁ ; s₂ ≃ s) × NoRet s₁
first-borrow-noRet ns (cons _ s≃ _ _) = _ , _ , s≃ , noRet-;-fst (noRet-≃ (Eq*.symmetric _≃𝕊_ s≃) ns)


------------------------------------------------------------------------
-- ANSWER (A), part 1 — the `last` branch (B₁ = []) is fully vacuous.
--
-- TP-Res forces  C : BindCtx (s ; end ⁇) (suc b₁ ∷ B₁) Γ₁  with  New s.
-- When B₁ = [] the front block is  BindCtx′ (s ; end ⁇) (suc b₁) _ ,
-- whose session is NoRet (New s, and `end ⁇` carries no ret).  Its first
-- borrow is therefore NoRet, hence ≄ ret — but the dropped handle 0F has
-- type ⟨ ret ⟩, so the R-Drop redex is UNTYPEABLE in this branch (for
-- EVERY b₁, including 0).  A drop can only be typed via cons-ret/acq,
-- whose structural `; ret` supplies the ret.
------------------------------------------------------------------------

noRet-front-last : New s → NoRet (s ; end ⁇)
noRet-front-last N = new⇒noRet N ; end

-- The first borrow of a NoRet front chain is never ≃ ret.  Specialised
-- to s ; end ⁇ this says the dropped handle (0F) cannot be typed at all
-- in the `last` branch.
last-first-borrow-≄ret :
  ∀ {b Γ a r} → New s → BindCtx′ (s ; end ⁇) (suc b) Γ →
  (a ; r ≃ s ; end ⁇) → a ≄ ret
last-first-borrow-≄ret N _ eqv a≃ret =
  ¬noRet-ret (noRet-≃ a≃ret (noRet-;-fst (noRet-≃ (Eq*.symmetric _≃𝕊_ eqv) (noRet-front-last N))))

------------------------------------------------------------------------
-- ANSWER (A), part 2 — the cons-ret/acq branch closes at b₁ = 0.
--
-- The front block is  BindCtx′ (s₁ ; ret) (suc b₁) _  with  s₁ NoRet
-- (because s₁ ; s₂ ≃ s ; end ⁇ is NoRet, so its left factor is NoRet).
-- The session  s₁ ; ret  is RetTip: its unique bounded tip is the
-- structural `ret`, with nothing borrowable after it.  The dropped
-- handle is the first borrow  a₀ ≃ ret ; the residual r₀ after it must
-- then be Skips (retTip-Sc-skips) — but the SECOND `cons` (present iff
-- b₁ ≥ 1) demands ¬ Skips r₀.  Contradiction ⇒ b₁ = 0.
--
-- The reduction lemma below is the closed core of this argument; the
-- only remaining step to a fully closed cons-ret/acq theorem is
-- `RetTip Respects _≃_` (every case proven except the fold-under-μ case
-- `bwd ≃𝕊-μ`, a guardedness fact: no `ret` sits under a μ in a New-
-- derived front, so the μ body is variable-free — left as the single
-- open obligation `mu-bwd`).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- RetTip : a spine whose unique bounded tip is `ret`, with only Skips
-- to its right.  retTip-Sc-skips below is the closed reduction step
-- that forbids a second borrow after the dropped ret.
------------------------------------------------------------------------

data RetTip {n} : 𝕊 n → Set where
  ret  : RetTip (ret {n})
  _tL_ : RetTip s₁ → Skips s₂ → RetTip (s₁ ; s₂)
  _tR_ : NoRet s₁ → RetTip s₂ → RetTip (s₁ ; s₂)
  brn  : RetTip s₁ → RetTip s₂ → RetTip (brn p s₁ s₂)
  muC  : RetTip s → RetTip (mu (s ⋯ weakenᵣ))

retTip⊥skips : RetTip s → Skips s → ⊥
retTip⊥skips (r tL _)  (sk1 ; _)   = retTip⊥skips r sk1
retTip⊥skips (nr tR r) (_ ; sk2)   = retTip⊥skips r sk2
retTip⊥skips (muC r)   (mu sk)      = retTip⊥skips r (skips-⋯ᵣ⁻¹ sk)

-- The cons-ret/acq front block s₁ ; ret (s₁ NoRet) is RetTip.
noRet-front-cons : NoRet s → RetTip (s ; ret)
noRet-front-cons ns = ns tR ret

retTip-Sc-skips : ∀ {a r : 𝕊 0} → RetTip (a ; r) → a ≃ ret → Skips r
retTip-Sc-skips (r tL sk) _    = sk
retTip-Sc-skips (nr tR _) aret = ⊥-elim (¬noRet-ret (noRet-≃ aret nr))


------------------------------------------------------------------------
-- RetTip respects ≃.  NoRet-side rewrites delegate to noRet-≃; the μ-fold
-- cases need mu-bwd / mu-cancel.
------------------------------------------------------------------------

mu-cancel : ∀ {u : 𝕊 0} → unfold (u ⋯ weakenᵣ) ≡ u
mu-cancel {u} = fusion u weakenᵣ ⦅ mu (u ⋯ weakenᵣ) ⦆ₛ ■ ⋯-id u wkc
  where
    wkc : (weakenᵣ ·ₖ ⦅ mu (u ⋯ weakenᵣ) ⦆ₛ) ≗ idₛ
    wkc ()

-- RESIDUAL (guardedness / occurrence lemma).  For s with a structural top
-- (mu / ; / brn), RetTip (unfold s) forces s to be var0-free: a var0 would
-- place the recursive `mu s` at a RetTip leaf, but `mu s` (it contains a ret)
-- is neither ret, Skips, nor NoRet, so it cannot occupy a ret-tip / skip /
-- NoRet slot.  Then s ≡ u ⋯ weakenᵣ (mu-cancel) and RetTip(mu s)=muC(RetTip u).
-- Closing it needs a binder-depth-generalized strengthening reconstruction
-- (reN/reS/reR over 𝕊 (suc k)); this is the single remaining open obligation.
mu-bwd : ∀ {s : 𝕊 1} → RetTip (unfold s) → RetTip (mu s)
mu-bwd {` zero}      rt = rt
mu-bwd {ret}         rt = muC ret
mu-bwd {mu s}        rt = {! mu-bwd-mu !}
mu-bwd {s₁ ; s₂}   rt = {! mu-bwd-seq !}
mu-bwd {brn p s₁ s₂} rt = {! mu-bwd-brn !}

retTip-≃ : RetTip {0} Respects _≃_
retTip-≃ refl       rt = rt
retTip-≃ (x ◅ xs)   rt = retTip-≃ xs (go x rt) where
  go : RetTip {0} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (r tL sk)  = go (fwd eq) r tL sk
  go (fwd (≃𝕊-;₁ eq)) (nr tR rt) = noRet-≃ (fwd eq ◅ refl) nr tR rt
  go (fwd (≃𝕊-;₂ eq)) (r tL sk)  = r tL (≃-skips (fwd eq ◅ refl) sk)
  go (fwd (≃𝕊-;₂ eq)) (nr tR rt) = nr tR go (fwd eq) rt
  go (fwd ≃𝕊-skipˡ)   (r tL sk)  = ⊥-elim (retTip⊥skips r skip)
  go (fwd ≃𝕊-skipˡ)   (nr tR rt) = rt
  go (fwd ≃𝕊-skipʳ)   (r tL sk)  = r
  go (fwd ≃𝕊-skipʳ)   (nr tR rt) = ⊥-elim (retTip⊥skips rt skip)
  go (fwd ≃𝕊-μ)       (muC rt)   = subst RetTip (sym mu-cancel) rt
  go (fwd ≃𝕊-assoc)   ((r tL s1) tL s2)   = r tL (s1 ; s2)
  go (fwd ≃𝕊-assoc)   ((n tR r)  tL s2)   = n tR (r tL s2)
  go (fwd ≃𝕊-assoc)   ((nL ; nR) tR rt) = nL tR (nR tR rt)
  go (fwd ≃𝕊-distr)   (brn r1 r2 tL sk)   = brn (r1 tL sk) (r2 tL sk)
  go (fwd ≃𝕊-distr)   (brn nL nR tR rt)   = brn (nL tR rt) (nR tR rt)
  go (bwd (≃𝕊-;₁ eq)) (r tL sk)  = go (bwd eq) r tL sk
  go (bwd (≃𝕊-;₁ eq)) (nr tR rt) = noRet-≃ (bwd eq ◅ refl) nr tR rt
  go (bwd (≃𝕊-;₂ eq)) (r tL sk)  = r tL (≃-skips (bwd eq ◅ refl) sk)
  go (bwd (≃𝕊-;₂ eq)) (nr tR rt) = nr tR go (bwd eq) rt
  go (bwd ≃𝕊-skipˡ)   rt         = skip tR rt
  go (bwd ≃𝕊-skipʳ)   rt         = rt tL skip
  go (bwd ≃𝕊-μ)       rt         = mu-bwd rt
  go (bwd ≃𝕊-assoc)   (r tL (s1 ; s2))        = (r tL s1) tL s2
  go (bwd ≃𝕊-assoc)   (n tR (r tL s2))          = (n tR r) tL s2
  go (bwd ≃𝕊-assoc)   (n tR (nr tR rt))         = (n ; nr) tR rt
  go (bwd ≃𝕊-distr)   (brn (r1 tL sk1) (r2 tL sk2)) = brn r1 r2 tL sk1
  go (bwd ≃𝕊-distr)   (brn (n1 tR r1) (n2 tR r2))   = (brn n1 n2) tR r1
  go (bwd ≃𝕊-distr)   (brn (r1 tL sk1) (n2 tR r2))  = ⊥-elim (retTip⊥skips r2 sk1)
  go (bwd ≃𝕊-distr)   (brn (n1 tR r1) (r2 tL sk2))  = ⊥-elim (retTip⊥skips r1 sk2)
