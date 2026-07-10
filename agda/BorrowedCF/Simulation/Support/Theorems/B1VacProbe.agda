module BorrowedCF.Simulation.Support.Theorems.B1VacProbe where

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
open Nat using (_≤_; ℕ; z≤n; s≤s; ≤-refl; ≤-trans; ≤-pred; m≤m+n; m≤n+m)
open Fin.Patterns

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
  go (fwd (≃𝕊-msg eq))  msg       = msg
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-msg eq))  msg       = msg
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)

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
first-borrow-noRet ns (cons _ _ _ s≃ _ _) = _ , _ , s≃ , noRet-;-fst (noRet-≃ (Eq*.symmetric _≃𝕊_ s≃) ns)


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

------------------------------------------------------------------------
-- Strengthening reconstruction.  `Bad t` holds for the recursive body
-- `mu s` substituted at var 0 by `unfold`: it is neither NoRet, Skips,
-- nor ret.  RetTip / NoRet / Skips of `s ⋯ (pσ i t)` then force `s` to
-- avoid variable `i`, so `s = s₀ ⋯ pin i` for some strengthened `s₀`.
------------------------------------------------------------------------

Bad : ∀ {n} → 𝕊 n → Set
Bad t = (¬ NoRet t) × (¬ Skips t) × (t ≢ ret)

wk-ret⁻¹ : ∀ {t : 𝕊 n} → t ⋯ weakenᵣ ≡ ret → t ≡ ret
wk-ret⁻¹ {t = ret} _ = refl

bad-wk : {t : 𝕊 n} → Bad t → Bad (t ⋯ weakenᵣ)
bad-wk (¬nr , ¬sk , ¬rt) =
  (λ nr → ¬nr (noRet-⋯⁻¹ nr)) , (λ sk → ¬sk (skips-⋯ᵣ⁻¹ sk)) , (λ eq → ¬rt (wk-ret⁻¹ eq))

-- point substitution: var i ↦ t, everything else renamed down by punchOut.
pσ : ∀ {j} → 𝔽 (suc j) → 𝕊 j → suc j →ₛ j
pσ i t x with i Fin.≟ x
... | yes _  = t
... | no  ¬p = ` Fin.punchOut ¬p

-- the strengthening renaming: var x ↦ punchIn i x (skips slot i).
pin : ∀ {j} → 𝔽 (suc j) → 𝕊 j → 𝕊 (suc j)
pin i s = s ⋯ (λ x → Fin.punchIn i x)

Str : ∀ {j} → 𝔽 (suc j) → 𝕊 (suc j) → Set
Str i s = ∃[ s₀ ] s ≡ pin i s₀

-- pσ commutes with ↑, raising the bad variable.
pσ-↑ : ∀ {j} (i : 𝔽 (suc j)) (t : 𝕊 j) → (pσ i t ↑) ≗ pσ (Fin.suc i) (t ⋯ weakenᵣ)
pσ-↑ i t zero = refl
pσ-↑ i t (suc x) with i Fin.≟ x
... | yes refl = refl
... | no ¬p with Fin.suc i Fin.≟ Fin.suc x
...   | yes eq = ⊥-elim (¬p (Fin.suc-injective eq))
...   | no ¬q  = cong `_ (cong suc (Fin.punchOut-cong i refl))

-- pin commutes with mu, lowering the avoided slot under the binder.
pin-↑ : ∀ {j} (i : 𝔽 (suc j)) (a₀ : 𝕊 (suc j)) →
        pin i (mu a₀) ≡ mu (pin (Fin.suc i) a₀)
pin-↑ i a₀ = cong mu (⋯-cong a₀ λ where
  zero    → refl
  (suc x) → refl)

pin0 : ∀ {n} {s : 𝕊 n} → pin 0F s ≡ s ⋯ weakenᵣ
pin0 {s = s} = ⋯-cong s (λ _ → refl)

------------------------------------------------------------------------
-- RESIDUAL (guardedness / occurrence lemma).  For s with a structural top
-- (mu / ; / brn), RetTip (unfold s) forces s to be var0-free: a var0 would
-- place the recursive `mu s` at a RetTip leaf, but `mu s` (it contains a ret)
-- is neither ret, Skips, nor NoRet, so it cannot occupy a ret-tip / skip /
-- NoRet slot.  Then s ≡ u ⋯ weakenᵣ (mu-cancel) and RetTip(mu s)=muC(RetTip u).
-- reN/reS/reR reconstruct the strengthening witness Str i s.

-- RetTip preservation by renaming (forward, easy direction).
rettip-⋯ᵣ : ∀ {ρ : m →ᵣ n} → RetTip s → RetTip (s ⋯ ρ)
rettip-⋯ᵣ ret        = ret
rettip-⋯ᵣ (r tL sk)  = rettip-⋯ᵣ r tL skips-⋯ sk
rettip-⋯ᵣ (nr tR r)  = noRet-⋯ᵣ nr tR rettip-⋯ᵣ r
rettip-⋯ᵣ (brn r₁ r₂) = brn (rettip-⋯ᵣ r₁) (rettip-⋯ᵣ r₂)
rettip-⋯ᵣ {ρ = ρ} (muC {s = c} r) =
  subst RetTip (cong mu (sym (fusion c weakenᵣ (ρ ↑) ■ ⋯-cong c (λ _ → refl) ■ sym (fusion c ρ weakenᵣ))))
    (muC (rettip-⋯ᵣ r))

rettip-mu-inv : ∀ {n} {X : 𝕊 (suc n)} → RetTip (mu X) →
                ∃[ c ] (X ≡ c ⋯ weakenᵣ) × RetTip c
rettip-mu-inv (muC {s = c} r) = c , refl , r

¬rettip-var : ∀ {n} {x : 𝔽 n} → ¬ RetTip (` x)
¬rettip-var ()

rettip⇒¬noRet : RetTip s → ¬ NoRet s
rettip⇒¬noRet ret        ()
rettip⇒¬noRet (r tL _)   (nr ; _)  = rettip⇒¬noRet r nr
rettip⇒¬noRet (_ tR r)   (_ ; nr)  = rettip⇒¬noRet r nr
rettip⇒¬noRet (brn r₁ _) (brn nr₁ _) = rettip⇒¬noRet r₁ nr₁
rettip⇒¬noRet (muC r)    (mu nr)   = rettip⇒¬noRet r (noRet-⋯⁻¹ nr)

-- constructor count (a strictly decreasing measure for fuelled recursion).
size : 𝕊 n → ℕ
size (` x)        = 1
size (end p)      = 1
size (msg p T)    = 1
size (brn p s₁ s₂) = suc (size s₁ + size s₂)
size (mu s)       = suc (size s)
size (s₁ ; s₂)    = suc (size s₁ + size s₂)
size skip         = 1
size ret          = 1
size acq          = 1
size (`` α)       = 1

size-⋯ᵣ : (s : 𝕊 m) (ρ : m →ᵣ n) → size (s ⋯ ρ) ≡ size s
size-⋯ᵣ (` x) ρ = refl
size-⋯ᵣ (end p) ρ = refl
size-⋯ᵣ (msg p T) ρ = refl
size-⋯ᵣ (brn p s₁ s₂) ρ = cong suc (cong₂ _+_ (size-⋯ᵣ s₁ ρ) (size-⋯ᵣ s₂ ρ))
size-⋯ᵣ (mu s) ρ = cong suc (size-⋯ᵣ s (ρ ↑))
size-⋯ᵣ (s₁ ; s₂) ρ = cong suc (cong₂ _+_ (size-⋯ᵣ s₁ ρ) (size-⋯ᵣ s₂ ρ))
size-⋯ᵣ skip ρ = refl
size-⋯ᵣ ret ρ = refl
size-⋯ᵣ acq ρ = refl
size-⋯ᵣ (`` α) ρ = refl

-- pure occurrence + strengthening across a punchIn-renaming.
Mentions : ∀ {n} → 𝔽 n → 𝕊 n → Set
Mentions i (` x)        = i ≡ x
Mentions i (end p)      = ⊥
Mentions i (msg p T)    = ⊥
Mentions i (brn p s₁ s₂) = Mentions i s₁ ⊎ Mentions i s₂
Mentions i (mu s)       = Mentions (suc i) s
Mentions i (s₁ ; s₂)    = Mentions i s₁ ⊎ Mentions i s₂
Mentions i skip         = ⊥
Mentions i ret          = ⊥
Mentions i acq          = ⊥
Mentions i (`` α)       = ⊥

mentions? : ∀ {n} (i : 𝔽 n) (s : 𝕊 n) → Dec (Mentions i s)
mentions? i (` x)        = i Fin.≟ x
mentions? i (end p)      = no λ()
mentions? i (msg p T)    = no λ()
mentions? i (brn p s₁ s₂) = mentions? i s₁ ⊎-dec mentions? i s₂
mentions? i (mu s)       = mentions? (suc i) s
mentions? i (s₁ ; s₂)    = mentions? i s₁ ⊎-dec mentions? i s₂
mentions? i skip         = no λ()
mentions? i ret          = no λ()
mentions? i acq          = no λ()
mentions? i (`` α)       = no λ()

-- s avoiding slot i strengthens: s = s₀ ⋯ punchIn i.
str-ren : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) → ¬ Mentions i s → Str i s
str-ren (` x) i ¬m with i Fin.≟ x
... | yes eq = ⊥-elim (¬m eq)
... | no ¬p  = ` Fin.punchOut ¬p , cong `_ (sym (Fin.punchIn-punchOut ¬p))
str-ren (end p) i ¬m = end p , refl
str-ren (msg p T) i ¬m = msg p T , refl
str-ren (brn p s₁ s₂) i ¬m =
  let a₀ , ea = str-ren s₁ i (¬m ∘ inj₁)
      b₀ , eb = str-ren s₂ i (¬m ∘ inj₂)
  in brn p a₀ b₀ , cong₂ (brn p) ea eb
str-ren (mu s) i ¬m =
  let s₀ , es = str-ren s (suc i) ¬m
  in mu s₀ , (cong mu es ■ sym (pin-↑ i s₀))
str-ren (s₁ ; s₂) i ¬m =
  let a₀ , ea = str-ren s₁ i (¬m ∘ inj₁)
      b₀ , eb = str-ren s₂ i (¬m ∘ inj₂)
  in (a₀ ; b₀) , cong₂ _;_ ea eb
str-ren skip i ¬m = skip , refl
str-ren ret i ¬m = ret , refl
str-ren acq i ¬m = acq , refl
str-ren (`` α) i ¬m = `` α , refl

-- weakenᵣ ↑ , post-composed onto the image of weakenᵣ, agrees with weakenᵣ.
wk-wk↑ : (c₀ : 𝕊 m) → (c₀ ⋯ weakenᵣ) ⋯ (weakenᵣ ↑) ≡ (c₀ ⋯ weakenᵣ) ⋯ weakenᵣ
wk-wk↑ c₀ = fusion c₀ weakenᵣ (weakenᵣ ↑) ■ ⋯-cong c₀ (λ _ → refl) ■ sym (fusion c₀ weakenᵣ weakenᵣ)

-- occurrence transports forward along a renaming.
mention-⋯ᵣ : ∀ {i} (s : 𝕊 m) (ρ : m →ᵣ n) → Mentions i s → Mentions (ρ i) (s ⋯ ρ)
mention-⋯ᵣ (` x) ρ refl = refl
mention-⋯ᵣ (brn p s₁ s₂) ρ (inj₁ x) = inj₁ (mention-⋯ᵣ s₁ ρ x)
mention-⋯ᵣ (brn p s₁ s₂) ρ (inj₂ y) = inj₂ (mention-⋯ᵣ s₂ ρ y)
mention-⋯ᵣ {i = i} (mu s) ρ m = mention-⋯ᵣ s (ρ ↑) m
mention-⋯ᵣ (s₁ ; s₂) ρ (inj₁ x) = inj₁ (mention-⋯ᵣ s₁ ρ x)
mention-⋯ᵣ (s₁ ; s₂) ρ (inj₂ y) = inj₂ (mention-⋯ᵣ s₂ ρ y)

-- occurrence reflects backward: a mention of s⋯ρ comes from a mention of s.
mention-⋯ᵣ⁻¹ : ∀ {i} (s : 𝕊 m) (ρ : m →ᵣ n) → Mentions i (s ⋯ ρ) → ∃[ i′ ] (Mentions i′ s × ρ i′ ≡ i)
mention-⋯ᵣ⁻¹ (` x) ρ refl = x , refl , refl
mention-⋯ᵣ⁻¹ (brn p s₁ s₂) ρ (inj₁ x) = let i′ , m , e = mention-⋯ᵣ⁻¹ s₁ ρ x in i′ , inj₁ m , e
mention-⋯ᵣ⁻¹ (brn p s₁ s₂) ρ (inj₂ y) = let i′ , m , e = mention-⋯ᵣ⁻¹ s₂ ρ y in i′ , inj₂ m , e
mention-⋯ᵣ⁻¹ (mu s) ρ m with mention-⋯ᵣ⁻¹ s (ρ ↑) m
... | zero    , mm , ()
... | suc i″ , mm , e = i″ , mm , Fin.suc-injective e
mention-⋯ᵣ⁻¹ (s₁ ; s₂) ρ (inj₁ x) = let i′ , m , e = mention-⋯ᵣ⁻¹ s₁ ρ x in i′ , inj₁ m , e
mention-⋯ᵣ⁻¹ (s₁ ; s₂) ρ (inj₂ y) = let i′ , m , e = mention-⋯ᵣ⁻¹ s₂ ρ y in i′ , inj₂ m , e

-- weakenᵣ never produces an occurrence of slot 0.
mention-after-wk : (X : 𝕊 m) → ¬ Mentions 0F (X ⋯ weakenᵣ)
mention-after-wk X m with mention-⋯ᵣ⁻¹ X weakenᵣ m
... | i′ , _ , ()

rettip-wkN : (k : ℕ) {t : 𝕊 n} → size t ≤ k → RetTip (t ⋯ weakenᵣ) → RetTip t
rettip-wkN k {ret}        sz ret        = ret
rettip-wkN (suc k) {_ ; _}     sz (r tL sk)  =
  rettip-wkN k (≤-trans (m≤m+n _ _) (≤-pred sz)) r tL skips-⋯ᵣ⁻¹ sk
rettip-wkN (suc k) {_ ; _}     sz (nr tR r)  =
  noRet-⋯⁻¹ nr tR rettip-wkN k (≤-trans (m≤n+m _ _) (≤-pred sz)) r
rettip-wkN (suc k) {brn _ _ _} sz (brn r₁ r₂) =
  brn (rettip-wkN k (≤-trans (m≤m+n _ _) (≤-pred sz)) r₁)
      (rettip-wkN k (≤-trans (m≤n+m _ _) (≤-pred sz)) r₂)
rettip-wkN (suc k) {mu c} sz rt
  with rettip-mu-inv rt
... | d , eq , rd =
  let ¬m0c : ¬ Mentions 0F c
      ¬m0c mc = mention-after-wk d (subst (Mentions 0F) eq (mention-⋯ᵣ c (weakenᵣ ↑) mc))
      c₀ , ec₀ = str-ren c 0F ¬m0c
      ec : c ≡ c₀ ⋯ weakenᵣ
      ec = ec₀ ■ pin0 {s = c₀}
      rc⋯ : RetTip (c ⋯ weakenᵣ ↑)
      rc⋯ = subst RetTip (sym eq) (rettip-⋯ᵣ rd)
      rc₀ww : RetTip ((c₀ ⋯ weakenᵣ) ⋯ weakenᵣ)
      rc₀ww = subst RetTip (wk-wk↑ c₀) (subst (λ ■ → RetTip (■ ⋯ weakenᵣ ↑)) ec rc⋯)
      szk : size c ≤ k
      szk = ≤-pred sz
      sz₀ : size c₀ ≤ k
      sz₀ = subst (_≤ k) (cong size ec ■ size-⋯ᵣ c₀ weakenᵣ) szk
      rc₀ : RetTip c₀
      rc₀ = rettip-wkN k sz₀ (rettip-wkN k (subst (_≤ k) (sym (size-⋯ᵣ c₀ weakenᵣ)) sz₀) rc₀ww)
  in subst (λ ■ → RetTip (mu ■)) (sym ec) (muC rc₀)

rettip-wk⁻¹ : {t : 𝕊 n} → RetTip (t ⋯ weakenᵣ) → RetTip t
rettip-wk⁻¹ {t = t} = rettip-wkN (size t) ≤-refl

reN : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ NoRet t → NoRet (s ⋯ pσ i t) → Str i s
reS : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ Skips t → Skips (s ⋯ pσ i t) → Str i s
reR : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ NoRet t → ¬ Skips t → ¬ RetTip t → RetTip (s ⋯ pσ i t) → Str i s

reN (` x) i {t} ¬nr nr with i Fin.≟ x
... | yes _ = ⊥-elim (¬nr nr)
... | no ¬p = ` Fin.punchOut ¬p , cong `_ (sym (Fin.punchIn-punchOut ¬p))
reN (mu a) i {t} ¬nr (mu nr) =
  let a₀ , ea = reN a (suc i) {t ⋯ weakenᵣ}
                    (λ nr′ → ¬nr (noRet-⋯⁻¹ nr′))
                    (subst NoRet (⋯-cong a (pσ-↑ i t)) nr)
  in mu a₀ , (cong mu ea ■ sym (pin-↑ i a₀))
reN (s₁ ; s₂) i ¬nr (nr₁ ; nr₂) =
  let a₀ , ea = reN s₁ i ¬nr nr₁
      b₀ , eb = reN s₂ i ¬nr nr₂
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reN (brn p s₁ s₂) i ¬nr (brn nr₁ nr₂) =
  let a₀ , ea = reN s₁ i ¬nr nr₁
      b₀ , eb = reN s₂ i ¬nr nr₂
  in brn p a₀ b₀ , cong₂ (brn p) ea eb
reN (end p) i ¬nr nr = end p , refl
reN acq i ¬nr nr = acq , refl
reN skip i ¬nr nr = skip , refl
reN (msg p T) i ¬nr nr = msg p T , refl

reS (` x) i {t} ¬sk sk with i Fin.≟ x
... | yes _ = ⊥-elim (¬sk sk)
... | no ¬p = ⊥-elim (¬skips-` sk)
reS (mu a) i {t} ¬sk (mu sk) =
  let a₀ , ea = reS a (suc i) {t ⋯ weakenᵣ}
                    (λ sk′ → ¬sk (skips-⋯ᵣ⁻¹ sk′))
                    (subst Skips (⋯-cong a (pσ-↑ i t)) sk)
  in mu a₀ , (cong mu ea ■ sym (pin-↑ i a₀))
reS (s₁ ; s₂) i ¬sk (sk₁ ; sk₂) =
  let a₀ , ea = reS s₁ i ¬sk sk₁
      b₀ , eb = reS s₂ i ¬sk sk₂
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reS skip i ¬sk sk = skip , refl

reR (` x) i {t} ¬nr ¬sk ¬rt rt with i Fin.≟ x
... | yes _ = ⊥-elim (¬rt rt)
... | no ¬p = ⊥-elim (¬rettip-var rt)
reR ret i ¬nr ¬sk ¬rt rt = ret , refl
reR (mu a) i {t} ¬nr ¬sk ¬rt rt
  with rettip-mu-inv (subst RetTip (cong mu (⋯-cong a (pσ-↑ i t))) rt)
... | d , eq , rd =
  let rt-a : RetTip (a ⋯ pσ (suc i) (t ⋯ weakenᵣ))
      rt-a = subst RetTip (sym eq) (rettip-⋯ᵣ rd)
      a₀ , ea = reR a (suc i) {t ⋯ weakenᵣ}
                    (λ nr′ → ¬nr (noRet-⋯⁻¹ nr′))
                    (λ sk′ → ¬sk (skips-⋯ᵣ⁻¹ sk′))
                    (λ rt′ → ¬rt (rettip-wk⁻¹ rt′))
                    rt-a
  in mu a₀ , (cong mu ea ■ sym (pin-↑ i a₀))
reR (s₁ ; s₂) i ¬nr ¬sk ¬rt (r tL sk) =
  let a₀ , ea = reR s₁ i ¬nr ¬sk ¬rt r
      b₀ , eb = reS s₂ i ¬sk sk
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reR (s₁ ; s₂) i ¬nr ¬sk ¬rt (nr tR r) =
  let a₀ , ea = reN s₁ i ¬nr nr
      b₀ , eb = reR s₂ i ¬nr ¬sk ¬rt r
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reR (brn p s₁ s₂) i ¬nr ¬sk ¬rt (brn r₁ r₂) =
  let a₀ , ea = reR s₁ i ¬nr ¬sk ¬rt r₁
      b₀ , eb = reR s₂ i ¬nr ¬sk ¬rt r₂
  in brn p a₀ b₀ , cong₂ (brn p) ea eb

-- unfold is the point-substitution of `mu s` at slot 0.
unfold≡pσ : (s : 𝕊 (suc n)) → unfold s ≡ s ⋯ pσ 0F (mu s)
unfold≡pσ s = ⋯-cong s (λ where zero → refl ; (suc x) → refl)

-- if s mentions slot 0, `mu s` cannot be a RetTip.
mentions-mu-¬rettip : {s : 𝕊 (suc n)} → Mentions 0F s → ¬ RetTip (mu s)
mentions-mu-¬rettip m rtm =
  let s′ , e , _ = rettip-mu-inv rtm
  in mention-after-wk s′ (subst (Mentions 0F) e m)

mu-bwd : ∀ {s : 𝕊 1} → RetTip (unfold s) → RetTip (mu s)
mu-bwd {` zero} rt = rt
mu-bwd {ret}    rt = muC ret
mu-bwd {s} rt with mentions? 0F s
... | no ¬m =
  let s₀ , es = str-ren s 0F ¬m
      es′ : s ≡ s₀ ⋯ weakenᵣ
      es′ = es ■ pin0 {s = s₀}
      rs₀ : RetTip s₀
      rs₀ = subst RetTip (cong unfold es′ ■ mu-cancel) rt
  in subst (λ ■ → RetTip (mu ■)) (sym es′) (muC rs₀)
... | yes m =
  let ¬nrmus : ¬ NoRet (mu s)
      ¬nrmus = λ where
        (mu nrs) → rettip⇒¬noRet rt
          (noRet-⋯ nrs (λ where zero → mu nrs ; (suc x) → `-))
      ¬skmus : ¬ Skips (mu s)
      ¬skmus = λ where (mu sks) → retTip⊥skips rt (skips-⋯ sks)
      s₀ , es = reR s 0F {mu s} ¬nrmus ¬skmus (mentions-mu-¬rettip m)
                    (subst RetTip (unfold≡pσ s) rt)
  in ⊥-elim (mention-after-wk s₀ (subst (Mentions 0F) (es ■ pin0 {s = s₀}) m))

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
  go (fwd (≃𝕊-msg eq))  ()
  go (fwd (≃𝕊-brn₁ eq)) (brn r1 r2) = brn (go (fwd eq) r1) r2
  go (fwd (≃𝕊-brn₂ eq)) (brn r1 r2) = brn r1 (go (fwd eq) r2)
  go (bwd (≃𝕊-msg eq))  ()
  go (bwd (≃𝕊-brn₁ eq)) (brn r1 r2) = brn (go (bwd eq) r1) r2
  go (bwd (≃𝕊-brn₂ eq)) (brn r1 r2) = brn r1 (go (bwd eq) r2)
