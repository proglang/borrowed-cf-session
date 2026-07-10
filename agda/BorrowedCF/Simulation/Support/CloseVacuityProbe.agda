module BorrowedCF.Simulation.Support.CloseVacuityProbe where

open import Data.Nat.ListAction using (sum)
open import Data.Vec.Functional as F using ()
open import Data.Empty using (⊥; ⊥-elim)

open import BorrowedCF.Prelude
open import BorrowedCF.Kits
open import BorrowedCF.Types
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.Predicates using (New)
open import BorrowedCF.Types.Syntax using (Skips)
open import BorrowedCF.Context using (Ctx)
open import BorrowedCF.Processes.Typed

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

import BorrowedCF.Simulation.Support.Theorems.B1VacProbe as V

open Un hiding (U)
open Bin using (_Respects_)
open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- NoEnd : a session containing no `end` leaf.  Mirrors V.NoRet, but the
-- forbidden leaf is `end p` rather than `ret`.  Every New-derived session
-- is NoEnd (New has NO `end` constructor: `-, msg, brn, mu, ;, skip).
------------------------------------------------------------------------

data NoEnd {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoEnd (` x)
  ret  : NoEnd (ret {n})
  acq  : NoEnd (acq {n})
  skip : NoEnd (skip {n})
  msg  : NoEnd (msg {n} p T)
  brn  : NoEnd s₁ → NoEnd s₂ → NoEnd (brn p s₁ s₂)
  mu   : NoEnd s → NoEnd (mu s)
  _;_  : NoEnd s₁ → NoEnd s₂ → NoEnd (s₁ ; s₂)

¬noEnd-end : ¬ NoEnd (end {n} p)
¬noEnd-end ()

new⇒noEnd : New s → NoEnd s
new⇒noEnd New.`-          = `-
new⇒noEnd New.msg         = msg
new⇒noEnd (New.brn x y)   = brn (new⇒noEnd x) (new⇒noEnd y)
new⇒noEnd (New.mu x)      = mu (new⇒noEnd x)
new⇒noEnd (x New.; y)     = new⇒noEnd x ; new⇒noEnd y
new⇒noEnd New.skip        = skip

noEnd-⋯ᵣ : NoEnd s → {ρ : m →ᵣ n} → NoEnd (s ⋯ ρ)
noEnd-⋯ᵣ `-          = `-
noEnd-⋯ᵣ ret         = ret
noEnd-⋯ᵣ acq         = acq
noEnd-⋯ᵣ skip        = skip
noEnd-⋯ᵣ msg         = msg
noEnd-⋯ᵣ (brn x y)   = brn (noEnd-⋯ᵣ x) (noEnd-⋯ᵣ y)
noEnd-⋯ᵣ (mu x)      = mu (noEnd-⋯ᵣ x)
noEnd-⋯ᵣ (x ; y)     = noEnd-⋯ᵣ x ; noEnd-⋯ᵣ y

noEnd-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoEnd s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoEnd (`/id (ϕ x))) → NoEnd (s ⋯ ϕ)
noEnd-⋯ `- ∀ϕ = ∀ϕ _
noEnd-⋯ ret ∀ϕ = ret
noEnd-⋯ acq ∀ϕ = acq
noEnd-⋯ skip ∀ϕ = skip
noEnd-⋯ msg ∀ϕ = msg
noEnd-⋯ (brn x y) ∀ϕ = brn (noEnd-⋯ x ∀ϕ) (noEnd-⋯ y ∀ϕ)
noEnd-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noEnd-⋯ x λ where
  zero    → subst NoEnd (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoEnd (wk-`/id _) (noEnd-⋯ᵣ (∀ϕ z))
noEnd-⋯ (x ; y) ∀ϕ = noEnd-⋯ x ∀ϕ ; noEnd-⋯ y ∀ϕ

noEnd-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoEnd (s ⋯ ϕ) → NoEnd s
noEnd-⋯⁻¹ {s = ` _} x = `-
noEnd-⋯⁻¹ {s = end p} x = ⊥-elim (¬noEnd-end x)
noEnd-⋯⁻¹ {s = ret} x = ret
noEnd-⋯⁻¹ {s = acq} x = acq
noEnd-⋯⁻¹ {s = skip} x = skip
noEnd-⋯⁻¹ {s = msg p t} x = msg
noEnd-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noEnd-⋯⁻¹ x) (noEnd-⋯⁻¹ y)
noEnd-⋯⁻¹ {s = mu s} (mu x) = mu (noEnd-⋯⁻¹ x)
noEnd-⋯⁻¹ {s = _ ; _} (x ; y) = noEnd-⋯⁻¹ x ; noEnd-⋯⁻¹ y

noEnd-≃ : NoEnd {n} Respects _≃_
noEnd-≃ refl = id
noEnd-≃ (x ◅ xs) = noEnd-≃ xs ∘ go x where
  go : NoEnd {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-msg eq))  msg       = msg
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-msg eq))  msg       = msg
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noEnd-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noEnd-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y

---------------------------------------------------------------------------------------------------------------
-- NoAcq : a session with no acq leaf.  Mirror of NoEnd (forbidden leaf =
-- acq).  A channel whose session is a factor of a New-derived  s ; end  is
-- NoAcq, hence NOT Mobile (Mobile needs  s = acq ; bounded).
------------------------------------------------------------------------

data NoAcq {n} : 𝕊 n → Set where
  `-   : ∀ {x} → NoAcq (` x)
  end  : NoAcq (end {n} p)
  ret  : NoAcq (ret {n})
  skip : NoAcq (skip {n})
  msg  : NoAcq (msg {n} p T)
  brn  : NoAcq s₁ → NoAcq s₂ → NoAcq (brn p s₁ s₂)
  mu   : NoAcq s → NoAcq (mu s)
  _;_  : NoAcq s₁ → NoAcq s₂ → NoAcq (s₁ ; s₂)

¬noAcq-acq : ¬ NoAcq (acq {n})
¬noAcq-acq ()

noAcq-;-fst : NoAcq (s₁ ; s₂) → NoAcq s₁
noAcq-;-fst (x ; _) = x

noAcq-;-snd : NoAcq (s₁ ; s₂) → NoAcq s₂
noAcq-;-snd (_ ; y) = y

new⇒noAcq : New s → NoAcq s
new⇒noAcq New.`-        = `-
new⇒noAcq New.msg       = msg
new⇒noAcq (New.brn x y) = brn (new⇒noAcq x) (new⇒noAcq y)
new⇒noAcq (New.mu x)    = mu (new⇒noAcq x)
new⇒noAcq (x New.; y)   = new⇒noAcq x ; new⇒noAcq y
new⇒noAcq New.skip      = skip

new-end⇒noAcq : New s → NoAcq (s ; end p)
new-end⇒noAcq N = new⇒noAcq N ; end

noAcq-⋯ᵣ : NoAcq s → {ρ : m →ᵣ n} → NoAcq (s ⋯ ρ)
noAcq-⋯ᵣ `-          = `-
noAcq-⋯ᵣ end         = end
noAcq-⋯ᵣ ret         = ret
noAcq-⋯ᵣ skip        = skip
noAcq-⋯ᵣ msg         = msg
noAcq-⋯ᵣ (brn x y)   = brn (noAcq-⋯ᵣ x) (noAcq-⋯ᵣ y)
noAcq-⋯ᵣ (mu x)      = mu (noAcq-⋯ᵣ x)
noAcq-⋯ᵣ (x ; y)     = noAcq-⋯ᵣ x ; noAcq-⋯ᵣ y

noAcq-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → NoAcq s → {ϕ : m –[ K ]→ n} →
          (∀ x → NoAcq (`/id (ϕ x))) → NoAcq (s ⋯ ϕ)
noAcq-⋯ `- ∀ϕ = ∀ϕ _
noAcq-⋯ end ∀ϕ = end
noAcq-⋯ ret ∀ϕ = ret
noAcq-⋯ skip ∀ϕ = skip
noAcq-⋯ msg ∀ϕ = msg
noAcq-⋯ (brn x y) ∀ϕ = brn (noAcq-⋯ x ∀ϕ) (noAcq-⋯ y ∀ϕ)
noAcq-⋯ ⦃ K ⦄ (mu x) ∀ϕ = mu $ noAcq-⋯ x λ where
  zero    → subst NoAcq (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst NoAcq (wk-`/id _) (noAcq-⋯ᵣ (∀ϕ z))
noAcq-⋯ (x ; y) ∀ϕ = noAcq-⋯ x ∀ϕ ; noAcq-⋯ y ∀ϕ

noAcq-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → NoAcq (s ⋯ ϕ) → NoAcq s
noAcq-⋯⁻¹ {s = ` _} x = `-
noAcq-⋯⁻¹ {s = acq} x = ⊥-elim (¬noAcq-acq x)
noAcq-⋯⁻¹ {s = end p} x = end
noAcq-⋯⁻¹ {s = ret} x = ret
noAcq-⋯⁻¹ {s = skip} x = skip
noAcq-⋯⁻¹ {s = msg p t} x = msg
noAcq-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (noAcq-⋯⁻¹ x) (noAcq-⋯⁻¹ y)
noAcq-⋯⁻¹ {s = mu s} (mu x) = mu (noAcq-⋯⁻¹ x)
noAcq-⋯⁻¹ {s = _ ; _} (x ; y) = noAcq-⋯⁻¹ x ; noAcq-⋯⁻¹ y

noAcq-≃ : NoAcq {n} Respects _≃_
noAcq-≃ refl na = na
noAcq-≃ (x ◅ xs) na = noAcq-≃ xs (go x na)
  where
  go : NoAcq {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd ≃𝕊-μ) (mu x) = noAcq-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (fwd (≃𝕊-msg eq))  msg       = msg
  go (fwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (fwd eq) x) y
  go (fwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (fwd eq) y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (noAcq-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y
  go (bwd (≃𝕊-msg eq))  msg       = msg
  go (bwd (≃𝕊-brn₁ eq)) (brn x y) = brn (go (bwd eq) x) y
  go (bwd (≃𝕊-brn₂ eq)) (brn x y) = brn x (go (bwd eq) y)

¬mobile-noAcq : NoAcq s → ¬ Mobile ⟨ s ⟩
¬mobile-noAcq NAs ⟨ _ , _ , s≃ ⟩ = ¬noAcq-acq (noAcq-;-fst (noAcq-≃ s≃ NAs))

¬mobile-of : ∀ {T : 𝕋} {s} → T ≡ ⟨ s ⟩ → NoAcq s → ¬ Mobile T
¬mobile-of eq NAs = subst (λ T → ¬ Mobile T) (sym eq) (¬mobile-noAcq NAs)

---------------------------------
-- EndTip : a spine whose unique bounded tip is `end p`, with only Skips
-- to its right.  Mirror of V.RetTip with `end` in place of `ret`.
------------------------------------------------------------------------

data EndTip {n} : 𝕊 n → Set where
  end  : ∀ {p} → EndTip (end {n} p)
  _tL_ : EndTip s₁ → Skips s₂ → EndTip (s₁ ; s₂)
  _tR_ : NoEnd s₁ → EndTip s₂ → EndTip (s₁ ; s₂)
  brn  : EndTip s₁ → EndTip s₂ → EndTip (brn p s₁ s₂)
  muC  : EndTip s → EndTip (mu (s ⋯ weakenᵣ))

endTip⊥skips : EndTip s → Skips s → ⊥
endTip⊥skips (r tL _)  (sk1 ; _) = endTip⊥skips r sk1
endTip⊥skips (nr tR r) (_ ; sk2) = endTip⊥skips r sk2
endTip⊥skips (muC r)   (mu sk)   = endTip⊥skips r (skips-⋯ᵣ⁻¹ sk)

noEnd-front : NoEnd s → EndTip (s ; end {0} p)
noEnd-front ns = ns tR end

endTip-Sc-skips : ∀ {a r : 𝕊 0} {p} → EndTip (a ; r) → a ≃ end p → Skips r
endTip-Sc-skips (r tL sk) _    = sk
endTip-Sc-skips (nr tR _) aend = ⊥-elim (¬noEnd-end (noEnd-≃ aend nr))

rettip-⋯ᵣ : ∀ {ρ : m →ᵣ n} → EndTip s → EndTip (s ⋯ ρ)
rettip-⋯ᵣ end        = end
rettip-⋯ᵣ (r tL sk)  = rettip-⋯ᵣ r tL skips-⋯ sk
rettip-⋯ᵣ (nr tR r)  = noEnd-⋯ᵣ nr tR rettip-⋯ᵣ r
rettip-⋯ᵣ (brn r₁ r₂) = brn (rettip-⋯ᵣ r₁) (rettip-⋯ᵣ r₂)
rettip-⋯ᵣ {ρ = ρ} (muC {s = c} r) =
  subst EndTip (cong mu (sym (fusion c weakenᵣ (ρ ↑) ■ ⋯-cong c (λ _ → refl) ■ sym (fusion c ρ weakenᵣ))))
    (muC (rettip-⋯ᵣ r))

rettip-mu-inv : ∀ {n} {X : 𝕊 (suc n)} → EndTip (mu X) →
                ∃[ c ] (X ≡ c ⋯ weakenᵣ) × EndTip c
rettip-mu-inv (muC {s = c} r) = c , refl , r

¬rettip-var : ∀ {n} {x : 𝔽 n} → ¬ EndTip (` x)
¬rettip-var ()

rettip⇒¬noEnd : EndTip s → ¬ NoEnd s
rettip⇒¬noEnd end        ()
rettip⇒¬noEnd (r tL _)   (nr ; _)  = rettip⇒¬noEnd r nr
rettip⇒¬noEnd (_ tR r)   (_ ; nr)  = rettip⇒¬noEnd r nr
rettip⇒¬noEnd (brn r₁ _) (brn nr₁ _) = rettip⇒¬noEnd r₁ nr₁
rettip⇒¬noEnd (muC r)    (mu nr)   = rettip⇒¬noEnd r (noEnd-⋯⁻¹ nr)

rettip-wkN : (k : ℕ) {t : 𝕊 n} → V.size t Nat.≤ k → EndTip (t ⋯ weakenᵣ) → EndTip t
rettip-wkN k {end p}      sz end        = end
rettip-wkN (suc k) {_ ; _}     sz (r tL sk)  =
  rettip-wkN k (Nat.≤-trans (Nat.m≤m+n _ _) (Nat.≤-pred sz)) r tL skips-⋯ᵣ⁻¹ sk
rettip-wkN (suc k) {_ ; _}     sz (nr tR r)  =
  noEnd-⋯⁻¹ nr tR rettip-wkN k (Nat.≤-trans (Nat.m≤n+m _ _) (Nat.≤-pred sz)) r
rettip-wkN (suc k) {brn _ _ _} sz (brn r₁ r₂) =
  brn (rettip-wkN k (Nat.≤-trans (Nat.m≤m+n _ _) (Nat.≤-pred sz)) r₁)
      (rettip-wkN k (Nat.≤-trans (Nat.m≤n+m _ _) (Nat.≤-pred sz)) r₂)
rettip-wkN (suc k) {mu c} sz rt
  with rettip-mu-inv rt
... | d , eq , rd =
  let ¬m0c : ¬ V.Mentions 0F c
      ¬m0c mc = V.mention-after-wk d (subst (V.Mentions 0F) eq (V.mention-⋯ᵣ c (weakenᵣ ↑) mc))
      c₀ , ec₀ = V.str-ren c 0F ¬m0c
      ec : c ≡ c₀ ⋯ weakenᵣ
      ec = ec₀ ■ V.pin0 {s = c₀}
      rc⋯ : EndTip (c ⋯ weakenᵣ ↑)
      rc⋯ = subst EndTip (sym eq) (rettip-⋯ᵣ rd)
      rc₀ww : EndTip ((c₀ ⋯ weakenᵣ) ⋯ weakenᵣ)
      rc₀ww = subst EndTip (V.wk-wk↑ c₀) (subst (λ ■ → EndTip (■ ⋯ weakenᵣ ↑)) ec rc⋯)
      szk : V.size c Nat.≤ k
      szk = Nat.≤-pred sz
      sz₀ : V.size c₀ Nat.≤ k
      sz₀ = subst (Nat._≤ k) (cong V.size ec ■ V.size-⋯ᵣ c₀ weakenᵣ) szk
      rc₀ : EndTip c₀
      rc₀ = rettip-wkN k sz₀ (rettip-wkN k (subst (Nat._≤ k) (sym (V.size-⋯ᵣ c₀ weakenᵣ)) sz₀) rc₀ww)
  in subst (λ ■ → EndTip (mu ■)) (sym ec) (muC rc₀)

rettip-wk⁻¹ : {t : 𝕊 n} → EndTip (t ⋯ weakenᵣ) → EndTip t
rettip-wk⁻¹ {t = t} = rettip-wkN (V.size t) Nat.≤-refl

reN : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ NoEnd t → NoEnd (s ⋯ V.pσ i t) → V.Str i s
reS : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ Skips t → Skips (s ⋯ V.pσ i t) → V.Str i s
reR : ∀ {j} (s : 𝕊 (suc j)) (i : 𝔽 (suc j)) {t : 𝕊 j} →
      ¬ NoEnd t → ¬ Skips t → ¬ EndTip t → EndTip (s ⋯ V.pσ i t) → V.Str i s

reN (` x) i {t} ¬nr nr with i Fin.≟ x
... | yes _ = ⊥-elim (¬nr nr)
... | no ¬p = ` Fin.punchOut ¬p , cong `_ (sym (Fin.punchIn-punchOut ¬p))
reN (mu a) i {t} ¬nr (mu nr) =
  let a₀ , ea = reN a (suc i) {t ⋯ weakenᵣ}
                    (λ nr′ → ¬nr (noEnd-⋯⁻¹ nr′))
                    (subst NoEnd (⋯-cong a (V.pσ-↑ i t)) nr)
  in mu a₀ , (cong mu ea ■ sym (V.pin-↑ i a₀))
reN (s₁ ; s₂) i ¬nr (nr₁ ; nr₂) =
  let a₀ , ea = reN s₁ i ¬nr nr₁
      b₀ , eb = reN s₂ i ¬nr nr₂
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reN (brn p s₁ s₂) i ¬nr (brn nr₁ nr₂) =
  let a₀ , ea = reN s₁ i ¬nr nr₁
      b₀ , eb = reN s₂ i ¬nr nr₂
  in brn p a₀ b₀ , cong₂ (brn p) ea eb
reN ret i ¬nr nr = ret , refl
reN acq i ¬nr nr = acq , refl
reN skip i ¬nr nr = skip , refl
reN (msg p T) i ¬nr nr = msg p T , refl

reS (` x) i {t} ¬sk sk with i Fin.≟ x
... | yes _ = ⊥-elim (¬sk sk)
... | no ¬p = ⊥-elim (¬skips-` sk)
reS (mu a) i {t} ¬sk (mu sk) =
  let a₀ , ea = reS a (suc i) {t ⋯ weakenᵣ}
                    (λ sk′ → ¬sk (skips-⋯ᵣ⁻¹ sk′))
                    (subst Skips (⋯-cong a (V.pσ-↑ i t)) sk)
  in mu a₀ , (cong mu ea ■ sym (V.pin-↑ i a₀))
reS (s₁ ; s₂) i ¬sk (sk₁ ; sk₂) =
  let a₀ , ea = reS s₁ i ¬sk sk₁
      b₀ , eb = reS s₂ i ¬sk sk₂
  in (a₀ ; b₀) , cong₂ _;_ ea eb
reS skip i ¬sk sk = skip , refl

reR (` x) i {t} ¬nr ¬sk ¬rt rt with i Fin.≟ x
... | yes _ = ⊥-elim (¬rt rt)
... | no ¬p = ⊥-elim (¬rettip-var rt)
reR (end p) i ¬nr ¬sk ¬rt rt = end p , refl
reR (mu a) i {t} ¬nr ¬sk ¬rt rt
  with rettip-mu-inv (subst EndTip (cong mu (⋯-cong a (V.pσ-↑ i t))) rt)
... | d , eq , rd =
  let rt-a : EndTip (a ⋯ V.pσ (suc i) (t ⋯ weakenᵣ))
      rt-a = subst EndTip (sym eq) (rettip-⋯ᵣ rd)
      a₀ , ea = reR a (suc i) {t ⋯ weakenᵣ}
                    (λ nr′ → ¬nr (noEnd-⋯⁻¹ nr′))
                    (λ sk′ → ¬sk (skips-⋯ᵣ⁻¹ sk′))
                    (λ rt′ → ¬rt (rettip-wk⁻¹ rt′))
                    rt-a
  in mu a₀ , (cong mu ea ■ sym (V.pin-↑ i a₀))
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

mentions-mu-¬rettip : {s : 𝕊 (suc n)} → V.Mentions 0F s → ¬ EndTip (mu s)
mentions-mu-¬rettip m rtm =
  let s′ , e , _ = rettip-mu-inv rtm
  in V.mention-after-wk s′ (subst (V.Mentions 0F) e m)

mu-bwd : ∀ {s : 𝕊 1} → EndTip (unfold s) → EndTip (mu s)
mu-bwd {s} rt with V.mentions? 0F s
... | no ¬m =
  let s₀ , es = V.str-ren s 0F ¬m
      es′ : s ≡ s₀ ⋯ weakenᵣ
      es′ = es ■ V.pin0 {s = s₀}
      rs₀ : EndTip s₀
      rs₀ = subst EndTip (cong unfold es′ ■ V.mu-cancel) rt
  in subst (λ ■ → EndTip (mu ■)) (sym es′) (muC rs₀)
... | yes m =
  let ¬nrmus : ¬ NoEnd (mu s)
      ¬nrmus = λ where
        (mu nrs) → rettip⇒¬noEnd rt
          (noEnd-⋯ nrs (λ where zero → mu nrs ; (suc x) → `-))
      ¬skmus : ¬ Skips (mu s)
      ¬skmus = λ where (mu sks) → endTip⊥skips rt (skips-⋯ sks)
      s₀ , es = reR s 0F {mu s} ¬nrmus ¬skmus (mentions-mu-¬rettip m)
                    (subst EndTip (V.unfold≡pσ s) rt)
  in ⊥-elim (V.mention-after-wk s₀ (subst (V.Mentions 0F) (es ■ V.pin0 {s = s₀}) m))

endTip-≃ : EndTip {0} Respects _≃_
endTip-≃ refl       rt = rt
endTip-≃ (x ◅ xs)   rt = endTip-≃ xs (go x rt) where
  go : EndTip {0} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-msg eq))  ()
  go (fwd (≃𝕊-brn₁ eq)) (brn r1 r2) = brn (go (fwd eq) r1) r2
  go (fwd (≃𝕊-brn₂ eq)) (brn r1 r2) = brn r1 (go (fwd eq) r2)
  go (bwd (≃𝕊-msg eq))  ()
  go (bwd (≃𝕊-brn₁ eq)) (brn r1 r2) = brn (go (bwd eq) r1) r2
  go (bwd (≃𝕊-brn₂ eq)) (brn r1 r2) = brn r1 (go (bwd eq) r2)
  go (fwd (≃𝕊-;₁ eq)) (r tL sk)  = go (fwd eq) r tL sk
  go (fwd (≃𝕊-;₁ eq)) (nr tR rt) = noEnd-≃ (fwd eq ◅ refl) nr tR rt
  go (fwd (≃𝕊-;₂ eq)) (r tL sk)  = r tL (≃-skips (fwd eq ◅ refl) sk)
  go (fwd (≃𝕊-;₂ eq)) (nr tR rt) = nr tR go (fwd eq) rt
  go (fwd ≃𝕊-skipˡ)   (r tL sk)  = ⊥-elim (endTip⊥skips r skip)
  go (fwd ≃𝕊-skipˡ)   (nr tR rt) = rt
  go (fwd ≃𝕊-skipʳ)   (r tL sk)  = r
  go (fwd ≃𝕊-skipʳ)   (nr tR rt) = ⊥-elim (endTip⊥skips rt skip)
  go (fwd ≃𝕊-μ)       (muC rt)   = subst EndTip (sym V.mu-cancel) rt
  go (fwd ≃𝕊-assoc)   ((r tL s1) tL s2)   = r tL (s1 ; s2)
  go (fwd ≃𝕊-assoc)   ((n tR r)  tL s2)   = n tR (r tL s2)
  go (fwd ≃𝕊-assoc)   ((nL ; nR) tR rt) = nL tR (nR tR rt)
  go (fwd ≃𝕊-distr)   (brn r1 r2 tL sk)   = brn (r1 tL sk) (r2 tL sk)
  go (fwd ≃𝕊-distr)   (brn nL nR tR rt)   = brn (nL tR rt) (nR tR rt)
  go (bwd (≃𝕊-;₁ eq)) (r tL sk)  = go (bwd eq) r tL sk
  go (bwd (≃𝕊-;₁ eq)) (nr tR rt) = noEnd-≃ (bwd eq ◅ refl) nr tR rt
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
  go (bwd ≃𝕊-distr)   (brn (r1 tL sk1) (n2 tR r2))  = ⊥-elim (endTip⊥skips r2 sk1)
  go (bwd ≃𝕊-distr)   (brn (n1 tR r1) (r2 tL sk2))  = ⊥-elim (endTip⊥skips r1 sk2)

------------------------------------------------------------------------
-- VERDICT (A).  See report.  The residual after the close handle is Skips,
-- so a second cons (b ≥ 1) is impossible; b is forced to 0.
------------------------------------------------------------------------

close-residual-skips : ∀ {s s₂ : 𝕊 0} {p p′} → New s →
                       s₁ ; s₂ ≃ s ; end {0} p → s₁ ≃ end {0} p′ → Skips s₂
close-residual-skips {s₁ = s₁} {s = s} {s₂} N s≃ h≃ =
  endTip-Sc-skips (endTip-≃ (≃-sym s≃) (noEnd-front (new⇒noEnd N))) h≃

b≡0 : ∀ {s : 𝕊 0} {n Γ p′} → New s →
      (bc : BindCtx′ (s ; end {0} ‼) (suc n) Γ) →
      (∀ {a r Γ′} → a ; r ≃ s ; end {0} ‼ → a ≃ end {0} p′ →
         BindCtx′ r n Γ′ → n ≡ 0)
b≡0 N bc s≃ ha (nil _) = refl
b≡0 N bc s≃ ha (cons _ _ ¬skips s≃′ Γ≗′ bc′) =
  ⊥-elim (¬skips (close-residual-skips N s≃ ha))

------------------------------------------------------------------------
-- The b = 0 ("block = 1 ; []") instance IS inhabited: the close handle is
-- the unique borrow, residual = skip (Skips), recursion = nil.  This is the
-- shape the reverse RU-Close-inj1 reconstructs.  (New skip ⇒ dual = skip.)
------------------------------------------------------------------------

g1 : Ctx 1
g1 = ⟨ end ‼ ⟩ F.∷ (λ ())

bc1 : BindCtx′ (skip ; end ‼) 1 g1
bc1 = cons (end ‼) skip (λ { (_ ; ()) }) (≃-trans ≃-skipʳ (≃-sym ≃-skipˡ)) (λ _ → refl) (nil skip)

-- And the verdict applied to it: forced to length 0 (b = 0).
bc1-b≡0 : 1 ≡ suc 0   -- length is suc 0, the "n" component is 0
bc1-b≡0 = refl
