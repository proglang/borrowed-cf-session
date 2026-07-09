-- Proof of `atom-;-unsnoc` (was a postulate in Types/Equivalence): from
-- `x ; y ≃ z ; a` (a an atom) either `y` skips, or `y` factors as `y′ ; a`
-- with `x ; y′ ≃ z`.  Proven for ALL atoms.
--
-- Method: `Snoc a w z` is a structural witness that `w ≃ z ; a`.  Its prefix
-- `z` is ≃-determined by `(a, w)` (`snoc-prefix-unique`), so the ≃-transport
-- `≃-snoc` carries `Snoc a (z;a)(z;skip)` backward along `x;y ≃ z;a` PRESERVING
-- the prefix up to ≃ — the backward-μ case round-trips through `snoc-unfold`,
-- so NO right-cancellation is needed.  The μ-unfold un-substitution
-- `snoc-unfold⁻¹ᴬ` works for EVERY atom incl. bare variables (the sum-based
-- `snoc-⋯-sum` recurses on the body and the actual Snoc, dissolving the
-- one-branch `brn` limitation).  For a `msg p T` ending a ≃𝕊-msg step in one
-- `brn` branch desyncs the payloads, so that case uses the payload-indexed
-- `SnocM` (ending = `msg p _`, payload ≃ T): every leaf is a msg atom (no
-- variable leaves), the index is scope-independent, and ≃𝕊-msg just updates the
-- payload proof — the transport stays clean and the unsnoc recovers T via
-- `snocM-sound`.
module BorrowedCF.Types.AtomUnsnoc where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomSnoc

open Bin
open Nat.Variables

private variable
  w z z₁ z₂ z′ : 𝕊 n

snoc-mu⁻ : {a : 𝕊 n} → Atom a → Snoc a (mu s) z → ∃[ z′ ] Snoc (a ⋯ weakenᵣ) s z′
snoc-mu⁻ A (mu sn) = _ , sn
snoc-mu⁻ A here = case A of λ ()

snoc-;⁻ : {a : 𝕊 n} → Atom a → Snoc a (s₁ ; s₂) z →
  (∃[ z′ ] Snoc a s₁ z′ × Skips s₂) ⊎ (∃[ z′ ] Snoc a s₂ z′)
snoc-;⁻ A (sn ;₁ Sk) = inj₁ (_ , sn , Sk)
snoc-;⁻ A (-;₂ sn)   = inj₂ (_ , sn)
snoc-;⁻ A here = case A of λ ()

snoc-brn⁻ : {a : 𝕊 n} → Atom a → Snoc a (brn p s₁ s₂) z → (∃[ z₁ ] Snoc a s₁ z₁) × (∃[ z₂ ] Snoc a s₂ z₂)
snoc-brn⁻ A (brn sn₁ sn₂) = (_ , sn₁) , (_ , sn₂)
snoc-brn⁻ A here = case A of λ ()

------------------------------------------------------------------------
-- Backward-μ un-substitution for Snoc (prefix-relaxed)
------------------------------------------------------------------------

closedatom-⋯ᶜ : ⦃ K : Kit 𝓕 ⦄ {a : 𝕊 m}{ϕ : m –[ K ]→ n} → ClosedAtom a → ClosedAtom (a ⋯ ϕ)
closedatom-⋯ᶜ end = end
closedatom-⋯ᶜ msg = msg
closedatom-⋯ᶜ ret = ret
closedatom-⋯ᶜ acq = acq
closedatom-⋯ᶜ ``- = ``-

closedatom-≢var : {c : 𝕊 n}{y : 𝔽 n} → ClosedAtom c → c ≢ ` y
closedatom-≢var end ()
closedatom-≢var msg ()
closedatom-≢var ret ()
closedatom-≢var acq ()
closedatom-≢var ``- ()

closed-⋯-inj : ⦃ K : Kit 𝓕 ⦄ {a c : 𝕊 m}{ϕ : m –[ K ]→ n} →
  ClosedAtom a → ClosedAtom c → a ⋯ ϕ ≡ c ⋯ ϕ → a ≡ c
closed-⋯-inj end end refl = refl
closed-⋯-inj end msg ()
closed-⋯-inj end ret ()
closed-⋯-inj end acq ()
closed-⋯-inj end ``- ()
closed-⋯-inj msg end ()
closed-⋯-inj msg msg refl = refl
closed-⋯-inj msg ret ()
closed-⋯-inj msg acq ()
closed-⋯-inj msg ``- ()
closed-⋯-inj ret end ()
closed-⋯-inj ret msg ()
closed-⋯-inj ret ret refl = refl
closed-⋯-inj ret acq ()
closed-⋯-inj ret ``- ()
closed-⋯-inj acq end ()
closed-⋯-inj acq msg ()
closed-⋯-inj acq ret ()
closed-⋯-inj acq acq refl = refl
closed-⋯-inj acq ``- ()
closed-⋯-inj ``- end ()
closed-⋯-inj ``- msg ()
closed-⋯-inj ``- ret ()
closed-⋯-inj ``- acq ()
closed-⋯-inj ``- ``- refl = refl

-- Pull a closed leaf atom `c` back through ϕ:  its image `a` must be `c`.
pullClosed : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {a c : 𝕊 m}{ϕ : m –[ K ]→ n} →
  Atom a → ClosedAtom c → (∀ x → a ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  a ⋯ ϕ ≡ c ⋯ ϕ → Snoc a c skip
pullClosed {a = a}{c}{ϕ} (`- {x = x}) cc avar eqϕ with avar x refl
... | y , ϕx≡ = ⊥-elim (closedatom-≢var (closedatom-⋯ᶜ cc) (sym eqϕ ■ ϕx≡))
pullClosed {a = a}{c} end cc avar eqϕ = subst (λ t → Snoc a t skip) (closed-⋯-inj end cc eqϕ) here
pullClosed {a = a}{c} msg cc avar eqϕ = subst (λ t → Snoc a t skip) (closed-⋯-inj msg cc eqϕ) here
pullClosed {a = a}{c} ret cc avar eqϕ = subst (λ t → Snoc a t skip) (closed-⋯-inj ret cc eqϕ) here
pullClosed {a = a}{c} acq cc avar eqϕ = subst (λ t → Snoc a t skip) (closed-⋯-inj acq cc eqϕ) here
pullClosed {a = a}{c} ``- cc avar eqϕ = subst (λ t → Snoc a t skip) (closed-⋯-inj ``- cc eqϕ) here

wk-avar : {a′ : 𝕊 m}{ϕ : m →ₛ n} → Atom a′ →
  (∀ x → a′ ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  ∀ x → a′ ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id ((ϕ ↑) x) ≡ ` y
wk-avar {ϕ = ϕ} (`- {x = x′}) avar x a′w≡ =
  let x≡ = `-injective a′w≡ ; y , e = avar x′ refl
  in suc y , (cong (λ v → `/id ((ϕ ↑) v)) (sym x≡) ■ wk-`/id (ϕ x′) ■ cong (_⋯ weakenᵣ) e)
wk-avar end avar x a′w≡ = case a′w≡ of λ ()
wk-avar msg avar x a′w≡ = case a′w≡ of λ ()
wk-avar ret avar x a′w≡ = case a′w≡ of λ ()
wk-avar acq avar x a′w≡ = case a′w≡ of λ ()
wk-avar ``- avar x a′w≡ = case a′w≡ of λ ()

snoc-⋯⁻¹ : {α : 𝕊 n}{a′ : 𝕊 m}{ϕ : m →ₛ n} →
  Atom α → Atom a′ → α ≡ a′ ⋯ ϕ → (∀ x → a′ ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  Snoc α (s ⋯ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) →
  (∀ y → EndsIn-` y s → ∃[ z′ ] Snoc a′ s z′) →
  ∃[ z′ ] Snoc a′ s z′
snoc-⋯⁻¹ {s = ` x} Aα A eq avar sn ∀¬S ∀¬E = ∀¬E x here
snoc-⋯⁻¹ {s = end q} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosed A end avar (sym eq)
snoc-⋯⁻¹ {s = msg q T} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosed A msg avar (sym eq)
snoc-⋯⁻¹ {s = ret} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosed A ret avar (sym eq)
snoc-⋯⁻¹ {s = acq} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosed A acq avar (sym eq)
snoc-⋯⁻¹ {s = `` β} Aα A eq avar here ∀¬S ∀¬E = _ , pullClosed A ``- avar (sym eq)
snoc-⋯⁻¹ {s = skip} Aα A eq avar here ∀¬S ∀¬E = case Aα of λ ()
snoc-⋯⁻¹ {s = brn p s₁ s₂} Aα A eq avar sn ∀¬S ∀¬E with snoc-brn⁻ Aα sn
... | (_ , sn₁) , (_ , sn₂) =
  _ , brn (proj₂ (snoc-⋯⁻¹ Aα A eq avar sn₁ ∀¬S
                    (λ y E → proj₁ (snoc-brn⁻ A (proj₂ (∀¬E y (brn (inj₁ E))))))))
          (proj₂ (snoc-⋯⁻¹ Aα A eq avar sn₂ ∀¬S
                    (λ y E → proj₂ (snoc-brn⁻ A (proj₂ (∀¬E y (brn (inj₂ E))))))))
snoc-⋯⁻¹ {s = s₁ ; s₂} Aα A eq avar sn ∀¬S ∀¬E with snoc-;⁻ Aα sn
... | inj₁ (_ , sn₁ , SkΦ) =
  let s′ = skips-⋯⁻¹ SkΦ ∀¬S in
  Π.map₂ (_;₁ s′) (snoc-⋯⁻¹ Aα A eq avar sn₁ ∀¬S
    (λ y E → Sum.[ (λ (z′ , sn₀ , _) → z′ , sn₀)
                 , (λ (_ , sn₀) → ⊥-elim (skips⊥snoc A s′ sn₀)) ]
             (snoc-;⁻ A (proj₂ (∀¬E y (E ;₁ s′))))))
... | inj₂ (_ , sn₂) =
  Π.map (s₁ ;_) -;₂_ (snoc-⋯⁻¹ Aα A eq avar sn₂ ∀¬S
    (λ y E → Sum.[ (λ (_ , _ , Sk) → ⊥-elim (skips⊥snoc Aα (skips-⋯ Sk) sn₂))
                 , (λ (z′ , sn₀) → z′ , sn₀) ]
             (snoc-;⁻ A (proj₂ (∀¬E y (-;₂ E))))))
snoc-⋯⁻¹ {s = mu s₀} {α = α}{a′ = a′}{ϕ = ϕ} Aα A eq avar sn ∀¬S ∀¬E with snoc-mu⁻ Aα sn
... | (_ , sn₀) = Π.map (_⋯ ⦅ mu s₀ ⦆ₛ) mu (snoc-⋯⁻¹ (atom-⋯ᵣ Aα) (atom-⋯ᵣ A) eq′ avar′ sn₀ ∀¬S′ cb)
  where
  ∀¬S′ : ∀ z → ¬ Skips (`/id ((ϕ ↑) z))
  ∀¬S′ zero = ¬skips-`/` Kₛ
  ∀¬S′ (suc z) = ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ z)))
  eq′ : α ⋯ weakenᵣ ≡ (a′ ⋯ weakenᵣ) ⋯ (ϕ ↑)
  eq′ = cong (_⋯ weakenᵣ) eq ■ ⋯-↑-wk a′ ϕ
  avar′ : ∀ x → a′ ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id ((ϕ ↑) x) ≡ ` y
  avar′ = wk-avar A avar
  cb : ∀ z → EndsIn-` z s₀ → ∃[ z′ ] Snoc (a′ ⋯ weakenᵣ) s₀ z′
  cb zero    E = let z′ , s0 = snoc⋯⇒snoc {ϕ = ϕ ↑} (atom-⋯ᵣ Aα) sn₀ ∀¬S′ E
                 in ⊥-elim (¬snoc-wk-zero {α = α} (subst (λ w → Snoc (α ⋯ weakenᵣ) w z′) (`/`-is-` ⦃ Kₛ ⦄ zero) s0))
  cb (suc z) E = snoc-mu⁻ A (proj₂ (∀¬E z (mu E)))

closedatom-atom : {a : 𝕊 n} → ClosedAtom a → Atom a
closedatom-atom end = end
closedatom-atom msg = msg
closedatom-atom ret = ret
closedatom-atom acq = acq
closedatom-atom ``- = ``-

¬snoc-closed-var : {a : 𝕊 n}{x : 𝔽 n} → ClosedAtom a → ¬ Snoc a (` x) z
¬snoc-closed-var ca here = case ca of λ ()

snoc-unfold⁻¹ : {a : 𝕊 n} → ClosedAtom a → Snoc a (unfold s) z → ∃[ z′ ] Snoc a (mu s) z′
snoc-unfold⁻¹ {s = s} {a = a} ca sn with skips? s
... | yes Ss = ⊥-elim (skips⊥snoc (closedatom-atom ca) (skips-⋯ Ss) sn)
... | no ¬Ss = Π.map (_⋯ ⦅ mu s ⦆ₛ) mu
    (snoc-⋯⁻¹ (closedatom-atom ca) (atom-⋯ᵣ (closedatom-atom ca))
       (sym (wk-cancels-⦅⦆-⋯ _ (mu s))) avarϕ sn ∀¬Sϕ cb)
  where
  A = closedatom-atom ca
  ∀¬Sϕ : ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
  ∀¬Sϕ zero (mu Ss′) = ¬Ss Ss′
  ∀¬Sϕ (suc x) = ¬skips-`
  avarϕ : ∀ x → a ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id (⦅ mu s ⦆ₛ x) ≡ ` y
  avarϕ x eqx = ⊥-elim (closedatom-≢var (closedatom-⋯ᶜ ca) eqx)
  cb : ∀ y → EndsIn-` y s → ∃[ z′ ] Snoc (a ⋯ weakenᵣ) s z′
  cb zero    E = snoc-mu⁻ A (proj₂ (snoc⋯⇒snoc A sn ∀¬Sϕ E))
  cb (suc x) E = ⊥-elim (¬snoc-closed-var ca (proj₂ (snoc⋯⇒snoc A sn ∀¬Sϕ E)))

------------------------------------------------------------------------
-- Sum-based μ-unfold un-substitution — closes the variable-ending case too
------------------------------------------------------------------------

brn≡ : {q q′ : Pol}{a b c d : 𝕊 n} → brn q a b ≡ brn q′ c d → q ≡ q′ × a ≡ c × b ≡ d
brn≡ refl = refl , refl , refl
mu≡ : {a b : 𝕊 (suc n)} → mu a ≡ mu b → a ≡ b
mu≡ refl = refl
seq≡ : {a b c d : 𝕊 n} → a ; b ≡ c ; d → a ≡ c × b ≡ d
seq≡ refl = refl , refl

⋯ᵣ-inj : {ρ : m →ᵣ n} → (∀ {x y} → ρ x ≡ ρ y → x ≡ y) → (t u : 𝕊 m) → t ⋯ ρ ≡ u ⋯ ρ → t ≡ u
⋯ᵣ-inj inj (` x) (` y) e = cong `_ (inj (`-injective e))
⋯ᵣ-inj inj (` x) (end q) e = case e of λ ()
⋯ᵣ-inj inj (` x) (msg q T) e = case e of λ ()
⋯ᵣ-inj inj (` x) (brn q u₁ u₂) e = case e of λ ()
⋯ᵣ-inj inj (` x) (mu u) e = case e of λ ()
⋯ᵣ-inj inj (` x) (u₁ ; u₂) e = case e of λ ()
⋯ᵣ-inj inj (` x) skip e = case e of λ ()
⋯ᵣ-inj inj (` x) ret e = case e of λ ()
⋯ᵣ-inj inj (` x) acq e = case e of λ ()
⋯ᵣ-inj inj (` x) (`` γ) e = case e of λ ()
⋯ᵣ-inj inj (end p) (` y) e = case e of λ ()
⋯ᵣ-inj {ρ = ρ} inj (end p) (end q) e = closed-⋯-inj ⦃ Kᵣ ⦄ {ϕ = ρ} end end e
⋯ᵣ-inj {ρ = ρ} inj (msg p T) (msg q U) e = closed-⋯-inj ⦃ Kᵣ ⦄ {ϕ = ρ} msg msg e
⋯ᵣ-inj inj (brn p t₁ t₂) (brn q u₁ u₂) e =
  let q≡ , e₁ , e₂ = brn≡ e in
  cong₂ (brn _) (⋯ᵣ-inj inj t₁ u₁ e₁) (⋯ᵣ-inj inj t₂ u₂ e₂) ■ cong (λ P → brn P u₁ u₂) q≡
⋯ᵣ-inj inj (mu t) (mu u) e = cong mu (⋯ᵣ-inj (↑ᵣ-inj inj) t u (mu≡ e))
⋯ᵣ-inj inj (t₁ ; t₂) (u₁ ; u₂) e =
  let e₁ , e₂ = seq≡ e in cong₂ _;_ (⋯ᵣ-inj inj t₁ u₁ e₁) (⋯ᵣ-inj inj t₂ u₂ e₂)
⋯ᵣ-inj inj skip skip e = refl
⋯ᵣ-inj inj ret ret e = refl
⋯ᵣ-inj inj acq acq e = refl
⋯ᵣ-inj {ρ = ρ} inj (`` γ) (`` δ) e = closed-⋯-inj ⦃ Kᵣ ⦄ {ϕ = ρ} ``- ``- e

zero≢atomwk : {α : 𝕊 n} → Atom α → ¬ (` zero ≡ α ⋯ weakenᵣ)
zero≢atomwk (`- {x = x}) e = case e of λ ()
zero≢atomwk end e = case e of λ ()
zero≢atomwk msg e = case e of λ ()
zero≢atomwk ret e = case e of λ ()
zero≢atomwk acq e = case e of λ ()
zero≢atomwk ``- e = case e of λ ()

wk-pb : {α : 𝕊 n}{a′ : 𝕊 m}{ϕ : m →ₛ n} → Atom α →
  (∀ y → `/id (ϕ y) ≡ α → a′ ≡ ` y) →
  ∀ y → `/id ((ϕ ↑) y) ≡ α ⋯ weakenᵣ → a′ ⋯ weakenᵣ ≡ ` y
wk-pb Aα pb zero e = ⊥-elim (zero≢atomwk Aα (sym (`/`-is-` ⦃ Kₛ ⦄ zero) ■ e))
wk-pb {ϕ = ϕ} Aα pb (suc x) e =
  cong (_⋯ weakenᵣ) (pb x (⋯ᵣ-inj weaken-inj _ _ (sym (wk-`/id (ϕ x)) ■ e)))

RSUM : {n : ℕ} → 𝕊 n → (m : ℕ) → (𝔽 m → 𝕊 n) → 𝕊 m → Set
RSUM {n} α _ img t = ∃[ y ] EndsIn-` y t × (∃[ z′ ] Snoc α (img y) z′) × (∀ x → img y ≢ ` x)

leafLR : {α : 𝕊 n}{a′ : 𝕊 m}{ϕ : m →ₛ n} (y : 𝔽 m) → Atom α →
  (∀ x → `/id (ϕ x) ≡ α → a′ ≡ ` x) →
  (w : 𝕊 n) → `/id (ϕ y) ≡ w → Snoc α w z →
  (∃[ z′ ] Snoc a′ (` y) z′) ⊎ ((∃[ z′ ] Snoc α w z′) × (∀ x → w ≢ ` x))
leafLR y Aα pb (` w) imgeq here = inj₁ (_ , subst (λ v → Snoc v (` y) skip) (sym (pb y imgeq)) here)
leafLR y Aα pb (end q) imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb (msg q T) imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb (brn q u₁ u₂) imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb (mu u) imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb (u₁ ; u₂) imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb skip imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb ret imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb acq imgeq sn = inj₂ ((_ , sn) , λ x ())
leafLR y Aα pb (`` γ) imgeq sn = inj₂ ((_ , sn) , λ x ())

snoc-⋯-sum : {α : 𝕊 n}{a′ : 𝕊 m}{ϕ : m →ₛ n} → Atom α → Atom a′ → α ≡ a′ ⋯ ϕ →
  (∀ x → a′ ≡ ` x → ∃[ y ] `/id (ϕ x) ≡ ` y) →
  (∀ y → `/id (ϕ y) ≡ α → a′ ≡ ` y) →
  (∀ x → ¬ Skips (`/id (ϕ x))) →
  {t : 𝕊 m} → Snoc α (t ⋯ ϕ) z →
  (∃[ z′ ] Snoc a′ t z′) ⊎ RSUM α _ (λ y → `/id (ϕ y)) t
snoc-⋯-sum {ϕ = ϕ} Aα A eq avar pb ∀¬S {t = ` y} sn =
  Sum.map (λ r → r) (λ ((z′ , r) , nv) → y , here , (z′ , r) , nv) (leafLR y Aα pb (`/id (ϕ y)) refl sn)
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = end q} here = inj₁ (_ , pullClosed A end avar (sym eq))
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = msg q T} here = inj₁ (_ , pullClosed A msg avar (sym eq))
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = ret} here = inj₁ (_ , pullClosed A ret avar (sym eq))
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = acq} here = inj₁ (_ , pullClosed A acq avar (sym eq))
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = `` β} here = inj₁ (_ , pullClosed A ``- avar (sym eq))
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = skip} here = case Aα of λ ()
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = brn q t₁ t₂} here = case Aα of λ ()
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = brn q t₁ t₂} (brn sn₁ sn₂)
  with snoc-⋯-sum Aα A eq avar pb ∀¬S sn₁ | snoc-⋯-sum Aα A eq avar pb ∀¬S sn₂
... | inj₁ (_ , l₁) | inj₁ (_ , l₂) = inj₁ (_ , brn l₁ l₂)
... | inj₂ (y , E , snr , nv) | _ = inj₂ (y , brn (inj₁ E) , snr , nv)
... | inj₁ _ | inj₂ (y , E , snr , nv) = inj₂ (y , brn (inj₂ E) , snr , nv)
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = t₁ ; t₂} here = case Aα of λ ()
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = t₁ ; t₂} (sn₁ ;₁ Sk)
  with snoc-⋯-sum Aα A eq avar pb ∀¬S sn₁
... | inj₁ (_ , l₁) = inj₁ (_ , l₁ ;₁ skips-⋯⁻¹ Sk ∀¬S)
... | inj₂ (y , E , snr , nv) = inj₂ (y , E ;₁ skips-⋯⁻¹ Sk ∀¬S , snr , nv)
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = t₁ ; t₂} (-;₂ sn₂)
  with snoc-⋯-sum Aα A eq avar pb ∀¬S sn₂
... | inj₁ (_ , l₂) = inj₁ (_ , -;₂ l₂)
... | inj₂ (y , E , snr , nv) = inj₂ (y , -;₂ E , snr , nv)
snoc-⋯-sum Aα A eq avar pb ∀¬S {t = mu t₀} here = case Aα of λ ()
snoc-⋯-sum {α = α}{a′ = a′}{ϕ = ϕ} Aα A eq avar pb ∀¬S {t = mu t₀} (mu sn₀)
  with snoc-⋯-sum (atom-⋯ᵣ Aα) (atom-⋯ᵣ A) eq′ (wk-avar A avar) (wk-pb Aα pb) ∀¬S′ sn₀
  where
  eq′ = cong (_⋯ weakenᵣ) eq ■ ⋯-↑-wk a′ ϕ
  ∀¬S′ : ∀ z → ¬ Skips (`/id ((ϕ ↑) z))
  ∀¬S′ zero = ¬skips-`/` Kₛ
  ∀¬S′ (suc z) = ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ z)))
... | inj₁ (_ , l₀) = inj₁ (_ , mu l₀)
... | inj₂ (zero , E₀ , (z′ , sn′₀) , nv) =
  ⊥-elim (¬snoc-wk-zero {α = α} (subst (λ w → Snoc (α ⋯ weakenᵣ) w z′) (`/`-is-` ⦃ Kₛ ⦄ zero) sn′₀))
... | inj₂ (suc y′ , E₀ , (z′ , sn′₀) , nv) =
  inj₂ (y′ , mu E₀ ,
        snoc-⋯ᵣ⁻¹ weaken-inj Aα refl (subst (λ w → Snoc (α ⋯ weakenᵣ) w z′) (wk-`/id (ϕ y′)) sn′₀) ,
        λ x e → nv (suc x) (wk-`/id (ϕ y′) ■ cong (_⋯ weakenᵣ) e))

img0 : {s : 𝕊 (suc n)} → `/id (⦅ mu s ⦆ₛ zero) ≡ mu s
img0 = refl
imgS : {s : 𝕊 (suc n)} (w : 𝔽 n) → `/id (⦅ mu s ⦆ₛ (suc w)) ≡ ` w
imgS w = refl
wk-var : (w : 𝔽 n) → (` w) ⋯ weakenᵣ ≡ ` suc w
wk-var w = refl

∀¬Sϕ : {s : 𝕊 (suc n)} → ¬ Skips s → ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
∀¬Sϕ ¬Ss zero (mu Ss) = ¬Ss Ss
∀¬Sϕ ¬Ss (suc x) = ¬skips-`

avarϕ : {s : 𝕊 (suc n)}{a : 𝕊 n} → Atom a → ∀ x → a ⋯ weakenᵣ ≡ ` x → ∃[ y ] `/id (⦅ mu s ⦆ₛ x) ≡ ` y
avarϕ {s = s} (`- {x = v}) x eqx = v , (cong (λ u → `/id (⦅ mu s ⦆ₛ u)) (sym (`-injective eqx)) ■ imgS {s = s} v)
avarϕ end x eqx = case eqx of λ ()
avarϕ msg x eqx = case eqx of λ ()
avarϕ ret x eqx = case eqx of λ ()
avarϕ acq x eqx = case eqx of λ ()
avarϕ ``- x eqx = case eqx of λ ()

pbϕ : {s : 𝕊 (suc n)}{a : 𝕊 n} → Atom a → ∀ y → `/id (⦅ mu s ⦆ₛ y) ≡ a → a ⋯ weakenᵣ ≡ ` y
pbϕ A′ zero e = ⊥-elim (case subst Atom (sym (sym img0 ■ e)) A′ of λ ())
pbϕ {s = s} A′ (suc w) e = cong (_⋯ weakenᵣ) (sym (sym (imgS {s = s} w) ■ e))

snoc-unfold⁻¹ᴬ : {a : 𝕊 n} → Atom a → Snoc a (unfold s) z → ∃[ z′ ] Snoc a (mu s) z′
snoc-unfold⁻¹ᴬ {s = s}{a = a} A sn with skips? s
... | yes Ss = ⊥-elim (skips⊥snoc A (skips-⋯ Ss) sn)
... | no ¬Ss with snoc-⋯-sum {ϕ = ⦅ mu s ⦆ₛ} A (atom-⋯ᵣ A) (sym (wk-cancels-⦅⦆-⋯ a (mu s))) (avarϕ {s = s} A) (pbϕ {s = s} A) (∀¬Sϕ {s = s} ¬Ss) sn
...   | inj₁ (_ , l) = _ , mu l
...   | inj₂ (zero , _ , (z′ , snr) , _) = z′ , snr
...   | inj₂ (suc w , _ , _ , nv) = ⊥-elim (nv w refl)

------------------------------------------------------------------------
-- SnocA: Snoc whose ending atom is only required ≃ a (per-branch).
-- Handles msg-payload rewrites (no brn desync); prefix uniqueness kills
-- the residual right-cancellation at the μ-step.
------------------------------------------------------------------------

data SnocA {n} (a : 𝕊 n) : 𝕊 n → 𝕊 n → Set where
  here : {a″ : 𝕊 n} → Atom a″ → a″ ≃ a → SnocA a a″ skip
  _;₁_ : SnocA a s₁ z → Skips s₂ → SnocA a (s₁ ; s₂) z
  -;₂_ : SnocA a s₂ z → SnocA a (s₁ ; s₂) (s₁ ; z)
  brn  : SnocA a s₁ z₁ → SnocA a s₂ z₂ → SnocA a (brn p s₁ s₂) (brn p z₁ z₂)
  mu   : SnocA (a ⋯ weakenᵣ) s z → SnocA a (mu s) (z ⋯ ⦅ mu s ⦆ₛ)

snocA-sound : {a : 𝕊 n} → SnocA a w z → w ≃ z ; a
snocA-sound (here A e) = ≃-trans e (≃-sym ≃-skipˡ)
snocA-sound (sn ;₁ Sk) = ≃-trans (≃-skipsʳ Sk) (snocA-sound sn)
snocA-sound (-;₂ sn) = ≃-trans (≃-; ≃-refl (snocA-sound sn)) (≃-sym ≃-assoc-;)
snocA-sound (brn sn₁ sn₂) = ≃-trans (≃-brn (snocA-sound sn₁) (snocA-sound sn₂)) (≃-sym ≃-distr)
snocA-sound {a = a} (mu {s = s} {z = z} sn) =
  ≃-trans (≃-μ) (≃-trans (≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (snocA-sound sn))
    (≃-; ≃-refl (≃-reflexive (wk-cancels-⦅⦆-⋯ a (mu s)))))

skipsA⊥snocA : {a : 𝕊 n} → Skips w → SnocA a w z → ⊥
skipsA⊥snocA Sk (here A e) = ¬skips-atom A Sk
skipsA⊥snocA (Sk₁ ; Sk₂) (sn ;₁ _) = skipsA⊥snocA Sk₁ sn
skipsA⊥snocA (Sk₁ ; Sk₂) (-;₂ sn) = skipsA⊥snocA Sk₂ sn
skipsA⊥snocA (mu Sk) (mu sn) = skipsA⊥snocA Sk sn

snocA-mu⁻ : {a : 𝕊 n} → SnocA a (mu s) z → ∃[ z′ ] SnocA (a ⋯ weakenᵣ) s z′
snocA-mu⁻ (mu sn) = _ , sn
snocA-mu⁻ (here A e) = case A of λ ()

snocA-;⁻ : {a : 𝕊 n} → SnocA a (s₁ ; s₂) z →
  (∃[ z′ ] SnocA a s₁ z′ × Skips s₂) ⊎ (∃[ z′ ] SnocA a s₂ z′)
snocA-;⁻ (sn ;₁ Sk) = inj₁ (_ , sn , Sk)
snocA-;⁻ (-;₂ sn) = inj₂ (_ , sn)
snocA-;⁻ (here A e) = case A of λ ()

snocA-brn⁻ : {a : 𝕊 n} → SnocA a (brn p s₁ s₂) z → (∃[ z₁ ] SnocA a s₁ z₁) × (∃[ z₂ ] SnocA a s₂ z₂)
snocA-brn⁻ (brn sn₁ sn₂) = (_ , sn₁) , (_ , sn₂)
snocA-brn⁻ (here A e) = case A of λ ()

snocA-prefix-unique : {a : 𝕊 n} → SnocA a w z₁ → SnocA a w z₂ → z₁ ≃ z₂
snocA-prefix-unique (here A₁ e₁) (here A₂ e₂) = ≃-refl
snocA-prefix-unique (here A₁ e₁) (sn₂ ;₁ Sk) = case A₁ of λ ()
snocA-prefix-unique (here A₁ e₁) (-;₂ sn₂) = case A₁ of λ ()
snocA-prefix-unique (here A₁ e₁) (brn sn₂ sn₃) = case A₁ of λ ()
snocA-prefix-unique (here A₁ e₁) (mu sn₂) = case A₁ of λ ()
snocA-prefix-unique (sn₁ ;₁ Sk) (here A₂ e₂) = case A₂ of λ ()
snocA-prefix-unique (-;₂ sn₁) (here A₂ e₂) = case A₂ of λ ()
snocA-prefix-unique (brn sn₁ sn₃) (here A₂ e₂) = case A₂ of λ ()
snocA-prefix-unique (mu sn₁) (here A₂ e₂) = case A₂ of λ ()
snocA-prefix-unique (sn₁ ;₁ Sk₁) (sn₂ ;₁ Sk₂) = snocA-prefix-unique sn₁ sn₂
snocA-prefix-unique (sn₁ ;₁ Sk₁) (-;₂ sn₂) = ⊥-elim (skipsA⊥snocA Sk₁ sn₂)
snocA-prefix-unique (-;₂ sn₁) (sn₂ ;₁ Sk₂) = ⊥-elim (skipsA⊥snocA Sk₂ sn₁)
snocA-prefix-unique (-;₂ sn₁) (-;₂ sn₂) = ≃-; ≃-refl (snocA-prefix-unique sn₁ sn₂)
snocA-prefix-unique (brn sn₁ sn₂) (brn sn₃ sn₄) = ≃-brn (snocA-prefix-unique sn₁ sn₃) (snocA-prefix-unique sn₂ sn₄)
snocA-prefix-unique (mu {s = s} sn₁) (mu sn₂) = ≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (snocA-prefix-unique sn₁ sn₂)

------------------------------------------------------------------------
-- Prefix uniqueness (exact Snoc) — makes bwd-μ preserve the prefix.
------------------------------------------------------------------------

snoc-prefix-unique : {a : 𝕊 n} → Atom a → Snoc a w z₁ → Snoc a w z₂ → z₁ ≃ z₂
snoc-prefix-unique A here here = ≃-refl
snoc-prefix-unique A here (sn₂ ;₁ Sk) = case A of λ ()
snoc-prefix-unique A here (-;₂ sn₂) = case A of λ ()
snoc-prefix-unique A (sn₁ ;₁ Sk) here = case A of λ ()
snoc-prefix-unique A (-;₂ sn₁) here = case A of λ ()
snoc-prefix-unique A (sn₁ ;₁ Sk₁) (sn₂ ;₁ Sk₂) = snoc-prefix-unique A sn₁ sn₂
snoc-prefix-unique A (sn₁ ;₁ Sk₁) (-;₂ sn₂) = ⊥-elim (skips⊥snoc A Sk₁ sn₂)
snoc-prefix-unique A (-;₂ sn₁) (sn₂ ;₁ Sk₂) = ⊥-elim (skips⊥snoc A Sk₂ sn₁)
snoc-prefix-unique A (-;₂ sn₁) (-;₂ sn₂) = ≃-; ≃-refl (snoc-prefix-unique A sn₁ sn₂)
snoc-prefix-unique A (brn sn₁ sn₂) (brn sn₃ sn₄) = ≃-brn (snoc-prefix-unique A sn₁ sn₃) (snoc-prefix-unique A sn₂ sn₄)
snoc-prefix-unique {a = a} A (mu {s = s} sn₁) (mu sn₂) = ≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (snoc-prefix-unique (atom-⋯ᵣ A) sn₁ sn₂)

------------------------------------------------------------------------
-- ≃ transports Snoc, prefix preserved up to ≃ (fixed non-msg atom)
------------------------------------------------------------------------

SnocR : {n : ℕ} → 𝕊 n → 𝕊 n → 𝕊 n → Set
SnocR {n} a w₂ z = ∃[ z₂ ] Snoc a w₂ z₂ × z ≃ z₂

≃-snoc : {a : 𝕊 n} → Atom a → (∀ {p T} → a ≢ msg p T) → {w₁ w₂ : 𝕊 n} → w₁ ≃ w₂ → Snoc a w₁ z → SnocR a w₂ z
≃-snoc A nm refl sn = _ , sn , ≃-refl
≃-snoc {a = a} A nm (x ◅ xs) sn =
  let z₂ , sn₂ , e = go x sn ; z₃ , sn₃ , e′ = ≃-snoc A nm xs sn₂ in z₃ , sn₃ , ≃-trans e e′
  where
  go : {w₁ w₂ : 𝕊 _} → SymClosure _≃𝕊_ w₁ w₂ → Snoc a w₁ z → SnocR a w₂ z
  go (fwd (≃𝕊-msg x)) here = ⊥-elim (nm refl)
  go (bwd (≃𝕊-msg x)) here = ⊥-elim (nm refl)
  go (fwd ≃𝕊-μ) sn = _ , snoc-unfold A sn , ≃-refl
  go (bwd ≃𝕊-μ) sn = let z₂ , sn₂ = snoc-unfold⁻¹ᴬ A sn in z₂ , sn₂ , snoc-prefix-unique A sn (snoc-unfold A sn₂)
  go (fwd (≃𝕊-;₁ x)) (sn₁ ;₁ Sk) = let z₂ , sn₂ , e = go (fwd x) sn₁ in z₂ , sn₂ ;₁ Sk , e
  go (fwd (≃𝕊-;₁ x)) (-;₂ sn) = _ , -;₂ sn , ≃-; (Eq*.return x) ≃-refl
  go (bwd (≃𝕊-;₁ x)) (sn₁ ;₁ Sk) = let z₂ , sn₂ , e = go (bwd x) sn₁ in z₂ , sn₂ ;₁ Sk , e
  go (bwd (≃𝕊-;₁ x)) (-;₂ sn) = _ , -;₂ sn , ≃-; (≃-sym (Eq*.return x)) ≃-refl
  go (fwd (≃𝕊-;₂ x)) (sn₁ ;₁ Sk) = _ , sn₁ ;₁ ≃-skips (Eq*.return x) Sk , ≃-refl
  go (fwd (≃𝕊-;₂ x)) (-;₂ sn) = let z₂ , sn₂ , e = go (fwd x) sn in _ , -;₂ sn₂ , ≃-; ≃-refl e
  go (bwd (≃𝕊-;₂ x)) (sn₁ ;₁ Sk) = _ , sn₁ ;₁ ≃-skips (≃-sym (Eq*.return x)) Sk , ≃-refl
  go (bwd (≃𝕊-;₂ x)) (-;₂ sn) = let z₂ , sn₂ , e = go (bwd x) sn in _ , -;₂ sn₂ , ≃-; ≃-refl e
  go (fwd ≃𝕊-skipˡ) (sn₁ ;₁ Sk) = ⊥-elim (skips⊥snoc A skip sn₁)
  go (fwd ≃𝕊-skipˡ) (-;₂ sn) = _ , sn , ≃-skipˡ
  go (bwd ≃𝕊-skipˡ) sn = _ , -;₂ sn , ≃-sym ≃-skipˡ
  go (fwd ≃𝕊-skipʳ) (sn₁ ;₁ Sk) = _ , sn₁ , ≃-refl
  go (fwd ≃𝕊-skipʳ) (-;₂ sn) = ⊥-elim (skips⊥snoc A skip sn)
  go (bwd ≃𝕊-skipʳ) sn = _ , sn ;₁ skip , ≃-refl
  go (fwd ≃𝕊-assoc) ((sn₁ ;₁ Sk₂) ;₁ Sk₃) = _ , sn₁ ;₁ (Sk₂ ; Sk₃) , ≃-refl
  go (fwd ≃𝕊-assoc) ((-;₂ sn₂) ;₁ Sk₃) = _ , -;₂ (sn₂ ;₁ Sk₃) , ≃-refl
  go (fwd ≃𝕊-assoc) (-;₂ sn₃) = _ , -;₂ (-;₂ sn₃) , ≃-assoc-;
  go (bwd ≃𝕊-assoc) (sn₁ ;₁ (Sk₂ ; Sk₃)) = _ , (sn₁ ;₁ Sk₂) ;₁ Sk₃ , ≃-refl
  go (bwd ≃𝕊-assoc) (-;₂ (sn₂ ;₁ Sk₃)) = _ , (-;₂ sn₂) ;₁ Sk₃ , ≃-refl
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ sn₃)) = _ , -;₂ sn₃ , ≃-sym ≃-assoc-;
  go (fwd ≃𝕊-distr) (brn sn₁ sn₂ ;₁ Sk) = _ , brn (sn₁ ;₁ Sk) (sn₂ ;₁ Sk) , ≃-refl
  go (fwd ≃𝕊-distr) (-;₂ sn) = _ , brn (-;₂ sn) (-;₂ sn) , ≃-distr
  go (bwd ≃𝕊-distr) (brn (sn₁ ;₁ Sk₁) (sn₂ ;₁ Sk₂)) = _ , brn sn₁ sn₂ ;₁ Sk₂ , ≃-refl
  go (bwd ≃𝕊-distr) (brn (sn₁ ;₁ Sk₁) (-;₂ sn₂)) = ⊥-elim (skips⊥snoc A Sk₁ sn₂)
  go (bwd ≃𝕊-distr) (brn (-;₂ sn₁) (sn₂ ;₁ Sk₂)) = ⊥-elim (skips⊥snoc A Sk₂ sn₁)
  go (bwd ≃𝕊-distr) (brn (-;₂ sn₁) (-;₂ sn₂)) = _ , -;₂ sn₁ , ≃-trans (≃-brn ≃-refl (≃-; ≃-refl (snoc-prefix-unique A sn₂ sn₁))) (≃-sym ≃-distr)
  go (fwd (≃𝕊-brn₁ x)) (brn sn₁ sn₂) = let z₂ , sn₁′ , e = go (fwd x) sn₁ in _ , brn sn₁′ sn₂ , ≃-brn₁ e
  go (fwd (≃𝕊-brn₂ x)) (brn sn₁ sn₂) = let z₂ , sn₂′ , e = go (fwd x) sn₂ in _ , brn sn₁ sn₂′ , ≃-brn₂ e
  go (bwd (≃𝕊-brn₁ x)) (brn sn₁ sn₂) = let z₂ , sn₁′ , e = go (bwd x) sn₁ in _ , brn sn₁′ sn₂ , ≃-brn₁ e
  go (bwd (≃𝕊-brn₂ x)) (brn sn₁ sn₂) = let z₂ , sn₂′ , e = go (bwd x) sn₂ in _ , brn sn₁ sn₂′ , ≃-brn₂ e

unsnoc-nonmsg : {a : 𝕊 n} → Atom a → (∀ {p T} → a ≢ msg p T) →
  {x y z : 𝕊 n} → x ; y ≃ z ; a → Skips y ⊎ ∃[ y′ ] x ; y′ ≃ z × y′ ; a ≃ y
unsnoc-nonmsg {a = a} A nm {x}{y}{z} eq
  with z₂ , sn , zsk≃z₂ ← ≃-snoc A nm (≃-sym eq) (-;₂ here)
  with sn
... | here = case A of λ ()
... | (_ ;₁ Sky) = inj₁ Sky
... | (-;₂ sn-y) = inj₂ (_ , ≃-trans (≃-sym zsk≃z₂) ≃-skipʳ , ≃-sym (snoc-sound sn-y))

------------------------------------------------------------------------
-- msg case: SnocA transport (ending atom ≃ a, per branch)
------------------------------------------------------------------------

≃-var-rigid : {w : 𝔽 n}{α : 𝕊 n} → Atom α → ` w ≃ α → α ≡ ` w
≃-var-rigid {w = w} (`- {x = x}) e with w Fin.≟ x
... | yes refl = refl
... | no w≢x = ⊥-elim (atomKind≢⇒≄ `- `- (λ keq → w≢x (AKvar-inj keq)) e)
≃-var-rigid end e = ⊥-elim (atomKind≢⇒≄ `- end (λ ()) e)
≃-var-rigid msg e = ⊥-elim (atomKind≢⇒≄ `- msg (λ ()) e)
≃-var-rigid ret e = ⊥-elim (atomKind≢⇒≄ `- ret (λ ()) e)
≃-var-rigid acq e = ⊥-elim (atomKind≢⇒≄ `- acq (λ ()) e)
≃-var-rigid ``- e = ⊥-elim (atomKind≢⇒≄ `- ``- (λ ()) e)

------------------------------------------------------------------------
-- SnocM: msg-specialised Snoc (ending = msg p _, payload ≃ T).  Every leaf
-- is a msg atom, so no variable leaves and the index is scope-independent
-- (mu does not weaken it) — the whole SnocA stack collapses.
------------------------------------------------------------------------

data SnocM {n} (p : Pol) (T : 𝕋) : 𝕊 n → 𝕊 n → Set where
  here : {U : 𝕋} → U ≃ T → SnocM p T (msg p U) skip
  _;₁_ : SnocM p T s₁ z → Skips s₂ → SnocM p T (s₁ ; s₂) z
  -;₂_ : SnocM p T s₂ z → SnocM p T (s₁ ; s₂) (s₁ ; z)
  brn  : SnocM p T s₁ z₁ → SnocM p T s₂ z₂ → SnocM p T (brn p′ s₁ s₂) (brn p′ z₁ z₂)
  mu   : SnocM p T s z → SnocM p T (mu s) (z ⋯ ⦅ mu s ⦆ₛ)

snocM-sound : {p : Pol}{T : 𝕋} → SnocM p T w z → w ≃ z ; msg p T
snocM-sound (here e) = ≃-trans (Eq*.return (≃𝕊-msg e)) (≃-sym ≃-skipˡ)
snocM-sound (sn ;₁ Sk) = ≃-trans (≃-skipsʳ Sk) (snocM-sound sn)
snocM-sound (-;₂ sn) = ≃-trans (≃-; ≃-refl (snocM-sound sn)) (≃-sym ≃-assoc-;)
snocM-sound (brn sn₁ sn₂) = ≃-trans (≃-brn (snocM-sound sn₁) (snocM-sound sn₂)) (≃-sym ≃-distr)
snocM-sound {p = p}{T = T} (mu {s = s} {z = z} sn) =
  ≃-trans ≃-μ (≃-trans (≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (snocM-sound sn)) (≃-; ≃-refl ≃-refl))

skipsM⊥snocM : {p : Pol}{T : 𝕋} → Skips w → SnocM p T w z → ⊥
skipsM⊥snocM (Sk₁ ; Sk₂) (sn ;₁ _) = skipsM⊥snocM Sk₁ sn
skipsM⊥snocM (Sk₁ ; Sk₂) (-;₂ sn) = skipsM⊥snocM Sk₂ sn
skipsM⊥snocM (mu Sk) (mu sn) = skipsM⊥snocM Sk sn

snocM-mu⁻ : {p : Pol}{T : 𝕋} → SnocM p T (mu s) z → ∃[ z′ ] SnocM p T s z′
snocM-mu⁻ (mu sn) = _ , sn

snocM-;⁻ : {p : Pol}{T : 𝕋} → SnocM p T (s₁ ; s₂) z →
  (∃[ z′ ] SnocM p T s₁ z′ × Skips s₂) ⊎ (∃[ z′ ] SnocM p T s₂ z′)
snocM-;⁻ (sn ;₁ Sk) = inj₁ (_ , sn , Sk)
snocM-;⁻ (-;₂ sn) = inj₂ (_ , sn)

snocM-prefix-unique : {p : Pol}{T : 𝕋} → SnocM p T w z₁ → SnocM p T w z₂ → z₁ ≃ z₂
snocM-prefix-unique (here e₁) (here e₂) = ≃-refl
snocM-prefix-unique (sn₁ ;₁ Sk₁) (sn₂ ;₁ Sk₂) = snocM-prefix-unique sn₁ sn₂
snocM-prefix-unique (sn₁ ;₁ Sk₁) (-;₂ sn₂) = ⊥-elim (skipsM⊥snocM Sk₁ sn₂)
snocM-prefix-unique (-;₂ sn₁) (sn₂ ;₁ Sk₂) = ⊥-elim (skipsM⊥snocM Sk₂ sn₁)
snocM-prefix-unique (-;₂ sn₁) (-;₂ sn₂) = ≃-; ≃-refl (snocM-prefix-unique sn₁ sn₂)
snocM-prefix-unique (brn sn₁ sn₂) (brn sn₃ sn₄) = ≃-brn (snocM-prefix-unique sn₁ sn₃) (snocM-prefix-unique sn₂ sn₄)
snocM-prefix-unique (mu {s = s} sn₁) (mu sn₂) = ≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (snocM-prefix-unique sn₁ sn₂)

snocM-⋯ᵣ⁻¹ : {p : Pol}{T : 𝕋}{ρ : m →ᵣ n} → SnocM p T (s ⋯ ρ) z → ∃[ z₀ ] SnocM p T s z₀
snocM-⋯ᵣ⁻¹ {s = ` x} ()
snocM-⋯ᵣ⁻¹ {s = end q} ()
snocM-⋯ᵣ⁻¹ {s = ret} ()
snocM-⋯ᵣ⁻¹ {s = acq} ()
snocM-⋯ᵣ⁻¹ {s = `` γ} ()
snocM-⋯ᵣ⁻¹ {s = skip} ()
snocM-⋯ᵣ⁻¹ {s = msg q U} (here e) = _ , here e
snocM-⋯ᵣ⁻¹ {s = brn q s₁ s₂} (brn sn₁ sn₂) = _ , brn (proj₂ (snocM-⋯ᵣ⁻¹ sn₁)) (proj₂ (snocM-⋯ᵣ⁻¹ sn₂))
snocM-⋯ᵣ⁻¹ {s = s₁ ; s₂} (sn₁ ;₁ Sk) = _ , proj₂ (snocM-⋯ᵣ⁻¹ sn₁) ;₁ skips-⋯ᵣ⁻¹ Sk
snocM-⋯ᵣ⁻¹ {s = s₁ ; s₂} (-;₂ sn₂) = _ , -;₂ proj₂ (snocM-⋯ᵣ⁻¹ sn₂)
snocM-⋯ᵣ⁻¹ {s = mu s₀} (mu sn₀) = _ , mu (proj₂ (snocM-⋯ᵣ⁻¹ sn₀))

RSUMM : {n : ℕ}(p : Pol)(T : 𝕋)(m : ℕ)(img : 𝔽 m → 𝕊 n)(t : 𝕊 m) → Set
RSUMM {n} p T _ img t = ∃[ y ] EndsIn-` y t × (∃[ z′ ] SnocM p T (img y) z′) × (∀ x → img y ≢ ` x)

snocM-leafLR : {p : Pol}{T : 𝕋}(w : 𝕊 n) → SnocM p T w z → (∃[ z′ ] SnocM p T w z′) × (∀ x → w ≢ ` x)
snocM-leafLR (` x) ()
snocM-leafLR (end q) ()
snocM-leafLR ret ()
snocM-leafLR acq ()
snocM-leafLR (`` γ) ()
snocM-leafLR skip ()
snocM-leafLR (msg q U) sn = (_ , sn) , λ x ()
snocM-leafLR (brn q u₁ u₂) sn = (_ , sn) , λ x ()
snocM-leafLR (mu u) sn = (_ , sn) , λ x ()
snocM-leafLR (u₁ ; u₂) sn = (_ , sn) , λ x ()

snocM-⋯-sum : {p : Pol}{T : 𝕋}{ϕ : m →ₛ n} → (∀ x → ¬ Skips (`/id (ϕ x))) →
  {t : 𝕊 m} → SnocM p T (t ⋯ ϕ) z →
  (∃[ z′ ] SnocM p T t z′) ⊎ RSUMM p T _ (λ y → `/id (ϕ y)) t
snocM-⋯-sum {ϕ = ϕ} ∀¬S {t = ` y} sn = let r , nv = snocM-leafLR (`/id (ϕ y)) sn in inj₂ (y , here , r , nv)
snocM-⋯-sum ∀¬S {t = msg q U} (here e) = inj₁ (_ , here e)
snocM-⋯-sum ∀¬S {t = end q} ()
snocM-⋯-sum ∀¬S {t = ret} ()
snocM-⋯-sum ∀¬S {t = acq} ()
snocM-⋯-sum ∀¬S {t = `` γ} ()
snocM-⋯-sum ∀¬S {t = skip} ()
snocM-⋯-sum ∀¬S {t = brn q t₁ t₂} (brn sn₁ sn₂) with snocM-⋯-sum ∀¬S sn₁ | snocM-⋯-sum ∀¬S sn₂
... | inj₁ (_ , l₁) | inj₁ (_ , l₂) = inj₁ (_ , brn l₁ l₂)
... | inj₂ (y , E , snr , nv) | _ = inj₂ (y , brn (inj₁ E) , snr , nv)
... | inj₁ _ | inj₂ (y , E , snr , nv) = inj₂ (y , brn (inj₂ E) , snr , nv)
snocM-⋯-sum ∀¬S {t = t₁ ; t₂} (sn₁ ;₁ Sk) with snocM-⋯-sum ∀¬S sn₁
... | inj₁ (_ , l₁) = inj₁ (_ , l₁ ;₁ skips-⋯⁻¹ Sk ∀¬S)
... | inj₂ (y , E , snr , nv) = inj₂ (y , E ;₁ skips-⋯⁻¹ Sk ∀¬S , snr , nv)
snocM-⋯-sum ∀¬S {t = t₁ ; t₂} (-;₂ sn₂) with snocM-⋯-sum ∀¬S sn₂
... | inj₁ (_ , l₂) = inj₁ (_ , -;₂ l₂)
... | inj₂ (y , E , snr , nv) = inj₂ (y , -;₂ E , snr , nv)
snocM-⋯-sum {ϕ = ϕ} ∀¬S {t = mu t₀} (mu sn₀) with snocM-⋯-sum ∀¬S′ sn₀
  where
  ∀¬S′ : ∀ z → ¬ Skips (`/id ((ϕ ↑) z))
  ∀¬S′ zero = ¬skips-`/` Kₛ
  ∀¬S′ (suc z) = ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ z)))
... | inj₁ (_ , l₀) = inj₁ (_ , mu l₀)
... | inj₂ (zero , _ , _ , nv) = ⊥-elim (nv zero (`/`-is-` ⦃ Kₛ ⦄ zero))
... | inj₂ (suc y′ , E₀ , (z′ , sn′₀) , nv) =
  inj₂ (y′ , mu E₀ , snocM-⋯ᵣ⁻¹ (subst (λ w → SnocM _ _ w z′) (wk-`/id (ϕ y′)) sn′₀) ,
        λ x e → nv (suc x) (wk-`/id (ϕ y′) ■ cong (_⋯ weakenᵣ) e))

snocM-⋯ : {p : Pol}{T : 𝕋}{ϕ : m →ₛ n} → SnocM p T w z → SnocM p T (w ⋯ ϕ) (z ⋯ ϕ)
snocM-⋯ (here e) = here e
snocM-⋯ (sn ;₁ Sk) = snocM-⋯ sn ;₁ skips-⋯ Sk
snocM-⋯ (-;₂ sn) = -;₂ snocM-⋯ sn
snocM-⋯ (brn sn₁ sn₂) = brn (snocM-⋯ sn₁) (snocM-⋯ sn₂)
snocM-⋯ {ϕ = ϕ} (mu {s = s} {z = z} sn) =
  subst (SnocM _ _ (mu (s ⋯ ϕ ↑))) (sym (dist-↑-⦅⦆-⋯ z (mu s) ϕ)) (mu (snocM-⋯ {ϕ = ϕ ↑} sn))

snocM-unfold : {p : Pol}{T : 𝕋} → SnocM p T (mu s) z → SnocM p T (unfold s) z
snocM-unfold (mu {s = s} sn) = snocM-⋯ {ϕ = ⦅ mu s ⦆ₛ} sn

snocM-unfold⁻¹ : {p : Pol}{T : 𝕋} → SnocM p T (unfold s) z → ∃[ z′ ] SnocM p T (mu s) z′
snocM-unfold⁻¹ {s = s} sn with skips? s
... | yes Ss = ⊥-elim (skipsM⊥snocM (skips-⋯ Ss) sn)
... | no ¬Ss with snocM-⋯-sum {ϕ = ⦅ mu s ⦆ₛ} (∀¬Sϕ {s = s} ¬Ss) sn
...   | inj₁ (_ , l) = _ , mu l
...   | inj₂ (zero , _ , (z′ , snr) , _) = z′ , snr
...   | inj₂ (suc w , _ , _ , nv) = ⊥-elim (nv w refl)

SnocRM : {n : ℕ} → Pol → 𝕋 → 𝕊 n → 𝕊 n → Set
SnocRM {n} p T w₂ z = ∃[ z₂ ] SnocM p T w₂ z₂ × z ≃ z₂

≃-snocM : {p : Pol}{T : 𝕋} → {w₁ w₂ : 𝕊 n} → w₁ ≃ w₂ → SnocM p T w₁ z → SnocRM p T w₂ z
≃-snocM refl sn = _ , sn , ≃-refl
≃-snocM {p = p}{T = T} (x ◅ xs) sn =
  let z₂ , sn₂ , e = go x sn ; z₃ , sn₃ , e′ = ≃-snocM xs sn₂ in z₃ , sn₃ , ≃-trans e e′
  where
  go : {w₁ w₂ : 𝕊 _} → SymClosure _≃𝕊_ w₁ w₂ → SnocM p T w₁ z → SnocRM p T w₂ z
  go (fwd ≃𝕊-μ) (mu {s = s} sn) = _ , snocM-⋯ {ϕ = ⦅ mu s ⦆ₛ} sn , ≃-refl
  go (bwd ≃𝕊-μ) sn = let z₂ , sn₂ = snocM-unfold⁻¹ sn in z₂ , sn₂ , snocM-prefix-unique sn (snocM-unfold sn₂)
  go (fwd (≃𝕊-;₁ x)) (sn₁ ;₁ Sk) = let z₂ , sn₂ , e = go (fwd x) sn₁ in z₂ , sn₂ ;₁ Sk , e
  go (fwd (≃𝕊-;₁ x)) (-;₂ sn) = _ , -;₂ sn , ≃-; (Eq*.return x) ≃-refl
  go (bwd (≃𝕊-;₁ x)) (sn₁ ;₁ Sk) = let z₂ , sn₂ , e = go (bwd x) sn₁ in z₂ , sn₂ ;₁ Sk , e
  go (bwd (≃𝕊-;₁ x)) (-;₂ sn) = _ , -;₂ sn , ≃-; (≃-sym (Eq*.return x)) ≃-refl
  go (fwd (≃𝕊-;₂ x)) (sn₁ ;₁ Sk) = _ , sn₁ ;₁ ≃-skips (Eq*.return x) Sk , ≃-refl
  go (fwd (≃𝕊-;₂ x)) (-;₂ sn) = let z₂ , sn₂ , e = go (fwd x) sn in _ , -;₂ sn₂ , ≃-; ≃-refl e
  go (bwd (≃𝕊-;₂ x)) (sn₁ ;₁ Sk) = _ , sn₁ ;₁ ≃-skips (≃-sym (Eq*.return x)) Sk , ≃-refl
  go (bwd (≃𝕊-;₂ x)) (-;₂ sn) = let z₂ , sn₂ , e = go (bwd x) sn in _ , -;₂ sn₂ , ≃-; ≃-refl e
  go (fwd ≃𝕊-skipˡ) (sn₁ ;₁ Sk) = ⊥-elim (skipsM⊥snocM skip sn₁)
  go (fwd ≃𝕊-skipˡ) (-;₂ sn) = _ , sn , ≃-skipˡ
  go (bwd ≃𝕊-skipˡ) sn = _ , -;₂ sn , ≃-sym ≃-skipˡ
  go (fwd ≃𝕊-skipʳ) (sn₁ ;₁ Sk) = _ , sn₁ , ≃-refl
  go (fwd ≃𝕊-skipʳ) (-;₂ sn) = ⊥-elim (skipsM⊥snocM skip sn)
  go (bwd ≃𝕊-skipʳ) sn = _ , sn ;₁ skip , ≃-refl
  go (fwd ≃𝕊-assoc) ((sn₁ ;₁ Sk₂) ;₁ Sk₃) = _ , sn₁ ;₁ (Sk₂ ; Sk₃) , ≃-refl
  go (fwd ≃𝕊-assoc) ((-;₂ sn₂) ;₁ Sk₃) = _ , -;₂ (sn₂ ;₁ Sk₃) , ≃-refl
  go (fwd ≃𝕊-assoc) (-;₂ sn₃) = _ , -;₂ (-;₂ sn₃) , ≃-assoc-;
  go (bwd ≃𝕊-assoc) (sn₁ ;₁ (Sk₂ ; Sk₃)) = _ , (sn₁ ;₁ Sk₂) ;₁ Sk₃ , ≃-refl
  go (bwd ≃𝕊-assoc) (-;₂ (sn₂ ;₁ Sk₃)) = _ , (-;₂ sn₂) ;₁ Sk₃ , ≃-refl
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ sn₃)) = _ , -;₂ sn₃ , ≃-sym ≃-assoc-;
  go (fwd ≃𝕊-distr) (brn sn₁ sn₂ ;₁ Sk) = _ , brn (sn₁ ;₁ Sk) (sn₂ ;₁ Sk) , ≃-refl
  go (fwd ≃𝕊-distr) (-;₂ sn) = _ , brn (-;₂ sn) (-;₂ sn) , ≃-distr
  go (bwd ≃𝕊-distr) (brn (sn₁ ;₁ Sk₁) (sn₂ ;₁ Sk₂)) = _ , brn sn₁ sn₂ ;₁ Sk₂ , ≃-refl
  go (bwd ≃𝕊-distr) (brn (sn₁ ;₁ Sk₁) (-;₂ sn₂)) = ⊥-elim (skipsM⊥snocM Sk₁ sn₂)
  go (bwd ≃𝕊-distr) (brn (-;₂ sn₁) (sn₂ ;₁ Sk₂)) = ⊥-elim (skipsM⊥snocM Sk₂ sn₁)
  go (bwd ≃𝕊-distr) (brn (-;₂ sn₁) (-;₂ sn₂)) = _ , -;₂ sn₁ , ≃-trans (≃-brn ≃-refl (≃-; ≃-refl (snocM-prefix-unique sn₂ sn₁))) (≃-sym ≃-distr)
  go (fwd (≃𝕊-brn₁ x)) (brn sn₁ sn₂) = let z₂ , sn₁′ , e = go (fwd x) sn₁ in _ , brn sn₁′ sn₂ , ≃-brn₁ e
  go (fwd (≃𝕊-brn₂ x)) (brn sn₁ sn₂) = let z₂ , sn₂′ , e = go (fwd x) sn₂ in _ , brn sn₁ sn₂′ , ≃-brn₂ e
  go (bwd (≃𝕊-brn₁ x)) (brn sn₁ sn₂) = let z₂ , sn₁′ , e = go (bwd x) sn₁ in _ , brn sn₁′ sn₂ , ≃-brn₁ e
  go (bwd (≃𝕊-brn₂ x)) (brn sn₁ sn₂) = let z₂ , sn₂′ , e = go (bwd x) sn₂ in _ , brn sn₁ sn₂′ , ≃-brn₂ e
  go (fwd (≃𝕊-msg x)) (here e) = _ , here (≃-trans (≃-sym x) e) , ≃-refl
  go (bwd (≃𝕊-msg x)) (here e) = _ , here (≃-trans x e) , ≃-refl

unsnoc-msg : {p : Pol}{T : 𝕋} → {x y z : 𝕊 n} →
  x ; y ≃ z ; msg p T → Skips y ⊎ ∃[ y′ ] x ; y′ ≃ z × y′ ; msg p T ≃ y
unsnoc-msg {p = p}{T = T} {x}{y}{z} eq
  with z₂ , sn , zsk≃z₂ ← ≃-snocM (≃-sym eq) (-;₂ (here (≃-refl {t = T})))
  with sn
... | (_ ;₁ Sky) = inj₁ Sky
... | (-;₂ sn-y) = inj₂ (_ , ≃-trans (≃-sym zsk≃z₂) ≃-skipʳ , ≃-sym (snocM-sound sn-y))

atom-;-unsnoc : {a x y z : 𝕊 n} → Atom a → x ; y ≃ z ; a →
  Skips y ⊎ ∃[ y′ ] x ; y′ ≃ z × y′ ; a ≃ y
atom-;-unsnoc (`- {x = v}) eq = unsnoc-nonmsg `- (λ ()) eq
atom-;-unsnoc end eq = unsnoc-nonmsg end (λ ()) eq
atom-;-unsnoc ret eq = unsnoc-nonmsg ret (λ ()) eq
atom-;-unsnoc acq eq = unsnoc-nonmsg acq (λ ()) eq
atom-;-unsnoc ``- eq = unsnoc-nonmsg ``- (λ ()) eq
atom-;-unsnoc msg eq = unsnoc-msg eq
