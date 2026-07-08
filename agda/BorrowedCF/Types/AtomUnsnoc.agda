-- Machinery toward `atom-;-unsnoc` (Types/Equivalence): backward-μ
-- un-substitution for `Snoc`, for ALL ending atoms — the variable case (the
-- documented non-closed-kind "all-paths-from-one-path" wall) is CRACKED here.
--
--   snoc-⋯⁻¹       : callback-based un-substitution (closed ending atoms).
--   snoc-⋯-sum     : SUM-based un-substitution — recurses on the body `t` and
--                    the actual `Snoc` (NO ∀¬E callback), returning LEFT (Snoc
--                    of the pulled-back body) or RIGHT (ending via a compound
--                    ϕ-image). Because it holds both `brn` sub-`Snoc`s at once,
--                    it dissolves the one-branch limitation that blocked the
--                    variable case. `leafLR` matches the ϕ-image as an explicit
--                    argument (so the split is on a concrete bound var, not the
--                    opaque `/id(ϕ y)`); `⋯ᵣ-inj`/`wk-pb` lift the pullback.
--   snoc-unfold⁻¹ᴬ : μ-unfold un-substitution for EVERY atom (incl. `` ` v``).
--                    Verified hole/postulate-free.
--
-- Still open to close `atom-;-unsnoc` outright (NOT the variable wall):
--   * exact prefix tracking through the transport, i.e. `snoc-⋯-sum`/`snoc-⋯⁻¹`
--     must also return `z ≡ z′ ⋯ ϕ` so the μ-step preserves the prefix up to ≃;
--     otherwise the μ-step only yields `z ; a ≃ z′ ; a`, leaving a residual
--     right-cancellation `p ; a ≃ q ; a → p ≃ q` (a separate confluence lemma).
--   * `msg p T` ending: a ≃𝕊-msg step in one `brn` branch desyncs the two
--     branch payloads, so `Snoc` must be relaxed to ≃-branches (cf. `≃-msg⁻¹`).
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
