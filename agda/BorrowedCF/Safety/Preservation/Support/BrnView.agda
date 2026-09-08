-- | Front-peeling a `brn` head, i.e. cancellation for internal/external choice.
--
--   `Types.AtomCons` peels an ATOM off the front of a session and shows the
--   suffix is determined up to `_≃_`.  A `brn` is not an atom -- `_;_`
--   distributes over it -- so none of that applies, yet `R-Choice` needs
--   exactly the `brn` analogue: the sender's handle is `brn ‼ σ₁ σ₂` and the
--   receiver's is `brn ⁇ τ₁ τ₂`, and preservation only goes through once the
--   two are known to select equivalent continuations.
--
--   `BrnV p i w z` is `Cons` with its `here` constructor replaced: it witnesses
--   that `w` starts with a `p`-choice whose `i`-th branch (with everything that
--   follows it appended) is `z`.  Every proof below is the corresponding proof
--   of `Types.AtomCons`, simplified because a `brn` is never a variable, so all
--   of the `ClosedAtom` / `pullClosed` var-avoidance disappears.
module BorrowedCF.Safety.Preservation.Support.BrnView where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.AtomCons using (StartsVar; here; hd; tl; mu; skips⊥startsVar)
open import BorrowedCF.Types.Predicates using (New; `-; brn; mu; skip; new-⋯; _;_)
open import BorrowedCF.Safety.Preservation.Support.Dual using (dual-⋯ₛ)

open Nat.Variables

private variable
  w w₁ w₂ z z₁ z₂ z′ : 𝕊 n
  i : Bool

------------------------------------------------------------------------
-- Two `if` lemmas.
------------------------------------------------------------------------

if-cong-≃ : ∀ (b : Bool) {s₁ s₁′ s₂ s₂′ : 𝕊 n} →
  s₁ ≃ s₁′ → s₂ ≃ s₂′ → (if b then s₁ else s₂) ≃ (if b then s₁′ else s₂′)
if-cong-≃ true  eq₁ eq₂ = eq₁
if-cong-≃ false eq₁ eq₂ = eq₂

if-; : ∀ (b : Bool) (s₁ s₂ s : 𝕊 n) →
  (if b then s₁ else s₂) ; s ≡ (if b then s₁ ; s else s₂ ; s)
if-; true  _ _ _ = refl
if-; false _ _ _ = refl

if-⋯ : ∀ ⦃ K : Kit 𝓕 ⦄ (b : Bool) (s₁ s₂ : 𝕊 m) (ϕ : m –[ K ]→ n) →
  (if b then s₁ else s₂) ⋯ ϕ ≡ (if b then s₁ ⋯ ϕ else s₂ ⋯ ϕ)
if-⋯ true  _ _ _ = refl
if-⋯ false _ _ _ = refl

------------------------------------------------------------------------
-- BrnV p i w z : `w` starts with a `p`-choice; `z` is its `i`-th branch.
------------------------------------------------------------------------

data BrnV {n} (p : Pol) (i : Bool) : 𝕊 n → 𝕊 n → Set where
  here : ∀ {Z₁ Z₂ : 𝕊 n} → BrnV p i (brn p Z₁ Z₂) (if i then Z₁ else Z₂)
  hd   : BrnV p i s₁ z → BrnV p i (s₁ ; s₂) (z ; s₂)
  tl   : Skips s₁ → BrnV p i s₂ z → BrnV p i (s₁ ; s₂) z
  mu   : BrnV p i s z → BrnV p i (mu s) (z ⋯ ⦅ mu s ⦆ₛ)

------------------------------------------------------------------------
-- Inversions and refutations.
------------------------------------------------------------------------

skips⊥brnv : Skips w → BrnV p i w z → ⊥
skips⊥brnv (Sk₁ ; Sk₂) (hd c) = skips⊥brnv Sk₁ c
skips⊥brnv (Sk₁ ; Sk₂) (tl _ c) = skips⊥brnv Sk₂ c
skips⊥brnv (mu Sk) (mu c) = skips⊥brnv Sk c

brnv-mu⁻ : BrnV p i (mu s) z → ∃[ z′ ] BrnV p i s z′
brnv-mu⁻ (mu c) = _ , c

brnv-;⁻ : BrnV p i (s₁ ; s₂) z →
  (∃[ z′ ] BrnV p i s₁ z′) ⊎ (Skips s₁ × ∃[ z′ ] BrnV p i s₂ z′)
brnv-;⁻ (hd c) = inj₁ (_ , c)
brnv-;⁻ (tl Sk c) = inj₂ (Sk , _ , c)

-- The branch is determined up to `_≃_` (the mirror of `cons-suffix-unique`).
brnv-unique : BrnV p i w z₁ → BrnV p i w z₂ → z₁ ≃ z₂
brnv-unique here here = ≃-refl
brnv-unique (hd c₁) (hd c₂) = ≃-; (brnv-unique c₁ c₂) ≃-refl
brnv-unique (hd c₁) (tl Sk c₂) = ⊥-elim (skips⊥brnv Sk c₁)
brnv-unique (tl Sk c₁) (hd c₂) = ⊥-elim (skips⊥brnv Sk c₂)
brnv-unique (tl _ c₁) (tl _ c₂) = brnv-unique c₁ c₂
brnv-unique (mu {s = s} c₁) (mu c₂) = ≃-⋯ {ϕ = ⦅ mu s ⦆ₛ} (brnv-unique c₁ c₂)

------------------------------------------------------------------------
-- Substitution; the forward μ step.
------------------------------------------------------------------------

brnv-⋯ : {ϕ : m →ₛ n} → BrnV p i w z → BrnV p i (w ⋯ₛ ϕ) (z ⋯ₛ ϕ)
brnv-⋯ {i = i} {ϕ = ϕ} (here {Z₁ = Z₁} {Z₂ = Z₂}) =
  subst (BrnV _ i (brn _ (Z₁ ⋯ ϕ) (Z₂ ⋯ ϕ))) (sym (if-⋯ i Z₁ Z₂ ϕ)) here
brnv-⋯ (hd c) = hd (brnv-⋯ c)
brnv-⋯ (tl Sk c) = tl (skips-⋯ Sk) (brnv-⋯ c)
brnv-⋯ {ϕ = ϕ} (mu {s = s} {z = z} c) =
  subst (BrnV _ _ (mu (s ⋯ ϕ ↑))) (sym (dist-↑-⦅⦆-⋯ z (mu s) ϕ)) (mu (brnv-⋯ c))

brnv-unfold : BrnV p i (mu s) z → BrnV p i (unfold s) z
brnv-unfold (mu c) = brnv-⋯ c

------------------------------------------------------------------------
-- Backward μ un-substitution.
------------------------------------------------------------------------

brnv-⋯ᵣ⁻¹ : {ρ : m →ᵣ n} → BrnV p i (s ⋯ᵣ ρ) z → ∃[ z₀ ] BrnV p i s z₀
brnv-⋯ᵣ⁻¹ {s = brn q s₁ s₂} here = _ , here
brnv-⋯ᵣ⁻¹ {s = s₁ ; s₂} (hd c) = Π.map (_; s₂) hd (brnv-⋯ᵣ⁻¹ c)
brnv-⋯ᵣ⁻¹ {s = s₁ ; s₂} (tl Sk c) = Π.map₂ (tl (skips-⋯ᵣ⁻¹ Sk)) (brnv-⋯ᵣ⁻¹ c)
brnv-⋯ᵣ⁻¹ {s = mu s₀} (mu c) = Π.map (_⋯ ⦅ mu s₀ ⦆ₛ) mu (brnv-⋯ᵣ⁻¹ c)

-- If `s ⋯ ϕ` starts with a `p`-choice and `s` starts with the variable `y`,
-- then the image of `y` starts with a `p`-choice.
brnv⋯⇒brnv : {ϕ : m →ₛ n} → BrnV p i (s ⋯ₛ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) → ∀ {y} → StartsVar y s → ∃[ z′ ] BrnV p i (`/id (ϕ y)) z′
brnv⋯⇒brnv c ∀¬S here = _ , c
brnv⋯⇒brnv (hd c) ∀¬S (hd E) = brnv⋯⇒brnv c ∀¬S E
brnv⋯⇒brnv (tl Sk c) ∀¬S (hd E) = ⊥-elim (skips⊥startsVar (skips-⋯⁻¹ Sk ∀¬S) E)
brnv⋯⇒brnv (hd c) ∀¬S (tl Sk E) = ⊥-elim (skips⊥brnv (skips-⋯ Sk) c)
brnv⋯⇒brnv (tl _ c) ∀¬S (tl _ E) = brnv⋯⇒brnv c ∀¬S E
brnv⋯⇒brnv {p = p} {i = i} {ϕ = ϕ} (mu c) ∀¬S {y = y} (mu E) =
  let ∀¬S′ = λ where zero → ¬skips-`/` Kₛ
                     (suc x) → ∀¬S x ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id (ϕ x)))
      z′ , c′ = brnv⋯⇒brnv c ∀¬S′ E
  in brnv-⋯ᵣ⁻¹ (subst (λ w → BrnV p i w z′) (sym (wk-`/id (ϕ y))) c′)

brnv-⋯⁻¹ : {ϕ : m →ₛ n} →
  BrnV p i (s ⋯ ϕ) z →
  (∀ x → ¬ Skips (`/id (ϕ x))) →
  (∀ y → StartsVar y s → ∃[ z′ ] BrnV p i s z′) →
  ∃[ z′ ] BrnV p i s z′
brnv-⋯⁻¹ {s = ` x} c ∀¬S ∀¬E = ∀¬E x here
brnv-⋯⁻¹ {s = brn q s₁ s₂} here ∀¬S ∀¬E = _ , here
brnv-⋯⁻¹ {s = s₁ ; s₂} (hd c) ∀¬S ∀¬E =
  Π.map (λ w → w ; s₂) hd (brnv-⋯⁻¹ c ∀¬S
    (λ y E → Sum.[ (λ (z′ , c₀) → z′ , c₀)
                 , (λ (Sk , _) → ⊥-elim (skips⊥brnv (skips-⋯ Sk) c)) ]
             (brnv-;⁻ (proj₂ (∀¬E y (hd E))))))
brnv-⋯⁻¹ {s = s₁ ; s₂} (tl Sk c) ∀¬S ∀¬E =
  let Sk′ = skips-⋯⁻¹ Sk ∀¬S in
  Π.map₂ (tl Sk′) (brnv-⋯⁻¹ c ∀¬S
    (λ y E → Sum.[ (λ (_ , c₀) → ⊥-elim (skips⊥brnv Sk′ c₀))
                 , (λ (_ , z′ , c₀) → z′ , c₀) ]
             (brnv-;⁻ (proj₂ (∀¬E y (tl Sk′ E))))))
brnv-⋯⁻¹ {p = p} {i = i} {s = mu s₀} {ϕ = ϕ} (mu c) ∀¬S ∀¬E =
  Π.map (_⋯ ⦅ mu s₀ ⦆ₛ) mu (brnv-⋯⁻¹ c ∀¬S′ cb)
  where
  ∀¬S′ : ∀ z → ¬ Skips (`/id ((ϕ ↑) z))
  ∀¬S′ zero = ¬skips-`/` Kₛ
  ∀¬S′ (suc z) = ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id (ϕ z)))
  cb : ∀ z → StartsVar z s₀ → ∃[ z′ ] BrnV p i s₀ z′
  cb zero E =
    let z′ , c0 = brnv⋯⇒brnv {ϕ = ϕ ↑} c ∀¬S′ E in
    ⊥-elim (case subst (λ w → BrnV p i w z′) (`/`-is-` ⦃ Kₛ ⦄ zero) c0 of λ ())
  cb (suc z) E = brnv-mu⁻ (proj₂ (∀¬E z (mu E)))

brnv-unfold⁻¹ : BrnV p i (unfold s) z → ∃[ z′ ] BrnV p i (mu s) z′
brnv-unfold⁻¹ {p = p} {i = i} {s = s} c with skips? s
... | yes Ss = ⊥-elim (skips⊥brnv (skips-⋯ Ss) c)
... | no ¬Ss = Π.map (_⋯ ⦅ mu s ⦆ₛ) mu (brnv-⋯⁻¹ c ¬Sμ cb)
  where
  ¬Sμ : ∀ x → ¬ Skips (`/id (⦅ mu s ⦆ₛ x))
  ¬Sμ zero (mu Ss′) = ¬Ss Ss′
  ¬Sμ (suc x) = ¬skips-`
  cb : ∀ y → StartsVar y s → ∃[ z′ ] BrnV p i s z′
  cb zero E = brnv-mu⁻ (proj₂ (brnv⋯⇒brnv c ¬Sμ E))
  cb (suc x) E = ⊥-elim (case proj₂ (brnv⋯⇒brnv c ¬Sμ E) of λ ())

------------------------------------------------------------------------
-- `_≃_` transports a `brn` head, branch preserved up to `_≃_`.
------------------------------------------------------------------------

BrnR : 𝕊 n → Pol → Bool → 𝕊 n → Set
BrnR w₂ p i z = ∃[ z₂ ] BrnV p i w₂ z₂ × z ≃ z₂

private
  step : SymClosure _≃𝕊_ w₁ w₂ → BrnV p i w₁ z → BrnR w₂ p i z
  step (fwd ≃𝕊-μ) c = _ , brnv-unfold c , ≃-refl
  step (bwd ≃𝕊-μ) c = let z₂ , c₂ = brnv-unfold⁻¹ c in z₂ , c₂ , brnv-unique c (brnv-unfold c₂)
  step (fwd (≃𝕊-;₁ x)) (hd c) = let _ , c₂ , e = step (fwd x) c in _ , hd c₂ , ≃-; e ≃-refl
  step (fwd (≃𝕊-;₁ x)) (tl Sk c) = _ , tl (≃-skips (Eq*.return x) Sk) c , ≃-refl
  step (bwd (≃𝕊-;₁ x)) (hd c) = let _ , c₂ , e = step (bwd x) c in _ , hd c₂ , ≃-; e ≃-refl
  step (bwd (≃𝕊-;₁ x)) (tl Sk c) = _ , tl (≃-skips (≃-sym (Eq*.return x)) Sk) c , ≃-refl
  step (fwd (≃𝕊-;₂ x)) (hd c) = _ , hd c , ≃-; ≃-refl (Eq*.return x)
  step (fwd (≃𝕊-;₂ x)) (tl Sk c) = let _ , c₂ , e = step (fwd x) c in _ , tl Sk c₂ , e
  step (bwd (≃𝕊-;₂ x)) (hd c) = _ , hd c , ≃-; ≃-refl (≃-sym (Eq*.return x))
  step (bwd (≃𝕊-;₂ x)) (tl Sk c) = let _ , c₂ , e = step (bwd x) c in _ , tl Sk c₂ , e
  step (fwd ≃𝕊-skipˡ) (hd c) = ⊥-elim (skips⊥brnv skip c)
  step (fwd ≃𝕊-skipˡ) (tl _ c) = _ , c , ≃-refl
  step (bwd ≃𝕊-skipˡ) c = _ , tl skip c , ≃-refl
  step (fwd ≃𝕊-skipʳ) (hd c) = _ , c , ≃-skipʳ
  step (fwd ≃𝕊-skipʳ) (tl _ c) = ⊥-elim (skips⊥brnv skip c)
  step (bwd ≃𝕊-skipʳ) c = _ , hd c , ≃-sym ≃-skipʳ
  step (fwd ≃𝕊-assoc) (hd (hd c)) = _ , hd c , ≃-assoc-;
  step (fwd ≃𝕊-assoc) (hd (tl Sk c)) = _ , tl Sk (hd c) , ≃-refl
  step (fwd ≃𝕊-assoc) (tl (Sk₁ ; Sk₂) c) = _ , tl Sk₁ (tl Sk₂ c) , ≃-refl
  step (bwd ≃𝕊-assoc) (hd c) = _ , hd (hd c) , ≃-sym ≃-assoc-;
  step (bwd ≃𝕊-assoc) (tl Sk (hd c)) = _ , hd (tl Sk c) , ≃-refl
  step (bwd ≃𝕊-assoc) (tl Sk₁ (tl Sk₂ c)) = _ , tl (Sk₁ ; Sk₂) c , ≃-refl
  step {i = i} (fwd (≃𝕊-distr {s₁ = s₁} {s₂ = s₂} {s = s})) (hd here) =
    _ , here , ≃-reflexive (if-; i s₁ s₂ s)
  step (fwd ≃𝕊-distr) (tl () _)
  step {i = i} (bwd (≃𝕊-distr {s₁ = s₁} {s₂ = s₂} {s = s})) here =
    _ , hd here , ≃-reflexive (sym (if-; i s₁ s₂ s))
  step {i = i} (fwd (≃𝕊-brn₁ x)) here = _ , here , if-cong-≃ i (Eq*.return x) ≃-refl
  step {i = i} (fwd (≃𝕊-brn₂ x)) here = _ , here , if-cong-≃ i ≃-refl (Eq*.return x)
  step {i = i} (bwd (≃𝕊-brn₁ x)) here = _ , here , if-cong-≃ i (≃-sym (Eq*.return x)) ≃-refl
  step {i = i} (bwd (≃𝕊-brn₂ x)) here = _ , here , if-cong-≃ i ≃-refl (≃-sym (Eq*.return x))

≃-brnv : w₁ ≃ w₂ → BrnV p i w₁ z → BrnR w₂ p i z
≃-brnv refl c = _ , c , ≃-refl
≃-brnv (x ◅ xs) c =
  let _ , c₂ , e = step x c in
  let _ , c₃ , e′ = ≃-brnv xs c₂ in
  _ , c₃ , ≃-trans e e′

------------------------------------------------------------------------
-- THE PAYOFF: choices cancel branchwise.
------------------------------------------------------------------------

brn-cancel : ∀ (i : Bool) {X₁ X₂ X Y₁ Y₂ Y : 𝕊 n} →
  brn p X₁ X₂ ; X ≃ brn p Y₁ Y₂ ; Y →
  (if i then X₁ else X₂) ; X ≃ (if i then Y₁ else Y₂) ; Y
brn-cancel i eq with ≃-brnv {i = i} eq (hd here)
... | _ , hd here , e = e
... | _ , tl () _ , e

------------------------------------------------------------------------
-- `_≃_` transports a choice head, branch preserved up to `_≃_`.
------------------------------------------------------------------------

brn-cancel₀ : ∀ (i : Bool) {X₁ X₂ Y₁ Y₂ : 𝕊 n} →
  brn p X₁ X₂ ≃ brn p Y₁ Y₂ →
  (if i then X₁ else X₂) ≃ (if i then Y₁ else Y₂)
brn-cancel₀ i eq with ≃-brnv {i = i} eq here
... | _ , here , e = e

------------------------------------------------------------------------
-- `BrnV` commutes with duality and preserves `New`.
------------------------------------------------------------------------

if-dual : ∀ (b : Bool) (Z₁ Z₂ : 𝕊 n) → dual (if b then Z₁ else Z₂) ≡ (if b then dual Z₁ else dual Z₂)
if-dual true  _ _ = refl
if-dual false _ _ = refl

brnv-dual : BrnV p i w z → BrnV (dualPol p) i (dual w) (dual z)
brnv-dual {i = i} (here {Z₁ = Z₁} {Z₂ = Z₂}) =
  subst (BrnV _ i (brn _ (dual Z₁) (dual Z₂))) (sym (if-dual i Z₁ Z₂)) here
brnv-dual (hd c) = hd (brnv-dual c)
brnv-dual (tl Sk c) = tl (skips-dual⁺ Sk) (brnv-dual c)
brnv-dual (mu {s = s} {z = z} c) =
  subst (BrnV _ _ (mu (dual s))) (sym (dual-⋯ₛ z ⦅ mu s ⦆ₛ ■ ⋯-cong (dual z) eq)) (mu (brnv-dual c))
  where
  eq : (dual ∘ ⦅ mu s ⦆ₛ) ≗ ⦅ mu (dual s) ⦆ₛ
  eq zero = refl
  eq (suc x) = refl

if-New : ∀ (b : Bool) {Z₁ Z₂ : 𝕊 n} → New Z₁ → New Z₂ → New (if b then Z₁ else Z₂)
if-New true  N₁ N₂ = N₁
if-New false N₁ N₂ = N₂

brnv-new : New w → BrnV p i w z → New z
brnv-new {i = i} (brn N₁ N₂) here = if-New i N₁ N₂
brnv-new (N₁ ; N₂) (hd c) = brnv-new N₁ c ; N₂
brnv-new (N₁ ; N₂) (tl _ c) = brnv-new N₂ c
brnv-new (mu N) (mu c) = new-⋯ (brnv-new N c) λ where
  zero → mu N
  (suc x) → `-
