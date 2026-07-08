{-# OPTIONS --allow-unsolved-metas #-}

module BorrowedCF.Types.Predicates where

open import Relation.Binary.Construct.Closure.Symmetric as Sym using (SymClosure; fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Equivalence
open import BorrowedCF.Types.Substitution
open import BorrowedCF.Types.Syntax

open Un hiding (U)
open Bin using (_Respects_)
open Nat.Variables

EndsIn-` : 𝔽 n → 𝕊 n → Set
EndsIn-` x = EndsIn one {` x} `-

data Bounded {n} : 𝕊 n → Set where
  end  : Bounded (end p)
  ret  : Bounded ret
  _;₁_ : Bounded s₁ → Skips s₂ → Bounded (s₁ ; s₂)
  -;₂_ : Bounded s₂ → Bounded (s₁ ; s₂)
  mu   : Bounded s → Bounded (mu s)
  brn  : Bounded s₁ → Bounded s₂ → Bounded (brn p s₁ s₂)

¬bounded-` : {x : 𝔽 n} → ¬ Bounded (` x)
¬bounded-` ()

bounded-mu⁻ : Bounded (mu s) → Bounded s
bounded-mu⁻ (mu B) = B

bounded-brn⁻ : Bounded (brn p s₁ s₂) → Bounded s₁ × Bounded s₂
bounded-brn⁻ (brn b₁ b₂) = b₁ , b₂

bounded-;⁻ : Bounded (s₁ ; s₂) → Bounded s₁ × Skips s₂ ⊎ Bounded s₂
bounded-;⁻ (b₁ ;₁ s₂) = inj₁ (b₁ , s₂)
bounded-;⁻ (-;₂ b₂)   = inj₂ b₂

skips⊥bounded : Skips s → Bounded s → ⊥
skips⊥bounded (s₁ ; s₂) (b ;₁ x) = skips⊥bounded s₁ b
skips⊥bounded (s₁ ; s₂) (-;₂ b) = skips⊥bounded s₂ b
skips⊥bounded (mu s) (mu b) = skips⊥bounded s b

bounded-⋯ᵣ : {ρ : m →ᵣ n} → Bounded s → Bounded (s ⋯ ρ)
bounded-⋯ᵣ end = end
bounded-⋯ᵣ ret = ret
bounded-⋯ᵣ (b ;₁ x) = bounded-⋯ᵣ b ;₁ skips-⋯ x
bounded-⋯ᵣ (-;₂ b) = -;₂ bounded-⋯ᵣ b
bounded-⋯ᵣ (mu b) = mu (bounded-⋯ᵣ b)
bounded-⋯ᵣ (brn b b₁) = brn (bounded-⋯ᵣ b) (bounded-⋯ᵣ b₁)

bounded-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Bounded s → Bounded (s ⋯ ϕ)
bounded-⋯ end = end
bounded-⋯ ret = ret
bounded-⋯ (b ;₁ x) = bounded-⋯ b ;₁ skips-⋯ x
bounded-⋯ (-;₂ b) = -;₂ bounded-⋯ b
bounded-⋯ (mu b) = mu (bounded-⋯ b)
bounded-⋯ (brn b b₁) = brn (bounded-⋯ b) (bounded-⋯ b₁)

bounded-⋯ᵣ⁻¹ : {ϕ : m →ᵣ n} → Bounded (s ⋯ ϕ) → Bounded s
bounded-⋯ᵣ⁻¹ {s = end p} end = end
bounded-⋯ᵣ⁻¹ {s = brn p s₁ s₂} (brn B B₁) = brn (bounded-⋯ᵣ⁻¹ B) (bounded-⋯ᵣ⁻¹ B₁)
bounded-⋯ᵣ⁻¹ {s = mu s} (mu B) = mu (bounded-⋯ᵣ⁻¹ B)
bounded-⋯ᵣ⁻¹ {s = s₁ ; s₂} (B ;₁ x) = bounded-⋯ᵣ⁻¹ B ;₁ skips-⋯ᵣ⁻¹ x
bounded-⋯ᵣ⁻¹ {s = s₁ ; s₂} (-;₂ B) = -;₂ bounded-⋯ᵣ⁻¹ B
bounded-⋯ᵣ⁻¹ {s = ret} ret = ret

bounded⋯⇒¬endsIn⊎bounded : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} →
  Bounded (s ⋯ ϕ) →
  (∀ z → ¬ Skips (`/id (ϕ z))) →
  ∀ {z} → EndsIn-` z s → Bounded (`/id (ϕ z))
bounded⋯⇒¬endsIn⊎bounded B ∀¬S here = B
bounded⋯⇒¬endsIn⊎bounded (B ;₁ x₁) ∀¬S (E ;₁ x) = bounded⋯⇒¬endsIn⊎bounded B ∀¬S E
bounded⋯⇒¬endsIn⊎bounded (-;₂ B) ∀¬S (E ;₁ s) = ⊥-elim (skips⊥bounded (skips-⋯ s) B)
bounded⋯⇒¬endsIn⊎bounded (B ;₁ s) ∀¬S (-;₂ E) = ⊥-elim (skips⊥endsIn (skips-⋯⁻¹ s ∀¬S) E)
bounded⋯⇒¬endsIn⊎bounded (-;₂ B) ∀¬S (-;₂ E) = bounded⋯⇒¬endsIn⊎bounded B ∀¬S E
bounded⋯⇒¬endsIn⊎bounded (brn B₁ B₂) ∀¬S (brn (inj₁ E)) = bounded⋯⇒¬endsIn⊎bounded B₁ ∀¬S E
bounded⋯⇒¬endsIn⊎bounded (brn B₁ B₂) ∀¬S (brn (inj₂ E)) = bounded⋯⇒¬endsIn⊎bounded B₂ ∀¬S E
bounded⋯⇒¬endsIn⊎bounded ⦃ K ⦄ (mu B) ∀¬S (mu E) =
  let IH = bounded⋯⇒¬endsIn⊎bounded B (λ{ zero → ¬skips-`/` K; (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _)) }) E in
  bounded-⋯ᵣ⁻¹ (subst Bounded (sym (wk-`/id _)) IH)

bounded-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Bounded (s ⋯ ϕ)
  → (∀ z → ¬ Skips (`/id (ϕ z)))
  → (∀ z → EndsIn-` z s → Bounded s)
  → Bounded s
bounded-⋯⁻¹ {s = ` x} B ∀¬S ∀¬E = ∀¬E x here
bounded-⋯⁻¹ {s = end p} B ∀¬S ∀¬E = end
bounded-⋯⁻¹ {s = brn p s₁ s₂} (brn B₁ B₂) ∀¬S ∀¬E =
  brn (bounded-⋯⁻¹ B₁ ∀¬S λ z → proj₁ ∘ bounded-brn⁻ ∘ ∀¬E z ∘ brn ∘′ inj₁)
      (bounded-⋯⁻¹ B₂ ∀¬S λ z → proj₂ ∘ bounded-brn⁻ ∘ ∀¬E z ∘ brn ∘′ inj₂)
bounded-⋯⁻¹ {s = mu s} ⦃ K ⦄ (mu B) ∀¬S ∀¬E =
  let ∀¬S′ = λ where zero    → ¬skips-`/` K
                     (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _))
  in
  mu (bounded-⋯⁻¹ B ∀¬S′ λ where
    zero    → ⊥-elim ∘ ¬bounded-` ∘ subst Bounded (`/`-is-` ⦃ K ⦄ _) ∘ bounded⋯⇒¬endsIn⊎bounded B ∀¬S′
    (suc z) → bounded-mu⁻ ∘ ∀¬E z ∘ mu)
bounded-⋯⁻¹ {s = s₁ ; s₂} (B ;₁ s) ∀¬S ∀¬E =
  let s′ = skips-⋯⁻¹ s ∀¬S in
  bounded-⋯⁻¹ B ∀¬S (λ z E → proj₁ $ Sum.fromInj₁ (⊥-elim ∘ skips⊥bounded s′) $ bounded-;⁻ $ ∀¬E z (E ;₁ s′)) ;₁ s′
bounded-⋯⁻¹ {s = s₁ ; s₂} (-;₂ B) ∀¬S ∀¬E = -;₂ bounded-⋯⁻¹ B ∀¬S λ z →
  Sum.fromInj₂ (⊥-elim ∘ flip skips⊥bounded B ∘ skips-⋯ ∘ proj₂) ∘ bounded-;⁻ ∘ ∀¬E z ∘ -;₂_
bounded-⋯⁻¹ {s = ret} B ∀¬S ∀¬E = ret

bounded-unfold⁻¹ : Bounded (unfold s) → Bounded s
bounded-unfold⁻¹ {s = s} B with skips? s
... | yes Ss = ⊥-elim (skips⊥bounded (skips-⋯ Ss) B)
... | no ¬Ss =
  let ¬skips-unfold = λ{ zero (mu Ss) → ¬Ss Ss } in
  bounded-⋯⁻¹ B ¬skips-unfold λ where
    zero    E → bounded-mu⁻ $ bounded⋯⇒¬endsIn⊎bounded B ¬skips-unfold E
    (suc x) E → ⊥-elim $ ¬bounded-` $ bounded⋯⇒¬endsIn⊎bounded B ¬skips-unfold E

≃-bounded : Bounded {n} Respects _≃_
≃-bounded refl = id
≃-bounded (x ◅ xs) = ≃-bounded xs ∘ go x where
  go : SymClosure _≃𝕊_ s₁ s₂ → Bounded s₁ → Bounded s₂
  go (fwd ≃𝕊-μ) (mu b) = bounded-⋯ b
  go (fwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (fwd x) b ;₁ x₁
  go (fwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
  go (fwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Eq*.return x) x₁
  go (fwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (fwd x) b
  go (fwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (fwd x) b) b₁
  go (fwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (fwd x) b₁)
  go (fwd ≃𝕊-skipˡ) (-;₂ b) = b
  go (fwd ≃𝕊-skipʳ) (b ;₁ x) = b
  go (fwd ≃𝕊-skipˡ) (() ;₁ _)
  go (fwd ≃𝕊-skipʳ) (-;₂ ())
  go (fwd ≃𝕊-assoc) ((b ;₁ x₁) ;₁ x) = b ;₁ (x₁ ; x)
  go (fwd ≃𝕊-assoc) ((-;₂ b) ;₁ x) = -;₂ (b ;₁ x)
  go (fwd ≃𝕊-assoc) (-;₂ b) = -;₂ (-;₂ b)
  go (fwd ≃𝕊-distr) (brn b b₁ ;₁ x) = brn (b ;₁ x) (b₁ ;₁ x)
  go (fwd ≃𝕊-distr) (-;₂ b) = brn (-;₂ b) (-;₂ b)
  go (bwd (≃𝕊-;₁ x)) (b ;₁ x₁) = go (bwd x) b ;₁ x₁
  go (bwd (≃𝕊-;₁ x)) (-;₂ b) = -;₂ b
  go (bwd (≃𝕊-;₂ x)) (b ;₁ x₁) = b ;₁ ≃-skips (Star.return (bwd x)) x₁
  go (bwd (≃𝕊-;₂ x)) (-;₂ b) = -;₂ go (bwd x) b
  go (bwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (bwd x) b) b₁
  go (bwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (bwd x) b₁)
  go (bwd ≃𝕊-μ) b = mu (bounded-unfold⁻¹ b)
  go (bwd ≃𝕊-skipˡ) b = -;₂ b
  go (bwd ≃𝕊-skipʳ) b = b ;₁ skip
  go (bwd ≃𝕊-assoc) (b ;₁ (x ; x₁)) = (b ;₁ x) ;₁ x₁
  go (bwd ≃𝕊-assoc) (-;₂ (b ;₁ x)) = (-;₂ b) ;₁ x
  go (bwd ≃𝕊-assoc) (-;₂ (-;₂ b)) = -;₂ b
  go (bwd ≃𝕊-distr) (brn (b ;₁ x) (b₁ ;₁ x₁)) = brn b b₁ ;₁ x₁
  go (bwd ≃𝕊-distr) (brn (b ;₁ x) (-;₂ b₁)) = -;₂ b₁
  go (bwd ≃𝕊-distr) (brn (-;₂ b) b₁) = -;₂ b

module _ (PA : Arr → Set) (PS : 𝕊 0 → Set) where
  data TPred : 𝕋 → Set where
    `⊤  : TPred `⊤
    arr : PA a → TPred (T ⟨ a ⟩→ U)
    _⊗_ : TPred T → TPred U → TPred (T ⊗⟨ d ⟩ U)
    _⊕_ : TPred T → TPred U → TPred (T ⊕ U)
    ⟨_⟩ : PS s → TPred ⟨ s ⟩

tpred-≃ : {PA : Arr → Set} {PS : 𝕊 0 → Set} → PS Respects _≃_ → TPred PA PS Respects _≃_
tpred-≃ ps≃ `⊤ `⊤ = `⊤
tpred-≃ ps≃ (eq₁ ⊗ eq₂) (px ⊗ py) = tpred-≃ ps≃ eq₁ px ⊗ tpred-≃ ps≃ eq₂ py
tpred-≃ ps≃ (eq₁ ⊕ eq₂) (px ⊕ py) = tpred-≃ ps≃ eq₁ px ⊕ tpred-≃ ps≃ eq₂ py
tpred-≃ ps≃ (eq₁ `→ eq₂) (arr pa) = arr pa
tpred-≃ ps≃ ⟨ eq ⟩ ⟨ ps ⟩ = ⟨ ps≃ eq ps ⟩

tpred-map : {PA₁ PA₂ : Arr → Set} {PS₁ PS₂ : 𝕊 0 → Set} → PA₁ ⊆ PA₂ → PS₁ ⊆ PS₂ → TPred PA₁ PS₁ ⊆ TPred PA₂ PS₂
tpred-map pa⊆ ps⊆ `⊤ = `⊤
tpred-map pa⊆ ps⊆ (arr pa) = arr (pa⊆ pa)
tpred-map pa⊆ ps⊆ (px ⊗ py) = tpred-map pa⊆ ps⊆ px ⊗ tpred-map pa⊆ ps⊆ py
tpred-map pa⊆ ps⊆ (px ⊕ py) = tpred-map pa⊆ ps⊆ px ⊕ tpred-map pa⊆ ps⊆ py
tpred-map pa⊆ ps⊆ ⟨ s ⟩ = ⟨ ps⊆ s ⟩

tpred? : {PA : Arr → Set} {PS : 𝕊 0 → Set} → Decidable PA → Decidable PS → Decidable (TPred PA PS)
tpred? pa? ps? ⟨ s ⟩ = map′ ⟨_⟩ (λ{ ⟨ ps ⟩ → ps }) (ps? s)
tpred? pa? ps? `⊤ = yes `⊤
tpred? pa? ps? (t ⟨ a ⟩→ u) = map′ arr (λ{ (arr pa) → pa }) (pa? a)
tpred? pa? ps? (t ⊗⟨ d ⟩ u) = map′ (uncurry _⊗_) (λ{ (pt ⊗ pu) → pt , pu }) (tpred? pa? ps? t ×-dec tpred? pa? ps? u)
tpred? pa? ps? (t ⊕ u) = map′ (uncurry _⊕_) (λ{ (pt ⊕ pu) → pt , pu }) (tpred? pa? ps? t ×-dec tpred? pa? ps? u)

Mobile = TPred Arr.Mobile (λ s → ∃[ s′ ] Bounded s′ × s ≃ acq ; s′)

Unr = TPred Arr.Unr (λ _ → ⊥)

unr⇒mobile : Unr ⊆ Mobile
unr⇒mobile = tpred-map (λ {a} → Arr.ω⇒M a) (λ ())

mobile-≃ : Mobile Respects _≃_
mobile-≃ = tpred-≃ λ eq → Π.map₂ (Π.map₂ (≃-trans (≃-sym eq)))

unr-≃ : Unr Respects _≃_
unr-≃ = tpred-≃ λ _ ()

unr? : Un.Decidable Unr
unr? = tpred? lin? (λ _ → no λ ())
  where lin? : ∀ a → Dec (Arr.Unr a)
        lin? a with Arr.lin a
        ... | 𝟙 = no λ()
        ... | unr = yes refl

data Solved : ∀ {κ x} → Ty κ x → Set where
  ⟨_⟩ : Solved s → Solved ⟨ s ⟩
  `⊤ : Solved `⊤
  _⟨_⟩→_ : Solved T → (a : Arr) → Solved U → Solved (T ⟨ a ⟩→ U)
  _⊗⟨_⟩_ : Solved T → (d : Dir) → Solved U → Solved (T ⊗⟨ d ⟩ U)
  _⊕_ : Solved T → Solved U → Solved (T ⊕ U)

  `_ : (x : 𝔽 n) → Solved (` x)
  end : Solved (end {n} p)
  msg : Solved T → Solved (msg {n} p T)
  brn : Solved s₁ → Solved s₂ → Solved (brn p s₁ s₂)
  mu : Solved s → Solved (mu s)
  _;_ : Solved s₁ → Solved s₂ → Solved (s₁ ; s₂)
  skip : Solved {x = n} skip
  acq : Solved {x = n} acq
  ret : Solved {x = n} ret

solved-⋯ᵣ : Solved s → {ρ : m →ᵣ n} → Solved (s ⋯ ρ)
solved-⋯ᵣ (` x) = ` _
solved-⋯ᵣ end = end
solved-⋯ᵣ (msg x) = msg x
solved-⋯ᵣ (brn x x₁) = brn (solved-⋯ᵣ x) (solved-⋯ᵣ x₁)
solved-⋯ᵣ (mu x) = mu (solved-⋯ᵣ x)
solved-⋯ᵣ (x ; x₁) = solved-⋯ᵣ x ; solved-⋯ᵣ x₁
solved-⋯ᵣ skip = skip
solved-⋯ᵣ acq = acq
solved-⋯ᵣ ret = ret

solved-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → Solved s → {ϕ : m –[ K ]→ n} → (∀ x → Solved (`/id (ϕ x))) → Solved (s ⋯ ϕ)
solved-⋯ (` x) ∀solved = ∀solved x
solved-⋯ end ∀solved = end
solved-⋯ (msg x) ∀solved = msg x
solved-⋯ (brn x₁ x₂) ∀solved = brn (solved-⋯ x₁ ∀solved) (solved-⋯ x₂ ∀solved)
solved-⋯ ⦃ K ⦄ (mu x) ∀solved = Solved.mu $ solved-⋯ x λ where
  zero → subst Solved (sym (`/`-is-` ⦃ K ⦄ _)) (` zero)
  (suc y) → subst Solved (wk-`/id _) (solved-⋯ᵣ (∀solved y))
solved-⋯ (x ; x₁) ∀solved = solved-⋯ x ∀solved ; solved-⋯ x₁ ∀solved
solved-⋯ skip ∀solved = skip
solved-⋯ acq ∀solved = acq
solved-⋯ ret ∀solved = ret

solved-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Solved (s ⋯ ϕ) → Solved s
solved-⋯⁻¹ {s = ` x₁} x = ` x₁
solved-⋯⁻¹ {s = end p} x = end
solved-⋯⁻¹ {s = msg p t} (msg x) = msg x
solved-⋯⁻¹ {s = brn p s₁ s₂} (brn x x₁) = brn (solved-⋯⁻¹ x) (solved-⋯⁻¹ x₁)
solved-⋯⁻¹ {s = mu s} (mu x) = mu (solved-⋯⁻¹ x)
solved-⋯⁻¹ {s = s₁ ; s₂} (x ; x₁) = solved-⋯⁻¹ x ; solved-⋯⁻¹ x₁
solved-⋯⁻¹ {s = skip} x = skip
solved-⋯⁻¹ {s = ret} x = ret
solved-⋯⁻¹ {s = acq} x = acq

solved-dual : Solved s → Solved (dual s)
solved-dual (` x) = ` x
solved-dual end = end
solved-dual (msg s) = msg s
solved-dual (brn s s₁) = brn (solved-dual s) (solved-dual s₁)
solved-dual (mu s) = mu (solved-dual s)
solved-dual (s ; s₁) = solved-dual s ; solved-dual s₁
solved-dual skip = skip
solved-dual acq = acq
solved-dual ret = ret

eqSize  : ∀ {κ x} {a b : Ty κ x} → a ≃ b → ℕ
eqSize′ : s₁ ≃𝕊 s₂ → ℕ

eqSize {𝕤} refl = 0
eqSize {𝕤} (fwd x ◅ xs) = suc (eqSize′ x + eqSize xs)
eqSize {𝕤} (bwd x ◅ xs) = suc (eqSize′ x + eqSize xs)
eqSize {𝕥} `⊤ = 0
eqSize {𝕥} (x ⊗ y) = suc (eqSize x + eqSize y)
eqSize {𝕥} (x ⊕ y) = suc (eqSize x + eqSize y)
eqSize {𝕥} (x `→ y) = suc (eqSize x + eqSize y)
eqSize {𝕥} ⟨ x ⟩ = suc (eqSize x)

eqSize′ (≃𝕊-;₁ x) = suc (eqSize′ x)
eqSize′ (≃𝕊-;₂ x) = suc (eqSize′ x)
eqSize′ ≃𝕊-skipˡ = 0
eqSize′ ≃𝕊-skipʳ = 0
eqSize′ ≃𝕊-μ = 0
eqSize′ ≃𝕊-assoc = 0
eqSize′ ≃𝕊-distr = 0
eqSize′ (≃𝕊-msg x) = suc (eqSize x)
eqSize′ (≃𝕊-brn₁ x) = suc (eqSize′ x)
eqSize′ (≃𝕊-brn₂ x) = suc (eqSize′ x)

≃-solved : ∀ {κ x} → Solved {κ} {x} Respects _≃_
≃-solved {𝕤} refl x = x
≃-solved {𝕤} {n} (x ◅ xs) = ≃-solved xs ∘ go x where
  go : Solved {𝕤} {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x₁ ; x₂) = go (fwd eq) x₁ ; x₂
  go (fwd (≃𝕊-;₂ eq)) (x₁ ; x₂) = x₁ ; go (fwd eq) x₂
  go (fwd (≃𝕊-msg x)) (msg T) = msg (≃-solved x T)
  go (fwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (fwd x) b) b₁
  go (fwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (fwd x) b₁)
  go (fwd ≃𝕊-skipˡ) (x₁ ; x₂) = x₂
  go (fwd ≃𝕊-skipʳ) (x₁ ; x₂) = x₁
  go (fwd ≃𝕊-μ) (mu x) = solved-⋯ x λ where
    zero → mu x
    (suc y) → ` y
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (bwd (≃𝕊-;₁ eq)) (x₁ ; x₂) = go (bwd eq) x₁ ; x₂
  go (bwd (≃𝕊-;₂ eq)) (x₁ ; x₂) = x₁ ; go (bwd eq) x₂
  go (bwd (≃𝕊-msg x)) (msg T) = {!msg (≃-solved (≃-sym x) T)!}  -- breaks the termination check, maybe use eqSize as an induction measure
  go (bwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (bwd x) b) b₁
  go (bwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (bwd x) b₁)
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (solved-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y
≃-solved {𝕥} `⊤ x = x
≃-solved {𝕥} (eq ⊗ eq₁) (x ⊗⟨ d ⟩ x₁) = ≃-solved eq x ⊗⟨ d ⟩ ≃-solved eq₁ x₁
≃-solved {𝕥} (eq ⊕ eq₁) (x ⊕ x₁) = ≃-solved eq x ⊕ ≃-solved eq₁ x₁
≃-solved {𝕥} (eq `→ eq₁) (x ⟨ a ⟩→ x₁) = ≃-solved eq x ⟨ a ⟩→ ≃-solved eq₁ x₁
≃-solved {𝕥} ⟨ eq ⟩ ⟨ x ⟩ = ⟨ ≃-solved eq x ⟩

data New {n} : 𝕊 n → Set where
  `-  : ∀ {x} → New (` x)
  msg : New (msg p T)
  brn : New s₁ → New s₂ → New (brn p s₁ s₂)
  mu : New s → New (mu s)
  _;_ : New s₁ → New s₂ → New (s₁ ; s₂)
  skip : New skip

new-⋯ᵣ : New s → {ρ : m →ᵣ n} → New (s ⋯ ρ)
new-⋯ᵣ `- = `-
new-⋯ᵣ msg = msg
new-⋯ᵣ (brn x x₁) = brn (new-⋯ᵣ x) (new-⋯ᵣ x₁)
new-⋯ᵣ (mu x) = mu (new-⋯ᵣ x)
new-⋯ᵣ (x ; x₁) = new-⋯ᵣ x ; new-⋯ᵣ x₁
new-⋯ᵣ skip = skip

new-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ → New s → {ϕ : m –[ K ]→ n} → (∀ x → New (`/id (ϕ x))) → New (s ⋯ ϕ)
new-⋯ `- ∀ϕ-new = ∀ϕ-new _
new-⋯ msg ∀ϕ-new = msg
new-⋯ (brn x y) ∀ϕ-new = brn (new-⋯ x ∀ϕ-new) (new-⋯ y ∀ϕ-new)
new-⋯ ⦃ K ⦄ (mu x) ∀ϕ-new = New.mu $ new-⋯ x λ where
  zero → subst New (sym (`/`-is-` ⦃ K ⦄ _)) `-
  (suc z) → subst New (wk-`/id _) (new-⋯ᵣ (∀ϕ-new z))
new-⋯ (x ; y) ∀ϕ-new = new-⋯ x ∀ϕ-new ; new-⋯ y ∀ϕ-new
new-⋯ skip ∀ϕ-new = skip

new-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → New (s ⋯ ϕ) → New s
new-⋯⁻¹ {s = ` _} x = `-
new-⋯⁻¹ {s = msg p t} x = msg
new-⋯⁻¹ {s = brn p _ _} (brn x y) = brn (new-⋯⁻¹ x) (new-⋯⁻¹ y)
new-⋯⁻¹ {s = mu s} (mu x) = mu (new-⋯⁻¹ x)
new-⋯⁻¹ {s = _ ; _} (x ; y) = new-⋯⁻¹ x ; new-⋯⁻¹ y
new-⋯⁻¹ {s = skip} skip = skip

new-≃ : New {n} Respects _≃_
new-≃ refl = id
new-≃ (x ◅ xs) = new-≃ xs ∘ go x where
  go : New {n} Respects SymClosure _≃𝕊_
  go (fwd (≃𝕊-;₁ eq)) (x ; y) = go (fwd eq) x ; y
  go (fwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (fwd eq) y
  go (fwd ≃𝕊-skipˡ) (x ; y) = y
  go (fwd ≃𝕊-skipʳ) (x ; y) = x
  go (fwd (≃𝕊-msg x)) msg = msg
  go (fwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (fwd x) b) b₁
  go (fwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (fwd x) b₁)
  go (fwd ≃𝕊-μ) (mu x) = new-⋯ x λ{ zero → mu x; (suc z) → `- }
  go (fwd ≃𝕊-assoc) ((x ; y) ; z) = x ; (y ; z)
  go (fwd ≃𝕊-distr) (brn x₁ x₂ ; y) = brn (x₁ ; y) (x₂ ; y)
  go (bwd (≃𝕊-;₁ eq)) (x ; y) = go (bwd eq) x ; y
  go (bwd (≃𝕊-;₂ eq)) (x ; y) = x ; go (bwd eq) y
  go (bwd (≃𝕊-msg x)) msg = msg
  go (bwd (≃𝕊-brn₁ x)) (brn b b₁) = brn (go (bwd x) b) b₁
  go (bwd (≃𝕊-brn₂ x)) (brn b b₁) = brn b (go (bwd x) b₁)
  go (bwd ≃𝕊-skipˡ) x = skip ; x
  go (bwd ≃𝕊-skipʳ) x = x ; skip
  go (bwd ≃𝕊-μ) x = mu (new-⋯⁻¹ x)
  go (bwd ≃𝕊-assoc) (x ; (y ; z)) = (x ; y) ; z
  go (bwd ≃𝕊-distr) (brn (x₁ ; y) (x₂ ; _)) = brn x₁ x₂ ; y

new-dual : New s → New (dual s)
new-dual `- = `-
new-dual msg = msg
new-dual (brn x y) = brn (new-dual x) (new-dual y)
new-dual (mu x) = mu (new-dual x)
new-dual (x ; y) = new-dual x ; new-dual y
new-dual skip = skip

¬new-end : ¬ New (s ; end p)
¬new-end (x ; ())
