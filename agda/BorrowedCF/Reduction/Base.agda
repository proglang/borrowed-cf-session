module BorrowedCF.Reduction.Base where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern

import BorrowedCF.Context.Substitution as 𝐂

open Fin.Patterns

module Variables where
  open Nat.Variables public
  variable e e₁ e₂ e₃ e′ : Tm n

open Variables

-- NB. Values are predicates on _unclosed_ terms. That is because
-- channel variables are values but we don't want to keep two kinds of
-- environments around. The notion of a "Value" is only correct in a
-- context Γ where `ChanCx Γ` holds.

ChanCx : Ctx n → Set
ChanCx Γ = ∀ x → ∃ λ s → Γ x ≡ ⟨ s ⟩

chanCx-⸴* : ChanCx Γ₁ → ChanCx Γ₂ → ChanCx (Γ₁ ⸴* Γ₂)
chanCx-⸴* {m} Γ₁-S Γ₂-S i with splitAt m i
... | inj₁ i₁ = Γ₁-S i₁
... | inj₂ i₂ = Γ₂-S i₂

data Value {n} : Tm n → Set where
  V-` : ∀ {x} → Value (` x)
  V-K : ∀ {c} → Value (K c)
  V-λ : Value (ƛ e)
  V-⊗ : Value e₁ → Value e₂ → Value (e₁ ⊗ e₂)
  V-⊕ : ∀ {i} → Value e → Value (`inj i e)

vTm : {e : Tm n} → Value e → Tm n
vTm {e = e} _ = e

Value-irr : {U V : Value e} → U ≡ V
Value-irr {U = V-`} {V-`} = refl
Value-irr {U = V-K} {V-K} = refl
Value-irr {U = V-λ} {V-λ} = refl
Value-irr {U = V-⊗ U₁ U₂} {V-⊗ V₁ V₂} = cong₂ V-⊗ Value-irr Value-irr
Value-irr {U = V-⊕ U} {V-⊕ V} = cong V-⊕ Value-irr

{-
data Blocked {n} : Tm n → Set where
  `fork : Blocked (K `fork · ƛ e)
  `new : Blocked (K (`new s) · K `unit)
  `lsplit : ∀ {x} → Blocked (K `lsplit · (` x))
  `rsplit : ∀ {x} → Blocked (K `rsplit · (` x))
  `drop : ∀ {x} → Blocked (K `drop · (` x))
  `acq : ∀ {x} → Blocked (K `acq · (` x))
  `send : ∀ {x} → Value e → Blocked (K `send · (e ⊗ (` x)))
  `recv : ∀ {x} → Blocked (K `recv · (` x))
  `end : ∀ {x} → Blocked (K (`end p) · (` x))
-}

Blocked : Tm n → Set
Blocked e = ∃[ c ] ∃[ e′ ] Value e′ × e ≡ c · e′

data Frame n : Set where
  □·_ : (e₂ : Tm n) → Frame n
  _·□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □⊗_ : (e₂ : Tm n) → Frame n
  _⊗□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □;_ : (e₂ : Tm n) → Frame n
  `let-`in_ : (e′ : Tm (1 + n)) → Frame n
  `let⊗-`in_ : (e′ : Tm (2 + n)) → Frame n
  `inj□      : (i : Side) → Frame n
  `case□`of⟨_;_⟩ : (e₁ e₂ : Tm (suc n)) → Frame n

infixl 4.5 _[_]

_[_] : Frame n → Tm n → Tm n
(□· e) [ e₀ ] = e₀ · e
(V ·□) [ e₀ ] = vTm V · e₀
(□⊗ e) [ e₀ ] = e₀ ⊗ e
(V ⊗□) [ e₀ ] = vTm V ⊗ e₀
(□; e) [ e₀ ] = e₀ ; e
(`let-`in e) [ e₀ ] = `let e₀ `in e
(`let⊗-`in e) [ e₀ ] = `let⊗ e₀ `in e
`inj□ i [ e₀ ] = `inj i e₀
`case□`of⟨ e₁ ; e₂ ⟩ [ e₀ ] = `case e₀ `of⟨ e₁ ; e₂ ⟩

VSub : ⦃ K : Kit 𝓕 ⦄ → m –[ K ]→ n → Set
VSub ϕ = ∀ x → Value (`/id (ϕ x))

value-⋯ : ⦃ K : Kit 𝓕 ⦄ → Value e → (ϕ : m –[ K ]→ n) → VSub ϕ → Value (e ⋯ ϕ)
value-⋯ V-` ϕ Vϕ = Vϕ _
value-⋯ V-K ϕ Vϕ = V-K
value-⋯ V-λ ϕ Vϕ = V-λ
value-⋯ (V-⊗ V₁ V₂) ϕ Vϕ = V-⊗ (value-⋯ V₁ ϕ Vϕ) (value-⋯ V₂ ϕ Vϕ)
value-⋯ (V-⊕ V) ϕ Vϕ = V-⊕ (value-⋯ V ϕ Vϕ)

frame-⋯ : ⦃ K : Kit 𝓕 ⦄ → Frame m → (ϕ : m –[ K ]→ n) → VSub ϕ → Frame n
frame-⋯ (□· e₂) ϕ Vϕ = □· (e₂ ⋯ ϕ)
frame-⋯ (V₁ ·□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ·□
frame-⋯ (□⊗ e₂) ϕ Vϕ = □⊗ (e₂ ⋯ ϕ)
frame-⋯ (V₁ ⊗□) ϕ Vϕ = (value-⋯ V₁ ϕ Vϕ) ⊗□
frame-⋯ (□; e₂) ϕ Vϕ = □; (e₂ ⋯ ϕ)
frame-⋯ (`let-`in e′) ϕ Vϕ = `let-`in (e′ ⋯ ϕ ↑)
frame-⋯ (`let⊗-`in e′) ϕ Vϕ = `let⊗-`in (e′ ⋯ ϕ ↑ ↑)
frame-⋯ (`inj□ i) ϕ Vϕ = `inj□ i
frame-⋯ (`case□`of⟨ e₁ ; e₂ ⟩) ϕ Vϕ = `case□`of⟨ (e₁ ⋯ ϕ ↑) ; (e₂ ⋯ ϕ ↑) ⟩

infixl 5 _⋯ᵛ_ _⋯ᶠ_

_⋯ᵛ_ : Value e → (ϕ : m →ᵣ n) → Value (e ⋯ ϕ)
V ⋯ᵛ ϕ = value-⋯ V ϕ λ x → V-`

_⋯ᶠ_ : Frame m → (ϕ : m →ᵣ n) → Frame n
E ⋯ᶠ ϕ = frame-⋯ E ϕ λ x → V-`

infix 4 _;_⊢_∶_⇒_∣_⇒_

data _;_⊢_∶_⇒_∣_⇒_ (Γ : Ctx n) : CxPat n → Frame n → 𝕋 → 𝕋 → Eff → Eff → Set where
  TF-□· :
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    (appPar   : Arr.Par a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ϵ) →
    (appLeft  : Arr.IsL a → ϵ₁ ≡ ℙ × ϵ₂ ≡ ϵ) →
    (appRight : Arr.IsR a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ℙ) →
    Γ ; γ ⊢ e₂ ∶ T ∣ ϵ₂ →
    Γ ; 𝒫[ Arr.dir a , γ ] ⊢ □· e₂ ∶ T ⟨ a ⟩→ U ⇒ U ∣ ϵ₁ ⇒ ϵ

  TF-·□ : {V₁ : Value e₁} →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    (appPar   : Arr.Par a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ϵ) →
    (appLeft  : Arr.IsL a → ϵ₁ ≡ ℙ × ϵ₂ ≡ ϵ) →
    (appRight : Arr.IsR a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ℙ) →
    Γ ; γ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ₁ →
    Γ ; 𝒫[ flipDir (Arr.dir a) , γ ] ⊢ V₁ ·□ ∶ T ⇒ U ∣ ϵ₂ ⇒ ϵ

  TF-□⊗ : (p/s : ParSeq) →
    let d = biasedDir p/s in
    (seq⇒p : Seq⇒Pure p/s ϵ₁ ϵ₂) →
    Γ ; γ ⊢ e₂ ∶ U ∣ ϵ₂ →
    Γ ; 𝒫[ flipDir d , γ ] ⊢ □⊗ e₂ ∶ T ⇒ T ⊗⟨ d ⟩ U ∣ ϵ₁ ⇒ ϵ₁

  TF-⊗□ : (p/s : ParSeq) {V : Value e₁} →
    let d = biasedDir p/s in
    (seq⇒p : Seq⇒Pure p/s ϵ₁ ϵ₂) →
    Γ ; γ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; 𝒫[ d , γ ] ⊢ V ⊗□ ∶ U ⇒ T ⊗⟨ d ⟩ U ∣ ϵ₂ ⇒ ϵ₁

  TF-; :
    Unr T →
    Γ ; γ ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ R , γ ] ⊢ □; e₂ ∶ T ⇒ U ∣ ϵ ⇒ ϵ

  TF-`let : (p/s : ParSeq) →
    T ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ) ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `let-`in e₂ ∶ T ⇒ U ∣ ϵ ⇒ ϵ

  TF-`let⊗ : (p/s : ParSeq) →
    T₁ ⸴ T₂ ⸴ Γ ; join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ)) ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `let⊗-`in e₂ ∶ T₁ ⊗⟨ d ⟩ T₂ ⇒ U ∣ ϵ ⇒ ϵ

  TF-`inj□ : ∀ i →
    Γ ; [] ⊢ `inj□ i ∶ if i then T₁ else T₂ ⇒ T₁ ⊕ T₂ ∣ ϵ ⇒ ϵ

  TF-`case□ : (p/s : ParSeq) →
    let γ′ = join p/s (` 0F) (𝐂.wk γ) in
    T₁ ⸴ Γ ; γ′ ⊢ e₁ ∶ U ∣ ϵ →
    T₂ ⸴ Γ ; γ′ ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `case□`of⟨ e₁ ; e₂ ⟩ ∶ T₁ ⊕ T₂ ⇒ U ∣ ϵ ⇒ ϵ

⊢⟨_[_]⟩ : {E : Frame n} → Γ ; P ⊢ E ∶ T ⇒ U ∣ ϵ₁ ⇒ ϵ₂ → Γ ; γ ⊢ e ∶ T ∣ ϵ₁ → Γ ; P [ γ ]𝓅 ⊢ E [ e ] ∶ U ∣ ϵ₂
⊢⟨ TF-□· {a} ≤ₐ appPar appLeft appRight x [ e ]⟩
  with Arr.lin a in lin-eq
... | unr
  rewrite Arr.ω⇒𝟙 a lin-eq
  with refl , refl ← appPar refl
  = T-Weaken (≼-refl ∥-comm) $ T-AppUnr lin-eq ≤ₐ e x
... | 𝟙
  with Arr.dir a in dir-eq
... | L with refl , refl ← appLeft  refl = T-AppLeft dir-eq ≤ₐ e x
... | R with refl , refl ← appRight refl = T-AppRight dir-eq ≤ₐ e x
... | 𝟙 with refl , refl ← appPar   refl = T-Weaken (≼-refl ∥-comm) $ T-AppLin dir-eq ≤ₐ e x
⊢⟨ TF-·□ {a = a} ≤ₐ appPar appLeft appRight x [ e ]⟩
  with Arr.lin a in lin-eq
... | unr
  rewrite Arr.ω⇒𝟙 a lin-eq
  with refl , refl ← appPar refl
  = T-AppUnr lin-eq ≤ₐ x e
... | 𝟙
  with Arr.dir a in dir-eq
... | L with refl , refl ← appLeft  refl = T-AppLeft dir-eq ≤ₐ x e
... | R with refl , refl ← appRight refl = T-AppRight dir-eq ≤ₐ x e
... | 𝟙 with refl , refl ← appPar   refl = T-AppLin dir-eq ≤ₐ x e
⊢⟨ TF-□⊗ p/s seq⇒p x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Pair p/s seq⇒p e x
⊢⟨ TF-⊗□ p/s seq⇒p x [ e ]⟩ = T-Pair p/s seq⇒p x e
⊢⟨ TF-; uT x [ e ]⟩ = T-Seq uT e x
⊢⟨ TF-`let p/s x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Let p/s e x
⊢⟨ TF-`let⊗ p/s x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-LetPair p/s e x
⊢⟨ TF-`inj□ i [ e ]⟩ = T-Inj e
⊢⟨ TF-`case□ p/s x₁ x₂ [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Case p/s e x₁ x₂

Frame* : ℕ → Set
Frame* n = List (Frame n)

infixl 4.5 _[_]*

_[_]* : Frame* n → Tm n → Tm n
[] [ e ]* = e
(E ∷ E*) [ e ]* = E [ E* [ e ]* ]

infixl 5 _⋯ᶠ*_

_⋯ᶠ*_ : Frame* m → (ϕ : m →ᵣ n) → Frame* n
E* ⋯ᶠ* ϕ = L.map (_⋯ᶠ ϕ) E*

infix 4 _;_⊢*_∶_⇒_∣_⇒_

data _;_⊢*_∶_⇒_∣_⇒_ (Γ : Ctx n) : CxPat n → Frame* n → 𝕋 → 𝕋 → Eff → Eff → Set where
  [] :
    Γ ; [] ⊢* [] ∶ T ⇒ T ∣ ϵ ⇒ ϵ

  _∷_ : {E : Frame n} {E* : Frame* n} →
    Γ ; P₁ ⊢  E  ∶ T₂ ⇒ T₃ ∣ ϵ₂ ⇒ ϵ₃ →
    Γ ; P₂ ⊢* E* ∶ T₁ ⇒ T₂ ∣ ϵ₁ ⇒ ϵ₂ →
    Γ ; P₁ ++ P₂ ⊢* E ∷ E* ∶ T₁ ⇒ T₃ ∣ ϵ₁ ⇒ ϵ₃

⊢⟨_[_]*⟩ : {E* : Frame* n} → Γ ; P ⊢* E* ∶ T ⇒ U ∣ ϵ₁ ⇒ ϵ₂ → Γ ; γ ⊢ e ∶ T ∣ ϵ₁ → Γ ; P [ γ ]𝓅 ⊢ E* [ e ]* ∶ U ∣ ϵ₂
⊢⟨ [] [ e ]*⟩ = e
⊢⟨_[_]*⟩ {γ = γ} (_∷_ {P₁} {P₂ = P₂} E E*) e = subst-γ (sym ([-]𝓅-dist-++ P₁ P₂ γ)) ⊢⟨ E [ ⊢⟨ E* [ e ]*⟩ ]⟩

FullBlocked : Tm n → Set
FullBlocked {n} e = ∀ E (e′ : Tm n) → e ≡ E [ e′ ] → Blocked e′

Value⊥Blocked : Value {n} Un.⊥ Blocked
Value⊥Blocked (() , _ , _ , _ , refl)

unique-frame : (E E′ : Frame n) → ¬ Value e → ¬ Value e′ → E [ e ] ≡ E′ [ e′ ] → E ≡ E′ × e ≡ e′
unique-frame (□· e₂) (□· e₃) ¬V ¬V′ refl = refl , refl
unique-frame (□· e₂) (V₁ ·□) ¬V ¬V′ refl = ⊥-elim (¬V V₁)
unique-frame (V₁ ·□) (□· e₂) ¬V ¬V′ refl = ⊥-elim (¬V′ V₁)
unique-frame (V₁ ·□) (V₂ ·□) ¬V ¬V′ refl = cong _·□ Value-irr , refl
unique-frame (□⊗ e₂) (□⊗ e₃) ¬V ¬V′ refl = refl , refl
unique-frame (□⊗ e₂) (V₁ ⊗□) ¬V ¬V′ refl = ⊥-elim (¬V V₁)
unique-frame (V₁ ⊗□) (□⊗ e₂) ¬V ¬V′ refl = ⊥-elim (¬V′ V₁)
unique-frame (V₁ ⊗□) (V₂ ⊗□) ¬V ¬V′ refl = cong _⊗□ Value-irr , refl
unique-frame (□; e₂) (□; e₃) ¬V ¬V′ refl = refl , refl
unique-frame (`let-`in e′) (`let-`in e′₁) ¬V ¬V′ refl = refl , refl
unique-frame (`let⊗-`in e′) (`let⊗-`in e′₁) ¬V ¬V′ refl = refl , refl
unique-frame (`inj□ i) (`inj□ i) ¬V ¬V′ refl = refl , refl
unique-frame `case□`of⟨ _ ; _ ⟩ `case□`of⟨ _ ; _ ⟩ _ _ refl = refl , refl
