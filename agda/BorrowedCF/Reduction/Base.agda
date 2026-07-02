module BorrowedCF.Reduction.Base where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

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
  V-λ : Value (ƛ d e)
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

Blocked : Tm n → Set
Blocked e = ∃[ c ] ∃[ d ] ∃[ e′ ] Value e′ × e ≡ c ·⟨ d ⟩ e′

data Frame n : Set where
  app₁ : (e : Tm n) (d : Dir) → (d ≡ L         → Value e) → Frame n
  app₂ : (e : Tm n) (d : Dir) → (d ≡ 𝟙 ⊎ d ≡ R → Value e) → Frame n
  □⊗_ : (e₂ : Tm n) → Frame n
  _⊗□ : {e₁ : Tm n} (V₁ : Value e₁) → Frame n
  □;_ : (e₂ : Tm n) → Frame n
  `let-`in_ : (e′ : Tm (1 + n)) → Frame n
  `let⊗-`in_ : (e′ : Tm (2 + n)) → Frame n
  `inj□      : (i : Side) → Frame n
  `case□`of⟨_;_⟩ : (e₁ e₂ : Tm (suc n)) → Frame n

infixl 4.5 _[_]

_[_] : Frame n → Tm n → Tm n
app₁ e d V? [ e₀ ] = e₀ ·⟨ d ⟩ e
app₂ e d V? [ e₀ ] = e ·⟨ d ⟩ e₀
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
frame-⋯ (app₁ e d V?) ϕ Vϕ = app₁ (e ⋯ ϕ) d λ x → value-⋯ (V? x) ϕ Vϕ
frame-⋯ (app₂ e d V?) ϕ Vϕ = app₂ (e ⋯ ϕ) d λ x → value-⋯ (V? x) ϕ Vϕ
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

infix 4 _;_⊢_∶_∣_⟶_∣_

data _;_⊢_∶_∣_⟶_∣_ (Γ : Ctx n) : CxPat n → Frame n → 𝕋 → Eff → 𝕋 → Eff → Set where
  TF-app₁ : ∀ {V?} →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    (appPar   : Arr.Par a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ϵ) →
    (appLeft  : Arr.IsL a → ϵ₁ ≡ ℙ × ϵ₂ ≡ ϵ) →
    (appRight : Arr.IsR a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ℙ) →
    Γ ; γ ⊢ e₂ ∶ T ∣ ϵ₂ →
    Γ ; 𝒫[ Arr.dir a , γ ] ⊢ app₁ e₂ (Arr.dir a) V? ∶ T ⟨ a ⟩→ U ∣ ϵ₁ ⟶ U ∣ ϵ

  TF-app₂ : ∀ {V?} →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    (appPar   : Arr.Par a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ϵ) →
    (appLeft  : Arr.IsL a → ϵ₁ ≡ ℙ × ϵ₂ ≡ ϵ) →
    (appRight : Arr.IsR a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ℙ) →
    Γ ; γ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ₁ →
    Γ ; 𝒫[ flipDir (Arr.dir a) , γ ] ⊢ app₂ e₁ (Arr.dir a) V? ∶ T ∣ ϵ₂ ⟶ U ∣ ϵ

  TF-□⊗ : (p/s : ParSeq) →
    let d = biasedDir p/s in
    (seq⇒p : Seq⇒Pure p/s ϵ₁ ϵ₂) →
    Γ ; γ ⊢ e₂ ∶ U ∣ ϵ₂ →
    Γ ; 𝒫[ flipDir d , γ ] ⊢ □⊗ e₂ ∶ T ∣ ϵ₁ ⟶ T ⊗⟨ d ⟩ U ∣ ϵ₁

  TF-⊗□ : (p/s : ParSeq) {V : Value e₁} →
    let d = biasedDir p/s in
    (seq⇒p : Seq⇒Pure p/s ϵ₁ ϵ₂) →
    Γ ; γ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; 𝒫[ d , γ ] ⊢ V ⊗□ ∶ U ∣ ϵ₂ ⟶ T ⊗⟨ d ⟩ U ∣ ϵ₁

  TF-; :
    Unr T →
    Γ ; γ ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ R , γ ] ⊢ □; e₂ ∶ T ∣ ϵ ⟶ U ∣ ϵ

  TF-`let : (p/s : ParSeq) →
    T ⸴ Γ ; join p/s (` 0F) (𝐂.wk γ) ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `let-`in e₂ ∶ T ∣ ϵ ⟶ U ∣ ϵ

  TF-`let⊗ : (p/s : ParSeq) →
    T₁ ⸴ T₂ ⸴ Γ ; join p/s (join d (` 0F) (` 1F)) (𝐂.wk (𝐂.wk γ)) ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `let⊗-`in e₂ ∶ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ ⟶ U ∣ ϵ

  TF-`inj□ : ∀ i →
    Γ ; [] ⊢ `inj□ i ∶ if i then T₁ else T₂ ∣ ϵ ⟶ T₁ ⊕ T₂ ∣ ϵ

  TF-`case□ : (p/s : ParSeq) →
    let γ′ = join p/s (` 0F) (𝐂.wk γ) in
    T₁ ⸴ Γ ; γ′ ⊢ e₁ ∶ U ∣ ϵ →
    T₂ ⸴ Γ ; γ′ ⊢ e₂ ∶ U ∣ ϵ →
    Γ ; 𝒫[ flipDir (biasedDir p/s) , γ ] ⊢ `case□`of⟨ e₁ ; e₂ ⟩ ∶ T₁ ⊕ T₂ ∣ ϵ ⟶ U ∣ ϵ

⊢⟨_[_]⟩ : {E : Frame n} → Γ ; 𝒫 ⊢ E ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → Γ ; γ ⊢ e ∶ T ∣ ϵ₁ → Γ ; 𝒫 [ γ ]𝓅 ⊢ E [ e ] ∶ U ∣ ϵ₂
⊢⟨ TF-app₁ {a} ≤ₐ appPar appLeft appRight x [ e ]⟩
  with Arr.lin a in lin-eq
... | unr
  rewrite Arr.ω⇒𝟙 a lin-eq
  with refl , refl ← appPar refl
  = T-Weaken (≼-refl ∥-comm) $ T-AppUnr lin-eq ≤ₐ e x
... | 𝟙
  with Arr.dir a in dir-eq
... | L with refl , refl ← appLeft  refl = T-AppLeft dir-eq ≤ₐ e x
... | R with refl , refl ← appRight refl = T-AppRight dir-eq ≤ₐ e x
... | 𝟙 with refl , refl ← appPar   refl = T-Weaken (≼-refl ∥-comm) $ T-AppLin (lin-eq , dir-eq) ≤ₐ e x
⊢⟨ TF-app₂ {a = a} ≤ₐ appPar appLeft appRight x [ e ]⟩
  with Arr.lin a in lin-eq
... | unr
  rewrite Arr.ω⇒𝟙 a lin-eq
  with refl , refl ← appPar refl
  = T-AppUnr lin-eq ≤ₐ x e
... | 𝟙
  with Arr.dir a in dir-eq
... | L with refl , refl ← appLeft  refl = T-AppLeft dir-eq ≤ₐ x e
... | R with refl , refl ← appRight refl = T-AppRight dir-eq ≤ₐ x e
... | 𝟙 with refl , refl ← appPar   refl = T-AppLin (lin-eq , dir-eq) ≤ₐ x e
⊢⟨ TF-□⊗ p/s seq⇒p x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Pair p/s seq⇒p e x
⊢⟨ TF-⊗□ p/s seq⇒p x [ e ]⟩ = T-Pair p/s seq⇒p x e
⊢⟨ TF-; uT x [ e ]⟩ = T-Seq uT e x
⊢⟨ TF-`let p/s x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Let p/s e x
⊢⟨ TF-`let⊗ p/s x [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-LetPair p/s e x
⊢⟨ TF-`inj□ i [ e ]⟩ = T-Inj e
⊢⟨ TF-`case□ p/s x₁ x₂ [ e ]⟩ = T-Weaken (≼-refl (≈-sym (join-flip (biasedDir p/s)))) $ T-Case p/s e x₁ x₂

_⊢⋯ᶠ_ : {E : Frame m} {P : CxPat m} → Γ₁ ; P ⊢ E ∶ T ∣ ϵ ⟶ U ∣ ϵ′ → ∀ {ϕ : m →ᵣ n} {σ} → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  Γ₂ ; P ⋯𝓅 σ ⊢ E ⋯ᶠ ϕ ∶ T ∣ ϵ ⟶ U ∣ ϵ′
TF-app₁ ≤ₐ appPar appLeft appRight x ⊢⋯ᶠ ⊢ϕ = TF-app₁ ≤ₐ appPar appLeft appRight (x ⊢⋯ ⊢ϕ)
TF-app₂ ≤ₐ appPar appLeft appRight x ⊢⋯ᶠ ⊢ϕ = TF-app₂ ≤ₐ appPar appLeft appRight (x ⊢⋯ ⊢ϕ)
TF-□⊗ p/s seq⇒p x ⊢⋯ᶠ ⊢ϕ = TF-□⊗ p/s seq⇒p (x ⊢⋯ ⊢ϕ)
TF-⊗□ p/s seq⇒p x ⊢⋯ᶠ ⊢ϕ = TF-⊗□ p/s seq⇒p (x ⊢⋯ ⊢ϕ)
TF-; x x₁ ⊢⋯ᶠ ⊢ϕ = TF-; x (x₁ ⊢⋯ ⊢ϕ)
_⊢⋯ᶠ_ (TF-`let {γ = γ} p/s x) {σ = σ} ⊢ϕ =
  let eq = join-⋯ p/s (` 0F) (𝐂.wk γ) ■ cong (join p/s (` 0F)) (sym (𝐂.⋯-↑-wk γ σ)) in
  TF-`let p/s $ subst-γ eq $ x ⊢⋯ ⊢↑ ⊢ϕ
_⊢⋯ᶠ_ (TF-`let⊗ {d = d} {γ = γ} p/s x) {σ = σ} ⊢ϕ =
  let eq = join-⋯ p/s (join d (` 0F) (` 1F)) _
             ■ cong₂ (join p/s) (join-⋯ d _ _)
                     (sym (cong 𝐂.wk (𝐂.⋯-↑-wk γ σ) ■ 𝐂.⋯-↑-wk (𝐂.wk γ) (σ 𝐂.↑)))
  in
  TF-`let⊗ p/s $ subst-γ eq $ x ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)
TF-`inj□ i ⊢⋯ᶠ ⊢ϕ = TF-`inj□ i
_⊢⋯ᶠ_ (TF-`case□ {γ} p/s x₁ x₂) {σ = σ} ⊢ϕ =
  let eq = join-⋯ p/s _ _ ■ cong (join p/s _) (sym (𝐂.⋯-↑-wk γ σ)) in
  TF-`case□ p/s
    (subst-γ eq $ x₁ ⊢⋯ ⊢↑ ⊢ϕ)
    (subst-γ eq $ x₂ ⊢⋯ ⊢↑ ⊢ϕ)

Frame* : ℕ → Set
Frame* n = List (Frame n)

infixl 4.5 _[_]*

_[_]* : Frame* n → Tm n → Tm n
[] [ e ]* = e
(E ∷ E*) [ e ]* = E [ E* [ e ]* ]

infixl 5 _⋯ᶠ*_

_⋯ᶠ*_ : Frame* m → (ϕ : m →ᵣ n) → Frame* n
E* ⋯ᶠ* ϕ = L.map (_⋯ᶠ ϕ) E*

infix 4 _;_⊢*_∶_∣_⟶_∣_

data _;_⊢*_∶_∣_⟶_∣_ (Γ : Ctx n) : CxPat n → Frame* n → 𝕋 → Eff → 𝕋 → Eff → Set where
  [] :
    Γ ; [] ⊢* [] ∶ T ∣ ϵ ⟶ T ∣ ϵ

  _∷⟨_⟩_ : {E : Frame n} {E* : Frame* n} →
    Γ ; 𝒫₁ ⊢  E  ∶ U′ ∣ ϵ′ ⟶ T₂ ∣ ϵ₂ →
    U ≃ U′ × (ϵ ≤ϵ ϵ′) →
    Γ ; 𝒫₂ ⊢* E* ∶ T₁ ∣ ϵ₁ ⟶ U ∣ ϵ →
    Γ ; 𝒫₁ ++ 𝒫₂ ⊢* E ∷ E* ∶ T₁ ∣ ϵ₁ ⟶ T₂ ∣ ϵ₂

⊢⟨_[_]*⟩ : {E* : Frame* n} → Γ ; 𝒫 ⊢* E* ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → Γ ; γ ⊢ e ∶ T ∣ ϵ₁ → Γ ; 𝒫 [ γ ]𝓅 ⊢ E* [ e ]* ∶ U ∣ ϵ₂
⊢⟨ [] [ e ]*⟩ = e
⊢⟨_[_]*⟩ {γ = γ} (_∷⟨_⟩_ {𝒫₁} {𝒫₂ = 𝒫₂} E (eq , ϵ≤) E*) e = subst-γ (sym ([-]𝓅-dist-++ 𝒫₁ 𝒫₂ γ)) ⊢⟨ E [ T-Conv eq ϵ≤ ⊢⟨ E* [ e ]*⟩ ]⟩

_⊢⋯ᶠ*_ : {E : Frame* m} {P : CxPat m} → Γ₁ ; P ⊢* E ∶ T ∣ ϵ ⟶ U ∣ ϵ′ → ∀ {ϕ : m →ᵣ n} {σ} → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
  Γ₂ ; P ⋯𝓅 σ ⊢* E ⋯ᶠ* ϕ ∶ T ∣ ϵ ⟶ U ∣ ϵ′
[] ⊢⋯ᶠ* ⊢ϕ = []
_⊢⋯ᶠ*_ {Γ₂ = Γ₂} (_∷⟨_⟩_ {𝒫₁} {𝒫₂ = 𝒫₂} E x E*) ⊢ϕ =
  subst (Γ₂ ;_⊢* _ ∶ _ ∣ _ ⟶ _ ∣ _) (sym (⋯𝓅-dist-++ 𝒫₁ 𝒫₂ _)) $ (E ⊢⋯ᶠ ⊢ϕ) ∷⟨ x ⟩ (E* ⊢⋯ᶠ* ⊢ϕ)

FullBlocked : Tm n → Set
FullBlocked {n} e = ∀ E (e′ : Tm n) → e ≡ E [ e′ ] → Blocked e′

Value⊥Blocked : Value {n} Un.⊥ Blocked
Value⊥Blocked (() , _ , _ , _ , _ , refl)

{-
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
-}

⊢[]⁻¹ : (E : Frame n) (e : Tm n) → Γ ; γ ⊢ E [ e ] ∶ T ∣ ϵ → ∃[ P ] ∃[ γ′ ] ∃[ T′ ] ∃[ U ] ∃[ ϵₚ ] ∃[ ϵₑ ]
  Γ ∶ P [ γ′ ]𝓅 ≼ γ × T′ ≃ T × ϵₚ ≤ϵ ϵ × Γ ; P ⊢ E ∶ U ∣ ϵₑ ⟶ T′ ∣ ϵₚ × Γ ; γ′ ⊢ e ∶ U ∣ ϵₑ
⊢[]⁻¹ (app₁ e₂ d V?) e x with inv-· x
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppUnr a-unr x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₁ ≤ₐ (λ z → refl , refl)
                 (λ z → case sym z ■ Arr.ω⇒𝟙 a a-unr of λ())
                 (λ z → case sym z ■ Arr.ω⇒𝟙 a a-unr of λ())
                 x₂
    , x₁
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppLin a-par x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₁ ≤ₐ (λ z → refl , refl)
                 (λ z → case sym z ■ a-par .proj₂ of λ())
                 (λ z → case sym z ■ a-par .proj₂ of λ())
                 x₂
    , x₁
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppLeft aL x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₁ ≤ₐ (λ z → case sym z ■ aL of λ())
                 (λ z → refl , refl)
                 (λ z → case sym z ■ aL of λ())
                 x₂
    , x₁
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppRight aR x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₁ ≤ₐ (λ z → case sym z ■ aR of λ())
                 (λ z → case sym z ■ aR of λ())
                 (λ z → refl , refl)
                 x₂
    , x₁
⊢[]⁻¹ (app₂ e₁ d V?) e x with inv-· x
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppUnr a-unr x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (Arr.dir a))) ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₂ ≤ₐ (λ z → refl , refl)
                 (λ z → case sym z ■ Arr.ω⇒𝟙 a a-unr of λ())
                 (λ z → case sym z ■ Arr.ω⇒𝟙 a a-unr of λ())
                 x₁
    , x₂
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppLin a-par x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (Arr.dir a))) ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₂ ≤ₐ (λ z → refl , refl)
                 (λ z → case sym z ■ a-par .proj₂ of λ())
                 (λ z → case sym z ■ a-par .proj₂ of λ())
                 x₁
    , x₂
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppLeft aL x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (Arr.dir a))) ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₂ ≤ₐ (λ z → case sym z ■ aL of λ())
                 (λ z → refl , refl)
                 (λ z → case sym z ■ aL of λ())
                 x₁
    , x₂
... | a , _ , _ , _ , ≤γ , refl , ≤ₐ , T-AppRight aR x₁ x₂ =
  _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (Arr.dir a))) ≤γ , ≃-refl , ≤ϵ-refl
    , TF-app₂ ≤ₐ (λ z → case sym z ■ aR of λ())
                 (λ z → case sym z ■ aR of λ())
                 (λ z → refl , refl)
                 x₁
    , x₂
⊢[]⁻¹ (□⊗ e₂) e x
  using p/s , _ , _ , _ , _ , _ , _ , ≤γ , T≃ , ϵ≤ , seq⇒p , x₁ , x₂ ← inv-⊗ x
  = _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (biasedDir p/s))) ≤γ , T≃ , ϵ≤ , TF-□⊗ p/s seq⇒p x₂ , x₁
⊢[]⁻¹ (V₁ ⊗□) e x
  using p/s , _ , _ , _ , _ , _ , _ , ≤γ , T≃ , ϵ≤ , seq⇒p , x₁ , x₂ ← inv-⊗ x
  = _ , _ , _ , _ , _ , _ , ≤γ , T≃ , ϵ≤ , TF-⊗□ p/s seq⇒p x₁ , x₂
⊢[]⁻¹ (□; e₂) e x
  using _ , _ , _ , uT , ≤γ , x₁ , x₂ ← inv-; x
  = _ , _ , _ , _ , _ , _ , ≤γ , ≃-refl , ≤ϵ-refl , TF-; uT x₂ , x₁
⊢[]⁻¹ (`let-`in e′) e x
  using p/s , _ , _ , _ , ≤γ , x₁ , x₂ ← inv-`let x
  = _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (biasedDir p/s))) ≤γ , ≃-refl , ≤ϵ-refl , TF-`let p/s x₂ , x₁
⊢[]⁻¹ (`let⊗-`in e′) e x
  using p/s , _ , _ , _ , _ , _ , ≤γ , x₁ , x₂ ← inv-`let⊗ x
  = _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (biasedDir p/s))) ≤γ , ≃-refl , ≤ϵ-refl , TF-`let⊗ p/s x₂ , x₁
⊢[]⁻¹ (`inj□ i) e x
  using _ , _ , eq , x′ ← inv-inj x
  = [] , _ , _ , _ , _ , _ , ≼-refl refl , eq , ≤ϵ-refl , TF-`inj□ i , x′
⊢[]⁻¹ `case□`of⟨ e₁ ; e₂ ⟩ e x
  using p/s , _ , _ , _ , _ , ≤γ , x , x₁ , x₂ ← inv-`case x
  = _ , _ , _ , _ , _ , _ , ≼-trans (≼-refl (join-flip (biasedDir p/s))) ≤γ , ≃-refl , ≤ϵ-refl , TF-`case□ p/s x₁ x₂ , x

⊢[]*⁻¹ : (E : Frame* n) (e : Tm n) →
  Γ ; γ ⊢ E [ e ]* ∶ T ∣ ϵ →
  ∃[ 𝒫 ] ∃[ γ′ ] ∃[ T′ ] ∃[ U ] ∃[ ϵₚ ] ∃[ ϵₑ ]
    Γ ∶ 𝒫 [ γ′ ]𝓅 ≼ γ
      × T′ ≃ T
      × ϵₚ ≤ϵ ϵ
      × Γ ; 𝒫 ⊢* E ∶ U ∣ ϵₑ ⟶ T′ ∣ ϵₚ
      × Γ ; γ′ ⊢ e ∶ U ∣ ϵₑ
⊢[]*⁻¹ [] e x = [] , _ , _ , _ , _ , _ , ≼-refl refl , ≃-refl , ≤ϵ-refl , [] , x
⊢[]*⁻¹ {Γ = Γ} {γ = γ} (E ∷ E*) e x
  using 𝒫₁ , _ , _ , _ , _ , _ , ≤γ₁ , T-eq₁ , ϵ≤₁ , ⊢E , ⊢E*e ← ⊢[]⁻¹ E (E* [ e ]*) x
  using 𝒫₂ , γ′ , _ , _ , _ , _ , ≤γ₂ , T-eq₂ , ϵ≤₂ , ⊢E* , ⊢e ← ⊢[]*⁻¹ E* e ⊢E*e
  = _ , _ , _ , _ , _ , _
      , subst (Γ ∶_≼ γ) (sym ([-]𝓅-dist-++ 𝒫₁ 𝒫₂ γ′)) (≼-trans ([-]𝓅-≼ 𝒫₁ ≤γ₂) ≤γ₁)
      , T-eq₁ , ϵ≤₁ , ⊢E ∷⟨ T-eq₂ , ϵ≤₂ ⟩ ⊢E* , ⊢e
