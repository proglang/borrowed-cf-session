{-# OPTIONS --allow-unsolved-metas #-}

module BorrowedCF.Terms where

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Vec.Functional as F using (Vector)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_; kleisliStar) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)
open import BorrowedCF.Context renaming (module Substitution to 𝐂)

import BorrowedCF.FinKits as Kits

open Nat.Variables

data Const : Set where
  `unit `fork `send `recv `drop `acq `end : Const
  `new : 𝕊 0 → Const
  `lsplit `rsplit : (s₁ s₂ : 𝕊 0) → Const

data Tm (n : ℕ) : Set where
  `_ : 𝔽 n → Tm n
  K : (c : Const) → Tm n
  λ[_] : (d : Dir) (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _,⟨_⟩_ : (e₁ : Tm n) (d : Dir) (e₂ : Tm n) → Tm n
  `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  `let⊗_`in_ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n

open module Syntax = Kits.Syntax record
  { Tm = Tm
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Tm; `_; Traversal)
  renaming (id to idₖ)
  public

infixl 5 _⋯_

_⋯_ : ⦃ K : Kit 𝓕 ⦄ → Tm m → m –[ K ]→ n → Tm n
(` x) ⋯ ϕ = `/id (ϕ x)
K c ⋯ ϕ = K c
λ[ d ] e ⋯ ϕ = λ[ d ] (e ⋯ ϕ ↑)
(e · e₁) ⋯ ϕ = (e ⋯ ϕ) · (e₁ ⋯ ϕ)
(e ; e₁) ⋯ ϕ =  (e ⋯ ϕ) ; (e₁ ⋯ ϕ)
(e ,⟨ d ⟩ e₁) ⋯ ϕ =  (e ⋯ ϕ) ,⟨ d ⟩ (e₁ ⋯ ϕ)
(`let e `in e₁) ⋯ ϕ = `let (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑)
(`let⊗ e `in e₁) ⋯ ϕ = `let⊗ (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑ ↑)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (e : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → e ⋯ ϕ ≡ e
⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
⋯-id (K c) eq = refl
⋯-id (λ[ d ] e) eq = cong λ[ d ] (⋯-id e (id↑ eq))
⋯-id (e · e₁) eq = cong₂ _·_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ; e₁) eq = cong₂ _;_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ,⟨ d ⟩ e₁) eq = cong₂ (_,⟨ d ⟩_) (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-id e eq) (⋯-id e₁ (id↑ eq))
⋯-id (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-id e eq) (⋯-id e₁ (id↑* 2 eq))

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (e : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → e ⋯ ϕ₁ ≡ e ⋯ ϕ₂
⋯-cong (` x) eq = cong `/id (eq x)
⋯-cong (K c) eq = refl
⋯-cong (λ[ d ] e) eq = cong λ[ d ] (⋯-cong e (eq ~↑))
⋯-cong (e · e₁) eq = cong₂ _·_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ; e₁) eq = cong₂ _;_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ,⟨ d ⟩ e₁) eq = cong₂ (_,⟨ d ⟩_) (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑))
⋯-cong (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑* 2))

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-id; ⋯-cong; CTraversal)

fusion :
  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
  (x : Tm n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) → x ⋯ ϕ₁ ⋯ ϕ₂ ≡ x ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion (x₁ ; x₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x₁ ϕ₁ ϕ₂) (fusion x₂ ϕ₁ ϕ₂)
fusion (K c) ϕ₁ ϕ₂ = refl
fusion (λ[ d ] e) ϕ₁ ϕ₂ = cong λ[ d ] $
  fusion e (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (e₁ · e₂) ϕ₁ ϕ₂ = cong₂ _·_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (e₁ ,⟨ d ⟩ e₂) ϕ₁ ϕ₂ = cong₂ (_,⟨ d ⟩_) (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (`let e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e₂ (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (`let⊗ e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑* 2) (ϕ₂ ↑* 2) ■ ⋯-cong e₂ (sym ∘ dist-↑*-· 2 ϕ₁ ϕ₂)

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

{-
infixl 5 _⋯𝓢_

_⋯𝓢_ : Struct m → m →ᵣ n → Struct n
` x ⋯𝓢 ρ = ` ρ x
[] ⋯𝓢 ρ = []
x ∥ y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ∥ (y ⋯𝓢 ρ)
x ; y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ; (y ⋯𝓢 ρ)
-}

infix 4 ⊢_∶_

private
  _→m,1_∣_ : 𝕋 → 𝕋 → Eff → 𝕋
  t →m,1 u ∣ ϵ = arr mob 𝟙 ϵ t u

data ⊢_∶_ : Const → 𝕋 → Set where
  `unit : ⊢ `unit ∶ unit
  `new : ∀ {s} → ⊢ `new s ∶ arr mob 𝟙 ϵ unit (pair 𝟙 ⟨ acq ; s ⟩ ⟨ acq ; dual s ⟩)
  `lsplit : ∀ {s₁ s₂} → ⊢ `lsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair L ⟨ s₁ ⟩ ⟨ s₂ ⟩)
  `rsplit : ∀ {s₁ s₂} → ⊢ `rsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair 𝟙 ⟨ s₁ ; ret ⟩ ⟨ acq ; s₂ ⟩)
  `drop : ⊢ `drop ∶ arr mob 𝟙 ϵ ⟨ ret ⟩ unit
  `acq : ∀ {s} → ⊢ `acq ∶ ⟨ acq ; s ⟩ →m,1 ⟨ s ⟩ ∣ ϵ
  `fork : ⊢ `fork ∶ (unit →m,1 unit ∣ 𝕀) →m,1 unit ∣ ϵ
  `send : ∀ {t} → Mobile t → ⊢ `send ∶ pair 𝟙 t ⟨ msg ‼ t ⟩ →m,1 unit ∣ 𝕀
  `recv : ∀ {t} → Mobile t → ⊢ `recv ∶ ⟨ msg ⁇ t ⟩ →m,1 t ∣ 𝕀
  `end : ⊢ `end ∶ ⟨ end p ⟩ →m,1 unit ∣ 𝕀


private variable
  e e₁ e₂ : Tm n

infix 4 _;_⊢_∶_∣_

data _;_⊢_∶_∣_ (Γ : Ctx n) (γ : Struct n) : Tm n → 𝕋 → Eff → Set where
  T-Const : ∀ {c} →
    (γ-eq : γ ≈ []) →
    ⊢ c ∶ T →
    -------------------
    Γ ; γ ⊢ K c ∶ T ∣ ℙ

  T-Var : ∀ x →
    (γ-eq : γ ≈ ` x) →
    (T-eq : Γ x ≡ T) →
    -------------------
    Γ ; γ ⊢ ` x ∶ T ∣ ℙ

  T-Abs :
    (𝓂→C : 𝓂 ≡ mob → MobCx Γ γ) →
    T F.∷ Γ ; join d (` zero) (𝐂.wk γ) ⊢ e ∶ U ∣ ϵ →
    ------------------------------------------------
    Γ ; γ ⊢ λ[ d ] e ∶ arr 𝓂 d ϵ T U ∣ ℙ

  T-App :
    (γ-eq : Split d γ γ₁ γ₂)        →
    Γ ; γ₁ ⊢ e₁ ∶ arr 𝓂 d ϵ T U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T             ∣ ϵ →
    ---------------------------------
    Γ ; γ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-Pair : (p/s : ParSeq) →
    (γ-eq : γ ≈ join p/s γ₁ γ₂) →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    SeqIsPure p/s ϵ₁ ϵ₂ →
    ------------------------------------------------------------
    Γ ; γ ⊢ e₁ ,⟨ pairDir p/s ⟩ e₂ ∶ pair (pairDir p/s) T U ∣ ϵ₁

  T-Let : (p/s : ParSeq) →
    (γ-eq : Split p/s γ γ₁ γ₂) →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ →
    T F.∷ Γ ; join p/s (` zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ →
    ----------------------------------------------------
    Γ ; γ ⊢ `let e₁ `in e₂ ∶ U ∣ ϵ

  T-LetUnit : (p/s : ParSeq) →
    (γ-eq : Split p/s γ γ₁ γ₂) →
    Γ ; γ₁ ⊢ e₁ ∶ unit ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T    ∣ ϵ →
    ------------------------
    Γ ; γ ⊢ e₁ ; e₂ ∶ T ∣ ϵ

  T-LetPair : (p/s : ParSeq) →
    (γ-eq : Split p/s γ γ₁ γ₂) →
    Γ ; γ₁ ⊢ e₁ ∶ pair d T₁ T₂ ∣ ϵ →
    T₁ F.∷ T₂ F.∷ Γ ;
      join p/s (join d (` zero) (` suc zero))
               (𝐂.wk (𝐂.wk γ₂))
      ⊢ e₂ ∶ U ∣ ϵ →
    -----------------------------------------
    Γ ; γ ⊢ `let⊗ e₁ `in e₂ ∶ U ∣ ϵ

  T-Weak :
    (ϵ≤ : ϵ′ ≤ϵ ϵ) →
    (γ≤ : γ′ ≼ γ) →
    Γ ; γ′ ⊢ e ∶ T ∣ ϵ′ →
    ---------------------
    Γ ; γ ⊢ e ∶ T ∣ ϵ


record TKit (K : Kit 𝓕) : Set₁ where
  private instance _ = K

  field
    𝓕[_;_⊢_∶_] : Ctx n → Struct n → 𝓕 n → 𝕋 → Set
    ⊢id/` : {x : 𝔽 n} → γ ≈ ` x → 𝓕[ Γ ; γ ⊢ id/` x ∶ Γ x ]
    ⊢`/id : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → Γ ; γ ⊢ `/id x/t ∶ T ∣ ℙ
    ⊢wk : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ U ] → 𝓕[ T F.∷ Γ ; 𝐂.wk γ ⊢ wk x/t ∶ U ]

  infix 4 _∶_⊢_⇒_

  _∶_⊢_⇒_ : m –[ K ]→ n → m 𝐂.→ₛ n → Ctx m → Ctx n → Set
  ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ = ∀ x → 𝓕[ Γ₂ ; σ x ⊢ ϕ x ∶ Γ₁ x ]

  ⊢id : {Γ : Ctx n} → idₖ ∶ 𝐂.idₛ ⊢ Γ ⇒ Γ
  ⊢id x = ⊢id/` refl

  ⊢↑ : ∀ {ϕ : m –[ K ]→ n} {σ} → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ↑ ∶ σ 𝐂.↑ ⊢ T F.∷ Γ₁ ⇒ T F.∷ Γ₂
  ⊢↑ ⊢ϕ zero = ⊢id/` refl
  ⊢↑ ⊢ϕ (suc x) = ⊢wk (⊢ϕ x)

  ⊢⦅_⦆ : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → ⦅ x/t ⦆ ∶ 𝐂.⦅ γ ⦆ ⊢ T F.∷ Γ ⇒ Γ
  ⊢⦅ ⊢x/t ⦆ zero    = ⊢x/t
  ⊢⦅ ⊢x/t ⦆ (suc y) = ⊢id/` refl

  ⊢weaken : (Γ : Ctx n) → weaken ∶ 𝐂.weaken ⊢ Γ ⇒ T F.∷ Γ
  ⊢weaken Γ x = ⊢wk (⊢id/` refl)

infix 4 _∶_⊢[_]_⇒_

_∶_⊢[_]_⇒_ : ∀ {K : Kit 𝓕} → m –[ K ]→ n → m 𝐂.→ₛ n → TKit K → Ctx m → Ctx n → Set
ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ = ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ where open TKit TK

open TKit ⦃ ... ⦄ public

infixl 5 _⊢≈_ _⊢⋯_

_⊢≈_ : Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → γ₁ ≈ γ₂ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
T-Const γ-eq x ⊢≈ eq = T-Const (≈-trans (≈-sym eq) γ-eq) x
T-Var x γ-eq T-eq ⊢≈ eq = T-Var x (≈-trans (≈-sym eq) γ-eq) T-eq
T-Abs {d = d} 𝓂→C x ⊢≈ eq = T-Abs (mobCx-≈ eq ∘ 𝓂→C) (x ⊢≈ cong-join d refl (cong-wk eq))
T-App γ-eq x x₁ ⊢≈ eq = T-App (≈-trans (≈-sym eq) γ-eq) x x₁
T-Pair p/s γ-eq x x₁ x₂ ⊢≈ eq = T-Pair p/s (≈-trans (≈-sym eq) γ-eq) x x₁ x₂
T-Let p/s γ-eq x x₁ ⊢≈ eq = T-Let p/s (≈-trans (≈-sym eq) γ-eq) x x₁
T-LetUnit p/s γ-eq x x₁ ⊢≈ eq = T-LetUnit p/s (≈-trans (≈-sym eq) γ-eq) x x₁
T-LetPair p/s γ-eq x x₁ ⊢≈ eq = T-LetPair p/s (≈-trans (≈-sym eq) γ-eq) x x₁
T-Weak ϵ≤ γ≤ x ⊢≈ eq = T-Weak ϵ≤ (≼-trans γ≤ (refl eq)) x

mobCx-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
  {ϕ : m –[ K ]→ n} {σ : _} →
  MobCx Γ₁ γ → ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ → MobCx Γ₂ (γ 𝐂.⋯ σ)
mobCx-⋯ [] ⊢ϕ = []
mobCx-⋯ (C₁ ∥ C₂) ⊢ϕ = mobCx-⋯ C₁ ⊢ϕ ∥ mobCx-⋯ C₂ ⊢ϕ
mobCx-⋯ (C₁ ; C₂) ⊢ϕ = mobCx-⋯ C₁ ⊢ϕ ; mobCx-⋯ C₂ ⊢ϕ
mobCx-⋯ (` x) ⊢ϕ = {!MobCx.` ?!}

subst-γ : Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → γ₁ ≡ γ₂ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
subst-γ x refl = x

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ →
       {ϕ : m –[ K ]→ n} {σ : _} →
       Γ₁ ; γ ⊢ e ∶ T ∣ ϵ →
       ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ →
       Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
T-Const γ-eq x ⊢⋯ ⊢ϕ = T-Const (⋯-preserves-≈ γ-eq) x
_⊢⋯_ {γ = γ} {σ = σ} (T-Var x γ-eq T-eq) ⊢ϕ =
  let open ≈-Reasoning in
  ⊢`/id (subst 𝓕[ _ ; _ ⊢ _ ∶_] T-eq (⊢ϕ x)) ⊢≈ (begin
    σ x        ≡⟨⟩
    ` x 𝐂.⋯ σ  ≈⟨ ⋯-preserves-≈ γ-eq ⟨
    γ 𝐂.⋯ σ    ∎)
_⊢⋯_ {γ = γ} (T-Abs {d = d} 𝓂→C x) ⊢ϕ =
  let open Fin.Patterns in
  T-Abs {!{!mobCx-≈!} ∘ 𝓂→C!} $ subst-γ (x ⊢⋯ ⊢↑ ⊢ϕ) $
    join-⋯ d (` 0F) _
      ■ cong (join d (` 0F)) (sym (𝐂.⋯-↑-wk γ _))
T-App {d = d} {γ₁} {γ₂} γ-eq e₁ e₂ ⊢⋯ ⊢ϕ =
  let open ≈-Reasoning in
  let eq = begin _ ≈⟨ ⋯-preserves-≈ γ-eq ⟩
                 _ ≡⟨ join-⋯ d γ₁ γ₂ ⟩
                 _ ∎
  in
  T-App eq (e₁ ⊢⋯ ⊢ϕ) (e₂ ⊢⋯ ⊢ϕ)
T-Pair {γ₁ = γ₁} {γ₂} p/s γ-eq x₁ x₂ seq→ℙ ⊢⋯ ⊢ϕ =
  let open ≈-Reasoning in
  let eq = begin _ ≈⟨ ⋯-preserves-≈ γ-eq ⟩
                 _ ≡⟨ join-⋯ p/s γ₁ γ₂ ⟩
                 _ ∎
  in
  T-Pair p/s eq (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ) seq→ℙ
T-Let {γ₁ = γ₁} {γ₂} p/s γ-eq x₁ x₂ ⊢⋯ ⊢ϕ =
  let open Fin.Patterns in
  let open ≈-Reasoning in
  let eq = begin _ ≈⟨ ⋯-preserves-≈ γ-eq ⟩
                 _ ≡⟨ join-⋯ p/s γ₁ γ₂ ⟩
                 _ ∎
  in
  T-Let p/s eq (x₁ ⊢⋯ ⊢ϕ) $ subst-γ (x₂ ⊢⋯ ⊢↑ ⊢ϕ) $
    join-⋯ p/s (` 0F) (𝐂.wk γ₂)
      ■ cong (join p/s (` 0F)) (sym (𝐂.⋯-↑-wk γ₂ _))
T-LetUnit {γ₁ = γ₁} {γ₂} p/s γ-eq x x₁ ⊢⋯ ⊢ϕ =
  let open ≈-Reasoning in
  let eq = begin _ ≈⟨ ⋯-preserves-≈ γ-eq ⟩
                 _ ≡⟨ join-⋯ p/s γ₁ γ₂ ⟩
                 _ ∎
  in
  T-LetUnit p/s eq (x ⊢⋯ ⊢ϕ) (x₁ ⊢⋯ ⊢ϕ)
T-LetPair {γ₁ = γ₁} {γ₂} {d = d} p/s γ-eq x x₁ ⊢⋯ ⊢ϕ =
  let open Fin.Patterns in
  let open ≈-Reasoning in
  let eq = begin _ ≈⟨ ⋯-preserves-≈ γ-eq ⟩
                 _ ≡⟨ join-⋯ p/s γ₁ γ₂ ⟩
                 _ ∎
  in
  T-LetPair p/s eq (x ⊢⋯ ⊢ϕ) $ subst-γ (x₁ ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)) $
    join-⋯ p/s (join d (` 0F) (` 1F)) _
      ■ cong₂ (join p/s) (join-⋯ d _ _)
                         (sym (cong 𝐂.wk (𝐂.⋯-↑-wk γ₂ _) ■ 𝐂.⋯-↑-wk (𝐂.wk γ₂) _))
T-Weak ϵ≤ γ≤ x ⊢⋯ ⊢ϕ = T-Weak ϵ≤ (≼-⋯ γ≤) (x ⊢⋯ ⊢ϕ)

instance
  TKᵣ : TKit Kᵣ
  TKᵣ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → γ ≈ ` x × Γ x ≡ T
    ; ⊢id/` = λ γ-eq → γ-eq , refl
    ; ⊢`/id = λ (γ-eq , T-eq) → T-Var _ γ-eq T-eq
    ; ⊢wk = λ (γ-eq , T-eq) → cong-wk γ-eq , T-eq
    }

  TKₛ : TKit Kₛ
  TKₛ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → Γ ; γ ⊢ x ∶ T ∣ ℙ
    ; ⊢id/` = λ γ-eq → T-Var _ γ-eq refl
    ; ⊢`/id = λ x → x
    ; ⊢wk = λ {_} {Γ} {γ} {T} x → subst (_ ;_⊢ _ ∶ _ ∣ _) (𝐂.weaken/wk γ) (x ⊢⋯ ⊢weaken ⦃ TKᵣ ⦄ {T = T} Γ)
    }
