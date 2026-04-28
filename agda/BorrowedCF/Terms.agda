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
  _⊗_ : (e₁ : Tm n) (e₂ : Tm n) → Tm n
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
(e ⊗ e₁) ⋯ ϕ =  (e ⋯ ϕ) ⊗ (e₁ ⋯ ϕ)
(`let e `in e₁) ⋯ ϕ = `let (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑)
(`let⊗ e `in e₁) ⋯ ϕ = `let⊗ (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑ ↑)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (e : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → e ⋯ ϕ ≡ e
⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
⋯-id (K c) eq = refl
⋯-id (λ[ d ] e) eq = cong λ[ d ] (⋯-id e (id↑ eq))
⋯-id (e · e₁) eq = cong₂ _·_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ; e₁) eq = cong₂ _;_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ⊗ e₁) eq = cong₂ _⊗_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-id e eq) (⋯-id e₁ (id↑ eq))
⋯-id (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-id e eq) (⋯-id e₁ (id↑* 2 eq))

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (e : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → e ⋯ ϕ₁ ≡ e ⋯ ϕ₂
⋯-cong (` x) eq = cong `/id (eq x)
⋯-cong (K c) eq = refl
⋯-cong (λ[ d ] e) eq = cong λ[ d ] (⋯-cong e (eq ~↑))
⋯-cong (e · e₁) eq = cong₂ _·_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ; e₁) eq = cong₂ _;_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (e ⊗ e₁) eq = cong₂ _⊗_ (⋯-cong e eq) (⋯-cong e₁ eq)
⋯-cong (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑))
⋯-cong (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-cong e eq) (⋯-cong e₁ (eq ~↑* 2))

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-id; ⋯-cong; CTraversal)
  public

fusion :
  ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
  (x : Tm n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) → x ⋯ ϕ₁ ⋯ ϕ₂ ≡ x ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion (x₁ ; x₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x₁ ϕ₁ ϕ₂) (fusion x₂ ϕ₁ ϕ₂)
fusion (K c) ϕ₁ ϕ₂ = refl
fusion (λ[ d ] e) ϕ₁ ϕ₂ = cong λ[ d ] $
  fusion e (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (e₁ · e₂) ϕ₁ ϕ₂ = cong₂ _·_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (e₁ ⊗ e₂) ϕ₁ ϕ₂ = cong₂ _⊗_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
fusion (`let e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e₂ (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (`let⊗ e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion e₁ ϕ₁ ϕ₂) $
  fusion e₂ (ϕ₁ ↑* 2) (ϕ₂ ↑* 2) ■ ⋯-cong e₂ (sym ∘ dist-↑*-· 2 ϕ₁ ϕ₂)

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

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

data _;_⊢_∶_∣_ (Γ : Ctx n) : Struct n → Tm n → 𝕋 → Eff → Set where
  T-Const : ∀ {c} →
    ⊢ c ∶ T →
    --------------------
    Γ ; [] ⊢ K c ∶ T ∣ ℙ

  T-Var : ∀ x →
    (T-eq : Γ x ≡ T) →
    ---------------------
    Γ ; ` x ⊢ ` x ∶ T ∣ ℙ

  T-Abs :
    (𝓂→C : 𝓂 ≡ mob → MobCx Γ γ) →
    T F.∷ Γ ; join d (` zero) (𝐂.wk γ) ⊢ e ∶ U ∣ ϵ →
    ------------------------------------------------
    Γ ; γ ⊢ λ[ d ] e ∶ arr 𝓂 d ϵ T U ∣ ℙ

  T-App : ∀ {d γ₁ γ₂} →
    Γ ; γ₁ ⊢ e₁ ∶ arr 𝓂 d ϵ T U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T             ∣ ϵ →
    ----------------------------------
    Γ ; join d γ₂ γ₁ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-Pair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    let d = biasedDir p/s in
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    Seq⇒Pure p/s ϵ₁ ϵ₂ →
    -------------------------------------------------
    Γ ; join d γ₁ γ₂ ⊢ e₁ ⊗ e₂ ∶ pair d T U ∣ ϵ₁

  T-Let : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ →
    T F.∷ Γ ; join p/s (` zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ →
    ----------------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let e₁ `in e₂ ∶ U ∣ ϵ

  T-LetUnit : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ unit ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T    ∣ ϵ →
    ------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ e₁ ; e₂ ∶ T ∣ ϵ

  T-LetPair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ pair d T₁ T₂ ∣ ϵ →
    T₁ F.∷ T₂ F.∷ Γ ;
      join p/s (join d (` zero) (` suc zero))
               (𝐂.wk (𝐂.wk γ₂))
      ⊢ e₂ ∶ U ∣ ϵ →
    --------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let⊗ e₁ `in e₂ ∶ U ∣ ϵ

  T-Weaken :
    (ϵ≤ : ϵ₁ ≤ϵ ϵ₂) →
    (γ≤ : γ₁ ≼ γ₂) →
    Γ ; γ₁ ⊢ e ∶ T ∣ ϵ₁ →
    ---------------------
    Γ ; γ₂ ⊢ e ∶ T ∣ ϵ₂


record TKit (K : Kit 𝓕) : Set₁ where
  private instance _ = K

  field
    𝓕[_;_⊢_∶_] : Ctx n → Struct n → 𝓕 n → 𝕋 → Set
    ⊢id/` : (x : 𝔽 n) → 𝓕[ Γ ; ` x ⊢ id/` x ∶ Γ x ]
    ⊢`/id : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → Γ ; γ ⊢ `/id x/t ∶ T ∣ ℙ
    ⊢wk : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ U ] → 𝓕[ T F.∷ Γ ; 𝐂.wk γ ⊢ wk x/t ∶ U ]

  infix 4 _∶_⊢_⇒_

  _∶_⊢_⇒_ : m –[ K ]→ n → m 𝐂.→ₛ n → Ctx m → Ctx n → Set
  ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ = ∀ x → 𝓕[ Γ₂ ; σ x ⊢ ϕ x ∶ Γ₁ x ]

  ⊢id : {Γ : Ctx n} → idₖ ∶ 𝐂.idₛ ⊢ Γ ⇒ Γ
  ⊢id x = ⊢id/` x

  ⊢↑ : ∀ {ϕ : m –[ K ]→ n} {σ} → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ↑ ∶ σ 𝐂.↑ ⊢ T F.∷ Γ₁ ⇒ T F.∷ Γ₂
  ⊢↑ ⊢ϕ zero = ⊢id/` zero
  ⊢↑ ⊢ϕ (suc x) = ⊢wk (⊢ϕ x)

  ⊢⦅_⦆ : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → ⦅ x/t ⦆ ∶ 𝐂.⦅ γ ⦆ ⊢ T F.∷ Γ ⇒ Γ
  ⊢⦅ ⊢x/t ⦆ zero    = ⊢x/t
  ⊢⦅ ⊢x/t ⦆ (suc y) = ⊢id/` y

  ⊢weaken : (Γ : Ctx n) → weaken ∶ 𝐂.weaken ⊢ Γ ⇒ T F.∷ Γ
  ⊢weaken Γ x = ⊢wk (⊢id/` x)

infix 4 _∶_⊢[_]_⇒_

_∶_⊢[_]_⇒_ : ∀ {K : Kit 𝓕} → m –[ K ]→ n → m 𝐂.→ₛ n → TKit K → Ctx m → Ctx n → Set
ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ = ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ where open TKit TK

open TKit ⦃ ... ⦄ public

infixl 5 _⊢≈_ _⊢⋯_

_⊢≈_ : Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → γ₁ ≈ γ₂ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
x ⊢≈ eq = T-Weaken ≤ϵ-refl (refl eq) x

mobCx-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
  {ϕ : m –[ K ]→ n} {σ : _} →
  MobCx Γ₁ γ → ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ → MobCx Γ₂ (γ 𝐂.⋯ σ)
mobCx-⋯ [] ⊢ϕ = []
mobCx-⋯ (C₁ ∥ C₂) ⊢ϕ = mobCx-⋯ C₁ ⊢ϕ ∥ mobCx-⋯ C₂ ⊢ϕ
mobCx-⋯ (C₁ ; C₂) ⊢ϕ = mobCx-⋯ C₁ ⊢ϕ ; mobCx-⋯ C₂ ⊢ϕ
mobCx-⋯ (` x) ⊢ϕ = {!MobCx.` ?!}

subst-γ : γ₁ ≡ γ₂ → Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
subst-γ refl x = x

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ →
       {ϕ : m –[ K ]→ n} {σ : _} →
       Γ₁ ; γ ⊢ e ∶ T ∣ ϵ →
       ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ →
       Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
T-Const x ⊢⋯ ⊢ϕ = T-Const x
_⊢⋯_ {γ = γ} {σ = σ} (T-Var x T-eq) ⊢ϕ =
  let open ≈-Reasoning in
  ⊢`/id (subst 𝓕[ _ ; _ ⊢ _ ∶_] T-eq (⊢ϕ x))
_⊢⋯_ {γ = γ} (T-Abs {d = d} 𝓂→C x) ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ d (` 0F) _
             ■ cong (join d (` 0F)) (sym (𝐂.⋯-↑-wk γ _))
  in
  T-Abs {!{!mobCx-≈!} ∘ 𝓂→C!} (subst-γ eq (x ⊢⋯ ⊢↑ ⊢ϕ))
T-App {d = d} {γ₁} {γ₂} e₁ e₂ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ d γ₂ γ₁)) $
    T-App (e₁ ⊢⋯ ⊢ϕ) (e₂ ⊢⋯ ⊢ϕ)
T-Pair p/s {γ₁} {γ₂} x₁ x₂ seq→ℙ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-Pair p/s (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ) seq→ℙ
T-Let p/s {γ₁} {γ₂} x₁ x₂ ⊢⋯ ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (` 0F) (𝐂.wk γ₂) ■ cong (join p/s (` 0F)) (sym (𝐂.⋯-↑-wk γ₂ _)) in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-Let p/s (x₁ ⊢⋯ ⊢ϕ) $ subst-γ eq (x₂ ⊢⋯ ⊢↑ ⊢ϕ)
T-LetUnit p/s {γ₁} {γ₂} x x₁ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-LetUnit p/s (x ⊢⋯ ⊢ϕ) (x₁ ⊢⋯ ⊢ϕ)
T-LetPair {d = d} p/s {γ₁} {γ₂} x x₁ ⊢⋯ ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (join d (` 0F) (` 1F)) _
             ■ cong₂ (join p/s) (join-⋯ d _ _)
                     (sym (cong 𝐂.wk (𝐂.⋯-↑-wk γ₂ _) ■ 𝐂.⋯-↑-wk (𝐂.wk γ₂) _))
  in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-LetPair p/s (x ⊢⋯ ⊢ϕ) $ subst-γ eq (x₁ ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ))
T-Weaken ϵ≤ γ≤ x ⊢⋯ ⊢ϕ = T-Weaken ϵ≤ (≼-⋯ γ≤) (x ⊢⋯ ⊢ϕ)

instance
  TKᵣ : TKit Kᵣ
  TKᵣ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → γ ≡ ` x × Γ x ≡ T
    ; ⊢id/` = λ x → refl , refl
    ; ⊢`/id = λ{ (refl , T-eq) → T-Var _ T-eq }
    ; ⊢wk   = λ{ (refl , T-eq) → refl , T-eq }
    }

  TKₛ : TKit Kₛ
  TKₛ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → Γ ; γ ⊢ x ∶ T ∣ ℙ
    ; ⊢id/` = λ x → T-Var _ refl
    ; ⊢`/id = λ x → x
    ; ⊢wk   = λ {_} {Γ} {γ} {T} x → subst (_ ;_⊢ _ ∶ _ ∣ _) (𝐂.weaken/wk γ) (x ⊢⋯ ⊢weaken ⦃ TKᵣ ⦄ {T = T} Γ)
    }

open TKit TKᵣ using () renaming (⊢⦅_⦆ to ⊢⦅_⦆ᵣ; ⊢weaken to ⊢weakenᵣ) public
open TKit TKₛ using () renaming (⊢⦅_⦆ to ⊢⦅_⦆ₛ) public

infixl 5 _⊢⋯ₛ_

_⊢⋯ₛ_ : {ϕ : m →ₖ n} {σ : _} →
        Γ₁ ; γ ⊢ e ∶ T ∣ ϵ →
        ϕ ∶ σ ⊢[ TKₛ ] Γ₁ ⇒ Γ₂ →
        Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
_⊢⋯ₛ_ = _⊢⋯_ ⦃ TK = TKₛ ⦄
