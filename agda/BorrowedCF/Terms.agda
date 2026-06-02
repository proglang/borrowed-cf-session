{-# OPTIONS --rewriting #-}

module BorrowedCF.Terms where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context

import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.FinKits as Kits using (Scoped) public

open Nat.Variables

data Const : Set where
  `unit `fork `send `recv `drop `acq : Const
  `end : Pol → Const
  `new : 𝕊 0 → Const
  `lsplit `rsplit : 𝕊 0 → Const

data Tm (n : ℕ) : Set where
  `_ : 𝔽 n → Tm n
  K : (c : Const) → Tm n
  ƛ : (e : Tm (1 + n)) → Tm n
  μ : (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _⊗_ : (e₁ : Tm n) (e₂ : Tm n) → Tm n
  `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  `let⊗_`in_ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n

private variable
  e e₁ e₂ : Tm n

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
ƛ e ⋯ ϕ = ƛ (e ⋯ ϕ ↑)
μ e ⋯ ϕ = μ (e ⋯ ϕ ↑)
(e · e₁) ⋯ ϕ = (e ⋯ ϕ) · (e₁ ⋯ ϕ)
(e ; e₁) ⋯ ϕ =  (e ⋯ ϕ) ; (e₁ ⋯ ϕ)
(e ⊗ e₁) ⋯ ϕ =  (e ⋯ ϕ) ⊗ (e₁ ⋯ ϕ)
(`let e `in e₁) ⋯ ϕ = `let (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑)
(`let⊗ e `in e₁) ⋯ ϕ = `let⊗ (e ⋯ ϕ) `in (e₁ ⋯ ϕ ↑ ↑)

⋯-id : ⦃ K : Kit 𝓕 ⦄ (e : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → e ⋯ ϕ ≡ e
⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
⋯-id (K c) eq = refl
⋯-id (ƛ e) eq = cong ƛ (⋯-id e (id↑ eq))
⋯-id (μ e) eq = cong μ (⋯-id e (id↑ eq))
⋯-id (e · e₁) eq = cong₂ _·_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ; e₁) eq = cong₂ _;_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (e ⊗ e₁) eq = cong₂ _⊗_ (⋯-id e eq) (⋯-id e₁ eq)
⋯-id (`let e `in e₁) eq = cong₂ `let_`in_ (⋯-id e eq) (⋯-id e₁ (id↑ eq))
⋯-id (`let⊗ e `in e₁) eq = cong₂ `let⊗_`in_ (⋯-id e eq) (⋯-id e₁ (id↑* 2 eq))

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (e : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → e ⋯ ϕ₁ ≡ e ⋯ ϕ₂
⋯-cong (` x) eq = cong `/id (eq x)
⋯-cong (K c) eq = refl
⋯-cong (ƛ e) eq = cong ƛ (⋯-cong e (eq ~↑))
⋯-cong (μ e) eq = cong μ (⋯-cong e (eq ~↑))
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
fusion (ƛ e) ϕ₁ ϕ₂ = cong ƛ $
  fusion e (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (μ e) ϕ₁ ϕ₂ = cong μ $
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
                 --Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

infix 4 ⊢_∶_

data ⊢_∶_ : Const → 𝕋 → Set where
  `unit : ⊢ `unit ∶ `⊤

  `fork : ⊢ `fork ∶ (`⊤ →1M `⊤ ∣ 𝕀) →1M `⊤ ∣ ℙ

  `new  : ⊢ `new s ∶ `⊤ →1M ⟨ acq ; s ⟩ ⊗¹ ⟨ acq ; dual s ⟩ ∣ ℙ

  `lsplit : ⊢ `lsplit s ∶ ⟨ s ; s′ ⟩ →1M ⟨ s ⟩       ⊗ᴸ ⟨ s′ ⟩       ∣ ℙ
  `rsplit : ⊢ `rsplit s ∶ ⟨ s ; s′ ⟩ →1M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; s′ ⟩ ∣ ℙ

  `drop : ⊢ `drop ∶ ⟨ ret ⟩     →1M `⊤    ∣ ℙ
  `acq  : ⊢ `acq  ∶ ⟨ acq ; s ⟩ →1M ⟨ s ⟩ ∣ ℙ

  `send : Mobile T → ⊢ `send ∶ T ⊗¹ ⟨ msg ‼ T ⟩ →1M `⊤ ∣ 𝕀
  `recv : Mobile T → ⊢ `recv ∶      ⟨ msg ⁇ T ⟩ →1M  T ∣ 𝕀

  `end  : ⊢ `end p ∶ ⟨ end p ⟩ →1M `⊤ ∣ 𝕀

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
    (Γ-unr : Arr.Unr a → UnrCx Γ γ) →
    (Γ-mob : Arr.Mobile a → MobCx Γ γ) →
    T ⸴ Γ ; join (Arr.dir a) (` zero) (𝐂.wk γ) ⊢ e ∶ U ∣ Arr.eff a →
    ----------------------------------------------------------------
    Γ ; γ ⊢ ƛ e ∶ T ⟨ a ⟩→ U ∣ ℙ

  T-AbsRec :
    let open Fin.Patterns in
    UnrCx Γ γ →
    Arr.Unr a →
    T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) ⊢ e ∶ U ∣ Arr.eff a →
    --------------------------------------------------------------------------
    Γ ; γ ⊢ μ (ƛ e) ∶ T ⟨ a ⟩→ U ∣ ℙ

  T-App : ∀ {γ₁ γ₂} →
    Arr.eff a ≡ ϵ →
    Γ ; γ₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T          ∣ ϵ →
    --------------------------------------------
    Γ ; join (Arr.dir a) γ₂ γ₁ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-Pair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    let d = biasedDir p/s in
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    Seq⇒Pure p/s ϵ₁ ϵ₂ →
    --------------------------------------------
    Γ ; join d γ₁ γ₂ ⊢ e₁ ⊗ e₂ ∶ T ⊗⟨ d ⟩ U ∣ ϵ₁

  T-Let : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ →
    T ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ →
    --------------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let e₁ `in e₂ ∶ U ∣ ϵ

  T-LetUnit : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ `⊤ ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T  ∣ ϵ →
    ------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ e₁ ; e₂ ∶ T ∣ ϵ

  T-LetPair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ →
    T₁ ⸴ T₂ ⸴ Γ ;
      join p/s (join d (` zero) (` suc zero))
               (𝐂.wk (𝐂.wk γ₂))
      ⊢ e₂ ∶ U ∣ ϵ →
    --------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let⊗ e₁ `in e₂ ∶ U ∣ ϵ

  T-Eff :
    (ϵ≤ : ϵ₁ ≤ϵ ϵ₂) →
    Γ ; γ ⊢ e ∶ T ∣ ϵ₁ →
    --------------------
    Γ ; γ ⊢ e ∶ T ∣ ϵ₂

  T-Weaken :
    (γ≤ : Γ ∶ γ₁ ≼ γ₂) →
    Γ ; γ₁ ⊢ e ∶ T ∣ ϵ →
    --------------------
    Γ ; γ₂ ⊢ e ∶ T ∣ ϵ

record TKit (K : Kit 𝓕) : Set₁ where
  private instance _ = K

  field
    𝓕[_;_⊢_∶_] : Ctx n → Struct n → 𝓕 n → 𝕋 → Set
    ⊢id/` : (x : 𝔽 n) → 𝓕[ Γ ; ` x ⊢ id/` x ∶ Γ x ]
    ⊢`/id : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → Γ ; γ ⊢ `/id x/t ∶ T ∣ ℙ
    ⊢wk : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ U ] → 𝓕[ T ⸴ Γ ; 𝐂.wk γ ⊢ wk x/t ∶ U ]

  infix 4 _∶_⊢_⇒_

  record _∶_⊢_⇒_ (ϕ : m –[ K ]→ n) (σ : m 𝐂.→ₛ n) (Γ₁ : Ctx m) (Γ₂ : Ctx n) : Set where
    field
      _&_ : ∀ x → 𝓕[ Γ₂ ; σ x ⊢ ϕ x ∶ Γ₁ x ]
      &-unr : σ 𝐂.Preserves[ Unr ] Γ₁ ⇒ Γ₂
      &-mob : σ 𝐂.Preserves[ Mobile ] Γ₁ ⇒ Γ₂

  open _∶_⊢_⇒_ public

  ⊢id : {Γ : Ctx n} → idₖ ∶ 𝐂.idₛ ⊢ Γ ⇒ Γ
  ⊢id = record { _&_ = ⊢id/` ; &-unr = `_ ; &-mob = `_ }

  ⊢↑ : ∀ {ϕ : m –[ K ]→ n} {σ} → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ↑ ∶ σ 𝐂.↑ ⊢ T ⸴ Γ₁ ⇒ T ⸴ Γ₂
  ⊢↑ ⊢ϕ = record
    { _&_   = λ{ zero → ⊢id/` zero; (suc x) → ⊢wk (⊢ϕ & x) }
    ; &-unr = λ {x} → 𝐂.↑-preserves (&-unr ⊢ϕ) {x}
    ; &-mob = λ {x} → 𝐂.↑-preserves (&-mob ⊢ϕ) {x}
    }

  ⊢sub : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → (Unr T → UnrCx Γ γ) → (Mobile T → MobCx Γ γ) → ⦅ x/t ⦆ ∶ 𝐂.⦅ γ ⦆ ⊢ T ⸴ Γ ⇒ Γ
  ⊢sub ⊢x/t γ-unr γ-mob = record
    { _&_   = λ{ zero   → ⊢x/t ; (suc y) → ⊢id/` y }
    ; &-unr = λ{ {zero} → γ-unr; {suc y} → `_ }
    ; &-mob = λ{ {zero} → γ-mob; {suc y} → `_ }
    }

  ⊢weaken : (Γ : Ctx n) → weaken ∶ 𝐂.weaken ⊢ Γ ⇒ T ⸴ Γ
  ⊢weaken Γ = record { _&_ = ⊢wk ∘ ⊢id/` ; &-unr = `_ ; &-mob = `_}

infix 4 _∶_⊢[_]_⇒_

_∶_⊢[_]_⇒_ : ∀ {K : Kit 𝓕} → m –[ K ]→ n → m 𝐂.→ₛ n → TKit K → Ctx m → Ctx n → Set
ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ = ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ where open TKit TK

open TKit ⦃ ... ⦄ public

subst-γ : γ₁ ≡ γ₂ → Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
subst-γ refl x = x

infixl 5 _⊢⋯_

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄ →
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄ →
       {ϕ : m –[ K ]→ n} {σ : _} →
       Γ₁ ; γ ⊢ e ∶ T ∣ ϵ →
       ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ →
       Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
T-Const x ⊢⋯ ⊢ϕ = T-Const x
_⊢⋯_ {γ = γ} (T-Var x T-eq) ⊢ϕ =
  let open ≈-Reasoning in
  ⊢`/id (subst 𝓕[ _ ; _ ⊢ _ ∶_] T-eq (⊢ϕ & x))
_⊢⋯_ {γ = γ} (T-Abs {a = a} Γ-unr Γ-mob x) ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ (Arr.dir a) (` 0F) _
             ■ cong (join (Arr.dir a) (` 0F)) (sym (𝐂.⋯-↑-wk γ _))
  in
  T-Abs (𝐂.allCx-⋯ (&-unr ⊢ϕ) ∘ Γ-unr) (𝐂.allCx-⋯ (&-mob ⊢ϕ) ∘ Γ-mob)
    $ subst-γ eq
    $ x ⊢⋯ ⊢↑ ⊢ϕ
_⊢⋯_ {γ = γ} (T-AbsRec Γ-unr a-unr x) ⊢ϕ =
  let open Fin.Patterns in
  let eq = cong 𝐂.wk (𝐂.⋯-↑-wk γ _) ■ 𝐂.⋯-↑-wk (𝐂.wk γ) _ in
  T-AbsRec (𝐂.allCx-⋯ (&-unr ⊢ϕ) Γ-unr) a-unr
    $ subst-γ (cong (_ ∥_) (sym eq))
    $ x ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)
T-App {a = a} {γ₁ = γ₁} {γ₂} ϵ-eq e₁ e₂ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ (Arr.dir a) γ₂ γ₁)) $
    T-App ϵ-eq (e₁ ⊢⋯ ⊢ϕ) (e₂ ⊢⋯ ⊢ϕ)
T-Pair p/s {γ₁} {γ₂} x₁ x₂ seq→ℙ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-Pair p/s (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ) seq→ℙ
T-Let p/s {γ₁} {γ₂} x₁ x₂ ⊢⋯ ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (` 0F) (𝐂.wk γ₂) ■ cong (join p/s (` 0F)) (sym (𝐂.⋯-↑-wk γ₂ _)) in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂))
    $ T-Let p/s (x₁ ⊢⋯ ⊢ϕ)
    $ subst-γ eq
    $ x₂ ⊢⋯ ⊢↑ ⊢ϕ
T-LetUnit p/s {γ₁} {γ₂} x x₁ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-LetUnit p/s (x ⊢⋯ ⊢ϕ) (x₁ ⊢⋯ ⊢ϕ)
T-LetPair {d = d} p/s {γ₁} {γ₂} x x₁ ⊢⋯ ⊢ϕ  =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (join d (` 0F) (` 1F)) _
             ■ cong₂ (join p/s) (join-⋯ d _ _)
                     (sym (cong 𝐂.wk (𝐂.⋯-↑-wk γ₂ _) ■ 𝐂.⋯-↑-wk (𝐂.wk γ₂) _))
  in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂))
    $ T-LetPair p/s (x ⊢⋯ ⊢ϕ)
    $ subst-γ eq
    $ x₁ ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)
T-Eff ϵ≤ x ⊢⋯ ⊢ϕ = T-Eff ϵ≤ (x ⊢⋯ ⊢ϕ)
T-Weaken γ≤ x ⊢⋯ ⊢ϕ = T-Weaken (𝐂.≼-⋯ (&-unr ⊢ϕ) γ≤) (x ⊢⋯ ⊢ϕ)

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
    ; ⊢wk   = λ {_} {Γ} {γ} {T} {U} x → subst (_ ;_⊢ _ ∶ _ ∣ _) (𝐂.weaken/wk γ) $
                x ⊢⋯ ⊢weaken ⦃ TKᵣ ⦄ {T = U} Γ
    }

open TKit TKᵣ using () renaming (⊢weaken to ⊢weakenᵣ) public
open TKit TKₛ using () renaming (⊢sub to ⊢subₛ) public

infixl 5 _⊢⋯ₛ_

_⊢⋯ₛ_ : ∀ {ϕ : m →ₖ n} {σ} → Γ₁ ; γ ⊢ e ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKₛ ] Γ₁ ⇒ Γ₂ → Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
_⊢⋯ₛ_ = _⊢⋯_ ⦃ TK = TKₛ ⦄

swapᵣ : ∀ m₁ m₂ {n} → m₁ + m₂ + n →ᵣ m₂ + m₁ + n
swapᵣ m₁ m₂ = Fin.join _ _ ∘ Sum.map₁ (Fin.swap m₁) ∘ Fin.splitAt (m₁ + m₂)

assocSwapᵣ : ∀ a b {n} → a + (b + n) →ᵣ b + (a + n)
assocSwapᵣ a b {n} = Fin.cast (+-assoc b a n) ∘ swapᵣ a b ∘ Fin.cast (sym (+-assoc a b n))

wk-swap : ∀ a b {n} → weaken* (a + b) ·ₖ swapᵣ a b {n} ≗ weaken* ⦃ Kᵣ ⦄ (b + a)
wk-swap a b x rewrite
  weaken*~↑ʳ ⦃ Kᵣ ⦄ (a + b) x
    | Fin.splitAt-↑ʳ (a + b) _ x
    | weaken*~↑ʳ ⦃ Kᵣ ⦄ (b + a) x
    = refl

module _ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ where
  open ≡-Reasoning

  &/⋯-wk∘weaken : ∀ m (x/t : 𝓕[ K ] n) →
    wk ⦃ K ⦄ (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ≡ x/t &/⋯ weaken* ⦃ Kᵣ ⦄ (suc m)
  &/⋯-wk∘weaken m x/t = `/id-injective $
    `/id ⦃ K ⦄ (wk (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m)) ≡⟨ wk-`/id (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ⟨
    `/id ⦃ K ⦄ (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ⋯ weakenᵣ ≡⟨ cong (_⋯ weakenᵣ) (&/⋯-⋯ x/t (weaken* m)) ⟩
    `/id ⦃ K ⦄ x/t ⋯ weaken* m ⋯ weakenᵣ ≡⟨ fusion (`/id x/t) (weaken* m) weakenᵣ ⟩
    `/id ⦃ K ⦄ x/t ⋯ weaken* (suc m) ≡⟨ &/⋯-⋯ x/t (weaken* (suc m)) ⟨
    `/id ⦃ K ⦄ (x/t &/⋯ weaken* (suc m)) ∎

  ↑*∼id/wk-splitAt : ∀ (ϕ : n₁ –[ K ]→ n₂) m →
    ϕ ↑* m ≗ [ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ m ] ∘ Fin.splitAt m
  ↑*∼id/wk-splitAt ϕ zero x = `/id-injective $
    `/id ((ϕ ↑* zero) x)    ≡⟨⟩
    `/id (ϕ x)              ≡⟨ ⋯-id (`/id (ϕ x)) (λ _ → refl) ⟨
    `/id (ϕ x) ⋯ (λ y → y)  ≡⟨ &/⋯-⋯ (ϕ x) (λ y → y) ⟨
    `/id (ϕ x &/⋯ λ y → y)  ∎
  ↑*∼id/wk-splitAt ϕ (suc m) zero = refl
  ↑*∼id/wk-splitAt {n₁ = n₁} {n₂} ϕ (suc m) (suc x) = `/id-injective $
    `/id ⦃ K ⦄ ((ϕ ↑* suc m) (suc x))  ≡⟨⟩
    `/id ⦃ K ⦄ (wk ((ϕ ↑* m) x))       ≡⟨ cong (`/id ∘ wk) (↑*∼id/wk-splitAt ϕ m x) ⟩
    `/id ⦃ K ⦄ (wk ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ m ] (Fin.splitAt m x)))
      ≡⟨ cong (`/id ⦃ K ⦄) ([,]-∘ (wk ⦃ K ⦄) (Fin.splitAt m x)) ⟩
    `/id ⦃ K ⦄ ([ wk ∘ id/` ∘ (_↑ˡ n₂) , wk ∘ (ϕ ·ₖ weaken* m) ] (Fin.splitAt m x))
      ≡⟨ cong (`/id ⦃ K ⦄) ([,]-cong (λ y → wk-id/` (y ↑ˡ _)) (λ y → &/⋯-wk∘weaken m (ϕ y)) (Fin.splitAt m x)) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) ∘ suc , ϕ ·ₖ weaken* (suc m) ] (Fin.splitAt m x))
      ≡⟨ cong (`/id ⦃ K ⦄) ([,]-map (Fin.splitAt m x)) ⟨
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (suc m) ] (Sum.map₁ suc (Fin.splitAt m x))) ≡⟨⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (suc m) ] (Fin.splitAt (suc m) (suc x))) ∎

  dist-↑*-swapˡ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
      ≡
    `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n₂) &/⋯ swapᵣ b₁ b₂)
  dist-↑*-swapˡ b₁ b₂ {n₁} {n₂} {ϕ} x =
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
      ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (b₂ + b₁) ] (splitAt (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)))
      ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ˡ (b₂ + b₁) (Fin.swap b₁ x) n₁) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (b₂ + b₁) ]′ (inj₁ (Fin.swap b₁ x)))
      ≡⟨⟩
    `/id ⦃ K ⦄ (id/` (Fin.swap b₁ x ↑ˡ n₂))
      ≡⟨ `/`-is-` ⦃ K ⦄ (Fin.swap b₁ x ↑ˡ n₂) ⟩
    ` (Fin.swap b₁ x ↑ˡ n₂)
      ≡⟨⟩
    ` (Fin.join (b₂ + b₁) n₂ (inj₁ (Fin.swap b₁ x)))
      ≡⟨ cong (`_ ∘ Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁)) (Fin.splitAt-↑ˡ (b₁ + b₂) x n₂) ⟨
    ` (Fin.join _ _ (Sum.map₁ (Fin.swap b₁) (Fin.splitAt (b₁ + b₂) (x ↑ˡ n₂))))
      ≡⟨⟩
    ` (swapᵣ b₁ b₂ (x ↑ˡ n₂))
      ≡⟨ &/⋯-& ⦃ C ⦄ (x ↑ˡ n₂) (swapᵣ b₁ b₂) ⟨
    `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n₂) &/⋯ swapᵣ b₁ b₂) ∎

  dist-↑*-swapʳ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
      ≡
    `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (swapᵣ b₁ b₂))
  dist-↑*-swapʳ b₁ b₂ {n₁} {n₂} {ϕ} x =
    `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
      ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (b₂ + b₁ ↑ʳ x)) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ] (Fin.splitAt (b₂ + b₁) (b₂ + b₁ ↑ʳ x)))
      ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ʳ (b₂ + b₁) n₁ x) ⟩
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ]′ (inj₂ x))
      ≡⟨⟩
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₂ + b₁))
      ≡⟨ &/⋯-⋯ (ϕ x) (weaken* (b₂ + b₁)) ⟩
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₂ + b₁)
      ≡⟨ ⋯-cong (`/id (ϕ x)) (wk-swap b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ·ₖ swapᵣ b₁ b₂
      ≡⟨ fusion (`/id (ϕ x)) (weaken* (b₁ + b₂)) (swapᵣ b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ⋯ swapᵣ b₁ b₂
      ≡⟨ cong (_⋯ swapᵣ b₁ b₂) (&/⋯-⋯ (ϕ x) (weaken* (b₁ + b₂))) ⟨
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂)) ⋯ swapᵣ b₁ b₂
      ≡⟨ &/⋯-⋯ (ϕ x &/⋯ weaken* (b₁ + b₂)) (swapᵣ b₁ b₂) ⟨
    `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂) &/⋯ swapᵣ b₁ b₂)
      ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (swapᵣ b₁ b₂)) ∎

  dist-↑*-swap : ∀ m₁ m₂ {n₁ n₂} (ϕ : n₁ –[ K ]→ n₂) →
    swapᵣ m₁ m₂ {n₁} ·[ Cᵣ ] ϕ ↑* (m₂ + m₁) ≗ ϕ ↑* (m₁ + m₂) ·ₖ swapᵣ m₁ m₂ {n₂}
  dist-↑*-swap m₁ m₂ {n₁} {n₂} ϕ x = `/id-injective $
    `/id ⦃ K ⦄ ((swapᵣ m₁ m₂ ·[ Cᵣ ] ϕ ↑* (m₂ + m₁)) x) ≡⟨⟩
    `/id ⦃ K ⦄ (swapᵣ m₁ m₂ x &/⋯ ϕ ↑* (m₂ + m₁))
      ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) z)) (Sum.map₁ (Fin.swap m₁) (Fin.splitAt (m₁ + m₂) x)) ⟩
    [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) (y ↑ˡ n₁)))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) ((m₂ + m₁) ↑ʳ y)))
    ] (Sum.map₁ (Fin.swap m₁) (Fin.splitAt (m₁ + m₂) x))
      ≡⟨ [,]-map (Fin.splitAt (m₁ + m₂) x) ⟩
    [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) (Fin.swap m₁ y ↑ˡ n₁)))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) ((m₂ + m₁) ↑ʳ y)))
    ] (Fin.splitAt (m₁ + m₂) x)
      ≡⟨ [,]-cong (dist-↑*-swapˡ m₁ m₂) (dist-↑*-swapʳ m₁ m₂) (Fin.splitAt (m₁ + m₂) x) ⟩
    [ (λ y → `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (y ↑ˡ _) &/⋯ swapᵣ m₁ m₂ {n₂}))
    , (λ y → `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (m₁ + m₂)) y &/⋯ swapᵣ m₁ m₂ {n₂}))
    ] (Fin.splitAt (m₁ + m₂) x)
      ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ (CKit._&/⋯_ C z (swapᵣ m₁ m₂ {n₂}))) (Fin.splitAt (m₁ + m₂) x) ⟨
    `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ _) , ϕ ·ₖ weaken* (m₁ + m₂) ] (Fin.splitAt (m₁ + m₂) x) &/⋯ swapᵣ m₁ m₂ {n₂})
      ≡⟨ cong (λ z → `/id (z &/⋯ swapᵣ m₁ m₂)) (↑*∼id/wk-splitAt ϕ (m₁ + m₂) x) ⟨
    `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂)) x &/⋯ swapᵣ m₁ m₂) ≡⟨⟩
    `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂) ·ₖ swapᵣ m₁ m₂) x) ∎

  postulate
    dist-↑*-assocSwap : ∀ a b {m n} (ϕ : m –[ K ]→ n) →
      assocSwapᵣ a b {m} ·[ Cᵣ ] ϕ ↑* a ↑* b ≗ ϕ ↑* b ↑* a ·ₖ assocSwapᵣ a b {n}
  -- dist-↑*-assocSwap a b {m} {n} ϕ x = `/id-injective $
  --   `/id ⦃ K ⦄ ((ϕ ↑* a ↑* b) (assocSwapᵣ a b x)) ≡⟨ {!!} ⟩
  --   `/id ⦃ K ⦄ ((ϕ ↑* b ↑* a) x &/⋯ assocSwapᵣ a b) ∎
