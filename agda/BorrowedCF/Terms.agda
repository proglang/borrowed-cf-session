{-# OPTIONS --rewriting #-}

module BorrowedCF.Terms where

open import Data.Bool using () renaming (Bool to Side; true to L; false to R) public

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

isSplit? : (c : Const) → Dec (∃[ s ] (c ≡ `lsplit s ⊎ c ≡ `rsplit s))
isSplit? `unit = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? `fork = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? `send = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? `recv = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? `drop = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? `acq = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? (`end x) = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? (`new x) = no λ{ (_ , inj₁ ()) ; (_ , inj₂ ()) }
isSplit? (`lsplit x) = yes (x , inj₁ refl)
isSplit? (`rsplit x) = yes (x , inj₂ refl)

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
  `inj : (i : Side) (e : Tm n) → Tm n
  `case_`of⟨_;_⟩ : (e : Tm n) (e₁ e₂ : Tm (1 + n)) → Tm n

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
`inj i e ⋯ ϕ = `inj i (e ⋯ ϕ)
`case e `of⟨ e₁ ; e₂ ⟩ ⋯ ϕ = `case (e ⋯ ϕ) `of⟨ (e₁ ⋯ ϕ ↑) ; (e₂ ⋯ ϕ ↑) ⟩

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
⋯-id (`inj i e) eq = cong (`inj i) (⋯-id e eq)
⋯-id (`case e `of⟨ e₁ ; e₂ ⟩) eq
  rewrite ⋯-id e eq | ⋯-id e₁ (id↑ eq) | ⋯-id e₂ (id↑ eq)
  = refl

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
⋯-cong (`inj i e) eq = cong (`inj i) (⋯-cong e eq)
⋯-cong (`case e `of⟨ e₁ ; e₂ ⟩) eq
  rewrite ⋯-cong e eq | ⋯-cong e₁ (eq ~↑) | ⋯-cong e₂ (eq ~↑)
  = refl

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
fusion (`inj i e) ϕ₁ ϕ₂ = cong (`inj i) (fusion e ϕ₁ ϕ₂)
fusion (`case e `of⟨ e₁ ; e₂ ⟩) ϕ₁ ϕ₂ rewrite fusion e ϕ₁ ϕ₂ =
  cong₂ (`case _ `of⟨_;_⟩)
    (fusion e₁ (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e₁ (sym ∘ dist-↑-· ϕ₁ ϕ₂))
    (fusion e₂ (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong e₂ (sym ∘ dist-↑-· ϕ₁ ϕ₂))

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

infix 4 ⊢_∶_

data ⊢_∶_ : Const → 𝕋 → Set where
  `unit : ⊢ `unit ∶ `⊤

  `fork : ⊢ `fork ∶ (`⊤ →1M `⊤ ∣ 𝕀) →1M `⊤ ∣ ℙ

  `new  : ⊢ `new s ∶ `⊤ →1M ⟨ acq ; s ; end ⁇ ⟩ ⊗¹ ⟨ acq ; dual s ; end ‼ ⟩ ∣ ℙ

  `lsplit : ¬ Skips s → (s′ : 𝕊 0) →
    ⊢ `lsplit s ∶ ⟨ s ; s′ ⟩ →1M ⟨ s ⟩       ⊗ᴸ ⟨ s′ ⟩       ∣ ℙ
  `rsplit : ¬ Skips s → (s′ : 𝕊 0) →
    ⊢ `rsplit s ∶ ⟨ s ; s′ ⟩ →1M ⟨ s ; ret ⟩ ⊗¹ ⟨ acq ; s′ ⟩ ∣ ℙ

  `drop : ⊢ `drop ∶ ⟨ ret ⟩     →1M `⊤    ∣ ℙ
  `acq  : ⊢ `acq  ∶ ⟨ acq ; s ⟩ →1M ⟨ s ⟩ ∣ ℙ

  `send : Mobile T → ⊢ `send ∶ T ⊗¹ ⟨ msg ‼ T ⟩ →1M `⊤ ∣ 𝕀
  `recv : Mobile T → ⊢ `recv ∶      ⟨ msg ⁇ T ⟩ →1M  T ∣ 𝕀

  `end  : ⊢ `end p ∶ ⟨ end p ⟩ →1M `⊤ ∣ 𝕀

infix 4 _;_⊢_∶_∣_

data _;_⊢_∶_∣_ (Γ : Ctx n) : Struct n → Tm n → 𝕋 → Eff → Set where
  T-Const : ∀ {c} →
    (⊢c : ⊢ c ∶ T) →
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
    (Γ-unr : UnrCx Γ γ) →
    (a-unr : Arr.Unr a) →
    T ⸴ T ⟨ a ⟩→ U ⸴ Γ ; (` 0F) ∥ (` 1F) ∥ 𝐂.wk (𝐂.wk γ) ⊢ e ∶ U ∣ Arr.eff a →
    --------------------------------------------------------------------------
    Γ ; γ ⊢ μ (ƛ e) ∶ T ⟨ a ⟩→ U ∣ ℙ

  T-AppUnr :
    (a-unr : Arr.Unr a) →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    Γ ; γ₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T          ∣ ϵ →
    -------------------------------
    Γ ; γ₁ ∥ γ₂ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-AppLin :
    (a-par : Arr.Par a) →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    Γ ; γ₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T          ∣ ϵ →
    ------------------------------
    Γ ; γ₁ ∥ γ₂ ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-AppLeft :
    (aL : Arr.IsL a) →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    Γ ; γ₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ℙ →
    Γ ; γ₂ ⊢ e₂ ∶ T          ∣ ϵ →
    -------------------------------
    Γ ; (γ₂ ; γ₁) ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-AppRight :
    (aR : Arr.IsR a) →
    (≤ₐ : Arr.eff a ≤ϵ ϵ) →
    Γ ; γ₁ ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T          ∣ ℙ →
    -------------------------------
    Γ ; (γ₁ ; γ₂) ⊢ e₁ · e₂ ∶ U ∣ ϵ

  T-Pair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    let d = biasedDir p/s in
    (seq⇒p : Seq⇒Pure p/s ϵ₁ ϵ₂) →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ₁ →
    Γ ; γ₂ ⊢ e₂ ∶ U ∣ ϵ₂ →
    --------------------------------------------
    Γ ; join d γ₁ γ₂ ⊢ e₁ ⊗ e₂ ∶ T ⊗⟨ d ⟩ U ∣ ϵ₁

  T-Let : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ T ∣ ϵ →
    T ⸴ Γ ; join p/s (` zero) (𝐂.wk γ₂) ⊢ e₂ ∶ U ∣ ϵ →
    --------------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let e₁ `in e₂ ∶ U ∣ ϵ

  T-LetUnit : {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ `⊤ ∣ ϵ →
    Γ ; γ₂ ⊢ e₂ ∶ T  ∣ ϵ →
    -----------------------------
    Γ ; (γ₁ ; γ₂) ⊢ e₁ ; e₂ ∶ T ∣ ϵ

  T-LetPair : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    Γ ; γ₁ ⊢ e₁ ∶ T₁ ⊗⟨ d ⟩ T₂ ∣ ϵ →
    T₁ ⸴ T₂ ⸴ Γ ;
      join p/s (join d (` zero) (` suc zero))
               (𝐂.wk (𝐂.wk γ₂))
      ⊢ e₂ ∶ U ∣ ϵ →
    --------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `let⊗ e₁ `in e₂ ∶ U ∣ ϵ

  T-Inj : {i : Side} →
    Γ ; γ ⊢ e ∶ if i then T else U ∣ ϵ →
    ------------------------------------
    Γ ; γ ⊢ `inj i e ∶ T ⊕ U ∣ ϵ

  T-Case : (p/s : ParSeq) {γ₁ γ₂ : Struct n} →
    let γ₂′ = join p/s (` zero) (𝐂.wk γ₂) in
    Γ      ; γ₁  ⊢ e  ∶ T₁ ⊕ T₂ ∣ ϵ →
    T₁ ⸴ Γ ; γ₂′ ⊢ e₁ ∶ U       ∣ ϵ →
    T₂ ⸴ Γ ; γ₂′ ⊢ e₂ ∶ U       ∣ ϵ →
    ---------------------------------------------------
    Γ ; join p/s γ₁ γ₂ ⊢ `case e `of⟨ e₁ ; e₂ ⟩ ∶ U ∣ ϵ

  T-Conv :
    (T≃ : T ≃ U) →
    (ϵ≤ : ϵ₁ ≤ϵ ϵ₂) →
    Γ ; γ ⊢ e ∶ T ∣ ϵ₁ →
    -------------------
    Γ ; γ ⊢ e ∶ U ∣ ϵ₂

  T-Weaken :
    (γ≤ : Γ ∶ γ₁ ≼ γ₂) →
    Γ ; γ₁ ⊢ e ∶ T ∣ ϵ →
    --------------------
    Γ ; γ₂ ⊢ e ∶ T ∣ ϵ

subst-γ : γ₁ ≡ γ₂ → Γ ; γ₁ ⊢ e ∶ T ∣ ϵ → Γ ; γ₂ ⊢ e ∶ T ∣ ϵ
subst-γ refl x = x

subst-ϵ : ϵ₁ ≡ ϵ₂ → Γ ; γ ⊢ e ∶ T ∣ ϵ₁ → Γ ; γ ⊢ e ∶ T ∣ ϵ₂
subst-ϵ refl x = x

{-
weaken-ϵ : ϵ ≤ϵ ϵ′ → Γ ; γ ⊢ e ∶ T ∣ ϵ → Γ ; γ ⊢ e ∶ T ∣ ϵ′
weaken-ϵ ϵ≤ (T-Const c) = T-Const c
weaken-ϵ ϵ≤ (T-Var x T-eq) = T-Var x T-eq
weaken-ϵ ϵ≤ (T-Abs Γ-unr Γ-mob x) = T-Abs Γ-unr Γ-mob  x
weaken-ϵ ϵ≤ (T-AbsRec Γ-unr a-unr x) = T-AbsRec Γ-unr a-unr x
weaken-ϵ ϵ≤ (T-AppUnr a-unr ≤₁ ≤₂ ≤ₐ x y) =
  T-AppUnr a-unr (≤ϵ-trans ≤₁ ϵ≤) (≤ϵ-trans ≤₂ ϵ≤) (≤ϵ-trans ≤ₐ ϵ≤) x y
weaken-ϵ ϵ≤ (T-AppLin a-par ≤₁ ≤₂ ≤ₐ x y) =
  T-AppLin a-par (≤ϵ-trans ≤₁ ϵ≤) (≤ϵ-trans ≤₂ ϵ≤) (≤ϵ-trans ≤ₐ ϵ≤) x y
weaken-ϵ ϵ≤ (T-AppLeft aL ≤₂ ≤ₐ x y) =
  T-AppLeft aL (≤ϵ-trans ≤₂ ϵ≤) (≤ϵ-trans ≤ₐ ϵ≤) x y
weaken-ϵ ϵ≤ (T-AppRight aR ≤₁ ≤ₐ x y) =
  T-AppRight aR (≤ϵ-trans ≤₁ ϵ≤) (≤ϵ-trans ≤ₐ ϵ≤) x y
weaken-ϵ ϵ≤ (T-Pair p/s ≤₁ seq⇒p x y) =
  T-Pair p/s (≤ϵ-trans ≤₁ ϵ≤) seq⇒p x y
weaken-ϵ ϵ≤ (T-Let p/s ≤₁ ≤₂ x y) = {!!}
weaken-ϵ ϵ≤ (T-LetUnit p/s ≤₁ ≤₂ x y) = {!!}
weaken-ϵ ϵ≤ (T-LetPair p/s ≤₁ ≤₂ x y) = {!!}
weaken-ϵ ϵ≤ (T-Inj x) = {!!}
weaken-ϵ ϵ≤ (T-Case p/s ≤′ ≤₁ ≤₂ x y₁ y₂) = {!!}
weaken-ϵ ϵ≤ (T-Conv T≃ x) = {!!}
weaken-ϵ ϵ≤ (T-Weaken γ≤ x) = {!!}
-}

-- weaken-ϵ-→ : Arr.eff a ≤ϵ ϵ′ → Γ ; γ ⊢ e ∶ T ⟨ a ⟩→ U ∣ ϵ → Γ ; γ ⊢ e ∶ T ⟨ record a { eff = ϵ′ } ⟩→ U ∣ ϵ
-- weaken-ϵ-→ ≤ₐ x = {!!}

record TKit (K : Kit 𝓕) : Set₁ where
  private instance _ = K

  field
    𝓕[_;_⊢_∶_] : Ctx n → Struct n → 𝓕 n → 𝕋 → Set
    ⊢id/` : (x : 𝔽 n) → 𝓕[ Γ ; ` x ⊢ id/` x ∶ Γ x ]
    ⊢`/id : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → Γ ; γ ⊢ `/id x/t ∶ T ∣ ℙ
    ⊢wk : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ U ] → 𝓕[ T ⸴ Γ ; 𝐂.wk γ ⊢ wk x/t ∶ U ]
    ⊢𝓕-≗ : {x : 𝓕 n} → Γ₁ ≗ Γ₂ → 𝓕[ Γ₁ ; γ ⊢ x ∶ T ] → 𝓕[ Γ₂ ; γ ⊢ x ∶ T ]

  infix 4 _∶_⊢_⇒_

  record _∶_⊢_⇒_ (ϕ : m –[ K ]→ n) (σ : m 𝐂.→ₛ n) (Γ₁ : Ctx m) (Γ₂ : Ctx n) : Set where
    field
      _&_ : ∀ x → 𝓕[ Γ₂ ; σ x ⊢ ϕ x ∶ Γ₁ x ]
      &-unr : σ 𝐂.Preserves[ Unr ] Γ₁ ⇒ Γ₂
      &-mob : σ 𝐂.Preserves[ Mobile ] Γ₁ ⇒ Γ₂

  open _∶_⊢_⇒_ public

  ⊢⇒-≗ : {ϕ : m –[ K ]→ n} {σ : m 𝐂.→ₛ n} {Γ₁ Γ₁′ : Ctx m} {Γ₂ Γ₂′ : Ctx n} → Γ₁ ≗ Γ₁′ → Γ₂ ≗ Γ₂′ → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ∶ σ ⊢ Γ₁′ ⇒ Γ₂′
  ⊢⇒-≗ eq₁ eq₂ ⊢ϕ = record
    { _&_ = λ x → subst 𝓕[ _ ; _ ⊢ _ ∶_] (eq₁ x) (⊢𝓕-≗ eq₂ (⊢ϕ & x))
    ; &-unr = λ x → allCx-≗ eq₂ (&-unr ⊢ϕ (subst Unr (sym (eq₁ _)) x))
    ; &-mob = λ x → allCx-≗ eq₂ (&-mob ⊢ϕ (subst Mobile (sym (eq₁ _)) x))
    }

  ⊢id : {Γ : Ctx n} → idₖ ∶ 𝐂.idₛ ⊢ Γ ⇒ Γ
  ⊢id = record { _&_ = ⊢id/` ; &-unr = `_ ; &-mob = `_ }

  ⊢↑ : ∀ {ϕ : m –[ K ]→ n} {σ} → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ↑ ∶ σ 𝐂.↑ ⊢ T ⸴ Γ₁ ⇒ T ⸴ Γ₂
  ⊢↑ ⊢ϕ = record
    { _&_   = λ{ zero → ⊢id/` zero; (suc x) → ⊢wk (⊢ϕ & x) }
    ; &-unr = λ {x} → 𝐂.↑-preserves (&-unr ⊢ϕ) {x}
    ; &-mob = λ {x} → 𝐂.↑-preserves (&-mob ⊢ϕ) {x}
    }

  ⊢↑* : ∀ (Γ : Ctx m) {ϕ : n₁ –[ K ]→ n₂} {σ} → ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ → ϕ ↑* m ∶ σ 𝐂.↑* m ⊢ Γ ⸴* Γ₁ ⇒ Γ ⸴* Γ₂
  ⊢↑* {zero} Γ ⊢ϕ = ⊢ϕ
  ⊢↑* {suc m} Γ ⊢ϕ = ⊢⇒-≗ ⸴-⸴*-cons ⸴-⸴*-cons (⊢↑ (⊢↑* (Γ ∘ suc) ⊢ϕ))

  ⊢sub : {x/t : 𝓕 n} → 𝓕[ Γ ; γ ⊢ x/t ∶ T ] → (Unr T → UnrCx Γ γ) → (Mobile T → MobCx Γ γ) → ⦅ x/t ⦆ ∶ 𝐂.⦅ γ ⦆ ⊢ T ⸴ Γ ⇒ Γ
  ⊢sub ⊢x/t γ-unr γ-mob = record
    { _&_   = λ{ zero   → ⊢x/t ; (suc y) → ⊢id/` y }
    ; &-unr = λ{ {zero} → γ-unr; {suc y} → `_ }
    ; &-mob = λ{ {zero} → γ-mob; {suc y} → `_ }
    }

  ⊢weaken : (Γ : Ctx n) → weaken ∶ 𝐂.weaken ⊢ Γ ⇒ T ⸴ Γ
  ⊢weaken Γ = record { _&_ = ⊢wk ∘ ⊢id/` ; &-unr = `_ ; &-mob = `_ }

  ⊢weaken* : (Γ : Ctx m) (Γ′ : Ctx n) → weaken* m ∶ 𝐂.weaken* m ⊢ Γ′ ⇒ Γ ⸴* Γ′
  ⊢weaken* {m} Γ Γ′ = record
    { _&_   = go Γ
    ; &-unr = subst (UnrCx (Γ ⸴* Γ′)) (cong `_ (𝐂.weaken*~wkˡ m _) ■ sym (𝐂.weaken*~wkˡ m _)) ∘ 𝐂.wk*-preserves Γ {Γ′}
    ; &-mob = subst (MobCx (Γ ⸴* Γ′)) (cong `_ (𝐂.weaken*~wkˡ m _) ■ sym (𝐂.weaken*~wkˡ m _)) ∘ 𝐂.wk*-preserves Γ {Γ′}
    }
    where go : ∀ {m} (Γ : Ctx m) x → 𝓕[ Γ ⸴* Γ′ ; 𝐂.weaken* m x ⊢ weaken* m x ∶ Γ′ x ]
          go {zero}  Γ = ⊢id/`
          go {suc m} Γ = ⊢𝓕-≗ ⸴-⸴*-cons ∘ ⊢wk ∘ go (Γ ∘ suc)

infix 4 _∶_⊢[_]_⇒_

_∶_⊢[_]_⇒_ : ∀ {K : Kit 𝓕} → m –[ K ]→ n → m 𝐂.→ₛ n → TKit K → Ctx m → Ctx n → Set
ϕ ∶ σ ⊢[ TK ] Γ₁ ⇒ Γ₂ = ϕ ∶ σ ⊢ Γ₁ ⇒ Γ₂ where open TKit TK

open TKit ⦃ ... ⦄ public

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
_⊢⋯_ {γ = γ} {σ = σ} (T-Abs {a = a} Γ-unr Γ-mob x) ⊢ϕ =
  let open Fin.Patterns in
  let eq′ = join-⋯ (Arr.dir a) (` 0F) _
             ■ cong (join (Arr.dir a) (` 0F)) (sym (𝐂.⋯-↑-wk γ σ))
  in
  T-Abs (𝐂.allCx-⋯ (&-unr ⊢ϕ) ∘ Γ-unr) (𝐂.allCx-⋯ (&-mob ⊢ϕ) ∘ Γ-mob)
    $ subst-γ eq′
    $ x ⊢⋯ ⊢↑ ⊢ϕ
_⊢⋯_ {γ = γ} {σ = σ} (T-AbsRec Γ-unr a-unr x) ⊢ϕ =
  let open Fin.Patterns in
  let eq = cong 𝐂.wk (𝐂.⋯-↑-wk γ σ) ■ 𝐂.⋯-↑-wk (𝐂.wk γ) (σ 𝐂.↑) in
  T-AbsRec (𝐂.allCx-⋯ (&-unr ⊢ϕ) Γ-unr) a-unr
    $ subst-γ (cong (_ ∥_) (sym eq))
    $ x ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)
T-AppUnr   unr-a ≤ₐ x₁ x₂ ⊢⋯ ⊢ϕ = T-AppUnr   unr-a ≤ₐ (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
T-AppLin   lin-a ≤ₐ x₁ x₂ ⊢⋯ ⊢ϕ = T-AppLin   lin-a ≤ₐ (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
T-AppLeft  a-L   ≤ₐ x₁ x₂ ⊢⋯ ⊢ϕ = T-AppLeft  a-L   ≤ₐ (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
T-AppRight a-R   ≤ₐ x₁ x₂ ⊢⋯ ⊢ϕ = T-AppRight a-R   ≤ₐ (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
T-Pair p/s {γ₁} {γ₂}  seq→ℙ x₁ x₂ ⊢⋯ ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $
    T-Pair p/s seq→ℙ (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
_⊢⋯_ {σ = σ} (T-Let p/s {γ₁} {γ₂} x₁ x₂) ⊢ϕ =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (` 0F) (𝐂.wk γ₂) ■ cong (join p/s (` 0F)) (sym (𝐂.⋯-↑-wk γ₂ σ)) in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂))
    $ T-Let p/s (x₁ ⊢⋯ ⊢ϕ)
    $ subst-γ eq
    $ x₂ ⊢⋯ ⊢↑ ⊢ϕ
T-LetUnit {γ₁ = γ₁} {γ₂} x x₁ ⊢⋯ ⊢ϕ = T-LetUnit (x ⊢⋯ ⊢ϕ) (x₁ ⊢⋯ ⊢ϕ)
_⊢⋯_ {σ = σ} (T-LetPair {d = d} p/s {γ₁} {γ₂} x x₁) ⊢ϕ  =
  let open Fin.Patterns in
  let eq = join-⋯ p/s (join d (` 0F) (` 1F)) _
             ■ cong₂ (join p/s) (join-⋯ d _ _)
                     (sym (cong 𝐂.wk (𝐂.⋯-↑-wk γ₂ σ) ■ 𝐂.⋯-↑-wk (𝐂.wk γ₂) (σ 𝐂.↑)))
  in
  subst-γ (sym (join-⋯ p/s γ₁ γ₂))
    $ T-LetPair p/s (x ⊢⋯ ⊢ϕ)
    $ subst-γ eq
    $ x₁ ⊢⋯ ⊢↑ (⊢↑ ⊢ϕ)
T-Inj x ⊢⋯ ⊢ϕ = T-Inj (x ⊢⋯ ⊢ϕ)
_⊢⋯_ {σ = σ} (T-Case p/s {γ₁} {γ₂} x x₁ x₂) ⊢ϕ =
  subst-γ (sym (join-⋯ p/s γ₁ γ₂)) $ T-Case p/s (x ⊢⋯ ⊢ϕ)
    (subst-γ (join-⋯ p/s _ _ ■ cong (join p/s _) (sym (𝐂.⋯-↑-wk γ₂ σ))) (x₁ ⊢⋯ ⊢↑ ⊢ϕ))
    (subst-γ (join-⋯ p/s _ _ ■ cong (join p/s _) (sym (𝐂.⋯-↑-wk γ₂ σ))) (x₂ ⊢⋯ ⊢↑ ⊢ϕ))
T-Conv eq ϵ≤ x ⊢⋯ ⊢ϕ = T-Conv eq ϵ≤ (x ⊢⋯ ⊢ϕ)
T-Weaken γ≤ x ⊢⋯ ⊢ϕ = T-Weaken (𝐂.≼-⋯ (&-unr ⊢ϕ) γ≤) (x ⊢⋯ ⊢ϕ)

infixl 5 _⊢≗_

_⊢≗_ : Γ₁ ; γ ⊢ e ∶ T ∣ ϵ → Γ₁ ≗ Γ₂ → Γ₂ ; γ ⊢ e ∶ T ∣ ϵ
T-Const x ⊢≗ eq = T-Const x
T-Var x T-eq ⊢≗ eq = T-Var x (sym (eq _) ■ T-eq)
T-Abs Γ-unr Γ-mob x ⊢≗ eq =
  let open Fin.Patterns in
  T-Abs (allCx-≗ eq ∘ Γ-unr) (allCx-≗ eq ∘ Γ-mob) (x ⊢≗ λ{ 0F → refl; (suc x) → eq x })
T-AbsRec Γ-unr a-unr x ⊢≗ eq =
  let open Fin.Patterns in
  T-AbsRec (allCx-≗ eq Γ-unr) a-unr $ x ⊢≗ λ{ 0F → refl; 1F → refl; (suc (suc x)) → eq x }
T-AppUnr   a-unr ≤ₐ x₁ x₂ ⊢≗ eq = T-AppUnr   a-unr ≤ₐ (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-AppLin   a-lin ≤ₐ x₁ x₂ ⊢≗ eq = T-AppLin   a-lin ≤ₐ (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-AppLeft  aL    ≤ₐ x₁ x₂ ⊢≗ eq = T-AppLeft  aL    ≤ₐ (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-AppRight aR    ≤ₐ x₁ x₂ ⊢≗ eq = T-AppRight aR    ≤ₐ (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-Pair p/s seq⇒pure x₁ x₂ ⊢≗ eq = T-Pair p/s seq⇒pure (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-Let p/s x₁ x₂ ⊢≗ eq = T-Let p/s (x₁ ⊢≗ eq) (x₂ ⊢≗ λ{ zero → refl; (suc x) → eq x })
T-LetUnit x₁ x₂ ⊢≗ eq = T-LetUnit (x₁ ⊢≗ eq) (x₂ ⊢≗ eq)
T-LetPair p/s x₁ x₂ ⊢≗ eq =
  let open Fin.Patterns in
  T-LetPair p/s (x₁ ⊢≗ eq) $ x₂ ⊢≗ λ{ 0F → refl; 1F → refl; (suc (suc x)) → eq x }
T-Inj x ⊢≗ eq = T-Inj (x ⊢≗ eq)
T-Case {T₁ = T₁} {T₂ = T₂} p/s x x₁ x₂ ⊢≗ eq =
  let eq′ T = λ{ zero → refl; (suc x) → eq x } in
  T-Case p/s (x ⊢≗ eq) (x₁ ⊢≗ eq′ T₁) (x₂ ⊢≗ eq′ T₂)
T-Conv T≃ ϵ≤ x ⊢≗ eq = T-Conv T≃ ϵ≤ (x ⊢≗ eq)
T-Weaken γ≤ x ⊢≗ eq = T-Weaken (≼-≗ eq γ≤) (x ⊢≗ eq)

instance
  TKᵣ : TKit Kᵣ
  TKᵣ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → γ ≡ ` x × Γ x ≡ T
    ; ⊢id/` = λ x → refl , refl
    ; ⊢`/id = λ{ (refl , T-eq) → T-Var _ T-eq }
    ; ⊢wk   = λ{ (refl , T-eq) → refl , T-eq }
    ; ⊢𝓕-≗  = λ{ Γ-eq (γ-eq , T-eq) → γ-eq , (sym (Γ-eq _) ■ T-eq) }
    }

  TKₛ : TKit Kₛ
  TKₛ = record
    { 𝓕[_;_⊢_∶_] = λ Γ γ x T → Γ ; γ ⊢ x ∶ T ∣ ℙ
    ; ⊢id/` = λ x → T-Var _ refl
    ; ⊢`/id = λ x → x
    ; ⊢wk   = λ {_} {Γ} {γ} {T} {U} x → subst (_ ;_⊢ _ ∶ _ ∣ _) (𝐂.⋯-congᶜ γ λ _ → refl) $
                x ⊢⋯ ⊢weaken ⦃ TKᵣ ⦄ {T = U} Γ
    ; ⊢𝓕-≗  = λ Γ-eq x → x ⊢≗ Γ-eq
    }

open TKit TKᵣ using () renaming (⊢weaken to ⊢weakenᵣ) public
open TKit TKₛ using () renaming (⊢sub to ⊢subₛ) public

infixl 5 _⊢⋯ₛ_

_⊢⋯ₛ_ : ∀ {ϕ : m →ₖ n} {σ} → Γ₁ ; γ ⊢ e ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKₛ ] Γ₁ ⇒ Γ₂ → Γ₂ ; γ 𝐂.⋯ σ ⊢ e ⋯ ϕ ∶ T ∣ ϵ
_⊢⋯ₛ_ = _⊢⋯_ ⦃ TK = TKₛ ⦄

⊢swapᵣ : (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) {Γ : Ctx n} → swapᵣ m₁ m₂ ∶ `_ ∘ 𝐂.swapᵣ m₁ m₂ {n} ⊢[ TKᵣ ] (Γ₁ ⸴* Γ₂) ⸴* Γ ⇒ (Γ₂ ⸴* Γ₁) ⸴* Γ
⊢swapᵣ Γ₁ Γ₂ = record
  { _&_ = λ x → refl , ++-swapᵣ Γ₁ Γ₂ x
  ; &-unr = `_ ∘ subst Unr (sym (++-swapᵣ Γ₁ Γ₂ _))
  ; &-mob = `_ ∘ subst Mobile (sym (++-swapᵣ Γ₁ Γ₂ _))
  }

⊢assocSwapᵣ : (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) {Γ : Ctx n} →
  assocSwapᵣ m₁ m₂ ∶ `_ ∘ 𝐂.assocSwapᵣ m₁ m₂ {n} ⊢[ TKᵣ ] Γ₁ ⸴* (Γ₂ ⸴* Γ) ⇒ Γ₂ ⸴* (Γ₁ ⸴* Γ)
⊢assocSwapᵣ Γ₁ Γ₂ = record
  { _&_ = λ x → refl , ++-assocSwapᵣ Γ₁ Γ₂ x
  ; &-unr = `_ ∘ subst Unr (sym (++-assocSwapᵣ Γ₁ Γ₂ _))
  ; &-mob = `_ ∘ subst Mobile (sym (++-assocSwapᵣ Γ₁ Γ₂ _))
  }

inv-` : ∀ {x} → Γ ; γ ⊢ ` x ∶ T ∣ ϵ → T ≃ Γ x × Γ ∶ ` x ≼ γ
inv-` (T-Var x T-eq) = ≃-reflexive (sym T-eq) , ≼-refl refl
inv-` (T-Conv T≃ ϵ≤ x) = Π.map₁ (λ T≃′ → ≃-trans (≃-sym T≃) T≃′) (inv-` x)
inv-` (T-Weaken γ≤ x) = inv-` x .proj₁ , ≼-trans (inv-` x .proj₂) γ≤

inv-K : ∀ {c} → Γ ; γ ⊢ K c ∶ T ∣ ϵ → ∃[ U ] U ≃ T × Γ ∶ [] ≼ γ × ⊢ c ∶ U
inv-K (T-Const ⊢c) = _ , ≃-refl , ≼-∅ [] , ⊢c
inv-K (T-Conv T≃ ϵ≤ x) =
  let _ , U≃ , x′ = inv-K x in
  _ , ≃-trans U≃ T≃ , x′
inv-K (T-Weaken γ≤ x) =
  let _ , U≃ , ≤γ , x′ = inv-K x in
  _ , U≃ , ≼-trans ≤γ γ≤ , x′

postulate
  _⊢⋯⁻¹_ : {ϕ : m →ᵣ n} {σ : _} → Γ₂ ; γ ⊢ e ⋯ ϕ ∶ T ∣ ϵ → ϕ ∶ σ ⊢[ TKᵣ ] Γ₁ ⇒ Γ₂ →
    ∃[ γ′ ] Γ₂ ∶ γ′ 𝐂.⋯ σ ≼ γ × Γ₁ ; γ′ ⊢ e ∶ T ∣ ϵ

-- _⊢⋯⁻¹_ {e = ` _} x ⊢ϕ =
--   let T≃ , ≼γ = inv-` x in
--   _ , ≼-respˡ-≈ (≈-reflexive (sym (proj₁ (⊢ϕ & _)))) ≼γ
--     , T-Conv (≃-trans (≃-reflexive (sym (proj₂ (⊢ϕ & _)))) (≃-sym T≃)) ℙ≤ϵ (T-Var _ refl)
-- _⊢⋯⁻¹_ {e = K c} x ⊢ϕ =
--   let _ , T≃ , ≼γ , ⊢c = inv-K x in
--   _ , ≼γ , T-Conv T≃ ℙ≤ϵ (T-Const ⊢c)
-- _⊢⋯⁻¹_ {e = ƛ e} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = μ e} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = e · e₁} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = e ; e₁} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = e ⊗ e₁} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = `let e `in e₁} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = `let⊗ e `in e₁} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = `inj i e} x ⊢ϕ = {!!}
-- _⊢⋯⁻¹_ {e = `case e `of⟨ e₁ ; e₂ ⟩} x ⊢ϕ = {!!}
