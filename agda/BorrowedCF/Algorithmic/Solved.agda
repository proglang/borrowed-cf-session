{-# OPTIONS --rewriting #-}
module BorrowedCF.Algorithmic.Solved where

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Terms

import BorrowedCF.Types.Substitution as 𝐓

open Nat.Variables

data SolvedC : Const → Set where
  `unit : SolvedC `unit
  `fork : SolvedC `fork
  `send : SolvedC `send
  `recv : SolvedC `recv
  `drop : SolvedC `drop
  `acq  : SolvedC `acq
  `end  : SolvedC (`end p)
  `new  : SolvedTy s → SolvedC (`new s)
  `lsplit : SolvedTy s → SolvedC (`lsplit s)
  `rsplit : SolvedTy s → SolvedC (`rsplit s)

data SolvedTm {n} : Tm n → Set where
  `_ : (x : 𝔽 n) → SolvedTm (` x)
  K : ∀ {c} → SolvedC c → SolvedTm (K {n} c)
  ƛ : {e : Tm (1 + n)} → SolvedTm e → SolvedTm (ƛ e)
  μ : {e : Tm (1 + n)} → SolvedTm e → SolvedTm (μ e)
  _·_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ · e₂)
  _;_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ ; e₂)
  _⊗_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ ⊗ e₂)
  `let⊗_`in_ : {e₁ : Tm n} {e₂ : Tm (2 + n)} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (`let⊗ e₁ `in e₂)
  `inj : {i : Side} {e : Tm n} → SolvedTm e → SolvedTm (`inj i e)
  `case_`of⟨_;_⟩ : {e : Tm n} {e₁ e₂ : Tm (1 + n)} → SolvedTm e → SolvedTm e₁ → SolvedTm e₂ → SolvedTm `case e `of⟨ e₁ ; e₂ ⟩
  -- `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n


Sub = ℕ → 𝕊 0

variable σ σ₁ σ₂ : Sub

subTy : ∀ {κ x} → Ty κ x → Sub → Ty κ x
subTy ⟨ s ⟩ σ = ⟨ subTy s σ ⟩
subTy `⊤ σ = `⊤
subTy (t ⟨ a ⟩→ u) σ = subTy t σ ⟨ a ⟩→ subTy u σ
subTy (t ⊗⟨ d ⟩ u) σ = subTy t σ ⊗⟨ d ⟩ subTy u σ
subTy (t ⊕ u) σ = subTy t σ ⊕ subTy u σ
subTy (` x) σ = ` x
subTy (end p) σ = end p
subTy (msg p t) σ = msg p (subTy t σ)
subTy (brn p s₁ s₂) σ = brn p (subTy s₁ σ) (subTy s₂ σ)
subTy (mu s) σ = mu (subTy s σ)
subTy (s₁ ; s₂) σ = subTy s₁ σ ; subTy s₂ σ
subTy skip σ = skip
subTy ret σ = ret
subTy acq σ = acq
subTy (`` x) σ = σ x 𝐓.⋯ᵣ λ()

subTy-solved : ∀ {κ x} {t : Ty κ x} → SolvedTy t → SolvedTy (subTy t σ)
subTy-solved ⟨ x ⟩ = ⟨ subTy-solved x ⟩
subTy-solved `⊤ = `⊤
subTy-solved (x ⟨ a ⟩→ x₁) = subTy-solved x ⟨ a ⟩→ subTy-solved x₁
subTy-solved (x ⊗⟨ d ⟩ x₁) = subTy-solved x ⊗⟨ d ⟩ subTy-solved x₁
subTy-solved (x ⊕ x₁) = subTy-solved x ⊕ subTy-solved x₁
subTy-solved (` x) = ` x
subTy-solved end = end
subTy-solved (msg x) = msg (subTy-solved x)
subTy-solved (brn x x₁) = brn (subTy-solved x) (subTy-solved x₁)
subTy-solved (mu x) = mu (subTy-solved x)
subTy-solved (x ; x₁) = subTy-solved x ; subTy-solved x₁
subTy-solved skip = skip
subTy-solved acq = acq
subTy-solved ret = ret

subTy-id : ∀ {κ x} {t : Ty κ x} → SolvedTy t → subTy t σ ≡ t
subTy-id ⟨ t ⟩ = cong ⟨_⟩ (subTy-id t)
subTy-id `⊤ = refl
subTy-id (t ⟨ a ⟩→ t₁) = cong₂ _⟨ a ⟩→_ (subTy-id t) (subTy-id t₁)
subTy-id (t ⊗⟨ d ⟩ t₁) = cong₂ _⊗⟨ d ⟩_ (subTy-id t) (subTy-id t₁)
subTy-id (t ⊕ t₁) = cong₂ _⊕_ (subTy-id t) (subTy-id t₁)
subTy-id (` x) = refl
subTy-id end = refl
subTy-id (msg t) = cong (msg _) (subTy-id t)
subTy-id (brn t t₁) = cong₂ (brn _) (subTy-id t) (subTy-id t₁)
subTy-id (mu t) = cong mu (subTy-id t)
subTy-id (t ; t₁) = cong₂ _;_ (subTy-id t) (subTy-id t₁)
subTy-id skip = refl
subTy-id acq = refl
subTy-id ret = refl

subTy-dual : (s : 𝕊 n) → SolvedTy s ⊎ (∀ i → dual (σ i) ≡ σ i) → dual (subTy s σ) ≡ subTy (dual s) σ
subTy-dual (` x) h = refl
subTy-dual (end p) h = refl
subTy-dual (msg p t) h = refl
subTy-dual (brn p s₁ s₂) h = cong₂ (brn _) (subTy-dual s₁ (Sum.map₁ (λ{ (brn x _) → x }) h)) (subTy-dual s₂ (Sum.map₁ (λ{ (brn _ x) → x }) h))
subTy-dual (mu s) h = cong mu (subTy-dual s (Sum.map₁ (λ{ (mu x) → x }) h))
subTy-dual (s₁ ; s₂) h = cong₂ _;_ (subTy-dual s₁ (Sum.map₁ (λ{ (x ; _) → x}) h)) (subTy-dual s₂ (Sum.map₁ (λ{ (_ ; x) → x }) h))
subTy-dual skip h = refl
subTy-dual ret h = refl
subTy-dual acq h = refl
subTy-dual {σ = σ} (`` α) (inj₂ y) =
  let open ≡-Reasoning in
  dual (σ α 𝐓.⋯ λ ())    ≡⟨ 𝐓.⋯ᵣ-dual (σ α) ⟩
  dual (σ α) 𝐓.⋯ (λ ())  ≡⟨ cong (𝐓._⋯ (λ ())) (y α) ⟩
  σ α 𝐓.⋯ (λ ()) ∎

subTy-skips : Skips s → Skips (subTy s σ)
subTy-skips skip = skip
subTy-skips (s ; s₁) = subTy-skips s ; subTy-skips s₁
subTy-skips (mu s) = mu (subTy-skips s)

subTy-unr : Unr T → Unr (subTy T σ)
subTy-unr `⊤ = `⊤
subTy-unr (U ⊗ U₁) = subTy-unr U ⊗ subTy-unr U₁
subTy-unr (U ⊕ U₁) = subTy-unr U ⊕ subTy-unr U₁
subTy-unr (arr x) = arr x
subTy-unr ⟨ x ⟩ = ⟨ subTy-skips x ⟩

subConst : Const → Sub → Const
subConst `unit σ = `unit
subConst `fork σ = `fork
subConst `send σ = `send
subConst `recv σ = `recv
subConst `drop σ = `drop
subConst `acq σ = `acq
subConst (`end p) σ = `end p
subConst (`new s) σ = `new (subTy s σ)
subConst (`lsplit s) σ = `lsplit (subTy s σ)
subConst (`rsplit s) σ = `rsplit (subTy s σ)

subConst-solved : {c : Const} → SolvedC c → SolvedC (subConst c σ)
subConst-solved `unit = `unit
subConst-solved `fork = `fork
subConst-solved `send = `send
subConst-solved `recv = `recv
subConst-solved `drop = `drop
subConst-solved `acq = `acq
subConst-solved `end = `end
subConst-solved (`new s) = `new (subTy-solved s)
subConst-solved (`lsplit s) = `lsplit (subTy-solved s)
subConst-solved (`rsplit s) = `rsplit (subTy-solved s)

subConst-id : {c : Const} → SolvedC c → subConst c σ ≡ c
subConst-id `unit = refl
subConst-id `fork = refl
subConst-id `send = refl
subConst-id `recv = refl
subConst-id `drop = refl
subConst-id `acq = refl
subConst-id `end = refl
subConst-id (`new s) = cong `new (subTy-id s)
subConst-id (`lsplit s) = cong `lsplit (subTy-id s)
subConst-id (`rsplit s) = cong `rsplit (subTy-id s)

subConst-⊢ : ∀ {c} → ⊢ c ∶ T → ⊢ subConst c σ ∶ subTy T σ
subConst-⊢ `unit = `unit
subConst-⊢ `fork = `fork
subConst-⊢ (`new {s}) = {!⊢_∶_.`new!}
subConst-⊢ (`lsplit s s′) = `lsplit (subTy s _) (subTy s′ _)
subConst-⊢ (`rsplit s s′) = `rsplit (subTy s _) (subTy s′ _)
subConst-⊢ `drop = `drop
subConst-⊢ `acq = `acq
subConst-⊢ (`send x) = {!!}
subConst-⊢ (`recv x) = {!!}
subConst-⊢ `end = `end

subTm : Tm n → Sub → Tm n
subTm (` x) σ = ` x
subTm (K c) σ = K (subConst c σ)
subTm (ƛ e) σ = ƛ (subTm e σ)
subTm (μ e) σ = μ (subTm e σ)
subTm (e · e₁) σ = subTm e σ · subTm e₁ σ
subTm (e ; e₁) σ = subTm e σ ; subTm e₁ σ
subTm (e ⊗ e₁) σ = subTm e σ ⊗ subTm e₁ σ
subTm (`let e `in e₁) σ = `let subTm e σ `in subTm e₁ σ
subTm (`let⊗ e `in e₁) σ = `let⊗ subTm e σ `in subTm e₁ σ
subTm (`inj i e) σ = `inj i (subTm e σ)
subTm `case e `of⟨ e₁ ; e₂ ⟩ σ = `case subTm e σ `of⟨ subTm e₁ σ ; subTm e₂ σ ⟩

subTm-solved : {e : Tm n} → SolvedTm e → SolvedTm (subTm e σ)
subTm-solved (` x) = ` x
subTm-solved (K c) = K (subConst-solved c)
subTm-solved (ƛ e) = ƛ (subTm-solved e)
subTm-solved (μ e) = μ (subTm-solved e)
subTm-solved (e · e₁) = subTm-solved e · subTm-solved e₁
subTm-solved (e ; e₁) = subTm-solved e ; subTm-solved e₁
subTm-solved (e ⊗ e₁) = subTm-solved e ⊗ subTm-solved e₁
subTm-solved (`let⊗ e `in e₁) = `let⊗ subTm-solved e `in subTm-solved e₁
subTm-solved (`inj e) = `inj (subTm-solved e)
subTm-solved `case e `of⟨ e₁ ; e₂ ⟩ = `case subTm-solved e `of⟨ subTm-solved e₁ ; subTm-solved e₂ ⟩

subTm-id : {e : Tm n} → SolvedTm e → subTm e σ ≡ e
subTm-id (` x) = refl
subTm-id (K c) = cong K (subConst-id c)
subTm-id (ƛ e) = cong ƛ (subTm-id e)
subTm-id (μ e) = cong μ (subTm-id e)
subTm-id (e · e₁) = cong₂ _·_ (subTm-id e) (subTm-id e₁)
subTm-id (e ; e₁) = cong₂ _;_ (subTm-id e) (subTm-id e₁)
subTm-id (e ⊗ e₁) = cong₂ _⊗_ (subTm-id e) (subTm-id e₁)
subTm-id (`let⊗ e `in e₁) = cong₂ `let⊗_`in_ (subTm-id e) (subTm-id e₁)
subTm-id (`inj e) = cong (`inj _) (subTm-id e)
subTm-id {σ = σ} `case e `of⟨ e₁ ; e₂ ⟩ rewrite subTm-id {σ = σ} e = cong₂ `case _ `of⟨_;_⟩ (subTm-id e₁) (subTm-id e₂)
