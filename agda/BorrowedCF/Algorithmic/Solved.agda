module BorrowedCF.Algorithmic.Solved where

open import Data.Bool.Properties
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (_◅_; _◅◅_) renaming (ε to refl)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Data.List.Relation.Unary.All as All using (All)

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Context.Base

import BorrowedCF.Types.Substitution as 𝐓

open Nat.Variables

variable σ σ₁ σ₂ : UV.Sub

Solving : UV.Sub → Set
Solving σ = ∀ u → SolvedTy (UV.ap σ u)

subTy : ∀ {κ x} → Ty κ x → UV.Sub → Ty κ x
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
subTy (`` α) σ = UV.ap σ α 𝐓.⋯ᵣ λ()

subTy-solved : ∀ {κ x} (t : Ty κ x) → Solving σ → SolvedTy (subTy t σ)
subTy-solved ⟨ s ⟩ Sσ = ⟨ subTy-solved s Sσ ⟩
subTy-solved `⊤ Sσ = `⊤
subTy-solved (t ⟨ a ⟩→ u) Sσ = subTy-solved t Sσ ⟨ a ⟩→ subTy-solved u Sσ
subTy-solved (t ⊗⟨ d ⟩ u) Sσ = subTy-solved t Sσ ⊗⟨ d ⟩ subTy-solved u Sσ
subTy-solved (t ⊕ u) Sσ = subTy-solved t Sσ ⊕ subTy-solved u Sσ
subTy-solved (` x) Sσ = ` x
subTy-solved (end p) Sσ = end
subTy-solved (msg p t) Sσ = msg (subTy-solved t Sσ)
subTy-solved (brn p s₁ s₂) Sσ = brn (subTy-solved s₁ Sσ) (subTy-solved s₂ Sσ)
subTy-solved (mu s) Sσ = mu (subTy-solved s Sσ)
subTy-solved (s₁ ; s₂) Sσ = subTy-solved s₁ Sσ ; subTy-solved s₂ Sσ
subTy-solved skip Sσ = skip
subTy-solved ret Sσ = ret
subTy-solved acq Sσ = acq
subTy-solved (`` α) Sσ = solved-⋯ (Sσ α) λ()

subTy-id : ∀ {κ x} {t : Ty κ x} → SolvedTy t → ∀ {σ} → subTy t σ ≡ t
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

subTy-dual : (s : 𝕊 n) → dual (subTy s σ) ≡ subTy (dual s) σ
subTy-dual (` x) = refl
subTy-dual (end p) = refl
subTy-dual (msg p t) = refl
subTy-dual (brn p s₁ s₂) = cong₂ (brn _) (subTy-dual s₁) (subTy-dual s₂)
subTy-dual (mu s) = cong mu (subTy-dual s)
subTy-dual (s₁ ; s₂) = cong₂ _;_ (subTy-dual s₁) (subTy-dual s₂)
subTy-dual skip = refl
subTy-dual ret = refl
subTy-dual acq = refl
subTy-dual {σ = σ} (`` α) = dual-⋯ᵣ (UV.ap σ α) ■ cong (𝐓._⋯ᵣ λ()) (UV.ap-dual/dual σ α)

module _ where
  open 𝐓

  subTy-⋯ᵣ : (s : 𝕊 m) {ρ : m →ᵣ n} → subTy s σ ⋯ᵣ ρ ≡ subTy (s ⋯ᵣ ρ) σ
  subTy-⋯ᵣ (` x) = refl
  subTy-⋯ᵣ (end p) = refl
  subTy-⋯ᵣ (msg p t) = refl
  subTy-⋯ᵣ (brn p s₁ s₂) = cong₂ (brn p) (subTy-⋯ᵣ s₁) (subTy-⋯ᵣ s₂)
  subTy-⋯ᵣ (mu s) = cong mu (subTy-⋯ᵣ s)
  subTy-⋯ᵣ (s₁ ; s₂) = cong₂ _;_ (subTy-⋯ᵣ s₁) (subTy-⋯ᵣ s₂)
  subTy-⋯ᵣ skip = refl
  subTy-⋯ᵣ ret = refl
  subTy-⋯ᵣ acq = refl
  subTy-⋯ᵣ {σ = σ} (`` α) = fusion (UV.ap σ α) _ _ ■ ⋯-cong (UV.ap σ α) λ()

  subTy-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ (s : 𝕊 m) {ϕ : m –[ K ]→ n} →
    subTy s σ ⋯ (λ x → subTy (`/id (ϕ x)) σ) ≡ subTy (s ⋯ ϕ) σ
  subTy-⋯ (` x) = refl
  subTy-⋯ (end p) = refl
  subTy-⋯ (msg p t) = refl
  subTy-⋯ (brn p s₁ s₂) = cong₂ (brn p) (subTy-⋯ s₁) (subTy-⋯ s₂)
  subTy-⋯ {σ = σ} ⦃ K ⦄ ⦃ W ⦄ (mu s) {ϕ} = cong mu $
    ⋯-cong (subTy s σ) (λ{ zero → cong (λ t → subTy t σ) (sym (`/`-is-` ⦃ K ⦄ zero))
                         ; (suc x) → subTy-⋯ᵣ (`/id (ϕ x)) ■ cong (λ t → subTy t σ) (wk-`/id ⦃ W ⦄ _)
                         })
      ■ subTy-⋯ s
  subTy-⋯ (s₁ ; s₂) = cong₂ _;_ (subTy-⋯ s₁) (subTy-⋯ s₂)
  subTy-⋯ skip = refl
  subTy-⋯ ret = refl
  subTy-⋯ acq = refl
  subTy-⋯ {σ = σ} ⦃ K ⦄ (`` α) =
    let open ≡-Reasoning in
    UV.ap σ α ⋯ _ ⋯ _    ≡⟨ fusion (UV.ap σ α) _ _ ⟩
    UV.ap σ α ⋯ _        ≡⟨ ⋯-cong (UV.ap σ α) (λ()) ⟩
    UV.ap σ α ⋯ _        ≡⟨ fusion (UV.ap σ α) _ _ ⟨
    UV.ap σ α ⋯ _ ⋯ idₖ  ≡⟨ ⋯-id ⦃ Kₛ ⦄ (UV.ap σ α ⋯ᵣ λ()) (λ x → refl) ⟩
    UV.ap σ α ⋯ _ ∎

  subTy-unfold : (s : 𝕊 (suc n)) → unfold (subTy s σ) ≡ subTy (unfold s) σ
  subTy-unfold {σ = σ} s = ⋯-cong (subTy s σ) (λ{ zero → refl ; (suc x) → refl }) ■ subTy-⋯ s

subTy-≃ : ∀ {κ x} {a b : Ty κ x} → a ≃ b → subTy a σ ≃ subTy b σ
subTy-≃ {σ = σ} {𝕤} refl = refl
subTy-≃ {σ = σ} {𝕤} (x ◅ xs) = go x ◅ subTy-≃ xs where
  goF : ∀ {s₁ s₂ : 𝕊 _} → s₁ ≃𝕊 s₂ → subTy s₁ σ ≃𝕊 subTy s₂ σ
  go  : ∀ {s₁ s₂ : 𝕊 _} → Sym.SymClosure _≃𝕊_ s₁ s₂ → Sym.SymClosure _≃𝕊_ (subTy s₁ σ) (subTy s₂ σ)
  go (fwd y) = fwd (goF y)
  go (bwd y) = bwd (goF y)
  goF (≃𝕊-;₁ eq) = ≃𝕊-;₁ (goF eq)
  goF (≃𝕊-;₂ eq) = ≃𝕊-;₂ (goF eq)
  goF ≃𝕊-skipˡ = ≃𝕊-skipˡ
  goF ≃𝕊-skipʳ = ≃𝕊-skipʳ
  goF ≃𝕊-assoc = ≃𝕊-assoc
  goF ≃𝕊-distr = ≃𝕊-distr
  goF {s₁ = mu s} ≃𝕊-μ = subst (mu (subTy s σ) ≃𝕊_) (subTy-unfold s) ≃𝕊-μ
  goF (≃𝕊-msg eq) = ≃𝕊-msg (subTy-≃ eq)
  goF (≃𝕊-brn₁ eq) = ≃𝕊-brn₁ (goF eq)
  goF (≃𝕊-brn₂ eq) = ≃𝕊-brn₂ (goF eq)
subTy-≃ {σ = σ} {𝕥} `⊤ = `⊤
subTy-≃ {σ = σ} {𝕥} (eq ⊗ eq₁) = subTy-≃ eq ⊗ subTy-≃ eq₁
subTy-≃ {σ = σ} {𝕥} (eq ⊕ eq₁) = subTy-≃ eq ⊕ subTy-≃ eq₁
subTy-≃ {σ = σ} {𝕥} (eq `→ eq₁) = subTy-≃ eq `→ subTy-≃ eq₁
subTy-≃ {σ = σ} {𝕥} ⟨ eq ⟩ = ⟨ subTy-≃ eq ⟩

subTy-skips : Skips s → Skips (subTy s σ)
subTy-skips skip = skip
subTy-skips (s ; s₁) = subTy-skips s ; subTy-skips s₁
subTy-skips (mu s) = mu (subTy-skips s)

subTy-skips⁻¹ : Skips (subTy s σ) → Skips s
subTy-skips⁻¹ {s = mu s} (mu x) = mu (subTy-skips⁻¹ x)
subTy-skips⁻¹ {s = s₁ ; s₂} (x₁ ; x₂) = subTy-skips⁻¹ x₁ ; subTy-skips⁻¹ x₂
subTy-skips⁻¹ {s = skip} x = x
subTy-skips⁻¹ {s = `` α} {σ = σ} x = contradiction (skips-⋯ᵣ⁻¹ x) (UV.ap-¬skips σ α)

subTy-unr : Unr T → Unr (subTy T σ)
subTy-unr `⊤ = `⊤
subTy-unr (U ⊗ U₁) = subTy-unr U ⊗ subTy-unr U₁
subTy-unr (U ⊕ U₁) = subTy-unr U ⊕ subTy-unr U₁
subTy-unr (arr x) = arr x

subTy-bounded : Bounded s → Bounded (subTy s σ)
subTy-bounded end = end
subTy-bounded ret = ret
subTy-bounded (b ;₁ sk) = subTy-bounded b ;₁ subTy-skips sk
subTy-bounded (-;₂ b) = -;₂ subTy-bounded b
subTy-bounded (mu x) = mu (subTy-bounded x)
subTy-bounded (brn x x₁) = brn (subTy-bounded x) (subTy-bounded x₁)

subTy-mobile : Mobile T → Mobile (subTy T σ)
subTy-mobile `⊤ = `⊤
subTy-mobile (arr x) = arr x
subTy-mobile (m₁ ⊗ m₂) = subTy-mobile m₁ ⊗ subTy-mobile m₂
subTy-mobile (m₁ ⊕ m₂) = subTy-mobile m₁ ⊕ subTy-mobile m₂
subTy-mobile ⟨ (s , Bs , eq) ⟩ = ⟨ (_ , subTy-bounded Bs , subTy-≃ eq) ⟩

subTy-new : New s → New (subTy s σ)
subTy-new `- = `-
subTy-new msg = msg
subTy-new (brn x x₁) = brn (subTy-new x) (subTy-new x₁)
subTy-new (mu x) = mu (subTy-new x)
subTy-new (x ; x₁) = subTy-new x ; subTy-new x₁
subTy-new skip = skip

open import BorrowedCF.Terms

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
  _·_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ ·⟨ d ⟩ e₂)
  _;_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ ; e₂)
  _⊗_ : {e₁ e₂ : Tm n} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (e₁ ⊗ e₂)
  `let⊗_`in_ : {e₁ : Tm n} {e₂ : Tm (2 + n)} → SolvedTm e₁ → SolvedTm e₂ → SolvedTm (`let⊗ e₁ `in e₂)
  `inj : {i : Side} {e : Tm n} → SolvedTm e → SolvedTm (`inj i e)
  `case_`of⟨_;_⟩ : {e : Tm n} {e₁ e₂ : Tm (1 + n)} → SolvedTm e → SolvedTm e₁ → SolvedTm e₂ → SolvedTm `case e `of⟨ e₁ ; e₂ ⟩
  -- `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n

subConst : Const → UV.Sub → Const
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
subConst (`select k) σ = `select k
subConst `branch σ = `branch
subConst `discard σ = `discard

subConst-solved : {c : Const} → SolvedC c → SolvedC (subConst c σ)
subConst-solved `unit = `unit
subConst-solved `fork = `fork
subConst-solved `send = `send
subConst-solved `recv = `recv
subConst-solved `drop = `drop
subConst-solved `acq = `acq
subConst-solved `end = `end
subConst-solved {σ} (`new s) rewrite subTy-id s {σ} = `new s
subConst-solved {σ} (`lsplit s) rewrite subTy-id s {σ} = `lsplit s
subConst-solved {σ} (`rsplit s) rewrite subTy-id s {σ} = `rsplit s

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
subConst-⊢ {σ = σ} (`new {s = s} N)
  rewrite sym (subTy-dual {σ = σ} s)
  = `new (subTy-new N)
subConst-⊢ (`lsplit s s′ ¬s′) = `lsplit (subTy s _) (subTy s′ _) (¬s′ ∘ subTy-skips⁻¹)
subConst-⊢ (`rsplit s s′ ¬s′) = `rsplit (subTy s _) (subTy s′ _) (¬s′ ∘ subTy-skips⁻¹)
-- subConst-⊢ (`lsplit ¬skipₛ s′) = `lsplit (¬skipₛ ∘ subTy-skips⁻¹) (subTy s′ _)
-- subConst-⊢ (`rsplit ¬skipₛ s′) = `rsplit (¬skipₛ ∘ subTy-skips⁻¹) (subTy s′ _)
subConst-⊢ `drop = `drop
subConst-⊢ `acq = `acq
subConst-⊢ (`send m) = `send (subTy-mobile m)
subConst-⊢ (`recv m) = `recv (subTy-mobile m)
subConst-⊢ {σ = σ} (`select {s₁} {s₂} {k})
  rewrite if-float (flip subTy σ) k {s₁} {s₂}
  = `select
subConst-⊢ `branch = `branch
subConst-⊢ `end = `end
subConst-⊢ `discard = `discard

subTm : Tm n → UV.Sub → Tm n
subTm (` x) σ = ` x
subTm (K c) σ = K (subConst c σ)
subTm (ƛ e) σ = ƛ (subTm e σ)
subTm (μ e) σ = μ (subTm e σ)
subTm (e ·⟨ d ⟩ e₁) σ = subTm e σ ·⟨ d ⟩ subTm e₁ σ
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
subTm-id (e · e₁) = cong₂ _·⟨ _ ⟩_ (subTm-id e) (subTm-id e₁)
subTm-id (e ; e₁) = cong₂ _;_ (subTm-id e) (subTm-id e₁)
subTm-id (e ⊗ e₁) = cong₂ _⊗_ (subTm-id e) (subTm-id e₁)
subTm-id (`let⊗ e `in e₁) = cong₂ `let⊗_`in_ (subTm-id e) (subTm-id e₁)
subTm-id (`inj e) = cong (`inj _) (subTm-id e)
subTm-id {σ = σ} `case e `of⟨ e₁ ; e₂ ⟩ rewrite subTm-id {σ = σ} e = cong₂ `case _ `of⟨_;_⟩ (subTm-id e₁) (subTm-id e₂)

subCtx : Ctx n → UV.Sub → Ctx n
subCtx Γ σ k = subTy (Γ k) σ

SolvedCst : Constraint → UV.Sub → Set
SolvedCst (C-Eq t u) σ = subTy t σ ≃ subTy u σ
SolvedCst (C-Mob t) σ = Mobile (subTy t σ)

SolvedΔ : CSet → UV.Sub → Set
SolvedΔ Δ σ = flip All Δ (λ C → SolvedCst C σ)

SolvedΓ : Ctx n → UV.Sub → Set
SolvedΓ Γ σ = ∀ x →
  SolvedTy (subTy (Γ x) σ)

solved-⸴ : SolvedTy (subTy T σ) → SolvedΓ Γ σ → SolvedΓ (T ⸴ Γ) σ
solved-⸴ ST SΓ zero = ST
solved-⸴ ST SΓ (suc x) = SΓ x
