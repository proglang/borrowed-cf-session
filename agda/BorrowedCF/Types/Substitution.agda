{-# OPTIONS --rewriting #-}
module BorrowedCF.Types.Substitution where

open import BorrowedCF.Prelude
open import BorrowedCF.FinKits as Kits hiding (Syntax) public

open import BorrowedCF.Types.Syntax

open Nat.Variables

open module Syntax = Kits.Syntax record
  { Tm = 𝕊
  ; `_ = `_
  ; `-injective = λ{ refl → refl }
  }
  hiding (Traversal; Tm; `_)
  renaming (id to idₖ)
  public

infixl 5 _⋯_

_⋯_ : ⦃ K : Kit 𝓕 ⦄ → 𝕊 m → m –[ K ]→ n → 𝕊 n
(` x) ⋯ ϕ = `/id (ϕ x)
end p ⋯ ϕ = end p
msg p t ⋯ ϕ = msg p t
brn p s₁ s₂ ⋯ ϕ = brn p (s₁ ⋯ ϕ) (s₂ ⋯ ϕ)
mu s ⋯ ϕ = mu (s ⋯ ϕ ↑)
(s₁ ; s₂) ⋯ ϕ = (s₁ ⋯ ϕ) ; (s₂ ⋯ ϕ)
skip ⋯ ϕ = skip
ret ⋯ ϕ = ret
acq ⋯ ϕ = acq
(`` x) ⋯ ϕ = `` x

⋯-id : ⦃ K : Kit 𝓕 ⦄ (s : 𝕊 n) {ϕ : n –[ K ]→ n} → ϕ ≗ idₖ → s ⋯ ϕ ≡ s
⋯-id (` x) eq = cong `/id (eq x) ■ `/`-is-` x
⋯-id (end p) eq = refl
⋯-id (msg p t) eq = refl
⋯-id (brn p s₁ s₂) eq = cong₂ (brn p) (⋯-id s₁ eq) (⋯-id s₂ eq)
⋯-id (mu s) eq = cong mu (⋯-id s (id↑ eq))
⋯-id (s₁ ; s₂) eq = cong₂ _;_ (⋯-id s₁ eq) (⋯-id s₂ eq)
⋯-id skip eq = refl
⋯-id ret eq = refl
⋯-id acq eq = refl
⋯-id (`` x) eq = refl

⋯-cong : ⦃ K : Kit 𝓕 ⦄ (s : 𝕊 m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → s ⋯ ϕ₁ ≡ s ⋯ ϕ₂
⋯-cong (` x) eq = cong `/id (eq x)
⋯-cong (end p) eq = refl
⋯-cong (msg p t) eq = refl
⋯-cong (brn p s₁ s₂) eq = cong₂ (brn p) (⋯-cong s₁ eq) (⋯-cong s₂ eq)
⋯-cong (mu s) eq = cong mu (⋯-cong s (eq ~↑))
⋯-cong (s₁ ; s₂) eq = cong₂ _;_ (⋯-cong s₁ eq) (⋯-cong s₂ eq)
⋯-cong skip eq = refl
⋯-cong ret eq = refl
⋯-cong acq eq = refl
⋯-cong (`` x) eq = refl

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
  (s : 𝕊 n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) → s ⋯ ϕ₁ ⋯ ϕ₂ ≡ s ⋯ ϕ₁ ·ₖ ϕ₂
fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ x) ϕ₂)
fusion (end p) ϕ₁ ϕ₂ = refl
fusion (msg p t) ϕ₁ ϕ₂ = refl
fusion (brn p s₁ s₂) ϕ₁ ϕ₂ = cong₂ (brn p) (fusion s₁ ϕ₁ ϕ₂) (fusion s₂ ϕ₁ ϕ₂)
fusion (mu s) ϕ₁ ϕ₂ = cong mu $
  fusion s (ϕ₁ ↑) (ϕ₂ ↑) ■ ⋯-cong s (sym ∘ dist-↑-· ϕ₁ ϕ₂)
fusion (s₁ ; s₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion s₁ ϕ₁ ϕ₂) (fusion s₂ ϕ₁ ϕ₂)
fusion skip ϕ₁ ϕ₂ = refl
fusion ret ϕ₁ ϕ₂ = refl
fusion acq ϕ₁ ϕ₂ = refl
fusion (`` x) ϕ₁ ϕ₂ = refl

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

skips-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → Skips s → Skips (s ⋯ ϕ)
skips-⋯ skip = skip
skips-⋯ (x₁ ; x₂) = skips-⋯ x₁ ; skips-⋯ x₂
skips-⋯ (mu x) = mu (skips-⋯ x)

infix 4 𝓖_·_

data 𝓖_·_ (x : 𝔽 n) : 𝕊 n → Set where
  `_  : ∀ {y : 𝔽 n} → .(x ≢ y) → 𝓖 x · ` y
  end : 𝓖 x · end p
  msg : 𝓖 x · msg p T
  brn : 𝓖 x · brn p s₁ s₂
  mu  : 𝓖 suc x · s → 𝓖 x · mu s
  _;- : 𝓖 x · s₁ → 𝓖 x · s₁ ; s₂
  _;_ : Skips s₁ → 𝓖 x · s₂ → 𝓖 x · s₁ ; s₂
  acq : 𝓖 x · acq
  ret : 𝓖 x · ret

  ``_ : (y : ℕ) → 𝓖 x · `` y

𝓖₀ : Pred (𝕊 (1 + n)) _
𝓖₀ = 𝓖 zero ·_

infix 4 ⊢_

data ⊢_ : ∀ {κ x} → Ty κ x → Set where
  ⟨_⟩ : ⊢ s → ⊢ ⟨ s ⟩
  `⊤  : ⊢ `⊤
  _⟨_⟩→_ : ⊢ T → ⊢ U → ⊢ T ⟨ a ⟩→ U
  _⊗⟨_⟩_ : ⊢ T → ⊢ U → ⊢ T ⊗⟨ d ⟩ U

  `_  : (x : 𝔽 n) → ⊢ ` x
  end : ⊢ end {n} p
  msg : ⊢ T → ⊢ msg {n} p T
  brn : ⊢ s₁ → ⊢ s₂ → ⊢ brn p s₁ s₂
  mu  : 𝓖₀ s → ⊢ s → ⊢ mu s
  _;_ : ⊢ s₁ → ⊢ s₂ → ⊢ s₁ ; s₂
  skip : ⊢ skip {n}
  ret : ⊢ ret {n}
  acq : ⊢ acq {n}

  ``_ : (x : ℕ) → ⊢ ``_ {n} x

open module Typing = Types.Typing record { ⊢_ = ⊢_ ; ⊢` = `_ }
  hiding (TTraversal; ⊢_; ⊢`)
  public

𝓖-wk* : ∀ m {x : 𝔽 n} {t : 𝕊 (m + n)} →
  𝓖 weaken* m x          · t →
  𝓖 weaken* m (weaken x) · t ⋯ weakenᵣ ↑* m
𝓖-wk* m end = end
𝓖-wk* m msg = msg
𝓖-wk* m brn = brn
𝓖-wk* m acq = acq
𝓖-wk* m ret = ret
𝓖-wk* m (g ;-) = (𝓖-wk* m g) ;-
𝓖-wk* m (x ; g) = skips-⋯ x ; 𝓖-wk* m g
𝓖-wk* m (`` y) = `` y
𝓖-wk* m (mu g) = mu (𝓖-wk* (suc m) g)
𝓖-wk* zero (` x≢y) = ` λ{ refl → x≢y refl }
𝓖-wk* (suc m) (`_ {zero} x≢y) = ` λ()
𝓖-wk* (suc m) (`_ {suc y} x≢y)
  with ` x≢y′ ← 𝓖-wk* m (` λ{ refl → x≢y refl })
  = ` λ{ eq → x≢y′ (Fin.suc-injective eq) }

𝓖-wk : {x : 𝔽 n} → 𝓖 x · s → 𝓖 suc x · wk s
𝓖-wk = 𝓖-wk* 0

𝓖₀-↑wk : ∀ m (s : 𝕊 (m + n)) → 𝓖 weaken* m zero · s ⋯ weakenᵣ ↑* m
𝓖₀-↑wk m (` x) = {!!}
𝓖₀-↑wk m (end p) = end
𝓖₀-↑wk m (msg p t) = msg
𝓖₀-↑wk m (brn p s₁ s₂) = brn
𝓖₀-↑wk m (mu s) = {!!}
𝓖₀-↑wk m (s₁ ; s₂) = {!!}
𝓖₀-↑wk m skip = {!!}
𝓖₀-↑wk m ret = ret
𝓖₀-↑wk m acq = acq
𝓖₀-↑wk m (`` x) = `` x

𝓖-⋯ : ∀ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
         ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K Kₛ Kₛ ⦄
         {ϕ : m –[ K ]→ n} {x y} →
       𝓖 x · s →
       `/id (ϕ x) ≡ ` y →
       (∀ z → .(x ≢ z) → 𝓖 y · `/id (ϕ z)) →
       𝓖 y · s ⋯ ϕ
𝓖-⋯ (` x≢) eq ∀𝓖 = ∀𝓖 _ x≢
𝓖-⋯ end eq ∀𝓖 = end
𝓖-⋯ msg eq ∀𝓖 = msg
𝓖-⋯ brn eq ∀𝓖 = brn
𝓖-⋯ acq _ _ = acq
𝓖-⋯ ret _ _ = ret
𝓖-⋯ (`` y) _ _ = `` y
𝓖-⋯ ⦃ K ⦄ (mu x) eq ∀𝓖 = mu $ 𝓖-⋯ x (sym (wk-`/id _) ■ cong wk eq) λ where
  zero    x≢ → subst (𝓖 _ ·_) (sym (`/`-is-` ⦃ K ⦄ zero)) (` λ())
  (suc x) x≢ → subst (𝓖 _ ·_) (wk-`/id _) (𝓖-wk (∀𝓖 x λ{ refl → x≢ refl }))
𝓖-⋯ (x ;-) eq ∀𝓖 = 𝓖-⋯ x eq ∀𝓖 ;-
𝓖-⋯ (x₁ ; x₂) eq ∀𝓖 = (skips-⋯ x₁) ; (𝓖-⋯ x₂ eq ∀𝓖)

𝓖-⋯↑ : ∀ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
         ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K Kₛ Kₛ ⦄
         {ϕ : m –[ K ]→ n} →
       𝓖₀ s → 𝓖₀ (s ⋯ ϕ ↑)
𝓖-⋯↑ ⦃ K ⦄ x = 𝓖-⋯ x (`/`-is-` ⦃ K ⦄ _) λ where
  zero z≢0 → ⊥-elim-irr (z≢0 refl)
  (suc z) z≢0 → subst (𝓖 _ ·_) refl {!!}

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
       {s : 𝕊 m} {ϕ : m –[ K ]→ n} → ⊢ s → Φ⊢ ϕ → ⊢ s ⋯ ϕ
(` x) ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ x)
end ⊢⋯ ⊢ϕ = end
msg x ⊢⋯ ⊢ϕ = msg x
brn x₁ x₂ ⊢⋯ ⊢ϕ = brn (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
mu g x ⊢⋯ ⊢ϕ = mu {!!} (x ⊢⋯ (⊢↑ ⊢ϕ))
(x₁ ; x₂) ⊢⋯ ⊢ϕ = (x₁ ⊢⋯ ⊢ϕ) ; (x₂ ⊢⋯ ⊢ϕ)
skip ⊢⋯ ⊢ϕ = skip
ret ⊢⋯ ⊢ϕ = ret
acq ⊢⋯ ⊢ϕ = acq
(`` x) ⊢⋯ ⊢ϕ = `` x

open module TTraversal = Typing.TTraversal record { _⊢⋯_ = {!!} }
  hiding (_⊢⋯_)
  public
