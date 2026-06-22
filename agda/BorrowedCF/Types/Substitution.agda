module BorrowedCF.Types.Substitution where

open import BorrowedCF.Prelude
open import BorrowedCF.FinKits as Kits hiding (Syntax) public

open import BorrowedCF.Types.Syntax

open Nat.Variables
open Nat using (_≤_; z≤n; s≤s)

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
`` α ⋯ ϕ = `` α

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
⋯-id (`` α) eq = refl

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
⋯-cong (`` α) eq = refl

open module Traversal = Syntax.Traversal record
  { _⋯_ = _⋯_
  ; ⋯-var = λ x ϕ → refl
  ; ⋯-id = ⋯-id
  ; ⋯-cong = ⋯-cong
  }
  hiding (_⋯_; ⋯-id; ⋯-cong; CTraversal)
  public

dual-⋯ᵣ : (s : 𝕊 m) {ϕ : m →ᵣ n} → dual (s ⋯ ϕ) ≡ dual s ⋯ ϕ
dual-⋯ᵣ (` x) = refl
dual-⋯ᵣ (end p) = refl
dual-⋯ᵣ (msg p t) = refl
dual-⋯ᵣ (brn p s₁ s₂) = cong₂ (brn _) (dual-⋯ᵣ s₁) (dual-⋯ᵣ s₂)
dual-⋯ᵣ (mu s) = cong mu (dual-⋯ᵣ s)
dual-⋯ᵣ (s₁ ; s₂) = cong₂ _;_ (dual-⋯ᵣ s₁) (dual-⋯ᵣ s₂)
dual-⋯ᵣ skip = refl
dual-⋯ᵣ ret = refl
dual-⋯ᵣ acq = refl
dual-⋯ᵣ (`` α) = refl

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
fusion (`` α) ϕ₁ ϕ₂ = refl

open module CTraversal = Traversal.CTraversal record { fusion = fusion }
  hiding (fusion)
  public

¬skips-`/` : (K : Kit 𝓕) {x : 𝔽 n} → ¬ Skips (`/id ⦃ K ⦄ (id/` ⦃ K ⦄ x))
¬skips-`/` K = ¬skips-` ∘ subst Skips (`/`-is-` ⦃ K ⦄ _)

skips-⋯ : ⦃ K : Kit 𝓕 ⦄ {ϕ : m –[ K ]→ n} → Skips s → Skips (s ⋯ ϕ)
skips-⋯ skip = skip
skips-⋯ (x₁ ; x₂) = skips-⋯ x₁ ; skips-⋯ x₂
skips-⋯ (mu x) = mu (skips-⋯ x)

skips-⋯ᵣ⁻¹ : {ϕ : m →ᵣ n} → Skips (s ⋯ ϕ) → Skips s
skips-⋯ᵣ⁻¹ {s = mu s} (mu x) = mu (skips-⋯ᵣ⁻¹ x)
skips-⋯ᵣ⁻¹ {s = _ ; _} (x ; y) = (skips-⋯ᵣ⁻¹ x) ; (skips-⋯ᵣ⁻¹ y)
skips-⋯ᵣ⁻¹ {s = skip} x = skip

skips-⋯⁻¹ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ {ϕ : m –[ K ]→ n} → Skips (s ⋯ ϕ) → (∀ z → ¬ Skips (`/id (ϕ z))) → Skips s
skips-⋯⁻¹ {s = ` x} Sϕ ∀S = contradiction Sϕ (∀S x)
skips-⋯⁻¹ {s = mu s} ⦃ K ⦄ (mu Sϕ) ∀S = Skips.mu $ skips-⋯⁻¹ Sϕ λ where
  zero    → ¬skips-`/` K
  (suc z) → ∀S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _))
skips-⋯⁻¹ {s = s₁ ; s₂} (Sϕ₁ ; Sϕ₂) ∀S = skips-⋯⁻¹ Sϕ₁ ∀S ; skips-⋯⁻¹ Sϕ₂ ∀S
skips-⋯⁻¹ {s = skip} Sϕ ∀S = skip

skips-irr-⋯ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ → Skips s → {ϕ₁ : m –[ K₁ ]→ n} {ϕ₂ : m –[ K₂ ]→ n} → s ⋯ ϕ₁ ≡ s ⋯ ϕ₂
skips-irr-⋯ skip = refl
skips-irr-⋯ (s₁ ; s₂) = cong₂ _;_ (skips-irr-⋯ s₁) (skips-irr-⋯ s₂)
skips-irr-⋯ (mu s) = cong mu (skips-irr-⋯ s)

open module Typing = Types.Typing record
  { ⊢_ = ⊢_
  ; ⊢` = `_
  ; Pϕ = λ s → ¬ Skips s
  ; Pϕ-` = λ _ → ¬skips-`
  ; Pϕ-⋯ᵣ = λ ¬S → ¬S ∘ skips-⋯ᵣ⁻¹
  }
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
𝓖-wk* m skip = skip
𝓖-wk* m ((¬s , g) ;-) = (¬s ∘ skips-⋯ᵣ⁻¹ , 𝓖-wk* m g) ;-
𝓖-wk* m (s ; g) = skips-⋯ s ; 𝓖-wk* m g
𝓖-wk* m ``- = ``-
𝓖-wk* m (mu g) = mu (𝓖-wk* (suc m) g)
𝓖-wk* zero (` x≢y) = ` λ{ refl → x≢y refl }
𝓖-wk* (suc m) (`_ {zero} x≢y) = ` λ()
𝓖-wk* (suc m) (`_ {suc y} x≢y)
  with ` x≢y′ ← 𝓖-wk* m (` λ{ refl → x≢y refl })
  = ` λ{ eq → x≢y′ (Fin.suc-injective eq) }

𝓖-wk : {x : 𝔽 n} → 𝓖 x · s → 𝓖 suc x · wk s
𝓖-wk = 𝓖-wk* 0

𝓖₀-↑wk : ∀ m (s : 𝕊 (m + n)) → 𝓖 weaken* m zero · s ⋯ weakenᵣ ↑* m
𝓖₀-↑wk m (end p) = end
𝓖₀-↑wk m (msg p t) = msg
𝓖₀-↑wk m (brn p s₁ s₂) = brn
𝓖₀-↑wk m (mu s) = mu (𝓖₀-↑wk (suc m) s)
𝓖₀-↑wk m (s₁ ; s₂) with skips? s₁
... | yes ss₁ = skips-⋯ ss₁ ; 𝓖₀-↑wk m s₂
... | no ¬ss₁ = (¬ss₁ ∘ skips-⋯ᵣ⁻¹ , 𝓖₀-↑wk m s₁) ;-
𝓖₀-↑wk m skip = skip
𝓖₀-↑wk m ret = ret
𝓖₀-↑wk m acq = acq
𝓖₀-↑wk m (`` α) = ``-
𝓖₀-↑wk zero (` x) = ` λ()
𝓖₀-↑wk (suc m) (` zero) = ` λ()
𝓖₀-↑wk (suc m) (` suc x) = 𝓖-wk (𝓖₀-↑wk m (` x))

𝓖₀-wk : (s : 𝕊 n) → 𝓖₀ (wk s)
𝓖₀-wk = 𝓖₀-↑wk 0

𝓖-⋯ : ∀ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
         ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K Kₛ Kₛ ⦄
         {ϕ : m –[ K ]→ n} {x y} →
       𝓖 x · s →
       `/id (ϕ x) ≡ ` y →
       (∀ z → .(x ≢ z) → 𝓖 y · `/id (ϕ z)) →
       (∀ z → ¬ Skips (`/id (ϕ z))) →
       𝓖 y · s ⋯ ϕ
𝓖-⋯ (` x≢) eq ∀𝓖 ∀¬s = ∀𝓖 _ x≢
𝓖-⋯ end eq ∀𝓖 ∀¬s = end
𝓖-⋯ msg eq ∀𝓖 ∀¬s = msg
𝓖-⋯ brn eq ∀𝓖 ∀¬s = brn
𝓖-⋯ acq _ _ _ = acq
𝓖-⋯ ret _ _ _ = ret
𝓖-⋯ skip _ _ _ = skip
𝓖-⋯ ``- _ _ _ = ``-
𝓖-⋯ ⦃ K ⦄ (mu x) eq ∀𝓖 ∀¬s = mu $ 𝓖-⋯ x (sym (wk-`/id _) ■ cong wk eq)
  (λ where zero    x≢ → subst (𝓖 _ ·_) (sym (`/`-is-` ⦃ K ⦄ zero)) (` λ())
           (suc z) x≢ → subst (𝓖 _ ·_) (wk-`/id _) (𝓖-wk (∀𝓖 z λ{ refl → x≢ refl })))
  (λ where zero    → ¬skips-`/` K
           (suc z) → ∀¬s z ∘ skips-⋯ᵣ⁻¹ {ϕ = weakenᵣ} ∘ subst Skips (sym (wk-`/id _)))
𝓖-⋯ ((¬s , x) ;-) eq ∀𝓖 ∀¬s = ((λ Sϕ → ¬s (skips-⋯⁻¹ Sϕ ∀¬s)) , 𝓖-⋯ x eq ∀𝓖 ∀¬s) ;-
𝓖-⋯ (x₁ ; x₂) eq ∀𝓖 ∀¬s = (skips-⋯ x₁) ; (𝓖-⋯ x₂ eq ∀𝓖 ∀¬s)

𝓖-⋯↑ : ∀ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
         ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K Kₛ Kₛ ⦄
         {ϕ : m –[ K ]→ n} →
       (∀ z → ¬ Skips (`/id (ϕ z))) →
       𝓖₀ s → 𝓖₀ (s ⋯ ϕ ↑)
𝓖-⋯↑ ⦃ K ⦄ {ϕ} ∀¬S x = 𝓖-⋯ x (`/`-is-` ⦃ K ⦄ _)
  (λ where zero z≢0 → ⊥-elim-irr (z≢0 refl)
           (suc z) z≢0 → subst (𝓖 _ ·_) (wk-`/id _) (𝓖₀-wk (`/id (ϕ z))))
  (λ where zero    → ¬skips-`/` K
           (suc z) → ∀¬S z ∘ skips-⋯ᵣ⁻¹ ∘ subst Skips (sym (wk-`/id _)))

_⊢⋯_ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
       {s : 𝕊 m} {ϕ : m –[ K ]→ n} → ⊢ s → Φ⊢ ϕ → ⊢ s ⋯ ϕ
(` x) ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ x .proj₁)
end ⊢⋯ ⊢ϕ = end
msg x ⊢⋯ ⊢ϕ = msg x
brn x₁ x₂ ⊢⋯ ⊢ϕ = brn (x₁ ⊢⋯ ⊢ϕ) (x₂ ⊢⋯ ⊢ϕ)
mu g x ⊢⋯ ⊢ϕ = mu (𝓖-⋯↑ (λ z → ⊢ϕ z .proj₂) g) (x ⊢⋯ (⊢↑ ⊢ϕ))
(x₁ ; x₂) ⊢⋯ ⊢ϕ = (x₁ ⊢⋯ ⊢ϕ) ; (x₂ ⊢⋯ ⊢ϕ)
skip ⊢⋯ ⊢ϕ = skip
ret ⊢⋯ ⊢ϕ = ret
acq ⊢⋯ ⊢ϕ = acq
``- ⊢⋯ ⊢ϕ = ``-

open module TTraversal = Typing.TTraversal record { _⊢⋯_ = _⊢⋯_ }
  hiding (_⊢⋯_)
  public

unfold : 𝕊 (suc n) → 𝕊 n
unfold s = s ⋯ ⦅ mu s ⦆ₛ

⊢unfold : 𝓖₀ s → ⊢ s → ⊢ unfold s
⊢unfold {s = s} g x with skips? s
... | yes skips-s = skips⇒⊢ (skips-⋯ skips-s)
... | no ¬skips-s = x ⊢⋯ ⊢⦅ mu g x , (λ{ (mu s) → ¬skips-s s }) ⦆ₛ

-- Renamings preserve the μPrefix unconditionally.
μPrefix-⋯ᵣ : (s : 𝕊 m) (ρ : m →ᵣ n) → μPrefix (s ⋯ ρ) ≡ μPrefix s
μPrefix-⋯ᵣ (` x) ρ = refl
μPrefix-⋯ᵣ (end p) ρ = refl
μPrefix-⋯ᵣ (msg p t) ρ = refl
μPrefix-⋯ᵣ (brn p s₁ s₂) ρ = refl
μPrefix-⋯ᵣ (mu s) ρ = cong suc (μPrefix-⋯ᵣ s (ρ ↑))
μPrefix-⋯ᵣ (s₁ ; s₂) ρ = refl
μPrefix-⋯ᵣ skip ρ = refl
μPrefix-⋯ᵣ ret ρ = refl
μPrefix-⋯ᵣ acq ρ = refl
μPrefix-⋯ᵣ (`` α) ρ = refl

-- The μPrefix never decreases through substitution.
μPrefix-≤-⋯ : ⦃ K : Kit 𝓕 ⦄ (s : 𝕊 m) {ϕ : m –[ K ]→ n} → μPrefix s ≤ μPrefix (s ⋯ ϕ)
μPrefix-≤-⋯ (` x) = z≤n
μPrefix-≤-⋯ (end p) = z≤n
μPrefix-≤-⋯ (msg p t) = z≤n
μPrefix-≤-⋯ (brn p s₁ s₂) = z≤n
μPrefix-≤-⋯ (mu s) = s≤s (μPrefix-≤-⋯ s)
μPrefix-≤-⋯ (s₁ ; s₂) = z≤n
μPrefix-≤-⋯ skip = z≤n
μPrefix-≤-⋯ ret = z≤n
μPrefix-≤-⋯ acq = z≤n
μPrefix-≤-⋯ (`` α) = z≤n

-- Any other kit preserves the μPrefix if it preserves variables.
μPrefix-⋯ : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ →
  (⊢s : ⊢ s) (ϕ : m –[ K ]→ n) →
  (∀ x → 𝓖 x · s ⊎ ∃[ y ] `/id ⦃ K ⦄ (ϕ x) ≡ ` y) →
  μPrefix (s ⋯ ϕ) ≡ μPrefix s
μPrefix-⋯ (` x) ϕ ∀𝓖⊎` with `/id (ϕ x) in ϕx≡
... | ` y = refl
... | end p = refl
... | msg p t = refl
... | brn p s₁ s₂ = refl
... | s₁ ; s₂ = refl
... | skip = refl
... | ret = refl
... | acq = refl
... | `` α = refl
... | mu s with ∀𝓖⊎` x
... | inj₁ (` x≢x) = ⊥-elim (x≢x refl)
... | inj₂ (y , ϕx≡′) = case sym ϕx≡ ■ ϕx≡′ of λ()
μPrefix-⋯ end ϕ ∀𝓖⊎` = refl
μPrefix-⋯ (msg ⊢s) ϕ ∀𝓖⊎` = refl
μPrefix-⋯ (brn ⊢s ⊢s₁) ϕ ∀𝓖⊎` = refl
μPrefix-⋯ (⊢s ; ⊢s₁) ϕ ∀𝓖⊎` = refl
μPrefix-⋯ skip ϕ ∀𝓖⊎` = refl
μPrefix-⋯ ret ϕ ∀𝓖⊎` = refl
μPrefix-⋯ acq ϕ ∀𝓖⊎` = refl
μPrefix-⋯ ``- ϕ ∀𝓖⊎` = refl
μPrefix-⋯ (mu g ⊢s) ϕ ∀𝓖⊎` = cong suc $ μPrefix-⋯ ⊢s (ϕ ↑) λ where
  zero → inj₁ g
  (suc x) → case ∀𝓖⊎` x of λ where
    (inj₁ (mu g′)) → inj₁ g′
    (inj₂ (_ , eq)) → inj₂ (_ , (sym (wk-`/id _) ■ cong wk eq))

μPrefix-unfold : 𝓖₀ s → ⊢ s → μPrefix (unfold s) ≡ μPrefix s
μPrefix-unfold g s = μPrefix-⋯ s ⦅ mu _ ⦆ₛ λ where
  zero    → inj₁ g
  (suc z) → inj₂ (_ , refl)

skipsSize : Skips s → ℕ
skipsSize skip = 0
skipsSize (s₁ ; s₂) = 1 + (skipsSize s₁ + skipsSize s₂)
skipsSize (mu s) = 1 + skipsSize s

skipsSize-⋯ : ⦃ K : Kit 𝓕 ⦄ (x : Skips s) (ϕ : m –[ K ]→ n) → skipsSize (skips-⋯ {ϕ = ϕ} x) ≡ skipsSize x
skipsSize-⋯ skip ϕ = refl
skipsSize-⋯ (x₁ ; x₂) ϕ = cong₂ (λ m n → suc (m + n)) (skipsSize-⋯ x₁ ϕ) (skipsSize-⋯ x₂ ϕ)
skipsSize-⋯ (mu x) ϕ = cong suc (skipsSize-⋯ x (ϕ ↑))
