-- | Blocked⁺ and reduction exclude each other.
--
--     blocked⁺⇒¬step       : Blocked⁺ P → P ─→ₚ P′ → ⊥            (any P : Proc n)
--     step⇒¬blocked⁺       : P ─→ₚ P′ → ¬ Blocked⁺ P              (its contrapositive)
--     irreducible⇒blocked⁺ : [] ; γ ⊢ₚ P → ¬ (∃ P′. P ─→ₚ P′) → Blocked⁺ P   (P : Proc 0)
--
--   The first direction needs no typing.  It is an induction on the step; the
--   R-Struct case needs `Blocked⁺` to be invariant under `≋` (`bl-≋`), which in
--   turn needs BC / AC membership to be invariant under `≋′` and renamings.
--   BC and AC share one generic membership theory (`MemTheory`).  The ν rules of
--   `Blocked⁺` are read through a uniform view (`View`): each side of a binder is
--   either a channel group (`chan`) or a separator group (`sep`), and the side
--   condition only talks about the first variable of each side.
--
--   The converse is a corollary of `progress⁺ₚ`.  The paper's imprecise `Blocked`
--   is NOT exclusive with reduction (see the header of Safety/Blocked.agda).
module BorrowedCF.Safety.Progress.Exclusive where

open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base hiding (Blocked)
open import BorrowedCF.Reduction.Expressions using (_─→_; _⋯→_; E-App; E-Seq; E-PairElim; E-SumElim; E-Unfold; E-Ann; E-□; E-Ctx)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Processes.Congruence using (swap-swap; assocSwap-swap)
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_; R-Exp; R-New; R-Fork; R-Com; R-Choice; R-LSplit; R-RSplit; R-Drop; R-Acq; R-Close; R-Discard; R-Par; R-Bind; R-Struct)

open import BorrowedCF.Safety.Blocked
open import BorrowedCF.Safety.Progress.Expr.Plug
open import BorrowedCF.Safety.Progress.Sync.Unique using (plug-K⊥)
open import BorrowedCF.Safety.Progress using (progress⁺ₚ)

open Nat.Variables
open Variables
open Fin.Patterns

--------------------------------------------------------------------------------
-- 1.  Expressions: a stuck thread has exactly one redex, and it does not step.

-- A constant from class C applied to a value.
data KRed (C : Const → Set) {n} : Tm n → Set where
  kr : ∀ {c d} {v : Tm n} → C c → Value v → KRed C (K c ·⟨ d ⟩ v)

private
  kred-value⊥ : ∀ {C} {e : Tm n} → Value e → Plug (KRed C) e → ⊥
  kred-value⊥ V-`         (here ())
  kred-value⊥ V-K         (here ())
  kred-value⊥ V-λ         (here ())
  kred-value⊥ (V-⊗ V₁ V₂) (here ())
  kred-value⊥ (V-⊗ V₁ V₂) (pairˡ p)   = kred-value⊥ V₁ p
  kred-value⊥ (V-⊗ V₁ V₂) (pairʳ _ p) = kred-value⊥ V₂ p
  kred-value⊥ (V-⊕ V)     (here ())
  kred-value⊥ (V-⊕ V)     (injˡ p)    = kred-value⊥ V p

  -- In an application one side is a value, depending on the direction.
  app-split : ∀ {d : Dir} {e₁ e₂ : Tm n} {A : Set} →
    (d ≡ L → Value e₂) → (d ≡ 𝟙 ⊎ d ≡ R → Value e₁) →
    (Value e₁ → A) → (Value e₂ → A) → A
  app-split {d = L} V? V?′ k₁ k₂ = k₂ (V? refl)
  app-split {d = R} V? V?′ k₁ k₂ = k₁ (V?′ (inj₂ refl))
  app-split {d = 𝟙} V? V?′ k₁ k₂ = k₁ (V?′ (inj₁ refl))

-- Unique decomposition: two constant redexes in evaluation position are the same.
kred-det : ∀ {C D} (e : Tm n) → Plug (KRed C) e → Plug (KRed D) e → Σ[ c ∈ Const ] C c × D c
kred-det (` z) (here ()) q
kred-det (K c) (here ()) q
kred-det (ƛ e) (here ()) q
kred-det (μ e) (here ()) q
kred-det (e ⦂ T) (here ()) q
kred-det (e₁ ·⟨ d ⟩ e₂) (here (kr p _)) (here (kr q _)) = _ , p , q
kred-det (e₁ ·⟨ d ⟩ e₂) (here (kr _ _)) (appˡ _ q) = ⊥-elim (kred-value⊥ V-K q)
kred-det (e₁ ·⟨ d ⟩ e₂) (here (kr _ V)) (appʳ _ q) = ⊥-elim (kred-value⊥ V q)
kred-det (e₁ ·⟨ d ⟩ e₂) (appˡ _ p) (here (kr _ _)) = ⊥-elim (kred-value⊥ V-K p)
kred-det (e₁ ·⟨ d ⟩ e₂) (appʳ _ p) (here (kr _ V)) = ⊥-elim (kred-value⊥ V p)
kred-det (e₁ ·⟨ d ⟩ e₂) (appˡ _ p) (appˡ _ q) = kred-det e₁ p q
kred-det (e₁ ·⟨ d ⟩ e₂) (appʳ _ p) (appʳ _ q) = kred-det e₂ p q
kred-det (e₁ ·⟨ d ⟩ e₂) (appˡ V? p) (appʳ V?′ q) =
  app-split V? V?′ (λ V → ⊥-elim (kred-value⊥ V p)) (λ V → ⊥-elim (kred-value⊥ V q))
kred-det (e₁ ·⟨ d ⟩ e₂) (appʳ V?′ p) (appˡ V? q) =
  app-split V? V?′ (λ V → ⊥-elim (kred-value⊥ V q)) (λ V → ⊥-elim (kred-value⊥ V p))
kred-det (e₁ ⊗ e₂) (here ()) q
kred-det (e₁ ⊗ e₂) (pairˡ p) (here ())
kred-det (e₁ ⊗ e₂) (pairˡ p) (pairˡ q) = kred-det e₁ p q
kred-det (e₁ ⊗ e₂) (pairˡ p) (pairʳ V q) = ⊥-elim (kred-value⊥ V p)
kred-det (e₁ ⊗ e₂) (pairʳ V p) (here ())
kred-det (e₁ ⊗ e₂) (pairʳ V p) (pairˡ q) = ⊥-elim (kred-value⊥ V q)
kred-det (e₁ ⊗ e₂) (pairʳ _ p) (pairʳ _ q) = kred-det e₂ p q
kred-det (e₁ ; e₂) (here ()) q
kred-det (e₁ ; e₂) (seqˡ p) (here ())
kred-det (e₁ ; e₂) (seqˡ p) (seqˡ q) = kred-det e₁ p q
kred-det (`let⊗ e₁ `in e₂) (here ()) q
kred-det (`let⊗ e₁ `in e₂) (let⊗ˡ p) (here ())
kred-det (`let⊗ e₁ `in e₂) (let⊗ˡ p) (let⊗ˡ q) = kred-det e₁ p q
kred-det (`inj i e) (here ()) q
kred-det (`inj i e) (injˡ p) (here ())
kred-det (`inj i e) (injˡ p) (injˡ q) = kred-det e p q
kred-det (`case e `of⟨ e₁ ; e₂ ⟩) (here ()) q
kred-det (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) (here ())
kred-det (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) (caseˡ q) = kred-det e p q

-- Values do not step.
step-¬value : e ─→ e′ → Value e → ⊥
step-¬value (E-App _)        ()
step-¬value (E-Seq _)        ()
step-¬value (E-PairElim _ _) ()
step-¬value (E-SumElim _)    ()
step-¬value E-Unfold         ()
step-¬value E-Ann            ()

⋯→-¬value : e ⋯→ e′ → Value e → ⊥
⋯→-¬value (E-□ r) V = step-¬value r V
⋯→-¬value (E-Ctx (app₁ _ _ _) s) ()
⋯→-¬value (E-Ctx (app₂ _ _ _) s) ()
⋯→-¬value (E-Ctx (□⊗ _) s) (V-⊗ V₁ _) = ⋯→-¬value s V₁
⋯→-¬value (E-Ctx (_ ⊗□) s) (V-⊗ _ V₂) = ⋯→-¬value s V₂
⋯→-¬value (E-Ctx (□; _) s) ()
⋯→-¬value (E-Ctx (`let⊗-`in _) s) ()
⋯→-¬value (E-Ctx (`inj□ _) s) (V-⊕ V) = ⋯→-¬value s V
⋯→-¬value (E-Ctx `case□`of⟨ _ ; _ ⟩ s) ()

-- A term with a constant redex in evaluation position does not step.
private
  kred-¬─→ : ∀ {C} → e ─→ e′ → Plug (KRed C) e → ⊥
  kred-¬─→ (E-App V) (here ())
  kred-¬─→ (E-App V) (appˡ _ p) = kred-value⊥ V-λ p
  kred-¬─→ (E-App V) (appʳ _ p) = kred-value⊥ V p
  kred-¬─→ (E-Seq V) (here ())
  kred-¬─→ (E-Seq V) (seqˡ p) = kred-value⊥ V p
  kred-¬─→ (E-PairElim V₁ V₂) (here ())
  kred-¬─→ (E-PairElim V₁ V₂) (let⊗ˡ p) = kred-value⊥ (V-⊗ V₁ V₂) p
  kred-¬─→ (E-SumElim V) (here ())
  kred-¬─→ (E-SumElim V) (caseˡ p) = kred-value⊥ (V-⊕ V) p
  kred-¬─→ E-Unfold (here ())
  kred-¬─→ E-Ann (here ())

kred-¬⋯→ : ∀ {C} → e ⋯→ e′ → Plug (KRed C) e → ⊥
kred-¬⋯→ (E-□ r) p = kred-¬─→ r p
kred-¬⋯→ (E-Ctx (app₁ _ _ _) s) (here (kr _ _)) = ⋯→-¬value s V-K
kred-¬⋯→ (E-Ctx (app₁ _ _ _) s) (appˡ _ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (app₁ _ _ V?) s) (appʳ V?′ p) =
  app-split V? V?′ (⋯→-¬value s) (λ V → kred-value⊥ V p)
kred-¬⋯→ (E-Ctx (app₂ _ _ _) s) (here (kr _ V)) = ⋯→-¬value s V
kred-¬⋯→ (E-Ctx (app₂ _ _ _) s) (appʳ _ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (app₂ _ _ V?′) s) (appˡ V? p) =
  app-split V? V?′ (λ V → kred-value⊥ V p) (⋯→-¬value s)
kred-¬⋯→ (E-Ctx (□⊗ _) s) (here ())
kred-¬⋯→ (E-Ctx (□⊗ _) s) (pairˡ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (□⊗ _) s) (pairʳ V p) = ⋯→-¬value s V
kred-¬⋯→ (E-Ctx (V ⊗□) s) (here ())
kred-¬⋯→ (E-Ctx (V ⊗□) s) (pairˡ p) = kred-value⊥ V p
kred-¬⋯→ (E-Ctx (V ⊗□) s) (pairʳ _ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (□; _) s) (here ())
kred-¬⋯→ (E-Ctx (□; _) s) (seqˡ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (`let⊗-`in _) s) (here ())
kred-¬⋯→ (E-Ctx (`let⊗-`in _) s) (let⊗ˡ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx (`inj□ _) s) (here ())
kred-¬⋯→ (E-Ctx (`inj□ _) s) (injˡ p) = kred-¬⋯→ s p
kred-¬⋯→ (E-Ctx `case□`of⟨ _ ; _ ⟩ s) (here ())
kred-¬⋯→ (E-Ctx `case□`of⟨ _ ; _ ⟩ s) (caseˡ p) = kred-¬⋯→ s p

-- Blocked threads.

thr-inv : Blocked⁺ ⟪ e ⟫ → e ≡ * ⊎ Stuck e
thr-inv B-Unit⁺      = inj₁ refl
thr-inv (B-Const⁺ s) = inj₂ s

stuck⇒kred : Stuck e → Plug (KRed BlockingConst) e
stuck⇒kred (E , c , d , v , V , bc , refl) = plug-frame* E (here (kr bc V))

-- A blocked thread has no redex of a non-blocking constant.
thread-⊥ : Blocked⁺ ⟪ e ⟫ → Plug (KRed (λ c → ¬ BlockingConst c)) e → ⊥
thread-⊥ b p with thr-inv b
... | inj₁ refl = kred-value⊥ V-K p
... | inj₂ s with c , bc , ¬bc ← kred-det _ (stuck⇒kred s) p = ¬bc bc

thread-¬⋯→ : Blocked⁺ ⟪ e ⟫ → e ⋯→ e′ → ⊥
thread-¬⋯→ b s with thr-inv b
... | inj₁ refl = ⋯→-¬value s V-K
... | inj₂ stk  = kred-¬⋯→ s (stuck⇒kred stk)

--------------------------------------------------------------------------------
-- 2.  Renaming facts for the binder permutations of `≋′`.

swap-↑ʳ : ∀ a b {n} (x : 𝔽 n) → swapᵣ a b ((a + b) ↑ʳ x) ≡ (b + a) ↑ʳ x
swap-↑ʳ a b {n} x rewrite splitAt-↑ʳ (a + b) n x = refl

swap-hl : ∀ a b {n} (x : 𝔽 a) → swapᵣ a b {n} ((x ↑ˡ b) ↑ˡ n) ≡ (b ↑ʳ x) ↑ˡ n
swap-hl a b {n} x rewrite splitAt-↑ˡ (a + b) (x ↑ˡ b) n | splitAt-↑ˡ a x b = refl

swap-hr : ∀ a b {n} (y : 𝔽 b) → swapᵣ a b {n} ((a ↑ʳ y) ↑ˡ n) ≡ (y ↑ˡ a) ↑ˡ n
swap-hr a b {n} y rewrite splitAt-↑ˡ (a + b) (a ↑ʳ y) n | splitAt-↑ʳ a b y = refl

swap-inj : ∀ a b {n} → Inj (swapᵣ a b {n})
swap-inj a b {x = x} {y} eq = sym (swap-swap a b x) ■ cong (swapᵣ b a) eq ■ swap-swap a b y

assoc-A : ∀ a b {n} (x : 𝔽 b) → assocSwapᵣ a b (a ↑ʳ (x ↑ˡ n)) ≡ x ↑ˡ (a + n)
assoc-A a b {n} x rewrite splitAt-↑ʳ a (b + n) (x ↑ˡ n) | splitAt-↑ˡ b x n = refl

assoc-B : ∀ a b {n} (x : 𝔽 a) → assocSwapᵣ a b (x ↑ˡ (b + n)) ≡ b ↑ʳ (x ↑ˡ n)
assoc-B a b {n} x rewrite splitAt-↑ˡ a x (b + n) = refl

assoc-C : ∀ a b {n} (x : 𝔽 n) → assocSwapᵣ a b (a ↑ʳ (b ↑ʳ x)) ≡ b ↑ʳ (a ↑ʳ x)
assoc-C a b {n} x rewrite splitAt-↑ʳ a (b + n) (b ↑ʳ x) | splitAt-↑ʳ b n x = refl

assoc-inj : ∀ a b {n} → Inj (assocSwapᵣ a b {n})
assoc-inj a b {x = x} {y} eq =
  sym (assocSwap-swap a b x) ■ cong (assocSwapᵣ b a) eq ■ assocSwap-swap a b y

wk-↑ʳ : ∀ s {n} (x : 𝔽 n) → weaken* ⦃ Kᵣ ⦄ s x ≡ s ↑ʳ x
wk-↑ʳ s x = weaken*~wkˡ ⦃ Kᵣ ⦄ s x

--------------------------------------------------------------------------------
-- 3.  BC / AC membership, once for both.

module MemTheory
  (R : ∀ {n} → 𝔽 n → Tm n → Set)
  (R-⋯ᵣ : ∀ {m n} (ρ : m →ᵣ n) {x : 𝔽 m} {e : Tm m} → R x e → R (ρ x) (e ⋯ ρ))
  (R-⋯ᵣ⁻¹ : ∀ {m n} (ρ : m →ᵣ n) {y : 𝔽 n} (e : Tm m) → R y (e ⋯ ρ) →
            ∃[ x ] ρ x ≡ y × R x e)
  (R-unit : ∀ {n} {x : 𝔽 n} → ¬ R x *)
  where

  data Mem {n} (x : 𝔽 n) : Proc n → Set where
    thr : ∀ {e : Tm n} → R x e → Mem x ⟪ e ⟫
    ∥ˡ  : ∀ {P Q : Proc n} → Mem x P → Mem x (P ∥ Q)
    ∥ʳ  : ∀ {P Q : Proc n} → Mem x Q → Mem x (P ∥ Q)
    res : ∀ {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} →
          Mem ((sum B₁ + sum B₂) ↑ʳ x) P → Mem x (ν B₁ B₂ P)

  res⁻¹ : ∀ {x : 𝔽 n} {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} →
    Mem x (ν B₁ B₂ P) → Mem ((sum B₁ + sum B₂) ↑ʳ x) P
  res⁻¹ (res m) = m

  push : (ρ : m →ᵣ n) {x : 𝔽 m} (P : Proc m) → Mem x P → Mem (ρ x) (P ⋯ₚ ρ)
  push ρ ⟪ e ⟫   (thr r) = thr (R-⋯ᵣ ρ r)
  push ρ (P ∥ Q) (∥ˡ m)  = ∥ˡ (push ρ P m)
  push ρ (P ∥ Q) (∥ʳ m)  = ∥ʳ (push ρ Q m)
  push ρ (ν B₁ B₂ P) (res m) =
    res (subst (λ z → Mem z (P ⋯ₚ ρ ↑* (sum B₁ + sum B₂)))
               (↑*-↑ʳ (sum B₁ + sum B₂) ρ _)
               (push (ρ ↑* (sum B₁ + sum B₂)) P m))

  pull : (ρ : m →ᵣ n) {y : 𝔽 n} (P : Proc m) → Mem y (P ⋯ₚ ρ) →
    ∃[ x ] ρ x ≡ y × Mem x P
  pull ρ ⟪ e ⟫ (thr r)
    with x , eq , r′ ← R-⋯ᵣ⁻¹ ρ e r = x , eq , thr r′
  pull ρ (P ∥ Q) (∥ˡ m)
    with x , eq , m′ ← pull ρ P m = x , eq , ∥ˡ m′
  pull ρ (P ∥ Q) (∥ʳ m)
    with x , eq , m′ ← pull ρ Q m = x , eq , ∥ʳ m′
  pull ρ (ν B₁ B₂ P) (res m)
    with z , eqz , m′ ← pull (ρ ↑* (sum B₁ + sum B₂)) P m
    with x , refl , refl ← ↑*-↑ʳ⁻¹ (sum B₁ + sum B₂) ρ z eqz
    = x , refl , res m′

  push-eq : (ρ : m →ᵣ n) (P : Proc m) {x : 𝔽 m} {y : 𝔽 n} → ρ x ≡ y →
    Mem x P → Mem y (P ⋯ₚ ρ)
  push-eq ρ P refl m = push ρ P m

  pull-inj : (ρ : m →ᵣ n) → Inj ρ → (P : Proc m) {x : 𝔽 m} {y : 𝔽 n} → ρ x ≡ y →
    Mem y (P ⋯ₚ ρ) → Mem x P
  pull-inj ρ inj P eq m
    with z , eqz , m′ ← pull ρ P m
    with refl ← inj (eqz ■ sym eq) = m′

  -- A variable bound by a ν is not in the weakened left operand of ν-ext.
  ext-mem : ∀ s {P : Proc n} {Q : Proc (s + n)} (z : 𝔽 s) →
    Mem (z ↑ˡ n) ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ s) ∥ Q) → Mem (z ↑ˡ n) Q
  ext-mem s {P = P} z (∥ˡ m)
    with x , eq , _ ← pull (weaken* ⦃ Kᵣ ⦄ s) P m = ⊥-elim (↑ˡ≢↑ʳ (sym eq ■ wk-↑ʳ s x))
  ext-mem s z (∥ʳ m) = m

  mem-fwd : P ≋′ Q → ∀ {x} → Mem x P → Mem x Q
  mem-fwd ∥-comm′  (∥ˡ m) = ∥ʳ m
  mem-fwd ∥-comm′  (∥ʳ m) = ∥ˡ m
  mem-fwd ∥-assoc′ (∥ˡ m) = ∥ˡ (∥ˡ m)
  mem-fwd ∥-assoc′ (∥ʳ (∥ˡ m)) = ∥ˡ (∥ʳ m)
  mem-fwd ∥-assoc′ (∥ʳ (∥ʳ m)) = ∥ʳ m
  mem-fwd ∥-unit′  (∥ˡ (thr r)) = ⊥-elim (R-unit r)
  mem-fwd ∥-unit′  (∥ʳ m) = m
  mem-fwd (ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) (res m) =
    res (push-eq (swapᵣ (sum B₁) (sum B₂)) P (swap-↑ʳ (sum B₁) (sum B₂) _) m)
  mem-fwd (ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) (res (res m)) =
    res (res (push-eq (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)) P
                      (assoc-C (sum A₁ + sum A₂) (sum B₁ + sum B₂) _) m))
  mem-fwd (ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂}) (∥ˡ m) =
    res (∥ˡ (push-eq (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) P (wk-↑ʳ (sum B₁ + sum B₂) _) m))
  mem-fwd ν-ext′ (∥ʳ (res m)) = res (∥ʳ m)
  mem-fwd (∥-cong′ e) (∥ˡ m) = ∥ˡ (mem-fwd e m)
  mem-fwd (∥-cong′ e) (∥ʳ m) = ∥ʳ m
  mem-fwd (ν-cong′ e) (res m) = res (mem-fwd e m)

  mem-bwd : P ≋′ Q → ∀ {x} → Mem x Q → Mem x P
  mem-bwd ∥-comm′  (∥ˡ m) = ∥ʳ m
  mem-bwd ∥-comm′  (∥ʳ m) = ∥ˡ m
  mem-bwd ∥-assoc′ (∥ˡ (∥ˡ m)) = ∥ˡ m
  mem-bwd ∥-assoc′ (∥ˡ (∥ʳ m)) = ∥ʳ (∥ˡ m)
  mem-bwd ∥-assoc′ (∥ʳ m) = ∥ʳ (∥ʳ m)
  mem-bwd ∥-unit′  m = ∥ʳ m
  mem-bwd (ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) (res m) =
    res (pull-inj (swapᵣ (sum B₁) (sum B₂)) (swap-inj (sum B₁) (sum B₂)) P
                  (swap-↑ʳ (sum B₁) (sum B₂) _) m)
  mem-bwd (ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) (res (res m)) =
    res (res (pull-inj (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))
                       (assoc-inj (sum A₁ + sum A₂) (sum B₁ + sum B₂)) P
                       (assoc-C (sum A₁ + sum A₂) (sum B₁ + sum B₂) _) m))
  mem-bwd (ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂}) (res (∥ˡ m)) =
    ∥ˡ (pull-inj (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) (wk*-inj (sum B₁ + sum B₂)) P
                 (wk-↑ʳ (sum B₁ + sum B₂) _) m)
  mem-bwd ν-ext′ (res (∥ʳ m)) = ∥ʳ (res m)
  mem-bwd (∥-cong′ e) (∥ˡ m) = ∥ˡ (mem-bwd e m)
  mem-bwd (∥-cong′ e) (∥ʳ m) = ∥ʳ m
  mem-bwd (ν-cong′ e) (res m) = res (mem-bwd e m)

private
  bc-unit : ∀ {x : 𝔽 n} → ¬ x ∈BCe *
  bc-unit m = plug-K⊥ (∈BCe⇒plug m)

  ac-unit : ∀ {x : 𝔽 n} → ¬ x ∈ACe *
  ac-unit m with ∈ACe⇒plug m
  ... | here ()

module BC = MemTheory _∈BCe_ (λ ρ r → ∈BCe-⋯ᵣ ρ r) (λ ρ e r → ∈BCe-⋯ᵣ⁻¹ ρ e r) bc-unit
module AC = MemTheory _∈ACe_ (λ ρ r → ∈ACe-⋯ᵣ ρ r) (λ ρ e r → ∈ACe-⋯ᵣ⁻¹ ρ e r) ac-unit

private
  toBC : ∀ {x : 𝔽 n} {P} → x ∈BC P → BC.Mem x P
  toBC (thr m) = BC.thr m
  toBC (∥ˡ m)  = BC.∥ˡ (toBC m)
  toBC (∥ʳ m)  = BC.∥ʳ (toBC m)
  toBC (res m) = BC.res (toBC m)

  fromBC : ∀ {x : 𝔽 n} {P} → BC.Mem x P → x ∈BC P
  fromBC (BC.thr m) = thr m
  fromBC (BC.∥ˡ m)  = ∥ˡ (fromBC m)
  fromBC (BC.∥ʳ m)  = ∥ʳ (fromBC m)
  fromBC (BC.res m) = res (fromBC m)

  toAC : ∀ {x : 𝔽 n} {P} → x ∈AC P → AC.Mem x P
  toAC (thr m) = AC.thr m
  toAC (∥ˡ m)  = AC.∥ˡ (toAC m)
  toAC (∥ʳ m)  = AC.∥ʳ (toAC m)
  toAC (res m) = AC.res (toAC m)

  fromAC : ∀ {x : 𝔽 n} {P} → AC.Mem x P → x ∈AC P
  fromAC (AC.thr m) = thr m
  fromAC (AC.∥ˡ m)  = ∥ˡ (fromAC m)
  fromAC (AC.∥ʳ m)  = ∥ʳ (fromAC m)
  fromAC (AC.res m) = res (fromAC m)

--------------------------------------------------------------------------------
-- 4.  A uniform view of the four ν rules of `Blocked⁺`.

-- The side of a binder that `Blocked⁺` admits: a channel group or a separator group.
data GKind : BindGroup → Set where
  chan : ∀ {b B} → GKind (suc b ∷ B)
  sep  : ∀ {b B} → GKind (0 ∷ suc b ∷ B)

-- Its first variable.
hd : ∀ {B} → GKind B → 𝔽 (sum B)
hd chan = zero
hd sep  = zero

-- The side condition, over abstract propositions "head i is in BC / AC".
Cond : ∀ {B₁ B₂} → GKind B₁ → GKind B₂ → (b₁ b₂ a₁ a₂ : Set) → Set
Cond chan chan b₁ b₂ a₁ a₂ = ¬ (b₁ × b₂)
Cond chan sep  b₁ b₂ a₁ a₂ = ¬ a₂
Cond sep  chan b₁ b₂ a₁ a₂ = ¬ a₁
Cond sep  sep  b₁ b₂ a₁ a₂ = ¬ a₁ × ¬ a₂

Cond-map : ∀ {B₁ B₂} (k₁ : GKind B₁) (k₂ : GKind B₂) {b₁ b₂ a₁ a₂ b₁′ b₂′ a₁′ a₂′ : Set} →
  (b₁′ → b₁) → (b₂′ → b₂) → (a₁′ → a₁) → (a₂′ → a₂) →
  Cond k₁ k₂ b₁ b₂ a₁ a₂ → Cond k₁ k₂ b₁′ b₂′ a₁′ a₂′
Cond-map chan chan f₁ f₂ g₁ g₂ c = λ{ (m₁ , m₂) → c (f₁ m₁ , f₂ m₂) }
Cond-map chan sep  f₁ f₂ g₁ g₂ c = c ∘ g₂
Cond-map sep  chan f₁ f₂ g₁ g₂ c = c ∘ g₁
Cond-map sep  sep  f₁ f₂ g₁ g₂ (c₁ , c₂) = c₁ ∘ g₁ , c₂ ∘ g₂

Cond-swap : ∀ {B₁ B₂} (k₁ : GKind B₁) (k₂ : GKind B₂) {b₁ b₂ a₁ a₂ : Set} →
  Cond k₁ k₂ b₁ b₂ a₁ a₂ → Cond k₂ k₁ b₂ b₁ a₂ a₁
Cond-swap chan chan c = λ{ (m₂ , m₁) → c (m₁ , m₂) }
Cond-swap chan sep  c = c
Cond-swap sep  chan c = c
Cond-swap sep  sep  (c₁ , c₂) = c₂ , c₁

-- The side condition at two concrete variables of a process.
CondAt : ∀ {B₁ B₂ N} → GKind B₁ → GKind B₂ → 𝔽 N → 𝔽 N → Proc N → Set
CondAt k₁ k₂ x₁ x₂ P = Cond k₁ k₂ (BC.Mem x₁ P) (BC.Mem x₂ P) (AC.Mem x₁ P) (AC.Mem x₂ P)

module _ {B₁ B₂ : BindGroup} (k₁ : GKind B₁) (k₂ : GKind B₂) where

  cond-pull : (ρ : m →ᵣ n) → Inj ρ → (P : Proc m) {x₁ x₂ : 𝔽 m} {y₁ y₂ : 𝔽 n} →
    ρ x₁ ≡ y₁ → ρ x₂ ≡ y₂ → CondAt k₁ k₂ x₁ x₂ P → CondAt k₁ k₂ y₁ y₂ (P ⋯ₚ ρ)
  cond-pull ρ inj P e₁ e₂ =
    Cond-map k₁ k₂ (BC.pull-inj ρ inj P e₁) (BC.pull-inj ρ inj P e₂)
                   (AC.pull-inj ρ inj P e₁) (AC.pull-inj ρ inj P e₂)

  cond-push : (ρ : m →ᵣ n) (P : Proc m) {x₁ x₂ : 𝔽 m} {y₁ y₂ : 𝔽 n} →
    ρ x₁ ≡ y₁ → ρ x₂ ≡ y₂ → CondAt k₁ k₂ y₁ y₂ (P ⋯ₚ ρ) → CondAt k₁ k₂ x₁ x₂ P
  cond-push ρ P e₁ e₂ =
    Cond-map k₁ k₂ (BC.push-eq ρ P e₁) (BC.push-eq ρ P e₂)
                   (AC.push-eq ρ P e₁) (AC.push-eq ρ P e₂)

  -- Moving the condition through one restriction.
  cond-res : ∀ {A₁ A₂} {Q : Proc (sum A₁ + sum A₂ + n)} {x₁ x₂ : 𝔽 n} →
    CondAt k₁ k₂ ((sum A₁ + sum A₂) ↑ʳ x₁) ((sum A₁ + sum A₂) ↑ʳ x₂) Q →
    CondAt k₁ k₂ x₁ x₂ (ν A₁ A₂ Q)
  cond-res = Cond-map k₁ k₂ BC.res⁻¹ BC.res⁻¹ AC.res⁻¹ AC.res⁻¹

  cond-unres : ∀ {A₁ A₂} {Q : Proc (sum A₁ + sum A₂ + n)} {x₁ x₂ : 𝔽 n} →
    CondAt k₁ k₂ x₁ x₂ (ν A₁ A₂ Q) →
    CondAt k₁ k₂ ((sum A₁ + sum A₂) ↑ʳ x₁) ((sum A₁ + sum A₂) ↑ʳ x₂) Q
  cond-unres = Cond-map k₁ k₂ BC.res BC.res AC.res AC.res

-- The heads of `ν B₁ B₂ P`, as variables of P.
hˡ : ∀ {B₁} B₂ n → GKind B₁ → 𝔽 (sum B₁ + sum B₂ + n)
hˡ B₂ n k = (hd k ↑ˡ sum B₂) ↑ˡ n

hʳ : ∀ B₁ {B₂} n → GKind B₂ → 𝔽 (sum B₁ + sum B₂ + n)
hʳ B₁ n k = (sum B₁ ↑ʳ hd k) ↑ˡ n

record View {n} (B₁ B₂ : BindGroup) (P : Proc (sum B₁ + sum B₂ + n)) : Set where
  constructor view
  field
    kind₁ : GKind B₁
    kind₂ : GKind B₂
    cond : CondAt kind₁ kind₂ (hˡ B₂ n kind₁) (hʳ B₁ n kind₂) P
    body : Blocked⁺ P

view⇒ : ∀ {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} → Blocked⁺ (ν B₁ B₂ P) → View B₁ B₂ P
view⇒ (B-Nu⁺ ¬bc bl)         = view chan chan (λ{ (m₁ , m₂) → ¬bc (fromBC m₁ , fromBC m₂) }) bl
view⇒ (B-NuAcqˡ⁺ ¬ac bl)     = view sep chan (λ m → ¬ac (fromAC m)) bl
view⇒ (B-NuAcqʳ⁺ ¬ac bl)     = view chan sep (λ m → ¬ac (fromAC m)) bl
view⇒ (B-NuAcqˡʳ⁺ ¬a ¬b bl)  = view sep sep ((λ m → ¬a (fromAC m)) , (λ m → ¬b (fromAC m))) bl

view⇐ : ∀ {B₁ B₂} {P : Proc (sum B₁ + sum B₂ + n)} → View B₁ B₂ P → Blocked⁺ (ν B₁ B₂ P)
view⇐ (view chan chan c bl)       = B-Nu⁺ (λ{ (m₁ , m₂) → c (toBC m₁ , toBC m₂) }) bl
view⇐ (view sep  chan c bl)       = B-NuAcqˡ⁺ (λ m → c (toAC m)) bl
view⇐ (view chan sep  c bl)       = B-NuAcqʳ⁺ (λ m → c (toAC m)) bl
view⇐ (view sep  sep  (c₁ , c₂) bl) = B-NuAcqˡʳ⁺ (λ m → c₁ (toAC m)) (λ m → c₂ (toAC m)) bl

par-inv : Blocked⁺ (P ∥ Q) → Blocked⁺ P × Blocked⁺ Q
par-inv (B-Par⁺ p q) = p , q

--------------------------------------------------------------------------------
-- 5.  Blocked⁺ under renamings and structural congruence.

bl-⋯ᵣ : (ρ : m →ᵣ n) → Inj ρ → (P : Proc m) → Blocked⁺ P → Blocked⁺ (P ⋯ₚ ρ)
bl-⋯ᵣ ρ inj ⟪ e ⟫ b with thr-inv b
... | inj₁ refl = B-Unit⁺
... | inj₂ s    = B-Const⁺ (Stuck-⋯ᵣ ρ s)
bl-⋯ᵣ ρ inj (P ∥ Q) b with p , q ← par-inv b = B-Par⁺ (bl-⋯ᵣ ρ inj P p) (bl-⋯ᵣ ρ inj Q q)
bl-⋯ᵣ ρ inj (ν B₁ B₂ P) b with view k₁ k₂ c bl ← view⇒ b =
  let s = sum B₁ + sum B₂ in
  view⇐ (view k₁ k₂
    (cond-pull k₁ k₂ (ρ ↑* s) (↑*-inj s inj) P (↑*-↑ˡ s ρ _) (↑*-↑ˡ s ρ _) c)
    (bl-⋯ᵣ (ρ ↑* s) (↑*-inj s inj) P bl))

bl-⋯ᵣ⁻¹ : (ρ : m →ᵣ n) (P : Proc m) → Blocked⁺ (P ⋯ₚ ρ) → Blocked⁺ P
bl-⋯ᵣ⁻¹ ρ ⟪ e ⟫ b with thr-inv b
... | inj₁ eq with refl ← ⋯ᵣ-K⁻¹ ρ e eq = B-Unit⁺
... | inj₂ s = B-Const⁺ (Stuck-⋯ᵣ⁻¹ ρ e s)
bl-⋯ᵣ⁻¹ ρ (P ∥ Q) b with p , q ← par-inv b = B-Par⁺ (bl-⋯ᵣ⁻¹ ρ P p) (bl-⋯ᵣ⁻¹ ρ Q q)
bl-⋯ᵣ⁻¹ ρ (ν B₁ B₂ P) b with view k₁ k₂ c bl ← view⇒ b =
  let s = sum B₁ + sum B₂ in
  view⇐ (view k₁ k₂
    (cond-push k₁ k₂ (ρ ↑* s) P (↑*-↑ˡ s ρ _) (↑*-↑ˡ s ρ _) c)
    (bl-⋯ᵣ⁻¹ (ρ ↑* s) P bl))

bl-fwd : P ≋′ Q → Blocked⁺ P → Blocked⁺ Q
bl-bwd : P ≋′ Q → Blocked⁺ Q → Blocked⁺ P

bl-fwd ∥-comm′ b with p , q ← par-inv b = B-Par⁺ q p
bl-fwd ∥-assoc′ b
  with p , qr ← par-inv b
  with q , r ← par-inv qr = B-Par⁺ (B-Par⁺ p q) r
bl-fwd ∥-unit′ b = proj₂ (par-inv b)
bl-fwd (ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) b
  with view k₁ k₂ c bl ← view⇒ b =
  let σ = swapᵣ (sum B₁) (sum B₂) ; inj = swap-inj (sum B₁) (sum B₂) in
  view⇐ (view k₂ k₁
    (cond-pull k₂ k₁ σ inj P (swap-hr (sum B₁) (sum B₂) (hd k₂)) (swap-hl (sum B₁) (sum B₂) (hd k₁))
               (Cond-swap k₁ k₂ c))
    (bl-⋯ᵣ σ inj P bl))
bl-fwd (ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) b
  with view kB₁ kB₂ cB blA ← view⇒ b
  with view kA₁ kA₂ cA blP ← view⇒ blA =
  let a = sum A₁ + sum A₂ ; s = sum B₁ + sum B₂
      α = assocSwapᵣ a s ; inj = assoc-inj a s in
  view⇐ (view kA₁ kA₂
    (cond-res kA₁ kA₂ (cond-pull kA₁ kA₂ α inj P (assoc-B a s _) (assoc-B a s _) cA))
    (view⇐ (view kB₁ kB₂
      (cond-pull kB₁ kB₂ α inj P (assoc-A a s _) (assoc-A a s _) (cond-unres kB₁ kB₂ cB))
      (bl-⋯ᵣ α inj P blP))))
bl-fwd (ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂}) b
  with bp , bν ← par-inv b
  with view k₁ k₂ c bq ← view⇒ bν =
  let s = sum B₁ + sum B₂ in
  view⇐ (view k₁ k₂
    (Cond-map k₁ k₂ (BC.ext-mem s _) (BC.ext-mem s _) (AC.ext-mem s _) (AC.ext-mem s _) c)
    (B-Par⁺ (bl-⋯ᵣ (weaken* ⦃ Kᵣ ⦄ s) (wk*-inj s) P bp) bq))
bl-fwd (∥-cong′ e) b with p , q ← par-inv b = B-Par⁺ (bl-fwd e p) q
bl-fwd (ν-cong′ e) b with view k₁ k₂ c bl ← view⇒ b =
  view⇐ (view k₁ k₂
    (Cond-map k₁ k₂ (BC.mem-bwd e) (BC.mem-bwd e) (AC.mem-bwd e) (AC.mem-bwd e) c)
    (bl-fwd e bl))

bl-bwd ∥-comm′ b with p , q ← par-inv b = B-Par⁺ q p
bl-bwd ∥-assoc′ b
  with pq , r ← par-inv b
  with p , q ← par-inv pq = B-Par⁺ p (B-Par⁺ q r)
bl-bwd ∥-unit′ b = B-Par⁺ B-Unit⁺ b
bl-bwd (ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) b
  with view k₂ k₁ c bl ← view⇒ b =
  let σ = swapᵣ (sum B₁) (sum B₂) in
  view⇐ (view k₁ k₂
    (Cond-swap k₂ k₁
      (cond-push k₂ k₁ σ P (swap-hr (sum B₁) (sum B₂) (hd k₂)) (swap-hl (sum B₁) (sum B₂) (hd k₁)) c))
    (bl-⋯ᵣ⁻¹ σ P bl))
bl-bwd (ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) b
  with view kA₁ kA₂ cA blB ← view⇒ b
  with view kB₁ kB₂ cB blP ← view⇒ blB =
  let a = sum A₁ + sum A₂ ; s = sum B₁ + sum B₂ ; α = assocSwapᵣ a s in
  view⇐ (view kB₁ kB₂
    (cond-res kB₁ kB₂ (cond-push kB₁ kB₂ α P (assoc-A a s _) (assoc-A a s _) cB))
    (view⇐ (view kA₁ kA₂
      (cond-push kA₁ kA₂ α P (assoc-B a s _) (assoc-B a s _) (cond-unres kA₁ kA₂ cA))
      (bl-⋯ᵣ⁻¹ α P blP))))
bl-bwd (ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂}) b
  with view k₁ k₂ c bl ← view⇒ b
  with bp , bq ← par-inv bl =
  B-Par⁺ (bl-⋯ᵣ⁻¹ (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) P bp)
         (view⇐ (view k₁ k₂ (Cond-map k₁ k₂ BC.∥ʳ BC.∥ʳ AC.∥ʳ AC.∥ʳ c) bq))
bl-bwd (∥-cong′ e) b with p , q ← par-inv b = B-Par⁺ (bl-bwd e p) q
bl-bwd (ν-cong′ e) b with view k₁ k₂ c bl ← view⇒ b =
  view⇐ (view k₁ k₂
    (Cond-map k₁ k₂ (BC.mem-fwd e) (BC.mem-fwd e) (AC.mem-fwd e) (AC.mem-fwd e) c)
    (bl-bwd e bl))

bl-≋ : P ≋ Q → Blocked⁺ P → Blocked⁺ Q
bl-≋ ε b = b
bl-≋ (fwd e ◅ es) b = bl-≋ es (bl-fwd e b)
bl-≋ (bwd e ◅ es) b = bl-≋ es (bl-bwd e b)

--------------------------------------------------------------------------------
-- 6.  The theorems.

blocked⁺⇒¬step : {P P′ : Proc n} → Blocked⁺ P → P ─→ₚ P′ → ⊥
blocked⁺⇒¬step b (R-Exp s) = thread-¬⋯→ b s
blocked⁺⇒¬step b (R-New E) = thread-⊥ b (plug-frame* E (here (kr (λ ()) V-K)))
blocked⁺⇒¬step b (R-Fork E V) = thread-⊥ b (plug-frame* E (here (kr (λ ()) V)))
blocked⁺⇒¬step b (R-Com {b₁ = b₁} {B₁ = B₁} {b₂ = b₂} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} V)
  with view chan chan c _ ← view⇒ b =
  let wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
  c ( BC.∥ˡ (BC.∥ˡ (BC.thr (send (E₁ ⋯ᶠ* wkρ) (V ⋯ᵛ wkρ))))
    , BC.∥ˡ (BC.∥ʳ (BC.thr (recv (E₂ ⋯ᶠ* wkρ)))) )
blocked⁺⇒¬step b (R-Choice E₁ E₂ i) with view chan chan c _ ← view⇒ b =
  c (BC.∥ˡ (BC.∥ˡ (BC.thr (select E₁ i))) , BC.∥ˡ (BC.∥ʳ (BC.thr (branch E₂))))
blocked⁺⇒¬step b (R-LSplit {E = E})
  with view _ _ _ bl ← view⇒ b
  with bt , _ ← par-inv bl = thread-⊥ bt (plug-frame* E (here (kr (λ ()) V-`)))
blocked⁺⇒¬step b (R-RSplit {E = E})
  with view _ _ _ bl ← view⇒ b
  with bt , _ ← par-inv bl = thread-⊥ bt (plug-frame* E (here (kr (λ ()) V-`)))
blocked⁺⇒¬step b (R-Drop {E = E})
  with view _ _ _ bl ← view⇒ b
  with bt , _ ← par-inv bl = thread-⊥ bt (plug-frame* (E ⋯ᶠ* weakenᵣ) (here (kr (λ ()) V-`)))
blocked⁺⇒¬step b (R-Discard {E = E})
  with view _ _ _ bl ← view⇒ b
  with bt , _ ← par-inv bl = thread-⊥ bt (plug-frame* (E ⋯ᶠ* weakenᵣ) (here (kr (λ ()) V-`)))
blocked⁺⇒¬step b (R-Acq {E = E}) with view⇒ b
... | view sep chan c _       = c (AC.∥ˡ (AC.thr (acq E)))
... | view sep sep  (c , _) _ = c (AC.∥ˡ (AC.thr (acq E)))
blocked⁺⇒¬step b (R-Close {E₁ = E₁} {E₂ = E₂}) with view chan chan c _ ← view⇒ b =
  c ( BC.∥ˡ (BC.thr (end (E₁ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _) ‼))
    , BC.∥ʳ (BC.thr (end (E₂ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ _) ⁇)) )
blocked⁺⇒¬step b (R-Par s) = blocked⁺⇒¬step (proj₁ (par-inv b)) s
blocked⁺⇒¬step b (R-Bind s) = blocked⁺⇒¬step (View.body (view⇒ b)) s
blocked⁺⇒¬step b (R-Struct p s q) = blocked⁺⇒¬step (bl-≋ p b) s

blocked⁺⇒irreducible : {P : Proc n} → Blocked⁺ P → ¬ (Σ[ P′ ∈ Proc n ] P ─→ₚ P′)
blocked⁺⇒irreducible b (_ , s) = blocked⁺⇒¬step b s

-- Implied: the contrapositive.
step⇒¬blocked⁺ : {P P′ : Proc n} → P ─→ₚ P′ → ¬ Blocked⁺ P
step⇒¬blocked⁺ s b = blocked⁺⇒¬step b s

-- The converse needs progress, hence a closed well-typed process.
irreducible⇒blocked⁺ : {γ : Struct 0} {P : Proc 0} →
  [] ; γ ⊢ₚ P → ¬ (Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′) → Blocked⁺ P
irreducible⇒blocked⁺ ⊢P ¬s = [ (λ b → b) , (λ s → ⊥-elim (¬s s)) ]′ (progress⁺ₚ ⊢P)

blocked⁺⇔irreducible : {γ : Struct 0} {P : Proc 0} → [] ; γ ⊢ₚ P →
  (Blocked⁺ P → ¬ (Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′)) × (¬ (Σ[ P′ ∈ Proc 0 ] P ─→ₚ P′) → Blocked⁺ P)
blocked⁺⇔irreducible ⊢P = blocked⁺⇒irreducible , irreducible⇒blocked⁺ ⊢P
