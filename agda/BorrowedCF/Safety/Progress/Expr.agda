-- Strengthened expression progress (paper Theorem "Expression progress").
--
-- `Reduction.Expressions.progress` returns `e ⋯↛`, whose `Blocked` (from
-- Reduction.Base) only asks that the head of the application be SOME term, so a
-- lambda-headed application `(ƛ e) ·⟨ d ⟩ v` counts as blocked even though E-App
-- fires on it.  The paper demands a CONSTANT head.  `progress⁺` below returns
-- exactly the paper's trichotomy: a value, an application of a constant to a
-- value under an evaluation context, or a step.
--
-- The rest of the module collects the typing-derived facts about a constant
-- application that the process-level progress proof needs.
--
-- Owner: agent F.
module BorrowedCF.Safety.Progress.Expr where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base hiding (Blocked)
open import BorrowedCF.Reduction.Expressions
open import BorrowedCF.Safety.Blocked

-- Reused (never edited): the constants' domain-shape lemmas that already exist.
open import BorrowedCF.Simulation.Support.AcqInv using (fn-acq-dom)
open import BorrowedCF.Simulation.Support.PairConfine using (fn-end-dom)
open import BorrowedCF.Simulation.Support.Theorems.DropShape using (fn-drop-dom; fn-discard-dom)

open Variables
open Fin.Patterns

--------------------------------------------------------------------------------
-- "e is a constant applied to a value, under an evaluation context."
-- This is the middle case of the paper's expression-progress theorem; `Stuck`
-- (Safety.Blocked) is the same shape with the constant restricted to a
-- `BlockingConst`.

ConstApp : Tm n → Set
ConstApp {n} e =
  Σ[ E ∈ Frame* n ] Σ[ c ∈ Const ] Σ[ d ∈ Dir ] Σ[ v ∈ Tm n ]
    Value v × e ≡ E [ K c ·⟨ d ⟩ v ]*

constApp-frame : (F : Frame n) {e : Tm n} → ConstApp e → ConstApp (F [ e ])
constApp-frame F (E , c , d , v , V , refl) = F ∷ E , c , d , v , V , refl

stuck⇒constApp : ∀ {e : Tm n} → Stuck e → ConstApp e
stuck⇒constApp (E , c , d , v , V , _ , eq) = E , c , d , v , V , eq

--------------------------------------------------------------------------------
-- Constants have unrestricted arrows, hence direction 𝟙.

const-unr : ∀ {Γ : Ctx n} {γ : Struct n} {c : Const} {T U : 𝕋} {a ϵ} →
  Γ ; γ ⊢ K c ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.Unr a
const-unr ⊢c = constFnUnr′ (inv-K ⊢c .proj₂ .proj₁) (inv-K ⊢c .proj₂ .proj₂ .proj₂)

const-app-dir : ∀ {Γ : Ctx n} {γ : Struct n} {c : Const} {d} {v : Tm n} {T ϵ} →
  Γ ; γ ⊢ K c ·⟨ d ⟩ v ∶ T ∣ ϵ → d ≡ 𝟙
const-app-dir p with inv-· p
... | a , _ , _ , _ , _ , refl , _ , T-AppUnr   a-unr ⊢c ⊢v = Arr.ω⇒𝟙 a a-unr
... | a , _ , _ , _ , _ , refl , _ , T-AppLin   a-par ⊢c ⊢v = a-par .proj₂
... | a , _ , _ , _ , _ , refl , _ , T-AppLeft  aL    ⊢c ⊢v =
  case (sym aL ■ Arr.ω⇒𝟙 a (const-unr ⊢c)) of λ()
... | a , _ , _ , _ , _ , refl , _ , T-AppRight aR    ⊢c ⊢v =
  case (sym aR ■ Arr.ω⇒𝟙 a (const-unr ⊢c)) of λ()

-- The arrow-preserving application inversion.  (`Simulation.Support.InvFrame`
-- has an `inv-app`, but it forgets the arrow, keeping only ∃[ T₁ ] for the
-- function and ∃[ T₂ ] for the argument plus a `count` bound, so it cannot link
-- the constant's domain to the argument's type.  This is a thin repackaging of
-- `Terms.Base.inv-·`.)
inv-app-fn/arg : ∀ {Γ : Ctx n} {γ : Struct n} {d} {e₁ e₂ : Tm n} {U ϵ} →
  Γ ; γ ⊢ e₁ ·⟨ d ⟩ e₂ ∶ U ∣ ϵ →
  ∃[ a ] ∃[ α ] ∃[ β ] ∃[ T ] ∃[ ϵ₁ ] ∃[ ϵ₂ ]
    Γ ; α ⊢ e₁ ∶ T ⟨ a ⟩→ U ∣ ϵ₁ × Γ ; β ⊢ e₂ ∶ T ∣ ϵ₂
inv-app-fn/arg p with inv-·  p
... | a , α , β , T , _ , _ , _ , T-AppUnr   _ ⊢f ⊢v = a , α , β , T , _ , _ , ⊢f , ⊢v
... | a , α , β , T , _ , _ , _ , T-AppLin   _ ⊢f ⊢v = a , α , β , T , _ , _ , ⊢f , ⊢v
... | a , α , β , T , _ , _ , _ , T-AppLeft  _ ⊢f ⊢v = a , α , β , T , _ , _ , ⊢f , ⊢v
... | a , α , β , T , _ , _ , _ , T-AppRight _ ⊢f ⊢v = a , α , β , T , _ , _ , ⊢f , ⊢v

--------------------------------------------------------------------------------
-- Domains of the constants, in the style of `Simulation.Support.AcqInv.fn-acq-dom`
-- (imported below) and `Simulation.Support.Theorems.DropShape.fn-drop-dom`.
-- These eight have no importable counterpart: `Position.agda` and
-- `Leaves/Choice.agda` have `fn-send-dom`, `select-fn-dom`, `branch-fn-dom` only
-- inside `where` blocks.

fn-send-dom : ∀ {Γ : Ctx n} {β : Struct n} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K `send ∶ T ⟨ a ⟩→ U ∣ ϵ → Σ[ T₀ ∈ 𝕋 ] (T₀ ⊗¹ ⟨ msg ‼ T₀ ⟩) ≃ T
fn-send-dom (T-Const (`send _))            = _ , ≃-refl
fn-send-dom (T-Conv (dom≃ `→ cod≃) _ d)    = let T₀ , eq = fn-send-dom d in T₀ , ≃-trans eq dom≃
fn-send-dom (T-Weaken _ d)                 = fn-send-dom d

fn-recv-dom : ∀ {Γ : Ctx n} {β : Struct n} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K `recv ∶ T ⟨ a ⟩→ U ∣ ϵ → Σ[ T₀ ∈ 𝕋 ] ⟨ msg ⁇ T₀ ⟩ ≃ T
fn-recv-dom (T-Const (`recv _))            = _ , ≃-refl
fn-recv-dom (T-Conv (dom≃ `→ cod≃) _ d)    = let T₀ , eq = fn-recv-dom d in T₀ , ≃-trans eq dom≃
fn-recv-dom (T-Weaken _ d)                 = fn-recv-dom d

fn-select-dom : ∀ {Γ : Ctx n} {β : Struct n} {i} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K (`select i) ∶ T ⟨ a ⟩→ U ∣ ϵ →
  Σ[ ss ∈ 𝕊 0 × 𝕊 0 ] ⟨ brn ‼ (ss .proj₁) (ss .proj₂) ⟩ ≃ T
fn-select-dom (T-Const `select)            = _ , ≃-refl
fn-select-dom (T-Conv (dom≃ `→ cod≃) _ d)  = let ss , eq = fn-select-dom d in ss , ≃-trans eq dom≃
fn-select-dom (T-Weaken _ d)               = fn-select-dom d

fn-branch-dom : ∀ {Γ : Ctx n} {β : Struct n} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K `branch ∶ T ⟨ a ⟩→ U ∣ ϵ →
  Σ[ ss ∈ 𝕊 0 × 𝕊 0 ] ⟨ brn ⁇ (ss .proj₁) (ss .proj₂) ⟩ ≃ T
fn-branch-dom (T-Const `branch)            = _ , ≃-refl
fn-branch-dom (T-Conv (dom≃ `→ cod≃) _ d)  = let ss , eq = fn-branch-dom d in ss , ≃-trans eq dom≃
fn-branch-dom (T-Weaken _ d)               = fn-branch-dom d

fn-lsplit-dom : ∀ {Γ : Ctx n} {β : Struct n} {s : 𝕊 0} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K (`lsplit s) ∶ T ⟨ a ⟩→ U ∣ ϵ → Σ[ s′ ∈ 𝕊 0 ] ⟨ s ; s′ ⟩ ≃ T
fn-lsplit-dom (T-Const (`lsplit _ _ _ _))  = _ , ≃-refl
fn-lsplit-dom (T-Conv (dom≃ `→ cod≃) _ d)  = let s′ , eq = fn-lsplit-dom d in s′ , ≃-trans eq dom≃
fn-lsplit-dom (T-Weaken _ d)               = fn-lsplit-dom d

fn-rsplit-dom : ∀ {Γ : Ctx n} {β : Struct n} {s : 𝕊 0} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K (`rsplit s) ∶ T ⟨ a ⟩→ U ∣ ϵ → Σ[ s′ ∈ 𝕊 0 ] ⟨ s ; s′ ⟩ ≃ T
fn-rsplit-dom (T-Const (`rsplit _ _ _ _))  = _ , ≃-refl
fn-rsplit-dom (T-Conv (dom≃ `→ cod≃) _ d)  = let s′ , eq = fn-rsplit-dom d in s′ , ≃-trans eq dom≃
fn-rsplit-dom (T-Weaken _ d)               = fn-rsplit-dom d

fn-new-dom : ∀ {Γ : Ctx n} {β : Struct n} {s : 𝕊 0} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K (`new s) ∶ T ⟨ a ⟩→ U ∣ ϵ → `⊤ ≃ T
fn-new-dom (T-Const (`new _))              = ≃-refl
fn-new-dom (T-Conv (dom≃ `→ cod≃) _ d)     = ≃-trans (fn-new-dom d) dom≃
fn-new-dom (T-Weaken _ d)                  = fn-new-dom d

fn-fork-dom : ∀ {Γ : Ctx n} {β : Struct n} {T U : 𝕋} {a ϵ} →
  Γ ; β ⊢ K `fork ∶ T ⟨ a ⟩→ U ∣ ϵ → (`⊤ →1M `⊤ ∣ 𝕀) ≃ T
fn-fork-dom (T-Const `fork)                = ≃-refl
fn-fork-dom (T-Conv (dom≃ `→ cod≃) _ d)    = ≃-trans (fn-fork-dom d) dom≃
fn-fork-dom (T-Weaken _ d)                 = fn-fork-dom d

--------------------------------------------------------------------------------

module _ {n} {Γ : Ctx n} (Γ-S : ChanCx Γ) where

  ------------------------------------------------------------------------------
  -- Strengthened progress.

  progress⁺ : ∀ {γ : Struct n} {e : Tm n} {T : 𝕋} {ϵ : Eff} → Γ ; γ ⊢ e ∶ T ∣ ϵ →
    Value e ⊎ ConstApp e ⊎ (∃[ e′ ] e ⋯→ e′)
  progress⁺ (T-Const x)                   = inj₁ V-K
  progress⁺ (T-Var x T-eq)                = inj₁ V-`
  progress⁺ (T-Abs Γ-unr Γ-mob e)         = inj₁ V-λ
  progress⁺ (T-AbsRec Γ-unr a-unr e)      = inj₂ (inj₂ (_ , E-□ E-Unfold))
  progress⁺ (T-AppUnr unr-a ≤ₐ e₁ e₂)
    with progress⁺ e₁
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₁ _ 𝟙 λ()) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (app₁ _ 𝟙 λ()) e₁→))
  ... | inj₁ V-e₁
    with progress⁺ e₂
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₂ _ 𝟙 λ _ → V-e₁) ca))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (app₂ _ 𝟙 λ _ → V-e₁) e₂→))
  ... | inj₁ V-e₂
    with inv-arr Γ-S V-e₁ e₁
  ... | _ , _ , _ , _ , _ , _ , inj₁ (c , refl , _) = inj₂ (inj₁ ([] , c , 𝟙 , _ , V-e₂ , refl))
  ... | _ , _ , _ , _ , _ , _ , inj₂ (_ , refl , _) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress⁺ (T-AppLin lin-a ≤ₐ e₁ e₂)
    with progress⁺ e₁
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₁ _ 𝟙 λ()) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (app₁ _ 𝟙 λ()) e₁→))
  ... | inj₁ V-e₁
    with progress⁺ e₂
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₂ _ 𝟙 λ _ → V-e₁) ca))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (app₂ _ 𝟙 λ _ → V-e₁) e₂→))
  ... | inj₁ V-e₂
    with inv-arr Γ-S V-e₁ e₁
  ... | _ , _ , _ , _ , _ , _ , inj₁ (c , refl , _) = inj₂ (inj₁ ([] , c , 𝟙 , _ , V-e₂ , refl))
  ... | _ , _ , _ , _ , _ , _ , inj₂ (_ , refl , _) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress⁺ (T-AppLeft a-L ≤ₐ e₁ e₂)
    with progress⁺ e₂
  ... | inj₂ (inj₁ ca)       = inj₂ (inj₁ (constApp-frame (app₂ _ L (λ{ (inj₁ ()); (inj₂ ()) })) ca))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx (app₂ _ L (λ{ (inj₁ ()); (inj₂ ()) })) e→))
  ... | inj₁ V₂
    with progress⁺ e₁
  ... | inj₂ (inj₁ ca)       = inj₂ (inj₁ (constApp-frame (app₁ _ L (λ _ → V₂)) ca))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx (app₁ _ L (λ _ → V₂)) e→))
  ... | inj₁ V₁
    with inv-arr Γ-S V₁ e₁
  ... | _ , _ , _ , _ , _ , _ , inj₁ (c , refl , _) = inj₂ (inj₁ ([] , c , L , _ , V₂ , refl))
  ... | _ , _ , _ , _ , _ , _ , inj₂ (_ , refl , _) = inj₂ (inj₂ (_ , E-□ (E-App V₂)))
  progress⁺ (T-AppRight a-R ≤ₐ e₁ e₂)
    with progress⁺ e₁
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₁ _ R λ()) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (app₁ _ R λ()) e₁→))
  ... | inj₁ V-e₁
    with progress⁺ e₂
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (app₂ _ R λ _ → V-e₁) ca))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (app₂ _ R λ _ → V-e₁) e₂→))
  ... | inj₁ V-e₂
    with inv-arr Γ-S V-e₁ e₁
  ... | _ , _ , _ , _ , _ , _ , inj₁ (c , refl , _) = inj₂ (inj₁ ([] , c , R , _ , V-e₂ , refl))
  ... | _ , _ , _ , _ , _ , _ , inj₂ (_ , refl , _) = inj₂ (inj₂ (_ , E-□ (E-App V-e₂)))
  progress⁺ (T-Pair p/s seq⇒pure e₁ e₂)
    with progress⁺ e₁
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (□⊗ _) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□⊗ _) e₁→))
  ... | inj₁ V-e₁
    with progress⁺ e₂
  ... | inj₁ V-e₂             = inj₁ (V-⊗ V-e₁ V-e₂)
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (V-e₁ ⊗□) ca))
  ... | inj₂ (inj₂ (_ , e₂→)) = inj₂ (inj₂ (_ , E-Ctx (V-e₁ ⊗□) e₂→))
  progress⁺ (T-Let p/s e e′)
    with progress⁺ e
  ... | inj₁ V-e              = inj₂ (inj₂ (_ , E-□ (E-Let V-e)))
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (`let-`in _) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (`let-`in _) e₁→))
  progress⁺ (T-Seq unr-T e e′)
    with progress⁺ e
  ... | inj₁ V-e              = inj₂ (inj₂ (_ , E-□ (E-Seq V-e)))
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (□; _) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (□; _) e₁→))
  progress⁺ (T-LetPair p/s e e′)
    with progress⁺ e
  ... | inj₂ (inj₁ ca)        = inj₂ (inj₁ (constApp-frame (`let⊗-`in _) ca))
  ... | inj₂ (inj₂ (_ , e₁→)) = inj₂ (inj₂ (_ , E-Ctx (`let⊗-`in _) e₁→))
  ... | inj₁ V-e
    with _ , _ , refl ← value×⊗⇒⊗ Γ-S V-e e
    with V-⊗ V₁ V₂ ← V-e
    = inj₂ (inj₂ (_ , E-□ (E-PairElim V₁ V₂)))
  progress⁺ (T-Inj e)
    with progress⁺ e
  ... | inj₁ V-e             = inj₁ (V-⊕ V-e)
  ... | inj₂ (inj₁ ca)       = inj₂ (inj₁ (constApp-frame (`inj□ _) ca))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx (`inj□ _) e→))
  progress⁺ (T-Case p/s e e₁ e₂)
    with progress⁺ e
  ... | inj₂ (inj₁ ca)       = inj₂ (inj₁ (constApp-frame `case□`of⟨ _ ; _ ⟩ ca))
  ... | inj₂ (inj₂ (_ , e→)) = inj₂ (inj₂ (_ , E-Ctx `case□`of⟨ _ ; _ ⟩ e→))
  ... | inj₁ V-e
    with _ , _ , refl ← value×⊕⇒`inj Γ-S V-e e
    with V-⊕ V ← V-e
    = inj₂ (inj₂ (_ , E-□ (E-SumElim V)))
  progress⁺ (T-Weaken γ≤ e)  = progress⁺ e
  progress⁺ (T-Conv eq ϵ≤ e) = progress⁺ e

  ------------------------------------------------------------------------------
  -- Shape of the argument of a constant application.
  --
  -- `handle-arg` is the common pattern: whenever the constant's domain is a
  -- handle type ⟨ shape w ⟩, a *value* argument must be a variable, and the
  -- context assigns it a session equivalent to `shape w`.

  handle-arg : ∀ {A : Set} {shape : A → 𝕊 0} {γ : Struct n} {c : Const} {d}
                 {v : Tm n} {T ϵ} →
    Value v →
    Γ ; γ ⊢ K c ·⟨ d ⟩ v ∶ T ∣ ϵ →
    (dom : ∀ {γ′ : Struct n} {T′ U : 𝕋} {a ϵ′} →
             Γ ; γ′ ⊢ K c ∶ T′ ⟨ a ⟩→ U ∣ ϵ′ → Σ[ w ∈ A ] ⟨ shape w ⟩ ≃ T′) →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ w ∈ A ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ shape w
  handle-arg V p dom
    with _ , _ , _ , _ , _ , _ , ⊢c , ⊢v ← inv-app-fn/arg p
    with w , eq ← dom ⊢c
    with s′ , x , s≃ , refl , Γx , _ ← inv-session Γ-S V (T-Conv (≃-sym eq) ≤ϵ-refl ⊢v)
    = x , s′ , w , refl , Γx , ≃-sym s≃

  -- `send` is the only blocking constant whose argument is a pair.
  arg-send : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `send ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ v₀ ∈ Tm n ] Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ T₀ ∈ 𝕋 ]
      Value v₀ × v ≡ v₀ ⊗ (` x) × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ msg ‼ T₀
  arg-send V p
    with _ , _ , _ , _ , _ , _ , ⊢send , ⊢v ← inv-app-fn/arg p
    with T₀ , eq ← fn-send-dom ⊢send
    with ⊢v′ ← T-Conv (≃-sym eq) ≤ϵ-refl ⊢v
    with _ , _ , refl ← value×⊗⇒⊗ Γ-S V ⊢v′
    with V-⊗ V₁ V₂ ← V
    with _ , _ , _ , _ , _ , _ , _ , _ , ⊗≃ , _ , _ , ⊢v₁ , ⊢v₂ ← inv-⊗ ⊢v′
    with eq₁ , _ , eq₂ ← ≃-⊗⁻¹ ⊗≃
    with s′ , x , s≃ , refl , Γx , _ ← inv-session Γ-S V₂ (T-Conv eq₂ ≤ϵ-refl ⊢v₂)
    = _ , x , s′ , T₀ , V₁ , refl , Γx , ≃-sym s≃

  arg-recv : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `recv ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ T₀ ∈ 𝕋 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ msg ⁇ T₀
  arg-recv V p = handle-arg V p (λ ⊢c → fn-recv-dom ⊢c)

  arg-select : ∀ {γ : Struct n} {i} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K (`select i) ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ ss ∈ 𝕊 0 × 𝕊 0 ]
      v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ brn ‼ (ss .proj₁) (ss .proj₂)
  arg-select V p = handle-arg V p (λ ⊢c → fn-select-dom ⊢c)

  arg-branch : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `branch ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ ss ∈ 𝕊 0 × 𝕊 0 ]
      v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ brn ⁇ (ss .proj₁) (ss .proj₂)
  arg-branch V p = handle-arg V p (λ ⊢c → fn-branch-dom ⊢c)

  arg-end : ∀ {γ : Struct n} {p₀ : Pol} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K (`end p₀) ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ end p₀
  arg-end {p₀ = p₀} V p
    with x , s , _ , eq , Γx , s≃ ← handle-arg {A = ⊤} {shape = λ _ → end p₀} V p (λ ⊢c → tt , fn-end-dom ⊢c)
    = x , s , eq , Γx , s≃

  arg-acq : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `acq ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ s₀ ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ acq ; s₀
  arg-acq V p = handle-arg V p (λ ⊢c → fn-acq-dom ⊢c)

  -- The non-blocking constants, recorded for the process-level proof.

  arg-drop : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `drop ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ ret
  arg-drop V p
    with x , s , _ , eq , Γx , s≃ ← handle-arg {A = ⊤} {shape = λ _ → ret} V p (λ ⊢c → tt , fn-drop-dom ⊢c)
    = x , s , eq , Γx , s≃

  arg-discard : ∀ {γ : Struct n} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K `discard ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ skip
  arg-discard V p
    with x , s , _ , eq , Γx , s≃ ← handle-arg {A = ⊤} {shape = λ _ → skip} V p (λ ⊢c → tt , fn-discard-dom ⊢c)
    = x , s , eq , Γx , s≃

  arg-lsplit : ∀ {γ : Struct n} {s₀ : 𝕊 0} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K (`lsplit s₀) ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ s′ ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ s₀ ; s′
  arg-lsplit V p = handle-arg V p (λ ⊢c → fn-lsplit-dom ⊢c)

  arg-rsplit : ∀ {γ : Struct n} {s₀ : 𝕊 0} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K (`rsplit s₀) ·⟨ d ⟩ v ∶ T ∣ ϵ →
    Σ[ x ∈ 𝔽 n ] Σ[ s ∈ 𝕊 0 ] Σ[ s′ ∈ 𝕊 0 ] v ≡ ` x × Γ ﹫ x ≡ ⟨ s ⟩ × s ≃ s₀ ; s′
  arg-rsplit V p = handle-arg V p (λ ⊢c → fn-rsplit-dom ⊢c)

  arg-new : ∀ {γ : Struct n} {s₀ : 𝕊 0} {d} {v : Tm n} {T ϵ} →
    Value v → Γ ; γ ⊢ K (`new s₀) ·⟨ d ⟩ v ∶ T ∣ ϵ → v ≡ K `unit
  arg-new V p
    with _ , _ , _ , _ , _ , _ , ⊢new , ⊢v ← inv-app-fn/arg p
    = inv-`⊤ Γ-S V (T-Conv (≃-sym (fn-new-dom ⊢new)) ≤ϵ-refl ⊢v) .proj₁

  ------------------------------------------------------------------------------
  -- A stuck thread contributes a channel to BC (or, for `acq`, to AC).

  stuck⇒∈BC/AC : ∀ {γ : Struct n} {T ϵ} (E : Frame* n) {c : Const} {d} {v : Tm n} →
    Value v → BlockingConst c →
    Γ ; γ ⊢ E [ K c ·⟨ d ⟩ v ]* ∶ T ∣ ϵ →
    (∃[ x ] x ∈BCe (E [ K c ·⟨ d ⟩ v ]*)) ⊎ (∃[ x ] x ∈ACe (E [ K c ·⟨ d ⟩ v ]*))
  stuck⇒∈BC/AC E V B-send ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with _ , x , _ , _ , V₀ , refl , _ , _ ← arg-send V ⊢r
    = inj₁ (x , send E V₀)
  stuck⇒∈BC/AC E V B-recv ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with x , _ , _ , refl , _ , _ ← arg-recv V ⊢r
    = inj₁ (x , recv E)
  stuck⇒∈BC/AC E V (B-select i) ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with x , _ , _ , refl , _ , _ ← arg-select V ⊢r
    = inj₁ (x , select E i)
  stuck⇒∈BC/AC E V B-branch ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with x , _ , _ , refl , _ , _ ← arg-branch V ⊢r
    = inj₁ (x , branch E)
  stuck⇒∈BC/AC E V (B-end p₀) ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with x , _ , refl , _ , _ ← arg-end V ⊢r
    = inj₁ (x , end E p₀)
  stuck⇒∈BC/AC E V B-acq ⊢e
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with x , _ , _ , refl , _ , _ ← arg-acq V ⊢r
    = inj₂ (x , acq E)
