module BorrowedCF.TermsNoKits where

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Relation.Binary.Construct.Closure.Equivalence as Eq* using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using (ε; _◅_; _◅◅_; kleisliStar)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (symmetric)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Modes
open import BorrowedCF.Types hiding (s; s₁; s₂; s₃; s′)
open import BorrowedCF.Renaming

open Nat.Variables

data Const : Set where
  `unit `fork `send `recv `drop `acq `end : Const
  `new : 𝕊 0 → Const
  `lsplit `rsplit : (s₁ s₂ : 𝕊 0) → Const

data Tm (n : ℕ) : Set where
  -- Terms
  `_ : 𝔽 n → Tm n
  K : (c : Const) → Tm n
  λ[_] : (d : Dir) (e : Tm (1 + n)) → Tm n
  _·_ : (e₁ e₂ : Tm n) → Tm n
  _;_ : (e₁ e₂ : Tm n) → Tm n
  _,⟨_⟩_ : (e₁ : Tm n) (d : Dir) (e₂ : Tm n) → Tm n
  `let_`in_ : (e₁ : Tm n) (e₂ : Tm (1 + n)) → Tm n
  `let⊗_`in_ : (e₁ : Tm n) (e₂ : Tm (2 + n)) → Tm n

infixl 5 _⋯ᵣ_

_⋯ᵣ_ : Tm m → Ren m n → Tm n
(` x) ⋯ᵣ ρ = ` ρ x
K c ⋯ᵣ ρ = K c
λ[ d ] e ⋯ᵣ ρ = λ[ d ] (e ⋯ᵣ ↑ ρ)
(e · e₁) ⋯ᵣ ρ = (e ⋯ᵣ ρ) · (e₁ ⋯ᵣ ρ)
e ; e₁ ⋯ᵣ ρ =  (e ⋯ᵣ ρ) ; (e₁ ⋯ᵣ ρ)
(e ,⟨ d ⟩ e₁) ⋯ᵣ ρ =  (e ⋯ᵣ ρ) ,⟨ d ⟩ (e₁ ⋯ᵣ ρ)
(`let e `in e₁) ⋯ᵣ ρ = `let (e ⋯ᵣ ρ) `in (e₁ ⋯ᵣ ↑ ρ)
(`let⊗ e `in e₁) ⋯ᵣ ρ = `let⊗ (e ⋯ᵣ ρ) `in (e₁ ⋯ᵣ ↑ ↑ ρ)

⋯-id : (e : Tm n) → ρ ≗ id → e ⋯ᵣ ρ ≡ e
⋯-id (` x) ρ≗id = cong `_ (ρ≗id x)
⋯-id (K c) ρ≗id = refl
⋯-id (λ[ d ] e) ρ≗id = cong λ[ d ] (⋯-id e (↑-id ρ≗id))
⋯-id (e · e₁) ρ≗id = cong₂ _·_ (⋯-id e ρ≗id) (⋯-id e₁ ρ≗id)
⋯-id (e ; e₁) ρ≗id = cong₂ _;_ (⋯-id e ρ≗id) (⋯-id e₁ ρ≗id)
⋯-id (e ,⟨ d ⟩ e₁) ρ≗id = cong₂ (_,⟨ d ⟩_) (⋯-id e ρ≗id) (⋯-id e₁ ρ≗id)
⋯-id (`let e `in e₁) ρ≗id = cong₂ `let_`in_ (⋯-id e ρ≗id) (⋯-id e₁ (↑-id ρ≗id))
⋯-id (`let⊗ e `in e₁) ρ≗id = cong₂ `let⊗_`in_ (⋯-id e ρ≗id) (⋯-id e₁ (↑⋆-id 2 ρ≗id))

⋯-cong : (e : Tm n) → ρ₁ ≗ ρ₂ → e ⋯ᵣ ρ₁ ≡ e ⋯ᵣ ρ₂
⋯-cong (` x) ρ≗ = cong `_ (ρ≗ x)
⋯-cong (K c) ρ≗ = refl
⋯-cong (λ[ d ] e) ρ≗ = cong λ[ d ] (⋯-cong e (↑-pres-≗ ρ≗))
⋯-cong (e · e₁) ρ≗ = cong₂ _·_ (⋯-cong e ρ≗) (⋯-cong e₁ ρ≗)
⋯-cong (e ; e₁) ρ≗ = cong₂ _;_ (⋯-cong e ρ≗) (⋯-cong e₁ ρ≗)
⋯-cong (e ,⟨ d ⟩ e₁) ρ≗ = cong₂ (_,⟨ d ⟩_) (⋯-cong e ρ≗) (⋯-cong e₁ ρ≗)
⋯-cong (`let e `in e₁) ρ≗ = cong₂ `let_`in_ (⋯-cong e ρ≗) (⋯-cong e₁ (↑-pres-≗ ρ≗))
⋯-cong (`let⊗ e `in e₁) ρ≗ = cong₂ `let⊗_`in_ (⋯-cong e ρ≗) (⋯-cong e₁ (↑⋆-pres-≗ 2 ρ≗))



-- fusion :
--   ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄
--   (x : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → (x ⋯ ϕ₁) ⋯ ϕ₂ ≡ x ⋯ (ϕ₁ ·ₖ ϕ₂)
-- fusion (` x) ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
-- fusion (x₁ ; x₂) ϕ₁ ϕ₂ = cong₂ _;_ (fusion x₁ ϕ₁ ϕ₂) (fusion x₂ ϕ₁ ϕ₂)
-- fusion (K c) ϕ₁ ϕ₂ = refl
-- fusion (λ[ d ] e) ϕ₁ ϕ₂ = cong λ[ d ] $
--   fusion e (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ■ cong (e ⋯_) (sym (∼-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂)))
-- fusion (e₁ · e₂) ϕ₁ ϕ₂ = cong₂ _·_ (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
-- fusion (e₁ ,⟨ d ⟩ e₂) ϕ₁ ϕ₂ = cong₂ (_,⟨ d ⟩_) (fusion e₁ ϕ₁ ϕ₂) (fusion e₂ ϕ₁ ϕ₂)
-- fusion (`let e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let_`in_ (fusion e₁ ϕ₁ ϕ₂) $
--   fusion e₂ (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖)
--     ■ (cong (e₂ ⋯_) (sym (∼-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))))
-- fusion (`let⊗ e₁ `in e₂) ϕ₁ ϕ₂ = cong₂ `let⊗_`in_ (fusion e₁ ϕ₁ ϕ₂) $
--   fusion e₂ (ϕ₁ ↑* [2* 𝕖 ]) (ϕ₂ ↑* [2* 𝕖 ])
--     ■ cong (e₂ ⋯_) (sym (∼-ext (dist-↑*-· [2* 𝕖 ] ϕ₁ ϕ₂)))
-- fusion ⟨ t ⟩ ϕ₁ ϕ₂ = refl

-- open module CTraversal = Traversal.CTraversal record { fusion = fusion }
--   hiding (fusion; Types)
--   public

-- open module Types = CTraversal.Types record { ↑ᵗ = λ x → _ , 𝕥 }
--   hiding (Typing)
--   renaming (lookup to lookupCx)
--   public

-- variable
--   Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx S
--   T T₁ T₂ T₃ T′ : S ∶⊢ s

-- infixl 5 _⋯𝓢_

-- _⋯𝓢_ : Struct S → S →ᵣ S′ → Struct S′
-- ` x ⋯𝓢 ρ = ` ρ _ x
-- [] ⋯𝓢 ρ = []
-- x ∥ y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ∥ (y ⋯𝓢 ρ)
-- x ; y ⋯𝓢 ρ = (x ⋯𝓢 ρ) ; (y ⋯𝓢 ρ)

-- lookup-𝕋 : Ctx S → s ∈ S → 𝕋
-- lookup-𝕋 Γ x with ⟨ t ⟩ ← lookupCx Γ x = t

-- lookupCx≡⟨lookup-𝕋⟩ : (Γ : Ctx S) (x : 𝕖 ∈ S) → lookupCx Γ x ≡ ⟨ lookup-𝕋 Γ x ⟩
-- lookupCx≡⟨lookup-𝕋⟩ Γ x with ⟨ t ⟩ ← lookupCx Γ x = refl

-- data MobCx {S} (Γ : Ctx S) : Struct S → Set where
--   []  : MobCx Γ []
--   _∥_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ∥ α₂)
--   _;_ : MobCx Γ α₁ → MobCx Γ α₂ → MobCx Γ (α₁ ; α₂)
--   `_  : Mobile (lookup-𝕋 Γ x) → MobCx Γ (` x)

-- joinP/S : ParSeq → Struct S → Struct S → Struct S
-- joinP/S par = _∥_
-- joinP/S seq = _;_

-- joinDir : Dir → Struct S → Struct S → Struct S
-- joinDir 𝟙 = _∥_
-- joinDir L = _;_
-- joinDir R = flip _;_

-- Split : Dir → Struct S → Struct S → Struct S → Set
-- Split d α α₁ α₂ = α ≈ joinDir d α₁ α₂

-- infix 4 ⊢_∶_

-- private
--   _→m,1_∣_ : 𝕋 → 𝕋 → Eff → 𝕋
--   t →m,1 u ∣ ϵ = arr mob 𝟙 ϵ t u

-- data ⊢_∶_ : Const → 𝕋 → Set where
--   `unit : ⊢ `unit ∶ unit
--   `new : ∀ {s} → ⊢ `new s ∶ arr mob 𝟙 ϵ unit (pair 𝟙 ⟨ acq ; s ⟩ ⟨ acq ; dual s ⟩)
--   `lsplit : ∀ {s₁ s₂} → ⊢ `lsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair L ⟨ s₁ ⟩ ⟨ s₂ ⟩)
--   `rsplit : ∀ {s₁ s₂} → ⊢ `rsplit s₁ s₂ ∶ arr mob 𝟙 ϵ ⟨ s₁ ; s₂ ⟩ (pair 𝟙 ⟨ s₁ ; ret ⟩ ⟨ acq ; s₂ ⟩)
--   `drop : ⊢ `drop ∶ arr mob 𝟙 ϵ ⟨ ret ⟩ unit
--   `acq : ∀ {s} → ⊢ `acq ∶ ⟨ acq ; s ⟩ →m,1 ⟨ s ⟩ ∣ ϵ
--   `fork : ⊢ `fork ∶ (unit →m,1 unit ∣ 𝕀) →m,1 unit ∣ ϵ
--   `send : ∀ {t} → Mobile t → ⊢ `send ∶ pair 𝟙 t ⟨ msg ‼ t ⟩ →m,1 unit ∣ 𝕀
--   `recv : ∀ {t} → Mobile t → ⊢ `recv ∶ ⟨ msg ⁇ t ⟩ →m,1 t ∣ 𝕀
--   `end : ⊢ `end ∶ ⟨ end p ⟩ →m,1 unit ∣ 𝕀

-- infix 4 _;_⊢_∶_∣_

-- data _;_⊢_∶_∣_ {S} (Γ : Ctx S) (γ : Struct S) : S ⊢ 𝕖 → 𝕋 → Eff → Set where
--   T-Const : ∀ {c t} →
--     γ ≈ [] →
--     ⊢ c ∶ t →
--     -------------------
--     Γ ; γ ⊢ K c ∶ t ∣ ϵ

--   T-Var : ∀ {x t} →
--     γ ≈ ` x →
--     lookupCx Γ x ≡ ⟨ t ⟩ →
--     ----------------------
--     Γ ; γ ⊢ ` x ∶ t ∣ ϵ

--   T-Abs : ∀ {e t u} →
--     (𝓂 ≡ mob → MobCx Γ α) →
--     ⟨ t ⟩ ∷ Γ ; joinDir d (` here refl) (γ ⋯𝓢 weaken _) ⊢ e ∶ u ∣ ϵ′ →
--     -----------------------------------------------------------------
--     Γ ; γ ⊢ λ[ 𝟙 ] e ∶ arr 𝓂 d ϵ′ t u ∣ ϵ

--   T-App : ∀ {e₁ e₂ t u} →
--     Split d γ γ₁ γ₂                 →
--     Γ ; γ₁ ⊢ e₁ ∶ arr 𝓂 d ϵ t u ∣ ϵ →
--     Γ ; γ₂ ⊢ e₂ ∶ t             ∣ ϵ →
--     ---------------------------------
--     Γ ; γ ⊢ e₁ · e₂ ∶ u ∣ ϵ

--   T-Let : ∀ {e₁ e₂ t u} (p/s : ParSeq) →
--     γ ≈ joinP/S p/s γ₁ γ₂ →
--     Γ ; γ₁ ⊢ e₁ ∶ t ∣ ϵ →
--     ⟨ t ⟩ ∷ Γ ; joinP/S p/s (` here refl) (γ₂ ⋯𝓢 weaken _) ⊢ e₂ ∶ u ∣ ϵ →
--     ---------------------------------------------------------------------
--     Γ ; γ ⊢ `let e₁ `in e₂ ∶ u ∣ ϵ

--   T-LetUnit : ∀ {e₁ e₂ t} (p/s : ParSeq) →
--     γ ≈ joinP/S p/s γ₁ γ₂ →
--     Γ ; γ₁ ⊢ e₁ ∶ unit ∣ ϵ →
--     Γ ; γ₂ ⊢ e₂ ∶ t    ∣ ϵ →
--     ---------------------------------------
--     Γ ; γ ⊢ e₁ ; e₂ ∶ t ∣ ϵ

--   T-LetPair : ∀ {e₁ e₂ t₁ t₂ u} (p/s : ParSeq) →
--     γ ≈ joinP/S p/s γ₁ γ₂ →
--     Γ ; γ₁ ⊢ e₁ ∶ pair d t₁ t₂ ∣ ϵ →
--     ⟨ t₁ ⟩ ∷ ⟨ t₂ ⟩ ∷ Γ ;
--       joinP/S p/s (joinDir d (` here refl) (` there (here refl)))
--                   (γ₂ ⋯𝓢 weaken* [2* 𝕖 ])
--       ⊢ e₂ ∶ u ∣ ϵ →
--     ---------------------------------------
--     Γ ; γ ⊢ `let⊗ e₁ `in e₂ ∶ u ∣ ϵ

-- record TKit (K : Kit _∋/⊢_) : Set₁ where
--   private instance _ = K
--   infix 4 _∋/⊢_∶_ _∶_;_⇒_;_
--   infixl 6 _⊢↑_

-- --  field _∋/⊢_∶_

--   _∶_;_⇒_;_ : S₁ –[ K ]→ S₂ → Ctx S₁ → Struct S₁ → Ctx S₂ → Struct S₂ → Set
--   _∶_;_⇒_;_ {S₁} {S₂} ϕ Γ₁ γ₁ Γ₂ γ₂ = {!(x : 𝕖 ∈ S₁) (t : 𝕋) → Γ₁ !}

-- -- infix 4 _⊢_∶_

-- -- data _⊢_∶_ (Γ : Ctx S) : S ⊢ s → S ∶⊢ s → Set where
-- --   ⟨_⟩ : ∀ {e t} → Γ ; γ ⊢ e ∶ t ∣ ϵ → Γ ⊢ e ∶ ⟨ t ⟩

-- -- open module Typing = Types.Typing record
-- --   { _⊢_∶_ = λ Γ e t → Γ ⊢ e ∶ t
-- --   ; ⊢` = λ{ {s = 𝕖} {Γ = Γ} {x} refl →
-- --                subst (λ t → Γ ⊢ ` x ∶ t)
-- --                      (sym (lookupCx≡⟨lookup-𝕋⟩ Γ x))
-- --                      ⟨ T-Var {ϵ = ℙ} (Eq*.reflexive _) (lookupCx≡⟨lookup-𝕋⟩ Γ x) ⟩
-- --          }
-- --   }
-- --   hiding (_⊢_∶_)
-- --   public

-- -- ⟨_⟩⊢⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
-- --        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
-- --        {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
-- --        {e : S₁ ⊢ 𝕖} {t : 𝕋} {ϕ : S₁ –[ K ]→ S₂} →
-- --        Γ₁ ; γ₁ ⊢ e ∶ t ∣ ϵ →
-- --        ϕ ∶ Γ₁ ⇒ₖ Γ₂ →
-- --        Γ₂ ; γ₂ ⊢ e ⋯ ϕ ∶ t ∣ ϵ
-- -- ⟨ T-Const x x₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-Var x x₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-Abs x e ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-App γ e₁ e₂ ⟩⊢⋯ ⊢ϕ = T-App {!!} {!!} {!!}
-- -- ⟨ T-Let p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-LetUnit p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}
-- -- ⟨ T-LetPair p/s x e e₁ ⟩⊢⋯ ⊢ϕ = {!!}

-- -- _⊢⋯_ : ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
-- --        ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
-- --        {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
-- --        {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
-- --        Γ₁ ⊢ e ∶ t →
-- --        ϕ ∶ Γ₁ ⇒ₖ Γ₂ →
-- --        Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
-- -- ⟨ e ⟩ ⊢⋯ ⊢ϕ = ⟨ {!⟨ e ⟩ ⊢⋯ ⊢ϕ!} ⟩
