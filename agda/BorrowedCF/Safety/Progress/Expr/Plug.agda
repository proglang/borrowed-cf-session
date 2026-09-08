-- Evaluation-context plugging as a *structural* relation.
--
-- `Reduction.Base` represents an evaluation context as a list of frames
-- `E : Frame* n` and plugs with `E [ e ]*`.  That representation is convenient
-- for stating rules, but it is useless for deciding statements of the form
--
--     ∃[ E ] e ≡ E [ r ]*
--
-- because `E [ r ]*` is a stuck function application, so Agda's unifier cannot
-- case-split on it.  `Plug Red e` below is the same relation presented with one
-- constructor per *term* former; every index is a constructor application, so
-- inversion, decidability and renaming inversion are plain structural
-- recursions.  `plug⇒ctx` / `plug-frame*` translate between the two views.
--
-- Owned by agent F (Safety/Blocked.agda, Safety/Progress/Expr.agda).
module BorrowedCF.Safety.Progress.Expr.Plug where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Reduction.Base

open Variables
open Fin.Patterns

private variable
  Red Red′ : ∀ {n} → Tm n → Set

--------------------------------------------------------------------------------
-- Values are decidable.

value? : (e : Tm n) → Dec (Value e)
value? (` x)                    = yes V-`
value? (K c)                    = yes V-K
value? (ƛ e)                    = yes V-λ
value? (μ e)                    = no λ()
value? (e₁ ·⟨ d ⟩ e₂)           = no λ()
value? (e₁ ; e₂)                = no λ()
value? (`let e₁ `in e₂)         = no λ()
value? (`let⊗ e₁ `in e₂)        = no λ()
value? (`case e `of⟨ e₁ ; e₂ ⟩) = no λ()
value? (e₁ ⊗ e₂) with value? e₁ ×? value? e₂
... | yes (V₁ , V₂) = yes (V-⊗ V₁ V₂)
... | no ¬V         = no λ{ (V-⊗ V₁ V₂) → ¬V (V₁ , V₂) }
value? (`inj i e) with value? e
... | yes V = yes (V-⊕ V)
... | no ¬V = no λ{ (V-⊕ V) → ¬V V }

-- The two side conditions carried by the application frames.

app₁-cond? : (d : Dir) (e : Tm n) → Dec (d ≡ L → Value e)
app₁-cond? R e = yes λ()
app₁-cond? 𝟙 e = yes λ()
app₁-cond? L e with value? e
... | yes V = yes λ _ → V
... | no ¬V = no λ f → ¬V (f refl)

app₂-cond? : (d : Dir) (e : Tm n) → Dec (d ≡ 𝟙 ⊎ d ≡ R → Value e)
app₂-cond? L e = yes λ{ (inj₁ ()) ; (inj₂ ()) }
app₂-cond? R e with value? e
... | yes V = yes λ _ → V
... | no ¬V = no λ f → ¬V (f (inj₂ refl))
app₂-cond? 𝟙 e with value? e
... | yes V = yes λ _ → V
... | no ¬V = no λ f → ¬V (f (inj₁ refl))

--------------------------------------------------------------------------------
-- `Plug Red e`: some subterm of `e`, sitting under a chain of evaluation
-- frames, satisfies `Red`.

data Plug {n} (Red : Tm n → Set) : Tm n → Set where
  here  : ∀ {e : Tm n} → Red e → Plug Red e

  appˡ  : ∀ {e₁ e₂ : Tm n} {d} → (d ≡ L → Value e₂) →
          Plug Red e₁ → Plug Red (e₁ ·⟨ d ⟩ e₂)
  appʳ  : ∀ {e₁ e₂ : Tm n} {d} → (d ≡ 𝟙 ⊎ d ≡ R → Value e₁) →
          Plug Red e₂ → Plug Red (e₁ ·⟨ d ⟩ e₂)
  pairˡ : ∀ {e₁ e₂ : Tm n} → Plug Red e₁ → Plug Red (e₁ ⊗ e₂)
  pairʳ : ∀ {e₁ e₂ : Tm n} → Value e₁ → Plug Red e₂ → Plug Red (e₁ ⊗ e₂)
  seqˡ  : ∀ {e₁ e₂ : Tm n} → Plug Red e₁ → Plug Red (e₁ ; e₂)
  letˡ  : ∀ {e₁ : Tm n} {e₂ : Tm (suc n)} → Plug Red e₁ → Plug Red (`let e₁ `in e₂)
  let⊗ˡ : ∀ {e₁ : Tm n} {e₂ : Tm (suc (suc n))} → Plug Red e₁ → Plug Red (`let⊗ e₁ `in e₂)
  injˡ  : ∀ {i} {e : Tm n} → Plug Red e → Plug Red (`inj i e)
  caseˡ : ∀ {e : Tm n} {e₁ e₂ : Tm (suc n)} → Plug Red e → Plug Red (`case e `of⟨ e₁ ; e₂ ⟩)

--------------------------------------------------------------------------------
-- Translation to and from `Frame*`.

plug-frame : ∀ {Red : Tm n → Set} (F : Frame n) {e} → Plug Red e → Plug Red (F [ e ])
plug-frame (app₁ e d V?)           p = appˡ V? p
plug-frame (app₂ e d V?)           p = appʳ V? p
plug-frame (□⊗ e₂)                 p = pairˡ p
plug-frame (V₁ ⊗□)                 p = pairʳ V₁ p
plug-frame (□; e₂)                 p = seqˡ p
plug-frame (`let-`in e′)           p = letˡ p
plug-frame (`let⊗-`in e′)          p = let⊗ˡ p
plug-frame (`inj□ i)               p = injˡ p
plug-frame `case□`of⟨ e₁ ; e₂ ⟩    p = caseˡ p

plug-frame* : ∀ {Red : Tm n → Set} (E : Frame* n) {e} → Plug Red e → Plug Red (E [ e ]*)
plug-frame* []      p = p
plug-frame* (F ∷ E) p = plug-frame F (plug-frame* E p)

plug⇒ctx : ∀ {Red : Tm n → Set} {e} → Plug Red e →
  ∃[ E ] ∃[ r ] Red r × e ≡ E [ r ]*
plug⇒ctx (here r) = [] , _ , r , refl
plug⇒ctx (appˡ {e₂ = e₂} {d = d} V? p)
  with E , r , Rr , refl ← plug⇒ctx p = app₁ e₂ d V? ∷ E , r , Rr , refl
plug⇒ctx (appʳ {e₁ = e₁} {d = d} V? p)
  with E , r , Rr , refl ← plug⇒ctx p = app₂ e₁ d V? ∷ E , r , Rr , refl
plug⇒ctx (pairˡ {e₂ = e₂} p)
  with E , r , Rr , refl ← plug⇒ctx p = (□⊗ e₂) ∷ E , r , Rr , refl
plug⇒ctx (pairʳ V₁ p)
  with E , r , Rr , refl ← plug⇒ctx p = (V₁ ⊗□) ∷ E , r , Rr , refl
plug⇒ctx (seqˡ {e₂ = e₂} p)
  with E , r , Rr , refl ← plug⇒ctx p = (□; e₂) ∷ E , r , Rr , refl
plug⇒ctx (letˡ {e₂ = e₂} p)
  with E , r , Rr , refl ← plug⇒ctx p = (`let-`in e₂) ∷ E , r , Rr , refl
plug⇒ctx (let⊗ˡ {e₂ = e₂} p)
  with E , r , Rr , refl ← plug⇒ctx p = (`let⊗-`in e₂) ∷ E , r , Rr , refl
plug⇒ctx (injˡ {i = i} p)
  with E , r , Rr , refl ← plug⇒ctx p = `inj□ i ∷ E , r , Rr , refl
plug⇒ctx (caseˡ {e₁ = e₁} {e₂ = e₂} p)
  with E , r , Rr , refl ← plug⇒ctx p = `case□`of⟨ e₁ ; e₂ ⟩ ∷ E , r , Rr , refl

--------------------------------------------------------------------------------
-- Decidability.

plug? : ∀ {Red : Tm n → Set} → (∀ e → Dec (Red e)) → ∀ e → Dec (Plug Red e)
plug? R? (` x) with R? (` x)
... | yes r = yes (here r)
... | no ¬r = no λ{ (here r) → ¬r r }
plug? R? (K c) with R? (K c)
... | yes r = yes (here r)
... | no ¬r = no λ{ (here r) → ¬r r }
plug? R? (ƛ e) with R? (ƛ e)
... | yes r = yes (here r)
... | no ¬r = no λ{ (here r) → ¬r r }
plug? R? (μ e) with R? (μ e)
... | yes r = yes (here r)
... | no ¬r = no λ{ (here r) → ¬r r }
plug? R? (e₁ ·⟨ d ⟩ e₂)
  with R? (e₁ ·⟨ d ⟩ e₂)
     | app₁-cond? d e₂ ×? plug? R? e₁
     | app₂-cond? d e₁ ×? plug? R? e₂
... | yes r  | _              | _              = yes (here r)
... | no ¬r  | yes (V? , p)   | _              = yes (appˡ V? p)
... | no ¬r  | no _           | yes (V? , p)   = yes (appʳ V? p)
... | no ¬r  | no ¬l          | no ¬rr         = no λ where
        (here r)    → ¬r r
        (appˡ V? p) → ¬l  (V? , p)
        (appʳ V? p) → ¬rr (V? , p)
plug? R? (e₁ ⊗ e₂)
  with R? (e₁ ⊗ e₂) | plug? R? e₁ | value? e₁ ×? plug? R? e₂
... | yes r | _     | _            = yes (here r)
... | no ¬r | yes p | _            = yes (pairˡ p)
... | no ¬r | no _  | yes (V , p)  = yes (pairʳ V p)
... | no ¬r | no ¬l | no ¬rr       = no λ where
        (here r)    → ¬r r
        (pairˡ p)   → ¬l p
        (pairʳ V p) → ¬rr (V , p)
plug? R? (e₁ ; e₂) with R? (e₁ ; e₂) | plug? R? e₁
... | yes r | _     = yes (here r)
... | no ¬r | yes p = yes (seqˡ p)
... | no ¬r | no ¬p = no λ{ (here r) → ¬r r ; (seqˡ p) → ¬p p }
plug? R? (`let e₁ `in e₂) with R? (`let e₁ `in e₂) | plug? R? e₁
... | yes r | _     = yes (here r)
... | no ¬r | yes p = yes (letˡ p)
... | no ¬r | no ¬p = no λ{ (here r) → ¬r r ; (letˡ p) → ¬p p }
plug? R? (`let⊗ e₁ `in e₂) with R? (`let⊗ e₁ `in e₂) | plug? R? e₁
... | yes r | _     = yes (here r)
... | no ¬r | yes p = yes (let⊗ˡ p)
... | no ¬r | no ¬p = no λ{ (here r) → ¬r r ; (let⊗ˡ p) → ¬p p }
plug? R? (`inj i e) with R? (`inj i e) | plug? R? e
... | yes r | _     = yes (here r)
... | no ¬r | yes p = yes (injˡ p)
... | no ¬r | no ¬p = no λ{ (here r) → ¬r r ; (injˡ p) → ¬p p }
plug? R? (`case e `of⟨ e₁ ; e₂ ⟩) with R? (`case e `of⟨ e₁ ; e₂ ⟩) | plug? R? e
... | yes r | _     = yes (here r)
... | no ¬r | yes p = yes (caseˡ p)
... | no ¬r | no ¬p = no λ{ (here r) → ¬r r ; (caseˡ p) → ¬p p }

--------------------------------------------------------------------------------
-- Renamings.

value-⋯ᵣ⁻¹ : (e : Tm m) (ρ : m →ᵣ n) → Value (e ⋯ ρ) → Value e
value-⋯ᵣ⁻¹ (` x)      ρ V = V-`
value-⋯ᵣ⁻¹ (K c)      ρ V = V-K
value-⋯ᵣ⁻¹ (ƛ e)      ρ V = V-λ
value-⋯ᵣ⁻¹ (e₁ ⊗ e₂)  ρ (V-⊗ V₁ V₂) = V-⊗ (value-⋯ᵣ⁻¹ e₁ ρ V₁) (value-⋯ᵣ⁻¹ e₂ ρ V₂)
value-⋯ᵣ⁻¹ (`inj i e) ρ (V-⊕ V)     = V-⊕ (value-⋯ᵣ⁻¹ e ρ V)

-- `Frame*` plugging commutes with renaming.

⋯ᶠ-[] : (F : Frame m) (e : Tm m) (ρ : m →ᵣ n) → (F [ e ]) ⋯ ρ ≡ (F ⋯ᶠ ρ) [ e ⋯ ρ ]
⋯ᶠ-[] (app₁ e₂ d V?)        e ρ = refl
⋯ᶠ-[] (app₂ e₁ d V?)        e ρ = refl
⋯ᶠ-[] (□⊗ e₂)               e ρ = refl
⋯ᶠ-[] (V₁ ⊗□)               e ρ = refl
⋯ᶠ-[] (□; e₂)               e ρ = refl
⋯ᶠ-[] (`let-`in e′)         e ρ = refl
⋯ᶠ-[] (`let⊗-`in e′)        e ρ = refl
⋯ᶠ-[] (`inj□ i)             e ρ = refl
⋯ᶠ-[] `case□`of⟨ e₁ ; e₂ ⟩  e ρ = refl

⋯ᶠ*-[]* : (E : Frame* m) (e : Tm m) (ρ : m →ᵣ n) → (E [ e ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ e ⋯ ρ ]*
⋯ᶠ*-[]* []      e ρ = refl
⋯ᶠ*-[]* (F ∷ E) e ρ = ⋯ᶠ-[] F (E [ e ]*) ρ ■ cong ((F ⋯ᶠ ρ) [_]) (⋯ᶠ*-[]* E e ρ)

plug-⋯ᵣ : ∀ {Red : Tm m → Set} {Red′ : Tm n → Set} (ρ : m →ᵣ n) →
  (∀ (r : Tm m) → Red r → Red′ (r ⋯ ρ)) →
  ∀ (e : Tm m) → Plug Red e → Plug Red′ (e ⋯ ρ)
plug-⋯ᵣ ρ f e             (here r)      = here (f e r)
plug-⋯ᵣ ρ f (e₁ ·⟨ d ⟩ e₂) (appˡ V? p)  = appˡ (λ eq → V? eq ⋯ᵛ ρ) (plug-⋯ᵣ ρ f e₁ p)
plug-⋯ᵣ ρ f (e₁ ·⟨ d ⟩ e₂) (appʳ V? p)  = appʳ (λ eq → V? eq ⋯ᵛ ρ) (plug-⋯ᵣ ρ f e₂ p)
plug-⋯ᵣ ρ f (e₁ ⊗ e₂)      (pairˡ p)    = pairˡ (plug-⋯ᵣ ρ f e₁ p)
plug-⋯ᵣ ρ f (e₁ ⊗ e₂)      (pairʳ V p)  = pairʳ (V ⋯ᵛ ρ) (plug-⋯ᵣ ρ f e₂ p)
plug-⋯ᵣ ρ f (e₁ ; e₂)      (seqˡ p)     = seqˡ (plug-⋯ᵣ ρ f e₁ p)
plug-⋯ᵣ ρ f (`let e₁ `in e₂)  (letˡ p)  = letˡ (plug-⋯ᵣ ρ f e₁ p)
plug-⋯ᵣ ρ f (`let⊗ e₁ `in e₂) (let⊗ˡ p) = let⊗ˡ (plug-⋯ᵣ ρ f e₁ p)
plug-⋯ᵣ ρ f (`inj i e)     (injˡ p)     = injˡ (plug-⋯ᵣ ρ f e p)
plug-⋯ᵣ ρ f (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) = caseˡ (plug-⋯ᵣ ρ f e p)

plug-⋯ᵣ⁻¹ : ∀ {Red : Tm m → Set} {Red′ : Tm n → Set} (ρ : m →ᵣ n) →
  (∀ (r : Tm m) → Red′ (r ⋯ ρ) → Red r) →
  ∀ (e : Tm m) → Plug Red′ (e ⋯ ρ) → Plug Red e
plug-⋯ᵣ⁻¹ ρ f (` x) (here r) = here (f (` x) r)
plug-⋯ᵣ⁻¹ ρ f (K c) (here r) = here (f (K c) r)
plug-⋯ᵣ⁻¹ ρ f (ƛ e) (here r) = here (f (ƛ e) r)
plug-⋯ᵣ⁻¹ ρ f (μ e) (here r) = here (f (μ e) r)
plug-⋯ᵣ⁻¹ ρ f (e₁ ·⟨ d ⟩ e₂) (here r)     = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (e₁ ·⟨ d ⟩ e₂) (appˡ V? p)  =
  appˡ (λ eq → value-⋯ᵣ⁻¹ e₂ ρ (V? eq)) (plug-⋯ᵣ⁻¹ ρ f e₁ p)
plug-⋯ᵣ⁻¹ ρ f (e₁ ·⟨ d ⟩ e₂) (appʳ V? p)  =
  appʳ (λ eq → value-⋯ᵣ⁻¹ e₁ ρ (V? eq)) (plug-⋯ᵣ⁻¹ ρ f e₂ p)
plug-⋯ᵣ⁻¹ ρ f (e₁ ⊗ e₂) (here r)    = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (e₁ ⊗ e₂) (pairˡ p)   = pairˡ (plug-⋯ᵣ⁻¹ ρ f e₁ p)
plug-⋯ᵣ⁻¹ ρ f (e₁ ⊗ e₂) (pairʳ V p) = pairʳ (value-⋯ᵣ⁻¹ e₁ ρ V) (plug-⋯ᵣ⁻¹ ρ f e₂ p)
plug-⋯ᵣ⁻¹ ρ f (e₁ ; e₂) (here r) = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (e₁ ; e₂) (seqˡ p) = seqˡ (plug-⋯ᵣ⁻¹ ρ f e₁ p)
plug-⋯ᵣ⁻¹ ρ f (`let e₁ `in e₂) (here r) = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (`let e₁ `in e₂) (letˡ p) = letˡ (plug-⋯ᵣ⁻¹ ρ f e₁ p)
plug-⋯ᵣ⁻¹ ρ f (`let⊗ e₁ `in e₂) (here r)  = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (`let⊗ e₁ `in e₂) (let⊗ˡ p) = let⊗ˡ (plug-⋯ᵣ⁻¹ ρ f e₁ p)
plug-⋯ᵣ⁻¹ ρ f (`inj i e) (here r) = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (`inj i e) (injˡ p) = injˡ (plug-⋯ᵣ⁻¹ ρ f e p)
plug-⋯ᵣ⁻¹ ρ f (`case e `of⟨ e₁ ; e₂ ⟩) (here r)  = here (f _ r)
plug-⋯ᵣ⁻¹ ρ f (`case e `of⟨ e₁ ; e₂ ⟩) (caseˡ p) = caseˡ (plug-⋯ᵣ⁻¹ ρ f e p)
