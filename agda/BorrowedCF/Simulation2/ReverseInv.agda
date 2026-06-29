module BorrowedCF.Simulation2.ReverseInv where

-- | Reusable inversion lemmas for the REVERSE simulation (sim←).
--
--   These are the SOUND, hole-free ingredients of the typed reflection of
--   expression reduction through a value substitution.  Substituting VALUES
--   into a term cannot create new head redexes EXCEPT possibly at a channel-
--   typed variable in head position — which the source typing rules out
--   (ChanCx forces every free variable to a channel type ⟨ s ⟩, never an arrow
--   / pair / sum, so it can never head an application / let⊗ / case).  Exports:
--     • value-no-head / value-step / value-⋯⁻¹ — a value never reduces; a step
--       through a VSub reflects the source-side Value side conditions,
--     • chanvar-not{Arr,Pair,Sum} / var-app-absurd — a channel variable can
--       never occupy a redex-head position.
--   (The full reflection that consumes these is blocked only by the frame-plug
--   non-invertibility of Agda's unifier; see Reverse.agda RU-Exp.)

open import BorrowedCF.Simulation2.Base
open import BorrowedCF.Context using (Ctx; Struct)

open import BorrowedCF.Types using (_≃_; ⟨_⟩; ≃-sym; ≃-trans)
import BorrowedCF.Simulation2.InvFrame as IF
open import BorrowedCF.Simulation2.Frames using (frame*-⋯; frame-plug*; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation2.TranslationProperties using (≡→≋)
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
import Data.Sum as Sum

open Variables
open Fin.Patterns

-- A channel type is never equivalent to a function arrow.  ≃𝕋 is a head-
-- preserving congruence, so ⟨ s ⟩ ≃ (T ⟨ a ⟩→ U) has no constructor.
⟨⟩≄→ : ∀ {s T U a} → ¬ (⟨ s ⟩ ≃ (T ⟨ a ⟩→ U))
⟨⟩≄→ ()

⟨⟩≄⊗ : ∀ {s T U d} → ¬ (⟨ s ⟩ ≃ (T ⊗⟨ d ⟩ U))
⟨⟩≄⊗ ()

⟨⟩≄⊕ : ∀ {s T U} → ¬ (⟨ s ⟩ ≃ (T ⊕ U))
⟨⟩≄⊕ ()

⟨⟩≄⊤ : ∀ {s} → ¬ (⟨ s ⟩ ≃ `⊤)
⟨⟩≄⊤ ()

-- A channel-typed variable cannot be typed at an arrow / pair / sum, so it can
-- never occupy the (function / scrutinee) head position of an application,
-- let⊗, or case.  These rule out a VSub manufacturing a head redex at a var.
chanvar-notArr : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U a ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⟨ a ⟩→ U) ∣ ϵ → ⊥
chanvar-notArr {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄→ (≃-sym (subst (_ ≃_) eq T≃))

chanvar-notPair : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U d ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⊗⟨ d ⟩ U) ∣ ϵ → ⊥
chanvar-notPair {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄⊗ (≃-sym (subst (_ ≃_) eq T≃))

chanvar-notSum : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {T U ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ (T ⊕ U) ∣ ϵ → ⊥
chanvar-notSum {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄⊕ (≃-sym (subst (_ ≃_) eq T≃))

chanvar-not⊤ : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {ϵ}
  → ChanCx Γ → Γ ; γ ⊢ ` x ∶ `⊤ ∣ ϵ → ⊥
chanvar-not⊤ {x = x} Γ-S ⊢x with inv-` ⊢x | Γ-S x
... | T≃ , _ | s , eq = ⟨⟩≄⊤ (≃-sym (subst (_ ≃_) eq T≃))

-- new's declared domain is `⊤; reading it off the arrow ≃ forces the argument
-- type to `⊤.
⊤-dom : ∀ {m} {T U R R′ : Ty 𝕥 m} {a a′} → (T ⟨ a ⟩→ R) ≃ (U ⟨ a′ ⟩→ R′) → T ≃ U
⊤-dom (eq `→ _) = eq

-- The argument of `new s` is typed at `⊤, so a channel variable can never be
-- it: a (matched) App constructor types the function at (`⊤ ⟨a⟩→ R) and the
-- argument at `⊤, contradicting ChanCx.
clash-new : ∀ {m} {Γ : Ctx m} {γ₁ γ₂} {x : 𝔽 m} {s : 𝕊 0} {U a R ϵ₁ ϵ₂}
      → ChanCx Γ → Γ ; γ₁ ⊢ K (`new s) ∶ (U ⟨ a ⟩→ R) ∣ ϵ₁
      → Γ ; γ₂ ⊢ ` x ∶ U ∣ ϵ₂ → ⊥
clash-new Γ-S ⊢f ⊢a with inv-K ⊢f
... | _ , U≃ , _ , `new _ =
      chanvar-not⊤ Γ-S (T-Conv (≃-sym (⊤-dom U≃)) ≤ϵ-refl ⊢a)

new-arg-notVar : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {s : 𝕊 0} {T ϵ}
  → ChanCx Γ → Γ ; γ ⊢ K (`new s) · (` x) ∶ T ∣ ϵ → ⊥
new-arg-notVar Γ-S (T-AppUnr _ _ ⊢f ⊢a)  = clash-new Γ-S ⊢f ⊢a
new-arg-notVar Γ-S (T-AppLin _ _ ⊢f ⊢a)  = clash-new Γ-S ⊢f ⊢a
new-arg-notVar Γ-S (T-AppLeft _ _ ⊢f ⊢a) = clash-new Γ-S ⊢f ⊢a
new-arg-notVar Γ-S (T-AppRight _ _ ⊢f ⊢a) = clash-new Γ-S ⊢f ⊢a
new-arg-notVar Γ-S (T-Conv _ _ d) = new-arg-notVar Γ-S d
new-arg-notVar Γ-S (T-Weaken _ d) = new-arg-notVar Γ-S d

-- A channel-typed variable can never head a well-typed application: the
-- application rules type the function at an arrow, contradicting ChanCx.
var-app-absurd : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {e₂ T ϵ}
  → ChanCx Γ → Γ ; γ ⊢ (` x) · e₂ ∶ T ∣ ϵ → ⊥
var-app-absurd Γ-S (T-AppUnr _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppLin _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppLeft _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-AppRight _ _ ⊢f _) = chanvar-notArr Γ-S ⊢f
var-app-absurd Γ-S (T-Conv _ _ d) = var-app-absurd Γ-S d
var-app-absurd Γ-S (T-Weaken _ d) = var-app-absurd Γ-S d


-- A channel-typed variable can never be the scrutinee of a well-typed let⊗ or
-- case: those rules type the scrutinee at a pair / sum, contradicting ChanCx.
var-letpair-absurd : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {e : Tm (2 + m)} {T ϵ}
  → ChanCx Γ → Γ ; γ ⊢ `let⊗ (` x) `in e ∶ T ∣ ϵ → ⊥
var-letpair-absurd Γ-S (T-LetPair _ ⊢x _) = chanvar-notPair Γ-S ⊢x
var-letpair-absurd Γ-S (T-Conv _ _ d) = var-letpair-absurd Γ-S d
var-letpair-absurd Γ-S (T-Weaken _ d) = var-letpair-absurd Γ-S d

var-case-absurd : ∀ {m} {Γ : Ctx m} {γ} {x : 𝔽 m} {e₁ e₂ : Tm (suc m)} {T ϵ}
  → ChanCx Γ → Γ ; γ ⊢ `case (` x) `of⟨ e₁ ; e₂ ⟩ ∶ T ∣ ϵ → ⊥
var-case-absurd Γ-S (T-Case _ ⊢x _ _) = chanvar-notSum Γ-S ⊢x
var-case-absurd Γ-S (T-Conv _ _ d) = var-case-absurd Γ-S d
var-case-absurd Γ-S (T-Weaken _ d) = var-case-absurd Γ-S d

------------------------------------------------------------------------
-- Value reflection helpers (foundational; also re-used by Reverse).
------------------------------------------------------------------------

-- Value reflection through a VSub: a substituted term is a value iff the
-- source is.  (Recovers the source-side Value side conditions.)
value-⋯⁻¹ : (σ : m →ₛ n) → VSub σ → (e₀ : Tm m) → Value (e₀ ⋯ σ) → Value e₀
value-⋯⁻¹ σ Vσ (` x)               V = V-`
value-⋯⁻¹ σ Vσ (K c)               V = V-K
value-⋯⁻¹ σ Vσ (ƛ e)               V = V-λ
value-⋯⁻¹ σ Vσ (e₁ ⊗ e₂) (V-⊗ V₁ V₂) =
  V-⊗ (value-⋯⁻¹ σ Vσ e₁ V₁) (value-⋯⁻¹ σ Vσ e₂ V₂)
value-⋯⁻¹ σ Vσ (`inj i e)  (V-⊕ V)    = V-⊕ (value-⋯⁻¹ σ Vσ e V)

-- A value has no head reduction.
value-no-head : {t : Tm n} -> Value t -> {e2 : Tm n} -> ¬ (t ─→ e2)
value-no-head V-`         ()
value-no-head V-K         ()
value-no-head V-λ       ()
value-no-head (V-⊗ V1 V2) ()
value-no-head (V-⊕ V)   ()

-- A term that is a value never reduces.
value-step : {t : Tm n} -> Value t -> {e2 : Tm n} -> ¬ (t ⋯→ e2)
value-step V (E-□ hred)             = value-no-head V hred
value-step V (E-Ctx (□·  _)  red)    with V
... | ()
value-step V (E-Ctx (_ ·□)  red)    with V
... | ()
value-step V (E-Ctx (□⊗  _)  red)    with V
... | V-⊗ V1 V2 = value-step V1 red
value-step V (E-Ctx (_ ⊗□)  red)    with V
... | V-⊗ V1 V2 = value-step V2 red
value-step V (E-Ctx (□;  _)  red)    with V
... | ()
value-step V (E-Ctx (`let-`in  _)  red) with V
... | ()
value-step V (E-Ctx (`let⊗-`in _) red) with V
... | ()
value-step V (E-Ctx (`inj□  i) red)  with V
... | V-⊕ V' = value-step V' red
value-step V (E-Ctx `case□`of⟨ _ ; _ ⟩ red) with V
... | ()

------------------------------------------------------------------------
-- Head-shape inversions of expression reduction _⋯→_.
--
--   _⋯→_ has two constructors (E-□ head, E-Ctx frame), neither indexed by the
--   term's top constructor, so a direct `with` split on  (c …) ⋯→ e′  is
--   UnificationStuck (the plug E [ e ] is not constructor-headed).  We
--   generalise the LHS to a variable t with t ≡ c … , split, and discharge the
--   wrong frames by the (now constructor-headed) equation.  These are the SOUND
--   reverse of E-Ctx: a step at a head shape is either the head redex or a
--   congruence into one operand.
------------------------------------------------------------------------

⋯→-app : {e₁ e₂ e′ : Tm n} → (e₁ · e₂) ⋯→ e′ →
     (Σ[ b ∈ Tm (suc n) ] (e₁ ≡ ƛ b) × Value e₂ × (e′ ≡ b ⋯ ⦅ e₂ ⦆))
   ⊎ (Σ[ e₁′ ∈ Tm n ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ · e₂))
   ⊎ (Value e₁ × Σ[ e₂′ ∈ Tm n ] (e₂ ⋯→ e₂′) × (e′ ≡ e₁ · e₂′))
⋯→-app {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ e₁ · e₂ →
         (Σ[ b ∈ Tm (suc _) ] (e₁ ≡ ƛ b) × Value e₂ × (e′ ≡ b ⋯ ⦅ e₂ ⦆))
       ⊎ (Σ[ e₁′ ∈ Tm _ ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ · e₂))
       ⊎ (Value e₁ × Σ[ e₂′ ∈ Tm _ ] (e₂ ⋯→ e₂′) × (e′ ≡ e₁ · e₂′))
    go _ (E-□ (E-App V)) refl = inj₁ (_ , refl , V , refl)
    go _ (E-Ctx (□· e₃) inner) refl = inj₂ (inj₁ (_ , inner , refl))
    go _ (E-Ctx (V₁ ·□) inner) refl = inj₂ (inj₂ (V₁ , _ , inner , refl))

⋯→-pair : {e₁ e₂ e′ : Tm n} → (e₁ ⊗ e₂) ⋯→ e′ →
     (Σ[ e₁′ ∈ Tm n ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ ⊗ e₂))
   ⊎ (Value e₁ × Σ[ e₂′ ∈ Tm n ] (e₂ ⋯→ e₂′) × (e′ ≡ e₁ ⊗ e₂′))
⋯→-pair {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ e₁ ⊗ e₂ →
         (Σ[ e₁′ ∈ Tm _ ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ ⊗ e₂))
       ⊎ (Value e₁ × Σ[ e₂′ ∈ Tm _ ] (e₂ ⋯→ e₂′) × (e′ ≡ e₁ ⊗ e₂′))
    go _ (E-□ ()) refl
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) refl = inj₁ (_ , inner , refl)
    go _ (E-Ctx (V₁ ⊗□) inner) refl = inj₂ (V₁ , _ , inner , refl)
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

⋯→-inj : {i : Side} {e e′ : Tm n} → (`inj i e) ⋯→ e′ →
   Σ[ e₂ ∈ Tm n ] (e ⋯→ e₂) × (e′ ≡ `inj i e₂)
⋯→-inj {i = i} {e = e} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ `inj i e →
       Σ[ e₂ ∈ Tm _ ] (e ⋯→ e₂) × (e′ ≡ `inj i e₂)
    go _ (E-□ ()) refl
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ j) inner) refl = _ , inner , refl
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

⋯→-seq : {e₁ e₂ e′ : Tm n} → (e₁ ; e₂) ⋯→ e′ →
     (Value e₁ × (e′ ≡ e₂))
   ⊎ (Σ[ e₁′ ∈ Tm n ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ ; e₂))
⋯→-seq {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ e₁ ; e₂ →
         (Value e₁ × (e′ ≡ e₂))
       ⊎ (Σ[ e₁′ ∈ Tm _ ] (e₁ ⋯→ e₁′) × (e′ ≡ e₁′ ; e₂))
    go _ (E-□ (E-Seq V)) refl = inj₁ (V , refl)
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) refl = inj₂ (_ , inner , refl)
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

⋯→-let : {e₁ : Tm n} {e₂ : Tm (suc n)} {e′ : Tm n} → (`let e₁ `in e₂) ⋯→ e′ →
     (Value e₁ × (e′ ≡ e₂ ⋯ ⦅ e₁ ⦆))
   ⊎ (Σ[ e₁′ ∈ Tm n ] (e₁ ⋯→ e₁′) × (e′ ≡ `let e₁′ `in e₂))
⋯→-let {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ `let e₁ `in e₂ →
         (Value e₁ × (e′ ≡ e₂ ⋯ ⦅ e₁ ⦆))
       ⊎ (Σ[ e₁′ ∈ Tm _ ] (e₁ ⋯→ e₁′) × (e′ ≡ `let e₁′ `in e₂))
    go _ (E-□ (E-Let V)) refl = inj₁ (V , refl)
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) refl = inj₂ (_ , inner , refl)
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

⋯→-letpair : {e₁ : Tm n} {e₂ : Tm (suc (suc n))} {e′ : Tm n} → (`let⊗ e₁ `in e₂) ⋯→ e′ →
     (Σ[ a ∈ Tm n ] Σ[ b ∈ Tm n ] (e₁ ≡ a ⊗ b) × Value a × Value b × (e′ ≡ e₂ ⋯ ⦅ wk a ⦆ ⋯ ⦅ b ⦆))
   ⊎ (Σ[ e₁′ ∈ Tm n ] (e₁ ⋯→ e₁′) × (e′ ≡ `let⊗ e₁′ `in e₂))
⋯→-letpair {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ `let⊗ e₁ `in e₂ →
         (Σ[ a ∈ Tm _ ] Σ[ b ∈ Tm _ ] (e₁ ≡ a ⊗ b) × Value a × Value b × (e′ ≡ e₂ ⋯ ⦅ wk a ⦆ ⋯ ⦅ b ⦆))
       ⊎ (Σ[ e₁′ ∈ Tm _ ] (e₁ ⋯→ e₁′) × (e′ ≡ `let⊗ e₁′ `in e₂))
    go _ (E-□ (E-PairElim V₁ V₂)) refl = inj₁ (_ , _ , refl , V₁ , V₂ , refl)
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) refl = inj₂ (_ , inner , refl)
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

⋯→-case : {e : Tm n} {e₁ e₂ : Tm (suc n)} {e′ : Tm n} → (`case e `of⟨ e₁ ; e₂ ⟩) ⋯→ e′ →
     (Σ[ i ∈ Side ] Σ[ v ∈ Tm n ] (e ≡ `inj i v) × Value v × (e′ ≡ (if i then e₁ else e₂) ⋯ ⦅ v ⦆))
   ⊎ (Σ[ e0 ∈ Tm n ] (e ⋯→ e0) × (e′ ≡ `case e0 `of⟨ e₁ ; e₂ ⟩))
⋯→-case {e = e} {e₁ = e₁} {e₂ = e₂} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ `case e `of⟨ e₁ ; e₂ ⟩ →
         (Σ[ i ∈ Side ] Σ[ v ∈ Tm _ ] (e ≡ `inj i v) × Value v × (e′ ≡ (if i then e₁ else e₂) ⋯ ⦅ v ⦆))
       ⊎ (Σ[ e0 ∈ Tm _ ] (e ⋯→ e0) × (e′ ≡ `case e0 `of⟨ e₁ ; e₂ ⟩))
    go _ (E-□ (E-SumElim V)) refl = inj₁ (_ , _ , refl , V , refl)
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) refl = inj₂ (_ , inner , refl)

⋯→-mu : {e : Tm (suc n)} {e′ : Tm n} → (μ e) ⋯→ e′ → e′ ≡ e ⋯ ⦅ μ e ⦆
⋯→-mu {e = e} {e′ = e′} step = go _ step refl
  where
    go : (t : Tm _) → t ⋯→ e′ → t ≡ μ e → e′ ≡ e ⋯ ⦅ μ e ⦆
    go _ (E-□ E-Unfold) refl = refl
    go _ (E-Ctx (□· e₃) inner) ()
    go _ (E-Ctx (V₁ ·□) inner) ()
    go _ (E-Ctx (□⊗ e₃) inner) ()
    go _ (E-Ctx (V₁ ⊗□) inner) ()
    go _ (E-Ctx (□; e₃) inner) ()
    go _ (E-Ctx (`let-`in e₃) inner) ()
    go _ (E-Ctx (`let⊗-`in e₃) inner) ()
    go _ (E-Ctx (`inj□ i) inner) ()
    go _ (E-Ctx `case□`of⟨ f₁ ; f₂ ⟩ inner) ()

------------------------------------------------------------------------
-- Typed reflection of expression reduction through a value substitution.
--
--   The reverse of Frames.⋯→-⋯ₛ.  Substituting VALUES into e₀ cannot create a
--   NEW head redex EXCEPT at a variable in head position (σ x may be a λ / pair
--   / inj value), and the source typing (ChanCx Γ forces every free var to a
--   channel type ⟨ s ⟩) rules that out via chanvar-not* / var-app-absurd.  So
--   every step of e₀ ⋯ σ is the image of a step of e₀.  Proven by induction on
--   e₀, using the head-shape inversions above and the operand-typing inversions
--   of InvFrame; the substitution-commutation glue is the same dist-↑-⦅⦆-⋯ the
--   forward direction uses.
------------------------------------------------------------------------


-- A value substitution gives a λ-headed result only when the source is a
-- variable (σ may map it to a λ) or literally a λ.  (Likewise ⊗ / inj.)  Used
-- to dispatch the head-redex branch of ⋯→-reflect: the variable alternative is
-- refuted by the source typing (chanvar-not* / var-app-absurd).
headλ : (σ : m →ₛ n) → (e₁ : Tm m) {b : Tm (suc n)} → (e₁ ⋯ σ) ≡ ƛ b
  → (Σ[ x ∈ 𝔽 m ] e₁ ≡ ` x) ⊎ (Σ[ b₀ ∈ Tm (suc m) ] e₁ ≡ ƛ b₀)
headλ σ (` x)       eq = inj₁ (x , refl)
headλ σ (ƛ e)       eq = inj₂ (e , refl)

head⊗ : (σ : m →ₛ n) → (e₁ : Tm m) {a b : Tm n} → (e₁ ⋯ σ) ≡ a ⊗ b
  → (Σ[ x ∈ 𝔽 m ] e₁ ≡ ` x) ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm m ] e₁ ≡ a₀ ⊗ b₀)
head⊗ σ (` x)       eq = inj₁ (x , refl)
head⊗ σ (e₁ ⊗ e₂)   eq = inj₂ (e₁ , e₂ , refl)

head-inj : (σ : m →ₛ n) → (e : Tm m) {i : Side} {v : Tm n} → (e ⋯ σ) ≡ `inj i v
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x) ⊎ (Σ[ j ∈ Side ] Σ[ v₀ ∈ Tm m ] e ≡ `inj j v₀)
head-inj σ (` x)       eq = inj₁ (x , refl)
head-inj σ (`inj j v)  eq = inj₂ (j , v , refl)


-- Head-shape reflections that ALSO carry the operand equalities (needed by the
-- Frame* reflection below to peel a frame and recurse into the right subterm).
-- A value substitution gives a c-headed result only when the source is a
-- variable (σ x may be that value) or literally that head.
headK : (σ : m →ₛ n) → (e : Tm m) {c : Const} → (e ⋯ σ) ≡ K c
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x) ⊎ (e ≡ K c)
headK σ (` x)    eq = inj₁ (x , refl)
headK σ (K c)  refl = inj₂ refl

headApp : (σ : m →ₛ n) → (e : Tm m) {a b : Tm n} → (e ⋯ σ) ≡ a · b
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm m ] (e ≡ a₀ · b₀) × (a ≡ a₀ ⋯ σ) × (b ≡ b₀ ⋯ σ))
headApp σ (` x)       eq = inj₁ (x , refl)
headApp σ (a₀ · b₀) refl = inj₂ (a₀ , b₀ , refl , refl , refl)

head⊗′ : (σ : m →ₛ n) → (e : Tm m) {a b : Tm n} → (e ⋯ σ) ≡ a ⊗ b
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm m ] (e ≡ a₀ ⊗ b₀) × (a ≡ a₀ ⋯ σ) × (b ≡ b₀ ⋯ σ))
head⊗′ σ (` x)       eq = inj₁ (x , refl)
head⊗′ σ (a₀ ⊗ b₀) refl = inj₂ (a₀ , b₀ , refl , refl , refl)

headSeq : (σ : m →ₛ n) → (e : Tm m) {a b : Tm n} → (e ⋯ σ) ≡ a ; b
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm m ] (e ≡ a₀ ; b₀) × (a ≡ a₀ ⋯ σ) × (b ≡ b₀ ⋯ σ))
headSeq σ (` x)       eq = inj₁ (x , refl)
headSeq σ (a₀ ; b₀) refl = inj₂ (a₀ , b₀ , refl , refl , refl)

headInj′ : (σ : m →ₛ n) → (e : Tm m) {i : Side} {v : Tm n} → (e ⋯ σ) ≡ `inj i v
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ v₀ ∈ Tm m ] (e ≡ `inj i v₀) × (v ≡ v₀ ⋯ σ))
headInj′ σ (` x)        eq = inj₁ (x , refl)
headInj′ σ (`inj i v₀) refl = inj₂ (v₀ , refl , refl)

headLet : (σ : m →ₛ n) → (e : Tm m) {a : Tm n} {b : Tm (suc n)} → (e ⋯ σ) ≡ `let a `in b
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm (suc m) ] (e ≡ `let a₀ `in b₀) × (a ≡ a₀ ⋯ σ) × (b ≡ b₀ ⋯ σ ↑))
headLet σ (` x)              eq = inj₁ (x , refl)
headLet σ (`let a₀ `in b₀) refl = inj₂ (a₀ , b₀ , refl , refl , refl)

headLetpair : (σ : m →ₛ n) → (e : Tm m) {a : Tm n} {b : Tm (suc (suc n))} → (e ⋯ σ) ≡ `let⊗ a `in b
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ a₀ ∈ Tm m ] Σ[ b₀ ∈ Tm (suc (suc m)) ] (e ≡ `let⊗ a₀ `in b₀) × (a ≡ a₀ ⋯ σ) × (b ≡ b₀ ⋯ σ ↑ ↑))
headLetpair σ (` x)               eq = inj₁ (x , refl)
headLetpair σ (`let⊗ a₀ `in b₀) refl = inj₂ (a₀ , b₀ , refl , refl , refl)

headCase : (σ : m →ₛ n) → (e : Tm m) {s : Tm n} {b₁ b₂ : Tm (suc n)} → (e ⋯ σ) ≡ `case s `of⟨ b₁ ; b₂ ⟩
  → (Σ[ x ∈ 𝔽 m ] e ≡ ` x)
  ⊎ (Σ[ s₀ ∈ Tm m ] Σ[ c₁ ∈ Tm (suc m) ] Σ[ c₂ ∈ Tm (suc m) ]
       (e ≡ `case s₀ `of⟨ c₁ ; c₂ ⟩) × (s ≡ s₀ ⋯ σ) × (b₁ ≡ c₁ ⋯ σ ↑) × (b₂ ≡ c₂ ⋯ σ ↑))
headCase σ (` x)                     eq = inj₁ (x , refl)
headCase σ (`case s₀ `of⟨ c₁ ; c₂ ⟩) refl = inj₂ (s₀ , c₁ , c₂ , refl , refl , refl , refl)

-- Injectivity of term constructors (for matching head equalities).
ƛ-inj : {b₁ b₂ : Tm (suc n)} → (ƛ b₁) ≡ (ƛ b₂) → b₁ ≡ b₂
ƛ-inj refl = refl

⊗-inj : {a₁ a₂ b₁ b₂ : Tm n} → (a₁ ⊗ b₁) ≡ (a₂ ⊗ b₂) → (a₁ ≡ a₂) × (b₁ ≡ b₂)
⊗-inj refl = refl , refl

inj-inj : {i j : Side} {u v : Tm n} → (`inj i u) ≡ (`inj j v) → (i ≡ j) × (u ≡ v)
inj-inj refl = refl , refl

-- Substitution-commutation for the let⊗ / case heads (the same equalities the
-- forward ─→-⋯ₛ uses, run in reverse).
letpair-eq : ∀ {m n} (e₂ : Tm (2 + m)) (a b : Tm m) (σ : m →ₛ n)
  → (e₂ ⋯ σ ↑ ↑) ⋯ ⦅ wk (a ⋯ σ) ⦆ ⋯ ⦅ b ⋯ σ ⦆ ≡ (e₂ ⋯ ⦅ wk a ⦆ ⋯ ⦅ b ⦆) ⋯ σ
letpair-eq e₂ a b σ =
  let inner : e₂ ⋯ ⦅ wk a ⦆ ⋯ σ ↑ ≡ e₂ ⋯ σ ↑ ↑ ⋯ ⦅ wk (a ⋯ σ) ⦆
      inner = dist-↑-⦅⦆-⋯ e₂ (wk a) (σ ↑) ■ cong (λ z → e₂ ⋯ σ ↑ ↑ ⋯ ⦅ z ⦆) (sym (⋯-↑-wk a σ))
  in cong (_⋯ ⦅ b ⋯ σ ⦆) (sym inner) ■ sym (dist-↑-⦅⦆-⋯ (e₂ ⋯ ⦅ wk a ⦆) b σ)

case-eq : ∀ {m n} (j : Side) (e₁ e₂ : Tm (suc m)) (v : Tm m) (σ : m →ₛ n)
  → (if j then (e₁ ⋯ σ ↑) else (e₂ ⋯ σ ↑)) ⋯ ⦅ v ⋯ σ ⦆ ≡ ((if j then e₁ else e₂) ⋯ ⦅ v ⦆) ⋯ σ
case-eq true  e₁ e₂ v σ = sym (dist-↑-⦅⦆-⋯ e₁ v σ)
case-eq false e₁ e₂ v σ = sym (dist-↑-⦅⦆-⋯ e₂ v σ)

⋯→-reflect : ∀ {m n} {Γ : Ctx m} {γ : Struct m} {T ϵ}
  → ChanCx Γ → (e₀ : Tm m) → Γ ; γ ⊢ e₀ ∶ T ∣ ϵ
  → (σ : m →ₛ n) → VSub σ → {e₂ : Tm n} → (e₀ ⋯ σ) ⋯→ e₂
  → Σ[ e₀′ ∈ Tm m ] (e₀ ⋯→ e₀′) × (e₂ ≡ e₀′ ⋯ σ)
⋯→-reflect Γ-S (` x)   ⊢e σ Vσ step = ⊥-elim (value-step (Vσ x) step)
⋯→-reflect Γ-S (K c)   ⊢e σ Vσ step = ⊥-elim (value-step V-K step)
⋯→-reflect Γ-S (ƛ e)   ⊢e σ Vσ step = ⊥-elim (value-step V-λ step)
⋯→-reflect Γ-S (μ e)   ⊢e σ Vσ step =
  e ⋯ ⦅ μ e ⦆ , E-□ E-Unfold , (⋯→-mu step ■ sym (dist-↑-⦅⦆-⋯ e (μ e) σ))
⋯→-reflect Γ-S (e₁ ⊗ e₂) ⊢e σ Vσ step
  with α₁ , α₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , _ ← IF.inv-pair ⊢e
  with ⋯→-pair step
... | inj₁ (e₁″ , inner , refl)
      with e₁′ , s₁ , refl ← ⋯→-reflect Γ-S e₁ ⊢e₁ σ Vσ inner
      = e₁′ ⊗ e₂ , E-Ctx (□⊗ e₂) s₁ , refl
... | Sum.inj₂ (Ve₁σ , e₂″ , inner , refl)
      with e₂′ , s₂ , refl ← ⋯→-reflect Γ-S e₂ ⊢e₂ σ Vσ inner
      = e₁ ⊗ e₂′ , E-Ctx (value-⋯⁻¹ σ Vσ e₁ Ve₁σ ⊗□) s₂ , refl
⋯→-reflect Γ-S (`inj i e) ⊢e σ Vσ step
  with _ , _ , ⊢e′ ← IF.inv-inj ⊢e
  with e0 , inner , refl ← ⋯→-inj step
  with e0′ , s0 , refl ← ⋯→-reflect Γ-S e ⊢e′ σ Vσ inner
  = `inj i e0′ , E-Ctx (`inj□ i) s0 , refl
⋯→-reflect Γ-S (e₁ · e₂) ⊢e σ Vσ step
  with ⋯→-app step
... | inj₁ (b , e₁σ≡ƛ , Ve₂σ , refl)
      with headλ σ e₁ e₁σ≡ƛ
...   | inj₁ (x , refl) = ⊥-elim (var-app-absurd Γ-S ⊢e)
...   | inj₂ (b₀ , refl) =
        b₀ ⋯ ⦅ e₂ ⦆ , E-□ (E-App (value-⋯⁻¹ σ Vσ e₂ Ve₂σ)) ,
          (cong (_⋯ ⦅ e₂ ⋯ σ ⦆) (sym (ƛ-inj e₁σ≡ƛ)) ■ sym (dist-↑-⦅⦆-⋯ b₀ e₂ σ))
⋯→-reflect Γ-S (e₁ · e₂) ⊢e σ Vσ step | inj₂ (inj₁ (e₁″ , inner , refl))
  with α₁ , α₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , _ ← IF.inv-app ⊢e
  with e₁′ , s₁ , refl ← ⋯→-reflect Γ-S e₁ ⊢e₁ σ Vσ inner
  = e₁′ · e₂ , E-Ctx (□· e₂) s₁ , refl
⋯→-reflect Γ-S (e₁ · e₂) ⊢e σ Vσ step | inj₂ (inj₂ (Ve₁σ , e₂″ , inner , refl))
  with α₁ , α₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , _ ← IF.inv-app ⊢e
  with e₂′ , s₂ , refl ← ⋯→-reflect Γ-S e₂ ⊢e₂ σ Vσ inner
  = e₁ · e₂′ , E-Ctx (value-⋯⁻¹ σ Vσ e₁ Ve₁σ ·□) s₂ , refl

⋯→-reflect Γ-S (e₁ ; e₂) ⊢e σ Vσ step
  with α₁ , α₂ , (_ , _ , ⊢e₁) , (_ , _ , ⊢e₂) , _ ← IF.inv-seq ⊢e
  with ⋯→-seq step
... | inj₁ (Ve₁σ , refl) = e₂ , E-□ (E-Seq (value-⋯⁻¹ σ Vσ e₁ Ve₁σ)) , refl
... | inj₂ (e₁″ , inner , refl)
      with e₁′ , s₁ , refl ← ⋯→-reflect Γ-S e₁ ⊢e₁ σ Vσ inner
      = e₁′ ; e₂ , E-Ctx (□; e₂) s₁ , refl

⋯→-reflect Γ-S (`let e₁ `in e₂) ⊢e σ Vσ step
  with γ₁ , γ₂ , p/s , (_ , _ , ⊢e₁) , _ , _ ← IF.inv-let ⊢e
  with ⋯→-let step
... | inj₁ (Ve₁σ , refl) =
      e₂ ⋯ ⦅ e₁ ⦆ , E-□ (E-Let (value-⋯⁻¹ σ Vσ e₁ Ve₁σ)) , sym (dist-↑-⦅⦆-⋯ e₂ e₁ σ)
... | inj₂ (e₁″ , inner , refl)
      with e₁′ , s₁ , refl ← ⋯→-reflect Γ-S e₁ ⊢e₁ σ Vσ inner
      = `let e₁′ `in e₂ , E-Ctx (`let-`in e₂) s₁ , refl

⋯→-reflect Γ-S (`let⊗ e₁ `in e₂) ⊢e σ Vσ step
  with γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , _ , _ ← IF.inv-letpair ⊢e
  with ⋯→-letpair step
... | inj₁ (a , b , e₁σ≡⊗ , Va , Vb , refl)
      with head⊗ σ e₁ e₁σ≡⊗
...   | inj₁ (x , refl) = ⊥-elim (var-letpair-absurd Γ-S ⊢e)
...   | inj₂ (a₀ , b₀ , refl)
        with refl , refl ← ⊗-inj e₁σ≡⊗ =
        e₂ ⋯ ⦅ wk a₀ ⦆ ⋯ ⦅ b₀ ⦆ ,
          E-□ (E-PairElim (value-⋯⁻¹ σ Vσ a₀ Va) (value-⋯⁻¹ σ Vσ b₀ Vb)) ,
          letpair-eq e₂ a₀ b₀ σ
⋯→-reflect Γ-S (`let⊗ e₁ `in e₂) ⊢e σ Vσ step | inj₂ (e₁″ , inner , refl)
  with γ₁ , γ₂ , p/s , d , (_ , _ , ⊢e₁) , _ , _ ← IF.inv-letpair ⊢e
  with e₁′ , s₁ , refl ← ⋯→-reflect Γ-S e₁ ⊢e₁ σ Vσ inner
  = `let⊗ e₁′ `in e₂ , E-Ctx (`let⊗-`in e₂) s₁ , refl

⋯→-reflect Γ-S (`case e `of⟨ e₁ ; e₂ ⟩) ⊢e σ Vσ step
  with γ₁ , γ₂ , p/s , (_ , _ , ⊢escr) , _ , _ , _ ← IF.inv-case ⊢e
  with ⋯→-case step
... | inj₁ (i , v , eσ≡inj , Vv , refl)
      with head-inj σ e eσ≡inj
...   | inj₁ (x , refl) = ⊥-elim (var-case-absurd Γ-S ⊢e)
...   | inj₂ (j , v₀ , refl)
        with refl , refl ← inj-inj eσ≡inj =
        (if j then e₁ else e₂) ⋯ ⦅ v₀ ⦆ ,
          E-□ (E-SumElim (value-⋯⁻¹ σ Vσ v₀ Vv)) ,
          case-eq j e₁ e₂ v₀ σ
⋯→-reflect Γ-S (`case e `of⟨ e₁ ; e₂ ⟩) ⊢e σ Vσ step | inj₂ (e0 , inner , refl)
  with γ₁ , γ₂ , p/s , (_ , _ , ⊢escr) , _ , _ , _ ← IF.inv-case ⊢e
  with e0′ , s0 , refl ← ⋯→-reflect Γ-S e ⊢escr σ Vσ inner
  = `case e0′ `of⟨ e₁ ; e₂ ⟩ , E-Ctx `case□`of⟨ e₁ ; e₂ ⟩ s0 , refl

-- A frame-stack with an application redex at the bottom is never a value: the
-- innermost a · b is not a value, and the value-producing frames (⊗ / inj) only
-- yield a value when their plug is a value, recursing down to a · b.
plugApp-not-value : ∀ {n} (F : Frame* n) {a b : Tm n} → ¬ Value (F [ a · b ]*)
plugApp-not-value [] ()
plugApp-not-value (□· e₃ ∷ F*) ()
plugApp-not-value (_·□ V₁ ∷ F*) ()
plugApp-not-value (□⊗ e₃ ∷ F*) (V-⊗ V₁ _) = plugApp-not-value F* V₁
plugApp-not-value (_⊗□ V₁ ∷ F*) (V-⊗ _ V₂) = plugApp-not-value F* V₂
plugApp-not-value (□; e₃ ∷ F*) ()
plugApp-not-value (`let-`in e₃ ∷ F*) ()
plugApp-not-value (`let⊗-`in e₃ ∷ F*) ()
plugApp-not-value (`inj□ i ∷ F*) (V-⊕ V) = plugApp-not-value F* V
plugApp-not-value (`case□`of⟨ e₁ ; e₂ ⟩ ∷ F*) ()

------------------------------------------------------------------------
-- Frame* reflection through a value substitution (the Frame* analogue of
-- ⋯→-reflect).  Inverts  e₀ ⋯ σ ≡ F [ K c · arg ]*  to a SOURCE frame stack F₀
-- and source argument arg₀ with e₀ ≡ F₀ [ K c · arg₀ ]*, F ≡ frame*-⋯ F₀ σ Vσ,
-- arg ≡ arg₀ ⋯ σ.  A variable head is refuted by the source typing
-- (var-app-absurd); the constant K c is never in σ's (value) image at a redex
-- head because the only var alternative is the refuted one.  Powers RU-Fork.
------------------------------------------------------------------------

frameApp-reflect : ∀ {m n} {Γ : Ctx m} {γ : Struct m} {T ϵ}
  → ChanCx Γ → (e₀ : Tm m) → Γ ; γ ⊢ e₀ ∶ T ∣ ϵ
  → (σ : m →ₛ n) (Vσ : VSub σ) → (c : Const) (F : Frame* n) {arg : Tm n}
  → e₀ ⋯ σ ≡ F [ K c · arg ]*
  → Σ[ F₀ ∈ Frame* m ] Σ[ arg₀ ∈ Tm m ]
      (e₀ ≡ F₀ [ K c · arg₀ ]*) × (F ≡ frame*-⋯ F₀ σ Vσ) × (arg ≡ arg₀ ⋯ σ)
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c [] eq
  with headApp σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value [] (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with headK σ a₀ (sym aeq)
...   | inj₁ (x , refl) = ⊥-elim (var-app-absurd Γ-S ⊢e)
...   | inj₂ refl = [] , b₀ , refl , refl , beq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (□· e₃ ∷ F*) eq
  with headApp σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (□· e₃ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with _ , _ , (_ , _ , ⊢a₀) , _ , _ ← IF.inv-app ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S a₀ ⊢a₀ σ Vσ c F* (sym aeq)
      = (□· b₀) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong □·_ beq) Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (_·□ {e₁ = v} V₁ ∷ F*) eq
  with headApp σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (_·□ {e₁ = v} V₁ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with _ , _ , (_ , _ , ⊢a₀) , (_ , _ , ⊢b₀) , _ ← IF.inv-app ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S b₀ ⊢b₀ σ Vσ c F* (sym beq)
      = (value-⋯⁻¹ σ Vσ a₀ (subst Value aeq V₁) ·□) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (IF.·□-cong aeq V₁ (value-⋯ (value-⋯⁻¹ σ Vσ a₀ (subst Value aeq V₁)) σ Vσ)) Feq ,
        argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (□⊗ e₃ ∷ F*) eq
  with head⊗′ σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (□⊗ e₃ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with _ , _ , (_ , _ , ⊢a₀) , _ , _ ← IF.inv-pair ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S a₀ ⊢a₀ σ Vσ c F* (sym aeq)
      = (□⊗ b₀) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong □⊗_ beq) Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (_⊗□ {e₁ = v} V₁ ∷ F*) eq
  with head⊗′ σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (_⊗□ {e₁ = v} V₁ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with _ , _ , (_ , _ , ⊢a₀) , (_ , _ , ⊢b₀) , _ ← IF.inv-pair ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S b₀ ⊢b₀ σ Vσ c F* (sym beq)
      = (value-⋯⁻¹ σ Vσ a₀ (subst Value aeq V₁) ⊗□) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (IF.⊗□-cong aeq V₁ (value-⋯ (value-⋯⁻¹ σ Vσ a₀ (subst Value aeq V₁)) σ Vσ)) Feq ,
        argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (□; e₃ ∷ F*) eq
  with headSeq σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (□; e₃ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with _ , _ , (_ , _ , ⊢a₀) , _ , _ ← IF.inv-seq ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S a₀ ⊢a₀ σ Vσ c F* (sym aeq)
      = (□; b₀) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong □;_ beq) Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (`let-`in e₃ ∷ F*) eq
  with headLet σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (`let-`in e₃ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with γ₁ , γ₂ , p/s , (_ , _ , ⊢a₀) , _ , _ ← IF.inv-let ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S a₀ ⊢a₀ σ Vσ c F* (sym aeq)
      = (`let-`in b₀) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong `let-`in_ beq) Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (`let⊗-`in e₃ ∷ F*) eq
  with headLetpair σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (`let⊗-`in e₃ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (a₀ , b₀ , refl , aeq , beq)
      with γ₁ , γ₂ , p/s , d , (_ , _ , ⊢a₀) , _ , _ ← IF.inv-letpair ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S a₀ ⊢a₀ σ Vσ c F* (sym aeq)
      = (`let⊗-`in b₀) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong `let⊗-`in_ beq) Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (`inj□ i ∷ F*) eq
  with headInj′ σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (`inj□ i ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (v₀ , refl , veq)
      with _ , _ , ⊢v₀ ← IF.inv-inj ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S v₀ ⊢v₀ σ Vσ c F* (sym veq)
      = (`inj□ i) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ refl Feq , argeq
frameApp-reflect Γ-S e₀ ⊢e σ Vσ c (`case□`of⟨ e₁ ; e₂ ⟩ ∷ F*) eq
  with headCase σ e₀ eq
... | inj₁ (x , refl) = ⊥-elim (plugApp-not-value (`case□`of⟨ e₁ ; e₂ ⟩ ∷ F*) (subst Value eq (Vσ x)))
... | inj₂ (s₀ , c₁ , c₂ , refl , seq , beq1 , beq2)
      with γ₁ , γ₂ , p/s , (_ , _ , ⊢s₀) , _ , _ , _ ← IF.inv-case ⊢e
      with F₀ , arg₀ , refl , Feq , argeq ← frameApp-reflect Γ-S s₀ ⊢s₀ σ Vσ c F* (sym seq)
      = (`case□`of⟨ c₁ ; c₂ ⟩) ∷ F₀ , arg₀ , refl ,
        cong₂ L._∷_ (cong₂ (λ u v → `case□`of⟨ u ; v ⟩) beq1 beq2) Feq , argeq


------------------------------------------------------------------------
-- R-New codomain bridge (copied from Theorems.agda; reused for sim<- RU-New).
------------------------------------------------------------------------

□·-cong : {e₁ e₂ : Tm n} → e₁ ≡ e₂ → (□· e₁) ≡ (□· e₂)
□·-cong refl = refl

·□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ·□) ≡ (V₂ ·□)
·□-cong refl = cong _·□ Value-irr

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (□· e₂)        Vϕ Vψ eq = cong □·_ (⋯-cong e₂ eq)
frame-cong (V₁ ·□)        Vϕ Vψ eq = ·□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))
frame-cong (`inj□ i)      Vϕ Vψ eq = refl
frame-cong (`case□`of⟨ e₁ ; e₂ ⟩) Vϕ Vψ eq =
  cong₂ `case□`of⟨_;_⟩ (⋯-cong e₁ (eq ~↑)) (⋯-cong e₂ (eq ~↑))

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (□· e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □·_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ·□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ·□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
frame-fusion-gen (`inj□ i)      {ϕ} Vϕ {ξ} Vξ Vϕξ = refl
frame-fusion-gen (`case□`of⟨ e₁ ; e₂ ⟩) {ϕ} Vϕ {ξ} Vξ Vϕξ =
  cong₂ `case□`of⟨_;_⟩ (fusion e₁ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₁ (λ x → sym (dist-↑-· ϕ ξ x)))
                        (fusion e₂ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₂ (λ x → sym (dist-↑-· ϕ ξ x)))



tL : Tm (4 + n)
tL = (((` 0F) ⊗ (` 3F)) ⊗ *) ⊗ (((` 1F) ⊗ (` 2F)) ⊗ *)

rnew-bridge : (E : Frame* m) (σ : m →ₛ n) (Vσ : VSub σ) →
  UP.ν (UP.φ UP.acq (UP.φ UP.acq UP.⟪
        (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]* ⟫))
    UP.≋
  U[ TP.ν (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
        TP.⟪ (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 1F) ⊗ (` 0F) ]* ⟫ ] σ
rnew-bridge {m} {n} E σ Vσ =
  ≡→≋ (cong UP.ν (cong (UP.φ UP.acq) (cong (UP.φ UP.acq) (cong UP.⟪_⟫ bodyEq))))
  where
    cA : Tm (1 + (1 + (2 + n)))
    cA = chanTriple ((` 0F) , 1F , wk *) ⋯ weaken* ⦃ Kᵣ ⦄ 1
    cB : Tm (1 + (1 + (2 + n)))
    cB = chanTriple ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *)
    A : 1 →ₛ (1 + (1 + (2 + n)))
    A = λ _ → cA
    B : 1 →ₛ (1 + (1 + (2 + n)))
    B = λ _ → cB
    Bσ : m →ₛ (1 + (1 + (2 + n)))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 1 ⋯ weaken* ⦃ Kᵣ ⦄ 1
    σ′ : (1 + 1 + m) →ₛ (1 + (1 + (2 + n)))
    σ′ = (A ++ₛ B) ++ₛ Bσ
    VcAch : Value (chanTriple ((` 0F) , 1F , wk *))
    VcAch = V-⊗ (V-⊗ V-` V-`) (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
    VcBch : Value (chanTriple ((` 0F) , suc (weaken* ⦃ Kᵣ ⦄ 1 1F) , wk *))
    VcBch = V-⊗ (V-⊗ V-` V-`) (value-⋯ V-K (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`))
    VcA : Value cA
    VcA = value-⋯ VcAch (weaken* ⦃ Kᵣ ⦄ 1) (λ _ → V-`)
    VA : VSub A
    VA = λ _ → VcA
    VB : VSub B
    VB = λ _ → VcBch
    Vσ′ : VSub σ′
    Vσ′ = ++ₛ-VSub {σ₁ = A ++ₛ B}
            (++ₛ-VSub {σ₁ = A} VA VB)
            (weaken-VSub 1 (weaken-VSub 1 (weaken-VSub 2 Vσ)))
    weakenEq : Bσ ≗ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 4)
    weakenEq i = fusion (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ 1)
               ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ 1)
    perF : (F : Frame m) → frame-⋯ (F ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame-⋯ F σ Vσ ⋯ᶠ weaken* ⦃ Kᵣ ⦄ 4
    perF F = frame-fusion-gen F (λ _ → V-`) Vσ′ (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x))
           ■ frame-cong F (λ x → Vσ′ (weaken* ⦃ Kᵣ ⦄ 2 x)) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)) weakenEq
           ■ sym (frame-fusion-gen F Vσ (λ _ → V-`) (λ x → value-⋯ (Vσ x) (weaken* ⦃ Kᵣ ⦄ 4) (λ _ → V-`)))
    frameEqA : (E* : Frame* m) → frame*-⋯ (E* ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′ ≡ frame*-⋯ E* σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4
    frameEqA []        = refl
    frameEqA (F ∷ E*) = cong₂ _∷_ (perF F) (frameEqA E*)
    leafTermEq : ((` 1F) ⊗ (` 0F)) ⋯ σ′ ≡ tL
    leafTermEq = refl
    bodyEq : (frame*-⋯ E σ Vσ ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 4) [ tL ]*
             ≡ ((E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) [ (` 1F) ⊗ (` 0F) ]*) ⋯ σ′
    bodyEq = sym (frame-plug* (E ⋯ᶠ* weaken* ⦃ Kᵣ ⦄ 2) σ′ Vσ′
                 ■ cong₂ _[_]* (frameEqA E) leafTermEq)

------------------------------------------------------------------------
-- φ-free body inversion for the ν-headed reverse channel cases.
--
--   When U[ ν B₁ B₂ P₀ ] σ ≡ ν Body and Body's head is NOT a φ (i.e. the
--   redex sits in a thread/parallel body, as in RU-Close/Com/Choice), the
--   φ-telescope must have depth 0: syncs B₁ = syncs B₂ = 0, which forces
--   each Bᵢ to be [] or a singleton.  In that case UB[_] collapses
--   definitionally and Body ≡ U[ P₀ ] bigσ with a CONCRETE substitution.
--
--   `notφ` is the head-non-φ witness, supplied by the caller as the body
--   shape demanded by the firing untyped rule (e.g. A ∥ B for RU-Close).
------------------------------------------------------------------------

-- A bind group with syncs B = 0 is [] or a singleton.
syncs0-shape : (B : TP.BindGroup) → syncs B ≡ 0
             → (B ≡ []) Sum.⊎ (Σ[ b ∈ ℕ ] (B ≡ b ∷ []))
syncs0-shape []            _  = Sum.inj₁ refl
syncs0-shape (b ∷ [])      _  = Sum.inj₂ (b , refl)
syncs0-shape (b ∷ _ ∷ _)   ()

-- The concrete leaf substitution U[ ν [b₁] [b₂] P₀ ] σ uses on its body.
-- For singleton B₁=[b₁], B₂=[b₂] the φ-telescope is empty and the body is
-- exactly U[ P₀ ] (νσ b₁ b₂ σ).
νσ : ∀ {m n} → (b₁ b₂ : ℕ) → (m →ₛ n) → (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m →ₛ 2 + n)
νσ b₁ b₂ σ =
  ((λ i → (λ (_ : 𝔽 (sum (b₁ ∷ []))) → chanTriple (* , 0F , *)) i ⋯ weaken* ⦃ Kᵣ ⦄ 0) ++ₛ
    (λ (_ : 𝔽 (sum (b₂ ∷ []))) → chanTriple (* , weaken* ⦃ Kᵣ ⦄ 0 1F , *)))
  ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0)

-- U[ ν [b₁] [b₂] P₀ ] σ collapses (no φ binders) to ν (U[ P₀ ] (νσ …)).
U-ν-singleton : ∀ {m n} (b₁ b₂ : ℕ)
                (P₀ : TP.Proc (sum (b₁ ∷ []) + sum (b₂ ∷ []) + m)) (σ : m →ₛ n)
              → U[ TP.ν (b₁ ∷ []) (b₂ ∷ []) P₀ ] σ ≡ UP.ν (U[ P₀ ] (νσ b₁ b₂ σ))
U-ν-singleton b₁ b₂ P₀ σ = refl

-- For the ν-headed reverse channel cases the firing untyped rule demands a body
-- whose head is NOT a φ — for RU-Close/Com/Choice the body is a ∥.  Since
-- UB[ b ∷ c ∷ B ] heads with φ, a ∥-headed ν body forces BOTH bind groups to be
-- [] or a singleton (syncs Bᵢ = 0).  This lemma reads that B-shape off the body
-- head and returns the (non-φ) collapsed leaf — i.e. the body is literally the
-- U[_]-image of the source P₀ under the telescope substitution that U[_] uses.
-- We package the four (≤singleton) shape combinations as a Sum the caller
-- dispatches; the singleton/singleton component is the one a well-typed close
-- (each endpoint has ≥1 handle) lands in, and is `refl`.
-- ν-injectivity on the untyped Proc.
ν-inj : ∀ {n} {X Y : UP.Proc (2 + n)} → UP.ν X ≡ UP.ν Y → X ≡ Y
ν-inj refl = refl

inv-U-ν-∥-shape : ∀ {m n} (B₁ B₂ : TP.BindGroup)
              (P₀ : TP.Proc (sum B₁ + sum B₂ + m)) (σ : m →ₛ n) {A B : UP.Proc (2 + n)}
          → UP.ν (A UP.∥ B) ≡ U[ TP.ν B₁ B₂ P₀ ] σ
          → (Σ[ b₁ ∈ ℕ ] Σ[ b₂ ∈ ℕ ] (B₁ ≡ b₁ ∷ []) × (B₂ ≡ b₂ ∷ []))
            Sum.⊎ ((syncs B₁ ≡ 0) × (syncs B₂ ≡ 0))
inv-U-ν-∥-shape (b ∷ _ ∷ _) B₂ P₀ σ eq with ν-inj eq
... | ()
inv-U-ν-∥-shape (b₁ ∷ []) (b₂ ∷ _ ∷ _) P₀ σ eq with ν-inj eq
... | ()
inv-U-ν-∥-shape (b₁ ∷ []) (b₂ ∷ []) P₀ σ eq =
  Sum.inj₁ (b₁ , b₂ , refl , refl)
inv-U-ν-∥-shape [] (b₂ ∷ _ ∷ _) P₀ σ eq with ν-inj eq
... | ()
inv-U-ν-∥-shape [] (b₂ ∷ []) P₀ σ eq = Sum.inj₂ (refl , refl)
inv-U-ν-∥-shape [] []        P₀ σ eq = Sum.inj₂ (refl , refl)
inv-U-ν-∥-shape (b₁ ∷ []) [] P₀ σ eq = Sum.inj₂ (refl , refl)
