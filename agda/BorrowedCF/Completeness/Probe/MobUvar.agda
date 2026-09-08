-- | Mechanisation of the DECISION-mobility.md counterexample (§1): the closed
--   term whose declarative typing goes through the mobility of a component that
--   the ALGORITHM only knows as a unification variable.
--
--     f = λ(x : ⟨ !Unit ; (acq ; end‼) ⟩).
--           let⊗ (x₁ , x₂) = lsplit_{!Unit} x in
--             (end‼ (acq x₂)) ; (send (unit , x₁))
--
--   The body uses x₂ BEFORE x₁, while `lsplit` hands out the ORDERED pair
--   ⟨t₁⟩ ⊗ᴸ ⟨t₂⟩, so T-LetPair gives the body the structure x₁ ; x₂.  The gap is
--   bridged by `;-commMob`, which needs `Mobile ⟨ acq ; end ‼ ⟩` (mobile-x₂).
--   Algorithmically A-LSplit types the second component as ⟨ `` α ⟩ for a fresh
--   unification variable α, and ⟨ `` α ⟩ is NOT mobile (¬mobile-uvar), nor is
--   ⟨ msg ‼ `⊤ ⟩ (¬mobile-msg), so no mobility rule applies and the algorithm
--   rejects the term.
module BorrowedCF.Completeness.Probe.MobUvar where

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic.Solved using (subTy; subTy-mobile)
open import BorrowedCF.Simulation.BackwardSoup.GroupOrder using (¬mobile-noAcq; NoAcq)

open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- 1.  Sessions and the arrow of the λ.

t₁ t₂ t₀ : 𝕊 0
t₁ = msg ‼ `⊤            -- !Unit
t₂ = acq ; end ‼         -- Acq ; Term
t₀ = t₁ ; t₂

¬skips-t₁ : ¬ Skips t₁
¬skips-t₁ ()

¬skips-t₂ : ¬ Skips t₂
¬skips-t₂ (() ; _)

a₀ : Arr
a₀ = record { lin = 𝟙 ; dir = 𝟙 ; mob = S ; eff = 𝕀 ; ω⇒M = λ() ; ω⇒𝟙 = λ() }

------------------------------------------------------------------------
-- 2.  The term.

body : Tm 3
body = (K (`end ‼) ·¹ (K `acq ·¹ (` 1F))) ; (K `send ·¹ (* ⊗ (` 0F)))

f : Tm 0
f = ƛ (`let⊗ (K (`lsplit t₁) ·¹ (` 0F)) `in body)

------------------------------------------------------------------------
-- 3.  The two mobility facts.

--  x₂ : ⟨ acq ; end ‼ ⟩ IS mobile — this is what the declarative derivation uses.
mobile-x₂ : Mobile ⟨ t₂ ⟩
mobile-x₂ = ⟨ end ‼ , end , ≃-refl ⟩

--  ⟨ !Unit ⟩ is not mobile.
¬mobile-msg : ¬ Mobile ⟨ t₁ ⟩
¬mobile-msg = ¬mobile-noAcq NoAcq.msg

--  A bare unification variable is not mobile either: substituting `end` for it
--  and using `subTy-mobile` reduces the claim to ¬mobile-noAcq.
¬mobile-uvar : ∀ {α : UVar} → ¬ Mobile ⟨ `` α ⟩
¬mobile-uvar {uvar ‼ v} m = ¬mobile-noAcq NoAcq.end (subTy-mobile {σ = UV.someSub} m)
¬mobile-uvar {uvar ⁇ v} m = ¬mobile-noAcq NoAcq.end (subTy-mobile {σ = UV.someSub} m)

------------------------------------------------------------------------
-- 4.  The declarative derivation.

Cx₁ : Ctx 1
Cx₁ = ⟨ t₀ ⟩ ⸴ []

Cx₃ : Ctx 3
Cx₃ = ⟨ t₁ ⟩ ⸴ ⟨ t₂ ⟩ ⸴ Cx₁

-- applying an unrestricted constant, at the ambient effect ϵ
app-const : ∀ {n} {Γ : Ctx n} {γ : Struct n} {c T U a ϵ} {e : Tm n} →
            (⊢c : ⊢ c ∶ T ⟨ a ⟩→ U) → Arr.eff a ≤ϵ ϵ →
            Γ ; γ ⊢ e ∶ T ∣ ϵ →
            Γ ; ([] ∥ γ) ⊢ (K c) ·¹ e ∶ U ∣ ϵ
app-const ⊢c ≤a d = T-AppUnr (constFnUnr ⊢c) ≤a (T-Conv ≃-refl ℙ≤ϵ (T-Const ⊢c)) d

close-part : Cx₃ ; ([] ∥ ([] ∥ (` 1F))) ⊢ (K (`end ‼) ·¹ (K `acq ·¹ (` 1F))) ∶ `⊤ ∣ 𝕀
close-part = app-const `end 𝕀≤𝕀 (app-const `acq ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Var 1F refl)))

send-part : Cx₃ ; ([] ∥ ([] ∥ (` 0F))) ⊢ (K `send ·¹ (* ⊗ (` 0F))) ∶ `⊤ ∣ 𝕀
send-part = app-const (`send `⊤) 𝕀≤𝕀
              (T-Conv ≃-refl ℙ≤ϵ (T-Pair par par (T-Const `unit) (T-Var 0F refl)))

-- the body's own structure is x₂ ; x₁; T-LetPair prescribes (x₁ ; x₂) ∥ [].
body-decl : Cx₃ ; (((` 0F) ; (` 1F)) ∥ []) ⊢ body ∶ `⊤ ∣ 𝕀
body-decl = T-Weaken
  (≼-refl (≈-trans (≈-trans (;-cong (≈-trans ∥-unit₁ ∥-unit₁) (≈-trans ∥-unit₁ ∥-unit₁))
                            (;-commMob (inj₁ (` mobile-x₂))))
                   (≈-sym ∥-unit₂)))
  (T-Seq `⊤ close-part send-part)

e₁-decl : Cx₁ ; (` 0F) ⊢ (K (`lsplit t₁) ·¹ (` 0F)) ∶ ⟨ t₁ ⟩ ⊗⟨ L ⟩ ⟨ t₂ ⟩ ∣ 𝕀
e₁-decl = T-Weaken (≼-refl ∥-unit₁)
  (app-const (`lsplit t₁ t₂ ¬skips-t₁ ¬skips-t₂) ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)))

decl : [] ; [] ⊢ f ∶ ⟨ t₀ ⟩ ⟨ a₀ ⟩→ `⊤ ∣ ℙ
decl = T-Abs (λ()) (λ()) (T-LetPair par {γ₁ = ` 0F} {γ₂ = []} e₁-decl body-decl)
