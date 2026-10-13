-- | Undoing the communication weakening `wkₚ a c` on *structures*.
--
--   The `R-Com` redex is stated through `wkρ = wkₚ (b₁ + sum B₁) (b₂ + sum B₂)`,
--   which inserts the sent handle `x` at the head of the first binder block and
--   the received handle `y` at the head of the second.  Rebuilding the reduct's
--   `TP-Res` needs the *structure* inequality in the small (post-communication)
--   scope, and the only sane way to get it is to push the big one through a
--   structure substitution `del` that erases `x` and `y` and shifts everything
--   else back.  `del` is a substitution, not a renaming, precisely because the
--   two erased handles have no image.
--
--   `wkₚ-A` / `wkₚ-B` / `wkₚ-C` are transcribed from
--   `Simulation.ForwardSoup.Local.Com` (private there), together with
--   `lift*-↑ˡ` / `lift*-↑ʳ` from `Simulation.ForwardSoup.Renaming`; that tree is
--   far too expensive to import for four lines of Fin arithmetic.
module BorrowedCF.Safety.Preservation.Support.ComWeaken where

open import BorrowedCF.Prelude
open import BorrowedCF.Types
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Terms using (wkₚ; weakenᵣ; Kᵣ)
open import BorrowedCF.Processes.Typed using (BindGroup; structNSeq; structBinder)
open import Data.Nat.ListAction using (sum)

import BorrowedCF.Context.Substitution as 𝐂
open import BorrowedCF.Context.Substitution using (_∶_⇒_)
import BorrowedCF.Terms as Terms

open Nat.Variables
open Nat using (+-assoc)
open Fin.Patterns

private variable kk ll : ℕ

------------------------------------------------------------------------
-- Three one-line traversal lemmas, proved by direct induction so that no
-- Kit/CKit instance search is involved.
------------------------------------------------------------------------

⋯ᵣ∘ : (Q : Struct m) (ρ₁ : 𝔽 m → 𝔽 kk) (ρ₂ : 𝔽 kk → 𝔽 ll) →
  Q 𝐂.⋯ᵣ ρ₁ 𝐂.⋯ᵣ ρ₂ ≡ Q 𝐂.⋯ᵣ (ρ₂ ∘ ρ₁)
⋯ᵣ∘ (` x) ρ₁ ρ₂ = refl
⋯ᵣ∘ [] ρ₁ ρ₂ = refl
⋯ᵣ∘ (Q₁ ∥ Q₂) ρ₁ ρ₂ = cong₂ _∥_ (⋯ᵣ∘ Q₁ ρ₁ ρ₂) (⋯ᵣ∘ Q₂ ρ₁ ρ₂)
⋯ᵣ∘ (Q₁ ; Q₂) ρ₁ ρ₂ = cong₂ _;_ (⋯ᵣ∘ Q₁ ρ₁ ρ₂) (⋯ᵣ∘ Q₂ ρ₁ ρ₂)

⋯ᵣ⋯ₛ : (Q : Struct m) (ρ : 𝔽 m → 𝔽 kk) (σ : 𝔽 kk → Struct ll) →
  Q 𝐂.⋯ᵣ ρ 𝐂.⋯ σ ≡ Q 𝐂.⋯ (σ ∘ ρ)
⋯ᵣ⋯ₛ (` x) ρ σ = refl
⋯ᵣ⋯ₛ [] ρ σ = refl
⋯ᵣ⋯ₛ (Q₁ ∥ Q₂) ρ σ = cong₂ _∥_ (⋯ᵣ⋯ₛ Q₁ ρ σ) (⋯ᵣ⋯ₛ Q₂ ρ σ)
⋯ᵣ⋯ₛ (Q₁ ; Q₂) ρ σ = cong₂ _;_ (⋯ᵣ⋯ₛ Q₁ ρ σ) (⋯ᵣ⋯ₛ Q₂ ρ σ)

⋯ₛ≗ᵣ : (Q : Struct m) {σ : 𝔽 m → Struct kk} {ρ : 𝔽 m → 𝔽 kk} →
  (∀ x → σ x ≡ ` (ρ x)) → Q 𝐂.⋯ σ ≡ Q 𝐂.⋯ᵣ ρ
⋯ₛ≗ᵣ (` x) eq = eq x
⋯ₛ≗ᵣ [] eq = refl
⋯ₛ≗ᵣ (Q₁ ∥ Q₂) eq = cong₂ _∥_ (⋯ₛ≗ᵣ Q₁ eq) (⋯ₛ≗ᵣ Q₂ eq)
⋯ₛ≗ᵣ (Q₁ ; Q₂) eq = cong₂ _;_ (⋯ₛ≗ᵣ Q₁ eq) (⋯ₛ≗ᵣ Q₂ eq)

⋯ᵣ-cong : (Q : Struct m) {ρ₁ ρ₂ : 𝔽 m → 𝔽 kk} → ρ₁ ≗ ρ₂ → Q 𝐂.⋯ᵣ ρ₁ ≡ Q 𝐂.⋯ᵣ ρ₂
⋯ᵣ-cong (` x) eq = cong `_ (eq x)
⋯ᵣ-cong [] eq = refl
⋯ᵣ-cong (Q₁ ∥ Q₂) eq = cong₂ _∥_ (⋯ᵣ-cong Q₁ eq) (⋯ᵣ-cong Q₂ eq)
⋯ᵣ-cong (Q₁ ; Q₂) eq = cong₂ _;_ (⋯ᵣ-cong Q₁ eq) (⋯ᵣ-cong Q₂ eq)

------------------------------------------------------------------------
-- Where `wkₚ a c` sends the three families of variables.
------------------------------------------------------------------------

lift*-↑ˡ : (ρ : 𝔽 m → 𝔽 n) (b : ℕ) (x : 𝔽 b) → Terms._↑*_ ρ b (x ↑ˡ m) ≡ x ↑ˡ n
lift*-↑ˡ ρ (suc b) 0F = refl
lift*-↑ˡ ρ (suc b) (Fin.suc x) = cong Fin.suc (lift*-↑ˡ ρ b x)

lift*-↑ʳ : (ρ : 𝔽 m → 𝔽 n) (b : ℕ) (x : 𝔽 m) → Terms._↑*_ ρ b (b ↑ʳ x) ≡ b ↑ʳ ρ x
lift*-↑ʳ ρ zero x = refl
lift*-↑ʳ ρ (suc b) x = cong Fin.suc (lift*-↑ʳ ρ b x)

module _ (a c : ℕ) {kk : ℕ} where
  private
    cast₁ : 𝔽 (suc (a + c + kk)) → 𝔽 (suc a + (c + kk))
    cast₁ = Fin.cast (cong suc (+-assoc a c kk))

    cast₂ : 𝔽 (suc a + suc (c + kk)) → 𝔽 (suc a + suc c + kk)
    cast₂ = Fin.cast (sym (+-assoc (suc a) (suc c) kk))

  wkₚ-A : (v : 𝔽 a) → wkₚ {n = kk} a c ((v ↑ˡ c) ↑ˡ kk) ≡ ((Fin.suc v ↑ˡ suc c) ↑ˡ kk)
  wkₚ-A v =
    cong (λ z → cast₂ (Terms._↑*_ weakenᵣ (suc a) z)) step₁
      ■ cong cast₂ (lift*-↑ˡ weakenᵣ (suc a) (Fin.suc v))
      ■ step₃
    where
    step₁ : cast₁ (Fin.suc ((v ↑ˡ c) ↑ˡ kk)) ≡ Fin.suc v ↑ˡ (c + kk)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c kk)) (Fin.suc ((v ↑ˡ c) ↑ˡ kk))
       ■ cong suc (Fin.toℕ-↑ˡ (v ↑ˡ c) kk ■ Fin.toℕ-↑ˡ v c)
       ■ sym (Fin.toℕ-↑ˡ (Fin.suc v) (c + kk)))
    step₃ : cast₂ (Fin.suc v ↑ˡ suc (c + kk)) ≡ ((Fin.suc v ↑ˡ suc c) ↑ˡ kk)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) kk)) (Fin.suc v ↑ˡ suc (c + kk))
       ■ Fin.toℕ-↑ˡ (Fin.suc v) (suc (c + kk))
       ■ sym (Fin.toℕ-↑ˡ (Fin.suc v ↑ˡ suc c) kk ■ Fin.toℕ-↑ˡ (Fin.suc v) (suc c)))

  wkₚ-B : (w : 𝔽 c) → wkₚ {n = kk} a c ((a ↑ʳ w) ↑ˡ kk) ≡ ((suc a ↑ʳ Fin.suc w) ↑ˡ kk)
  wkₚ-B w =
    cong (λ z → cast₂ (Terms._↑*_ weakenᵣ (suc a) z)) step₁
      ■ cong cast₂ (lift*-↑ʳ weakenᵣ (suc a) (w ↑ˡ kk))
      ■ step₃
    where
    step₁ : cast₁ (Fin.suc ((a ↑ʳ w) ↑ˡ kk)) ≡ suc a ↑ʳ (w ↑ˡ kk)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c kk)) (Fin.suc ((a ↑ʳ w) ↑ˡ kk))
       ■ cong suc (Fin.toℕ-↑ˡ (a ↑ʳ w) kk ■ Fin.toℕ-↑ʳ a w)
       ■ sym (Fin.toℕ-↑ʳ (suc a) (w ↑ˡ kk) ■ cong (suc a +_) (Fin.toℕ-↑ˡ w kk)))
    step₃ : cast₂ (suc a ↑ʳ Fin.suc (w ↑ˡ kk)) ≡ ((suc a ↑ʳ Fin.suc w) ↑ˡ kk)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) kk)) (suc a ↑ʳ Fin.suc (w ↑ˡ kk))
       ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc (w ↑ˡ kk))
       ■ cong (λ t → suc a + suc t) (Fin.toℕ-↑ˡ w kk)
       ■ sym (Fin.toℕ-↑ˡ (suc a ↑ʳ Fin.suc w) kk ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc w)))

  wkₚ-C : (y : 𝔽 kk) → wkₚ {n = kk} a c ((a + c) ↑ʳ y) ≡ ((suc a + suc c) ↑ʳ y)
  wkₚ-C y =
    cong (λ z → cast₂ (Terms._↑*_ weakenᵣ (suc a) z)) step₁
      ■ cong cast₂ (lift*-↑ʳ weakenᵣ (suc a) (c ↑ʳ y))
      ■ step₃
    where
    step₁ : cast₁ (Fin.suc ((a + c) ↑ʳ y)) ≡ suc a ↑ʳ (c ↑ʳ y)
    step₁ = Fin.toℕ-injective
      (Fin.toℕ-cast (cong suc (+-assoc a c kk)) (Fin.suc ((a + c) ↑ʳ y))
       ■ cong suc (Fin.toℕ-↑ʳ (a + c) y)
       ■ cong suc (+-assoc a c (Fin.toℕ y))
       ■ sym (Fin.toℕ-↑ʳ (suc a) (c ↑ʳ y) ■ cong (suc a +_) (Fin.toℕ-↑ʳ c y)))
    step₃ : cast₂ (suc a ↑ʳ Fin.suc (c ↑ʳ y)) ≡ ((suc a + suc c) ↑ʳ y)
    step₃ = Fin.toℕ-injective
      (Fin.toℕ-cast (sym (+-assoc (suc a) (suc c) kk)) (suc a ↑ʳ Fin.suc (c ↑ʳ y))
       ■ Fin.toℕ-↑ʳ (suc a) (Fin.suc (c ↑ʳ y))
       ■ cong (λ t → suc a + suc t) (Fin.toℕ-↑ʳ c y)
       ■ sym (Fin.toℕ-↑ʳ (suc a + suc c) y ■ +-assoc (suc a) (suc c) (Fin.toℕ y)))

------------------------------------------------------------------------
-- A three-way view of a variable of a doubly-blocked scope.
------------------------------------------------------------------------

data Split3 (a c : ℕ) {kk : ℕ} : 𝔽 (a + c + kk) → Set where
  inA : (v : 𝔽 a) → Split3 a c ((v ↑ˡ c) ↑ˡ kk)
  inB : (w : 𝔽 c) → Split3 a c ((a ↑ʳ w) ↑ˡ kk)
  inC : (y : 𝔽 kk) → Split3 a c ((a + c) ↑ʳ y)

split3 : ∀ a c {kk} (x : 𝔽 (a + c + kk)) → Split3 a c x
split3 a c x with splitAt (a + c) x in eq
... | inj₂ y = subst (Split3 a c) (splitAt⁻¹-↑ʳ eq) (inC y)
... | inj₁ u with splitAt a u in eq′
...   | inj₁ v = subst (Split3 a c) (cong (_↑ˡ _) (splitAt⁻¹-↑ˡ eq′) ■ splitAt⁻¹-↑ˡ eq) (inA v)
...   | inj₂ w = subst (Split3 a c) (cong (_↑ˡ _) (splitAt⁻¹-↑ʳ eq′) ■ splitAt⁻¹-↑ˡ eq) (inB w)

------------------------------------------------------------------------
-- `del a c` : erase the two inserted handles, shift everything else back.
------------------------------------------------------------------------

delBlock : ∀ a c {kk} → 𝔽 (suc a + suc c) → Struct (a + c + kk)
delBlock a c {kk} u with splitAt (suc a) u
... | inj₁ 0F          = []
... | inj₁ (Fin.suc v) = ` ((v ↑ˡ c) ↑ˡ kk)
... | inj₂ 0F          = []
... | inj₂ (Fin.suc w) = ` ((a ↑ʳ w) ↑ˡ kk)

del : ∀ a c {kk} → 𝔽 (suc a + suc c + kk) → Struct (a + c + kk)
del a c {kk} z with splitAt (suc a + suc c) z
... | inj₁ u = delBlock a c u
... | inj₂ y = ` ((a + c) ↑ʳ y)

del-A : ∀ a c {kk} (v : 𝔽 a) → del a c {kk} ((Fin.suc v ↑ˡ suc c) ↑ˡ kk) ≡ ` ((v ↑ˡ c) ↑ˡ kk)
del-A a c {kk} v
  rewrite splitAt-↑ˡ (suc a + suc c) (Fin.suc v ↑ˡ suc c) kk
        | splitAt-↑ˡ (suc a) (Fin.suc v) (suc c) = refl

del-B : ∀ a c {kk} (w : 𝔽 c) → del a c {kk} ((suc a ↑ʳ Fin.suc w) ↑ˡ kk) ≡ ` ((a ↑ʳ w) ↑ˡ kk)
del-B a c {kk} w
  rewrite splitAt-↑ˡ (suc a + suc c) (suc a ↑ʳ Fin.suc w) kk
        | splitAt-↑ʳ (suc a) (suc c) (Fin.suc w) = refl

del-C : ∀ a c {kk} (y : 𝔽 kk) → del a c {kk} ((suc a + suc c) ↑ʳ y) ≡ ` ((a + c) ↑ʳ y)
del-C a c {kk} y rewrite splitAt-↑ʳ (suc a + suc c) kk y = refl

del-x : ∀ a c {kk} → del a c {kk} ((0F ↑ˡ suc c) ↑ˡ kk) ≡ []
del-x a c {kk}
  rewrite splitAt-↑ˡ (suc a + suc c) (Fin.zero {a} ↑ˡ suc c) kk = refl

del-y : ∀ a c {kk} → del a c {kk} ((suc a ↑ʳ 0F) ↑ˡ kk) ≡ []
del-y a c {kk}
  rewrite splitAt-↑ˡ (suc a + suc c) (suc a ↑ʳ Fin.zero {c}) kk
        | splitAt-↑ʳ (suc a) (suc c) (Fin.zero {c}) = refl

-- | `del` undoes `wkₚ`.
del-wkₚ : ∀ a c {kk} (x : 𝔽 (a + c + kk)) → del a c (wkₚ a c x) ≡ ` x
del-wkₚ a c x with split3 a c x
... | inA v = cong (del a c) (wkₚ-A a c v) ■ del-A a c v
... | inB w = cong (del a c) (wkₚ-B a c w) ■ del-B a c w
... | inC y = cong (del a c) (wkₚ-C a c y) ■ del-C a c y

⋯-wkₚ-del : ∀ a c {kk} (γ : Struct (a + c + kk)) → (γ 𝐂.⋯ᵣ wkₚ a c) 𝐂.⋯ del a c ≡ γ
⋯-wkₚ-del a c γ = ⋯ᵣ⋯ₛ γ (wkₚ a c) (del a c) ■ ⋯ₛ≗ᵣ γ (del-wkₚ a c) ■ 𝐂.⋯-id γ (λ _ → refl)

------------------------------------------------------------------------
-- `del` is a legal structure substitution: it only ever erases, and an
-- erased slot is `[]`, which is both unrestricted and mobile.
------------------------------------------------------------------------

module _ {a c kk : ℕ} (Γ₁ : Ctx a) (Γ₂ : Ctx c) (Γ : Ctx kk) {T₁ T₂ : 𝕋} where
  private
    Δ : Ctx (suc a + suc c + kk)
    Δ = ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) ⸴* Γ

    Δ′ : Ctx (a + c + kk)
    Δ′ = (Γ₁ ⸴* Γ₂) ⸴* Γ

    lookA : (v : 𝔽 a) → Δ ﹫ ((Fin.suc v ↑ˡ suc c) ↑ˡ kk) ≡ Δ′ ﹫ ((v ↑ˡ c) ↑ˡ kk)
    lookA v =
        V.lookup-++ˡ ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) Γ (Fin.suc v ↑ˡ suc c)
      ■ V.lookup-++ˡ Γ₁ (T₂ ⸴ Γ₂) v
      ■ sym (V.lookup-++ˡ Γ₁ Γ₂ v)
      ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (v ↑ˡ c))

    lookB : (w : 𝔽 c) → Δ ﹫ ((suc a ↑ʳ Fin.suc w) ↑ˡ kk) ≡ Δ′ ﹫ ((a ↑ʳ w) ↑ˡ kk)
    lookB w =
        V.lookup-++ˡ ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) Γ (suc a ↑ʳ Fin.suc w)
      ■ V.lookup-++ʳ Γ₁ (T₂ ⸴ Γ₂) (Fin.suc w)
      ■ sym (V.lookup-++ʳ Γ₁ Γ₂ w)
      ■ sym (V.lookup-++ˡ (Γ₁ ⸴* Γ₂) Γ (a ↑ʳ w))

    lookC : (y : 𝔽 kk) → Δ ﹫ ((suc a + suc c) ↑ʳ y) ≡ Δ′ ﹫ ((a + c) ↑ʳ y)
    lookC y =
        V.lookup-++ʳ ((T₁ ⸴ Γ₁) ⸴* (T₂ ⸴ Γ₂)) Γ y
      ■ sym (V.lookup-++ʳ (Γ₁ ⸴* Γ₂) Γ y)

  del-⇒-var : (z : 𝔽 (suc a + suc c + kk)) →
    (del a c z ≡ []) ⊎ (∃[ y ] del a c z ≡ ` y × Δ ﹫ z ≡ Δ′ ﹫ y)
  del-⇒-var z with split3 (suc a) (suc c) z
  ... | inC y = inj₂ (_ , del-C a c y , lookC y)
  ... | inA 0F = inj₁ (del-x a c)
  ... | inA (Fin.suc v) = inj₂ (_ , del-A a c v , lookA v)
  ... | inB 0F = inj₁ (del-y a c)
  ... | inB (Fin.suc w) = inj₂ (_ , del-B a c w , lookB w)

  del-⇒ : del a c ∶ Δ ⇒ Δ′
  del-⇒ z with del-⇒-var z
  ... | inj₁ eq = (λ _ → subst (UnrCx Δ′) (sym eq) [])
                , (λ _ → subst (MobCx Δ′) (sym eq) [])
  ... | inj₂ (y , eq , leq) =
      (λ u → subst (UnrCx Δ′) (sym eq) (` subst Unr leq u))
    , (λ mo → subst (MobCx Δ′) (sym eq) (` subst Mobile leq mo))

------------------------------------------------------------------------
-- The binder structure of a group whose head block grows by one.
------------------------------------------------------------------------

structBinder-suc : ∀ b (B : BindGroup) →
  structBinder (suc b ∷ B)
    ≡ ((` 0F) ; ((structNSeq b 𝐂.⋯ᵣ 𝐂.wkʳ (sum B)) 𝐂.⋯ᵣ weakenᵣ))
      ∥ ((structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ b) 𝐂.⋯ᵣ weakenᵣ)
structBinder-suc b B = cong₂ _∥_ (cong ((` 0F) ;_) eq₁) eq₂
  where
  eq₁ : (structNSeq b 𝐂.⋯ᵣ weakenᵣ) 𝐂.⋯ᵣ 𝐂.wkʳ (sum B)
      ≡ (structNSeq b 𝐂.⋯ᵣ 𝐂.wkʳ (sum B)) 𝐂.⋯ᵣ weakenᵣ
  eq₁ = ⋯ᵣ∘ (structNSeq b) weakenᵣ (𝐂.wkʳ (sum B))
      ■ sym (⋯ᵣ∘ (structNSeq b) (𝐂.wkʳ (sum B)) weakenᵣ)

  eq₂ : structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ (suc b) ≡ (structBinder B 𝐂.⋯ᵣ 𝐂.wkˡ b) 𝐂.⋯ᵣ weakenᵣ
  eq₂ = sym (⋯ᵣ∘ (structBinder B) (𝐂.wkˡ b) weakenᵣ)

------------------------------------------------------------------------
-- Pushing `del` through the three components of the `TP-Res` structure.
------------------------------------------------------------------------

blockA-del : ∀ a c {kk} (Q : Struct a) →
  ((Q 𝐂.⋯ᵣ weakenᵣ) 𝐂.⋯ᵣ 𝐂.wkʳ (suc c) 𝐂.⋯ᵣ 𝐂.wkʳ kk) 𝐂.⋯ del a c
    ≡ Q 𝐂.⋯ᵣ 𝐂.wkʳ c 𝐂.⋯ᵣ 𝐂.wkʳ kk
blockA-del a c {kk} Q =
    cong (𝐂._⋯ del a c) (⋯ᵣ∘ (Q 𝐂.⋯ᵣ weakenᵣ) _ _ ■ ⋯ᵣ∘ Q _ _)
  ■ ⋯ᵣ⋯ₛ Q _ (del a c)
  ■ ⋯ₛ≗ᵣ Q (del-A a c)
  ■ sym (⋯ᵣ∘ Q (𝐂.wkʳ c) (𝐂.wkʳ kk))

blockB-del : ∀ a c {kk} (Q : Struct c) →
  ((Q 𝐂.⋯ᵣ weakenᵣ) 𝐂.⋯ᵣ 𝐂.wkˡ (suc a) 𝐂.⋯ᵣ 𝐂.wkʳ kk) 𝐂.⋯ del a c
    ≡ Q 𝐂.⋯ᵣ 𝐂.wkˡ a 𝐂.⋯ᵣ 𝐂.wkʳ kk
blockB-del a c {kk} Q =
    cong (𝐂._⋯ del a c) (⋯ᵣ∘ (Q 𝐂.⋯ᵣ weakenᵣ) _ _ ■ ⋯ᵣ∘ Q _ _)
  ■ ⋯ᵣ⋯ₛ Q _ (del a c)
  ■ ⋯ₛ≗ᵣ Q (del-B a c)
  ■ sym (⋯ᵣ∘ Q (𝐂.wkˡ a) (𝐂.wkʳ kk))

tail-del : ∀ a c {kk} (γ : Struct kk) →
  (γ 𝐂.⋯ᵣ 𝐂.weaken* (suc a + suc c)) 𝐂.⋯ del a c ≡ γ 𝐂.⋯ᵣ 𝐂.weaken* (a + c)
tail-del a c {kk} γ =
    cong (𝐂._⋯ del a c) (⋯ᵣ-cong γ (𝐂.weaken*~wkˡ (suc a + suc c)))
  ■ ⋯ᵣ⋯ₛ γ _ (del a c)
  ■ ⋯ₛ≗ᵣ γ (del-C a c)
  ■ sym (⋯ᵣ-cong γ (𝐂.weaken*~wkˡ (a + c)))

------------------------------------------------------------------------
-- THE PAYOFF: erasing the two communicated handles turns the redex's
-- `TP-Res` structure into the reduct's.
------------------------------------------------------------------------


Fr : (B₁ B₂ : BindGroup) → ∀ {kk} (γ : Struct kk) → Struct (sum B₁ + sum B₂ + kk)
Fr B₁ B₂ {kk} γ =
    ((structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ kk)
  ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B₁) 𝐂.⋯ᵣ 𝐂.wkʳ kk))
  ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B₁ + sum B₂))

module _ (b₁ : ℕ) (B₁ : BindGroup) (b₂ : ℕ) (B₂ : BindGroup)
         {kk : ℕ} (γ : Struct kk) where
  private
    aa cc : ℕ
    aa = b₁ + sum B₁
    cc = b₂ + sum B₂

    P₁ P₂ : Struct aa
    P₁ = structNSeq b₁ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₁)
    P₂ = structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ b₁

    R₁ R₂ : Struct cc
    R₁ = structNSeq b₂ 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂)
    R₂ = structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ b₂

  Fr-del-≡ :
    Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ 𝐂.⋯ del aa cc
      ≡ ((([] ; (P₁ 𝐂.⋯ᵣ 𝐂.wkʳ cc 𝐂.⋯ᵣ 𝐂.wkʳ kk)) ∥ (P₂ 𝐂.⋯ᵣ 𝐂.wkʳ cc 𝐂.⋯ᵣ 𝐂.wkʳ kk))
      ∥ (([] ; (R₁ 𝐂.⋯ᵣ 𝐂.wkˡ aa 𝐂.⋯ᵣ 𝐂.wkʳ kk)) ∥ (R₂ 𝐂.⋯ᵣ 𝐂.wkˡ aa 𝐂.⋯ᵣ 𝐂.wkʳ kk)))
      ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (aa + cc))
  Fr-del-≡ =
    cong₂ _∥_
      (cong₂ _∥_
        (cong (λ z → (z 𝐂.⋯ᵣ 𝐂.wkʳ (suc cc) 𝐂.⋯ᵣ 𝐂.wkʳ kk) 𝐂.⋯ del aa cc)
              (structBinder-suc b₁ B₁)
         ■ cong₂ _∥_ (cong₂ _;_ (del-x aa cc) (blockA-del aa cc P₁))
                     (blockA-del aa cc P₂))
        (cong (λ z → (z 𝐂.⋯ᵣ 𝐂.wkˡ (suc aa) 𝐂.⋯ᵣ 𝐂.wkʳ kk) 𝐂.⋯ del aa cc)
              (structBinder-suc b₂ B₂)
         ■ cong₂ _∥_ (cong₂ _;_ (del-y aa cc) (blockB-del aa cc R₁))
                     (blockB-del aa cc R₂)))
      (tail-del aa cc γ)

  Fr-del : ∀ {Δ′ : Ctx (aa + cc + kk)} →
    Δ′ ∶ Fr (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) γ 𝐂.⋯ del aa cc ≈ Fr (b₁ ∷ B₁) (b₂ ∷ B₂) γ
  Fr-del = ≈-trans (≈-reflexive Fr-del-≡)
    (∥-cong (∥-cong (∥-cong ;-unit₁ ≈-refl) (∥-cong ;-unit₁ ≈-refl)) ≈-refl)

------------------------------------------------------------------------
-- Cancellation stated for the substitution `_ ∘ wkₚ a c` that the typed
-- renaming `⊢wkₚ` carries, and lifted to context patterns.
------------------------------------------------------------------------

⋯-cancel : ∀ a c {kk} (γ : Struct (a + c + kk)) {σ : 𝔽 (a + c + kk) → Struct (suc a + suc c + kk)} →
  (∀ x → σ x ≡ ` (wkₚ a c x)) → (γ 𝐂.⋯ σ) 𝐂.⋯ del a c ≡ γ
⋯-cancel a c γ eq = cong (𝐂._⋯ del a c) (⋯ₛ≗ᵣ γ eq) ■ ⋯-wkₚ-del a c γ

⋯𝓅-cancel : ∀ a c {kk} (𝒫 : CxPat (a + c + kk)) {σ : 𝔽 (a + c + kk) → Struct (suc a + suc c + kk)} →
  (∀ x → σ x ≡ ` (wkₚ a c x)) → (𝒫 ⋯𝓅 σ) ⋯𝓅 del a c ≡ 𝒫
⋯𝓅-cancel a c [] eq = refl
⋯𝓅-cancel a c ((d , γ) ∷ 𝒫) eq =
  cong₂ _∷_ (cong (d ,_) (⋯-cancel a c γ eq)) (⋯𝓅-cancel a c 𝒫 eq)
