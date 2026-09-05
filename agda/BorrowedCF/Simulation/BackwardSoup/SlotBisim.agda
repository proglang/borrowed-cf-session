-- | Slot-renumbering is a strong bisimulation for the soup dynamics.
module BorrowedCF.Simulation.BackwardSoup.SlotBisim where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric
  using (SymClosure; fwd; bwd)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.ExpressionsSoup as Expr
import BorrowedCF.Reduction.Processes.UntypedSoup as RUS
import BorrowedCF.Terms.BaseSoup as Term
import BorrowedCF.Types as Types
import BorrowedCF.Simulation.BackwardSoup.SlotInsert as SlotInsert
open import BorrowedCF.Simulation.ForwardSoup.Expressions as FExpr
  using (SubEq; sub-cong)

open import BorrowedCF.Simulation.BackwardSoup.Statement
  using ( Slot-Bisim
        ; _≈¹_; _≈ˢ_; swap
        ; swapSlot; swapPhi; swapFlags; swapAt
        ; swapPhi-hit; swapPhi-miss
        ; swapSlot-involutive
        ; ≈¹-sym; ≈¹⇒≈ˢ; ≈ˢ-refl; ≈ˢ-sym; ≈ˢ-trans)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using (endpoint-channel-injective; liftRen-injective)
open import BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport
  using (endpoint-side-injective)
open import BorrowedCF.Simulation.ForwardSoup.Local.New
  using (insertEndpoint-endpoint)

open Nat.Variables
open Fin.Patterns

private
  variable
    A : Set
    p q : ℕ

  cong₃ :
    {A B C D : Set} (f : A → B → C → D)
    {a a′ : A} {b b′ : B} {c c′ : C} →
    a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

pattern 𝓒[_×_×_] e₁ x e₂ = (e₁ Term.⊗ (Term.` x)) Term.⊗ e₂

------------------------------------------------------------------------
-- Basic action of a slot swap on soup expressions.

swapPhi-Value :
  (x : 𝔽 n) (k : ℕ) {e : Term.Tm n} →
  Expr.Value e → Expr.Value (swapPhi x k e)
swapPhi-Value x k Expr.V-` = Expr.V-`
swapPhi-Value x k (Expr.V-phi {r = y , l}) with x FinP.≟ y
... | no _ = Expr.V-phi
... | yes refl = Expr.V-phi
swapPhi-Value x k Expr.V-K = Expr.V-K
swapPhi-Value x k Expr.V-λ = Expr.V-λ
swapPhi-Value x k (Expr.V-⊗ V₁ V₂) =
  Expr.V-⊗ (swapPhi-Value x k V₁) (swapPhi-Value x k V₂)
swapPhi-Value x k (Expr.V-⊕ V) =
  Expr.V-⊕ (swapPhi-Value x k V)

swapPhi-frame : (x : 𝔽 n) → ℕ → Expr.Frame n → Expr.Frame n
swapPhi-frame x k (Expr.app₁ e d V?) =
  Expr.app₁ (swapPhi x k e) d λ d≡L → swapPhi-Value x k (V? d≡L)
swapPhi-frame x k (Expr.app₂ e d V?) =
  Expr.app₂ (swapPhi x k e) d λ d≡→ → swapPhi-Value x k (V? d≡→)
swapPhi-frame x k (Expr.□⊗ e) = Expr.□⊗ (swapPhi x k e)
swapPhi-frame x k (V Expr.⊗□) = swapPhi-Value x k V Expr.⊗□
swapPhi-frame x k (Expr.□; e) = Expr.□; (swapPhi x k e)
swapPhi-frame x k (Expr.`let-`in e) = Expr.`let-`in (swapPhi (suc x) k e)
swapPhi-frame x k (Expr.`let⊗-`in e) =
  Expr.`let⊗-`in (swapPhi (suc (suc x)) k e)
swapPhi-frame x k (Expr.`inj□ i) = Expr.`inj□ i
swapPhi-frame x k (Expr.`case□`of⟨ e₁ ; e₂ ⟩) =
  Expr.`case□`of⟨ swapPhi (suc x) k e₁ ; swapPhi (suc x) k e₂ ⟩

swapPhi-frames : (x : 𝔽 n) → ℕ → Expr.Frame* n → Expr.Frame* n
swapPhi-frames x k [] = []
swapPhi-frames x k (F ∷ Fs) = swapPhi-frame x k F ∷ swapPhi-frames x k Fs

swapPhi-plug :
  (x : 𝔽 n) (k : ℕ) (F : Expr.Frame n) (t : Term.Tm n) →
  swapPhi x k (F Expr.[ t ]) ≡ swapPhi-frame x k F Expr.[ swapPhi x k t ]
swapPhi-plug x k (Expr.app₁ e d V?) t = refl
swapPhi-plug x k (Expr.app₂ e d V?) t = refl
swapPhi-plug x k (Expr.□⊗ e) t = refl
swapPhi-plug x k (V Expr.⊗□) t = refl
swapPhi-plug x k (Expr.□; e) t = refl
swapPhi-plug x k (Expr.`let-`in e) t = refl
swapPhi-plug x k (Expr.`let⊗-`in e) t = refl
swapPhi-plug x k (Expr.`inj□ i) t = refl
swapPhi-plug x k (Expr.`case□`of⟨ e₁ ; e₂ ⟩) t = refl

swapPhi-plug* :
  (x : 𝔽 n) (k : ℕ) (F : Expr.Frame* n) (t : Term.Tm n) →
  swapPhi x k (F Expr.[ t ]*) ≡
  swapPhi-frames x k F Expr.[ swapPhi x k t ]*
swapPhi-plug* x k [] t = refl
swapPhi-plug* x k (F ∷ Fs) t =
  swapPhi-plug x k F (Fs Expr.[ t ]*) ■
  cong (swapPhi-frame x k F Expr.[_]) (swapPhi-plug* x k Fs t)

------------------------------------------------------------------------
-- Interaction with renaming and expression reduction.

swapPhi-ren :
  {ρ : 𝔽 p → 𝔽 q} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  (x : 𝔽 p) (k : ℕ) (t : Term.Tm p) →
  swapPhi (ρ x) k (t Term.⋯ᵣ ρ) ≡
  swapPhi x k t Term.⋯ᵣ ρ
swapPhi-ren inj x k (Term.` y) = refl
swapPhi-ren {ρ = ρ} inj x k (Term.`phi (y , l))
  with x FinP.≟ y | ρ x FinP.≟ ρ y
... | no apart | no _ = refl
... | no apart | yes same = ⊥-elim (apart (inj same))
... | yes refl | no apart = ⊥-elim (apart refl)
... | yes refl | yes refl = refl
swapPhi-ren inj x k (Term.K c) = refl
swapPhi-ren {ρ = ρ} inj x k (Term.ƛ t) =
  cong Term.ƛ
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) k t)
swapPhi-ren {ρ = ρ} inj x k (Term.μ t) =
  cong Term.μ
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) k t)
swapPhi-ren inj x k (t₁ Term.·⟨ d ⟩ t₂) =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-ren inj x k t₁) (swapPhi-ren inj x k t₂)
swapPhi-ren inj x k (t₁ Term.; t₂) =
  cong₂ Term._;_ (swapPhi-ren inj x k t₁) (swapPhi-ren inj x k t₂)
swapPhi-ren inj x k (t₁ Term.⊗ t₂) =
  cong₂ Term._⊗_ (swapPhi-ren inj x k t₁) (swapPhi-ren inj x k t₂)
swapPhi-ren {ρ = ρ} inj x k (Term.`let t₁ `in t₂) =
  cong₂ Term.`let_`in_
    (swapPhi-ren inj x k t₁)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) k t₂)
swapPhi-ren {ρ = ρ} inj x k (Term.`let⊗ t₁ `in t₂) =
  cong₂ Term.`let⊗_`in_
    (swapPhi-ren inj x k t₁)
    (swapPhi-ren {ρ = Term.liftRen (Term.liftRen ρ)}
      (liftRen-injective (liftRen-injective inj)) (suc (suc x)) k t₂)
swapPhi-ren inj x k (Term.`inj i t) =
  cong (Term.`inj i) (swapPhi-ren inj x k t)
swapPhi-ren {ρ = ρ} inj x k (Term.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₃ Term.`case_`of⟨_;_⟩
    (swapPhi-ren inj x k t)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) k t₁)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) k t₂)

swapPhi-wk :
  (x : 𝔽 n) (k : ℕ) (t : Term.Tm n) →
  swapPhi (suc x) k (Term.wk t) ≡ Term.wk (swapPhi x k t)
swapPhi-wk = swapPhi-ren {ρ = Fin.suc} Fin.suc-injective

slotSub : {n : ℕ} → (x : 𝔽 n) → ℕ → Term.Sub n n
slotSub {n = n} x k = Term.sub vars refs
  where
  vars : 𝔽 n → Term.Tm n
  vars y = Term.` y

  refs : Term.PhiRef n → Term.Tm n
  refs (y , l) with x FinP.≟ y
  ... | no _ = Term.`phi (y , l)
  ... | yes refl = Term.`phi (x , swapSlot k l)

slotSub-liftEq :
  (x : 𝔽 n) (k : ℕ) →
  SubEq (Term.liftSub (slotSub x k)) (slotSub (suc x) k)
slotSub-liftEq x k = vars , refs
  where
  vars : ∀ y →
    Term.varImage (Term.liftSub (slotSub x k)) y ≡
    Term.varImage (slotSub (suc x) k) y
  vars zero = refl
  vars (suc y) = refl

  refs : ∀ r →
    Term.phiImage (Term.liftSub (slotSub x k)) r ≡
    Term.phiImage (slotSub (suc x) k) r
  refs (zero , l) with suc x FinP.≟ zero
  ... | no _ = refl
  ... | yes ()
  refs (suc y , l) with x FinP.≟ y | suc x FinP.≟ suc y
  ... | no _ | no _ = refl
  ... | no apart | yes same = ⊥-elim (apart (Fin.suc-injective same))
  ... | yes refl | no apart = ⊥-elim (apart refl)
  ... | yes refl | yes refl = refl

SubEq-trans :
  {σ τ υ : Term.Sub n n′} → SubEq σ τ → SubEq τ υ → SubEq σ υ
SubEq-trans (vars₁ , refs₁) (vars₂ , refs₂) =
  (λ x → vars₁ x ■ vars₂ x) , (λ r → refs₁ r ■ refs₂ r)

slotSub-liftEq₂ :
  (x : 𝔽 n) (k : ℕ) →
  SubEq (Term.liftSub (Term.liftSub (slotSub x k)))
        (slotSub (suc (suc x)) k)
slotSub-liftEq₂ x k =
  SubEq-trans (FExpr.liftSubEq (slotSub-liftEq x k))
              (slotSub-liftEq (suc x) k)

swapPhi-as-sub :
  (x : 𝔽 n) (k : ℕ) (t : Term.Tm n) →
  swapPhi x k t ≡ t Term.⋯ₛ slotSub x k
swapPhi-as-sub x k (Term.` y) = refl
swapPhi-as-sub x k (Term.`phi (y , l)) with x FinP.≟ y
... | no _ = refl
... | yes refl = refl
swapPhi-as-sub x k (Term.K c) = refl
swapPhi-as-sub x k (Term.ƛ t) =
  cong Term.ƛ
    (swapPhi-as-sub (suc x) k t ■
     sym (sub-cong t (slotSub-liftEq x k)))
swapPhi-as-sub x k (Term.μ t) =
  cong Term.μ
    (swapPhi-as-sub (suc x) k t ■
     sym (sub-cong t (slotSub-liftEq x k)))
swapPhi-as-sub x k (t₁ Term.·⟨ d ⟩ t₂) =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-as-sub x k t₁) (swapPhi-as-sub x k t₂)
swapPhi-as-sub x k (t₁ Term.; t₂) =
  cong₂ Term._;_ (swapPhi-as-sub x k t₁) (swapPhi-as-sub x k t₂)
swapPhi-as-sub x k (t₁ Term.⊗ t₂) =
  cong₂ Term._⊗_ (swapPhi-as-sub x k t₁) (swapPhi-as-sub x k t₂)
swapPhi-as-sub x k (Term.`let t₁ `in t₂) =
  cong₂ Term.`let_`in_
    (swapPhi-as-sub x k t₁)
    (swapPhi-as-sub (suc x) k t₂ ■
     sym (sub-cong t₂ (slotSub-liftEq x k)))
swapPhi-as-sub x k (Term.`let⊗ t₁ `in t₂) =
  cong₂ Term.`let⊗_`in_
    (swapPhi-as-sub x k t₁)
    (swapPhi-as-sub (suc (suc x)) k t₂ ■
     sym (sub-cong t₂ (slotSub-liftEq₂ x k)))
swapPhi-as-sub x k (Term.`inj i t) =
  cong (Term.`inj i) (swapPhi-as-sub x k t)
swapPhi-as-sub x k (Term.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₃ Term.`case_`of⟨_;_⟩
    (swapPhi-as-sub x k t)
    (swapPhi-as-sub (suc x) k t₁ ■
     sym (sub-cong t₁ (slotSub-liftEq x k)))
    (swapPhi-as-sub (suc x) k t₂ ■
     sym (sub-cong t₂ (slotSub-liftEq x k)))

compSub : {p q n : ℕ} → Term.Sub p q → Term.Sub q n → Term.Sub p n
compSub {p = p} {n = n} σ τ = Term.sub vars refs
  where
  vars : 𝔽 p → Term.Tm n
  vars y = Term.varImage σ y Term.⋯ₛ τ

  refs : Term.PhiRef p → Term.Tm n
  refs r = Term.phiImage σ r Term.⋯ₛ τ

compSub-liftEq :
  (σ : Term.Sub p q) (τ : Term.Sub q n) →
  SubEq (compSub (Term.liftSub σ) (Term.liftSub τ))
        (Term.liftSub (compSub σ τ))
compSub-liftEq σ τ = vars , refs
  where
  vars : ∀ y →
    Term.varImage (compSub (Term.liftSub σ) (Term.liftSub τ)) y ≡
    Term.varImage (Term.liftSub (compSub σ τ)) y
  vars zero = refl
  vars (suc y) = FExpr.wk-⋯ₛ (Term.varImage σ y) τ

  refs : ∀ r →
    Term.phiImage (compSub (Term.liftSub σ) (Term.liftSub τ)) r ≡
    Term.phiImage (Term.liftSub (compSub σ τ)) r
  refs (zero , l) = refl
  refs (suc y , l) = FExpr.wk-⋯ₛ (Term.phiImage σ (y , l)) τ

compSub-liftEq₂ :
  (σ : Term.Sub p q) (τ : Term.Sub q n) →
  SubEq
    (compSub (Term.liftSub (Term.liftSub σ))
             (Term.liftSub (Term.liftSub τ)))
    (Term.liftSub (Term.liftSub (compSub σ τ)))
compSub-liftEq₂ σ τ =
  SubEq-trans (compSub-liftEq (Term.liftSub σ) (Term.liftSub τ))
    (FExpr.liftSubEq (compSub-liftEq σ τ))

sub-sub :
  (t : Term.Tm p) (σ : Term.Sub p q) (τ : Term.Sub q n) →
  (t Term.⋯ₛ σ) Term.⋯ₛ τ ≡ t Term.⋯ₛ compSub σ τ
sub-sub (Term.` y) σ τ = refl
sub-sub (Term.`phi r) σ τ = refl
sub-sub (Term.K c) σ τ = refl
sub-sub (Term.ƛ t) σ τ =
  cong Term.ƛ
    (sub-sub t (Term.liftSub σ) (Term.liftSub τ) ■
     sub-cong t (compSub-liftEq σ τ))
sub-sub (Term.μ t) σ τ =
  cong Term.μ
    (sub-sub t (Term.liftSub σ) (Term.liftSub τ) ■
     sub-cong t (compSub-liftEq σ τ))
sub-sub (t₁ Term.·⟨ d ⟩ t₂) σ τ =
  cong₂ (Term._·⟨ d ⟩_) (sub-sub t₁ σ τ) (sub-sub t₂ σ τ)
sub-sub (t₁ Term.; t₂) σ τ =
  cong₂ Term._;_ (sub-sub t₁ σ τ) (sub-sub t₂ σ τ)
sub-sub (t₁ Term.⊗ t₂) σ τ =
  cong₂ Term._⊗_ (sub-sub t₁ σ τ) (sub-sub t₂ σ τ)
sub-sub (Term.`let t₁ `in t₂) σ τ =
  cong₂ Term.`let_`in_
    (sub-sub t₁ σ τ)
    (sub-sub t₂ (Term.liftSub σ) (Term.liftSub τ) ■
     sub-cong t₂ (compSub-liftEq σ τ))
sub-sub (Term.`let⊗ t₁ `in t₂) σ τ =
  cong₂ Term.`let⊗_`in_
    (sub-sub t₁ σ τ)
    (sub-sub t₂
      (Term.liftSub (Term.liftSub σ))
      (Term.liftSub (Term.liftSub τ)) ■
     sub-cong t₂ (compSub-liftEq₂ σ τ))
sub-sub (Term.`inj i t) σ τ =
  cong (Term.`inj i) (sub-sub t σ τ)
sub-sub (Term.`case t `of⟨ t₁ ; t₂ ⟩) σ τ =
  cong₃ Term.`case_`of⟨_;_⟩
    (sub-sub t σ τ)
    (sub-sub t₁ (Term.liftSub σ) (Term.liftSub τ) ■
     sub-cong t₁ (compSub-liftEq σ τ))
    (sub-sub t₂ (Term.liftSub σ) (Term.liftSub τ) ■
     sub-cong t₂ (compSub-liftEq σ τ))

singleSub-slotSubEq :
  (x : 𝔽 n) (k : ℕ) (v : Term.Tm n) →
  SubEq (compSub (Expr.singleSub v) (slotSub x k))
        (compSub (slotSub (suc x) k) (Expr.singleSub (swapPhi x k v)))
singleSub-slotSubEq x k v = vars , refs
  where
  vars : ∀ y →
    Term.varImage (compSub (Expr.singleSub v) (slotSub x k)) y ≡
    Term.varImage
      (compSub (slotSub (suc x) k)
        (Expr.singleSub (swapPhi x k v))) y
  vars zero = sym (swapPhi-as-sub x k v)
  vars (suc y) = refl

  refs : ∀ r →
    Term.phiImage (compSub (Expr.singleSub v) (slotSub x k)) r ≡
    Term.phiImage
      (compSub (slotSub (suc x) k)
        (Expr.singleSub (swapPhi x k v))) r
  refs (zero , l) with suc x FinP.≟ zero
  ... | no _ = refl
  ... | yes ()
  refs (suc y , l) with x FinP.≟ y | suc x FinP.≟ suc y
  ... | no _ | no _ = refl
  ... | no apart | yes same = ⊥-elim (apart (Fin.suc-injective same))
  ... | yes refl | no apart = ⊥-elim (apart refl)
  ... | yes refl | yes refl = refl

swapPhi-subst₀ :
  (x : 𝔽 n) (k : ℕ) (v : Term.Tm n) (body : Term.Tm (1 + n)) →
  swapPhi x k (Expr.subst₀ v body) ≡
  Expr.subst₀ (swapPhi x k v) (swapPhi (suc x) k body)
swapPhi-subst₀ x k v body =
  swapPhi-as-sub x k (Expr.subst₀ v body) ■
  sub-sub body (Expr.singleSub v) (slotSub x k) ■
  sub-cong body (singleSub-slotSubEq x k v) ■
  sym (sub-sub body (slotSub (suc x) k)
        (Expr.singleSub (swapPhi x k v))) ■
  sym (cong (λ t → t Term.⋯ₛ Expr.singleSub (swapPhi x k v))
        (swapPhi-as-sub (suc x) k body))

swapPhi-pairSubst₀ :
  (x : 𝔽 n) (k : ℕ) (v₁ v₂ : Term.Tm n)
  (body : Term.Tm (2 + n)) →
  swapPhi x k (Expr.subst₀ v₂ (Expr.subst₀ (Term.wk v₁) body)) ≡
  Expr.subst₀ (swapPhi x k v₂)
    (Expr.subst₀ (Term.wk (swapPhi x k v₁))
      (swapPhi (suc (suc x)) k body))
swapPhi-pairSubst₀ x k v₁ v₂ body =
  swapPhi-subst₀ x k v₂ (Expr.subst₀ (Term.wk v₁) body) ■
  cong (Expr.subst₀ (swapPhi x k v₂))
    (swapPhi-subst₀ (suc x) k (Term.wk v₁) body ■
     cong (λ z → Expr.subst₀ z (swapPhi (suc (suc x)) k body))
       (swapPhi-wk x k v₁))

swapPhi-─→ :
  (x : 𝔽 n) (k : ℕ) {e e′ : Term.Tm n} →
  e Expr.─→ e′ → swapPhi x k e Expr.─→ swapPhi x k e′
swapPhi-─→ x k {Term.ƛ e₁ Term.·⟨ d ⟩ e₂}
  {.(Expr.subst₀ e₂ e₁)} (Expr.E-App V) =
  subst
    (Term.ƛ (swapPhi (suc x) k e₁) Term.·⟨ d ⟩ swapPhi x k e₂ Expr.─→_)
    (sym (swapPhi-subst₀ x k e₂ e₁))
    (Expr.E-App (swapPhi-Value x k V))
swapPhi-─→ x k {_ Term.; _} {._} (Expr.E-Seq V) =
  Expr.E-Seq (swapPhi-Value x k V)
swapPhi-─→ x k {Term.`let e₁ `in e₂}
  {.(Expr.subst₀ e₁ e₂)} (Expr.E-Let V) =
  subst
    (Term.`let swapPhi x k e₁ `in swapPhi (suc x) k e₂ Expr.─→_)
    (sym (swapPhi-subst₀ x k e₁ e₂))
    (Expr.E-Let (swapPhi-Value x k V))
swapPhi-─→ x k {Term.`let⊗ (e₁ Term.⊗ e₂) `in e}
  {.(Expr.subst₀ e₂ (Expr.subst₀ (Term.wk e₁) e))}
  (Expr.E-PairElim V₁ V₂) =
  subst
    (Term.`let⊗ (swapPhi x k e₁ Term.⊗ swapPhi x k e₂)
      `in swapPhi (suc (suc x)) k e Expr.─→_)
    (sym (swapPhi-pairSubst₀ x k e₁ e₂ e))
    (Expr.E-PairElim (swapPhi-Value x k V₁) (swapPhi-Value x k V₂))
swapPhi-─→ x k {Term.`case Term.`inj true e `of⟨ e₁ ; e₂ ⟩}
  {.(Expr.subst₀ e e₁)} (Expr.E-SumElim V) =
  subst
    (Term.`case Term.`inj true (swapPhi x k e)
      `of⟨ swapPhi (suc x) k e₁ ; swapPhi (suc x) k e₂ ⟩ Expr.─→_)
    (sym (swapPhi-subst₀ x k e e₁))
    (Expr.E-SumElim (swapPhi-Value x k V))
swapPhi-─→ x k {Term.`case Term.`inj false e `of⟨ e₁ ; e₂ ⟩}
  {.(Expr.subst₀ e e₂)} (Expr.E-SumElim V) =
  subst
    (Term.`case Term.`inj false (swapPhi x k e)
      `of⟨ swapPhi (suc x) k e₁ ; swapPhi (suc x) k e₂ ⟩ Expr.─→_)
    (sym (swapPhi-subst₀ x k e e₂))
    (Expr.E-SumElim (swapPhi-Value x k V))
swapPhi-─→ x k {Term.μ e} {.(Expr.subst₀ (Term.μ e) e)}
  Expr.E-Unfold =
  subst
    (swapPhi x k (Term.μ e) Expr.─→_)
    (sym (swapPhi-subst₀ x k (Term.μ e) e))
    Expr.E-Unfold

swapPhi-⋯→ :
  (x : 𝔽 n) (k : ℕ) {e e′ : Term.Tm n} →
  e Expr.⋯→ e′ → swapPhi x k e Expr.⋯→ swapPhi x k e′
swapPhi-⋯→ x k (Expr.E-□ red) = Expr.E-□ (swapPhi-─→ x k red)
swapPhi-⋯→ x k (Expr.E-Ctx F red) =
  subst₂ Expr._⋯→_
    (sym (swapPhi-plug x k F _))
    (sym (swapPhi-plug x k F _))
    (Expr.E-Ctx (swapPhi-frame x k F) (swapPhi-⋯→ x k red))

------------------------------------------------------------------------
-- Vector transport for the process rules.

map-replaceAt :
  (f : A → A) (xs : Vec A n) (i : 𝔽 n) (x : A) →
  V.map f (RUS.replaceAt xs i x) ≡
  RUS.replaceAt (V.map f xs) i (f x)
map-replaceAt f xs i x = V.map-updateAt xs i refl

map-replaceTwo :
  (f : A → A) (xs : Vec A n) (i j : 𝔽 n) (x y : A) →
  V.map f (RUS.replaceTwo xs i x j y) ≡
  RUS.replaceTwo (V.map f xs) i (f x) j (f y)
map-replaceTwo f xs i j x y =
  V.map-updateAt (RUS.replaceAt xs i x) j refl ■
  cong (λ ys → RUS.replaceAt ys j (f y))
    (map-replaceAt f xs i x)

map-insertAfter-replace :
  (f : A → A) (xs : Vec A n) (i : 𝔽 n) (x y : A) →
  V.map f (RUS.insertAfter (RUS.replaceAt xs i x) i y) ≡
  RUS.insertAfter (RUS.replaceAt (V.map f xs) i (f x)) i (f y)
map-insertAfter-replace f xs i x y =
  V.map-insertAt f y (RUS.replaceAt xs i x) (suc i) ■
  cong (λ ys → RUS.insertAfter ys i (f y)) (map-replaceAt f xs i x)

map-replaceAt-map :
  (f g h : A → A) (xs : Vec A n) (i : 𝔽 n) (x : A) →
  (∀ y → f (g y) ≡ h (f y)) →
  f x ≡ x →
  V.map f (RUS.replaceAt (V.map g xs) i x) ≡
  RUS.replaceAt (V.map h (V.map f xs)) i x
map-replaceAt-map f g h xs i x commute fixed =
  V.map-updateAt (V.map g xs) i fixed ■
  cong (λ ys → RUS.replaceAt ys i x)
    (sym (V.map-∘ f g xs) ■
     V.map-cong commute xs ■
     V.map-∘ h f xs)

map-replaceAt-map₂ :
  {A B : Set}
  (f : B → B) (g h : A → B) (xs : Vec A n) (i : 𝔽 n)
  (x y : B) →
  (∀ z → f (g z) ≡ h z) →
  f x ≡ y →
  V.map f (RUS.replaceAt (V.map g xs) i x) ≡
  RUS.replaceAt (V.map h xs) i y
map-replaceAt-map₂ f g h xs i x y commute fixed =
  V.map-updateAt (V.map g xs) i fixed
  ■ cong (λ ys → RUS.replaceAt ys i y)
      (sym (V.map-∘ f g xs) ■ V.map-cong commute xs)

updateAt-insertAt-punchIn :
  (xs : Vec A n) (i : 𝔽 (suc n)) (j : 𝔽 n)
  (f : A → A) (x : A) →
  V.updateAt (V.insertAt xs i x) (Fin.punchIn i j) f ≡
  V.insertAt (V.updateAt xs j f) i x
updateAt-insertAt-punchIn xs zero j f x = refl
updateAt-insertAt-punchIn (y ∷ xs) (suc i) zero f x = refl
updateAt-insertAt-punchIn (y ∷ xs) (suc i) (suc j) f x =
  cong (y ∷_) (updateAt-insertAt-punchIn xs i j f x)

------------------------------------------------------------------------
-- Endpoint and channel facts.

endpoint-apart-channel :
  {i i′ : 𝔽 n} {side side′ : 𝔽 2} →
  i ≢ i′ → Soup.endpoint i side ≢ Soup.endpoint i′ side′
endpoint-apart-channel apart equal = apart (endpoint-channel-injective equal)

endpoint-apart-side :
  (i : 𝔽 n) {side side′ : 𝔽 2} →
  side ≢ side′ → Soup.endpoint i side ≢ Soup.endpoint i side′
endpoint-apart-side i apart equal = apart (endpoint-side-injective i _ _ equal)

endpoint-remQuot :
  {n : ℕ} (x : 𝔽 (2 *ℕ n)) →
  let split = Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) x)
  in Soup.endpoint (proj₁ split) (proj₂ split) ≡ x
endpoint-remQuot {n = n} x
  with Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) x)
... | c , side =
  cong (Fin.cast (Nat.*-comm n 2))
    (Fin.combine-remQuot {n = n} 2 (Fin.cast (Nat.*-comm 2 n) x))
  ■ Fin.cast-involutive (Nat.*-comm n 2) (Nat.*-comm 2 n) x

endpoint-remQuot-at :
  {n : ℕ} (x : 𝔽 (2 *ℕ n)) {c : 𝔽 n} {side : 𝔽 2} →
  Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) x) ≡ (c , side) →
  Soup.endpoint c side ≡ x
endpoint-remQuot-at {n = n} x split =
  cong (Fin.cast (Nat.*-comm n 2))
    (cong (uncurry Fin.combine) (sym split)
     ■ Fin.combine-remQuot {n = n} 2 (Fin.cast (Nat.*-comm 2 n) x))
  ■ Fin.cast-involutive (Nat.*-comm n 2) (Nat.*-comm 2 n) x

insertEndpoint-injective :
  {n : ℕ} (target : 𝔽 (suc n)) →
  ∀ {x y : 𝔽 (2 *ℕ n)} →
  RUS.insertEndpoint target x ≡ RUS.insertEndpoint target y →
  x ≡ y
insertEndpoint-injective {n = n} target {x = x} {y = y} equal
  with Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) x) in splitX
     | Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) y) in splitY
... | cx , sx | cy , sy =
  sym (endpoint-remQuot-at x splitX)
  ■ cong₂ Soup.endpoint chanEq sideEq
  ■ endpoint-remQuot-at y splitY
  where
  endpointEq :
    Soup.endpoint (Fin.punchIn target cx) sx ≡
    Soup.endpoint (Fin.punchIn target cy) sy
  endpointEq =
    sym
      (cong
        (λ split → Soup.endpoint (Fin.punchIn target (proj₁ split)) (proj₂ split))
        splitX)
    ■ equal
    ■ cong
        (λ split → Soup.endpoint (Fin.punchIn target (proj₁ split)) (proj₂ split))
        splitY

  chanEq : cx ≡ cy
  chanEq =
    Fin.punchIn-injective target cx cy
      (endpoint-channel-injective endpointEq)

  sideEq : sx ≡ sy
  sideEq =
    endpoint-side-injective (Fin.punchIn target cx) sx sy
      (endpointEq
       ■ cong (λ c → Soup.endpoint (Fin.punchIn target c) sy)
           (sym chanEq))

swapPhi-insertThreadEndpoints :
  {n : ℕ} (target : 𝔽 (suc n)) (r : 𝔽 n) (side : 𝔽 2)
  (h : ℕ) (t : Soup.Thread n) →
  swapPhi (Soup.endpoint (Fin.punchIn target r) side) h
    (RUS.insertThreadEndpoints target t) ≡
  RUS.insertThreadEndpoints target
    (swapPhi (Soup.endpoint r side) h t)
swapPhi-insertThreadEndpoints target r side h t =
  cong (λ y → swapPhi y h (RUS.insertThreadEndpoints target t))
    (sym (insertEndpoint-endpoint target r side))
  ■ swapPhi-ren (insertEndpoint-injective target) (Soup.endpoint r side) h t

swapPhi-frame-rename-plug :
  {p q : ℕ} {ρ : 𝔽 p → 𝔽 q} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  (x : 𝔽 p) (h : ℕ) (F : Expr.Frame p) (t : Term.Tm q) →
  swapPhi (ρ x) h (Expr.frame-rename F ρ Expr.[ t ]) ≡
  Expr.frame-rename (swapPhi-frame x h F) ρ Expr.[
    swapPhi (ρ x) h t ]
swapPhi-frame-rename-plug inj x h (Expr.app₁ e d V?) t =
  cong₂ (Term._·⟨ d ⟩_)
    refl (swapPhi-ren inj x h e)
swapPhi-frame-rename-plug inj x h (Expr.app₂ e d V?) t =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-ren inj x h e) refl
swapPhi-frame-rename-plug inj x h (Expr.□⊗ e) t =
  cong₂ Term._⊗_ refl (swapPhi-ren inj x h e)
swapPhi-frame-rename-plug inj x h (V Expr.⊗□) t =
  cong₂ Term._⊗_ (swapPhi-ren inj x h (Expr.vTm V)) refl
swapPhi-frame-rename-plug inj x h (Expr.□; e) t =
  cong₂ Term._;_ refl (swapPhi-ren inj x h e)
swapPhi-frame-rename-plug {ρ = ρ} inj x h (Expr.`let-`in e) t =
  cong (Term.`let swapPhi (ρ x) h t `in_)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj) (suc x) h e)
swapPhi-frame-rename-plug {ρ = ρ} inj x h (Expr.`let⊗-`in e) t =
  cong (Term.`let⊗ swapPhi (ρ x) h t `in_)
    (swapPhi-ren {ρ = Term.liftRen (Term.liftRen ρ)}
      (liftRen-injective (liftRen-injective inj)) (suc (suc x)) h e)
swapPhi-frame-rename-plug inj x h (Expr.`inj□ side) t = refl
swapPhi-frame-rename-plug {ρ = ρ} inj x h
  (Expr.`case□`of⟨ e₁ ; e₂ ⟩) t =
  cong₂ (λ a b →
      Term.`case swapPhi (ρ x) h t `of⟨ a ; b ⟩)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj)
      (suc x) h e₁)
    (swapPhi-ren {ρ = Term.liftRen ρ} (liftRen-injective inj)
      (suc x) h e₂)

swapPhi-frames-rename-plug :
  {p q : ℕ} {ρ : 𝔽 p → 𝔽 q} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  (x : 𝔽 p) (h : ℕ) (F : Expr.Frame* p) (t : Term.Tm q) →
  swapPhi (ρ x) h (Expr.frames-rename F ρ Expr.[ t ]*) ≡
  Expr.frames-rename (swapPhi-frames x h F) ρ Expr.[
    swapPhi (ρ x) h t ]*
swapPhi-frames-rename-plug inj x h [] t = refl
swapPhi-frames-rename-plug inj x h (F ∷ Fs) t =
  swapPhi-frame-rename-plug inj x h F (Expr.frames-rename Fs _ Expr.[ t ]*)
  ■ cong (Expr.frame-rename (swapPhi-frame x h F) _ Expr.[_])
      (swapPhi-frames-rename-plug inj x h Fs t)

newPayload :
  {n : ℕ} → 𝔽 (suc n) → Soup.Thread (suc n)
newPayload i =
  let l = Soup.leftEnd i
      r = Soup.rightEnd i
      c₀ = 𝓒[ Term.`phi (l , 0) × l × Term.* ]
      c₁ = 𝓒[ Term.`phi (r , 0) × r × Term.* ]
  in c₀ Term.⊗ c₁

swapPhi-newPayload :
  {n : ℕ} (target : 𝔽 (suc n)) (r : 𝔽 n) (side : 𝔽 2)
  (h : ℕ) →
  swapPhi (Soup.endpoint (Fin.punchIn target r) side) h
    (newPayload target) ≡
  newPayload target
swapPhi-newPayload target r side h =
  cong₂ Term._⊗_
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_
        (swapPhi-miss (endpoint-apart-channel (Fin.punchInᵢ≢i target r))
          h 0)
        refl)
      refl)
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_
        (swapPhi-miss (endpoint-apart-channel (Fin.punchInᵢ≢i target r))
          h 0)
        refl)
      refl)

swapPhi-newResult :
  {n : ℕ} (target : 𝔽 (suc n)) (r : 𝔽 n) (side : 𝔽 2)
  (h : ℕ) (F : Expr.Frame* (2 *ℕ n)) →
  swapPhi (Soup.endpoint (Fin.punchIn target r) side) h
    (RUS.newResult target F) ≡
  RUS.newResult target (swapPhi-frames (Soup.endpoint r side) h F)
swapPhi-newResult target r side h F =
  cong (λ y → swapPhi y h (RUS.newResult target F))
    (sym (insertEndpoint-endpoint target r side))
  ■ swapPhi-frames-rename-plug (insertEndpoint-injective target)
      (Soup.endpoint r side) h F (newPayload target)
  ■ cong
      (λ t →
        Expr.frames-rename (swapPhi-frames (Soup.endpoint r side) h F)
          (RUS.insertEndpoint target) Expr.[ t ]*)
      (cong (λ y → swapPhi y h (newPayload target))
        (insertEndpoint-endpoint target r side)
       ■ swapPhi-newPayload target r side h)

open-preserved-swapFlags :
  (side : 𝔽 2) (k : ℕ) (ch : Soup.Channel) →
  proj₁ (swapFlags side k ch) ≡ proj₁ ch
open-preserved-swapFlags 0F k (o , fs₀ , fs₁) = refl
open-preserved-swapFlags 1F k (o , fs₀ , fs₁) = refl

endpointFlags-swapFlags-miss :
  (side side′ : 𝔽 2) (k : ℕ) (ch : Soup.Channel) →
  side ≢ side′ →
  RUS.endpointFlags (swapFlags side k ch) side′ ≡
  RUS.endpointFlags ch side′
endpointFlags-swapFlags-miss 0F 0F k ch apart = ⊥-elim (apart refl)
endpointFlags-swapFlags-miss 0F 1F k (o , fs₀ , fs₁) apart = refl
endpointFlags-swapFlags-miss 1F 0F k (o , fs₀ , fs₁) apart = refl
endpointFlags-swapFlags-miss 1F 1F k ch apart = ⊥-elim (apart refl)

endpointFlags-setEndpointFlags :
  (side : 𝔽 2) (fs : List Soup.Flag) (ch : Soup.Channel) →
  RUS.endpointFlags (RUS.setEndpointFlags side fs ch) side ≡ fs
endpointFlags-setEndpointFlags 0F fs (o , fs₀ , fs₁) = refl
endpointFlags-setEndpointFlags 1F fs (o , fs₀ , fs₁) = refl

endpointFlags-setEndpointFlags-miss :
  (side side′ : 𝔽 2) (fs : List Soup.Flag) (ch : Soup.Channel) →
  side ≢ side′ →
  RUS.endpointFlags (RUS.setEndpointFlags side fs ch) side′ ≡
  RUS.endpointFlags ch side′
endpointFlags-setEndpointFlags-miss 0F 0F fs ch apart = ⊥-elim (apart refl)
endpointFlags-setEndpointFlags-miss 0F 1F fs (o , fs₀ , fs₁) apart = refl
endpointFlags-setEndpointFlags-miss 1F 0F fs (o , fs₀ , fs₁) apart = refl
endpointFlags-setEndpointFlags-miss 1F 1F fs ch apart = ⊥-elim (apart refl)

setEndpointFlags-swapFlags-miss-commute :
  (swapSide side : 𝔽 2) (h : ℕ) (fs : List Soup.Flag)
  (ch : Soup.Channel) →
  swapSide ≢ side →
  RUS.setEndpointFlags side fs (swapFlags swapSide h ch) ≡
  swapFlags swapSide h (RUS.setEndpointFlags side fs ch)
setEndpointFlags-swapFlags-miss-commute 0F 0F h fs ch apart =
  ⊥-elim (apart refl)
setEndpointFlags-swapFlags-miss-commute 0F 1F h fs (o , fs₀ , fs₁) apart =
  refl
setEndpointFlags-swapFlags-miss-commute 1F 0F h fs (o , fs₀ , fs₁) apart =
  refl
setEndpointFlags-swapFlags-miss-commute 1F 1F h fs ch apart =
  ⊥-elim (apart refl)

setEndpointFlags-swapFlags-hit-replace :
  (side : 𝔽 2) (h : ℕ) (fs fs′ : List Soup.Flag)
  (ch : Soup.Channel) →
  swapAt h fs ≡ fs′ →
  RUS.setEndpointFlags side fs′ (swapFlags side h ch) ≡
  swapFlags side h (RUS.setEndpointFlags side fs ch)
setEndpointFlags-swapFlags-hit-replace 0F h fs fs′ (o , fs₀ , fs₁) swapped =
  cong (λ zs → o , zs , fs₁) (sym swapped)
setEndpointFlags-swapFlags-hit-replace 1F h fs fs′ (o , fs₀ , fs₁) swapped =
  cong (λ zs → o , fs₀ , zs) (sym swapped)

setEndpointFlags-swapFlags-overwrite :
  (side : 𝔽 2) (h : ℕ) (fs : List Soup.Flag) (ch : Soup.Channel) →
  RUS.setEndpointFlags side fs (swapFlags side h ch) ≡
  RUS.setEndpointFlags side fs ch
setEndpointFlags-swapFlags-overwrite 0F h fs (o , fs₀ , fs₁) = refl
setEndpointFlags-swapFlags-overwrite 1F h fs (o , fs₀ , fs₁) = refl

is-open-swap :
  (cs : Vec Soup.Channel n) (r : 𝔽 n) (side : 𝔽 2) (k : ℕ) (i : 𝔽 n) →
  RUS.is-open cs i →
  RUS.is-open (V.updateAt cs r (swapFlags side k)) i
is-open-swap cs r side k i live with r FinP.≟ i
... | yes refl =
  cong proj₁ (V.lookup∘updateAt r cs) ■
  open-preserved-swapFlags side k (lookup cs r) ■
  live
... | no apart =
  cong proj₁ (V.lookup∘updateAt′ i r (apart ∘ sym) cs) ■ live

closed-channel-swap :
  (cs : Vec Soup.Channel n) (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (i : 𝔽 n) →
  suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side) →
  lookup cs i ≡ (false , [] , []) →
  lookup (V.updateAt cs r (swapFlags side h)) i ≡ (false , [] , [])
closed-channel-swap cs r 0F h i lt closed with r FinP.≟ i
... | yes refl = ⊥-elim bad
  where
  bad : ⊥
  bad with subst (λ ch → suc h Nat.< L.length (RUS.endpointFlags ch 0F)) closed lt
  ... | ()
... | no apart = V.lookup∘updateAt′ i r (apart ∘ sym) cs ■ closed
closed-channel-swap cs r 1F h i lt closed with r FinP.≟ i
... | yes refl = ⊥-elim bad
  where
  bad : ⊥
  bad with subst (λ ch → suc h Nat.< L.length (RUS.endpointFlags ch 1F)) closed lt
  ... | ()
... | no apart = V.lookup∘updateAt′ i r (apart ∘ sym) cs ■ closed

empty-open-channel-swap :
  (cs : Vec Soup.Channel n) (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (i : 𝔽 n) →
  suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side) →
  lookup cs i ≡ (true , [] , []) →
  lookup (V.updateAt cs r (swapFlags side h)) i ≡ (true , [] , [])
empty-open-channel-swap cs r 0F h i lt empty with r FinP.≟ i
... | yes refl = ⊥-elim bad
  where
  bad : ⊥
  bad with subst (λ ch → suc h Nat.< L.length (RUS.endpointFlags ch 0F)) empty lt
  ... | ()
... | no apart = V.lookup∘updateAt′ i r (apart ∘ sym) cs ■ empty
empty-open-channel-swap cs r 1F h i lt empty with r FinP.≟ i
... | yes refl = ⊥-elim bad
  where
  bad : ⊥
  bad with subst (λ ch → suc h Nat.< L.length (RUS.endpointFlags ch 1F)) empty lt
  ... | ()
... | no apart = V.lookup∘updateAt′ i r (apart ∘ sym) cs ■ empty

empty-open-slot-impossible :
  (side : 𝔽 2) (h : ℕ) →
  suc h Nat.< L.length (RUS.endpointFlags (true , [] , []) side) →
  ⊥
empty-open-slot-impossible 0F h ()
empty-open-slot-impossible 1F h ()

------------------------------------------------------------------------
-- Selecting the same flag after a swap.

swapAt-select :
  (h : ℕ) (before after : List Soup.Flag) (f : Soup.Flag) →
  suc h Nat.< L.length (before ++ f ∷ after) →
  Σ[ before′ ∈ List Soup.Flag ] Σ[ after′ ∈ List Soup.Flag ]
    (swapAt h (before ++ f ∷ after) ≡ before′ ++ f ∷ after′) ×
    (L.length before′ ≡ swapSlot h (L.length before))
swapAt-select zero [] [] f (Nat.s≤s ())
swapAt-select zero [] (g ∷ after) f lt =
  (g ∷ []) , after , refl , refl
swapAt-select zero (g ∷ []) after f lt =
  [] , (g ∷ after) , refl , refl
swapAt-select zero (g ∷ g′ ∷ before) after f lt =
  (g′ ∷ g ∷ before) , after , refl , refl
swapAt-select (suc h) [] after f lt =
  [] , swapAt h after , refl , refl
swapAt-select (suc h) (g ∷ before) after f (Nat.s≤s lt)
  with swapAt-select h before after f lt
... | before′ , after′ , eq , lenEq =
  (g ∷ before′) , after′ , cong (g ∷_) eq , cong suc lenEq

swapAt-select₂ :
  (h : ℕ) (before after : List Soup.Flag) (old new : Soup.Flag) →
  suc h Nat.< L.length (before ++ old ∷ after) →
  Σ[ before′ ∈ List Soup.Flag ] Σ[ after′ ∈ List Soup.Flag ]
    (swapAt h (before ++ old ∷ after) ≡ before′ ++ old ∷ after′) ×
    (swapAt h (before ++ new ∷ after) ≡ before′ ++ new ∷ after′) ×
    (L.length before′ ≡ swapSlot h (L.length before))
swapAt-select₂ zero [] [] old new (Nat.s≤s ())
swapAt-select₂ zero [] (g ∷ after) old new lt =
  (g ∷ []) , after , refl , refl , refl
swapAt-select₂ zero (g ∷ []) after old new lt =
  [] , (g ∷ after) , refl , refl , refl
swapAt-select₂ zero (g ∷ g′ ∷ before) after old new lt =
  (g′ ∷ g ∷ before) , after , refl , refl , refl
swapAt-select₂ (suc h) [] after old new lt =
  [] , swapAt h after , refl , refl , refl
swapAt-select₂ (suc h) (g ∷ before) after old new (Nat.s≤s lt)
  with swapAt-select₂ h before after old new lt
... | before′ , after′ , oldEq , newEq , lenEq =
  (g ∷ before′) , after′ , cong (g ∷_) oldEq ,
    cong (g ∷_) newEq , cong suc lenEq

replace-flag-length :
  (before after : List Soup.Flag) (old new : Soup.Flag) →
  L.length (before ++ old ∷ after) ≡
  L.length (before ++ new ∷ after)
replace-flag-length [] after old new = refl
replace-flag-length (f ∷ before) after old new =
  cong suc (replace-flag-length before after old new)

data ResidualSwap : Set where
  none : ResidualSwap
  some : ℕ → ResidualSwap

residualSwap : ℕ → ℕ → ResidualSwap
residualSwap zero zero = none
residualSwap zero (suc zero) = none
residualSwap zero (suc (suc p)) = some zero
residualSwap (suc h) zero = some h
residualSwap (suc h) (suc p) with residualSwap h p
... | none = none
... | some q = some (suc q)

applyResidualPhi : 𝔽 n → ResidualSwap → Term.Tm n → Term.Tm n
applyResidualPhi x none t = t
applyResidualPhi x (some h) t = swapPhi x h t

applyResidualSlot : ResidualSwap → ℕ → ℕ
applyResidualSlot none l = l
applyResidualSlot (some h) l = swapSlot h l

applyResidualFlags : ResidualSwap → List Soup.Flag → List Soup.Flag
applyResidualFlags none fs = fs
applyResidualFlags (some h) fs = swapAt h fs

ResidualBound : ResidualSwap → List Soup.Flag → Set
ResidualBound none fs = ⊤
ResidualBound (some h) fs = suc h Nat.< L.length fs

applyResidualChannels :
  (i : 𝔽 n) → 𝔽 2 → ResidualSwap →
  Vec Soup.Channel n → Vec Soup.Channel n
applyResidualChannels i side none cs = cs
applyResidualChannels i side (some h) cs =
  V.updateAt cs i (swapFlags side h)

residual-bound-cong :
  {res : ResidualSwap} {fs gs : List Soup.Flag} →
  fs ≡ gs → ResidualBound res fs → ResidualBound res gs
residual-bound-cong {res = none} equal tt = tt
residual-bound-cong {res = some h} equal bound =
  subst (suc h Nat.<_) (cong L.length equal) bound

residual-config-related :
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (i : 𝔽 n) (side : 𝔽 2) (res : ResidualSwap) →
  ResidualBound res (RUS.endpointFlags (lookup cs i) side) →
  Soup.config cs ts ≈ˢ
  Soup.config (applyResidualChannels i side res cs)
    (V.map (applyResidualPhi (Soup.endpoint i side) res) ts)
residual-config-related cs ts i side none bound =
  subst (λ ys → Soup.config cs ts ≈ˢ Soup.config cs ys)
    (sym (V.map-id ts)) ≈ˢ-refl
residual-config-related cs ts i side (some h) bound =
  ≈¹⇒≈ˢ (swap cs ts i side h bound)

residual-channel-local :
  (side : 𝔽 2) (h : ℕ) (res : ResidualSwap)
  (sourceFlags targetFlags : List Soup.Flag) (ch : Soup.Channel) →
  targetFlags ≡ applyResidualFlags res sourceFlags →
  RUS.setEndpointFlags side targetFlags (swapFlags side h ch) ≡
  (case res of λ where
    none → RUS.setEndpointFlags side sourceFlags ch
    (some q) →
      swapFlags side q (RUS.setEndpointFlags side sourceFlags ch))
residual-channel-local side h none sourceFlags targetFlags ch removed =
  setEndpointFlags-swapFlags-overwrite side h targetFlags ch
  ■ cong (λ fs → RUS.setEndpointFlags side fs ch) removed
residual-channel-local side h (some q) sourceFlags targetFlags ch removed =
  setEndpointFlags-swapFlags-overwrite side h targetFlags ch
  ■ sym (setEndpointFlags-swapFlags-overwrite side q targetFlags ch)
  ■ setEndpointFlags-swapFlags-hit-replace
      side q sourceFlags targetFlags ch (sym removed)

acquire-residual-channels :
  (cs : Vec Soup.Channel n) (i : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (res : ResidualSwap) (sourceFlags targetFlags : List Soup.Flag) →
  targetFlags ≡ applyResidualFlags res sourceFlags →
  applyResidualChannels i side res
    (V.updateAt cs i (RUS.setEndpointFlags side sourceFlags))
  ≡
  V.updateAt (V.updateAt cs i (swapFlags side h)) i
    (RUS.setEndpointFlags side targetFlags)
acquire-residual-channels cs i side h none sourceFlags targetFlags removed =
  sym
    (V.updateAt-updateAt-local i cs
      (residual-channel-local
        side h none sourceFlags targetFlags (lookup cs i) removed))
acquire-residual-channels cs i side h (some q)
  sourceFlags targetFlags removed =
  V.updateAt-updateAt i cs
  ■ sym
      (V.updateAt-updateAt-local i cs
        (residual-channel-local
          side h (some q) sourceFlags targetFlags (lookup cs i) removed))

swapSlot-injective :
  (h : ℕ) {p l : ℕ} →
  swapSlot h p ≡ swapSlot h l → p ≡ l
swapSlot-injective h {p = p} {l = l} eq =
  sym (swapSlot-involutive h p)
  ■ cong (swapSlot h) eq
  ■ swapSlot-involutive h l

shiftSlot-swapSlot :
  (h p l : ℕ) →
  p ≢ l →
  RUS.shiftSlot (swapSlot h p) (swapSlot h l) ≡
  applyResidualSlot (residualSwap h p) (RUS.shiftSlot p l)
shiftSlot-swapSlot zero zero zero apart = ⊥-elim (apart refl)
shiftSlot-swapSlot zero zero (suc zero) apart = refl
shiftSlot-swapSlot zero zero (suc (suc l)) apart = refl
shiftSlot-swapSlot zero (suc zero) zero apart = refl
shiftSlot-swapSlot zero (suc zero) (suc zero) apart = ⊥-elim (apart refl)
shiftSlot-swapSlot zero (suc zero) (suc (suc l)) apart = refl
shiftSlot-swapSlot zero (suc (suc p)) zero apart = refl
shiftSlot-swapSlot zero (suc (suc p)) (suc zero) apart = refl
shiftSlot-swapSlot zero (suc (suc p)) (suc (suc l)) apart
  with p NatP.≟ l
... | yes refl = ⊥-elim (apart refl)
... | no p≢l = refl
shiftSlot-swapSlot (suc h) zero zero apart = ⊥-elim (apart refl)
shiftSlot-swapSlot (suc h) zero (suc l) apart = refl
shiftSlot-swapSlot (suc h) (suc p) zero apart
  with residualSwap h p
... | none = refl
... | some q = refl
shiftSlot-swapSlot (suc h) (suc p) (suc l) apart
  with residualSwap h p | shiftSlot-swapSlot h p l (apart ∘ cong suc)
... | none | ih = cong suc ih
... | some q | ih = cong suc ih

consumePhi-hit-at :
  (x : 𝔽 n) (k : ℕ) →
  RUS.consumePhi x k (Term.`phi (x , k)) ≡ Term.*
consumePhi-hit-at x k with x FinP.≟ x
... | no apart = ⊥-elim (apart refl)
... | yes refl with k NatP.≟ k
...   | no apart = ⊥-elim (apart refl)
...   | yes same rewrite ≡-irrelevant same refl = refl

consumePhi-shift-at :
  (x : 𝔽 n) (k l : ℕ) →
  k ≢ l →
  RUS.consumePhi x k (Term.`phi (x , l)) ≡
  Term.`phi (x , RUS.shiftSlot k l)
consumePhi-shift-at x k l apart with x FinP.≟ x
... | no contra = ⊥-elim (contra refl)
... | yes refl rewrite Dec.dec-no (k NatP.≟ l) apart = refl

applyResidualPhi-hit :
  (x : 𝔽 n) (res : ResidualSwap) (l : ℕ) →
  applyResidualPhi x res (Term.`phi (x , l)) ≡
  Term.`phi (x , applyResidualSlot res l)
applyResidualPhi-hit x none l = refl
applyResidualPhi-hit x (some h) l = swapPhi-hit x h l

applyResidualPhi-miss :
  {x y : 𝔽 n} →
  x ≢ y → (res : ResidualSwap) (l : ℕ) →
  applyResidualPhi x res (Term.`phi (y , l)) ≡ Term.`phi (y , l)
applyResidualPhi-miss apart none l = refl
applyResidualPhi-miss apart (some h) l = swapPhi-miss apart h l

consumePhi-miss :
  {x y : 𝔽 n} →
  x ≢ y → (k l : ℕ) →
  RUS.consumePhi x k (Term.`phi (y , l)) ≡ Term.`phi (y , l)
consumePhi-miss {x = x} {y = y} apart k l with x FinP.≟ y
... | no _ = refl
... | yes same = ⊥-elim (apart same)

consumePhi-hit-at′ :
  (x : 𝔽 n) (k l : ℕ) →
  k ≡ l →
  RUS.consumePhi x k (Term.`phi (x , l)) ≡ Term.*
consumePhi-hit-at′ x k l same with x FinP.≟ x
... | no contra = ⊥-elim (contra refl)
... | yes refl with k NatP.≟ l
...   | no diff = ⊥-elim (diff same)
...   | yes refl = refl

endpoint-middle-contradiction :
  {x y z : 𝔽 n} →
  x ≢ y →
  y ≡ z →
  x ≡ z →
  ⊥
endpoint-middle-contradiction apart refl refl = apart refl

consumePhi-swapPhi :
  (x : 𝔽 n) (h k : ℕ) (t : Term.Tm n) →
  RUS.consumePhi x (swapSlot h k) (swapPhi x h t) ≡
  applyResidualPhi x (residualSwap h k) (RUS.consumePhi x k t)
consumePhi-swapPhi x h k (Term.` y) with residualSwap h k
... | none = refl
... | some q = refl
consumePhi-swapPhi x h k (Term.`phi (y , l))
  with x FinP.≟ y in xEq | residualSwap h k in resEq | k NatP.≟ l in kEq
... | no apart | none | _
  = consumePhi-miss apart (swapSlot h k) l
... | no apart | some q | _
  = consumePhi-miss apart (swapSlot h k) l
  ■ sym (swapPhi-miss apart q l)
... | yes refl | none | yes refl
  rewrite Dec.dec-yes-irr (x FinP.≟ x) ≡-irrelevant refl
        | Dec.dec-yes-irr
            (swapSlot h k NatP.≟ swapSlot h k) NatP.≡-irrelevant refl
        | Dec.dec-yes-irr (k NatP.≟ k) NatP.≡-irrelevant refl = refl
... | yes refl | some q | yes refl
  rewrite Dec.dec-yes-irr (x FinP.≟ x) ≡-irrelevant refl
        | Dec.dec-yes-irr
            (swapSlot h k NatP.≟ swapSlot h k) NatP.≡-irrelevant refl
        | Dec.dec-yes-irr (k NatP.≟ k) NatP.≡-irrelevant refl = refl
... | yes refl | none | no apart
  rewrite Dec.dec-yes-irr (x FinP.≟ x) ≡-irrelevant refl
        | Dec.dec-no
            (swapSlot h k NatP.≟ swapSlot h l)
            (apart ∘ swapSlot-injective h)
        | Dec.dec-no (k NatP.≟ l) apart =
  cong (λ q → Term.`phi (x , q))
    (shiftSlot-swapSlot h k l apart
    ■ cong (λ res → applyResidualSlot res (RUS.shiftSlot k l)) resEq)
... | yes refl | some q | no apart
  rewrite Dec.dec-yes-irr (x FinP.≟ x) ≡-irrelevant refl
        | Dec.dec-no
            (swapSlot h k NatP.≟ swapSlot h l)
            (apart ∘ swapSlot-injective h)
        | Dec.dec-no (k NatP.≟ l) apart =
  cong (λ q → Term.`phi (x , q))
    (shiftSlot-swapSlot h k l apart
    ■ cong (λ res → applyResidualSlot res (RUS.shiftSlot k l)) resEq)
  ■ sym (swapPhi-hit x q (RUS.shiftSlot k l))
consumePhi-swapPhi x h k (Term.K c) with residualSwap h k
... | none = refl
... | some q = refl
consumePhi-swapPhi x h k (Term.ƛ t) with residualSwap h k in resEq
... | none =
  cong Term.ƛ
    (consumePhi-swapPhi (suc x) h k t
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t))
        resEq)
... | some q =
  cong Term.ƛ
    (consumePhi-swapPhi (suc x) h k t
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t))
        resEq)
consumePhi-swapPhi x h k (Term.μ t) with residualSwap h k in resEq
... | none =
  cong Term.μ
    (consumePhi-swapPhi (suc x) h k t
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t))
        resEq)
... | some q =
  cong Term.μ
    (consumePhi-swapPhi (suc x) h k t
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t))
        resEq)
consumePhi-swapPhi x h k (t₁ Term.·⟨ d ⟩ t₂) with residualSwap h k in resEq
... | none =
  cong₂ (Term._·⟨ d ⟩_)
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
... | some q =
  cong₂ (Term._·⟨ d ⟩_)
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
consumePhi-swapPhi x h k (t₁ Term.; t₂) with residualSwap h k in resEq
... | none =
  cong₂ Term._;_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
... | some q =
  cong₂ Term._;_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
consumePhi-swapPhi x h k (t₁ Term.⊗ t₂) with residualSwap h k in resEq
... | none =
  cong₂ Term._⊗_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
... | some q =
  cong₂ Term._⊗_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi x h k t₂
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₂)) resEq)
consumePhi-swapPhi x h k (Term.`let t₁ `in t₂) with residualSwap h k in resEq
... | none =
  cong₂ Term.`let_`in_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi (suc x) h k t₂
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₂))
        resEq)
... | some q =
  cong₂ Term.`let_`in_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi (suc x) h k t₂
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₂))
        resEq)
consumePhi-swapPhi x h k (Term.`let⊗ t₁ `in t₂) with residualSwap h k in resEq
... | none =
  cong₂ Term.`let⊗_`in_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi (suc (suc x)) h k t₂
    ■ cong
        (λ res →
          applyResidualPhi (suc (suc x)) res
            (RUS.consumePhi (suc (suc x)) k t₂))
        resEq)
... | some q =
  cong₂ Term.`let⊗_`in_
    (consumePhi-swapPhi x h k t₁
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t₁)) resEq)
    (consumePhi-swapPhi (suc (suc x)) h k t₂
    ■ cong
        (λ res →
          applyResidualPhi (suc (suc x)) res
            (RUS.consumePhi (suc (suc x)) k t₂))
        resEq)
consumePhi-swapPhi x h k (Term.`inj side t) with residualSwap h k in resEq
... | none =
  cong (Term.`inj side)
    (consumePhi-swapPhi x h k t
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t)) resEq)
... | some q =
  cong (Term.`inj side)
    (consumePhi-swapPhi x h k t
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t)) resEq)
consumePhi-swapPhi x h k (Term.`case t `of⟨ t₁ ; t₂ ⟩)
  with residualSwap h k in resEq
... | none =
  cong₃ Term.`case_`of⟨_;_⟩
    (consumePhi-swapPhi x h k t
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t)) resEq)
    (consumePhi-swapPhi (suc x) h k t₁
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₁))
        resEq)
    (consumePhi-swapPhi (suc x) h k t₂
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₂))
        resEq)
... | some q =
  cong₃ Term.`case_`of⟨_;_⟩
    (consumePhi-swapPhi x h k t
    ■ cong (λ res → applyResidualPhi x res (RUS.consumePhi x k t)) resEq)
    (consumePhi-swapPhi (suc x) h k t₁
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₁))
        resEq)
    (consumePhi-swapPhi (suc x) h k t₂
    ■ cong
        (λ res → applyResidualPhi (suc x) res (RUS.consumePhi (suc x) k t₂))
        resEq)

swapPhi-consumePhi-miss :
  {x y : 𝔽 n} →
  x ≢ y → (h k : ℕ) (t : Term.Tm n) →
  swapPhi x h (RUS.consumePhi y k t) ≡
  RUS.consumePhi y k (swapPhi x h t)
swapPhi-consumePhi-miss apart h k (Term.` z) = refl
swapPhi-consumePhi-miss {x = x} {y = y} apart h k (Term.`phi (z , l))
  with y FinP.≟ z in yzEq | x FinP.≟ z in xzEq
... | no y≢z | no x≢z
  rewrite yzEq | xzEq = refl
... | no y≢z | yes refl
  rewrite yzEq | xzEq = refl
... | yes refl | yes refl = ⊥-elim (apart refl)
... | yes refl | no x≢y with k NatP.≟ l in klEq
...   | yes refl
  rewrite yzEq | klEq = refl
...   | no diff
  rewrite yzEq | xzEq | klEq = refl
swapPhi-consumePhi-miss apart h k (Term.K c) = refl
swapPhi-consumePhi-miss {x = x} {y = y} apart h k (Term.ƛ t) =
  cong Term.ƛ
    (swapPhi-consumePhi-miss (apart ∘ Fin.suc-injective) h k t)
swapPhi-consumePhi-miss {x = x} {y = y} apart h k (Term.μ t) =
  cong Term.μ
    (swapPhi-consumePhi-miss (apart ∘ Fin.suc-injective) h k t)
swapPhi-consumePhi-miss apart h k (t₁ Term.·⟨ d ⟩ t₂) =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-consumePhi-miss apart h k t₁)
    (swapPhi-consumePhi-miss apart h k t₂)
swapPhi-consumePhi-miss apart h k (t₁ Term.; t₂) =
  cong₂ Term._;_
    (swapPhi-consumePhi-miss apart h k t₁)
    (swapPhi-consumePhi-miss apart h k t₂)
swapPhi-consumePhi-miss apart h k (t₁ Term.⊗ t₂) =
  cong₂ Term._⊗_
    (swapPhi-consumePhi-miss apart h k t₁)
    (swapPhi-consumePhi-miss apart h k t₂)
swapPhi-consumePhi-miss {x = x} {y = y} apart h k (Term.`let t₁ `in t₂) =
  cong₂ Term.`let_`in_
    (swapPhi-consumePhi-miss apart h k t₁)
    (swapPhi-consumePhi-miss (apart ∘ Fin.suc-injective) h k t₂)
swapPhi-consumePhi-miss {x = x} {y = y} apart h k (Term.`let⊗ t₁ `in t₂) =
  cong₂ Term.`let⊗_`in_
    (swapPhi-consumePhi-miss apart h k t₁)
    (swapPhi-consumePhi-miss
      (apart ∘ Fin.suc-injective ∘ Fin.suc-injective) h k t₂)
swapPhi-consumePhi-miss apart h k (Term.`inj side t) =
  cong (Term.`inj side) (swapPhi-consumePhi-miss apart h k t)
swapPhi-consumePhi-miss {x = x} {y = y} apart h k
  (Term.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₃ Term.`case_`of⟨_;_⟩
    (swapPhi-consumePhi-miss apart h k t)
    (swapPhi-consumePhi-miss (apart ∘ Fin.suc-injective) h k t₁)
    (swapPhi-consumePhi-miss (apart ∘ Fin.suc-injective) h k t₂)

swapAt-remove-select :
  (h : ℕ) (before after : List Soup.Flag) (f : Soup.Flag) →
  suc h Nat.< L.length (before ++ f ∷ after) →
  Σ[ before′ ∈ List Soup.Flag ] Σ[ after′ ∈ List Soup.Flag ]
    (swapAt h (before ++ f ∷ after) ≡ before′ ++ f ∷ after′) ×
    (before′ ++ after′ ≡
      applyResidualFlags (residualSwap h (L.length before)) (before ++ after)) ×
    (L.length before′ ≡ swapSlot h (L.length before)) ×
    ResidualBound (residualSwap h (L.length before)) (before ++ after)
swapAt-remove-select zero [] [] f (Nat.s≤s ())
swapAt-remove-select zero [] (g ∷ after) f lt =
  (g ∷ []) , after , refl , refl , refl , tt
swapAt-remove-select zero (g ∷ []) after f lt =
  [] , (g ∷ after) , refl , refl , refl , tt
swapAt-remove-select zero (g ∷ g′ ∷ before) after f lt =
  (g′ ∷ g ∷ before) , after , refl , refl , refl ,
    Nat.s≤s (Nat.s≤s Nat.z≤n)
swapAt-remove-select (suc h) [] after f (Nat.s≤s lt) =
  [] , swapAt h after , refl , refl , refl , lt
swapAt-remove-select (suc h) (g ∷ before) after f (Nat.s≤s lt)
  with residualSwap h (L.length before)
     | swapAt-remove-select h before after f lt
... | none | before′ , after′ , swapped , removed , lenEq , bound =
  (g ∷ before′) , after′ , cong (g ∷_) swapped ,
    cong (g ∷_) removed , cong suc lenEq , tt
... | some q | before′ , after′ , swapped , removed , lenEq , bound =
  (g ∷ before′) , after′ , cong (g ∷_) swapped ,
    cong (g ∷_) removed , cong suc lenEq , Nat.s≤s bound

acquire-threads-miss :
  {x y : 𝔽 (2 *ℕ n)} →
  x ≢ y → (h k : ℕ) (ts : Vec (Soup.Thread n) m) (j : 𝔽 m)
  (F : Expr.Frame* (2 *ℕ n)) (e : Soup.Thread n) →
  V.map (swapPhi x h)
    (RUS.replaceAt (V.map (RUS.consumePhi y k) ts) j
      (RUS.consumePhi y k (F Expr.[ 𝓒[ Term.* × y × e ] ]*)))
  ≡
  RUS.replaceAt
    (V.map (RUS.consumePhi y k) (V.map (swapPhi x h) ts)) j
    (RUS.consumePhi y k
      (swapPhi-frames x h F Expr.[
        𝓒[ Term.* × y × swapPhi x h e ] ]*))
acquire-threads-miss apart h k ts j F e =
  map-replaceAt-map₂
    (swapPhi _ h)
    (RUS.consumePhi _ k)
    (λ t → RUS.consumePhi _ k (swapPhi _ h t))
    ts j
    (RUS.consumePhi _ k (F Expr.[ 𝓒[ Term.* × _ × e ] ]*))
    (RUS.consumePhi _ k
      (swapPhi-frames _ h F Expr.[
        𝓒[ Term.* × _ × swapPhi _ h e ] ]*))
    (swapPhi-consumePhi-miss apart h k)
    (swapPhi-consumePhi-miss apart h k
      (F Expr.[ 𝓒[ Term.* × _ × e ] ]*)
     ■ cong (RUS.consumePhi _ k)
         (swapPhi-plug* _ h F 𝓒[ Term.* × _ × e ]))
  ■ cong
      (λ ys →
        RUS.replaceAt ys j
          (RUS.consumePhi _ k
            (swapPhi-frames _ h F Expr.[
              𝓒[ Term.* × _ × swapPhi _ h e ] ]*)))
      (V.map-∘ (RUS.consumePhi _ k) (swapPhi _ h) ts)

acquire-threads-hit :
  (x : 𝔽 (2 *ℕ n)) (h k k′ : ℕ) (res : ResidualSwap) →
  residualSwap h k ≡ res →
  k′ ≡ swapSlot h k →
  (ts : Vec (Soup.Thread n) m) (j : 𝔽 m)
  (F : Expr.Frame* (2 *ℕ n)) (e : Soup.Thread n) →
  V.map (applyResidualPhi x res)
    (RUS.replaceAt (V.map (RUS.consumePhi x k) ts) j
      (RUS.consumePhi x k (F Expr.[ 𝓒[ Term.* × x × e ] ]*)))
  ≡
  RUS.replaceAt
    (V.map (RUS.consumePhi x k′) (V.map (swapPhi x h) ts)) j
    (RUS.consumePhi x k′
      (swapPhi-frames x h F Expr.[
        𝓒[ Term.* × x × swapPhi x h e ] ]*))
acquire-threads-hit {n = n} x h k k′ res resEq slotEq ts j F e =
  map-replaceAt-map₂
    (applyResidualPhi x res)
    (RUS.consumePhi x k)
    (λ t → RUS.consumePhi x k′ (swapPhi x h t))
    ts j
    (RUS.consumePhi x k (F Expr.[ 𝓒[ Term.* × x × e ] ]*))
    (RUS.consumePhi x k′
      (swapPhi-frames x h F Expr.[
        𝓒[ Term.* × x × swapPhi x h e ] ]*))
    commute replacement
  ■ cong
      (λ ys →
        RUS.replaceAt ys j
          (RUS.consumePhi x k′
            (swapPhi-frames x h F Expr.[
              𝓒[ Term.* × x × swapPhi x h e ] ]*)))
      (V.map-∘ (RUS.consumePhi x k′) (swapPhi x h) ts)
  where
  commute :
    (t : Soup.Thread n) →
    applyResidualPhi x res (RUS.consumePhi x k t) ≡
    RUS.consumePhi x k′ (swapPhi x h t)
  commute t =
    sym
      (consumePhi-swapPhi x h k t
      ■ cong (λ r → applyResidualPhi x r (RUS.consumePhi x k t)) resEq)
    ■ cong (λ l → RUS.consumePhi x l (swapPhi x h t)) (sym slotEq)

  body : Soup.Thread n
  body = 𝓒[ Term.* × x × e ]

  targetBody : Soup.Thread n
  targetBody =
    swapPhi-frames x h F Expr.[
      𝓒[ Term.* × x × swapPhi x h e ] ]*

  replacement :
    applyResidualPhi x res
      (RUS.consumePhi x k (F Expr.[ body ]*)) ≡
    RUS.consumePhi x k′ targetBody
  replacement =
    commute (F Expr.[ body ]*)
    ■ cong (RUS.consumePhi x k′) (swapPhi-plug* x h F body)

insertPhi-hit-at :
  (x : 𝔽 n) (k l : ℕ) →
  RUS.insertPhi x k (Term.`phi (x , l)) ≡
  Term.`phi (x , RUS.insertSlot k l)
insertPhi-hit-at x k l with x FinP.≟ x
... | yes refl = refl
... | no apart = ⊥-elim (apart refl)

insertPhi-miss-at :
  {x y : 𝔽 n} →
  x ≢ y → (k l : ℕ) →
  RUS.insertPhi x k (Term.`phi (y , l)) ≡ Term.`phi (y , l)
insertPhi-miss-at {x = x} {y = y} apart k l with x FinP.≟ y
... | no _ = refl
... | yes same = ⊥-elim (apart same)

swapPhi-insertPhi-miss :
  {x y : 𝔽 n} →
  x ≢ y → (h k : ℕ) (t : Term.Tm n) →
  swapPhi x h (RUS.insertPhi y k t) ≡
  RUS.insertPhi y k (swapPhi x h t)
swapPhi-insertPhi-miss apart h k (Term.` z) = refl
swapPhi-insertPhi-miss {x = x} {y = y} apart h k (Term.`phi (z , l))
  with y FinP.≟ z | x FinP.≟ z
... | no y≢z | no x≢z
  rewrite Dec.dec-no (y FinP.≟ z) y≢z
        | Dec.dec-no (x FinP.≟ z) x≢z = refl
... | no y≢z | yes refl
  rewrite Dec.dec-no (y FinP.≟ x) y≢z
        | Dec.dec-yes-irr (x FinP.≟ x) ≡-irrelevant refl = refl
... | yes refl | no x≢y
  rewrite Dec.dec-yes-irr (y FinP.≟ y) ≡-irrelevant refl
        | Dec.dec-no (x FinP.≟ y) x≢y = refl
... | yes refl | yes refl = ⊥-elim (apart refl)
swapPhi-insertPhi-miss apart h k (Term.K c) = refl
swapPhi-insertPhi-miss {x = x} {y = y} apart h k (Term.ƛ t) =
  cong Term.ƛ
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k t)
swapPhi-insertPhi-miss {x = x} {y = y} apart h k (Term.μ t) =
  cong Term.μ
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k t)
swapPhi-insertPhi-miss apart h k (t₁ Term.·⟨ d ⟩ t₂) =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-insertPhi-miss apart h k t₁)
    (swapPhi-insertPhi-miss apart h k t₂)
swapPhi-insertPhi-miss apart h k (t₁ Term.; t₂) =
  cong₂ Term._;_
    (swapPhi-insertPhi-miss apart h k t₁)
    (swapPhi-insertPhi-miss apart h k t₂)
swapPhi-insertPhi-miss apart h k (t₁ Term.⊗ t₂) =
  cong₂ Term._⊗_
    (swapPhi-insertPhi-miss apart h k t₁)
    (swapPhi-insertPhi-miss apart h k t₂)
swapPhi-insertPhi-miss {x = x} {y = y} apart h k (Term.`let t₁ `in t₂) =
  cong₂ Term.`let_`in_
    (swapPhi-insertPhi-miss apart h k t₁)
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k t₂)
swapPhi-insertPhi-miss {x = x} {y = y} apart h k (Term.`let⊗ t₁ `in t₂) =
  cong₂ Term.`let⊗_`in_
    (swapPhi-insertPhi-miss apart h k t₁)
    (swapPhi-insertPhi-miss
      (apart ∘ Fin.suc-injective ∘ Fin.suc-injective) h k t₂)
swapPhi-insertPhi-miss apart h k (Term.`inj side t) =
  cong (Term.`inj side) (swapPhi-insertPhi-miss apart h k t)
swapPhi-insertPhi-miss {x = x} {y = y} apart h k
  (Term.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₃ Term.`case_`of⟨_;_⟩
    (swapPhi-insertPhi-miss apart h k t)
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k t₁)
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k t₂)

swapPhi-insertPhi-miss-frame :
  {x y : 𝔽 n} →
  x ≢ y → (h k : ℕ) (F : Expr.Frame n) (t : Term.Tm n) →
  swapPhi x h (RUS.insertPhi-frame y k F Expr.[ t ]) ≡
  RUS.insertPhi-frame y k (swapPhi-frame x h F) Expr.[ swapPhi x h t ]
swapPhi-insertPhi-miss-frame apart h k (Expr.app₁ e d V?) t =
  cong₂ (Term._·⟨ d ⟩_) refl
    (swapPhi-insertPhi-miss apart h k e)
swapPhi-insertPhi-miss-frame apart h k (Expr.app₂ e d V?) t =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-insertPhi-miss apart h k e) refl
swapPhi-insertPhi-miss-frame apart h k (Expr.□⊗ e) t =
  cong₂ Term._⊗_ refl (swapPhi-insertPhi-miss apart h k e)
swapPhi-insertPhi-miss-frame apart h k (V Expr.⊗□) t =
  cong₂ Term._⊗_
    (swapPhi-insertPhi-miss apart h k (Expr.vTm V)) refl
swapPhi-insertPhi-miss-frame apart h k (Expr.□; e) t =
  cong₂ Term._;_ refl (swapPhi-insertPhi-miss apart h k e)
swapPhi-insertPhi-miss-frame {x = x} {y = y} apart h k
  (Expr.`let-`in e) t =
  cong₂ Term.`let_`in_ refl
    (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k e)
swapPhi-insertPhi-miss-frame {x = x} {y = y} apart h k
  (Expr.`let⊗-`in e) t =
  cong₂ Term.`let⊗_`in_ refl
    (swapPhi-insertPhi-miss
      (apart ∘ Fin.suc-injective ∘ Fin.suc-injective) h k e)
swapPhi-insertPhi-miss-frame apart h k (Expr.`inj□ side) t = refl
swapPhi-insertPhi-miss-frame {x = x} {y = y} apart h k
  (Expr.`case□`of⟨ e₁ ; e₂ ⟩) t =
  cong₂
    (λ head branches →
      Term.`case head `of⟨ proj₁ branches ; proj₂ branches ⟩)
    refl
    (cong₂ _,_
      (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k e₁)
      (swapPhi-insertPhi-miss (apart ∘ Fin.suc-injective) h k e₂))

swapPhi-insertPhi-miss-frames :
  {x y : 𝔽 n} →
  x ≢ y → (h k : ℕ) (F : Expr.Frame* n) (t : Term.Tm n) →
  swapPhi x h (RUS.insertPhi-frames y k F Expr.[ t ]*) ≡
  RUS.insertPhi-frames y k (swapPhi-frames x h F) Expr.[ swapPhi x h t ]*
swapPhi-insertPhi-miss-frames apart h k [] t = refl
swapPhi-insertPhi-miss-frames apart h k (F ∷ Fs) t =
  swapPhi-insertPhi-miss-frame apart h k F
    (RUS.insertPhi-frames _ k Fs Expr.[ t ]*)
  ■ cong (RUS.insertPhi-frame _ k (swapPhi-frame _ h F) Expr.[_])
      (swapPhi-insertPhi-miss-frames apart h k Fs t)

swapSlot-fixed-past :
  (h l : ℕ) →
  suc h Nat.< l →
  swapSlot h l ≡ l
swapSlot-fixed-past zero zero ()
swapSlot-fixed-past zero (suc zero) (Nat.s≤s ())
swapSlot-fixed-past zero (suc (suc l)) lt = refl
swapSlot-fixed-past (suc h) zero ()
swapSlot-fixed-past (suc h) (suc l) (Nat.s≤s lt) =
  cong suc (swapSlot-fixed-past h l lt)

swapSlot-insertSlot-past :
  (h k l : ℕ) →
  suc h Nat.< k →
  swapSlot h (RUS.insertSlot k l) ≡
  RUS.insertSlot k (swapSlot h l)
swapSlot-insertSlot-past zero zero l ()
swapSlot-insertSlot-past zero (suc zero) l (Nat.s≤s ())
swapSlot-insertSlot-past zero (suc (suc k)) zero lt = refl
swapSlot-insertSlot-past zero (suc (suc k)) (suc zero) lt = refl
swapSlot-insertSlot-past zero (suc (suc k)) (suc (suc l)) lt = refl
swapSlot-insertSlot-past (suc h) zero l ()
swapSlot-insertSlot-past (suc h) (suc k) zero lt = refl
swapSlot-insertSlot-past (suc h) (suc k) (suc l) (Nat.s≤s lt) =
  cong suc (swapSlot-insertSlot-past h k l lt)

swapPhi-insertPhi-past :
  (x : 𝔽 n) (h k : ℕ) (t : Term.Tm n) →
  suc h Nat.< k →
  swapPhi x h (RUS.insertPhi x k t) ≡
  RUS.insertPhi x k (swapPhi x h t)
swapPhi-insertPhi-past x h k (Term.` z) lt = refl
swapPhi-insertPhi-past x h k (Term.`phi (y , l)) lt with x FinP.≟ y
... | no apart =
  swapPhi-miss apart h l
  ■ sym (insertPhi-miss-at apart k l)
... | yes refl =
  swapPhi-hit x h (RUS.insertSlot k l)
  ■ cong (λ q → Term.`phi (x , q))
      (swapSlot-insertSlot-past h k l lt)
  ■ sym (insertPhi-hit-at x k (swapSlot h l))
swapPhi-insertPhi-past x h k (Term.K c) lt = refl
swapPhi-insertPhi-past x h k (Term.ƛ t) lt =
  cong Term.ƛ (swapPhi-insertPhi-past (suc x) h k t lt)
swapPhi-insertPhi-past x h k (Term.μ t) lt =
  cong Term.μ (swapPhi-insertPhi-past (suc x) h k t lt)
swapPhi-insertPhi-past x h k (t₁ Term.·⟨ d ⟩ t₂) lt =
  cong₂ (Term._·⟨ d ⟩_)
    (swapPhi-insertPhi-past x h k t₁ lt)
    (swapPhi-insertPhi-past x h k t₂ lt)
swapPhi-insertPhi-past x h k (t₁ Term.; t₂) lt =
  cong₂ Term._;_
    (swapPhi-insertPhi-past x h k t₁ lt)
    (swapPhi-insertPhi-past x h k t₂ lt)
swapPhi-insertPhi-past x h k (t₁ Term.⊗ t₂) lt =
  cong₂ Term._⊗_
    (swapPhi-insertPhi-past x h k t₁ lt)
    (swapPhi-insertPhi-past x h k t₂ lt)
swapPhi-insertPhi-past x h k (Term.`let t₁ `in t₂) lt =
  cong₂ Term.`let_`in_
    (swapPhi-insertPhi-past x h k t₁ lt)
    (swapPhi-insertPhi-past (suc x) h k t₂ lt)
swapPhi-insertPhi-past x h k (Term.`let⊗ t₁ `in t₂) lt =
  cong₂ Term.`let⊗_`in_
    (swapPhi-insertPhi-past x h k t₁ lt)
    (swapPhi-insertPhi-past (suc (suc x)) h k t₂ lt)
swapPhi-insertPhi-past x h k (Term.`inj side t) lt =
  cong (Term.`inj side) (swapPhi-insertPhi-past x h k t lt)
swapPhi-insertPhi-past x h k (Term.`case t `of⟨ t₁ ; t₂ ⟩) lt =
  cong₃ Term.`case_`of⟨_;_⟩
    (swapPhi-insertPhi-past x h k t lt)
    (swapPhi-insertPhi-past (suc x) h k t₁ lt)
    (swapPhi-insertPhi-past (suc x) h k t₂ lt)

swapPhi-insertPhi-past-frame :
  (x : 𝔽 n) (h k : ℕ) (F : Expr.Frame n) (t : Term.Tm n) →
  suc h Nat.< k →
  swapPhi x h (RUS.insertPhi-frame x k F Expr.[ t ]) ≡
  RUS.insertPhi-frame x k (swapPhi-frame x h F) Expr.[ swapPhi x h t ]
swapPhi-insertPhi-past-frame x h k (Expr.app₁ e d V?) t lt =
  cong₂ (Term._·⟨ d ⟩_) refl (swapPhi-insertPhi-past x h k e lt)
swapPhi-insertPhi-past-frame x h k (Expr.app₂ e d V?) t lt =
  cong₂ (Term._·⟨ d ⟩_) (swapPhi-insertPhi-past x h k e lt) refl
swapPhi-insertPhi-past-frame x h k (Expr.□⊗ e) t lt =
  cong₂ Term._⊗_ refl (swapPhi-insertPhi-past x h k e lt)
swapPhi-insertPhi-past-frame x h k (V Expr.⊗□) t lt =
  cong₂ Term._⊗_ (swapPhi-insertPhi-past x h k (Expr.vTm V) lt) refl
swapPhi-insertPhi-past-frame x h k (Expr.□; e) t lt =
  cong₂ Term._;_ refl (swapPhi-insertPhi-past x h k e lt)
swapPhi-insertPhi-past-frame x h k (Expr.`let-`in e) t lt =
  cong₂ Term.`let_`in_ refl (swapPhi-insertPhi-past (suc x) h k e lt)
swapPhi-insertPhi-past-frame x h k (Expr.`let⊗-`in e) t lt =
  cong₂ Term.`let⊗_`in_ refl
    (swapPhi-insertPhi-past (suc (suc x)) h k e lt)
swapPhi-insertPhi-past-frame x h k (Expr.`inj□ side) t lt = refl
swapPhi-insertPhi-past-frame x h k (Expr.`case□`of⟨ e₁ ; e₂ ⟩) t lt =
  cong₂
    (λ head branches →
      Term.`case head `of⟨ proj₁ branches ; proj₂ branches ⟩)
    refl
    (cong₂ _,_
      (swapPhi-insertPhi-past (suc x) h k e₁ lt)
      (swapPhi-insertPhi-past (suc x) h k e₂ lt))

swapPhi-insertPhi-past-frames :
  (x : 𝔽 n) (h k : ℕ) (F : Expr.Frame* n) (t : Term.Tm n) →
  suc h Nat.< k →
  swapPhi x h (RUS.insertPhi-frames x k F Expr.[ t ]*) ≡
  RUS.insertPhi-frames x k (swapPhi-frames x h F) Expr.[ swapPhi x h t ]*
swapPhi-insertPhi-past-frames x h k [] t lt = refl
swapPhi-insertPhi-past-frames x h k (F ∷ Fs) t lt =
  swapPhi-insertPhi-past-frame x h k F
    (RUS.insertPhi-frames x k Fs Expr.[ t ]*) lt
  ■ cong (RUS.insertPhi-frame x k (swapPhi-frame x h F) Expr.[_])
      (swapPhi-insertPhi-past-frames x h k Fs t lt)

swapAt-++end :
  (h : ℕ) (fs : List Soup.Flag) (f : Soup.Flag) →
  suc h Nat.< L.length fs →
  swapAt h (fs ++ f ∷ []) ≡ swapAt h fs ++ f ∷ []
swapAt-++end zero [] f ()
swapAt-++end zero (g ∷ []) f (Nat.s≤s ())
swapAt-++end zero (g ∷ g′ ∷ fs) f lt = refl
swapAt-++end (suc h) [] f ()
swapAt-++end (suc h) (g ∷ fs) f (Nat.s≤s lt) =
  cong (g ∷_) (swapAt-++end h fs f lt)

insertDrop-end :
  (fs : List Soup.Flag) →
  SlotInsert.insertDrop (L.length fs) fs ≡ fs ++ Soup.drop ∷ []
insertDrop-end [] = refl
insertDrop-end (f ∷ fs) = cong (f ∷_) (insertDrop-end fs)

insertDrop-at-length :
  (k : ℕ) (fs : List Soup.Flag) →
  k ≡ L.length fs →
  SlotInsert.insertDrop k fs ≡ fs ++ Soup.drop ∷ []
insertDrop-at-length .(L.length fs) fs refl = insertDrop-end fs

insertDrop-length :
  (k : ℕ) (fs : List Soup.Flag) →
  L.length (SlotInsert.insertDrop k fs) ≡ suc (L.length fs)
insertDrop-length zero fs = refl
insertDrop-length (suc k) [] = refl
insertDrop-length (suc k) (f ∷ fs) =
  cong suc (insertDrop-length k fs)

swapPhi-rsplitBody-miss :
  {x y : 𝔽 n} →
  x ≢ y → (h k : ℕ) (e₁ e₂ : Term.Tm n) →
  swapPhi x h (SlotInsert.rsplitBody y k e₁ e₂) ≡
  SlotInsert.rsplitBody y k (swapPhi x h e₁) (swapPhi x h e₂)
swapPhi-rsplitBody-miss apart h k e₁ e₂ =
  cong₂ Term._⊗_
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_
        (swapPhi-insertPhi-miss apart h k e₁) refl)
      (swapPhi-miss apart h k))
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_
        (swapPhi-miss apart h k) refl)
      (swapPhi-insertPhi-miss apart h k e₂))

swapPhi-rsplitBody-past :
  (x : 𝔽 n) (h k : ℕ) (e₁ e₂ : Term.Tm n) →
  suc h Nat.< k →
  swapPhi x h (SlotInsert.rsplitBody x k e₁ e₂) ≡
  SlotInsert.rsplitBody x k (swapPhi x h e₁) (swapPhi x h e₂)
swapPhi-rsplitBody-past x h k e₁ e₂ lt =
  cong₂ Term._⊗_
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_
        (swapPhi-insertPhi-past x h k e₁ lt) refl)
      phiFixed)
    (cong₂ Term._⊗_
      (cong₂ Term._⊗_ phiFixed refl)
      (swapPhi-insertPhi-past x h k e₂ lt))
  where
  phiFixed :
    swapPhi x h (Term.`phi (x , k)) ≡ Term.`phi (x , k)
  phiFixed =
    swapPhi-hit x h k
    ■ cong (λ l → Term.`phi (x , l)) (swapSlot-fixed-past h k lt)

swap-flags-selected :
  (cs : Vec Soup.Channel n) (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (i : 𝔽 n) (side : 𝔽 2)
  (before after : List Soup.Flag) (f : Soup.Flag) →
  suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide) →
  RUS.endpointFlags (lookup cs i) side ≡ before ++ f ∷ after →
  Σ[ before′ ∈ List Soup.Flag ] Σ[ after′ ∈ List Soup.Flag ]
    ( RUS.endpointFlags
        (lookup (V.updateAt cs r (swapFlags swapSide h)) i) side
      ≡ before′ ++ f ∷ after′) ×
    ( if does (r FinP.≟ i) then
        if does (swapSide FinP.≟ side) then
          L.length before′ ≡ swapSlot h (L.length before)
        else
          L.length before′ ≡ L.length before
      else
        L.length before′ ≡ L.length before )
swap-flags-selected cs r swapSide h i side before after f lt flags
  with r FinP.≟ i
... | no apart =
  before , after ,
  (cong (λ ch → RUS.endpointFlags ch side)
     (V.lookup∘updateAt′ i r (apart ∘ sym) cs) ■ flags) ,
  refl
... | yes refl with swapSide FinP.≟ side
...   | no sideApart =
  before , after ,
  (cong (λ ch → RUS.endpointFlags ch side)
     (V.lookup∘updateAt r cs) ■
   endpointFlags-swapFlags-miss swapSide side h (lookup cs r) sideApart ■
   flags) ,
  refl
...   | yes refl with swapAt-select h before after f (subst (suc h Nat.<_) (cong L.length flags) lt)
...     | before′ , after′ , swapped , lenEq =
  before′ , after′ ,
  (cong (λ ch → RUS.endpointFlags ch side)
     (V.lookup∘updateAt r cs) ■
   BorrowedCF.Simulation.BackwardSoup.Statement.endpointFlags-swapFlags side h
     (lookup cs r) ■
   cong (swapAt h) flags ■
   swapped) ,
  lenEq

------------------------------------------------------------------------
-- One-generator equivariance for the soup rules.

One-Bisim : Set
One-Bisim =
  ∀ {n m : ℕ} {C D : Soup.Config n m}
    {n′ m′ : ℕ} {C′ : Soup.Config n′ m′} →
  C ≈¹ D →
  C RUS.─→ₚ C′ →
  Σ[ D′ ∈ Soup.Config n′ m′ ] (D RUS.─→ₚ D′) × C′ ≈ˢ D′

exp-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side))
  (j : 𝔽 m) {e′ : Soup.Thread n} →
  lookup ts j Expr.⋯→ e′ →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags side h))
      (V.map (swapPhi (Soup.endpoint r side) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs (RUS.replaceAt ts j e′) ≈ˢ D′
exp-equiv {n = n} {m = m} cs ts r side h lt j {e′ = e′} red =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags side h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  C′ : Soup.Config n m
  C′ = Soup.config cs (RUS.replaceAt ts j e′)

  D′ : Soup.Config n m
  D′ = Soup.config csS (RUS.replaceAt tsS j (f e′))

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Exp j
      (subst (λ t → t Expr.⋯→ f e′)
        (sym (V.lookup-map j f ts))
        (swapPhi-⋯→ x h red))

  base : C′ ≈¹ Soup.config csS (V.map f (RUS.replaceAt ts j e′))
  base = swap cs (RUS.replaceAt ts j e′) r side h lt

  targetEq :
    Soup.config csS (V.map f (RUS.replaceAt ts j e′)) ≡ D′
  targetEq = cong (Soup.config csS) (map-replaceAt f ts j e′)

fork-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side))
  (j : 𝔽 m) (F : Expr.Frame* (2 *ℕ n)) {e : Soup.Thread n} →
  Expr.Value e →
  lookup ts j ≡ F Expr.[ Term.K Term.`fork Term.·⟨ Types.𝟙 ⟩ e ]* →
  Σ[ D′ ∈ Soup.Config n (suc m) ]
    (Soup.config (V.updateAt cs r (swapFlags side h))
      (V.map (swapPhi (Soup.endpoint r side) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs
      (RUS.insertAfter
        (RUS.replaceAt ts j (F Expr.[ Term.* ]*))
        j (e Term.·⟨ Types.𝟙 ⟩ Term.*)) ≈ˢ D′
fork-equiv {n = n} {m = m} cs ts r side h lt j F {e = e} Ve selected =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags side h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  parent : Soup.Thread n
  parent = F Expr.[ Term.* ]*

  child : Soup.Thread n
  child = e Term.·⟨ Types.𝟙 ⟩ Term.*

  redex : Soup.Thread n
  redex = Term.K Term.`fork Term.·⟨ Types.𝟙 ⟩ e

  C′ : Soup.Config n (suc m)
  C′ = Soup.config cs (RUS.insertAfter (RUS.replaceAt ts j parent) j child)

  D′ : Soup.Config n (suc m)
  D′ =
    Soup.config csS
      (RUS.insertAfter
        (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))
        j (f e Term.·⟨ Types.𝟙 ⟩ Term.*))

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K Term.`fork Term.·⟨ Types.𝟙 ⟩ f e ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD = RUS.RUS-Fork j F′ (swapPhi-Value x h Ve) selectedD

  base :
    C′ ≈¹
    Soup.config csS
      (V.map f (RUS.insertAfter (RUS.replaceAt ts j parent) j child))
  base =
    swap cs (RUS.insertAfter (RUS.replaceAt ts j parent) j child)
      r side h lt

  parentEq : f parent ≡ F′ Expr.[ Term.* ]*
  parentEq = swapPhi-plug* x h F Term.*

  targetThreadsEq :
    V.map f (RUS.insertAfter (RUS.replaceAt ts j parent) j child) ≡
    RUS.insertAfter
      (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))
      j (f e Term.·⟨ Types.𝟙 ⟩ Term.*)
  targetThreadsEq =
    map-insertAfter-replace f ts j parent child
    ■ cong₂ (λ p c → RUS.insertAfter (RUS.replaceAt tsS j p) j c)
        parentEq refl

  targetEq :
    Soup.config csS
      (V.map f (RUS.insertAfter (RUS.replaceAt ts j parent) j child)) ≡
    D′
  targetEq = cong (Soup.config csS) targetThreadsEq

lsplit-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : Expr.Frame* (2 *ℕ n)) {s : Types.𝕊 0}
  {e₁ e₂ : Soup.Thread n} →
  RUS.is-open cs i →
  lookup ts j ≡
    F Expr.[ Term.K (Term.`lsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × Soup.endpoint i side × e₂ ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs
      (RUS.replaceAt ts j
        (F Expr.[
          𝓒[ e₁ × Soup.endpoint i side × Term.* ] Term.⊗
          𝓒[ Term.* × Soup.endpoint i side × e₂ ] ]*)) ≈ˢ D′
lsplit-equiv {n = n} {m = m} cs ts r swapSide h lt j i side F {s = s}
  {e₁ = e₁} {e₂ = e₂} live selected =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K (Term.`lsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × Soup.endpoint i side × e₂ ]

  body : Soup.Thread n
  body =
    𝓒[ e₁ × Soup.endpoint i side × Term.* ] Term.⊗
    𝓒[ Term.* × Soup.endpoint i side × e₂ ]

  body′ : Soup.Thread n
  body′ =
    𝓒[ f e₁ × Soup.endpoint i side × Term.* ] Term.⊗
    𝓒[ Term.* × Soup.endpoint i side × f e₂ ]

  C′ : Soup.Config n m
  C′ = Soup.config cs (RUS.replaceAt ts j (F Expr.[ body ]*))

  D′ : Soup.Config n m
  D′ = Soup.config csS (RUS.replaceAt tsS j (F′ Expr.[ body′ ]*))

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K (Term.`lsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ f e₁ × Soup.endpoint i side × f e₂ ] ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-LSplit j i side F′
      (is-open-swap cs r swapSide h i live)
      selectedD

  base : C′ ≈¹ Soup.config csS (V.map f (RUS.replaceAt ts j (F Expr.[ body ]*)))
  base = swap cs (RUS.replaceAt ts j (F Expr.[ body ]*)) r swapSide h lt

  replacementEq : f (F Expr.[ body ]*) ≡ F′ Expr.[ body′ ]*
  replacementEq = swapPhi-plug* x h F body

  targetThreadsEq :
    V.map f (RUS.replaceAt ts j (F Expr.[ body ]*)) ≡
    RUS.replaceAt tsS j (F′ Expr.[ body′ ]*)
  targetThreadsEq =
    map-replaceAt f ts j (F Expr.[ body ]*)
    ■ cong (λ t → RUS.replaceAt tsS j t) replacementEq

  targetEq :
    Soup.config csS (V.map f (RUS.replaceAt ts j (F Expr.[ body ]*))) ≡
    D′
  targetEq = cong (Soup.config csS) targetThreadsEq

rsplit-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : Expr.Frame* (2 *ℕ n)) (before after : List Soup.Flag)
  {s : Types.𝕊 0} {e₁ e₂ : Soup.Thread n} →
  RUS.is-open cs i →
  RUS.endpointFlags (lookup cs i) side ≡ before ++ after →
  lookup ts j ≡
    F Expr.[ Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × Soup.endpoint i side × e₂ ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config
      (V.updateAt cs i
        (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after)))
      (let x = Soup.endpoint i side
           k = L.length before
       in RUS.replaceAt (V.map (RUS.insertPhi x k) ts) j
            (RUS.insertPhi-frames x k F Expr.[
              𝓒[ RUS.insertPhi x k e₁ × x × Term.`phi (x , k) ] Term.⊗
              𝓒[ Term.`phi (x , k) × x × RUS.insertPhi x k e₂ ] ]*))
      ≈ˢ D′
rsplit-equiv {n = n} {m = m} cs ts r swapSide h lt
  j i side F before after {s = s} {e₁ = e₁} {e₂ = e₂}
  live flags selected with r FinP.≟ i
... | no apart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  slot : ℕ
  slot = L.length before

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  g : Soup.Thread n → Soup.Thread n
  g = RUS.insertPhi y slot

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)
  sourceChannels =
    V.updateAt cs i (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after))
  targetChannels =
    V.updateAt csS i (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after))

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × y × e₂ ]

  replacement : Soup.Thread n
  replacement =
    RUS.insertPhi-frames y slot F Expr.[
      SlotInsert.rsplitBody y slot e₁ e₂ ]*

  replacementD : Soup.Thread n
  replacementD =
    RUS.insertPhi-frames y slot F′ Expr.[
      SlotInsert.rsplitBody y slot (f e₁) (f e₂) ]*

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannels
    (RUS.replaceAt (V.map g ts) j replacement)

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels
    (RUS.replaceAt (V.map g tsS) j replacementD)

  endpointApart : x ≢ y
  endpointApart = endpoint-apart-channel apart

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt′ i r (apart ∘ sym) cs)
    ■ flags

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ f e₁ × y × f e₂ ] ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-RSplit j i side F′ before after
      (is-open-swap cs r swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels r) swapSide ≡
    RUS.endpointFlags (lookup cs r) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt′ r i apart cs)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels r) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f (RUS.replaceAt (V.map g ts) j replacement))
  base =
    swap sourceChannels (RUS.replaceAt (V.map g ts) j replacement)
      r swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels r (swapFlags swapSide h) ≡ targetChannels
  channelsEq = V.updateAt-commutes r i apart cs

  replacementEq : f replacement ≡ replacementD
  replacementEq =
    swapPhi-insertPhi-miss-frames endpointApart h slot F
      (SlotInsert.rsplitBody y slot e₁ e₂)
    ■ cong (RUS.insertPhi-frames y slot F′ Expr.[_]*)
        (swapPhi-rsplitBody-miss endpointApart h slot e₁ e₂)

  threadsEq :
    V.map f (RUS.replaceAt (V.map g ts) j replacement) ≡
    RUS.replaceAt (V.map g tsS) j replacementD
  threadsEq =
    map-replaceAt-map₂ f g (λ t → g (f t)) ts j replacement replacementD
      (λ t → swapPhi-insertPhi-miss endpointApart h slot t)
      replacementEq
    ■ cong (λ ys → RUS.replaceAt ys j replacementD)
        (V.map-∘ g f ts)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f (RUS.replaceAt (V.map g ts) j replacement)) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

... | yes refl with swapSide FinP.≟ side
...   | no sideApart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  slot : ℕ
  slot = L.length before

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  g : Soup.Thread n → Soup.Thread n
  g = RUS.insertPhi y slot

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags swapSide h)
  sourceChannels =
    V.updateAt cs i (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after))
  targetChannels =
    V.updateAt csS i (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after))

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × y × e₂ ]

  replacement : Soup.Thread n
  replacement =
    RUS.insertPhi-frames y slot F Expr.[
      SlotInsert.rsplitBody y slot e₁ e₂ ]*

  replacementD : Soup.Thread n
  replacementD =
    RUS.insertPhi-frames y slot F′ Expr.[
      SlotInsert.rsplitBody y slot (f e₁) (f e₂) ]*

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannels
    (RUS.replaceAt (V.map g ts) j replacement)

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels
    (RUS.replaceAt (V.map g tsS) j replacementD)

  endpointApart : x ≢ y
  endpointApart = endpoint-apart-side i sideApart

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-swapFlags-miss swapSide side h (lookup cs i) sideApart
    ■ flags

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ f e₁ × y × f e₂ ] ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-RSplit j i side F′ before after
      (is-open-swap cs i swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels i) swapSide ≡
    RUS.endpointFlags (lookup cs i) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-setEndpointFlags-miss side swapSide
        (before ++ Soup.drop ∷ after) (lookup cs i) (sideApart ∘ sym)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels i) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f (RUS.replaceAt (V.map g ts) j replacement))
  base =
    swap sourceChannels (RUS.replaceAt (V.map g ts) j replacement)
      i swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels i (swapFlags swapSide h) ≡ targetChannels
  channelsEq =
    V.updateAt-updateAt i cs
    ■ sym
        (V.updateAt-updateAt-local i cs
          (setEndpointFlags-swapFlags-miss-commute swapSide side h
            (before ++ Soup.drop ∷ after) (lookup cs i) sideApart))

  replacementEq : f replacement ≡ replacementD
  replacementEq =
    swapPhi-insertPhi-miss-frames endpointApart h slot F
      (SlotInsert.rsplitBody y slot e₁ e₂)
    ■ cong (RUS.insertPhi-frames y slot F′ Expr.[_]*)
        (swapPhi-rsplitBody-miss endpointApart h slot e₁ e₂)

  threadsEq :
    V.map f (RUS.replaceAt (V.map g ts) j replacement) ≡
    RUS.replaceAt (V.map g tsS) j replacementD
  threadsEq =
    map-replaceAt-map₂ f g (λ t → g (f t)) ts j replacement replacementD
      (λ t → swapPhi-insertPhi-miss endpointApart h slot t)
      replacementEq
    ■ cong (λ ys → RUS.replaceAt ys j replacementD)
        (V.map-∘ g f ts)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f (RUS.replaceAt (V.map g ts) j replacement)) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

...   | yes refl =
  D′ , stepD , ≈ˢ-trans sourceToKD sourceKDToD
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i side

  flags₀ : List Soup.Flag
  flags₀ = before ++ after

  slot : ℕ
  slot = L.length before

  beforeD : List Soup.Flag
  beforeD = swapAt h flags₀

  kD : ℕ
  kD = L.length beforeD

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  g : Soup.Thread n → Soup.Thread n
  g = RUS.insertPhi x kD

  csS : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags side h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ e₁ × x × e₂ ]

  replacementP : Soup.Thread n
  replacementP =
    RUS.insertPhi-frames x slot F Expr.[
      SlotInsert.rsplitBody x slot e₁ e₂ ]*

  sourceChannelsP : Vec Soup.Channel n
  sourceChannelsP =
    V.updateAt cs i
      (RUS.setEndpointFlags side (before ++ Soup.drop ∷ after))

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannelsP
    (RUS.replaceAt (V.map (RUS.insertPhi x slot) ts) j replacementP)

  sourceAtP : Soup.Config n m
  sourceAtP = SlotInsert.rsplitResult cs ts j i side F flags₀ slot e₁ e₂

  sourceReplacementKD : Soup.Thread n
  sourceReplacementKD =
    RUS.insertPhi-frames x kD F Expr.[
      SlotInsert.rsplitBody x kD e₁ e₂ ]*

  sourceChannelsKD : Vec Soup.Channel n
  sourceChannelsKD =
    V.updateAt cs i (RUS.setEndpointFlags side
      (SlotInsert.insertDrop kD flags₀))

  sourceThreadsKD : Vec (Soup.Thread n) m
  sourceThreadsKD =
    RUS.replaceAt (V.map g ts) j sourceReplacementKD

  sourceAtKD : Soup.Config n m
  sourceAtKD = Soup.config sourceChannelsKD sourceThreadsKD

  targetChannels : Vec Soup.Channel n
  targetChannels =
    V.updateAt csS i
      (RUS.setEndpointFlags side (beforeD ++ Soup.drop ∷ []))

  targetReplacement : Soup.Thread n
  targetReplacement =
    RUS.insertPhi-frames x kD F′ Expr.[
      SlotInsert.rsplitBody x kD (f e₁) (f e₂) ]*

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels
    (RUS.replaceAt (V.map g tsS) j targetReplacement)

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ beforeD ++ []
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ BorrowedCF.Simulation.BackwardSoup.Statement.endpointFlags-swapFlags
        side h (lookup cs i)
    ■ cong (swapAt h) flags
    ■ sym (L.++-identityʳ beforeD)

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K (Term.`rsplit s) Term.·⟨ Types.𝟙 ⟩
      𝓒[ f e₁ × x × f e₂ ] ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-RSplit j i side F′ beforeD []
      (is-open-swap cs i side h i live)
      flagsD selectedD

  actualEq : C′ ≡ sourceAtP
  actualEq =
    cong₂ Soup.config
      (cong (λ fs → V.updateAt cs i (RUS.setEndpointFlags side fs))
        (sym (SlotInsert.insertDrop-prefix before after)))
      refl

  pBound : slot Nat.≤ L.length flags₀
  pBound = L.length-++-≤ˡ before

  kDEq : kD ≡ L.length flags₀
  kDEq = BorrowedCF.Simulation.BackwardSoup.Statement.swapAt-length h flags₀

  kDBound : kD Nat.≤ L.length flags₀
  kDBound = subst (λ k → k Nat.≤ L.length flags₀) (sym kDEq) NatP.≤-refl

  sourceToKD : C′ ≈ˢ sourceAtKD
  sourceToKD =
    subst (λ C → C ≈ˢ sourceAtKD) (sym actualEq)
      (SlotInsert.rsplit-positions cs ts j i side F flags₀
        slot kD e₁ e₂ pBound kDBound)

  sourceFlagsEq :
    RUS.endpointFlags (lookup sourceChannelsKD i) side ≡
    SlotInsert.insertDrop kD flags₀
  sourceFlagsEq =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-setEndpointFlags side
        (SlotInsert.insertDrop kD flags₀) (lookup cs i)

  ltFlags : suc h Nat.< L.length flags₀
  ltFlags = subst (suc h Nat.<_) (cong L.length flags) lt

  ltK : suc h Nat.< kD
  ltK = subst (suc h Nat.<_) (sym kDEq) ltFlags

  ltSource :
    suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannelsKD i) side)
  ltSource =
    subst (suc h Nat.<_) (sym (cong L.length sourceFlagsEq))
      (subst (suc h Nat.<_) (sym (insertDrop-length kD flags₀))
        (NatP.m≤n⇒m≤1+n ltFlags))

  base :
    sourceAtKD ≈¹
    Soup.config
      (V.updateAt sourceChannelsKD i (swapFlags side h))
      (V.map f sourceThreadsKD)
  base = swap sourceChannelsKD sourceThreadsKD i side h ltSource

  insertedAtEnd :
    SlotInsert.insertDrop kD flags₀ ≡ flags₀ ++ Soup.drop ∷ []
  insertedAtEnd = insertDrop-at-length kD flags₀ kDEq

  swappedFlags :
    swapAt h (SlotInsert.insertDrop kD flags₀) ≡ beforeD ++ Soup.drop ∷ []
  swappedFlags =
    cong (swapAt h) insertedAtEnd
    ■ swapAt-++end h flags₀ Soup.drop ltFlags

  channelsEq :
    V.updateAt sourceChannelsKD i (swapFlags side h) ≡ targetChannels
  channelsEq =
    V.updateAt-updateAt i cs
    ■ sym
        (V.updateAt-updateAt-local i cs
          (setEndpointFlags-swapFlags-hit-replace side h
            (SlotInsert.insertDrop kD flags₀)
            (beforeD ++ Soup.drop ∷ [])
            (lookup cs i) swappedFlags))

  targetReplacementEq : f sourceReplacementKD ≡ targetReplacement
  targetReplacementEq =
    swapPhi-insertPhi-past-frames x h kD F
      (SlotInsert.rsplitBody x kD e₁ e₂) ltK
    ■ cong (RUS.insertPhi-frames x kD F′ Expr.[_]*)
        (swapPhi-rsplitBody-past x h kD e₁ e₂ ltK)

  threadsEq : V.map f sourceThreadsKD ≡
    RUS.replaceAt (V.map g tsS) j targetReplacement
  threadsEq =
    map-replaceAt-map₂ f g (λ t → g (f t)) ts j
      sourceReplacementKD targetReplacement
      (λ t → swapPhi-insertPhi-past x h kD t ltK)
      targetReplacementEq
    ■ cong (λ ys → RUS.replaceAt ys j targetReplacement)
        (V.map-∘ g f ts)

  targetEq :
    Soup.config
      (V.updateAt sourceChannelsKD i (swapFlags side h))
      (V.map f sourceThreadsKD) ≡ D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

  sourceKDToD : sourceAtKD ≈ˢ D′
  sourceKDToD = ≈¹⇒≈ˢ (subst (sourceAtKD ≈¹_) targetEq base)

discard-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side))
  (j : 𝔽 m) (F : Expr.Frame* (2 *ℕ n)) {e : Soup.Thread n} →
  Expr.Value e →
  lookup ts j ≡ F Expr.[ Term.K Term.`discard Term.·⟨ Types.𝟙 ⟩ e ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags side h))
      (V.map (swapPhi (Soup.endpoint r side) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≈ˢ D′
discard-equiv {n = n} {m = m} cs ts r side h lt j F {e = e} Ve selected =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags side h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex = Term.K Term.`discard Term.·⟨ Types.𝟙 ⟩ e

  C′ : Soup.Config n m
  C′ = Soup.config cs (RUS.replaceAt ts j (F Expr.[ Term.* ]*))

  D′ : Soup.Config n m
  D′ = Soup.config csS (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K Term.`discard Term.·⟨ Types.𝟙 ⟩ f e ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD = RUS.RUS-Discard j F′ (swapPhi-Value x h Ve) selectedD

  base : C′ ≈¹ Soup.config csS (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)))
  base = swap cs (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) r side h lt

  targetThreadsEq :
    V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≡
    RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*)
  targetThreadsEq =
    map-replaceAt f ts j (F Expr.[ Term.* ]*)
    ■ cong (λ t → RUS.replaceAt tsS j t)
        (swapPhi-plug* x h F Term.*)

  targetEq :
    Soup.config csS (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*))) ≡ D′
  targetEq = cong (Soup.config csS) targetThreadsEq

com-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : Expr.Frame* (2 *ℕ n))
  {e e₁′ e₂′ : Soup.Thread n} →
  j ≢ k →
  RUS.Opposite side₁ side₂ →
  RUS.is-open cs i →
  Expr.Value e →
  lookup ts j ≡
    F₁ Expr.[ Term.K Term.`send Term.·⟨ Types.𝟙 ⟩
      (e Term.⊗ 𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ]) ]* →
  lookup ts k ≡
    F₂ Expr.[ Term.K Term.`recv Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs
      (RUS.replaceTwo ts
        j (F₁ Expr.[ Term.* ]*)
        k (F₂ Expr.[ e ]*)) ≈ˢ D′
com-equiv {n = n} {m = m} cs ts r swapSide h lt
  j k i side₁ side₂ F₁ F₂ {e = e} {e₁′ = e₁′} {e₂′ = e₂′}
  j≢k opposite live Ve selected₁ selected₂ =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F₁′ F₂′ : Expr.Frame* (2 *ℕ n)
  F₁′ = swapPhi-frames x h F₁
  F₂′ = swapPhi-frames x h F₂

  redex₁ redex₂ : Soup.Thread n
  redex₁ =
    Term.K Term.`send Term.·⟨ Types.𝟙 ⟩
      (e Term.⊗ 𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ])
  redex₂ =
    Term.K Term.`recv Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ]

  C′ : Soup.Config n m
  C′ =
    Soup.config cs
      (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ e ]*))

  D′ : Soup.Config n m
  D′ =
    Soup.config csS
      (RUS.replaceTwo tsS
        j (F₁′ Expr.[ Term.* ]*)
        k (F₂′ Expr.[ f e ]*))

  selectedD₁ :
    lookup tsS j ≡
    F₁′ Expr.[ Term.K Term.`send Term.·⟨ Types.𝟙 ⟩
      (f e Term.⊗ 𝓒[ Term.* × Soup.endpoint i side₁ × f e₁′ ]) ]*
  selectedD₁ =
    V.lookup-map j f ts
    ■ cong f selected₁
    ■ swapPhi-plug* x h F₁ redex₁

  selectedD₂ :
    lookup tsS k ≡
    F₂′ Expr.[ Term.K Term.`recv Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × f e₂′ ] ]*
  selectedD₂ =
    V.lookup-map k f ts
    ■ cong f selected₂
    ■ swapPhi-plug* x h F₂ redex₂

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Com j k i side₁ side₂ F₁′ F₂′
      j≢k opposite (is-open-swap cs r swapSide h i live)
      (swapPhi-Value x h Ve) selectedD₁ selectedD₂

  base : C′ ≈¹ Soup.config csS
    (V.map f (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ e ]*)))
  base =
    swap cs (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ e ]*))
      r swapSide h lt

  repl₁Eq : f (F₁ Expr.[ Term.* ]*) ≡ F₁′ Expr.[ Term.* ]*
  repl₁Eq = swapPhi-plug* x h F₁ Term.*

  repl₂Eq : f (F₂ Expr.[ e ]*) ≡ F₂′ Expr.[ f e ]*
  repl₂Eq = swapPhi-plug* x h F₂ e

  targetThreadsEq :
    V.map f (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ e ]*)) ≡
    RUS.replaceTwo tsS j (F₁′ Expr.[ Term.* ]*) k (F₂′ Expr.[ f e ]*)
  targetThreadsEq =
    map-replaceTwo f ts j k (F₁ Expr.[ Term.* ]*) (F₂ Expr.[ e ]*)
    ■ cong₂
        (λ a b → RUS.replaceTwo tsS j a k b)
        repl₁Eq repl₂Eq

  targetEq :
    Soup.config csS
      (V.map f (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ e ]*))) ≡
    D′
  targetEq = cong (Soup.config csS) targetThreadsEq

choice-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : Expr.Frame* (2 *ℕ n)) (choice : Term.Side)
  {e₁′ e₂′ : Soup.Thread n} →
  j ≢ k →
  RUS.Opposite side₁ side₂ →
  RUS.is-open cs i →
  lookup ts j ≡
    F₁ Expr.[ Term.K (Term.`select choice) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ] ]* →
  lookup ts k ≡
    F₂ Expr.[ Term.K Term.`branch Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config cs
      (RUS.replaceTwo ts
        j (F₁ Expr.[ 𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ] ]*)
        k (F₂ Expr.[ Term.`inj choice
             𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ] ]*)) ≈ˢ D′
choice-equiv {n = n} {m = m} cs ts r swapSide h lt
  j k i side₁ side₂ F₁ F₂ choice {e₁′ = e₁′} {e₂′ = e₂′}
  j≢k opposite live selected₁ selected₂ =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F₁′ F₂′ : Expr.Frame* (2 *ℕ n)
  F₁′ = swapPhi-frames x h F₁
  F₂′ = swapPhi-frames x h F₂

  redex₁ redex₂ : Soup.Thread n
  redex₁ =
    Term.K (Term.`select choice) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ]
  redex₂ =
    Term.K Term.`branch Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ]

  body₁ body₂ : Soup.Thread n
  body₁ = 𝓒[ Term.* × Soup.endpoint i side₁ × e₁′ ]
  body₂ = Term.`inj choice 𝓒[ Term.* × Soup.endpoint i side₂ × e₂′ ]

  body₁′ body₂′ : Soup.Thread n
  body₁′ = 𝓒[ Term.* × Soup.endpoint i side₁ × f e₁′ ]
  body₂′ = Term.`inj choice 𝓒[ Term.* × Soup.endpoint i side₂ × f e₂′ ]

  C′ : Soup.Config n m
  C′ = Soup.config cs (RUS.replaceTwo ts j (F₁ Expr.[ body₁ ]*) k (F₂ Expr.[ body₂ ]*))

  D′ : Soup.Config n m
  D′ = Soup.config csS (RUS.replaceTwo tsS j (F₁′ Expr.[ body₁′ ]*) k (F₂′ Expr.[ body₂′ ]*))

  selectedD₁ :
    lookup tsS j ≡
    F₁′ Expr.[ Term.K (Term.`select choice) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × f e₁′ ] ]*
  selectedD₁ =
    V.lookup-map j f ts
    ■ cong f selected₁
    ■ swapPhi-plug* x h F₁ redex₁

  selectedD₂ :
    lookup tsS k ≡
    F₂′ Expr.[ Term.K Term.`branch Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × f e₂′ ] ]*
  selectedD₂ =
    V.lookup-map k f ts
    ■ cong f selected₂
    ■ swapPhi-plug* x h F₂ redex₂

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Choice j k i side₁ side₂ F₁′ F₂′ choice
      j≢k opposite (is-open-swap cs r swapSide h i live)
      selectedD₁ selectedD₂

  base :
    C′ ≈¹
    Soup.config csS
      (V.map f (RUS.replaceTwo ts j (F₁ Expr.[ body₁ ]*) k (F₂ Expr.[ body₂ ]*)))
  base = swap cs (RUS.replaceTwo ts j (F₁ Expr.[ body₁ ]*) k (F₂ Expr.[ body₂ ]*))
    r swapSide h lt

  repl₁Eq : f (F₁ Expr.[ body₁ ]*) ≡ F₁′ Expr.[ body₁′ ]*
  repl₁Eq = swapPhi-plug* x h F₁ body₁

  repl₂Eq : f (F₂ Expr.[ body₂ ]*) ≡ F₂′ Expr.[ body₂′ ]*
  repl₂Eq = swapPhi-plug* x h F₂ body₂

  targetThreadsEq :
    V.map f (RUS.replaceTwo ts j (F₁ Expr.[ body₁ ]*) k (F₂ Expr.[ body₂ ]*)) ≡
    RUS.replaceTwo tsS j (F₁′ Expr.[ body₁′ ]*) k (F₂′ Expr.[ body₂′ ]*)
  targetThreadsEq =
    map-replaceTwo f ts j k (F₁ Expr.[ body₁ ]*) (F₂ Expr.[ body₂ ]*)
    ■ cong₂
        (λ a b → RUS.replaceTwo tsS j a k b)
        repl₁Eq repl₂Eq

  targetEq :
    Soup.config csS
      (V.map f (RUS.replaceTwo ts j (F₁ Expr.[ body₁ ]*) k (F₂ Expr.[ body₂ ]*))) ≡
    D′
  targetEq = cong (Soup.config csS) targetThreadsEq

drop-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : Expr.Frame* (2 *ℕ n)) (before after : List Soup.Flag) →
  RUS.is-open cs i →
  RUS.endpointFlags (lookup cs i) side ≡ before ++ Soup.drop ∷ after →
  lookup ts j ≡
    F Expr.[ Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side ×
         Term.`phi (Soup.endpoint i side , L.length before) ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config
      (V.updateAt cs i
        (RUS.setEndpointFlags side (before ++ Soup.acq ∷ after)))
      (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≈ˢ D′
drop-equiv {n = n} {m = m} cs ts r swapSide h lt j i side F before after
  live flags selected with r FinP.≟ i
... | no apart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  setC : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side (before ++ Soup.acq ∷ after)

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setC

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × y × Term.`phi (y , L.length before) ]

  redexD : Soup.Thread n
  redexD = redex

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ Soup.drop ∷ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt′ i r (apart ∘ sym) cs)
    ■ flags

  redexEq : f redex ≡ redexD
  redexEq =
    cong
      (λ z →
        Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
          𝓒[ Term.* × y × z ])
      (swapPhi-miss (endpoint-apart-channel apart) h (L.length before))

  selectedD : lookup tsS j ≡ F′ Expr.[ redexD ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Drop j i side F′ before after
      (is-open-swap cs r swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels r) swapSide ≡
    RUS.endpointFlags (lookup cs r) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt′ r i apart cs)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels r) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)))
  base = swap sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))
    r swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels r (swapFlags swapSide h) ≡ targetChannels
  channelsEq = V.updateAt-commutes r i apart cs

  threadsEq :
    V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≡
    RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*)
  threadsEq =
    map-replaceAt f ts j (F Expr.[ Term.* ]*)
    ■ cong (λ t → RUS.replaceAt tsS j t)
        (swapPhi-plug* x h F Term.*)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*))) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

... | yes refl with swapSide FinP.≟ side
...   | no sideApart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  setC : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side (before ++ Soup.acq ∷ after)

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags swapSide h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setC

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × y × Term.`phi (y , L.length before) ]

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ Soup.drop ∷ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-swapFlags-miss swapSide side h (lookup cs i) sideApart
    ■ flags

  redexEq : f redex ≡ redex
  redexEq =
    cong
      (λ z →
        Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
          𝓒[ Term.* × y × z ])
      (swapPhi-miss (endpoint-apart-side i sideApart) h (L.length before))

  selectedD : lookup tsS j ≡ F′ Expr.[ redex ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Drop j i side F′ before after
      (is-open-swap cs i swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels i) swapSide ≡
    RUS.endpointFlags (lookup cs i) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-setEndpointFlags-miss side swapSide
        (before ++ Soup.acq ∷ after) (lookup cs i) (sideApart ∘ sym)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels i) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)))
  base = swap sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))
    i swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels i (swapFlags swapSide h) ≡ targetChannels
  channelsEq =
    V.updateAt-updateAt i cs
    ■ sym
        (V.updateAt-updateAt-local i cs
          (setEndpointFlags-swapFlags-miss-commute swapSide side h
            (before ++ Soup.acq ∷ after) (lookup cs i) sideApart))

  threadsEq :
    V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≡
    RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*)
  threadsEq =
    map-replaceAt f ts j (F Expr.[ Term.* ]*)
    ■ cong (λ t → RUS.replaceAt tsS j t)
        (swapPhi-plug* x h F Term.*)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*))) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

...   | yes refl with
        swapAt-select₂ h before after Soup.drop Soup.acq
          (subst (suc h Nat.<_) (cong L.length flags) lt)
...     | before′ , after′ , dropSwapped , acqSwapped , lenEq =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  setC setD : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side (before ++ Soup.acq ∷ after)
  setD = RUS.setEndpointFlags side (before′ ++ Soup.acq ∷ after′)

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags side h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setD

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  redex : Soup.Thread n
  redex =
    Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × x × Term.`phi (x , L.length before) ]

  redexD : Soup.Thread n
  redexD =
    Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × x × Term.`phi (x , L.length before′) ]

  C′ : Soup.Config n m
  C′ = Soup.config sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))

  D′ : Soup.Config n m
  D′ = Soup.config targetChannels (RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*))

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before′ ++ Soup.drop ∷ after′
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt i cs)
    ■ BorrowedCF.Simulation.BackwardSoup.Statement.endpointFlags-swapFlags
        side h (lookup cs i)
    ■ cong (swapAt h) flags
    ■ dropSwapped

  redexEq : f redex ≡ redexD
  redexEq =
    cong
      (λ z →
        Term.K Term.`drop Term.·⟨ Types.𝟙 ⟩ 𝓒[ Term.* × x × z ])
      (swapPhi-hit x h (L.length before)
       ■ cong (λ l → Term.`phi (x , l)) (sym lenEq))

  selectedD : lookup tsS j ≡ F′ Expr.[ redexD ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Drop j i side F′ before′ after′
      (is-open-swap cs i side h i live)
      flagsD selectedD

  endpointEq :
    L.length (RUS.endpointFlags (lookup sourceChannels i) side) ≡
    L.length (RUS.endpointFlags (lookup cs i) side)
  endpointEq =
    cong L.length
      (cong (λ ch → RUS.endpointFlags ch side)
        (V.lookup∘updateAt i cs)
       ■ endpointFlags-setEndpointFlags side
           (before ++ Soup.acq ∷ after) (lookup cs i))
    ■ sym (replace-flag-length before after Soup.drop Soup.acq)
    ■ cong L.length (sym flags)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels i) side)
  lt′ = subst (suc h Nat.<_) (sym endpointEq) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels i (swapFlags side h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)))
  base = swap sourceChannels (RUS.replaceAt ts j (F Expr.[ Term.* ]*))
    i side h lt′

  channelsEq :
    V.updateAt sourceChannels i (swapFlags side h) ≡ targetChannels
  channelsEq =
    V.updateAt-updateAt i cs
    ■ sym
        (V.updateAt-updateAt-local i cs
          (setEndpointFlags-swapFlags-hit-replace side h
            (before ++ Soup.acq ∷ after)
            (before′ ++ Soup.acq ∷ after′)
            (lookup cs i) acqSwapped))

  threadsEq :
    V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*)) ≡
    RUS.replaceAt tsS j (F′ Expr.[ Term.* ]*)
  threadsEq =
    map-replaceAt f ts j (F Expr.[ Term.* ]*)
    ■ cong (λ t → RUS.replaceAt tsS j t)
        (swapPhi-plug* x h F Term.*)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels i (swapFlags side h))
      (V.map f (RUS.replaceAt ts j (F Expr.[ Term.* ]*))) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

acquire-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j : 𝔽 m) (i : 𝔽 n) (side : 𝔽 2)
  (F : Expr.Frame* (2 *ℕ n)) (before after : List Soup.Flag)
  {e : Soup.Thread n} →
  RUS.is-open cs i →
  RUS.endpointFlags (lookup cs i) side ≡ before ++ Soup.acq ∷ after →
  lookup ts j ≡
    F Expr.[ Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (Soup.endpoint i side , L.length before) ×
         Soup.endpoint i side × e ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config
      (V.updateAt cs i (RUS.setEndpointFlags side (before ++ after)))
      (let x = Soup.endpoint i side
           k = L.length before
       in RUS.replaceAt (V.map (RUS.consumePhi x k) ts) j
            (RUS.consumePhi x k (F Expr.[ 𝓒[ Term.* × x × e ] ]*)))
      ≈ˢ D′
acquire-equiv {n = n} {m = m} cs ts r swapSide h lt
  j i side F before after {e} live flags selected with r FinP.≟ i
... | no apart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  slot : ℕ
  slot = L.length before

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  consume : Soup.Thread n → Soup.Thread n
  consume = RUS.consumePhi y slot

  setC : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side (before ++ after)

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setC

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  sourceThreads targetThreads : Vec (Soup.Thread n) m
  sourceThreads =
    RUS.replaceAt (V.map consume ts) j
      (consume (F Expr.[ 𝓒[ Term.* × y × e ] ]*))
  targetThreads =
    RUS.replaceAt (V.map consume tsS) j
      (consume (F′ Expr.[ 𝓒[ Term.* × y × f e ] ]*))

  redex : Soup.Thread n
  redex =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (y , slot) × y × e ]

  redexD : Soup.Thread n
  redexD =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (y , slot) × y × f e ]

  C′ D′ : Soup.Config n m
  C′ = Soup.config sourceChannels sourceThreads
  D′ = Soup.config targetChannels targetThreads

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ Soup.acq ∷ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.lookup∘updateAt′ i r (apart ∘ sym) cs)
    ■ flags

  endpointApart : x ≢ y
  endpointApart = endpoint-apart-channel apart

  redexEq : f redex ≡ redexD
  redexEq =
    cong
      (λ z →
        Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
          𝓒[ z × y × f e ])
      (swapPhi-miss endpointApart h slot)

  selectedD : lookup tsS j ≡ F′ Expr.[ redexD ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Acquire j i side F′ before after
      (is-open-swap cs r swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels r) swapSide ≡
    RUS.endpointFlags (lookup cs r) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt′ r i apart cs)

  lt′ :
    suc h Nat.<
    L.length (RUS.endpointFlags (lookup sourceChannels r) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f sourceThreads)
  base = swap sourceChannels sourceThreads r swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels r (swapFlags swapSide h) ≡ targetChannels
  channelsEq = V.updateAt-commutes r i apart cs

  threadsEq : V.map f sourceThreads ≡ targetThreads
  threadsEq =
    acquire-threads-miss {n = n} {m = m}
      endpointApart h slot ts j F e

  targetEq :
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f sourceThreads) ≡ D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

... | yes refl with swapSide FinP.≟ side
...   | no sideApart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i swapSide

  y : 𝔽 (2 *ℕ n)
  y = Soup.endpoint i side

  slot : ℕ
  slot = L.length before

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  consume : Soup.Thread n → Soup.Thread n
  consume = RUS.consumePhi y slot

  setC : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side (before ++ after)

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags swapSide h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setC

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  sourceThreads targetThreads : Vec (Soup.Thread n) m
  sourceThreads =
    RUS.replaceAt (V.map consume ts) j
      (consume (F Expr.[ 𝓒[ Term.* × y × e ] ]*))
  targetThreads =
    RUS.replaceAt (V.map consume tsS) j
      (consume (F′ Expr.[ 𝓒[ Term.* × y × f e ] ]*))

  redex : Soup.Thread n
  redex =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (y , slot) × y × e ]

  redexD : Soup.Thread n
  redexD =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (y , slot) × y × f e ]

  C′ D′ : Soup.Config n m
  C′ = Soup.config sourceChannels sourceThreads
  D′ = Soup.config targetChannels targetThreads

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡ before ++ Soup.acq ∷ after
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side) (V.lookup∘updateAt i cs)
    ■ endpointFlags-swapFlags-miss swapSide side h (lookup cs i) sideApart
    ■ flags

  endpointApart : x ≢ y
  endpointApart = endpoint-apart-side i sideApart

  redexEq : f redex ≡ redexD
  redexEq =
    cong
      (λ z →
        Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
          𝓒[ z × y × f e ])
      (swapPhi-miss endpointApart h slot)

  selectedD : lookup tsS j ≡ F′ Expr.[ redexD ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Acquire j i side F′ before after
      (is-open-swap cs i swapSide h i live)
      flagsD selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels i) swapSide ≡
    RUS.endpointFlags (lookup cs i) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt i cs)
    ■ endpointFlags-setEndpointFlags-miss side swapSide
        (before ++ after) (lookup cs i) (sideApart ∘ sym)

  lt′ :
    suc h Nat.<
    L.length (RUS.endpointFlags (lookup sourceChannels i) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f sourceThreads)
  base = swap sourceChannels sourceThreads i swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels i (swapFlags swapSide h) ≡ targetChannels
  channelsEq =
    V.updateAt-updateAt i cs
    ■ sym
        (V.updateAt-updateAt-local i cs
          (setEndpointFlags-swapFlags-miss-commute swapSide side h
            (before ++ after) (lookup cs i) sideApart))

  threadsEq : V.map f sourceThreads ≡ targetThreads
  threadsEq =
    acquire-threads-miss {n = n} {m = m}
      endpointApart h slot ts j F e

  targetEq :
    Soup.config
      (V.updateAt sourceChannels i (swapFlags swapSide h))
      (V.map f sourceThreads) ≡ D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

...   | yes refl with
        residualSwap h (L.length before) in resEq
      | swapAt-remove-select h before after Soup.acq
          (subst (suc h Nat.<_) (cong L.length flags) lt)
...     | res | before′ , after′ , swapped , removed , lenEq , bound =
  D′ , stepD , subst (C′ ≈ˢ_) targetEq base
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint i side

  sourceSlot targetSlot : ℕ
  sourceSlot = L.length before
  targetSlot = L.length before′

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  consumeC consumeD : Soup.Thread n → Soup.Thread n
  consumeC = RUS.consumePhi x sourceSlot
  consumeD = RUS.consumePhi x targetSlot

  sourceFlags targetFlags : List Soup.Flag
  sourceFlags = before ++ after
  targetFlags = before′ ++ after′

  setC setD : Soup.Channel → Soup.Channel
  setC = RUS.setEndpointFlags side sourceFlags
  setD = RUS.setEndpointFlags side targetFlags

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs i (swapFlags side h)
  sourceChannels = V.updateAt cs i setC
  targetChannels = V.updateAt csS i setD

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  sourceThreads targetThreads : Vec (Soup.Thread n) m
  sourceThreads =
    RUS.replaceAt (V.map consumeC ts) j
      (consumeC (F Expr.[ 𝓒[ Term.* × x × e ] ]*))
  targetThreads =
    RUS.replaceAt (V.map consumeD tsS) j
      (consumeD (F′ Expr.[ 𝓒[ Term.* × x × f e ] ]*))

  redex redexD : Soup.Thread n
  redex =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (x , sourceSlot) × x × e ]
  redexD =
    Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.`phi (x , targetSlot) × x × f e ]

  C′ D′ residualConfig : Soup.Config n m
  C′ = Soup.config sourceChannels sourceThreads
  D′ = Soup.config targetChannels targetThreads
  residualConfig =
    Soup.config (applyResidualChannels i side res sourceChannels)
      (V.map (applyResidualPhi x res) sourceThreads)

  removedRes : targetFlags ≡ applyResidualFlags res sourceFlags
  removedRes = removed

  boundRes : ResidualBound res sourceFlags
  boundRes = bound

  flagsD :
    RUS.endpointFlags (lookup csS i) side ≡
    before′ ++ Soup.acq ∷ after′
  flagsD =
    cong (λ ch → RUS.endpointFlags ch side) (V.lookup∘updateAt i cs)
    ■ BorrowedCF.Simulation.BackwardSoup.Statement.endpointFlags-swapFlags
        side h (lookup cs i)
    ■ cong (swapAt h) flags
    ■ swapped

  redexEq : f redex ≡ redexD
  redexEq =
    cong
      (λ z →
        Term.K Term.`acq Term.·⟨ Types.𝟙 ⟩
          𝓒[ z × x × f e ])
      (swapPhi-hit x h sourceSlot
       ■ cong (λ l → Term.`phi (x , l)) (sym lenEq))

  selectedD : lookup tsS j ≡ F′ Expr.[ redexD ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex
    ■ cong (F′ Expr.[_]*) redexEq

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Acquire j i side F′ before′ after′
      (is-open-swap cs i side h i live)
      flagsD selectedD

  sourceEndpointEq :
    sourceFlags ≡ RUS.endpointFlags (lookup sourceChannels i) side
  sourceEndpointEq =
    sym
      (cong (λ ch → RUS.endpointFlags ch side) (V.lookup∘updateAt i cs)
      ■ endpointFlags-setEndpointFlags side sourceFlags (lookup cs i))

  boundSource :
    ResidualBound res
      (RUS.endpointFlags (lookup sourceChannels i) side)
  boundSource = residual-bound-cong sourceEndpointEq boundRes

  base : C′ ≈ˢ residualConfig
  base = residual-config-related sourceChannels sourceThreads i side res boundSource

  channelsEq :
    applyResidualChannels i side res sourceChannels ≡ targetChannels
  channelsEq =
    acquire-residual-channels
      cs i side h res sourceFlags targetFlags removedRes

  threadsEq :
    V.map (applyResidualPhi x res) sourceThreads ≡ targetThreads
  threadsEq =
    acquire-threads-hit {n = n} {m = m}
      x h sourceSlot targetSlot res resEq lenEq ts j F e

  targetEq : residualConfig ≡ D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

close-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (swapSide : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) swapSide))
  (j k : 𝔽 m) (i : 𝔽 n) (side₁ side₂ : 𝔽 2)
  (F₁ F₂ : Expr.Frame* (2 *ℕ n)) →
  j ≢ k →
  RUS.Opposite side₁ side₂ →
  lookup cs i ≡ (true , [] , []) →
  lookup ts j ≡
    F₁ Expr.[ Term.K (Term.`end Types.‼) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × Term.* ] ]* →
  lookup ts k ≡
    F₂ Expr.[ Term.K (Term.`end Types.⁇) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × Term.* ] ]* →
  Σ[ D′ ∈ Soup.Config n m ]
    (Soup.config (V.updateAt cs r (swapFlags swapSide h))
      (V.map (swapPhi (Soup.endpoint r swapSide) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config (RUS.replaceAt cs i (false , [] , []))
      (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*))
      ≈ˢ D′
close-equiv {n = n} {m = m} cs ts r swapSide h lt
  j k i side₁ side₂ F₁ F₂ j≢k opposite empty selected₁ selected₂
  with r FinP.≟ i
... | yes refl = ⊥-elim bad
  where
  bad : ⊥
  bad =
    empty-open-slot-impossible swapSide h
      (subst (λ ch → suc h Nat.< L.length (RUS.endpointFlags ch swapSide))
        empty lt)
... | no apart =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r swapSide

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  csS sourceChannels targetChannels : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags swapSide h)
  sourceChannels = RUS.replaceAt cs i (false , [] , [])
  targetChannels = RUS.replaceAt csS i (false , [] , [])

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F₁′ F₂′ : Expr.Frame* (2 *ℕ n)
  F₁′ = swapPhi-frames x h F₁
  F₂′ = swapPhi-frames x h F₂

  redex₁ redex₂ : Soup.Thread n
  redex₁ =
    Term.K (Term.`end Types.‼) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × Term.* ]
  redex₂ =
    Term.K (Term.`end Types.⁇) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × Term.* ]

  C′ : Soup.Config n m
  C′ =
    Soup.config sourceChannels
      (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*))

  D′ : Soup.Config n m
  D′ =
    Soup.config targetChannels
      (RUS.replaceTwo tsS j (F₁′ Expr.[ Term.* ]*) k (F₂′ Expr.[ Term.* ]*))

  selectedD₁ :
    lookup tsS j ≡
    F₁′ Expr.[ Term.K (Term.`end Types.‼) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₁ × Term.* ] ]*
  selectedD₁ =
    V.lookup-map j f ts
    ■ cong f selected₁
    ■ swapPhi-plug* x h F₁ redex₁

  selectedD₂ :
    lookup tsS k ≡
    F₂′ Expr.[ Term.K (Term.`end Types.⁇) Term.·⟨ Types.𝟙 ⟩
      𝓒[ Term.* × Soup.endpoint i side₂ × Term.* ] ]*
  selectedD₂ =
    V.lookup-map k f ts
    ■ cong f selected₂
    ■ swapPhi-plug* x h F₂ redex₂

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD =
    RUS.RUS-Close j k i side₁ side₂ F₁′ F₂′
      j≢k opposite
      (empty-open-channel-swap cs r swapSide h i lt empty)
      selectedD₁ selectedD₂

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels r) swapSide ≡
    RUS.endpointFlags (lookup cs r) swapSide
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch swapSide)
      (V.lookup∘updateAt′ r i apart cs)

  lt′ : suc h Nat.< L.length (RUS.endpointFlags (lookup sourceChannels r) swapSide)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f
        (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*)))
  base =
    swap sourceChannels
      (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*))
      r swapSide h lt′

  channelsEq :
    V.updateAt sourceChannels r (swapFlags swapSide h) ≡ targetChannels
  channelsEq = V.updateAt-commutes r i apart cs

  repl₁Eq : f (F₁ Expr.[ Term.* ]*) ≡ F₁′ Expr.[ Term.* ]*
  repl₁Eq = swapPhi-plug* x h F₁ Term.*

  repl₂Eq : f (F₂ Expr.[ Term.* ]*) ≡ F₂′ Expr.[ Term.* ]*
  repl₂Eq = swapPhi-plug* x h F₂ Term.*

  threadsEq :
    V.map f
      (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*)) ≡
    RUS.replaceTwo tsS j (F₁′ Expr.[ Term.* ]*) k (F₂′ Expr.[ Term.* ]*)
  threadsEq =
    map-replaceTwo f ts j k (F₁ Expr.[ Term.* ]*) (F₂ Expr.[ Term.* ]*)
    ■ cong₂ (λ a b → RUS.replaceTwo tsS j a k b) repl₁Eq repl₂Eq

  targetEq :
    Soup.config
      (V.updateAt sourceChannels r (swapFlags swapSide h))
      (V.map f
        (RUS.replaceTwo ts j (F₁ Expr.[ Term.* ]*) k (F₂ Expr.[ Term.* ]*))) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

new-equiv :
  {n m : ℕ}
  (cs : Vec Soup.Channel n) (ts : Vec (Soup.Thread n) m)
  (r : 𝔽 n) (side : 𝔽 2) (h : ℕ)
  (lt : suc h Nat.< L.length (RUS.endpointFlags (lookup cs r) side))
  (j : 𝔽 m) (i : 𝔽 (suc n))
  (F : Expr.Frame* (2 *ℕ n)) {s : Types.𝕊 0} →
  lookup ts j ≡
    F Expr.[ Term.K (Term.`new s) Term.·⟨ Types.𝟙 ⟩ Term.* ]* →
  Σ[ D′ ∈ Soup.Config (suc n) m ]
    (Soup.config (V.updateAt cs r (swapFlags side h))
      (V.map (swapPhi (Soup.endpoint r side) h) ts)
      RUS.─→ₚ D′) ×
    Soup.config
      (V.insertAt cs i (true , Soup.acq ∷ [] , Soup.acq ∷ []))
      (RUS.replaceAt (V.map (RUS.insertThreadEndpoints i) ts)
        j (RUS.newResult i F)) ≈ˢ D′
new-equiv {n = n} {m = m} cs ts r side h lt j i F {s = s} selected =
  D′ , stepD , ≈¹⇒≈ˢ (subst (C′ ≈¹_) targetEq base)
  where
  x : 𝔽 (2 *ℕ n)
  x = Soup.endpoint r side

  y : 𝔽 (2 *ℕ suc n)
  y = Soup.endpoint (Fin.punchIn i r) side

  f : Soup.Thread n → Soup.Thread n
  f = swapPhi x h

  g : Soup.Thread (suc n) → Soup.Thread (suc n)
  g = swapPhi y h

  rhoT : Soup.Thread n → Soup.Thread (suc n)
  rhoT = RUS.insertThreadEndpoints i

  rhoTf : Soup.Thread n → Soup.Thread (suc n)
  rhoTf t = rhoT (f t)

  fresh : Soup.Channel
  fresh = true , Soup.acq ∷ [] , Soup.acq ∷ []

  csS : Vec Soup.Channel n
  csS = V.updateAt cs r (swapFlags side h)

  sourceChannels : Vec Soup.Channel (suc n)
  sourceChannels = V.insertAt cs i fresh

  targetChannels : Vec Soup.Channel (suc n)
  targetChannels = V.insertAt csS i fresh

  tsS : Vec (Soup.Thread n) m
  tsS = V.map f ts

  F′ : Expr.Frame* (2 *ℕ n)
  F′ = swapPhi-frames x h F

  sourceThreads : Vec (Soup.Thread (suc n)) m
  sourceThreads = RUS.replaceAt (V.map rhoT ts) j (RUS.newResult i F)

  targetThreads : Vec (Soup.Thread (suc n)) m
  targetThreads = RUS.replaceAt (V.map rhoT tsS) j (RUS.newResult i F′)

  redex : Soup.Thread n
  redex = Term.K (Term.`new s) Term.·⟨ Types.𝟙 ⟩ Term.*

  C′ : Soup.Config (suc n) m
  C′ = Soup.config sourceChannels sourceThreads

  D′ : Soup.Config (suc n) m
  D′ = Soup.config targetChannels targetThreads

  selectedD :
    lookup tsS j ≡
    F′ Expr.[ Term.K (Term.`new s) Term.·⟨ Types.𝟙 ⟩ Term.* ]*
  selectedD =
    V.lookup-map j f ts
    ■ cong f selected
    ■ swapPhi-plug* x h F redex

  stepD : Soup.config csS tsS RUS.─→ₚ D′
  stepD = RUS.RUS-New j i F′ selectedD

  endpointEq :
    RUS.endpointFlags (lookup sourceChannels (Fin.punchIn i r)) side ≡
    RUS.endpointFlags (lookup cs r) side
  endpointEq =
    cong (λ ch → RUS.endpointFlags ch side)
      (V.insertAt-punchIn cs i fresh r)

  lt′ :
    suc h Nat.<
    L.length (RUS.endpointFlags (lookup sourceChannels (Fin.punchIn i r)) side)
  lt′ = subst (suc h Nat.<_) (sym (cong L.length endpointEq)) lt

  base :
    C′ ≈¹
    Soup.config
      (V.updateAt sourceChannels (Fin.punchIn i r) (swapFlags side h))
      (V.map g sourceThreads)
  base = swap sourceChannels sourceThreads (Fin.punchIn i r) side h lt′

  channelsEq :
    V.updateAt sourceChannels (Fin.punchIn i r) (swapFlags side h) ≡
    targetChannels
  channelsEq = updateAt-insertAt-punchIn cs i r (swapFlags side h) fresh

  threadsEq : V.map g sourceThreads ≡ targetThreads
  threadsEq =
    map-replaceAt-map₂ g rhoT rhoTf ts j
      (RUS.newResult i F) (RUS.newResult i F′)
      (swapPhi-insertThreadEndpoints i r side h)
      (swapPhi-newResult i r side h F)
    ■ cong (λ ys → RUS.replaceAt ys j (RUS.newResult i F′))
        (V.map-∘ rhoT f ts)

  targetEq :
    Soup.config
      (V.updateAt sourceChannels (Fin.punchIn i r) (swapFlags side h))
      (V.map g sourceThreads) ≡
    D′
  targetEq = cong₂ Soup.config channelsEq threadsEq

------------------------------------------------------------------------
-- Dispatcher and closure lift.

one-bisim : One-Bisim
one-bisim (swap cs ts r side h lt) (RUS.RUS-Exp j red) =
  exp-equiv cs ts r side h lt j red
one-bisim (swap cs ts r side h lt) (RUS.RUS-Fork j F Ve selected) =
  fork-equiv cs ts r side h lt j F Ve selected
one-bisim (swap cs ts r side h lt) (RUS.RUS-New j i F selected) =
  new-equiv cs ts r side h lt j i F selected
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-LSplit j i side F live selected) =
  lsplit-equiv cs ts r swapSide h lt j i side F live selected
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-RSplit j i side F before after live flags selected) =
  rsplit-equiv cs ts r swapSide h lt
    j i side F before after live flags selected
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-Drop j i side F before after live flags selected) =
  drop-equiv cs ts r swapSide h lt
    j i side F before after live flags selected
one-bisim (swap cs ts r side h lt) (RUS.RUS-Discard j F Ve selected) =
  discard-equiv cs ts r side h lt j F Ve selected
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-Acquire j i side F before after live flags selected) =
  acquire-equiv cs ts r swapSide h lt
    j i side F before after live flags selected
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-Close j k i side₁ side₂ F₁ F₂
    apart opposite channel selected₁ selected₂) =
  close-equiv cs ts r swapSide h lt
    j k i side₁ side₂ F₁ F₂
    apart opposite channel selected₁ selected₂
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-Com j k i side₁ side₂ F₁ F₂
    apart opposite live Ve selected₁ selected₂) =
  com-equiv cs ts r swapSide h lt
    j k i side₁ side₂ F₁ F₂
    apart opposite live Ve selected₁ selected₂
one-bisim (swap cs ts r swapSide h lt)
  (RUS.RUS-Choice j k i side₁ side₂ F₁ F₂ choice
    apart opposite live selected₁ selected₂) =
  choice-equiv cs ts r swapSide h lt
    j k i side₁ side₂ F₁ F₂ choice
    apart opposite live selected₁ selected₂

slot-bisim : Slot-Bisim
slot-bisim ε red = _ , red , ≈ˢ-refl
slot-bisim (fwd one ◅ rest) red
  with one-bisim one red
... | C₁′ , red₁ , related₁
  with slot-bisim rest red₁
... | D′ , redD , relatedD =
  D′ , redD , ≈ˢ-trans related₁ relatedD
slot-bisim (bwd one ◅ rest) red
  with one-bisim (≈¹-sym one) red
... | C₁′ , red₁ , related₁
  with slot-bisim rest red₁
... | D′ , redD , relatedD =
  D′ , redD , ≈ˢ-trans related₁ relatedD
