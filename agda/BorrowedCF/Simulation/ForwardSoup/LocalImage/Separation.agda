-- Phi-separation for the soup forward simulation.
--
-- `RUS-Acquire` rewrites *every* thread of the configuration with
-- `consumePhi x k`.  The simulation therefore needs an invariant saying that
-- the threads and the environment which the local view does not own mention
-- `phi` only on channels that the local view does not own either.  This
-- module defines that invariant (`PhiFreeFor`, `Separated`) and proves the
-- scoping lemma (`flatten-phiFree`) which says that the translation creates
-- `phi` cells only on the endpoints of its own channel vector, or inherits
-- them from its environment.
module BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation where

open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Nat.ListAction using (sum)

import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.Expressions using (T[_]-Env-cong)

open Nat.Variables
open Fin.Patterns

private
  variable
    a b : ℕ
    A : Set

------------------------------------------------------------------------
-- Generic vector plumbing

lookup-++-cases :
  {p q : ℕ} (xs : Vec A p) (ys : Vec A q) (Pr : A → Set) →
  (∀ i → Pr (lookup xs i)) → (∀ i → Pr (lookup ys i)) →
  ∀ j → Pr (lookup (xs V.++ ys) j)
lookup-++-cases [] ys Pr hx hy j = hy j
lookup-++-cases (x ∷ xs) ys Pr hx hy zero = hx zero
lookup-++-cases (x ∷ xs) ys Pr hx hy (suc j) =
  lookup-++-cases xs ys Pr (λ i → hx (suc i)) hy j

lookup-take-cases :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) (Pr : A → Set) →
  (∀ i → Pr (lookup xs i)) →
  ∀ i → Pr (lookup (V.take p xs) i)
lookup-take-cases (suc p) (x ∷ xs) Pr h zero = h zero
lookup-take-cases (suc p) (x ∷ xs) Pr h (suc i) =
  lookup-take-cases p xs Pr (λ l → h (suc l)) i

lookup-drop-cases :
  (p : ℕ) {q : ℕ} (xs : Vec A (p + q)) (Pr : A → Set) →
  (∀ i → Pr (lookup xs i)) →
  ∀ i → Pr (lookup (V.drop p xs) i)
lookup-drop-cases zero xs Pr h i = h i
lookup-drop-cases (suc p) (x ∷ xs) Pr h i =
  lookup-drop-cases p xs Pr (λ l → h (suc l)) i

------------------------------------------------------------------------
-- Distinct channels have distinct endpoints

cast-injective :
  ∀ {p q} .(eq : p ≡ q) {i j : 𝔽 p} →
  Fin.cast eq i ≡ Fin.cast eq j → i ≡ j
cast-injective eq {i} {j} equal =
  sym (Fin.cast-involutive (sym eq) eq i) ■
  cong (Fin.cast (sym eq)) equal ■
  Fin.cast-involutive (sym eq) eq j

-- `endpoint` is `cast ∘ combine`, so it determines the channel it belongs to.
endpoint-channel-injective :
  ∀ {i i′ : 𝔽 n} {s s′ : 𝔽 2} →
  Soup.endpoint i s ≡ Soup.endpoint i′ s′ → i ≡ i′
endpoint-channel-injective {i = i} {i′ = i′} {s = s} {s′ = s′} equal =
  Fin.combine-injectiveˡ i s i′ s′ (cast-injective _ equal)

------------------------------------------------------------------------
-- `consumePhi` commutes with injective renamings

liftRen-injective :
  {ρ : 𝔽 a → 𝔽 b} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  ∀ {x y} → SoupTerm.liftRen ρ x ≡ SoupTerm.liftRen ρ y → x ≡ y
liftRen-injective inj {zero} {zero} equal = refl
liftRen-injective inj {zero} {suc y} ()
liftRen-injective inj {suc x} {zero} ()
liftRen-injective inj {suc x} {suc y} equal =
  cong suc (inj (Fin.suc-injective equal))

consumePhi-ren :
  {ρ : 𝔽 a → 𝔽 b} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  (x : 𝔽 a) (k : ℕ) (t : SoupTerm.Tm a) →
  SoupReduction.consumePhi (ρ x) k (t SoupTerm.⋯ᵣ ρ) ≡
  SoupReduction.consumePhi x k t SoupTerm.⋯ᵣ ρ
consumePhi-ren inj x k (SoupTerm.` y) = refl
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.`phi (y , l))
  with x FinP.≟ y | ρ x FinP.≟ ρ y
... | no ¬same | no ¬same′ = refl
... | no ¬same | yes same′ = ⊥-elim (¬same (inj same′))
... | yes refl | no ¬same′ = ⊥-elim (¬same′ refl)
... | yes refl | yes refl with k NatP.≟ l
...   | no ¬slot = refl
...   | yes refl = refl
consumePhi-ren inj x k (SoupTerm.K c) = refl
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.ƛ t) =
  cong SoupTerm.ƛ
    (consumePhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj) (suc x) k t)
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.μ t) =
  cong SoupTerm.μ
    (consumePhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj) (suc x) k t)
consumePhi-ren inj x k (t₁ SoupTerm.·⟨ d ⟩ t₂) =
  cong₂ (SoupTerm._·⟨ d ⟩_)
    (consumePhi-ren inj x k t₁) (consumePhi-ren inj x k t₂)
consumePhi-ren inj x k (t₁ SoupTerm.; t₂) =
  cong₂ SoupTerm._;_
    (consumePhi-ren inj x k t₁) (consumePhi-ren inj x k t₂)
consumePhi-ren inj x k (t₁ SoupTerm.⊗ t₂) =
  cong₂ SoupTerm._⊗_
    (consumePhi-ren inj x k t₁) (consumePhi-ren inj x k t₂)
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.`let t₁ `in t₂) =
  cong₂ SoupTerm.`let_`in_
    (consumePhi-ren inj x k t₁)
    (consumePhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj) (suc x) k t₂)
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.`let⊗ t₁ `in t₂) =
  cong₂ SoupTerm.`let⊗_`in_
    (consumePhi-ren inj x k t₁)
    (consumePhi-ren {ρ = SoupTerm.liftRen (SoupTerm.liftRen ρ)}
      (liftRen-injective (liftRen-injective inj)) (suc (suc x)) k t₂)
consumePhi-ren inj x k (SoupTerm.`inj i t) =
  cong (SoupTerm.`inj i) (consumePhi-ren inj x k t)
consumePhi-ren {ρ = ρ} inj x k (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₂ (λ u us → SoupTerm.`case u `of⟨ proj₁ us ; proj₂ us ⟩)
    (consumePhi-ren inj x k t)
    (cong₂ _,_
      (consumePhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj) (suc x) k t₁)
      (consumePhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj) (suc x) k t₂))

consumePhi-wk :
  (x : 𝔽 a) (k : ℕ) (t : SoupTerm.Tm a) →
  SoupReduction.consumePhi (suc x) k (SoupTerm.wk t) ≡
  SoupTerm.wk (SoupReduction.consumePhi x k t)
consumePhi-wk = consumePhi-ren {ρ = Fin.suc} Fin.suc-injective

------------------------------------------------------------------------
-- `consumePhi` commutes with the expression translation

consumePhi-liftEnv :
  (x : 𝔽 b) (k : ℕ) (σ : Translation.Env a b) →
  ∀ y →
  SoupReduction.consumePhi (suc x) k (Translation.liftEnv σ y) ≡
  Translation.liftEnv (λ z → SoupReduction.consumePhi x k (σ z)) y
consumePhi-liftEnv x k σ zero = refl
consumePhi-liftEnv x k σ (suc y) = consumePhi-wk x k (σ y)

consumePhi-liftEnv₂ :
  (x : 𝔽 b) (k : ℕ) (σ : Translation.Env a b) →
  ∀ y →
  SoupReduction.consumePhi (suc (suc x)) k
    (Translation.liftEnv (Translation.liftEnv σ) y) ≡
  Translation.liftEnv
    (Translation.liftEnv (λ z → SoupReduction.consumePhi x k (σ z))) y
consumePhi-liftEnv₂ x k σ zero = refl
consumePhi-liftEnv₂ x k σ (suc y) =
  consumePhi-wk (suc x) k (Translation.liftEnv σ y) ■
  cong SoupTerm.wk (consumePhi-liftEnv x k σ y)

consumePhi-T :
  (x : 𝔽 b) (k : ℕ) (e : Source.Tm a) (σ : Translation.Env a b) →
  SoupReduction.consumePhi x k (Translation.T[ e ] σ) ≡
  Translation.T[ e ] (λ y → SoupReduction.consumePhi x k (σ y))
consumePhi-T x k (Source.` y) σ = refl
consumePhi-T x k (Source.K c) σ = refl
consumePhi-T x k (Source.ƛ e) σ =
  cong SoupTerm.ƛ
    (consumePhi-T (suc x) k e (Translation.liftEnv σ) ■
     T[_]-Env-cong e (consumePhi-liftEnv x k σ))
consumePhi-T x k (Source.μ e) σ =
  cong SoupTerm.μ
    (consumePhi-T (suc x) k e (Translation.liftEnv σ) ■
     T[_]-Env-cong e (consumePhi-liftEnv x k σ))
consumePhi-T x k (e₁ Source.·⟨ d ⟩ e₂) σ =
  cong₂ (SoupTerm._·⟨ d ⟩_) (consumePhi-T x k e₁ σ) (consumePhi-T x k e₂ σ)
consumePhi-T x k (e₁ Source.; e₂) σ =
  cong₂ SoupTerm._;_ (consumePhi-T x k e₁ σ) (consumePhi-T x k e₂ σ)
consumePhi-T x k (e₁ Source.⊗ e₂) σ =
  cong₂ SoupTerm._⊗_ (consumePhi-T x k e₁ σ) (consumePhi-T x k e₂ σ)
consumePhi-T x k (Source.`let e₁ `in e₂) σ =
  cong₂ SoupTerm.`let_`in_
    (consumePhi-T x k e₁ σ)
    (consumePhi-T (suc x) k e₂ (Translation.liftEnv σ) ■
     T[_]-Env-cong e₂ (consumePhi-liftEnv x k σ))
consumePhi-T x k (Source.`let⊗ e₁ `in e₂) σ =
  cong₂ SoupTerm.`let⊗_`in_
    (consumePhi-T x k e₁ σ)
    (consumePhi-T (suc (suc x)) k e₂
       (Translation.liftEnv (Translation.liftEnv σ)) ■
     T[_]-Env-cong e₂ (consumePhi-liftEnv₂ x k σ))
consumePhi-T x k (Source.`inj i e) σ =
  cong (SoupTerm.`inj i) (consumePhi-T x k e σ)
consumePhi-T x k (Source.`case e `of⟨ e₁ ; e₂ ⟩) σ =
  cong₂ (λ u us → SoupTerm.`case u `of⟨ proj₁ us ; proj₂ us ⟩)
    (consumePhi-T x k e σ)
    (cong₂ _,_
      (consumePhi-T (suc x) k e₁ (Translation.liftEnv σ) ■
       T[_]-Env-cong e₁ (consumePhi-liftEnv x k σ))
      (consumePhi-T (suc x) k e₂ (Translation.liftEnv σ) ■
       T[_]-Env-cong e₂ (consumePhi-liftEnv x k σ)))

------------------------------------------------------------------------
-- Binder environments are phi-free away from their own endpoint

phi-fixed :
  {x r : 𝔽 n} (k l : ℕ) → x ≢ r →
  SoupReduction.consumePhi x k (SoupTerm.`phi (r , l)) ≡ SoupTerm.`phi (r , l)
phi-fixed {x = x} {r = r} k l apart with x FinP.≟ r
... | no _ = refl
... | yes same = ⊥-elim (apart same)

chanTriple-phiFree :
  (x : 𝔽 n) (k : ℕ) {e₁ e₂ : SoupTerm.Tm n} (c : 𝔽 n) →
  SoupReduction.consumePhi x k e₁ ≡ e₁ →
  SoupReduction.consumePhi x k e₂ ≡ e₂ →
  SoupReduction.consumePhi x k (Translation.chanTriple (e₁ , c , e₂)) ≡
  Translation.chanTriple (e₁ , c , e₂)
chanTriple-phiFree x k c fixed₁ fixed₂ =
  cong₂ (λ u v → Translation.chanTriple (u , c , v)) fixed₁ fixed₂

sum-phiFree :
  {p q : ℕ} (x : 𝔽 n) (k : ℕ)
  (f : 𝔽 p → SoupTerm.Tm n) (h : 𝔽 q → SoupTerm.Tm n) →
  (∀ y → SoupReduction.consumePhi x k (f y) ≡ f y) →
  (∀ y → SoupReduction.consumePhi x k (h y) ≡ h y) →
  ∀ s → SoupReduction.consumePhi x k ([ f , h ]′ s) ≡ [ f , h ]′ s
sum-phiFree x k f h freeF freeH (inj₁ y) = freeF y
sum-phiFree x k f h freeF freeH (inj₂ y) = freeH y

Ub-phiFree :
  (g : ℕ) (x : 𝔽 n) (k : ℕ) {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  SoupReduction.consumePhi x k e₁ ≡ e₁ →
  SoupReduction.consumePhi x k e₂ ≡ e₂ →
  ∀ y →
  SoupReduction.consumePhi x k (Translation.Ub[ g ] (e₁ , c , e₂) y) ≡
  Translation.Ub[ g ] (e₁ , c , e₂) y
Ub-phiFree (suc zero) x k {c = c} fixed₁ fixed₂ zero =
  chanTriple-phiFree x k c fixed₁ fixed₂
Ub-phiFree (suc (suc g)) x k {c = c} fixed₁ fixed₂ zero =
  chanTriple-phiFree x k c fixed₁ refl
Ub-phiFree (suc (suc g)) x k fixed₁ fixed₂ (suc y) =
  Ub-phiFree (suc g) x k refl fixed₂ y

-- The environment produced for one binder group only ever refers to `phi`
-- cells sitting on that group's own endpoint `r`.
UB-phiFree :
  (B : Typed.BindGroup) (l : ℕ) (x r : 𝔽 n) (k : ℕ)
  {e₁ e₂ : SoupTerm.Tm n} {c : 𝔽 n} →
  x ≢ r →
  SoupReduction.consumePhi x k e₁ ≡ e₁ →
  SoupReduction.consumePhi x k e₂ ≡ e₂ →
  ∀ y →
  SoupReduction.consumePhi x k
    (proj₁ (Translation.UBFrom l B r (e₁ , c , e₂)) y) ≡
  proj₁ (Translation.UBFrom l B r (e₁ , c , e₂)) y
UB-phiFree (g ∷ []) l x r k apart fixed₁ fixed₂ y =
  Ub-phiFree (g + 0) x k fixed₁ fixed₂ y
UB-phiFree (g ∷ g′ ∷ B) l x r k {e₁ = e₁} {e₂ = e₂} {c = c}
  apart fixed₁ fixed₂ y =
  sum-phiFree x k
    (Translation.Ub[ g ] (e₁ , c , SoupTerm.`phi (r , l)))
    (proj₁ (Translation.UBFrom (suc l) (g′ ∷ B) r
             (SoupTerm.`phi (r , l) , c , e₂)))
    (Ub-phiFree g x k fixed₁ (phi-fixed k l apart))
    (UB-phiFree (g′ ∷ B) (suc l) x r k apart (phi-fixed k l apart) fixed₂)
    (Fin.splitAt g y)

-- The instance actually used by `flattenOriented`.
UB-phiFree-init :
  (B : Typed.BindGroup) (x r : 𝔽 n) (k : ℕ) →
  x ≢ r →
  ∀ y →
  SoupReduction.consumePhi x k
    (proj₁ (Translation.UB[ B ] r (SoupTerm.* , r , SoupTerm.*)) y) ≡
  proj₁ (Translation.UB[ B ] r (SoupTerm.* , r , SoupTerm.*)) y
UB-phiFree-init B x r k apart = UB-phiFree B 0 x r k apart refl refl

------------------------------------------------------------------------
-- The invariant

-- `t` mentions `phi` only on endpoints of channels in `aC`.
PhiFreeFor : (𝔽 n → Set) → SoupTerm.Tm (2 *ℕ n) → Set
PhiFreeFor {n} aC t =
  ∀ (i : 𝔽 n) (side : 𝔽 2) (k : ℕ) → ¬ aC i →
  SoupReduction.consumePhi (Soup.endpoint i side) k t ≡ t

phiFree-mono :
  {aC aC′ : 𝔽 n → Set} {t : SoupTerm.Tm (2 *ℕ n)} →
  (∀ i → aC i → aC′ i) → PhiFreeFor aC t → PhiFreeFor aC′ t
phiFree-mono mono free i side k ¬ambient =
  free i side k (λ ambient → ¬ambient (mono i ambient))

++ₛ-phiFree :
  {aC : 𝔽 n → Set} (p : ℕ) {q : ℕ}
  (σ₁ : Translation.Env p (2 *ℕ n)) (σ₂ : Translation.Env q (2 *ℕ n)) →
  (∀ y → PhiFreeFor aC (σ₁ y)) →
  (∀ y → PhiFreeFor aC (σ₂ y)) →
  ∀ y → PhiFreeFor aC ((σ₁ Translation.++ₛ σ₂) y)
++ₛ-phiFree p σ₁ σ₂ free₁ free₂ y with Fin.splitAt p y
... | inj₁ y₁ = free₁ y₁
... | inj₂ y₂ = free₂ y₂

record Separated {k n m : ℕ} (σ : Translation.Env k (2 *ℕ n))
  (ambientChannel : 𝔽 n → Set) (ambientThread : 𝔽 m → Set)
  (C : Soup.Config n m) : Set where
  field
    env-separated : ∀ x → PhiFreeFor ambientChannel (σ x)
    thread-separated :
      ∀ j → ambientThread j →
      PhiFreeFor ambientChannel (lookup (Soup.threads C) j)

open Separated public

separated-mono :
  {k n m : ℕ} {σ : Translation.Env k (2 *ℕ n)}
  {aC aC′ : 𝔽 n → Set} {aT aT′ : 𝔽 m → Set} {C : Soup.Config n m} →
  (∀ i → aC i → aC′ i) → (∀ l → aT′ l → aT l) →
  Separated σ aC aT C → Separated σ aC′ aT′ C
separated-mono monoC monoT separated = record
  { env-separated = λ x → phiFree-mono monoC (env-separated separated x)
  ; thread-separated = λ j ambient →
      phiFree-mono monoC (thread-separated separated j (monoT j ambient))
  }

------------------------------------------------------------------------
-- The scoping lemma

-- Every thread the translation produces mentions `phi` only on endpoints of
-- its own channel vector, or inherits the reference from its environment.
flatten-phiFree :
  (P : Typed.Proc k)
  (lc : Vec (OrientedChannel n) (Translation.channelCount P))
  (σ : Translation.Env k (2 *ℕ n)) {aC : 𝔽 n → Set} →
  (∀ y → PhiFreeFor aC (σ y)) →
  (∀ i → aC (physicalChannel (lookup lc i))) →
  ∀ j → PhiFreeFor aC (lookup (proj₂ (flattenOriented P lc σ)) j)
flatten-phiFree (Typed.⟪ e ⟫) [] σ envFree chanAmbient zero i side k ¬ambient =
  consumePhi-T (Soup.endpoint i side) k e σ ■
  T[_]-Env-cong e (λ y → envFree y i side k ¬ambient)
flatten-phiFree (P Typed.∥ Q) lc σ {aC} envFree chanAmbient =
  lookup-++-cases
    (proj₂ (flattenOriented P (V.take (Translation.channelCount P) lc) σ))
    (proj₂ (flattenOriented Q (V.drop (Translation.channelCount P) lc) σ))
    (PhiFreeFor aC)
    (flatten-phiFree P (V.take (Translation.channelCount P) lc) σ envFree
      (lookup-take-cases (Translation.channelCount P) lc
        (λ ch → aC (physicalChannel ch)) chanAmbient))
    (flatten-phiFree Q (V.drop (Translation.channelCount P) lc) σ envFree
      (lookup-drop-cases (Translation.channelCount P) lc
        (λ ch → aC (physicalChannel ch)) chanAmbient))
flatten-phiFree {k = k} {n = n} (Typed.ν B₁ B₂ P) (ch ∷ lc) σ {aC}
  envFree chanAmbient =
  flatten-phiFree P lc
    ((σ₁ Translation.++ₛ σ₂) Translation.++ₛ σ)
    (++ₛ-phiFree (sum B₁ + sum B₂) (σ₁ Translation.++ₛ σ₂) σ
      (++ₛ-phiFree (sum B₁) σ₁ σ₂ σ₁-free σ₂-free)
      envFree)
    (λ i → chanAmbient (suc i))
  where
  r₁ : 𝔽 (2 *ℕ n)
  r₁ = physicalEndpoint ch 0F

  r₂ : 𝔽 (2 *ℕ n)
  r₂ = physicalEndpoint ch 1F

  σ₁ : Translation.Env (sum B₁) (2 *ℕ n)
  σ₁ = proj₁ (Translation.UB[ B₁ ] r₁ (SoupTerm.* , r₁ , SoupTerm.*))

  σ₂ : Translation.Env (sum B₂) (2 *ℕ n)
  σ₂ = proj₁ (Translation.UB[ B₂ ] r₂ (SoupTerm.* , r₂ , SoupTerm.*))

  -- A non-ambient channel is not the channel bound here, so its endpoints
  -- differ from the two endpoints this binder installs.
  apart :
    (i : 𝔽 n) (side : 𝔽 2) → ¬ aC i → (s : 𝔽 2) →
    Soup.endpoint i side ≢ physicalEndpoint ch s
  apart i side ¬ambient s equal =
    ¬ambient
      (subst aC (sym (endpoint-channel-injective equal)) (chanAmbient 0F))

  σ₁-free : ∀ y → PhiFreeFor aC (σ₁ y)
  σ₁-free y i side k ¬ambient =
    UB-phiFree-init B₁ (Soup.endpoint i side) r₁ k
      (apart i side ¬ambient 0F) y

  σ₂-free : ∀ y → PhiFreeFor aC (σ₂ y)
  σ₂-free y i side k ¬ambient =
    UB-phiFree-init B₂ (Soup.endpoint i side) r₂ k
      (apart i side ¬ambient 1F) y
