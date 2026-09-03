module BorrowedCF.Simulation.ForwardSoup.Expressions where

open import BorrowedCF.Prelude

import BorrowedCF.Processes.TranslationSoup as TS
import BorrowedCF.Terms.Base as Src
import BorrowedCF.Terms.BaseSoup as Soup
import BorrowedCF.Reduction.Base as SrcBase
import BorrowedCF.Reduction.Expressions as SrcRed
import BorrowedCF.Reduction.ExpressionsSoup as SoupRed

open Nat.Variables

ValueEnv : TS.Env n n′ → Set
ValueEnv σ = ∀ x → SoupRed.Value (σ x)

idSub : Soup.Sub n n
idSub = Soup.sub (λ x → Soup.` x) Soup.`phi

SubEq : Soup.Sub n n′ → Soup.Sub n n′ → Set
SubEq σ τ =
  (∀ x → Soup.varImage σ x ≡ Soup.varImage τ x) ×
  (∀ r → Soup.phiImage σ r ≡ Soup.phiImage τ r)

liftSubEq : ∀ {n n′} {σ τ : Soup.Sub n n′} → SubEq σ τ → SubEq (Soup.liftSub σ) (Soup.liftSub τ)
liftSubEq {σ = σ} {τ = τ} (vars , refs) = vars′ , refs′
  where
  vars′ : ∀ x → Soup.varImage (Soup.liftSub σ) x ≡ Soup.varImage (Soup.liftSub τ) x
  vars′ zero = refl
  vars′ (suc x) = cong Soup.wk (vars x)

  refs′ : ∀ r → Soup.phiImage (Soup.liftSub σ) r ≡ Soup.phiImage (Soup.liftSub τ) r
  refs′ (zero , k) = refl
  refs′ (suc x , k) = cong Soup.wk (refs (x , k))

sub-cong : (e : Soup.Tm n) {σ τ : Soup.Sub n n′} → SubEq σ τ → Soup._⋯ₛ_ e σ ≡ Soup._⋯ₛ_ e τ
sub-cong (Soup.` x) (vars , refs) = vars x
sub-cong (Soup.`phi r) (vars , refs) = refs r
sub-cong (Soup.K c) eq = refl
sub-cong (Soup.ƛ e) eq = cong Soup.ƛ (sub-cong e (liftSubEq eq))
sub-cong (Soup.μ e) eq = cong Soup.μ (sub-cong e (liftSubEq eq))
sub-cong (e₁ Soup.·⟨ d ⟩ e₂) eq =
  cong₂ (Soup._·⟨ d ⟩_) (sub-cong e₁ eq) (sub-cong e₂ eq)
sub-cong (e₁ Soup.; e₂) eq = cong₂ Soup._;_ (sub-cong e₁ eq) (sub-cong e₂ eq)
sub-cong (e₁ Soup.⊗ e₂) eq = cong₂ Soup._⊗_ (sub-cong e₁ eq) (sub-cong e₂ eq)
sub-cong (Soup.`let e₁ `in e₂) eq =
  cong₂ Soup.`let_`in_ (sub-cong e₁ eq) (sub-cong e₂ (liftSubEq eq))
sub-cong (Soup.`let⊗ e₁ `in e₂) eq =
  cong₂ Soup.`let⊗_`in_ (sub-cong e₁ eq) (sub-cong e₂ (liftSubEq (liftSubEq eq)))
sub-cong (Soup.`inj i e) eq = cong (Soup.`inj i) (sub-cong e eq)
sub-cong (Soup.`case e `of⟨ e₁ ; e₂ ⟩) eq =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (sub-cong e eq)
    (cong₂ _,_
      (sub-cong e₁ (liftSubEq eq))
      (sub-cong e₂ (liftSubEq eq)))

sub-id : (e : Soup.Tm n) → Soup._⋯ₛ_ e idSub ≡ e
sub-id (Soup.` x) = refl
sub-id (Soup.`phi r) = refl
sub-id (Soup.K c) = refl
sub-id (Soup.ƛ e) = cong Soup.ƛ (sub-cong e liftId ■ sub-id e)
  where
  liftId : SubEq (Soup.liftSub idSub) idSub
  liftId = (λ where zero → refl; (suc x) → refl)
         , (λ where (zero , k) → refl; (suc x , k) → refl)
sub-id (Soup.μ e) = cong Soup.μ (sub-cong e liftId ■ sub-id e)
  where
  liftId : SubEq (Soup.liftSub idSub) idSub
  liftId = (λ where zero → refl; (suc x) → refl)
         , (λ where (zero , k) → refl; (suc x , k) → refl)
sub-id (e₁ Soup.·⟨ d ⟩ e₂) = cong₂ (Soup._·⟨ d ⟩_) (sub-id e₁) (sub-id e₂)
sub-id (e₁ Soup.; e₂) = cong₂ Soup._;_ (sub-id e₁) (sub-id e₂)
sub-id (e₁ Soup.⊗ e₂) = cong₂ Soup._⊗_ (sub-id e₁) (sub-id e₂)
sub-id (Soup.`let e₁ `in e₂) =
  cong₂ Soup.`let_`in_ (sub-id e₁) (sub-cong e₂ liftId ■ sub-id e₂)
  where
  liftId : SubEq (Soup.liftSub idSub) idSub
  liftId = (λ where zero → refl; (suc x) → refl)
         , (λ where (zero , k) → refl; (suc x , k) → refl)
sub-id (Soup.`let⊗ e₁ `in e₂) =
  cong₂ Soup.`let⊗_`in_ (sub-id e₁) (sub-cong e₂ liftId₂ ■ sub-id e₂)
  where
  liftId₂ : SubEq (Soup.liftSub (Soup.liftSub idSub)) idSub
  liftId₂ = (λ where zero → refl; (suc zero) → refl; (suc (suc x)) → refl)
          , (λ where
              (zero , k) → refl
              ((suc zero) , k) → refl
              ((suc (suc x)) , k) → refl)
sub-id (Soup.`inj i e) = cong (Soup.`inj i) (sub-id e)
sub-id (Soup.`case e `of⟨ e₁ ; e₂ ⟩) =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (sub-id e)
    (cong₂ _,_
      (sub-cong e₁ liftId ■ sub-id e₁)
      (sub-cong e₂ liftId ■ sub-id e₂))
  where
  liftId : SubEq (Soup.liftSub idSub) idSub
  liftId = (λ where zero → refl; (suc x) → refl)
         , (λ where (zero , k) → refl; (suc x , k) → refl)

ren-cong : (e : Soup.Tm n) {ρ τ : 𝔽 n → 𝔽 n′} → (∀ x → ρ x ≡ τ x) → Soup._⋯ᵣ_ e ρ ≡ Soup._⋯ᵣ_ e τ
ren-cong (Soup.` x) eq = cong (λ y → Soup.` y) (eq x)
ren-cong (Soup.`phi r) eq = cong Soup.`phi (cong (λ y → y , proj₂ r) (eq (proj₁ r)))
ren-cong (Soup.K c) eq = refl
ren-cong (Soup.ƛ e) eq = cong Soup.ƛ (ren-cong e λ where zero → refl; (suc x) → cong suc (eq x))
ren-cong (Soup.μ e) eq = cong Soup.μ (ren-cong e λ where zero → refl; (suc x) → cong suc (eq x))
ren-cong (e₁ Soup.·⟨ d ⟩ e₂) eq =
  cong₂ (Soup._·⟨ d ⟩_) (ren-cong e₁ eq) (ren-cong e₂ eq)
ren-cong (e₁ Soup.; e₂) eq = cong₂ Soup._;_ (ren-cong e₁ eq) (ren-cong e₂ eq)
ren-cong (e₁ Soup.⊗ e₂) eq = cong₂ Soup._⊗_ (ren-cong e₁ eq) (ren-cong e₂ eq)
ren-cong (Soup.`let e₁ `in e₂) eq =
  cong₂ Soup.`let_`in_ (ren-cong e₁ eq) (ren-cong e₂ λ where zero → refl; (suc x) → cong suc (eq x))
ren-cong (Soup.`let⊗ e₁ `in e₂) eq =
  cong₂ Soup.`let⊗_`in_ (ren-cong e₁ eq)
    (ren-cong e₂ λ where
      zero → refl
      (suc zero) → refl
      (suc (suc x)) → cong suc (cong suc (eq x)))
ren-cong (Soup.`inj i e) eq = cong (Soup.`inj i) (ren-cong e eq)
ren-cong (Soup.`case e `of⟨ e₁ ; e₂ ⟩) eq =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (ren-cong e eq)
    (cong₂ _,_
      (ren-cong e₁ λ where zero → refl; (suc x) → cong suc (eq x))
      (ren-cong e₂ λ where zero → refl; (suc x) → cong suc (eq x)))

ren-ren : (e : Soup.Tm n) (ρ₁ : 𝔽 n → 𝔽 n′) (ρ₂ : 𝔽 n′ → 𝔽 n₃) →
  Soup._⋯ᵣ_ (Soup._⋯ᵣ_ e ρ₁) ρ₂ ≡ Soup._⋯ᵣ_ e (ρ₂ ∘ ρ₁)
ren-ren (Soup.` x) ρ₁ ρ₂ = refl
ren-ren (Soup.`phi r) ρ₁ ρ₂ = refl
ren-ren (Soup.K c) ρ₁ ρ₂ = refl
ren-ren (Soup.ƛ e) ρ₁ ρ₂ =
  cong Soup.ƛ
    (ren-ren e (Soup.liftRen ρ₁) (Soup.liftRen ρ₂)
     ■ ren-cong e λ where zero → refl; (suc x) → refl)
ren-ren (Soup.μ e) ρ₁ ρ₂ =
  cong Soup.μ
    (ren-ren e (Soup.liftRen ρ₁) (Soup.liftRen ρ₂)
     ■ ren-cong e λ where zero → refl; (suc x) → refl)
ren-ren (e₁ Soup.·⟨ d ⟩ e₂) ρ₁ ρ₂ =
  cong₂ (Soup._·⟨ d ⟩_) (ren-ren e₁ ρ₁ ρ₂) (ren-ren e₂ ρ₁ ρ₂)
ren-ren (e₁ Soup.; e₂) ρ₁ ρ₂ = cong₂ Soup._;_ (ren-ren e₁ ρ₁ ρ₂) (ren-ren e₂ ρ₁ ρ₂)
ren-ren (e₁ Soup.⊗ e₂) ρ₁ ρ₂ = cong₂ Soup._⊗_ (ren-ren e₁ ρ₁ ρ₂) (ren-ren e₂ ρ₁ ρ₂)
ren-ren (Soup.`let e₁ `in e₂) ρ₁ ρ₂ =
  cong₂ Soup.`let_`in_ (ren-ren e₁ ρ₁ ρ₂)
    (ren-ren e₂ (Soup.liftRen ρ₁) (Soup.liftRen ρ₂)
     ■ ren-cong e₂ λ where zero → refl; (suc x) → refl)
ren-ren (Soup.`let⊗ e₁ `in e₂) ρ₁ ρ₂ =
  cong₂ Soup.`let⊗_`in_ (ren-ren e₁ ρ₁ ρ₂)
    (ren-ren e₂ (Soup.liftRen (Soup.liftRen ρ₁)) (Soup.liftRen (Soup.liftRen ρ₂))
     ■ ren-cong e₂ λ where
        zero → refl
        (suc zero) → refl
        (suc (suc x)) → refl)
ren-ren (Soup.`inj i e) ρ₁ ρ₂ = cong (Soup.`inj i) (ren-ren e ρ₁ ρ₂)
ren-ren (Soup.`case e `of⟨ e₁ ; e₂ ⟩) ρ₁ ρ₂ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (ren-ren e ρ₁ ρ₂)
    (cong₂ _,_
      (ren-ren e₁ (Soup.liftRen ρ₁) (Soup.liftRen ρ₂)
       ■ ren-cong e₁ λ where zero → refl; (suc x) → refl)
      (ren-ren e₂ (Soup.liftRen ρ₁) (Soup.liftRen ρ₂)
       ■ ren-cong e₂ λ where zero → refl; (suc x) → refl))

wk-⋯ᵣ : (e : Soup.Tm n) (ρ : 𝔽 n → 𝔽 n′) →
  Soup._⋯ᵣ_ (Soup.wk e) (Soup.liftRen ρ) ≡ Soup.wk (Soup._⋯ᵣ_ e ρ)
wk-⋯ᵣ e ρ =
  ren-ren e suc (Soup.liftRen ρ)
  ■ ren-cong e (λ x → refl)
  ■ sym (ren-ren e ρ suc)

renComp : (ρ : 𝔽 n → 𝔽 n′) → Soup.Sub n′ n₃ → Soup.Sub n n₃
renComp ρ σ = Soup.sub
  (λ x → Soup.varImage σ (ρ x))
  (λ r → Soup.phiImage σ (Soup.renameRef ρ r))

renComp-liftEq : (ρ : 𝔽 n → 𝔽 n′) (σ : Soup.Sub n′ n₃) →
  SubEq (renComp (Soup.liftRen ρ) (Soup.liftSub σ)) (Soup.liftSub (renComp ρ σ))
renComp-liftEq ρ σ = vars , refs
  where
  vars : ∀ x → Soup.varImage (renComp (Soup.liftRen ρ) (Soup.liftSub σ)) x
             ≡ Soup.varImage (Soup.liftSub (renComp ρ σ)) x
  vars zero = refl
  vars (suc x) = refl

  refs : ∀ r → Soup.phiImage (renComp (Soup.liftRen ρ) (Soup.liftSub σ)) r
             ≡ Soup.phiImage (Soup.liftSub (renComp ρ σ)) r
  refs (zero , k) = refl
  refs (suc x , k) = refl

renComp-liftEq₂ : (ρ : 𝔽 n → 𝔽 n′) (σ : Soup.Sub n′ n₃) →
  SubEq
    (renComp (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ)))
    (Soup.liftSub (Soup.liftSub (renComp ρ σ)))
renComp-liftEq₂ ρ σ = vars , refs
  where
  vars : ∀ x →
    Soup.varImage
      (renComp (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ))) x
    ≡ Soup.varImage (Soup.liftSub (Soup.liftSub (renComp ρ σ))) x
  vars zero = refl
  vars (suc zero) = refl
  vars (suc (suc x)) = refl

  refs : ∀ r →
    Soup.phiImage
      (renComp (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ))) r
    ≡ Soup.phiImage (Soup.liftSub (Soup.liftSub (renComp ρ σ))) r
  refs (zero , k) = refl
  refs ((suc zero) , k) = refl
  refs ((suc (suc x)) , k) = refl

ren-sub : (e : Soup.Tm n) (ρ : 𝔽 n → 𝔽 n′) (σ : Soup.Sub n′ n₃) →
  Soup._⋯ₛ_ (Soup._⋯ᵣ_ e ρ) σ ≡ Soup._⋯ₛ_ e (renComp ρ σ)
ren-sub (Soup.` x) ρ σ = refl
ren-sub (Soup.`phi r) ρ σ = refl
ren-sub (Soup.K c) ρ σ = refl
ren-sub (Soup.ƛ e) ρ σ =
  cong Soup.ƛ (ren-sub e (Soup.liftRen ρ) (Soup.liftSub σ) ■ sub-cong e (renComp-liftEq ρ σ))
ren-sub (Soup.μ e) ρ σ =
  cong Soup.μ (ren-sub e (Soup.liftRen ρ) (Soup.liftSub σ) ■ sub-cong e (renComp-liftEq ρ σ))
ren-sub (e₁ Soup.·⟨ d ⟩ e₂) ρ σ =
  cong₂ (Soup._·⟨ d ⟩_) (ren-sub e₁ ρ σ) (ren-sub e₂ ρ σ)
ren-sub (e₁ Soup.; e₂) ρ σ = cong₂ Soup._;_ (ren-sub e₁ ρ σ) (ren-sub e₂ ρ σ)
ren-sub (e₁ Soup.⊗ e₂) ρ σ = cong₂ Soup._⊗_ (ren-sub e₁ ρ σ) (ren-sub e₂ ρ σ)
ren-sub (Soup.`let e₁ `in e₂) ρ σ =
  cong₂ Soup.`let_`in_ (ren-sub e₁ ρ σ)
    (ren-sub e₂ (Soup.liftRen ρ) (Soup.liftSub σ) ■ sub-cong e₂ (renComp-liftEq ρ σ))
ren-sub (Soup.`let⊗ e₁ `in e₂) ρ σ =
  cong₂ Soup.`let⊗_`in_ (ren-sub e₁ ρ σ)
    (ren-sub e₂ (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ))
     ■ sub-cong e₂ (renComp-liftEq₂ ρ σ))
ren-sub (Soup.`inj i e) ρ σ = cong (Soup.`inj i) (ren-sub e ρ σ)
ren-sub (Soup.`case e `of⟨ e₁ ; e₂ ⟩) ρ σ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (ren-sub e ρ σ)
    (cong₂ _,_
      (ren-sub e₁ (Soup.liftRen ρ) (Soup.liftSub σ) ■ sub-cong e₁ (renComp-liftEq ρ σ))
      (ren-sub e₂ (Soup.liftRen ρ) (Soup.liftSub σ) ■ sub-cong e₂ (renComp-liftEq ρ σ)))

mapSub : (ρ : 𝔽 n′ → 𝔽 n₃) → Soup.Sub n n′ → Soup.Sub n n₃
mapSub ρ σ = Soup.sub
  (λ x → Soup._⋯ᵣ_ (Soup.varImage σ x) ρ)
  (λ r → Soup._⋯ᵣ_ (Soup.phiImage σ r) ρ)

mapSub-liftEq : (ρ : 𝔽 n′ → 𝔽 n₃) (σ : Soup.Sub n n′) →
  SubEq (mapSub (Soup.liftRen ρ) (Soup.liftSub σ)) (Soup.liftSub (mapSub ρ σ))
mapSub-liftEq ρ σ = vars , refs
  where
  vars : ∀ x → Soup.varImage (mapSub (Soup.liftRen ρ) (Soup.liftSub σ)) x
             ≡ Soup.varImage (Soup.liftSub (mapSub ρ σ)) x
  vars zero = refl
  vars (suc x) = wk-⋯ᵣ (Soup.varImage σ x) ρ

  refs : ∀ r → Soup.phiImage (mapSub (Soup.liftRen ρ) (Soup.liftSub σ)) r
             ≡ Soup.phiImage (Soup.liftSub (mapSub ρ σ)) r
  refs (zero , k) = refl
  refs (suc x , k) = wk-⋯ᵣ (Soup.phiImage σ (x , k)) ρ

mapSub-liftEq₂ : (ρ : 𝔽 n′ → 𝔽 n₃) (σ : Soup.Sub n n′) →
  SubEq
    (mapSub (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ)))
    (Soup.liftSub (Soup.liftSub (mapSub ρ σ)))
mapSub-liftEq₂ ρ σ = vars , refs
  where
  vars : ∀ x →
    Soup.varImage
      (mapSub (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ))) x
    ≡ Soup.varImage (Soup.liftSub (Soup.liftSub (mapSub ρ σ))) x
  vars zero = refl
  vars (suc zero) = refl
  vars (suc (suc x)) =
    wk-⋯ᵣ (Soup.wk (Soup.varImage σ x)) (Soup.liftRen ρ)
    ■ cong Soup.wk (wk-⋯ᵣ (Soup.varImage σ x) ρ)

  refs : ∀ r →
    Soup.phiImage
      (mapSub (Soup.liftRen (Soup.liftRen ρ)) (Soup.liftSub (Soup.liftSub σ))) r
    ≡ Soup.phiImage (Soup.liftSub (Soup.liftSub (mapSub ρ σ))) r
  refs (zero , k) = refl
  refs ((suc zero) , k) = refl
  refs ((suc (suc x)) , k) =
    wk-⋯ᵣ (Soup.wk (Soup.phiImage σ (x , k))) (Soup.liftRen ρ)
    ■ cong Soup.wk (wk-⋯ᵣ (Soup.phiImage σ (x , k)) ρ)

sub-ren : (e : Soup.Tm n) (σ : Soup.Sub n n′) (ρ : 𝔽 n′ → 𝔽 n₃) →
  Soup._⋯ᵣ_ (Soup._⋯ₛ_ e σ) ρ ≡ Soup._⋯ₛ_ e (mapSub ρ σ)
sub-ren (Soup.` x) σ ρ = refl
sub-ren (Soup.`phi r) σ ρ = refl
sub-ren (Soup.K c) σ ρ = refl
sub-ren (Soup.ƛ e) σ ρ =
  cong Soup.ƛ (sub-ren e (Soup.liftSub σ) (Soup.liftRen ρ) ■ sub-cong e (mapSub-liftEq ρ σ))
sub-ren (Soup.μ e) σ ρ =
  cong Soup.μ (sub-ren e (Soup.liftSub σ) (Soup.liftRen ρ) ■ sub-cong e (mapSub-liftEq ρ σ))
sub-ren (e₁ Soup.·⟨ d ⟩ e₂) σ ρ =
  cong₂ (Soup._·⟨ d ⟩_) (sub-ren e₁ σ ρ) (sub-ren e₂ σ ρ)
sub-ren (e₁ Soup.; e₂) σ ρ = cong₂ Soup._;_ (sub-ren e₁ σ ρ) (sub-ren e₂ σ ρ)
sub-ren (e₁ Soup.⊗ e₂) σ ρ = cong₂ Soup._⊗_ (sub-ren e₁ σ ρ) (sub-ren e₂ σ ρ)
sub-ren (Soup.`let e₁ `in e₂) σ ρ =
  cong₂ Soup.`let_`in_ (sub-ren e₁ σ ρ)
    (sub-ren e₂ (Soup.liftSub σ) (Soup.liftRen ρ) ■ sub-cong e₂ (mapSub-liftEq ρ σ))
sub-ren (Soup.`let⊗ e₁ `in e₂) σ ρ =
  cong₂ Soup.`let⊗_`in_ (sub-ren e₁ σ ρ)
    (sub-ren e₂ (Soup.liftSub (Soup.liftSub σ)) (Soup.liftRen (Soup.liftRen ρ))
     ■ sub-cong e₂ (mapSub-liftEq₂ ρ σ))
sub-ren (Soup.`inj i e) σ ρ = cong (Soup.`inj i) (sub-ren e σ ρ)
sub-ren (Soup.`case e `of⟨ e₁ ; e₂ ⟩) σ ρ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (sub-ren e σ ρ)
    (cong₂ _,_
      (sub-ren e₁ (Soup.liftSub σ) (Soup.liftRen ρ) ■ sub-cong e₁ (mapSub-liftEq ρ σ))
      (sub-ren e₂ (Soup.liftSub σ) (Soup.liftRen ρ) ■ sub-cong e₂ (mapSub-liftEq ρ σ)))

renComp-suc-liftSub≗mapSub-suc : (σ : Soup.Sub n n′) →
  SubEq (renComp suc (Soup.liftSub σ)) (mapSub suc σ)
renComp-suc-liftSub≗mapSub-suc σ = vars , refs
  where
  vars : ∀ x → Soup.varImage (renComp suc (Soup.liftSub σ)) x
             ≡ Soup.varImage (mapSub suc σ) x
  vars x = refl

  refs : ∀ r → Soup.phiImage (renComp suc (Soup.liftSub σ)) r
             ≡ Soup.phiImage (mapSub suc σ) r
  refs r = refl

wk-⋯ₛ : (e : Soup.Tm n) (σ : Soup.Sub n n′) →
  Soup._⋯ₛ_ (Soup.wk e) (Soup.liftSub σ) ≡ Soup.wk (Soup._⋯ₛ_ e σ)
wk-⋯ₛ e σ =
  ren-sub e suc (Soup.liftSub σ)
  ■ sub-cong e (renComp-suc-liftSub≗mapSub-suc σ)
  ■ sym (sub-ren e σ suc)

renComp-suc-singleSub-id : (t : Soup.Tm n) →
  SubEq (renComp suc (SoupRed.singleSub t)) idSub
renComp-suc-singleSub-id t = vars , refs
  where
  vars : ∀ x → Soup.varImage (renComp suc (SoupRed.singleSub t)) x ≡ Soup.varImage idSub x
  vars x = refl

  refs : ∀ r → Soup.phiImage (renComp suc (SoupRed.singleSub t)) r ≡ Soup.phiImage idSub r
  refs r = refl

subst₀-wk : (e t : Soup.Tm n) → SoupRed.subst₀ t (Soup.wk e) ≡ e
subst₀-wk e t =
  ren-sub e suc (SoupRed.singleSub t)
  ■ sub-cong e (renComp-suc-singleSub-id t)
  ■ sub-id e

liftEnv* : (k : ℕ) → TS.Env n n′ → TS.Env (k + n) (k + n′)
liftEnv* zero σ = σ
liftEnv* (suc k) σ = TS.liftEnv (liftEnv* k σ)

singleSub* : (k : ℕ) → Soup.Tm n′ → Soup.Sub (suc k + n′) (k + n′)
singleSub* zero t = SoupRed.singleSub t
singleSub* (suc k) t = Soup.liftSub (singleSub* k t)

envAt : (k : ℕ) → Soup.Tm n′ → TS.Env n n′ → TS.Env (suc k + n) (k + n′)
envAt zero t σ zero = t
envAt zero t σ (suc x) = σ x
envAt (suc k) t σ zero = Soup.` zero
envAt (suc k) t σ (suc x) = Soup.wk (envAt k t σ x)

envAt-point :
  (k : ℕ) (t : Soup.Tm n′) (σ : TS.Env n n′) (x : 𝔽 (suc k + n)) →
  envAt k t σ x ≡ Soup._⋯ₛ_ (liftEnv* (suc k) σ x) (singleSub* k t)
envAt-point zero t σ zero = refl
envAt-point zero t σ (suc x) = sym (subst₀-wk (σ x) t)
envAt-point (suc k) t σ zero = refl
envAt-point (suc k) t σ (suc x) =
  cong Soup.wk (envAt-point k t σ x)
  ■ sym (wk-⋯ₛ (liftEnv* (suc k) σ x) (singleSub* k t))

envAt-liftEq : (k : ℕ) (t : Soup.Tm n′) (σ : TS.Env n n′) →
  ∀ x → TS.liftEnv (envAt k t σ) x ≡ envAt (suc k) t σ x
envAt-liftEq k t σ zero = refl
envAt-liftEq k t σ (suc x) = refl

envAt-liftEq₂ : (k : ℕ) (t : Soup.Tm n′) (σ : TS.Env n n′) →
  ∀ x → TS.liftEnv (TS.liftEnv (envAt k t σ)) x ≡ envAt (suc (suc k)) t σ x
envAt-liftEq₂ k t σ zero = refl
envAt-liftEq₂ k t σ (suc x) = cong Soup.wk (envAt-liftEq k t σ x)

liftEnvEq : ∀ {n n′} {σ τ : TS.Env n n′} → (∀ x → σ x ≡ τ x) → ∀ x → TS.liftEnv σ x ≡ TS.liftEnv τ x
liftEnvEq eq zero = refl
liftEnvEq eq (suc x) = cong Soup.wk (eq x)

T[_]-Env-cong : (e : Src.Tm n) {σ τ : TS.Env n n′} →
  (∀ x → σ x ≡ τ x) → TS.T[ e ] σ ≡ TS.T[ e ] τ
T[_]-Env-cong (Src.` x) eq = eq x
T[_]-Env-cong (Src.K c) eq = refl
T[_]-Env-cong (Src.ƛ e) eq = cong Soup.ƛ (T[_]-Env-cong e (liftEnvEq eq))
T[_]-Env-cong (Src.μ e) eq = cong Soup.μ (T[_]-Env-cong e (liftEnvEq eq))
T[_]-Env-cong (e₁ Src.·⟨ d ⟩ e₂) eq =
  cong₂ (Soup._·⟨ d ⟩_) (T[_]-Env-cong e₁ eq) (T[_]-Env-cong e₂ eq)
T[_]-Env-cong (e₁ Src.; e₂) eq = cong₂ Soup._;_ (T[_]-Env-cong e₁ eq) (T[_]-Env-cong e₂ eq)
T[_]-Env-cong (e₁ Src.⊗ e₂) eq = cong₂ Soup._⊗_ (T[_]-Env-cong e₁ eq) (T[_]-Env-cong e₂ eq)
T[_]-Env-cong (Src.`let e₁ `in e₂) eq =
  cong₂ Soup.`let_`in_ (T[_]-Env-cong e₁ eq) (T[_]-Env-cong e₂ (liftEnvEq eq))
T[_]-Env-cong (Src.`let⊗ e₁ `in e₂) eq =
  cong₂ Soup.`let⊗_`in_ (T[_]-Env-cong e₁ eq) (T[_]-Env-cong e₂ (liftEnvEq (liftEnvEq eq)))
T[_]-Env-cong (Src.`inj i e) eq = cong (Soup.`inj i) (T[_]-Env-cong e eq)
T[_]-Env-cong (Src.`case e `of⟨ e₁ ; e₂ ⟩) eq =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (T[_]-Env-cong e eq)
    (cong₂ _,_
      (T[_]-Env-cong e₁ (liftEnvEq eq))
      (T[_]-Env-cong e₂ (liftEnvEq eq)))

T[_]-renEnv : (e : Src.Tm n) (σ : TS.Env n n′) (ρ : 𝔽 n′ → 𝔽 n₃) →
  TS.T[ e ] (λ x → Soup._⋯ᵣ_ (σ x) ρ) ≡ Soup._⋯ᵣ_ (TS.T[ e ] σ) ρ
T[_]-renEnv (Src.` x) σ ρ = refl
T[_]-renEnv (Src.K c) σ ρ = refl
T[_]-renEnv (Src.ƛ e) σ ρ =
  cong Soup.ƛ
    (T[_]-Env-cong e liftEq ■ (T[_]-renEnv e (TS.liftEnv σ) (Soup.liftRen ρ)))
  where
  liftEq : ∀ x → TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ) x ≡ Soup._⋯ᵣ_ (TS.liftEnv σ x) (Soup.liftRen ρ)
  liftEq zero = refl
  liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)
T[_]-renEnv (Src.μ e) σ ρ =
  cong Soup.μ
    (T[_]-Env-cong e liftEq ■ (T[_]-renEnv e (TS.liftEnv σ) (Soup.liftRen ρ)))
  where
  liftEq : ∀ x → TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ) x ≡ Soup._⋯ᵣ_ (TS.liftEnv σ x) (Soup.liftRen ρ)
  liftEq zero = refl
  liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)
T[_]-renEnv (e₁ Src.·⟨ d ⟩ e₂) σ ρ =
  cong₂ (Soup._·⟨ d ⟩_) (T[_]-renEnv e₁ σ ρ) (T[_]-renEnv e₂ σ ρ)
T[_]-renEnv (e₁ Src.; e₂) σ ρ = cong₂ Soup._;_ (T[_]-renEnv e₁ σ ρ) (T[_]-renEnv e₂ σ ρ)
T[_]-renEnv (e₁ Src.⊗ e₂) σ ρ = cong₂ Soup._⊗_ (T[_]-renEnv e₁ σ ρ) (T[_]-renEnv e₂ σ ρ)
T[_]-renEnv (Src.`let e₁ `in e₂) σ ρ =
  cong₂ Soup.`let_`in_ (T[_]-renEnv e₁ σ ρ)
    (T[_]-Env-cong e₂ liftEq ■ (T[_]-renEnv e₂ (TS.liftEnv σ) (Soup.liftRen ρ)))
  where
  liftEq : ∀ x → TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ) x ≡ Soup._⋯ᵣ_ (TS.liftEnv σ x) (Soup.liftRen ρ)
  liftEq zero = refl
  liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)
T[_]-renEnv (Src.`let⊗ e₁ `in e₂) σ ρ =
  cong₂ Soup.`let⊗_`in_ (T[_]-renEnv e₁ σ ρ)
    (T[_]-Env-cong e₂ liftEq₂
     ■ (T[_]-renEnv e₂ (TS.liftEnv (TS.liftEnv σ)) (Soup.liftRen (Soup.liftRen ρ))))
  where
  liftEq : ∀ x → TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ) x ≡ Soup._⋯ᵣ_ (TS.liftEnv σ x) (Soup.liftRen ρ)
  liftEq zero = refl
  liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)
  liftEq₂ : ∀ x → TS.liftEnv (TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ)) x
                 ≡ Soup._⋯ᵣ_ (TS.liftEnv (TS.liftEnv σ) x) (Soup.liftRen (Soup.liftRen ρ))
  liftEq₂ zero = refl
  liftEq₂ (suc zero) = refl
  liftEq₂ (suc (suc x)) =
    sym
      (wk-⋯ᵣ (Soup.wk (σ x)) (Soup.liftRen ρ)
       ■ cong Soup.wk (wk-⋯ᵣ (σ x) ρ))
T[_]-renEnv (Src.`inj i e) σ ρ = cong (Soup.`inj i) (T[_]-renEnv e σ ρ)
T[_]-renEnv (Src.`case e `of⟨ e₁ ; e₂ ⟩) σ ρ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (T[_]-renEnv e σ ρ)
    (cong₂ _,_
      (T[_]-Env-cong e₁ liftEq ■ (T[_]-renEnv e₁ (TS.liftEnv σ) (Soup.liftRen ρ)))
      (T[_]-Env-cong e₂ liftEq ■ (T[_]-renEnv e₂ (TS.liftEnv σ) (Soup.liftRen ρ))))
  where
  liftEq : ∀ x → TS.liftEnv (λ y → Soup._⋯ᵣ_ (σ y) ρ) x ≡ Soup._⋯ᵣ_ (TS.liftEnv σ x) (Soup.liftRen ρ)
  liftEq zero = refl
  liftEq (suc x) = sym (wk-⋯ᵣ (σ x) ρ)

T[_]-⋯ᵣ : (e : Src.Tm n) (ρ : 𝔽 n → 𝔽 n′) (σ : TS.Env n′ n₃) →
  TS.T[ Src._⋯_ e ρ ] σ ≡ TS.T[ e ] (σ ∘ ρ)
T[_]-⋯ᵣ (Src.` x) ρ σ = refl
T[_]-⋯ᵣ (Src.K c) ρ σ = refl
T[_]-⋯ᵣ (Src.ƛ e) ρ σ =
  cong Soup.ƛ (T[_]-⋯ᵣ e (ρ Src.↑ᵣ) (TS.liftEnv σ) ■ (T[_]-Env-cong e (λ where zero → refl; (suc x) → refl)))
T[_]-⋯ᵣ (Src.μ e) ρ σ =
  cong Soup.μ (T[_]-⋯ᵣ e (ρ Src.↑ᵣ) (TS.liftEnv σ) ■ (T[_]-Env-cong e (λ where zero → refl; (suc x) → refl)))
T[_]-⋯ᵣ (e₁ Src.·⟨ d ⟩ e₂) ρ σ =
  cong₂ (Soup._·⟨ d ⟩_) (T[_]-⋯ᵣ e₁ ρ σ) (T[_]-⋯ᵣ e₂ ρ σ)
T[_]-⋯ᵣ (e₁ Src.; e₂) ρ σ = cong₂ Soup._;_ (T[_]-⋯ᵣ e₁ ρ σ) (T[_]-⋯ᵣ e₂ ρ σ)
T[_]-⋯ᵣ (e₁ Src.⊗ e₂) ρ σ = cong₂ Soup._⊗_ (T[_]-⋯ᵣ e₁ ρ σ) (T[_]-⋯ᵣ e₂ ρ σ)
T[_]-⋯ᵣ (Src.`let e₁ `in e₂) ρ σ =
  cong₂ Soup.`let_`in_ (T[_]-⋯ᵣ e₁ ρ σ)
    (T[_]-⋯ᵣ e₂ (ρ Src.↑ᵣ) (TS.liftEnv σ) ■ (T[_]-Env-cong e₂ (λ where zero → refl; (suc x) → refl)))
T[_]-⋯ᵣ (Src.`let⊗ e₁ `in e₂) ρ σ =
  cong₂ Soup.`let⊗_`in_ (T[_]-⋯ᵣ e₁ ρ σ)
    (T[_]-⋯ᵣ e₂ ((ρ Src.↑ᵣ) Src.↑ᵣ) (TS.liftEnv (TS.liftEnv σ))
     ■ (T[_]-Env-cong e₂ (λ where zero → refl; (suc zero) → refl; (suc (suc x)) → refl)))
T[_]-⋯ᵣ (Src.`inj i e) ρ σ = cong (Soup.`inj i) (T[_]-⋯ᵣ e ρ σ)
T[_]-⋯ᵣ (Src.`case e `of⟨ e₁ ; e₂ ⟩) ρ σ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (T[_]-⋯ᵣ e ρ σ)
    (cong₂ _,_
      (T[_]-⋯ᵣ e₁ (ρ Src.↑ᵣ) (TS.liftEnv σ) ■ (T[_]-Env-cong e₁ (λ where zero → refl; (suc x) → refl)))
      (T[_]-⋯ᵣ e₂ (ρ Src.↑ᵣ) (TS.liftEnv σ) ■ (T[_]-Env-cong e₂ (λ where zero → refl; (suc x) → refl))))

T[_]-wk : (e : Src.Tm n) (σ : TS.Env n n′) →
  TS.T[ Src.wk e ] (TS.liftEnv σ) ≡ Soup.wk (TS.T[ e ] σ)
T[_]-wk e σ = T[_]-⋯ᵣ e suc (TS.liftEnv σ) ■ (T[_]-renEnv e σ suc)

T[_]-envAt :
  (k : ℕ) (e : Src.Tm (suc k + n)) (t : Soup.Tm n′) (σ : TS.Env n n′) →
  TS.T[ e ] (envAt k t σ) ≡ Soup._⋯ₛ_ (TS.T[ e ] (liftEnv* (suc k) σ)) (singleSub* k t)
T[_]-envAt k (Src.` x) t σ = envAt-point k t σ x
T[_]-envAt k (Src.K c) t σ = refl
T[_]-envAt k (Src.ƛ e) t σ =
  cong Soup.ƛ (T[_]-Env-cong e (envAt-liftEq k t σ) ■ T[_]-envAt (suc k) e t σ)
T[_]-envAt k (Src.μ e) t σ =
  cong Soup.μ (T[_]-Env-cong e (envAt-liftEq k t σ) ■ T[_]-envAt (suc k) e t σ)
T[_]-envAt k (e₁ Src.·⟨ d ⟩ e₂) t σ =
  cong₂ (Soup._·⟨ d ⟩_) (T[_]-envAt k e₁ t σ) (T[_]-envAt k e₂ t σ)
T[_]-envAt k (e₁ Src.; e₂) t σ = cong₂ Soup._;_ (T[_]-envAt k e₁ t σ) (T[_]-envAt k e₂ t σ)
T[_]-envAt k (e₁ Src.⊗ e₂) t σ = cong₂ Soup._⊗_ (T[_]-envAt k e₁ t σ) (T[_]-envAt k e₂ t σ)
T[_]-envAt k (Src.`let e₁ `in e₂) t σ =
  cong₂ Soup.`let_`in_ (T[_]-envAt k e₁ t σ)
    (T[_]-Env-cong e₂ (envAt-liftEq k t σ) ■ T[_]-envAt (suc k) e₂ t σ)
T[_]-envAt k (Src.`let⊗ e₁ `in e₂) t σ =
  cong₂ Soup.`let⊗_`in_ (T[_]-envAt k e₁ t σ)
    (T[_]-Env-cong e₂ (envAt-liftEq₂ k t σ) ■ T[_]-envAt (suc (suc k)) e₂ t σ)
T[_]-envAt k (Src.`inj i e) t σ = cong (Soup.`inj i) (T[_]-envAt k e t σ)
T[_]-envAt k (Src.`case e `of⟨ e₁ ; e₂ ⟩) t σ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (T[_]-envAt k e t σ)
    (cong₂ _,_
      (T[_]-Env-cong e₁ (envAt-liftEq k t σ) ■ T[_]-envAt (suc k) e₁ t σ)
      (T[_]-Env-cong e₂ (envAt-liftEq k t σ) ■ T[_]-envAt (suc k) e₂ t σ))

T[_]-⋯ₛ : (e : Src.Tm m) (τ : m Src.→ₛ n) (σ : TS.Env n n′) →
  TS.T[ Src._⋯_ e τ ] σ ≡ TS.T[ e ] (λ x → TS.T[ τ x ] σ)
T[_]-⋯ₛ (Src.` x) τ σ = refl
T[_]-⋯ₛ (Src.K c) τ σ = refl
T[_]-⋯ₛ (Src.ƛ e) τ σ =
  cong Soup.ƛ
    (T[_]-⋯ₛ e (τ Src.↑ₛ) (TS.liftEnv σ)
     ■ (T[_]-Env-cong e (λ where zero → refl; (suc x) → T[_]-wk (τ x) σ)))
T[_]-⋯ₛ (Src.μ e) τ σ =
  cong Soup.μ
    (T[_]-⋯ₛ e (τ Src.↑ₛ) (TS.liftEnv σ)
     ■ (T[_]-Env-cong e (λ where zero → refl; (suc x) → T[_]-wk (τ x) σ)))
T[_]-⋯ₛ (e₁ Src.·⟨ d ⟩ e₂) τ σ =
  cong₂ (Soup._·⟨ d ⟩_) (T[_]-⋯ₛ e₁ τ σ) (T[_]-⋯ₛ e₂ τ σ)
T[_]-⋯ₛ (e₁ Src.; e₂) τ σ = cong₂ Soup._;_ (T[_]-⋯ₛ e₁ τ σ) (T[_]-⋯ₛ e₂ τ σ)
T[_]-⋯ₛ (e₁ Src.⊗ e₂) τ σ = cong₂ Soup._⊗_ (T[_]-⋯ₛ e₁ τ σ) (T[_]-⋯ₛ e₂ τ σ)
T[_]-⋯ₛ (Src.`let e₁ `in e₂) τ σ =
  cong₂ Soup.`let_`in_ (T[_]-⋯ₛ e₁ τ σ)
    (T[_]-⋯ₛ e₂ (τ Src.↑ₛ) (TS.liftEnv σ)
     ■ (T[_]-Env-cong e₂ (λ where zero → refl; (suc x) → T[_]-wk (τ x) σ)))
T[_]-⋯ₛ (Src.`let⊗ e₁ `in e₂) τ σ =
  cong₂ Soup.`let⊗_`in_ (T[_]-⋯ₛ e₁ τ σ)
    (T[_]-⋯ₛ e₂ ((τ Src.↑ₛ) Src.↑ₛ) (TS.liftEnv (TS.liftEnv σ))
     ■ (T[_]-Env-cong e₂ liftEq₂))
  where
  liftEq₂ : ∀ x → TS.T[ ((τ Src.↑ₛ) Src.↑ₛ) x ] (TS.liftEnv (TS.liftEnv σ))
                 ≡ TS.liftEnv (TS.liftEnv (λ y → TS.T[ τ y ] σ)) x
  liftEq₂ zero = refl
  liftEq₂ (suc zero) = refl
  liftEq₂ (suc (suc x)) =
    T[_]-wk (Src.wk (τ x)) (TS.liftEnv σ)
    ■ cong Soup.wk (T[_]-wk (τ x) σ)
T[_]-⋯ₛ (Src.`inj i e) τ σ = cong (Soup.`inj i) (T[_]-⋯ₛ e τ σ)
T[_]-⋯ₛ (Src.`case e `of⟨ e₁ ; e₂ ⟩) τ σ =
  cong₂ (λ x ys → Soup.`case x `of⟨ proj₁ ys ; proj₂ ys ⟩)
    (T[_]-⋯ₛ e τ σ)
    (cong₂ _,_
      (T[_]-⋯ₛ e₁ (τ Src.↑ₛ) (TS.liftEnv σ)
       ■ (T[_]-Env-cong e₁ (λ where zero → refl; (suc x) → T[_]-wk (τ x) σ)))
      (T[_]-⋯ₛ e₂ (τ Src.↑ₛ) (TS.liftEnv σ)
       ■ (T[_]-Env-cong e₂ (λ where zero → refl; (suc x) → T[_]-wk (τ x) σ))))

T[_]-⦅⦆ : (e : Src.Tm (1 + n)) (v : Src.Tm n) (σ : TS.Env n n′) →
  TS.T[ Src._⋯_ e (Src.⦅ v ⦆) ] σ ≡ SoupRed.subst₀ (TS.T[ v ] σ) (TS.T[ e ] (TS.liftEnv σ))
T[_]-⦅⦆ e v σ =
  T[_]-⋯ₛ e (Src.⦅ v ⦆) σ
  ■ (T[_]-Env-cong e (λ where zero → refl; (suc x) → refl))
  ■ (T[_]-envAt 0 e (TS.T[ v ] σ) σ)

T[_]-Value : ∀ {n n′} {e : Src.Tm n} {σ : TS.Env n n′} → SrcBase.Value e → ValueEnv σ → SoupRed.Value (TS.T[ e ] σ)
T[_]-Value SrcBase.V-` Vσ = Vσ _
T[_]-Value SrcBase.V-K Vσ = SoupRed.V-K
T[_]-Value SrcBase.V-λ Vσ = SoupRed.V-λ
T[_]-Value (SrcBase.V-⊗ V₁ V₂) Vσ = SoupRed.V-⊗ (T[_]-Value V₁ Vσ) (T[_]-Value V₂ Vσ)
T[_]-Value (SrcBase.V-⊕ V) Vσ = SoupRed.V-⊕ (T[_]-Value V Vσ)

Tᶠ[_] : (E : SrcBase.Frame n) {σ : TS.Env n n′} → ValueEnv σ → SoupRed.Frame n′
Tᶠ[ SrcBase.app₁ e d V? ] {σ = σ} Vσ = SoupRed.app₁ (TS.T[ e ] σ) d λ eq → T[_]-Value (V? eq) Vσ
Tᶠ[ SrcBase.app₂ e d V? ] {σ = σ} Vσ = SoupRed.app₂ (TS.T[ e ] σ) d λ eq → T[_]-Value (V? eq) Vσ
Tᶠ[ SrcBase.□⊗ e ] {σ = σ} Vσ = SoupRed.□⊗ (TS.T[ e ] σ)
Tᶠ[ V SrcBase.⊗□ ] Vσ = T[_]-Value V Vσ SoupRed.⊗□
Tᶠ[ SrcBase.□; e ] {σ = σ} Vσ = SoupRed.□; (TS.T[ e ] σ)
Tᶠ[ SrcBase.`let-`in e ] {σ = σ} Vσ = SoupRed.`let-`in (TS.T[ e ] (TS.liftEnv σ))
Tᶠ[ SrcBase.`let⊗-`in e ] {σ = σ} Vσ = SoupRed.`let⊗-`in (TS.T[ e ] (TS.liftEnv (TS.liftEnv σ)))
Tᶠ[ SrcBase.`inj□ i ] Vσ = SoupRed.`inj□ i
Tᶠ[ SrcBase.`case□`of⟨ e₁ ; e₂ ⟩ ] {σ = σ} Vσ =
  SoupRed.`case□`of⟨ TS.T[ e₁ ] (TS.liftEnv σ) ; TS.T[ e₂ ] (TS.liftEnv σ) ⟩

Tᶠ*[_] : (E : SrcBase.Frame* n) {σ : TS.Env n n′} → ValueEnv σ → SoupRed.Frame* n′
Tᶠ*[ [] ] Vσ = []
Tᶠ*[ E ∷ Es ] Vσ = Tᶠ[ E ] Vσ ∷ Tᶠ*[ Es ] Vσ

T[_]-plugᶠ : (E : SrcBase.Frame n) {e : Src.Tm n} {σ : TS.Env n n′} (Vσ : ValueEnv σ) →
  TS.T[ SrcBase._[_] E e ] σ ≡ SoupRed._[_] (Tᶠ[ E ] {σ = σ} Vσ) (TS.T[ e ] σ)
T[_]-plugᶠ (SrcBase.app₁ e d V?) Vσ = refl
T[_]-plugᶠ (SrcBase.app₂ e d V?) Vσ = refl
T[_]-plugᶠ (SrcBase.□⊗ e) Vσ = refl
T[_]-plugᶠ (V SrcBase.⊗□) Vσ = refl
T[_]-plugᶠ (SrcBase.□; e) Vσ = refl
T[_]-plugᶠ (SrcBase.`let-`in e) Vσ = refl
T[_]-plugᶠ (SrcBase.`let⊗-`in e) Vσ = refl
T[_]-plugᶠ (SrcBase.`inj□ i) Vσ = refl
T[_]-plugᶠ (SrcBase.`case□`of⟨ e₁ ; e₂ ⟩) Vσ = refl

T[_]-plugᶠ* : (E : SrcBase.Frame* n) {e : Src.Tm n} {σ : TS.Env n n′} (Vσ : ValueEnv σ) →
  TS.T[ SrcBase._[_]* E e ] σ ≡ SoupRed._[_]* (Tᶠ*[ E ] {σ = σ} Vσ) (TS.T[ e ] σ)
T[_]-plugᶠ* [] Vσ = refl
T[_]-plugᶠ* (E ∷ Es) Vσ =
  T[_]-plugᶠ E Vσ
  ■ cong (λ t → SoupRed._[_] (Tᶠ[ E ] {σ = _} Vσ) t) (T[_]-plugᶠ* Es Vσ)

T[_]-─→ : ∀ {n n′} {σ : TS.Env n n′} {e e′ : Src.Tm n} →
  ValueEnv σ → e SrcRed.─→ e′ → TS.T[ e ] σ SoupRed.─→ TS.T[ e′ ] σ
T[_]-─→ {σ = σ} {e = e} Vσ red with e | red
... | (Src.ƛ e₁) Src.·⟨ d ⟩ e₂ | SrcRed.E-App V =
  subst (λ rhs → TS.T[ (Src.ƛ e₁) Src.·⟨ d ⟩ e₂ ] σ SoupRed.─→ rhs)
    (sym (T[_]-⦅⦆ e₁ e₂ σ))
    (SoupRed.E-App (T[_]-Value V Vσ))
... | e₁ Src.; e₂ | SrcRed.E-Seq V =
  SoupRed.E-Seq (T[_]-Value V Vσ)
... | Src.`let e₁ `in e₂ | SrcRed.E-Let V =
  subst (λ rhs → TS.T[ Src.`let e₁ `in e₂ ] σ SoupRed.─→ rhs)
    (sym (T[_]-⦅⦆ e₂ e₁ σ))
    (SoupRed.E-Let (T[_]-Value V Vσ))
... | Src.`let⊗ (e₁ Src.⊗ e₂) `in e | SrcRed.E-PairElim V₁ V₂ =
  subst (λ rhs → TS.T[ Src.`let⊗ (e₁ Src.⊗ e₂) `in e ] σ SoupRed.─→ rhs)
    pairEq
    (SoupRed.E-PairElim (T[_]-Value V₁ Vσ) (T[_]-Value V₂ Vσ))
  where
  pairEq :
    SoupRed.subst₀ (TS.T[ e₂ ] σ)
      (SoupRed.subst₀ (Soup.wk (TS.T[ e₁ ] σ))
        (TS.T[ e ] (TS.liftEnv (TS.liftEnv σ))))
    ≡ TS.T[ Src._⋯_ (Src._⋯_ e (Src.⦅ Src.wk e₁ ⦆)) (Src.⦅ e₂ ⦆) ] σ
  pairEq =
    cong (λ b → SoupRed.subst₀ (TS.T[ e₂ ] σ) b)
      (cong (λ t → SoupRed.subst₀ t (TS.T[ e ] (TS.liftEnv (TS.liftEnv σ)))) (sym (T[_]-wk e₁ σ))
       ■ sym (T[_]-⦅⦆ e (Src.wk e₁) (TS.liftEnv σ)))
    ■ sym (T[_]-⦅⦆ (Src._⋯_ e (Src.⦅ Src.wk e₁ ⦆)) e₂ σ)
... | Src.`case Src.`inj true e `of⟨ e₁ ; e₂ ⟩ | SrcRed.E-SumElim {i = true} V =
  subst (λ rhs → TS.T[ Src.`case Src.`inj true e `of⟨ e₁ ; e₂ ⟩ ] σ SoupRed.─→ rhs)
    (sym (T[_]-⦅⦆ e₁ e σ))
    (SoupRed.E-SumElim (T[_]-Value V Vσ))
... | Src.`case Src.`inj false e `of⟨ e₁ ; e₂ ⟩ | SrcRed.E-SumElim {i = false} V =
  subst (λ rhs → TS.T[ Src.`case Src.`inj false e `of⟨ e₁ ; e₂ ⟩ ] σ SoupRed.─→ rhs)
    (sym (T[_]-⦅⦆ e₂ e σ))
    (SoupRed.E-SumElim (T[_]-Value V Vσ))
... | Src.μ e | SrcRed.E-Unfold =
  subst (λ rhs → TS.T[ Src.μ e ] σ SoupRed.─→ rhs)
    (sym (T[_]-⦅⦆ e (Src.μ e) σ))
    SoupRed.E-Unfold

T[_]-⋯→ : ∀ {n n′} {σ : TS.Env n n′} {e e′ : Src.Tm n} →
  ValueEnv σ → e SrcRed.⋯→ e′ → TS.T[ e ] σ SoupRed.⋯→ TS.T[ e′ ] σ
T[_]-⋯→ Vσ (SrcRed.E-□ red) = SoupRed.E-□ (T[_]-─→ Vσ red)
T[_]-⋯→ Vσ (SrcRed.E-Ctx E red) =
  subst₂ SoupRed._⋯→_
    (sym (T[_]-plugᶠ E Vσ))
    (sym (T[_]-plugᶠ E Vσ))
    (SoupRed.E-Ctx (Tᶠ[ E ] Vσ) (T[_]-⋯→ Vσ red))
