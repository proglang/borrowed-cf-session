open import Axiom.Extensionality.Propositional
open import Level using (0ℓ)

module BorrowedCF.FinKits (∼-ext : Extensionality 0ℓ 0ℓ) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; _≗_; module ≡-Reasoning)
open ≡-Reasoning

private variable
  m m₁ m₂ n n₁ n₂ n₃ m′ n′ : ℕ

Scoped = ℕ → Set

record Syntax : Set₁ where
  field  Tm           : Scoped
         `_           : Fin n → Tm n
         `-injective  : {x y : Fin n} → ` x ≡ ` y → x ≡ y

  private variable
    x y z x₁ x₂ : Fin n

  variable 𝓕 𝓕₁ 𝓕₂ : Scoped

  record Kit (𝓕 : Scoped) : Set where
    field  id/`            : Fin n → 𝓕 n
           `/id            : 𝓕 n → Tm n
           wk              : 𝓕 n → 𝓕 (suc n)
           `/`-is-`        : (x : Fin n) → `/id (id/` x) ≡ ` x
           id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
           `/id-injective  : {x/t₁ x/t₂ : 𝓕 n} → `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
           wk-id/`         : (x : Fin n) → wk (id/` x) ≡ id/` (suc x)

    infix 4 _→ₖ_
    _→ₖ_ : ℕ → ℕ → Set
    m →ₖ n = Fin m → 𝓕 n

    id : n →ₖ n
    id x = id/` x

    wkm : m →ₖ n → m →ₖ suc n
    wkm ϕ x = wk (ϕ x)

    infixr 7 _∷ₖ_
    _∷ₖ_ : 𝓕 n → m →ₖ n → suc m →ₖ n
    (x/t ∷ₖ ϕ) zero     = x/t
    (x/t ∷ₖ ϕ) (suc x)  = ϕ x

    infixl 8 _↑
    _↑ : m →ₖ n → suc m →ₖ suc n
    ϕ ↑ = id/` zero ∷ₖ wkm ϕ

    ⦅_⦆ : 𝓕 n → suc n →ₖ n
    ⦅ x/t ⦆ = x/t ∷ₖ id

    weaken : n →ₖ suc n
    weaken = wkm id

    weaken* : (m : ℕ) → n →ₖ m + n
    weaken* zero    = id
    weaken* (suc m) = wkm (weaken* m)

    id↑∼id : (id {n} ↑) ≗ id
    id↑∼id zero    = refl
    id↑∼id (suc x) =
      (id ↑) (suc x)  ≡⟨⟩
      wk (id/` x)     ≡⟨ wk-id/` x ⟩
      id/` (suc x)    ≡⟨⟩
      id (suc x)      ∎

    infixl 8 _↑*_
    _↑*_ : n₁ →ₖ n₂ → ∀ m → (m + n₁) →ₖ (m + n₂)
    ϕ ↑* zero  = ϕ
    ϕ ↑* suc m = ϕ ↑* m ↑

    -- only necessary for `Generics.agda`; not counted for line numbers
    id↑*∼id : ∀ m → id {n} ↑* m ≗ id
    id↑*∼id zero    x = refl
    id↑*∼id (suc m) x =
      (id ↑* m ↑) x  ≡⟨ cong (λ ■ → (■ ↑) x) (∼-ext (id↑*∼id m)) ⟩
      (id ↑) x       ≡⟨ id↑∼id x ⟩
      id x           ∎

  open Kit ⦃ … ⦄ public

  infix 4 _–[_]→_

  𝓕[_] : Kit 𝓕 → Scoped
  𝓕[_] {𝓕} K = 𝓕

  _–[_]→_ : ℕ → Kit 𝓕 → ℕ → Set
  m –[ K ]→ n = Kit._→ₖ_ K m n

  record Traversal : Set₁ where
    infixl 5 _⋯_ _⋯ᵣ_ _⋯ₛ_
    field  _⋯_   : ⦃ K : Kit 𝓕 ⦄ → Tm m → m –[ K ]→ n → Tm n
           ⋯-var : ⦃ K : Kit 𝓕 ⦄ (x : Fin m) (ϕ : m –[ K ]→ n) → (` x) ⋯ ϕ ≡ `/id (ϕ x)
           ⋯-id  : ⦃ K : Kit 𝓕 ⦄ (t : Tm m) → t ⋯ id ⦃ K ⦄ ≡ t

    ⋯-cong : ⦃ K : Kit 𝓕 ⦄ (t : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → t ⋯ ϕ₁ ≡ t ⋯ ϕ₂
    ⋯-cong t ϕ∼ = cong (t ⋯_) (∼-ext ϕ∼)

    ⋯-id∼ : ⦃ K : Kit 𝓕 ⦄ (t : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ id → t ⋯ ϕ ≡ t
    ⋯-id∼ t ϕ∼id = trans (⋯-cong t ϕ∼id) (⋯-id t)

    instance
      Kᵣ : Kit Fin
      Kᵣ = record  { id/`            = λ x → x      ; `/id            = `_
                   ; wk              = λ x → suc x  ; `/`-is-`        = λ x → refl
                   ; id/`-injective  = λ eq → eq    ; `/id-injective  = `-injective
                   ; wk-id/`         = λ x → refl   }

      Kₛ : Kit Tm
      Kₛ = record  { id/`            = `_                             ; `/id            = λ t → t
                   ; wk              = λ t → t ⋯ weaken ⦃ Kᵣ ⦄        ; `/`-is-`        = λ x → refl
                   ; id/`-injective  = `-injective                    ; `/id-injective  = λ eq → eq
                   ; wk-id/`         = λ x → ⋯-var x (weaken ⦃ Kᵣ ⦄)  }

    open Kit Kᵣ public using () renaming
      (_→ₖ_ to infix 4 _→ᵣ_; wkm to wkmᵣ; _∷ₖ_ to _∷ᵣ_; _↑ to _↑ᵣ;
       id to idᵣ; ⦅_⦆ to ⦅_⦆ᵣ; weaken to weakenᵣ)
    open Kit Kₛ public using () renaming
      (_→ₖ_ to infix 4 _→ₛ_; wkm to wkmₛ; _∷ₖ_ to _∷ₛ_; _↑ to _↑ₛ;
       id to idₛ; ⦅_⦆ to ⦅_⦆ₛ; weaken to weakenₛ)

    _⋯ᵣ_ : Tm m → m –[ Kᵣ ]→ n → Tm n
    _⋯ᵣ_ = _⋯_

    _⋯ₛ_ : Tm m → m –[ Kₛ ]→ n → Tm n
    _⋯ₛ_ = _⋯_

    record WkKit (K : Kit 𝓕): Set₁ where
      private instance _ = K
      field wk-`/id : (x/t : 𝓕 n) → `/id x/t ⋯ weakenᵣ ≡ `/id (wk x/t)

    instance
      Wᵣ : WkKit Kᵣ ; Wₛ : WkKit Kₛ
      Wᵣ = record { wk-`/id = λ x → ⋯-var x (weaken) }
      Wₛ = record { wk-`/id = λ t → refl }

    open WkKit ⦃ … ⦄ public

    record CKit  (K₁ : Kit 𝓕₁) (K₂ : Kit 𝓕₂) (K₁⊔K₂ : Kit 𝓕) : Set where
      private instance _ = K₁; _ = K₂; _ = K₁⊔K₂
      infixl 5 _&/⋯_
      field  _&/⋯_     :  𝓕[ K₁ ] m → m –[ K₂ ]→ n → 𝓕[ K₁⊔K₂ ] n
             &/⋯-⋯     :  (x/t : 𝓕[ K₁ ] m) (ϕ : m –[ K₂ ]→ n) →
                          `/id (x/t &/⋯ ϕ) ≡ `/id x/t ⋯ ϕ
             &/⋯-wk-↑  :  (x/t : 𝓕[ K₁ ] m) (ϕ : m –[ K₂ ]→ n) →
                          wk (x/t &/⋯ ϕ) ≡ wk x/t &/⋯ (ϕ ↑)

      infix 6 _·ₖ_
      _·ₖ_ : n₁ –[ K₁ ]→ n₂ → n₂ –[ K₂ ]→ n₃ → n₁ –[ K₁⊔K₂ ]→ n₃
      (ϕ₁ ·ₖ ϕ₂) x = ϕ₁ x &/⋯ ϕ₂

      &/⋯-& : (x : Fin m) (ϕ : m –[ K₂ ]→ n) → `/id (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (ϕ x)
      &/⋯-& x ϕ =
          `/id (id/` x &/⋯ ϕ)       ≡⟨ &/⋯-⋯ (id/` x) ϕ ⟩
          `/id ⦃ K₁ ⦄ (id/` x) ⋯ ϕ  ≡⟨ cong (_⋯ ϕ) (`/`-is-` ⦃ K₁ ⦄ x) ⟩
          ` x ⋯ ϕ                   ≡⟨ ⋯-var ⦃ K₂ ⦄ x ϕ ⟩
          `/id ⦃ K₂ ⦄  (ϕ x)        ∎

      dist-↑-· : (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
                 (ϕ₁ ·ₖ ϕ₂) ↑ ≗ ϕ₁ ↑ ·ₖ ϕ₂ ↑
      dist-↑-· ϕ₁ ϕ₂ x@zero = `/id-injective (
        `/id ⦃ K₁⊔K₂ ⦄ (((ϕ₁ ·ₖ ϕ₂) ↑) x)    ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (id/` zero)           ≡⟨ `/`-is-` ⦃ K₁⊔K₂ ⦄ zero ⟩
        ` zero                               ≡⟨ sym (`/`-is-` ⦃ K₂ ⦄ zero) ⟩
        `/id ⦃ K₂ ⦄ (id/` zero)              ≡⟨⟩
        `/id ⦃ K₂ ⦄ ((ϕ₂ ↑) zero)            ≡⟨ sym (&/⋯-& (id/` zero) (ϕ₂ ↑)) ⟩
        `/id ⦃ K₁⊔K₂ ⦄ (id/` zero &/⋯ ϕ₂ ↑)  ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ ((ϕ₁ ↑) x &/⋯ ϕ₂ ↑)   ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ ((ϕ₁ ↑ ·ₖ ϕ₂ ↑) x)    ∎
        )
      dist-↑-· ϕ₁ ϕ₂ x@(suc y) = `/id-injective (
        `/id ⦃ K₁⊔K₂ ⦄ (((ϕ₁ ·ₖ ϕ₂) ↑) x)      ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk ((ϕ₁ ·ₖ ϕ₂) y))     ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk (ϕ₁ y &/⋯ ϕ₂))      ≡⟨ cong `/id (&/⋯-wk-↑ (ϕ₁ y) ϕ₂) ⟩
        `/id ⦃ K₁⊔K₂ ⦄ (wk (ϕ₁ y) &/⋯ (ϕ₂ ↑))  ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ ((ϕ₁ ↑) x &/⋯ ϕ₂ ↑)     ≡⟨⟩
        `/id ⦃ K₁⊔K₂ ⦄ ((ϕ₁ ↑ ·ₖ ϕ₂ ↑) x)      ∎
        )

      dist-↑*-· : (m : ℕ) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
                  (ϕ₁ ·ₖ ϕ₂) ↑* m ≗ ϕ₁ ↑* m ·ₖ ϕ₂ ↑* m
      dist-↑*-· zero    ϕ₁ ϕ₂ x = refl
      dist-↑*-· (suc m) ϕ₁ ϕ₂ x =
        ((ϕ₁ ·ₖ ϕ₂) ↑* suc m) x         ≡⟨⟩
        (((ϕ₁ ·ₖ ϕ₂) ↑* m) ↑) x         ≡⟨ cong (λ ■ → (■ ↑) x) (∼-ext (dist-↑*-· m ϕ₁ ϕ₂)) ⟩
        ((ϕ₁ ↑* m ·ₖ ϕ₂ ↑* m) ↑) x      ≡⟨ dist-↑-· (ϕ₁ ↑* m) (ϕ₂ ↑* m) x ⟩
        (ϕ₁ ↑* m ↑ ·ₖ ϕ₂ ↑* m ↑) x      ≡⟨⟩
        (ϕ₁ ↑* suc m ·ₖ ϕ₂ ↑* suc m) x  ∎

    _·[_]_ : {K₁ : Kit 𝓕₁} {K₂ : Kit 𝓕₂} {K₁⊔K₂ : Kit 𝓕} →
             n₁ –[ K₁ ]→ n₂ → CKit K₁ K₂ K₁⊔K₂ →
             n₂ –[ K₂ ]→ n₃ → n₁ –[ K₁⊔K₂ ]→ n₃
    ϕ₁ ·[ C ] ϕ₂ = ϕ₁ ·ₖ ϕ₂ where open CKit C

    open CKit ⦃ … ⦄ public

    record CTraversal : Set₁ where
      field fusion : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄
                     ⦃ C : CKit K₁ K₂ K ⦄ (t : Tm n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
                     t ⋯ ϕ₁ ⋯ ϕ₂ ≡ t ⋯ ϕ₁ ·ₖ ϕ₂

      ↑-wk :  ∀  ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit Kᵣ K K ⦄
                 (ϕ : m –[ K ]→ n) → ϕ ·ₖ weaken ≗ weaken ·ₖ ϕ ↑
      ↑-wk {m = m} {n} ϕ x = `/id-injective (
          `/id ((ϕ ·ₖ weaken) x)      ≡⟨⟩
          `/id (ϕ x &/⋯ weaken)       ≡⟨ &/⋯-⋯ (ϕ x) weaken ⟩
          `/id (`/id (ϕ x) ⋯ weaken)  ≡⟨ wk-`/id (ϕ x) ⟩
          `/id ((ϕ ↑) (suc x))        ≡⟨ sym (&/⋯-& (suc x) (ϕ ↑)) ⟩
          `/id (suc x &/⋯ ϕ ↑)        ≡⟨⟩
          `/id (weaken x &/⋯ ϕ ↑)     ≡⟨⟩
          `/id ((weaken ·ₖ ϕ ↑) x)    ∎)

      ⋯-↑-wk : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit Kᵣ K K ⦄
               (t : Tm m) (ϕ : m –[ K ]→ n) →
               t ⋯ ϕ ⋯ weaken ≡ t ⋯ weaken ⋯ ϕ ↑
      ⋯-↑-wk t ϕ =
        t ⋯ ϕ ⋯ weaken       ≡⟨ fusion t ϕ weaken ⟩
        t ⋯ (ϕ ·ₖ weaken)    ≡⟨ cong (t ⋯_) (∼-ext (↑-wk ϕ)) ⟩
        t ⋯ (weaken ·ₖ ϕ ↑)  ≡⟨ sym (fusion t weaken (ϕ ↑)) ⟩
        t ⋯ weaken ⋯ ϕ ↑     ∎

      instance
        Cᵣ : ⦃ K : Kit 𝓕 ⦄ → CKit Kᵣ K K
        Cᵣ = record  { _&/⋯_     = λ x ϕ → ϕ x
                     ; &/⋯-⋯     = λ x ϕ → sym (⋯-var x ϕ)
                     ; &/⋯-wk-↑  = λ x ϕ → refl }
        Cₛ :  ⦃ K : Kit 𝓕 ⦄ ⦃ C : CKit K Kᵣ K ⦄ ⦃ W : WkKit K ⦄ → CKit Kₛ K Kₛ
        Cₛ = record  { _&/⋯_     = λ t ϕ → t ⋯ ϕ
                     ; &/⋯-⋯     = λ t ϕ → refl
                     ; &/⋯-wk-↑  = λ t ϕ → ⋯-↑-wk t ϕ }

      ↑*-wk : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄
              (ϕ : n₁ –[ K ]→ n₂) (m : ℕ) → ϕ ·ₖ weaken* m ≗ weaken* m ·ₖ ϕ ↑* m
      ↑*-wk ⦃ K ⦄ ϕ zero x = `/id-injective (
        `/id ((ϕ ·ₖ weaken* zero) x)  ≡⟨⟩
        `/id (ϕ x &/⋯ id)             ≡⟨ &/⋯-⋯ (ϕ x) id ⟩
        `/id (ϕ x) ⋯ id               ≡⟨ ⋯-id (`/id (ϕ x)) ⟩
        `/id (ϕ x)                    ≡⟨ &/⋯-& ⦃ Cᵣ ⦄ x ϕ ⟨
        `/id (x &/⋯ ϕ)                ≡⟨⟩
        `/id ⦃ K ⦄ ((weaken* zero ·ₖ ϕ ↑* zero) x) ∎)
      ↑*-wk ⦃ K ⦄ ϕ (suc m) x = `/id-injective (
        `/id ((ϕ ·ₖ weaken* (suc m)) x)                 ≡⟨⟩
        `/id (ϕ x &/⋯ weaken* (suc m))                  ≡⟨ &/⋯-⋯ {K₁ = K} {K₂ = Kᵣ} (ϕ x) (weaken* (suc m)) ⟩
        `/id (ϕ x) ⋯ᵣ weaken* (suc m)                   ≡⟨⟩
        `/id (ϕ x) ⋯ᵣ weaken* m ·ₖ weakenᵣ              ≡⟨ fusion (`/id (ϕ x)) (weaken* m) weakenᵣ ⟨
        `/id (ϕ x) ⋯ᵣ weaken* m ⋯ weakenᵣ               ≡⟨ cong (_⋯ weakenᵣ) (&/⋯-⋯ (ϕ x) (weaken* m)) ⟨
        `/id (ϕ x &/⋯ weaken* m) ⋯ weakenᵣ              ≡⟨⟩
        `/id ((ϕ ·ₖ weaken* m) x) ⋯ weakenᵣ             ≡⟨ cong (λ ϕ′ → `/id (ϕ′ x) ⋯ weakenᵣ) (∼-ext (↑*-wk ϕ m)) ⟩
        `/id ⦃ K ⦄ ((weaken* m ·ₖ ϕ ↑* m) x) ⋯ weakenᵣ  ≡⟨⟩
        `/id ⦃ K ⦄ (weaken* m x &/⋯ ϕ ↑* m) ⋯ weakenᵣ   ≡⟨ cong (_⋯ weakenᵣ) (&/⋯-⋯ {K₁ = Kᵣ} (weaken* m x) (ϕ ↑* m)) ⟩
        ` (weaken* m x) ⋯ ϕ ↑* m ⋯ weakenᵣ              ≡⟨ ⋯-↑-wk (` weaken* m x) (ϕ ↑* m) ⟩
        ` (weaken* m x) ⋯ weakenᵣ ⋯ ϕ ↑* suc m          ≡⟨ cong (_⋯ (ϕ ↑* suc m)) (wk-`/id ⦃ Wᵣ ⦄ (weaken* m x)) ⟩
        ` (weaken* (suc m) x) ⋯ ϕ ↑* suc m              ≡⟨ &/⋯-⋯ {K₁ = Kᵣ} (wk (weaken* m x)) (ϕ ↑* suc m) ⟨
        `/id ⦃ K ⦄ (weaken* (suc m) x &/⋯ ϕ ↑* suc m)   ≡⟨⟩
        `/id ⦃ K ⦄ ((weaken* (suc m) ·ₖ ϕ ↑* suc m) x)  ∎)

      ⋯-↑*-wk : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄
                (t : Tm n₁) (ϕ : n₁ –[ K ]→ n₂) (m : ℕ) →
                t ⋯ ϕ ⋯ᵣ weaken* m ≡ t ⋯ᵣ weaken* m ⋯ ϕ ↑* m
      ⋯-↑*-wk t ϕ m =
        t ⋯ ϕ ⋯ weaken* m          ≡⟨ fusion t ϕ (weaken* m) ⟩
        t ⋯ (ϕ ·ₖ weaken* m)       ≡⟨ cong (t ⋯_) (∼-ext (↑*-wk ϕ m)) ⟩
        t ⋯ (weaken* m ·ₖ ϕ ↑* m)  ≡⟨ sym (fusion t (weaken* m) (ϕ ↑* m)) ⟩
        t ⋯ weaken* m ⋯ ϕ ↑* m     ∎

      wk-cancels-⦅⦆ : ⦃ K : Kit 𝓕 ⦄ (x/t : 𝓕[ K ] m) → weakenᵣ ·ₖ ⦅ x/t ⦆ ≗ id
      wk-cancels-⦅⦆ ⦃ K ⦄ x/t x = `/id-injective (&/⋯-& ⦃ Cᵣ ⦃ K ⦄ ⦄ (suc x) ⦅ x/t ⦆)

      wk-cancels-⦅⦆-⋯ : ⦃ K : Kit 𝓕 ⦄ (t : Tm n) (x/t : 𝓕[ K ] n) →
                         t ⋯ weaken ⋯ ⦅ x/t ⦆ ≡ t
      wk-cancels-⦅⦆-⋯ t x/t =
        t ⋯ weaken ⋯ ⦅ x/t ⦆     ≡⟨ fusion t weaken ⦅ x/t ⦆ ⟩
        t ⋯ (weaken ·ₖ ⦅ x/t ⦆)  ≡⟨ cong (t ⋯_) (∼-ext (wk-cancels-⦅⦆ x/t)) ⟩
        t ⋯ id                   ≡⟨ ⋯-id t ⟩
        t                        ∎

      dist-↑-⦅⦆ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₂ : WkKit K₂ ⦄
                  ⦃ C₁ : CKit K₁ K₂ K ⦄ ⦃ C₂ : CKit K₂ K K ⦄
                  (x/t : 𝓕[ K₁ ] m) (ϕ : m –[ K₂ ]→ n) →
                  ⦅ x/t ⦆ ·ₖ ϕ ≗ ϕ ↑ ·ₖ ⦅ x/t &/⋯ ϕ ⦆
      dist-↑-⦅⦆ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ x@zero = `/id-injective (
          `/id ((⦅ x/t ⦆ ·ₖ ϕ) x)                    ≡⟨⟩
          `/id (x/t &/⋯ ϕ)                           ≡⟨⟩
          `/id (⦅ (x/t &/⋯ ϕ) ⦆ zero)                ≡⟨ sym (&/⋯-& ⦃ C₂ ⦄ zero ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
          `/id (id/` ⦃ K₂ ⦄ zero &/⋯ ⦅ x/t &/⋯ ϕ ⦆)  ≡⟨⟩
          `/id ((ϕ ↑ ·ₖ ⦅ x/t &/⋯ ϕ ⦆) x)            ∎)
      dist-↑-⦅⦆ ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ W₂ ⦄ ⦃ C₁ ⦄ ⦃ C₂ ⦄ x/t ϕ x@(suc y) = `/id-injective (
          `/id ((⦅ x/t ⦆ ·ₖ ϕ) x)               ≡⟨⟩
          `/id (id/` ⦃ K₁ ⦄ y &/⋯ ϕ)            ≡⟨ &/⋯-& ⦃ C₁ ⦄ y ϕ ⟩
          `/id (ϕ y)                            ≡⟨ sym (wk-cancels-⦅⦆-⋯ (`/id (ϕ y)) (x/t &/⋯ ϕ)) ⟩
          `/id (ϕ y) ⋯ weaken ⋯ ⦅ x/t &/⋯ ϕ ⦆   ≡⟨ cong (_⋯ ⦅ x/t &/⋯ ϕ ⦆) (wk-`/id (ϕ y)) ⟩
          `/id (wk (ϕ y)) ⋯ ⦅ x/t &/⋯ ϕ ⦆       ≡⟨ sym (&/⋯-⋯ (wk (ϕ y)) ⦅ (x/t &/⋯ ϕ) ⦆) ⟩
          `/id (wk (ϕ y) &/⋯ ⦅ x/t &/⋯ ϕ ⦆)     ≡⟨⟩
          `/id ((ϕ ↑ ·ₖ ⦅ x/t &/⋯ ϕ ⦆) x)       ∎)

      dist-↑-⦅⦆-⋯ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ W₂ : WkKit K₂ ⦄
                    ⦃ K : Kit 𝓕 ⦄ ⦃ C₁ : CKit K₁ K₂ K ⦄ ⦃ C₂ : CKit K₂ K K ⦄
                    (t : Tm (suc m)) (x/t : 𝓕[ K₁ ] m) (ϕ : m –[ K₂ ]→ n) →
                     t ⋯ ⦅ x/t ⦆ ⋯ ϕ ≡ t ⋯ ϕ ↑ ⋯ ⦅ x/t &/⋯ ϕ ⦆
      dist-↑-⦅⦆-⋯ t x/t ϕ =
        t ⋯ ⦅ x/t ⦆ ⋯ ϕ               ≡⟨ fusion t ⦅ x/t ⦆ ϕ ⟩
        t ⋯ (⦅ x/t ⦆ ·ₖ ϕ)            ≡⟨ cong (t ⋯_) (∼-ext (dist-↑-⦅⦆ x/t ϕ)) ⟩
        t ⋯ (ϕ ↑ ·ₖ ⦅ (x/t &/⋯ ϕ) ⦆)  ≡⟨ sym (fusion t (ϕ ↑) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
        t ⋯ ϕ ↑ ⋯ ⦅ (x/t &/⋯ ϕ) ⦆     ∎

      -- record Types : Set₁ where
      --   field ↑ᵗ : ∀ {st} → Sort st → ∃[ st' ] Sort st'

      --   _∶⊢_ : ∀ {t} → List (Sort Var) → Sort t → Set
      --   S ∶⊢ s = S ⊢ proj₂ (↑ᵗ s)

      --   infixr 5 _∷_ _++ᶜ_

      --   data Ctx : List (Sort Var) → Set where
      --     []   : Ctx []
      --     _∷_  : S ∶⊢ s → Ctx S → Ctx (s ∷ S)

      --   _++ᶜ_ : Ctx S₁ → Ctx S₂ → Ctx (S₁ ++ S₂)
      --   [] ++ᶜ Γ′ = Γ′
      --   _++ᶜ_ {S₂ = S₂} (t ∷ Γ) Γ′ = _⋯_ ⦃ Kᵣ ⦄ t (λ x → ∈-++⁺ˡ) ∷ (Γ ++ᶜ Γ′)

      --   lookup : Ctx S → S ∋ s → S ∶⊢ s
      --   lookup (t ∷ Γ) zero     = t ⋯ weaken ⦃ Kᵣ ⦄ _
      --   lookup (t ∷ Γ) (suc x)  = lookup Γ x ⋯ weaken ⦃ Kᵣ ⦄ _

      --   _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
      --   Γ ∋ x ∶ t = lookup Γ x ≡ t

      --   record Typing : Set₁ where
      --     field  _⊢_∶_  : ∀ {s : Sort st} → Ctx S → S ⊢ s → S ∶⊢ s → Set
      --            ⊢`     : ∀ {Γ : Ctx S} {x : S ∋ s} {t} → Γ ∋ x ∶ t → Γ ⊢ ` x ∶ t

      --     infix 4 _⊢_∶_

      --     record TKit (K : Kit 𝓕) : Set₁ where
      --       private instance _ = K
      --       infix   4  𝓕∶_  _∶_⇒ₖ_
      --       infixl  6  _⊢↑_
      --       field  𝓕∶_  : Ctx S → S ∋/⊢ s → S ∶⊢ s → Set
      --              id/⊢`    : ∀ {t : S ∶⊢ s} {Γ : Ctx S} → Γ ∋ x ∶ t → Γ ∋/⊢ id/` x ∶ t
      --              ⊢`/id    : ∀ {e : S ∋/⊢ s} {t : S ∶⊢ s} {Γ : Ctx S} → Γ ∋/⊢ e ∶ t → Γ ⊢ `/id e ∶ t
      --              ⊢wk      : ∀ (Γ : Ctx S) (t' : S ∶⊢ s) (e : S ∋/⊢ s') (t : S ∶⊢ s') →
      --                         Γ ∋/⊢ e ∶ t → (t' ∷ Γ) ∋/⊢ wk _ e ∶ (t ⋯ weaken _)

      --       _∶_⇒ₖ_ : S₁ –[ K ]→ S₂ → Ctx S₁ → Ctx S₂ → Set
      --       _∶_⇒ₖ_ {S₁} {S₂} ϕ Γ₁ Γ₂ = ∀ {s₁} (x : S₁ ∋ s₁) (t : S₁ ∶⊢ s₁) →
      --         Γ₁ ∋ x ∶ t → Γ₂ ∋/⊢ (x & ϕ) ∶ (t ⋯ ϕ)

      --       _⊢↑_ :  ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {ϕ : S₁ –[ K ]→ S₂}
      --               → ϕ ∶ Γ₁ ⇒ₖ Γ₂ → (t : S₁ ∶⊢ s) → (ϕ ↑ s) ∶ (t ∷ Γ₁) ⇒ₖ ((t ⋯ ϕ) ∷ Γ₂)
      --       _⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@zero _ refl =
      --         subst (  ((t ⋯ ϕ) ∷ Γ₂) ∋/⊢ (zero & (ϕ ↑ s)) ∶_ )
      --               (  t ⋯ ϕ ⋯ weaken s                 ≡⟨ ⋯-↑-wk t ϕ s ⟩
      --                  t ⋯ weaken s ⋯ (ϕ ↑ s)           ≡⟨⟩
      --                  lookup (t ∷ Γ₁) zero ⋯ (ϕ ↑ s)  ∎ )
      --               (  id/⊢` {x = zero} {Γ = (t ⋯ ϕ) ∷ Γ₂} refl )
      --       _⊢↑_ {S₁} {S₂} {s} {Γ₁} {Γ₂} {ϕ} ⊢ϕ t {sx} x@(suc y) _ refl =
      --         subst (((t ⋯ ϕ) ∷ Γ₂) ∋/⊢ (suc y & (ϕ ↑ s)) ∶_)
      --               (lookup Γ₁ y ⋯ ϕ ⋯ weaken s          ≡⟨ ⋯-↑-wk _ ϕ s ⟩
      --                lookup Γ₁ y ⋯ weaken s ⋯ (ϕ ↑ s)    ≡⟨⟩
      --                lookup (t ∷ Γ₁) (suc y) ⋯ (ϕ ↑ s)  ∎)
      --               (⊢wk _ _ _ _ (⊢ϕ y _ refl))

      --       ⊢⦅_⦆ :  ∀ {s S} {Γ : Ctx S} {x/t : S ∋/⊢ s} {T : S ∶⊢ s} →
      --               Γ ∋/⊢ x/t ∶ T → ⦅ x/t ⦆ ∶ (T ∷ Γ) ⇒ₖ Γ
      --       ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@zero _ refl =
      --         subst (Γ ∋/⊢ t ∶_)
      --               (T                            ≡⟨ sym (wk-cancels-⦅⦆-⋯ T t) ⟩
      --                T ⋯ weaken _ ⋯ ⦅ t ⦆         ≡⟨⟩
      --                lookup (T ∷ Γ) zero ⋯ ⦅ t ⦆  ∎)
      --               ⊢x/t
      --       ⊢⦅_⦆ {s} {S} {Γ} {t} {T} ⊢x/t x@(suc y) _ refl =
      --         subst (Γ ∋/⊢ id/` y ∶_)
      --               (lookup Γ y                      ≡⟨ sym (wk-cancels-⦅⦆-⋯ _ t) ⟩
      --                lookup Γ y ⋯ weaken _ ⋯ ⦅ t ⦆   ≡⟨⟩
      --                lookup (T ∷ Γ) (suc y) ⋯ ⦅ t ⦆  ∎)
      --               (id/⊢` refl)

      --     open TKit ⦃ … ⦄ public

      --     infixl  5  _∶_⇒[_]_
      --     _∶_⇒[_]_ :
      --       ∀ {K : Kit 𝓕} {S₁ S₂} →
      --       S₁ –[ K ]→ S₂ → Ctx S₁ → TKit K → Ctx S₂ → Set
      --     ϕ ∶ Γ₁ ⇒[ TK ] Γ₂ = ϕ ∶ Γ₁ ⇒ₖ Γ₂ where instance _ = TK

      --     record TTraversal : Set₁ where
      --       field _⊢⋯_ : ∀  ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
      --                       ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
      --                       {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
      --                       {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
      --                    Γ₁ ⊢ e ∶ t →
      --                    ϕ ∶ Γ₁ ⇒ₖ Γ₂ →
      --                    Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)

      --       infixl  5  _⊢⋯_  _⊢⋯ᵣ_  _⊢⋯ₛ_ _⊢⋯[_]_

      --       instance
      --         TKᵣ : TKit Kᵣ ; TKₛ : TKit Kₛ
      --         TKᵣ = record  { 𝓕∶_  = _∋_∶_      ; ⊢`/id  = ⊢`
      --                       ; id/⊢`    = λ ⊢x → ⊢x  ; ⊢wk    = λ { Γ t' x t refl → refl } }
      --         TKₛ = record  { 𝓕∶_  = _⊢_∶_  ; ⊢`/id  = λ ⊢x → ⊢x
      --                       ; id/⊢`    = ⊢`     ; ⊢wk    = λ Γ t' e t ⊢e → ⊢e ⊢⋯ ⊢wk Γ t' }
      --       open TKit TKᵣ public using () renaming
      --         (⊢wk to ⊢wkᵣ; _∶_⇒ₖ_ to _∶_⇒ᵣ_; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
      --       open TKit TKₛ public using () renaming
      --         (⊢wk to ⊢wkₛ; _∶_⇒ₖ_ to _∶_⇒ₛ_; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

      --       _⊢⋯[_]_ :
      --         {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
      --         Γ₁ ⊢ e ∶ t →
      --         {K : Kit 𝓕} ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
      --         (TK : TKit K) →
      --         {ϕ : S₁ –[ K ]→ S₂} →
      --         ϕ ∶ Γ₁ ⇒[ TK ] Γ₂ →
      --         let instance _ = K in
      --         Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
      --       _⊢⋯[_]_ x {K} TK ⊢ϕ = x ⊢⋯ ⊢ϕ where instance _ = K; instance _ = TK

      --       -- Renaming preserves typing

      --       _⊢⋯ᵣ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
      --                 {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ρ : S₁ →ᵣ S₂} →
      --               Γ₁ ⊢ e ∶ t →
      --               ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
      --               Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
      --       _⊢⋯ᵣ_ = _⊢⋯_

      --       -- Substitution preserves typing

      --       _⊢⋯ₛ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
      --                 {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ₛ S₂} →
      --               Γ₁ ⊢ e ∶ t →
      --               σ ∶ Γ₁ ⇒ₛ Γ₂ →
      --               Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
      --       _⊢⋯ₛ_ = _⊢⋯_
