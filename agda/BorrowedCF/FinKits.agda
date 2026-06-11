{-# OPTIONS --rewriting #-}

module BorrowedCF.FinKits where

open import BorrowedCF.Prelude hiding (id; _++_) renaming (_■_ to trans)
open ≡-Reasoning

private variable
  m m₁ m₂ n n₁ n₂ n₃ m′ n′ : ℕ

Scoped = ℕ → Set

record Syntax : Set₁ where
  field  Tm           : Scoped
         `_           : 𝔽 n → Tm n
         `-injective  : {x y : 𝔽 n} → ` x ≡ ` y → x ≡ y

  private variable
    x y z x₁ x₂ : 𝔽 n

  variable 𝓕 𝓕₁ 𝓕₂ : Scoped

  record Kit (𝓕 : Scoped) : Set where
    field  id/`            : 𝔽 n → 𝓕 n
           `/id            : 𝓕 n → Tm n
           wk              : 𝓕 n → 𝓕 (suc n)
           `/`-is-`        : (x : 𝔽 n) → `/id (id/` x) ≡ ` x
           id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
           `/id-injective  : {x/t₁ x/t₂ : 𝓕 n} → `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
           wk-id/`         : (x : 𝔽 n) → wk (id/` x) ≡ id/` (suc x)

    infix 4 _→ₖ_
    _→ₖ_ : ℕ → ℕ → Set
    m →ₖ n = 𝔽 m → 𝓕 n

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

    weaken*~↑ʳ : ∀ m → weaken* {n} m ≗ id/` ∘ (m ↑ʳ_)
    weaken*~↑ʳ zero x = refl
    weaken*~↑ʳ (suc m) x = trans (cong wk (weaken*~↑ʳ m x)) (wk-id/` (m ↑ʳ x))

    infixl 8 _↑*_
    _↑*_ : n₁ →ₖ n₂ → ∀ m → (m + n₁) →ₖ (m + n₂)
    ϕ ↑* zero  = ϕ
    ϕ ↑* suc m = ϕ ↑* m ↑

    id↑ : {ϕ : n →ₖ n} → ϕ ≗ id → ϕ ↑ ≗ id
    id↑ eq zero = refl
    id↑ eq (suc x) = trans (cong wk (eq x)) (wk-id/` x)

    id↑* : ∀ m {ϕ : n →ₖ n} → ϕ ≗ id → ϕ ↑* m ≗ id
    id↑* zero eq = eq
    id↑* (suc m) eq = id↑ (id↑* m eq)

    _~↑ : {ϕ₁ ϕ₂ : m →ₖ n} → ϕ₁ ≗ ϕ₂ → ϕ₁ ↑ ≗ ϕ₂ ↑
    (eq ~↑) zero = refl
    (eq ~↑) (suc x) = cong wk (eq x)

    _~↑*_ : {ϕ₁ ϕ₂ : m →ₖ n} → ϕ₁ ≗ ϕ₂ → ∀ m → ϕ₁ ↑* m ≗ ϕ₂ ↑* m
    eq ~↑* zero = eq
    eq ~↑* suc m = (eq ~↑* m) ~↑

    wkˡ : ∀ m → n →ₖ m + n
    wkˡ m x = id/` (m ↑ʳ x)

    wkʳ : ∀ m → n →ₖ n + m
    wkʳ m x = id/` (x ↑ˡ m)

  open Kit ⦃ … ⦄ public

  infix 4 _–[_]→_

  𝓕[_] : Kit 𝓕 → Scoped
  𝓕[_] {𝓕} K = 𝓕

  _–[_]→_ : ℕ → Kit 𝓕 → ℕ → Set
  m –[ K ]→ n = Kit._→ₖ_ K m n

  record Traversal : Set₁ where
    infixl 5 _⋯_ _⋯ᵣ_ _⋯ₛ_
    field  _⋯_    : ⦃ K : Kit 𝓕 ⦄ → Tm m → m –[ K ]→ n → Tm n
           ⋯-var  : ⦃ K : Kit 𝓕 ⦄ (x : 𝔽 m) (ϕ : m –[ K ]→ n) → (` x) ⋯ ϕ ≡ `/id (ϕ x)
           ⋯-id   : ⦃ K : Kit 𝓕 ⦄ (t : Tm n) {ϕ : n –[ K ]→ n} → ϕ ≗ id → t ⋯ ϕ ≡ t
           ⋯-cong : ⦃ K : Kit 𝓕 ⦄ (t : Tm m) {ϕ₁ ϕ₂ : m –[ K ]→ n} → ϕ₁ ≗ ϕ₂ → t ⋯ ϕ₁ ≡ t ⋯ ϕ₂

    instance
      Kᵣ : Kit 𝔽
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
      Wᵣ = record { wk-`/id = λ x → ⋯-var x weaken }
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

      &/⋯-& : (x : 𝔽 m) (ϕ : m –[ K₂ ]→ n) → `/id (id/` ⦃ K₁ ⦄ x &/⋯ ϕ) ≡ `/id (ϕ x)
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
        (((ϕ₁ ·ₖ ϕ₂) ↑* m) ↑) x         ≡⟨ (dist-↑*-· m ϕ₁ ϕ₂ ~↑) x ⟩
        ((ϕ₁ ↑* m ·ₖ ϕ₂ ↑* m) ↑) x      ≡⟨ dist-↑-· (ϕ₁ ↑* m) (ϕ₂ ↑* m) x ⟩
        (ϕ₁ ↑* m ↑ ·ₖ ϕ₂ ↑* m ↑) x      ≡⟨⟩
        (ϕ₁ ↑* suc m ·ₖ ϕ₂ ↑* suc m) x  ∎

    infix 6 _·[_]_
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
        t ⋯ (ϕ ·ₖ weaken)    ≡⟨ ⋯-cong t (↑-wk ϕ) ⟩
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

      ⋯-congᶜ : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ W₂ : WkKit K₂ ⦄
        ⦃ C₁ₛ : CKit K₁ Kₛ Kₛ ⦄ ⦃ C₂ₛ : CKit K₂ Kₛ Kₛ ⦄ ⦃ C₁ᵣ : CKit K₁ Kᵣ K₁ ⦄ ⦃ C₂ᵣ : CKit K₂ Kᵣ K₂ ⦄
        (t : Tm m) {ϕ₁ : m –[ K₁ ]→ n} {ϕ₂ : m –[ K₂ ]→ n} → `/id ∘ ϕ₁ ≗ `/id ∘ ϕ₂ → t ⋯ ϕ₁ ≡ t ⋯ ϕ₂
      ⋯-congᶜ ⦃ K₁ ⦄ ⦃ K₂ ⦄ t {ϕ₁} {ϕ₂} eq =
        t ⋯ ϕ₁         ≡⟨ ⋯-id _ (λ _ → refl) ⟨
        t ⋯ ϕ₁ ⋯ idₛ   ≡⟨ fusion t ϕ₁ id ⟩
        t ⋯ ϕ₁ ·ₖ idₛ  ≡⟨ ⋯-cong t (λ x → trans (&/⋯-⋯ (ϕ₁ x) `_)
                                        $ trans (sym (trans (⋯-var ⦃ K₁ ⦄ x ϕ₁) (sym (⋯-id (`/id (ϕ₁ x)) (λ _ → refl)))))
                                        $ &/⋯-& ⦃ Cₛ ⦄ x ϕ₁) ⟩
        t ⋯ `/id ∘ ϕ₁  ≡⟨ ⋯-cong t eq ⟩
        t ⋯ `/id ∘ ϕ₂  ≡⟨ ⋯-cong t (λ x → trans (&/⋯-⋯ (ϕ₂ x) `_)
                                        $ trans (sym (trans (⋯-var ⦃ K₂ ⦄ x ϕ₂) (sym (⋯-id (`/id (ϕ₂ x)) (λ _ → refl)))))
                                        $ &/⋯-& ⦃ Cₛ ⦄ x ϕ₂) ⟨
        t ⋯ ϕ₂ ·ₖ idₛ  ≡⟨ fusion t ϕ₂ idₛ ⟨
        t ⋯ ϕ₂ ⋯ idₛ   ≡⟨ ⋯-id _ (λ _ → refl) ⟩
        t ⋯ ϕ₂         ∎

      ↑*-wk : ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄
              (ϕ : n₁ –[ K ]→ n₂) (m : ℕ) → ϕ ·ₖ weaken* m ≗ weaken* m ·ₖ ϕ ↑* m
      ↑*-wk ⦃ K ⦄ ϕ zero x = `/id-injective (
        `/id ((ϕ ·ₖ weaken* zero) x)  ≡⟨⟩
        `/id (ϕ x &/⋯ id)             ≡⟨ &/⋯-⋯ (ϕ x) id ⟩
        `/id (ϕ x) ⋯ id               ≡⟨ ⋯-id (`/id (ϕ x)) (λ _ → refl) ⟩
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
        `/id ((ϕ ·ₖ weaken* m) x) ⋯ weakenᵣ             ≡⟨ cong (λ z → `/id z ⋯ weakenᵣ) (↑*-wk ϕ m x) ⟩
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
        t ⋯ (ϕ ·ₖ weaken* m)       ≡⟨ ⋯-cong t (↑*-wk ϕ m) ⟩
        t ⋯ (weaken* m ·ₖ ϕ ↑* m)  ≡⟨ sym (fusion t (weaken* m) (ϕ ↑* m)) ⟩
        t ⋯ weaken* m ⋯ ϕ ↑* m     ∎

      wkʳ-cancels-↑* : ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ C : CKit K₁ K₂ K ⦄ →
        ∀ m (σ : n –[ K₂ ]→ n′) → wkʳ n ·[ C ] σ ↑* m ≗ wkʳ n′
      wkʳ-cancels-↑* {n = n} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ C ⦄ (suc m) σ zero = `/id-injective ⦃ K ⦄ $
        `/id ⦃ K ⦄ ((wkʳ n ·[ C ] σ ↑* suc m) zero)         ≡⟨⟩
        `/id ⦃ K ⦄ (CKit._&/⋯_ C (id/` zero) (σ ↑* suc m))  ≡⟨ &/⋯-& ⦃ C ⦄ zero (σ ↑* suc m) ⟩
        `/id ⦃ K₂ ⦄ (id/` ⦃ K₂ ⦄ zero)                      ≡⟨ `/`-is-` ⦃ K₂ ⦄ zero ⟩
        ` zero                                              ≡⟨ `/`-is-` ⦃ K ⦄ zero ⟨
        `/id ⦃ K ⦄ (id/` ⦃ K ⦄ zero)                        ∎
      wkʳ-cancels-↑* {n = n} {n′} ⦃ K₁ ⦄ ⦃ K₂ ⦄ ⦃ K ⦄ ⦃ C ⦄ (suc m) σ (suc x) = `/id-injective ⦃ K ⦄ $
        `/id ⦃ K ⦄ ((wkʳ n ·[ C ] σ ↑* suc m) (suc x))          ≡⟨⟩
        `/id ⦃ K ⦄ (CKit._&/⋯_ C (wkʳ n (suc x)) (σ ↑* suc m))  ≡⟨ &/⋯-& ⦃ C ⦄ (suc x ↑ˡ n) (σ ↑* suc m) ⟩
        `/id ⦃ K₂ ⦄ ((σ ↑* suc m) (suc x ↑ˡ n))                 ≡⟨⟩
        `/id ⦃ K₂ ⦄ (wk ((σ ↑* m) (wkʳ n x)))                   ≡⟨ cong (`/id ⦃ K₂ ⦄ ∘ wk) (wkʳ-cancels-↑* m σ x) ⟩
        `/id ⦃ K₂ ⦄ (wk (wkʳ n′ x))                             ≡⟨ cong (`/id ⦃ K₂ ⦄) (wk-id/` (wkʳ n′ x)) ⟩
        `/id ⦃ K₂ ⦄ (id/` ⦃ K₂ ⦄ (wkʳ n′ (suc x)))              ≡⟨ `/`-is-` ⦃ K₂ ⦄ _ ⟩
        ` (suc x ↑ˡ n′)                                         ≡⟨ `/`-is-` ⦃ K ⦄ _ ⟨
        `/id ⦃ K ⦄ (wkʳ n′ (suc x))                             ∎

      wk-cancels-⦅⦆ : ⦃ K : Kit 𝓕 ⦄ (x/t : 𝓕[ K ] m) → weakenᵣ ·ₖ ⦅ x/t ⦆ ≗ id
      wk-cancels-⦅⦆ ⦃ K ⦄ x/t x = `/id-injective (&/⋯-& ⦃ Cᵣ ⦃ K ⦄ ⦄ (suc x) ⦅ x/t ⦆)

      wk-cancels-⦅⦆-⋯ : ⦃ K : Kit 𝓕 ⦄ (t : Tm n) (x/t : 𝓕[ K ] n) →
                         t ⋯ weaken ⋯ ⦅ x/t ⦆ ≡ t
      wk-cancels-⦅⦆-⋯ t x/t =
        t ⋯ weaken ⋯ ⦅ x/t ⦆     ≡⟨ fusion t weaken ⦅ x/t ⦆ ⟩
        t ⋯ (weaken ·ₖ ⦅ x/t ⦆)  ≡⟨ ⋯-id t (wk-cancels-⦅⦆ x/t) ⟩
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
        t ⋯ (⦅ x/t ⦆ ·ₖ ϕ)            ≡⟨ ⋯-cong t (dist-↑-⦅⦆ x/t ϕ) ⟩
        t ⋯ (ϕ ↑ ·ₖ ⦅ (x/t &/⋯ ϕ) ⦆)  ≡⟨ sym (fusion t (ϕ ↑) ⦅ x/t &/⋯ ϕ ⦆ ) ⟩
        t ⋯ ϕ ↑ ⋯ ⦅ (x/t &/⋯ ϕ) ⦆     ∎

      conv-⋯ᵣₛ : (x : Tm m) {ρ : m →ᵣ n} → x ⋯ₛ `_ ∘ ρ ≡ x ⋯ᵣ ρ
      conv-⋯ᵣₛ x = ⋯-congᶜ x λ x₁ → refl

      swapᵣ : ∀ m₁ m₂ {n} → m₁ + m₂ + n →ᵣ m₂ + m₁ + n
      swapᵣ m₁ m₂ = Fin.join _ _ ∘ Sum.map₁ (Fin.swap m₁) ∘ Fin.splitAt (m₁ + m₂)

      module _ {a} {A : Set a} where
        open import Data.Vec.Functional

        private Ctx = Vector A

        ++-swapᵣ : (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) {Γ : Ctx n} → ((Γ₂ ++ Γ₁) ++ Γ) ∘ swapᵣ m₁ m₂ ≗ (Γ₁ ++ Γ₂) ++ Γ
        ++-swapᵣ {m₁}{m₂} Γ₁ Γ₂ {Γ} x
          with Fin.splitAt (m₁ + m₂) x
        ... | inj₂ xₙ = cong [ Γ₂ ++ Γ₁ , Γ ] (Fin.splitAt-↑ʳ (m₂ + m₁) _ xₙ)
        ... | inj₁ xₘ
          with Fin.splitAt m₁ xₘ
        ... | inj₁ x₁ = trans (cong [ Γ₂ ++ Γ₁ , Γ ] (Fin.splitAt-↑ˡ (m₂ + m₁) (m₂ ↑ʳ x₁) _)) (cong [ Γ₂ , Γ₁ ] (Fin.splitAt-↑ʳ m₂ _ x₁))
        ... | inj₂ x₂ = trans (cong [ Γ₂ ++ Γ₁ , Γ ] (Fin.splitAt-↑ˡ (m₂ + m₁) (x₂ ↑ˡ m₁) _)) (cong [ Γ₂ , Γ₁ ] (Fin.splitAt-↑ˡ m₂ x₂ _))

      assocSwapᵣ : ∀ a b {n} → a + (b + n) →ᵣ b + (a + n)
      assocSwapᵣ a b {n} = Fin.cast (+-assoc b a n) ∘ swapᵣ a b ∘ Fin.cast (sym (+-assoc a b n))

      wk-swap : ∀ a b {n} → weaken* (a + b) ·ₖ swapᵣ a b {n} ≗ weaken* ⦃ Kᵣ ⦄ (b + a)
      wk-swap a b x rewrite
        weaken*~↑ʳ ⦃ Kᵣ ⦄ (a + b) x
          | Fin.splitAt-↑ʳ (a + b) _ x
          | weaken*~↑ʳ ⦃ Kᵣ ⦄ (b + a) x
          = refl

      wk-swap-⋯ : ∀ m₁ m₂ {n} (x : Tm n) → x ⋯ᵣ weaken* (m₁ + m₂) ⋯ᵣ swapᵣ m₁ m₂ ≡ x ⋯ᵣ weaken* (m₂ + m₁)
      wk-swap-⋯ m₁ m₂ x = trans (fusion x _ _) (⋯-cong x (wk-swap m₁ m₂))

      module _ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ where
        &/⋯-wk∘weaken : ∀ m (x/t : 𝓕[ K ] n) →
          wk ⦃ K ⦄ (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ≡ x/t &/⋯ weaken* ⦃ Kᵣ ⦄ (suc m)
        &/⋯-wk∘weaken m x/t = `/id-injective $
          `/id ⦃ K ⦄ (wk (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m)) ≡⟨ wk-`/id (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ⟨
          `/id ⦃ K ⦄ (x/t &/⋯ weaken* ⦃ Kᵣ ⦄ m) ⋯ weakenᵣ ≡⟨ cong (_⋯ weakenᵣ) (&/⋯-⋯ x/t (weaken* m)) ⟩
          `/id ⦃ K ⦄ x/t ⋯ weaken* m ⋯ weakenᵣ ≡⟨ fusion (`/id x/t) (weaken* m) weakenᵣ ⟩
          `/id ⦃ K ⦄ x/t ⋯ weaken* (suc m) ≡⟨ &/⋯-⋯ x/t (weaken* (suc m)) ⟨
          `/id ⦃ K ⦄ (x/t &/⋯ weaken* (suc m)) ∎

        ↑*∼id/wk-splitAt : ∀ (ϕ : n₁ –[ K ]→ n₂) m →
          ϕ ↑* m ≗ [ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ m ] ∘ Fin.splitAt m
        ↑*∼id/wk-splitAt ϕ zero x = `/id-injective $
          `/id ((ϕ ↑* zero) x)    ≡⟨⟩
          `/id (ϕ x)              ≡⟨ ⋯-id (`/id (ϕ x)) (λ _ → refl) ⟨
          `/id (ϕ x) ⋯ (λ y → y)  ≡⟨ &/⋯-⋯ (ϕ x) (λ y → y) ⟨
          `/id (ϕ x &/⋯ λ y → y)  ∎
        ↑*∼id/wk-splitAt ϕ (suc m) zero = refl
        ↑*∼id/wk-splitAt {n₁ = n₁} {n₂} ϕ (suc m) (suc x) = `/id-injective $
          `/id ⦃ K ⦄ ((ϕ ↑* suc m) (suc x))  ≡⟨⟩
          `/id ⦃ K ⦄ (wk ((ϕ ↑* m) x))       ≡⟨ cong (`/id ∘ wk) (↑*∼id/wk-splitAt ϕ m x) ⟩
          `/id ⦃ K ⦄ (wk ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ m ] (Fin.splitAt m x)))
            ≡⟨ cong (`/id ⦃ K ⦄) ([,]-∘ (wk ⦃ K ⦄) (Fin.splitAt m x)) ⟩
          `/id ⦃ K ⦄ ([ wk ∘ id/` ∘ (_↑ˡ n₂) , wk ∘ (ϕ ·ₖ weaken* m) ] (Fin.splitAt m x))
            ≡⟨ cong (`/id ⦃ K ⦄) ([,]-cong (λ y → wk-id/` (y ↑ˡ _)) (λ y → &/⋯-wk∘weaken m (ϕ y)) (Fin.splitAt m x)) ⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) ∘ suc , ϕ ·ₖ weaken* (suc m) ] (Fin.splitAt m x))
            ≡⟨ cong (`/id ⦃ K ⦄) ([,]-map (Fin.splitAt m x)) ⟨
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (suc m) ] (Sum.map₁ suc (Fin.splitAt m x))) ≡⟨⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (suc m) ] (Fin.splitAt (suc m) (suc x))) ∎

        dist-↑*-swapˡ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
            ≡
          `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n₂) &/⋯ swapᵣ b₁ b₂)
        dist-↑*-swapˡ b₁ b₂ {n₁} {n₂} {ϕ} x =
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
            ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)) ⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (b₂ + b₁) ] (splitAt (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)))
            ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ˡ (b₂ + b₁) (Fin.swap b₁ x) n₁) ⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* (b₂ + b₁) ]′ (inj₁ (Fin.swap b₁ x)))
            ≡⟨⟩
          `/id ⦃ K ⦄ (id/` (Fin.swap b₁ x ↑ˡ n₂))
            ≡⟨ `/`-is-` ⦃ K ⦄ (Fin.swap b₁ x ↑ˡ n₂) ⟩
          ` (Fin.swap b₁ x ↑ˡ n₂)
            ≡⟨⟩
          ` (Fin.join (b₂ + b₁) n₂ (inj₁ (Fin.swap b₁ x)))
            ≡⟨ cong (`_ ∘ Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁)) (Fin.splitAt-↑ˡ (b₁ + b₂) x n₂) ⟨
          ` (Fin.join _ _ (Sum.map₁ (Fin.swap b₁) (Fin.splitAt (b₁ + b₂) (x ↑ˡ n₂))))
            ≡⟨⟩
          ` (swapᵣ b₁ b₂ (x ↑ˡ n₂))
            ≡⟨ &/⋯-& ⦃ C ⦄ (x ↑ˡ n₂) (swapᵣ b₁ b₂) ⟨
          `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (x ↑ˡ n₂) &/⋯ swapᵣ b₁ b₂) ∎

        dist-↑*-swapʳ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
            ≡
          `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (swapᵣ b₁ b₂))
        dist-↑*-swapʳ b₁ b₂ {n₁} {n₂} {ϕ} x =
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
            ≡⟨ cong (`/id ⦃ K ⦄) (↑*∼id/wk-splitAt ϕ (b₂ + b₁) (b₂ + b₁ ↑ʳ x)) ⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ] (Fin.splitAt (b₂ + b₁) (b₂ + b₁ ↑ʳ x)))
            ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ _ , _ ]) (Fin.splitAt-↑ʳ (b₂ + b₁) n₁ x) ⟩
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ n₂) , ϕ ·ₖ weaken* ⦃ Kᵣ ⦄ (b₂ + b₁) ]′ (inj₂ x))
            ≡⟨⟩
          `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₂ + b₁))
            ≡⟨ &/⋯-⋯ (ϕ x) (weaken* (b₂ + b₁)) ⟩
          `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₂ + b₁)
            ≡⟨ ⋯-cong (`/id (ϕ x)) (wk-swap b₁ b₂) ⟨
          `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ·ₖ swapᵣ b₁ b₂
            ≡⟨ fusion (`/id (ϕ x)) (weaken* (b₁ + b₂)) (swapᵣ b₁ b₂) ⟨
          `/id ⦃ K ⦄ (ϕ x) ⋯ weaken* (b₁ + b₂) ⋯ swapᵣ b₁ b₂
            ≡⟨ cong (_⋯ swapᵣ b₁ b₂) (&/⋯-⋯ (ϕ x) (weaken* (b₁ + b₂))) ⟨
          `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂)) ⋯ swapᵣ b₁ b₂
            ≡⟨ &/⋯-⋯ (ϕ x &/⋯ weaken* (b₁ + b₂)) (swapᵣ b₁ b₂) ⟨
          `/id ⦃ K ⦄ (ϕ x &/⋯ weaken* (b₁ + b₂) &/⋯ swapᵣ b₁ b₂)
            ≡⟨⟩
          `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (b₁ + b₂)) x &/⋯ (swapᵣ b₁ b₂)) ∎

        dist-↑*-swap : ∀ m₁ m₂ {n₁ n₂} (ϕ : n₁ –[ K ]→ n₂) →
          swapᵣ m₁ m₂ {n₁} ·[ Cᵣ ] ϕ ↑* (m₂ + m₁) ≗ ϕ ↑* (m₁ + m₂) ·ₖ swapᵣ m₁ m₂ {n₂}
        dist-↑*-swap m₁ m₂ {n₁} {n₂} ϕ x = `/id-injective $
          `/id ⦃ K ⦄ ((swapᵣ m₁ m₂ ·[ Cᵣ ] ϕ ↑* (m₂ + m₁)) x) ≡⟨⟩
          `/id ⦃ K ⦄ (swapᵣ m₁ m₂ x &/⋯ ϕ ↑* (m₂ + m₁))
            ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) z)) (Sum.map₁ (Fin.swap m₁) (Fin.splitAt (m₁ + m₂) x)) ⟩
          [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) (y ↑ˡ n₁)))
          , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) ((m₂ + m₁) ↑ʳ y)))
          ] (Sum.map₁ (Fin.swap m₁) (Fin.splitAt (m₁ + m₂) x))
            ≡⟨ [,]-map (Fin.splitAt (m₁ + m₂) x) ⟩
          [ (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) (Fin.swap m₁ y ↑ˡ n₁)))
          , (λ y → `/id ⦃ K ⦄ ((ϕ ↑* (m₂ + m₁)) ((m₂ + m₁) ↑ʳ y)))
          ] (Fin.splitAt (m₁ + m₂) x)
            ≡⟨ [,]-cong (dist-↑*-swapˡ m₁ m₂) (dist-↑*-swapʳ m₁ m₂) (Fin.splitAt (m₁ + m₂) x) ⟩
          [ (λ y → `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (y ↑ˡ _) &/⋯ swapᵣ m₁ m₂ {n₂}))
          , (λ y → `/id ⦃ K ⦄ ((ϕ ·ₖ weaken* (m₁ + m₂)) y &/⋯ swapᵣ m₁ m₂ {n₂}))
          ] (Fin.splitAt (m₁ + m₂) x)
            ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ (CKit._&/⋯_ C z (swapᵣ m₁ m₂ {n₂}))) (Fin.splitAt (m₁ + m₂) x) ⟨
          `/id ⦃ K ⦄ ([ id/` ∘ (_↑ˡ _) , ϕ ·ₖ weaken* (m₁ + m₂) ] (Fin.splitAt (m₁ + m₂) x) &/⋯ swapᵣ m₁ m₂ {n₂})
            ≡⟨ cong (λ z → `/id (z &/⋯ swapᵣ m₁ m₂)) (↑*∼id/wk-splitAt ϕ (m₁ + m₂) x) ⟨
          `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂)) x &/⋯ swapᵣ m₁ m₂) ≡⟨⟩
          `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂) ·ₖ swapᵣ m₁ m₂) x) ∎

        ↑-subst₂ : ∀ {m₁ m₂ n₁ n₂} (p : m₁ ≡ m₂) (q : n₁ ≡ n₂) (ψ : m₁ –[ K ]→ n₁) →
                   subst₂ (λ p q → p –[ K ]→ q) p q ψ ↑ ≡ subst₂ (λ p q → p –[ K ]→ q) (cong suc p) (cong suc q) (ψ ↑)
        ↑-subst₂ refl refl ψ = refl

        ↑*-assoc : ∀ a b {m n} (ϕ : m –[ K ]→ n) →
                   ϕ ↑* a ↑* b ≡ subst₂ (λ p q → p –[ K ]→ q) (+-assoc b a m) (+-assoc b a n) (ϕ ↑* (b + a))
        ↑*-assoc a zero ϕ = refl
        ↑*-assoc a (suc b) {m} {n} ϕ =
          trans (cong _↑ (↑*-assoc a b ϕ))
                (↑-subst₂ (+-assoc b a m) (+-assoc b a n) (ϕ ↑* (b + a)))

        subst₂-app : ∀ {m₁ m₂ n₁ n₂} (p : m₁ ≡ m₂) (q : n₁ ≡ n₂) (ψ : m₁ –[ K ]→ n₁) (z : 𝔽 m₂) →
                     subst₂ (λ p q → p –[ K ]→ q) p q ψ z ≡ subst 𝓕[ K ] q (ψ (Fin.cast (sym p) z))
        subst₂-app refl refl ψ z = cong ψ (sym (Fin.cast-is-id refl z))

        `/id-subst : ∀ {a b} (eq : a ≡ b) (w : 𝓕[ K ] a) →
                     `/id ⦃ K ⦄ (subst 𝓕[ K ] eq w) ≡ subst Tm eq (`/id ⦃ K ⦄ w)
        `/id-subst refl w = refl

        subst-Tm-cast : ∀ {a b} (eq : a ≡ b) (t : Tm a) → subst Tm eq t ≡ t ⋯ Fin.cast eq
        subst-Tm-cast refl t = sym (⋯-id t (Fin.cast-is-id refl))

        cast·assocSwap : ∀ a b {n} (z : 𝔽 (a + b + n)) →
                         assocSwapᵣ a b {n} (Fin.cast (+-assoc a b n) z) ≡ Fin.cast (+-assoc b a n) (swapᵣ a b z)
        cast·assocSwap a b {n} z =
          cong (λ w → Fin.cast (+-assoc b a n) (swapᵣ a b w))
               (trans (Fin.cast-trans (+-assoc a b n) (sym (+-assoc a b n)) z) (Fin.cast-is-id _ z))

        dist-↑*-assocSwap : ∀ a b {m n} (ϕ : m –[ K ]→ n) →
          assocSwapᵣ a b {m} ·[ Cᵣ ] ϕ ↑* a ↑* b ≗ ϕ ↑* b ↑* a ·ₖ assocSwapᵣ a b {n}
        dist-↑*-assocSwap a b {m} {n} ϕ x =
            cong (λ f → f (assocSwapᵣ a b x)) (↑*-assoc a b ϕ)
          ■ subst₂-app (+-assoc b a m) (+-assoc b a n) (ϕ ↑* (b + a)) (assocSwapᵣ a b x)
          ■ cong (λ z → subst 𝓕[ K ] (+-assoc b a n) ((ϕ ↑* (b + a)) z))
                 (Fin.cast-trans (+-assoc b a m) (sym (+-assoc b a m)) (swapᵣ a b (Fin.cast (sym (+-assoc a b m)) x))
                  ■ Fin.cast-is-id _ (swapᵣ a b (Fin.cast (sym (+-assoc a b m)) x)))
          ■ cong (subst 𝓕[ K ] (+-assoc b a n))
                 (dist-↑*-swap a b ϕ (Fin.cast (sym (+-assoc a b m)) x))
          ■ value-eq ((ϕ ↑* (a + b)) (Fin.cast (sym (+-assoc a b m)) x))
          ■ sym (cong (λ w → w &/⋯ assocSwapᵣ a b {n})
                      (cong (λ f → f x) (↑*-assoc b a ϕ)
                       ■ subst₂-app (+-assoc a b m) (+-assoc a b n) (ϕ ↑* (a + b)) x))
          where
            infixr 1 _■_
            _■_ = trans
            value-eq : (v : 𝓕[ K ] (a + b + n)) →
                       subst 𝓕[ K ] (+-assoc b a n) (v &/⋯ swapᵣ a b {n})
                       ≡ (subst 𝓕[ K ] (+-assoc a b n) v) &/⋯ assocSwapᵣ a b {n}
            value-eq v = `/id-injective (
                `/id-subst (+-assoc b a n) (v &/⋯ swapᵣ a b {n})
              ■ cong (subst Tm (+-assoc b a n)) (&/⋯-⋯ v (swapᵣ a b {n}))
              ■ subst-Tm-cast (+-assoc b a n) (`/id ⦃ K ⦄ v ⋯ swapᵣ a b {n})
              ■ fusion (`/id ⦃ K ⦄ v) (swapᵣ a b {n}) (Fin.cast (+-assoc b a n))
              ■ ⋯-cong (`/id ⦃ K ⦄ v) (λ z → sym (cast·assocSwap a b z))
              ■ sym (fusion (`/id ⦃ K ⦄ v) (Fin.cast (+-assoc a b n)) (assocSwapᵣ a b {n}))
              ■ cong (_⋯ assocSwapᵣ a b {n}) (sym (subst-Tm-cast (+-assoc a b n) (`/id ⦃ K ⦄ v)))
              ■ cong (_⋯ assocSwapᵣ a b {n}) (sym (`/id-subst (+-assoc a b n) v))
              ■ sym (&/⋯-⋯ (subst 𝓕[ K ] (+-assoc a b n) v) (assocSwapᵣ a b {n})))

      record Types : Set₁ where
        -- field ↑ᵗ : ∀ {st} → Sort st → ∃[ st' ] Sort st'

        -- _∶⊢_ : ∀ {t} → List (Sort Var) → Sort t → Set
        -- S ∶⊢ s = S ⊢ proj₂ (↑ᵗ s)

        -- infixr 5 _∷_ _++ᶜ_
        --
        -- data Ctx : List (Sort Var) → Set where
        --   []   : Ctx []
        --   _∷_  : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
        --
        -- _++ᶜ_ : Ctx S₁ → Ctx S₂ → Ctx (S₁ ++ S₂)
        -- [] ++ᶜ Γ′ = Γ′
        -- _++ᶜ_ {S₂ = S₂} (t ∷ Γ) Γ′ = _⋯_ ⦃ Kᵣ ⦄ t (λ x → ∈-++⁺ˡ) ∷ (Γ ++ᶜ Γ′)
        --
        -- lookup : Ctx S → S ∋ s → S ∶⊢ s
        -- lookup (t ∷ Γ) zero     = t ⋯ weaken ⦃ Kᵣ ⦄ _
        -- lookup (t ∷ Γ) (suc x)  = lookup Γ x ⋯ weaken ⦃ Kᵣ ⦄ _
        --
        -- _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
        -- Γ ∋ x ∶ t = lookup Γ x ≡ t

        record Typing : Set₁ where
          infix 4 ⊢_
          field  ⊢_ : Tm n → Set
                 ⊢` : (x : 𝔽 n) → ⊢ ` x
                 Pϕ : Tm n → Set
                 Pϕ-`  : (x : 𝔽 n) → Pϕ (` x)
                 Pϕ-⋯ᵣ : {e : Tm m} {ϕ : m →ᵣ n} → Pϕ e → Pϕ (e ⋯ ϕ)


          Pϕ-`/` : (K : Kit 𝓕) (x : 𝔽 n) → Pϕ (`/id ⦃ K ⦄ (id/` ⦃ K ⦄ x))
          Pϕ-`/` K = subst Pϕ (sym (`/`-is-` ⦃ K ⦄ _)) ∘ Pϕ-`

          Pϕ-wk : (K : Kit 𝓕) ⦃ W : WkKit K ⦄ {e : 𝓕 n} → Pϕ (`/id ⦃ K ⦄ e) → Pϕ (`/id ⦃ K ⦄ (wk ⦃ K ⦄ e))
          Pϕ-wk K = subst Pϕ (wk-`/id _) ∘ Pϕ-⋯ᵣ

          record TKit (K : Kit 𝓕) : Set₁ where
            private instance _ = K
            infix   4  𝓕⊢_  Φ⊢_
            infixl  6  ⊢↑_
            field
              𝓕⊢_ : 𝓕 n → Set
              id/⊢` : (x : 𝔽 n) → 𝓕⊢ id/` x
              ⊢`/id : {e : 𝓕 n} → (x : 𝓕⊢ e) → ⊢ `/id e
              ⊢wk : {e : 𝓕 n} → 𝓕⊢ e → 𝓕⊢ wk e

            Φ⊢_ : m –[ K ]→ n → Set
            Φ⊢ ϕ = ∀ x → 𝓕⊢ ϕ x × Pϕ (`/id (ϕ x))

            ⊢↑_ :  ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ {ϕ : m –[ K ]→ n}
                    → Φ⊢ ϕ → Φ⊢ ϕ ↑
            ⊢↑_ ⊢ϕ zero    = id/⊢` zero , Pϕ-`/` K zero
            ⊢↑_ ⊢ϕ (suc x) = ⊢wk (⊢ϕ x .proj₁) , Pϕ-wk K (⊢ϕ x .proj₂)

            ⊢⦅_⦆ : {x/t : 𝓕 n} → 𝓕⊢ x/t × Pϕ (`/id x/t) → Φ⊢ ⦅ x/t ⦆
            ⊢⦅ ⊢x/t ⦆ zero = ⊢x/t
            ⊢⦅ ⊢x/t ⦆ (suc x) = id/⊢` x , Pϕ-`/` K x

          open TKit ⦃ … ⦄ public

          infixl 5 Φ[_]⊢_
          Φ[_]⊢_ : ∀ {K : Kit 𝓕} → TKit K → m –[ K ]→ n → Set
          Φ[_]⊢_ TK = Φ⊢_ where instance _ = TK

          record TTraversal : Set₁ where
            field _⊢⋯_ : ∀  ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TKit K ⦄
                            ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
                            {e : Tm m} {ϕ : m –[ K ]→ n} →
                         ⊢ e → Φ⊢ ϕ → ⊢ e ⋯ ϕ

            infixl  5  _⊢⋯_  --_⊢⋯ᵣ_  _⊢⋯ₛ_ _⊢⋯[_]_

            instance
              TKᵣ : TKit Kᵣ
              TKᵣ = record
                { 𝓕⊢_ = λ _ → ⊤
                ; ⊢`/id = λ _ → ⊢` _
                }

              TKₛ : TKit Kₛ
              TKₛ = record
                { 𝓕⊢_ = ⊢_
                ; id/⊢` = ⊢`
                ; ⊢`/id = λ ⊢x → ⊢x
                ; ⊢wk = λ x → x ⊢⋯ λ z → _ , Pϕ-` _
                }

            open TKit TKᵣ public using () renaming
              (⊢wk to ⊢wkᵣ; ⊢⦅_⦆ to ⊢⦅_⦆ᵣ)
            open TKit TKₛ public using () renaming
              (⊢wk to ⊢wkₛ; ⊢⦅_⦆ to ⊢⦅_⦆ₛ)

            -- _⊢⋯[_]_ :
            --   {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
            --   Γ₁ ⊢ e ∶ t →
            --   {K : Kit 𝓕} ⦃ W : WkKit K ⦄ ⦃ C₁ : CKit K Kᵣ K ⦄ ⦃ C₂ : CKit K K K ⦄ ⦃ C₃ : CKit K Kₛ Kₛ ⦄
            --   (TK : TKit K) →
            --   {ϕ : S₁ –[ K ]→ S₂} →
            --   ϕ ∶ Γ₁ ⇒[ TK ] Γ₂ →
            --   let instance _ = K in
            --   Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
            -- _⊢⋯[_]_ x {K} TK ⊢ϕ = x ⊢⋯ ⊢ϕ where instance _ = K; instance _ = TK

            -- -- Renaming preserves typing

            -- _⊢⋯ᵣ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
            --           {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ρ : S₁ →ᵣ S₂} →
            --         Γ₁ ⊢ e ∶ t →
            --         ρ ∶ Γ₁ ⇒ᵣ Γ₂ →
            --         Γ₂ ⊢ e ⋯ ρ ∶ t ⋯ ρ
            -- _⊢⋯ᵣ_ = _⊢⋯_

            -- -- Substitution preserves typing

            -- _⊢⋯ₛ_ : ∀ {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
            --           {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ₛ S₂} →
            --         Γ₁ ⊢ e ∶ t →
            --         σ ∶ Γ₁ ⇒ₛ Γ₂ →
            --         Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
            -- _⊢⋯ₛ_ = _⊢⋯_
