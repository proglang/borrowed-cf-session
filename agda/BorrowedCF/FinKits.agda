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

  variable 𝓕 𝓕₁ 𝓕₂ 𝓕′ 𝓕″ : Scoped

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

    weaken*~wkˡ : ∀ m → weaken* {n} m ≗ wkˡ m
    weaken*~wkˡ zero x = refl
    weaken*~wkˡ (suc m) x = trans (cong wk (weaken*~wkˡ m x)) (wk-id/` (m ↑ʳ x))

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

      &/⋯-id : (x/t : 𝓕[ K₁ ] n) {ϕ : n –[ K₂ ]→ n} → ϕ ≗ id → `/id (x/t &/⋯ ϕ) ≡ `/id x/t
      &/⋯-id x/t eq = trans (&/⋯-⋯ x/t _) (⋯-id (`/id x/t) eq)

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

      &/⋯-fusion : {𝓕₁₂ : Scoped} ⦃ K : Kit 𝓕 ⦄ ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K′ : Kit 𝓕′ ⦄ ⦃ K″ : Kit 𝓕″ ⦄ ⦃ K₁₂ : Kit 𝓕₁₂ ⦄ →
        ⦃ C₁ : CKit K K₁ K′ ⦄ ⦃ C₂ : CKit K′ K₂ K″ ⦄ ⦃ C₃ : CKit K₁ K₂ K₁₂ ⦄ ⦃ W : WkKit K₁ ⦄ →
        (x/t : 𝓕[ K ] n₁) (ϕ₁ : n₁ –[ K₁ ]→ n₂) (ϕ₂ : n₂ –[ K₂ ]→ n₃) →
        `/id (x/t &/⋯ ϕ₁ &/⋯ ϕ₂) ≡ `/id x/t ⋯ ϕ₁ ·ₖ ϕ₂
      &/⋯-fusion x/t ϕ₁ ϕ₂ =
        trans (&/⋯-⋯ (x/t &/⋯ ϕ₁) ϕ₂)
          $ trans (cong (_⋯ ϕ₂) (&/⋯-⋯ x/t ϕ₁))
          $ fusion (`/id x/t) ϕ₁ ϕ₂

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
      swapᵣ m₁ m₂ = Fin.join _ _ ∘ Sum.map₁ (Fin.swap m₁) ∘ splitAt (m₁ + m₂)

      assocSwapᵣ : ∀ a b {n} → a + (b + n) →ᵣ b + (a + n)
      assocSwapᵣ a b {n} = [ (λ x → b ↑ʳ (x ↑ˡ n)) , Fin.join _ _ ∘ Sum.map₂ (a ↑ʳ_) ∘ splitAt b ]′ ∘ splitAt a

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

        ++-assocSwapᵣ : (Γ₁ : Ctx m₁) (Γ₂ : Ctx m₂) {Γ : Ctx n} → (Γ₂ ++ (Γ₁ ++ Γ)) ∘ assocSwapᵣ m₁ m₂ ≗ Γ₁ ++ (Γ₂ ++ Γ)
        ++-assocSwapᵣ {m₁}{m₂}{n} Γ₁ Γ₂ {Γ} x
          with Fin.splitAt m₁ x
        ... | inj₁ x₁ rewrite Fin.splitAt-↑ʳ m₂ _ (x₁ ↑ˡ n) | Fin.splitAt-↑ˡ m₁ x₁ n = refl
        ... | inj₂ x₂ₙ
          with Fin.splitAt m₂ x₂ₙ
        ... | inj₁ x₂ rewrite Fin.splitAt-↑ˡ m₂ x₂ (m₁ + n) = refl
        ... | inj₂ xₙ rewrite Fin.splitAt-↑ʳ m₂ _ (m₁ ↑ʳ xₙ) | Fin.splitAt-↑ʳ m₁ _ xₙ = refl

      wk-swap : ∀ a b {n} → wkˡ (a + b) ·ₖ swapᵣ a b {n} ≗ wkˡ ⦃ Kᵣ ⦄ (b + a)
      wk-swap a b x rewrite splitAt-↑ʳ (a + b) _ x = refl

      weaken*-swap-⋯ : ∀ (x : Tm n) a b → x ⋯ᵣ weaken* (a + b) ⋯ swapᵣ a b ≡ x ⋯ᵣ weaken* (b + a)
      weaken*-swap-⋯ x a b =
        trans (cong (_⋯ swapᵣ a b) (⋯-cong x (weaken*~wkˡ (a + b))))
          $ trans (fusion x (wkˡ (a + b)) (swapᵣ a b))
          $ trans (⋯-cong x (wk-swap a b))
          $ sym (⋯-cong x (weaken*~wkˡ (b + a)))

      wkˡ-swap≗wkʳ : ∀ m₁ m₂ {n} →
        (wkˡ ⦃ Kᵣ ⦄ {n = m₂} m₁ ·ₖ wkʳ ⦃ Kᵣ ⦄ n) ·ₖ swapᵣ m₁ m₂ ≗ wkʳ {n = m₂} m₁ ·ₖ wkʳ n
      wkˡ-swap≗wkʳ m₁ m₂ {n} x
        with Fin.splitAt (m₁ + m₂) ((m₁ ↑ʳ x) ↑ˡ n) in eq
      ... | inj₁ xₘ rewrite Fin.↑ˡ-injective n _ _ (Fin.splitAt⁻¹-↑ˡ eq) | Fin.splitAt-↑ʳ m₁ _ x = refl
      ... | inj₂ xₙ = contradiction (Fin.splitAt⁻¹-↑ʳ eq) (Fin.↑ˡ≢↑ʳ ∘ sym)

      wkʳ-swap≗wkˡ : ∀ m₁ m₂ {n} →
        (wkʳ ⦃ Kᵣ ⦄ {n = m₁} m₂ ·ₖ wkʳ ⦃ Kᵣ ⦄ n) ·ₖ swapᵣ m₁ m₂ ≗ wkˡ {n = m₁} m₂ ·ₖ wkʳ n
      wkʳ-swap≗wkˡ m₁ m₂ {n} x
        with Fin.splitAt (m₁ + m₂) (x ↑ˡ m₂ ↑ˡ n) in eq
      ... | inj₁ xₘ rewrite Fin.↑ˡ-injective n xₘ (x ↑ˡ m₂) (Fin.splitAt⁻¹-↑ˡ eq) | Fin.splitAt-↑ˡ m₁ x m₂ = refl
      ... | inj₂ xₙ = contradiction (Fin.splitAt⁻¹-↑ʳ eq) (Fin.↑ˡ≢↑ʳ ∘ sym)

      wkˡ-assocSwap : ∀ m₁ m₂ {n} →
        (wkˡ ⦃ Kᵣ ⦄ m₂ ·ₖ wkˡ ⦃ Kᵣ ⦄ m₁) ·ₖ assocSwapᵣ m₁ m₂ {n} ≗ wkˡ m₁ ·ₖ wkˡ m₂
      wkˡ-assocSwap m₁ m₂ {n} x rewrite splitAt-↑ʳ m₁ _ (m₂ ↑ʳ x) | splitAt-↑ʳ m₂ _ x = refl

      wkˡʳ-assocSwap : ∀ m₁ m₂ {n} →
        assocSwapᵣ m₁ m₂ ∘ wkˡ m₁ ∘ wkʳ n ≗ wkʳ (m₁ + n)
      wkˡʳ-assocSwap m₁ m₂ {n} x rewrite splitAt-↑ʳ m₁ _ (x ↑ˡ n) | splitAt-↑ˡ m₂ x n = refl

      module _ ⦃ K : Kit 𝓕 ⦄ ⦃ W : WkKit K ⦄ ⦃ C : CKit K Kᵣ K ⦄ where

        ↑*≗wkˡʳ : ∀ (ϕ : n₁ –[ K ]→ n₂) m → ϕ ↑* m ≗ [ wkʳ n₂ , ϕ ·ₖ wkˡ m ] ∘ splitAt m
        ↑*≗wkˡʳ ϕ zero x = `/id-injective (sym (&/⋯-id (ϕ x) λ _ → refl))
        ↑*≗wkˡʳ ϕ (suc m) zero = refl
        ↑*≗wkˡʳ {n₁} {n₂} ϕ (suc m) (suc x) = `/id-injective $
          `/id ⦃ K ⦄ ((ϕ ↑* suc m) (suc x)) ≡⟨⟩
          `/id ⦃ K ⦄ (wk ((ϕ ↑* m) x))      ≡⟨ cong (`/id ⦃ K ⦄ ∘ wk) (↑*≗wkˡʳ ϕ m x) ⟩
          `/id ⦃ K ⦄ (wk ([ wkʳ n₂ , ϕ ·ₖ wkˡ m ] (splitAt m x)))
            ≡⟨ [,]-∘ (`/id ⦃ K ⦄ ∘ wk) (splitAt m x) ⟩
          [ `/id ⦃ K ⦄ ∘ wk ∘ wkʳ n₂ , `/id ⦃ K ⦄ ∘ wk ∘ (ϕ ·ₖ wkˡ m) ] (splitAt m x)
            ≡⟨ [,]-cong (λ z → cong (`/id ⦃ K ⦄) (wk-id/` (z ↑ˡ n₂)))
                        (λ z → trans (sym (wk-`/id (ϕ z &/⋯ wkˡ m)))
                                 $ trans (cong wk (&/⋯-⋯ (ϕ z) (wkˡ m)))
                                 $ trans (fusion (`/id (ϕ z)) _ _)
                                 $ sym (&/⋯-⋯ (ϕ z) (wkˡ (suc m)) ))
                        (splitAt m x)
            ⟩
          [ (λ xₘ → `/id ⦃ K ⦄ (id/` ⦃ K ⦄ (wkʳ n₂ (suc xₘ)))) , (λ xₙ → `/id ⦃ K ⦄ (ϕ xₙ &/⋯ wkˡ (suc m))) ] (splitAt m x)
            ≡⟨ [,]-∘ (`/id ⦃ K ⦄) (splitAt m x) ⟨
          `/id ⦃ K ⦄ ([ (λ xₘ → id/` ⦃ K ⦄ (wkʳ n₂ (suc xₘ))) , (λ xₙ → ϕ xₙ &/⋯ wkˡ (suc m)) ] (splitAt m x))
            ≡⟨ cong (`/id ⦃ K ⦄) ([,]-map (splitAt m x)) ⟨
          `/id ⦃ K ⦄ ([ (λ xₘ → id/` ⦃ K ⦄ (wkʳ n₂ xₘ)) , (λ xₙ → ϕ xₙ &/⋯ wkˡ (suc m)) ] (Sum.map₁ suc (splitAt m x))) ∎

        dist-↑*-assocSwapˡ : ∀ a b {m n} (ϕ : m –[ K ]→ n) x →
          (ϕ ↑* a ↑* b) (b ↑ʳ (x ↑ˡ m)) ≡ wkʳ ⦃ K ⦄ (b + n) x &/⋯ assocSwapᵣ a b
        dist-↑*-assocSwapˡ a b {m}{n} ϕ x = `/id-injective $
          `/id ⦃ K ⦄ ((ϕ ↑* a ↑* b) (b ↑ʳ (x ↑ˡ m)))
            ≡⟨ cong `/id (↑*≗wkˡʳ (ϕ ↑* a) b (b ↑ʳ (x ↑ˡ m))) ⟩
          `/id ⦃ K ⦄ ([ wkʳ (a + n) , ϕ ↑* a ·ₖ wkˡ b ] (splitAt b (b ↑ʳ (x ↑ˡ m))))
            ≡⟨ cong (`/id ∘ [ wkʳ (a + n) , ϕ ↑* a ·ₖ wkˡ b ]) (splitAt-↑ʳ b _ (x ↑ˡ m)) ⟩
          `/id ⦃ K ⦄ ((ϕ ↑* a) (x ↑ˡ m) &/⋯ wkˡ b)
            ≡⟨ cong (`/id ∘ (_&/⋯ wkˡ b)) (↑*≗wkˡʳ ϕ a (x ↑ˡ m)) ⟩
          `/id ⦃ K ⦄ (([ wkʳ n , ϕ ·ₖ wkˡ a ]′ (splitAt a (x ↑ˡ m))) &/⋯ wkˡ b)
            ≡⟨  cong (λ y → `/id ([ wkʳ n , ϕ ·ₖ wkˡ a ]′ y &/⋯ wkˡ b)) (splitAt-↑ˡ a x m)  ⟩
          `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n x &/⋯ wkˡ b)
            ≡⟨ &/⋯-& ⦃ C ⦄ (x ↑ˡ n) (wkˡ b) ⟩
          ` (b ↑ʳ (x ↑ˡ n))
            ≡⟨ cong (`_ ∘ [ (λ y → b ↑ʳ (y ↑ˡ n)) , Fin.join _ _ ∘ Sum.map₂ (a ↑ʳ_) ∘ splitAt b ]) (splitAt-↑ˡ a x (b + n)) ⟨
          ` assocSwapᵣ a b (x ↑ˡ b + n)
            ≡⟨ &/⋯-& ⦃ C ⦄ (x ↑ˡ (b + n)) (assocSwapᵣ a b) ⟨
          `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ (b + n) x &/⋯ assocSwapᵣ a b) ∎

        dist-↑*-assocSwapʳ : ∀ a b {m n} (ϕ : m –[ K ]→ n) x →
          (ϕ ↑* a ↑* b) (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (splitAt b x)))
            ≡
          (ϕ ↑* b ·ₖ wkˡ ⦃ Kᵣ ⦄ a) x &/⋯ assocSwapᵣ a b
        dist-↑*-assocSwapʳ a b {m}{n} ϕ x = `/id-injective $
          `/id ⦃ K ⦄ ((ϕ ↑* a ↑* b) (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (splitAt b x))))
             ≡⟨ cong `/id (↑*≗wkˡʳ (ϕ ↑* a) b (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (splitAt b x)))) ⟩
          `/id ⦃ K ⦄ ([ wkʳ (a + n) , (ϕ ↑* a) ·ₖ wkˡ b ] (splitAt b (Fin.join b (a + m) (Sum.map₂ (a ↑ʳ_) (splitAt b x)))))
            ≡⟨ cong (`/id ∘ [ wkʳ (a + n) , (ϕ ↑* a) ·ₖ wkˡ b ]) (Fin.splitAt-join b (a + m) (Sum.map₂ (a ↑ʳ_) (splitAt b x))) ⟩
          `/id ⦃ K ⦄ ([ wkʳ (a + n) , (ϕ ↑* a) ·ₖ wkˡ b ] (Sum.map₂ (a ↑ʳ_) (splitAt b x)))
            ≡⟨ cong (`/id ⦃ K ⦄) ([,]-map (splitAt b x)) ⟩
          `/id ⦃ K ⦄ ([ wkʳ (a + n) , ((ϕ ↑* a) ·ₖ wkˡ b) ∘ (a ↑ʳ_) ] (splitAt b x))
            ≡⟨ [,]-∘ (`/id ⦃ K ⦄) (splitAt b x) ⟩
          [ `/id ⦃ K ⦄ ∘ wkʳ (a + n) , `/id ⦃ K ⦄ ∘ ((ϕ ↑* a) ·ₖ wkˡ b) ∘ (a ↑ʳ_) ] (splitAt b x)
            ≡⟨ [,-]-cong (λ y → cong (`/id ⦃ K ⦄ ∘ (_&/⋯ wkˡ b))
                                  $ trans (↑*≗wkˡʳ ϕ a (a ↑ʳ y))
                                  $ cong [ wkʳ n , ϕ ·ₖ wkˡ a ] (Fin.splitAt-↑ʳ a _ y))
                         (splitAt b x) ⟩
          [ `/id ⦃ K ⦄ ∘ wkʳ (a + n) , (λ y → `/id ⦃ K ⦄ (ϕ y &/⋯ wkˡ a &/⋯ wkˡ b)) ] (splitAt b x)
            ≡⟨ [,]-cong (λ y → `/`-is-` ⦃ K ⦄ (wkʳ (a + n) y))
                        (λ y → &/⋯-fusion (ϕ y) (wkˡ a) (wkˡ b))
                        (splitAt b x) ⟩
          [ (λ y → ` wkʳ (a + n) y)
          , (λ y → `/id ⦃ K ⦄ (ϕ y) ⋯ wkˡ a ·ₖ wkˡ b)
          ] (splitAt b x)
            ≡⟨ [,]-cong (λ y → cong `_ (wkˡʳ-assocSwap a b y))
                        (λ y → ⋯-cong (`/id (ϕ y)) (wkˡ-assocSwap a b))
                        (splitAt b x) ⟨
          [ (λ y → ` assocSwapᵣ a b (wkˡ ⦃ Kᵣ ⦄ a (wkʳ ⦃ Kᵣ ⦄ n y)))
          , (λ y → `/id ⦃ K ⦄ (ϕ y) ⋯ (wkˡ b ·ₖ wkˡ a) ·ₖ assocSwapᵣ a b)
          ]′ (splitAt b x)
            ≡⟨ [-,]-cong (λ y → sym (⋯-var ⦃ Kᵣ ⦄ (wkʳ n y) (wkˡ a ·ₖ assocSwapᵣ a b))) (splitAt b x) ⟩
          [ (λ y → ` (wkʳ ⦃ Kᵣ ⦄ n y) ⋯ wkˡ ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b)
          , (λ y → `/id ⦃ K ⦄ (ϕ y) ⋯ (wkˡ b ·ₖ wkˡ a) ·ₖ assocSwapᵣ a b)
          ]′ (splitAt b x)
            ≡⟨ [,]-cong (λ y → cong (_⋯ wkˡ ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b) (`/`-is-` ⦃ K ⦄ (wkʳ n y)))
                        (λ y → fusion (`/id (ϕ y)) (wkˡ b ·ₖ wkˡ a) (assocSwapᵣ a b))
                        (splitAt b x) ⟨
          [ (λ y → `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n y) ⋯ wkˡ ⦃ Kᵣ ⦄ a ·ₖ assocSwapᵣ a b)
          , (λ y → `/id ⦃ K ⦄ (ϕ y) ⋯ wkˡ b ·ₖ wkˡ a ⋯ assocSwapᵣ a b)
          ]′ (splitAt b x)
            ≡⟨ [,]-cong (λ y → &/⋯-fusion (wkʳ ⦃ K ⦄ n y) (wkˡ a) (assocSwapᵣ a b))
                        (λ y → trans (&/⋯-⋯ (ϕ y &/⋯ wkˡ b &/⋯ wkˡ a) (assocSwapᵣ a b))
                                     (cong (_⋯ assocSwapᵣ a b) (&/⋯-fusion (ϕ y) (wkˡ b) (wkˡ a))))
                        (splitAt b x) ⟨
          [ (λ y → `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n y &/⋯ wkˡ a &/⋯ assocSwapᵣ a b))
          , (λ y → `/id ⦃ K ⦄ (ϕ y &/⋯ wkˡ b &/⋯ wkˡ a &/⋯ assocSwapᵣ a b))
          ]′ (splitAt b x)
            ≡⟨ [,]-∘ (`/id ∘ (_&/⋯ assocSwapᵣ a b) ∘ (_&/⋯ wkˡ a)) {wkʳ n} {ϕ ·ₖ wkˡ b} (splitAt b x) ⟨
          `/id ⦃ K ⦄ (([ wkʳ n , ϕ ·ₖ wkˡ b ]′ (splitAt b x) &/⋯ wkˡ a) &/⋯ assocSwapᵣ a b)
            ≡⟨ cong (`/id ∘ (_&/⋯ assocSwapᵣ a b) ∘ (_&/⋯ wkˡ a)) (↑*≗wkˡʳ ϕ b x) ⟨
          `/id ⦃ K ⦄ ((ϕ ↑* b ·ₖ wkˡ a) x &/⋯ assocSwapᵣ a b) ∎

        dist-↑*-assocSwap : ∀ a b {m n} (ϕ : m –[ K ]→ n) →
          assocSwapᵣ a b {m} ·[ Cᵣ ] ϕ ↑* a ↑* b ≗ ϕ ↑* b ↑* a ·ₖ assocSwapᵣ a b {n}
        dist-↑*-assocSwap a b {m} {n} ϕ x =
          (assocSwapᵣ a b ·ₖ ϕ ↑* a ↑* b) x
            ≡⟨⟩
          (ϕ ↑* a ↑* b) (assocSwapᵣ a b x)
            ≡⟨ [,]-∘ (ϕ ↑* a ↑* b) (splitAt a x) ⟩
          [ (ϕ ↑* a ↑* b) ∘ (λ z → b ↑ʳ (z ↑ˡ m)) ,
            (ϕ ↑* a ↑* b) ∘ Fin.join b (a + m) ∘ Sum.map₂ (a ↑ʳ_) ∘ splitAt b
          ] (splitAt a x)
            ≡⟨ [,]-cong (dist-↑*-assocSwapˡ a b ϕ) (dist-↑*-assocSwapʳ a b ϕ) (splitAt a x) ⟩
          [ (λ z → wkʳ ⦃ K ⦄ (b + n) z &/⋯ assocSwapᵣ a b)
          , (λ z → (ϕ ↑* b ·ₖ wkˡ a) z &/⋯ assocSwapᵣ a b)
          ]′ (splitAt a x)
            ≡⟨ [,]-∘ (λ z → CKit._&/⋯_ C z (assocSwapᵣ a b)) (splitAt a x) ⟨
          [ wkʳ (b + n) , ϕ ↑* b ·ₖ wkˡ a ]′ (splitAt a x) &/⋯ assocSwapᵣ a b
            ≡⟨ cong (_&/⋯ assocSwapᵣ a b) (↑*≗wkˡʳ (ϕ ↑* b) a x) ⟨
          (ϕ ↑* b ↑* a) x &/⋯ assocSwapᵣ a b
            ≡⟨⟩
          (ϕ ↑* b ↑* a ·ₖ assocSwapᵣ a b) x ∎

        dist-↑*-swapˡ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
            ≡
          `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n₂ x &/⋯ swapᵣ b₁ b₂)
        dist-↑*-swapˡ b₁ b₂ {n₁} {n₂} {ϕ} x =
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (Fin.swap b₁ x ↑ˡ n₁))
            ≡⟨ cong (`/id ⦃ K ⦄) (↑*≗wkˡʳ ϕ (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)) ⟩
          `/id ⦃ K ⦄ ([ wkʳ n₂ , ϕ ·ₖ wkˡ (b₂ + b₁) ]′ (splitAt (b₂ + b₁) (Fin.swap b₁ x ↑ˡ n₁)))
            ≡⟨ cong (`/id ∘ [ wkʳ n₂ , ϕ ·ₖ wkˡ (b₂ + b₁) ]′) (splitAt-↑ˡ (b₂ + b₁) (Fin.swap b₁ x) n₁) ⟩
          `/id ⦃ K ⦄ (wkʳ n₂ (Fin.swap b₁ x))
            ≡⟨ `/`-is-` ⦃ K ⦄ (wkʳ n₂ (Fin.swap b₁ x)) ⟩
          ` wkʳ n₂ (Fin.swap b₁ x)
            ≡⟨ cong (`_ ∘ Fin.join _ _ ∘ Sum.map₁ (Fin.swap b₁)) (splitAt-↑ˡ (b₁ + b₂) x n₂) ⟨
          ` Fin.join _ _ (Sum.map₁ (Fin.swap b₁) (splitAt (b₁ + b₂) (wkʳ n₂ x)))
            ≡⟨ ⋯-var (wkʳ n₂ x) (swapᵣ b₁ b₂) ⟨
          ` wkʳ n₂ x ⋯ swapᵣ b₁ b₂
            ≡⟨ cong (_⋯ swapᵣ b₁ b₂) (`/`-is-` ⦃ K ⦄ (wkʳ n₂ x)) ⟨
          `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n₂ x) ⋯ swapᵣ b₁ b₂
            ≡⟨ &/⋯-⋯ (wkʳ ⦃ K ⦄ n₂ x) (swapᵣ b₁ b₂) ⟨
          `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n₂ x &/⋯ swapᵣ b₁ b₂) ∎

        dist-↑*-swapʳ : ∀ b₁ b₂ {n₁ n₂} {ϕ : n₁ –[ K ]→ n₂} x →
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
            ≡
          `/id ⦃ K ⦄ (ϕ x &/⋯ wkˡ (b₁ + b₂) &/⋯ swapᵣ b₁ b₂)
        dist-↑*-swapʳ b₁ b₂ {n₁} {n₂} {ϕ} x =
          `/id ⦃ K ⦄ ((ϕ ↑* (b₂ + b₁)) (b₂ + b₁ ↑ʳ x))
            ≡⟨ cong (`/id ⦃ K ⦄) (↑*≗wkˡʳ ϕ (b₂ + b₁) (b₂ + b₁ ↑ʳ x)) ⟩
          `/id ⦃ K ⦄ ([ wkʳ n₂ , ϕ ·ₖ wkˡ (b₂ + b₁) ] (splitAt (b₂ + b₁) (b₂ + b₁ ↑ʳ x)))
            ≡⟨ cong (`/id ⦃ K ⦄ ∘ [ wkʳ n₂ , ϕ ·ₖ wkˡ (b₂ + b₁) ]) (splitAt-↑ʳ (b₂ + b₁) _ x) ⟩
          `/id ⦃ K ⦄ (ϕ x &/⋯ wkˡ (b₂ + b₁))
            ≡⟨ &/⋯-⋯ (ϕ x) (wkˡ (b₂ + b₁)) ⟩
          `/id ⦃ K ⦄ (ϕ x) ⋯ wkˡ (b₂ + b₁)
            ≡⟨ ⋯-cong (`/id (ϕ x)) (wk-swap b₁ b₂) ⟨
          `/id ⦃ K ⦄ (ϕ x) ⋯ wkˡ (b₁ + b₂) ·ₖ swapᵣ b₁ b₂
            ≡⟨ &/⋯-fusion (ϕ x) (wkˡ (b₁ + b₂)) (swapᵣ b₁ b₂) ⟨
          `/id ⦃ K ⦄ (ϕ x &/⋯ wkˡ (b₁ + b₂) &/⋯ swapᵣ b₁ b₂) ∎

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
          [ (λ y → `/id ⦃ K ⦄ (wkʳ ⦃ K ⦄ n₂ y &/⋯ swapᵣ m₁ m₂))
          , (λ y → `/id ⦃ K ⦄ (ϕ y &/⋯ wkˡ (m₁ + m₂) &/⋯ swapᵣ m₁ m₂))
          ] (Fin.splitAt (m₁ + m₂) x)
            ≡⟨ [,]-∘ (λ z → `/id ⦃ K ⦄ (CKit._&/⋯_ C z (swapᵣ m₁ m₂ {n₂}))) (Fin.splitAt (m₁ + m₂) x) ⟨
          `/id ⦃ K ⦄ ([ wkʳ n₂ , ϕ ·ₖ wkˡ (m₁ + m₂) ] (Fin.splitAt (m₁ + m₂) x) &/⋯ swapᵣ m₁ m₂ {n₂})
            ≡⟨ cong (λ z → `/id (z &/⋯ swapᵣ m₁ m₂)) (↑*≗wkˡʳ ϕ (m₁ + m₂) x) ⟨
          `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂)) x &/⋯ swapᵣ m₁ m₂) ≡⟨⟩
          `/id ⦃ K ⦄ ((ϕ ↑* (m₁ + m₂) ·ₖ swapᵣ m₁ m₂) x) ∎

      record Types : Set₁ where
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
