module BorrowedCF.Simulation2.TranslationProperties where

-- | Basic algebra of the (reworked) translation U[_] / UB[_]: congruence in the
--   substitution argument (≋- and ≡-variants), naturality of the φ-nest UB[_]
--   under target renaming, and the two commutation lemmas relating the
--   translation with renaming/substitution of the SOURCE and of the TARGET.
--
--   Rebuilt against the NEW Processes.Bisim UB[_]/U[_] (single-chain
--   `f (λ _ → chanTriple c)`, multi-chain `φ ϕ[ b ] (UB[ B ] … (λ σ → subst …))`),
--   the new flag-carrying φ constructor, and the Kit-generalized _⋯ₚ_.

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR

------------------------------------------------------------------------
-- Generic transport / coercion plumbing (ported, constructor-agnostic).
------------------------------------------------------------------------

≋-subst : {a b : ℕ} (eq : a ≡ b) {x y : UP.Proc a} → x UP.≋ y → subst UP.Proc eq x UP.≋ subst UP.Proc eq y
≋-subst refl xy = xy

++ₛ-congʳ : ∀ {a b N} (σ₁ : a →ₛ N) {σ₂ σ₂′ : b →ₛ N} → σ₂ ≗ σ₂′ → σ₁ ++ₛ σ₂ ≗ σ₁ ++ₛ σ₂′
++ₛ-congʳ {a} σ₁ eq i = [,]-cong (λ _ → refl) eq (splitAt a i)

++ₛ-⋯ : ∀ {a b N N′} (σ₁ : a →ₛ N) (σ₂ : b →ₛ N) (θ : N →ᵣ N′) i →
        (σ₁ ++ₛ σ₂) i ⋯ θ ≡ ((λ j → σ₁ j ⋯ θ) ++ₛ (λ j → σ₂ j ⋯ θ)) i
++ₛ-⋯ {a} σ₁ σ₂ θ i = helper (splitAt a i)
  where
    helper : (s : 𝔽 a ⊎ 𝔽 _) →
             [ σ₁ , σ₂ ]′ s ⋯ θ ≡ [ (λ j → σ₁ j ⋯ θ) , (λ j → σ₂ j ⋯ θ) ]′ s
    helper (inj₁ j) = refl
    helper (inj₂ j) = refl

subst-⋯ₚ-cod : ∀ {a c d} (q : c ≡ d) (Q : UP.Proc a) (θ : a →ᵣ c) →
               Q UP.⋯ₚ subst (λ z → a →ᵣ z) q θ ≡ subst UP.Proc q (Q UP.⋯ₚ θ)
subst-⋯ₚ-cod refl Q θ = refl

subst-⋯ₚ-dom : ∀ {a b c} (p : a ≡ b) (Q : UP.Proc b) (θ : a →ᵣ c) →
               subst UP.Proc (sym p) Q UP.⋯ₚ θ ≡ Q UP.⋯ₚ subst (λ z → z →ᵣ c) p θ
subst-⋯ₚ-dom refl Q θ = refl

subst-⋯ : ∀ {a b c} (p : a ≡ b) (t : Tm a) (θ : b →ᵣ c) →
          subst Tm p t ⋯ θ ≡ t ⋯ subst (λ z → z →ᵣ c) (sym p) θ
subst-⋯ refl t θ = refl

subst-⋯-cod : ∀ {a c d} (q : c ≡ d) (t : Tm a) (θ : a →ᵣ c) →
              t ⋯ subst (λ z → a →ᵣ z) q θ ≡ subst Tm q (t ⋯ θ)
subst-⋯-cod refl t θ = refl

subst-Π : ∀ {D a b} (p : a ≡ b) (s : 𝔽 D → Tm a) (i : 𝔽 D) →
          subst (λ z → 𝔽 D → Tm z) p s i ≡ subst Tm p (s i)
subst-Π refl s i = refl

subst₂-↑ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (ρ : a →ᵣ b) →
           subst₂ _→ᵣ_ (cong suc p) (cong suc q) (ρ ↑) ≡ (subst₂ _→ᵣ_ p q ρ) ↑
subst₂-↑ refl refl ρ = refl

subst₂→ : ∀ {a b c d} (p : a ≡ b) (q : c ≡ d) (ρ : a →ᵣ c) →
          subst₂ _→ᵣ_ p q ρ ≡ subst (λ z → b →ᵣ z) q (subst (λ z → z →ᵣ c) p ρ)
subst₂→ refl refl ρ = refl

subst₂-cancel : ∀ {a b c d} (p : a ≡ b) (q : c ≡ d) (ρ : a →ᵣ c) →
                subst₂ _→ᵣ_ (sym p) (sym q) (subst₂ _→ᵣ_ p q ρ) ≡ ρ
subst₂-cancel refl refl ρ = refl

subst-flip : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {a : F x} {b : F y} →
             subst F q a ≡ b → a ≡ subst F (sym q) b
subst-flip refl eq = eq

subst-subst-sym′ : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {b : F y} →
                   subst F q (subst F (sym q) b) ≡ b
subst-subst-sym′ refl = refl

≡→≋ : {P Q : UP.Proc n} → P ≡ Q → P UP.≋ Q
≡→≋ refl = ε

------------------------------------------------------------------------
-- Two elementary renaming facts (provable from the FinKits primitives).
------------------------------------------------------------------------

-- weakening a Fin (under the renaming Kit) is the right injection.
weaken*~↑ʳ : ∀ (m : ℕ) {n : ℕ} (x : 𝔽 n) →
             weaken* ⦃ Kᵣ ⦄ m x ≡ m ↑ʳ x
weaken*~↑ʳ zero    x = refl
weaken*~↑ʳ (suc m) x = cong suc (weaken*~↑ʳ m x)

↑*∼id/wk-splitAt : ∀ {m m′} (ρ : m →ᵣ m′) (len : ℕ) (i : 𝔽 (len + m)) →
                   (ρ ↑* len) i ≡ [ (_↑ˡ m′) , (λ k → len ↑ʳ ρ k) ]′ (splitAt len i)
↑*∼id/wk-splitAt ρ zero    i = refl
↑*∼id/wk-splitAt ρ (suc len) zero    = refl
↑*∼id/wk-splitAt {m} {m′} ρ (suc len) (suc i) =
  cong suc (↑*∼id/wk-splitAt ρ len i) ■ helper (splitAt len i)
  where
    helper : (s : 𝔽 len ⊎ 𝔽 m) →
             suc ([ (_↑ˡ m′) , (λ k → len ↑ʳ ρ k) ]′ s)
             ≡ [ (_↑ˡ m′) , (λ k → suc (len ↑ʳ ρ k)) ]′
                 ([ inj₁ ∘ suc , inj₂ ]′ s)
    helper (inj₁ j) = refl
    helper (inj₂ k) = refl

------------------------------------------------------------------------
-- mapᶜ : renaming of channel triples.
------------------------------------------------------------------------

mapᶜ : (n →ᵣ n′) → UChan n → UChan n′
mapᶜ θ (e₁ , x , e₂) = (e₁ ⋯ θ , θ x , e₂ ⋯ θ)

mapᶜ-cong : {ρ₁ ρ₂ : n →ᵣ n′} → ρ₁ ≗ ρ₂ → (cc : UChan n) → mapᶜ ρ₁ cc ≡ mapᶜ ρ₂ cc
mapᶜ-cong eq (e₁ , x , e₂) = cong₂ _,_ (⋯-cong e₁ eq) (cong₂ _,_ (eq x) (⋯-cong e₂ eq))

mapᶜ-fusion : ∀ {n‴} (ρ₁ : n →ᵣ n′) (ρ₂ : n′ →ᵣ n‴) (cc : UChan n) →
              mapᶜ ρ₂ (mapᶜ ρ₁ cc) ≡ mapᶜ (ρ₁ ·ₖ ρ₂) cc
mapᶜ-fusion ρ₁ ρ₂ (e₁ , x , e₂) =
  cong₂ _,_ (fusion e₁ ρ₁ ρ₂) (cong₂ _,_ refl (fusion e₂ ρ₁ ρ₂))

------------------------------------------------------------------------
-- chanTriple commutes with renaming via mapᶜ.
------------------------------------------------------------------------

chanTriple-mapᶜ : (θ : n →ᵣ n′) (cc : UChan n) → chanTriple cc ⋯ θ ≡ chanTriple (mapᶜ θ cc)
chanTriple-mapᶜ θ (e₁ , x , e₂) = refl

------------------------------------------------------------------------
-- Ub[_] : pointwise naturality of the distributing data-block leaf.
------------------------------------------------------------------------

Ub-nat : (b : ℕ) (cc : UChan n) (θ : n →ᵣ n′) (j : 𝔽 b) →
         Ub[ b ] cc j ⋯ θ ≡ Ub[ b ] (mapᶜ θ cc) j
Ub-nat (suc b) (e₁ , c , e₂) θ zero    = refl
Ub-nat (suc b) (e₁ , c , e₂) θ (suc j) = Ub-nat b (* , c , e₂) θ j

------------------------------------------------------------------------
-- UB-cong : the φ-nest respects pointwise-equal continuations (≋-variant).
------------------------------------------------------------------------

UB-cong : (B : TP.BindGroup) (cc : UChan n) {f g : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)} →
          (∀ σ → f σ UP.≋ g σ) → UB[ B ] cc f UP.≋ UB[ B ] cc g
UB-cong [] cc h = h λ()
UB-cong (b ∷ []) cc h = h _
UB-cong (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) h =
  UP.φ-cong (UB-cong B _ (λ σ → ≋-subst (sym (+-suc (syncs B) _)) (h _)))

------------------------------------------------------------------------
-- UB-cong-≡ : the ≡-variant (for reasoning under renaming/substitution).
------------------------------------------------------------------------

UB-cong-≡ : (B : TP.BindGroup) (cc : UChan n) {f g : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)} →
            (∀ σ → f σ ≡ g σ) → UB[ B ] cc f ≡ UB[ B ] cc g
UB-cong-≡ [] cc h = h λ()
UB-cong-≡ (b ∷ []) cc h = h _
UB-cong-≡ (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) h =
  cong (UP.φ ϕ[ b ]) (UB-cong-≡ B _ (λ σ → cong (subst UP.Proc (sym (+-suc (syncs B) _))) (h _)))

------------------------------------------------------------------------
-- U-cong : the translation depends on its substitution only pointwise.
------------------------------------------------------------------------

U-cong : (P : TP.Proc m) {σ₁ σ₂ : m →ₛ n} → σ₁ ≗ σ₂ → U[ P ] σ₁ ≡ U[ P ] σ₂
U-cong TP.⟪ e ⟫     eq = cong UP.⟪_⟫ (⋯-cong e eq)
U-cong (P TP.∥ Q)   eq = cong₂ UP._∥_ (U-cong P eq) (U-cong Q eq)
U-cong (TP.ν B₁ B₂ P) eq =
  cong UP.ν (UB-cong-≡ B₁ _ (λ τ₁ → UB-cong-≡ B₂ _ (λ τ₂ →
    U-cong P (++ₛ-congʳ _ (λ i →
      cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (eq i))))))

------------------------------------------------------------------------
-- A lifted renaming distributes over a substitution concatenation.
------------------------------------------------------------------------

dist-↑*-++ₛ : ∀ len {m m′ N} {ρ : m →ᵣ m′} {A : len →ₛ N} {C : m′ →ₛ N} →
              (ρ ↑* len) ·ₖ (A ++ₛ C) ≗ A ++ₛ (ρ ·ₖ C)
dist-↑*-++ₛ len {m} {m′} {N} {ρ} {A} {C} i =
  cong (A ++ₛ C) (↑*∼id/wk-splitAt ρ len i) ■ helper (splitAt len i)
  where
    helper : (s : 𝔽 len ⊎ 𝔽 m) →
             (A ++ₛ C) ([ (_↑ˡ m′) , (λ k → len ↑ʳ ρ k) ]′ s) ≡ [ A , (λ k → C (ρ k)) ]′ s
    helper (inj₁ j) = cong [ A , C ]′ (splitAt-↑ˡ len j m′)
    helper (inj₂ k) = cong [ A , C ]′ (splitAt-↑ʳ len m′ (ρ k))

------------------------------------------------------------------------
-- The translation commutes with (typed) process renaming/substitution of
-- the SOURCE.
------------------------------------------------------------------------

U-⋯ₚ : (P : TP.Proc m) {ρ : m →ᵣ m′} {σ : m′ →ₛ n} → U[ P TP.⋯ₚ ρ ] σ ≡ U[ P ] (ρ ·ₖ σ)
U-⋯ₚ TP.⟪ e ⟫ {ρ} {σ} = cong UP.⟪_⟫ (fusion e ρ σ)
U-⋯ₚ (P TP.∥ Q)       = cong₂ UP._∥_ (U-⋯ₚ P) (U-⋯ₚ Q)
U-⋯ₚ (TP.ν B₁ B₂ P) {ρ} {σ} =
  cong UP.ν (UB-cong-≡ B₁ _ (λ τ₁ → UB-cong-≡ B₂ _ (λ τ₂ →
    U-⋯ₚ P ■ U-cong P (dist-↑*-++ₛ (sum B₁ + sum B₂) {ρ = ρ}
      {A = (λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂}
      {C = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)}))))

------------------------------------------------------------------------
-- Renaming-coercion helpers for naturality.
------------------------------------------------------------------------

liftCast : ∀ {n n′} (m : ℕ) (θ : n →ᵣ n′) →
           subst₂ _→ᵣ_ (+-suc m n) (+-suc m n′) ((θ ↑) ↑* m) ≡ (θ ↑* m) ↑
liftCast zero    θ = refl
liftCast (suc k) θ = subst₂-↑ (+-suc k _) (+-suc k _) ((θ ↑) ↑* k) ■ cong _↑ (liftCast k θ)

varΘ : ∀ {a b} sB (ψ : a →ᵣ b) (y : 𝔽 a) →
       (ψ ↑* sB) (weaken* ⦃ Kᵣ ⦄ sB y) ≡ weaken* ⦃ Kᵣ ⦄ sB (ψ y)
varΘ sB ψ y =
  cong (ψ ↑* sB) (weaken*~↑ʳ sB y)
  ■ ↑*∼id/wk-splitAt ψ sB (sB ↑ʳ y)
  ■ cong [ (_↑ˡ _) , (λ k → sB ↑ʳ ψ k) ]′ (splitAt-↑ʳ sB _ y)
  ■ sym (weaken*~↑ʳ sB (ψ y))

------------------------------------------------------------------------
-- Renaming naturality of the φ-nest UB[_].
------------------------------------------------------------------------

UB-nat : (B : TP.BindGroup) (cc : UChan n) (θ : n →ᵣ n′)
         {f : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)}
         {f′ : (sum B →ₛ syncs B + n′) → UP.Proc (syncs B + n′)} →
         (∀ τ → f τ UP.⋯ₚ (θ ↑* syncs B) ≡ f′ (λ i → τ i ⋯ (θ ↑* syncs B))) →
         UB[ B ] cc f UP.⋯ₚ θ ≡ UB[ B ] (mapᶜ θ cc) f′
UB-nat [] cc θ {f} {f′} h = h (λ ()) ■ cong f′ (funext (λ ()))
UB-nat (b ∷ []) (e₁ , x , e₂) θ {f} {f′} h =
  h (λ _ → chanTriple (e₁ , x , e₂))
  ■ cong f′ (funext (λ _ → chanTriple-mapᶜ θ (e₁ , x , e₂)))
UB-nat {n} {n′} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) θ {f} {f′} h =
  cong (UP.φ ϕ[ b ])
    (UB-nat B (` 0F , suc x , e₂ ⋯ weakenᵣ) (θ ↑) {f = gL} {f′ = gR} contH
     ■ cong (λ cc → UB[ B ] cc gR) ccEq)
  where
    sB = syncs B
    UbL : b →ₛ (sB + suc n)
    UbL = Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
    UbR : b →ₛ (sB + suc n′)
    UbR = Ub[ b ] (e₁ ⋯ θ ⋯ weakenᵣ , suc (θ x) , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
    gL : (sum B →ₛ sB + suc n) → UP.Proc (sB + suc n)
    gL σ = subst UP.Proc (sym (+-suc sB n))
             (f (λ y → subst Tm (+-suc sB n)
                  ([ UbL , σ ]′ (splitAt b y))))
    gR : (sum B →ₛ sB + suc n′) → UP.Proc (sB + suc n′)
    gR σ = subst UP.Proc (sym (+-suc sB n′))
             (f′ (λ y → subst Tm (+-suc sB n′)
                  ([ UbR , σ ]′ (splitAt b y))))
    ccEq : mapᶜ (θ ↑) (` 0F , suc x , e₂ ⋯ weakenᵣ)
           ≡ (` 0F , suc (θ x) , (e₂ ⋯ θ) ⋯ weakenᵣ)
    ccEq = cong₂ _,_ refl (cong₂ _,_ refl (sym (⋯-↑-wk e₂ θ)))
    Θ : (sB + suc n) →ᵣ (sB + suc n′)
    Θ = (θ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ᵣ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ᵣ z) (sym (+-suc sB n′)) (θ ↑* suc sB)
    Θ⁺eq = subst-flip (+-suc sB n′) (sym (subst₂→ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCast sB θ)
    Y : (sum B →ₛ sB + suc n) → (sum (b ∷ B) →ₛ suc (sB + n))
    Y τ y = subst Tm (+-suc sB n) ([ UbL , τ ]′ (splitAt b y))
    Y′ : (sum B →ₛ sB + suc n′) → (sum (b ∷ B) →ₛ suc (sB + n′))
    Y′ τ y = subst Tm (+-suc sB n′) ([ UbR , τ ]′ (splitAt b y))
    θ⁻ : (sB + suc n) →ᵣ suc (sB + n′)
    θ⁻ = subst (λ z → z →ᵣ suc (sB + n′)) (sym (+-suc sB n)) (θ ↑* suc sB)
    ΘθEq : Θ ≡ subst (λ z → (sB + suc n) →ᵣ z) (sym (+-suc sB n′)) θ⁻
    ΘθEq = sym ( sym (subst₂→ (sym (+-suc sB n)) (sym (+-suc sB n′)) (θ ↑* suc sB))
               ■ cong (subst₂ _→ᵣ_ (sym (+-suc sB n)) (sym (+-suc sB n′))) (sym (liftCast sB θ))
               ■ subst₂-cancel (+-suc sB n) (+-suc sB n′) Θ )
    ΘrelEq : (t : Tm (sB + suc n)) → t ⋯ θ⁻ ≡ subst Tm (+-suc sB n′) (t ⋯ Θ)
    ΘrelEq t = sym ( cong (λ r → subst Tm (+-suc sB n′) (t ⋯ r)) ΘθEq
                   ■ cong (subst Tm (+-suc sB n′)) (subst-⋯-cod (sym (+-suc sB n′)) t θ⁻)
                   ■ subst-subst-sym′ (+-suc sB n′) )
    ccUbEq : mapᶜ (θ ↑) (e₁ ⋯ weakenᵣ , suc x , ` 0F) ≡ (e₁ ⋯ θ ⋯ weakenᵣ , suc (θ x) , ` 0F)
    ccUbEq = cong₂ _,_ (sym (⋯-↑-wk e₁ θ)) refl
    UbReq : (j : 𝔽 b) → UbL j ⋯ Θ ≡ UbR j
    UbReq j =
        sym (⋯-↑*-wk (Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) j) (θ ↑) sB)
      ■ cong (_⋯ᵣ weaken* ⦃ Kᵣ ⦄ sB) (Ub-nat b (e₁ ⋯ weakenᵣ , suc x , ` 0F) (θ ↑) j)
      ■ cong (λ cc → Ub[ b ] cc j ⋯ᵣ weaken* ⦃ Kᵣ ⦄ sB) ccUbEq
    Yeq : (τ : sum B →ₛ sB + suc n) →
          (λ i → Y τ i ⋯ (θ ↑* suc sB)) ≡ Y′ (λ i → τ i ⋯ Θ)
    Yeq τ = funext (λ i →
        subst-⋯ (+-suc sB n) ([ UbL , τ ]′ (splitAt b i)) (θ ↑* suc sB)
      ■ ΘrelEq ([ UbL , τ ]′ (splitAt b i))
      ■ cong (subst Tm (+-suc sB n′)) (body (splitAt b i)))
      where
        body : (s : 𝔽 b ⊎ 𝔽 (sum B)) →
               [ UbL , τ ]′ s ⋯ Θ ≡ [ UbR , (λ i → τ i ⋯ Θ) ]′ s
        body (inj₁ j) = UbReq j
        body (inj₂ k) = refl
    contH : (τ : sum B →ₛ sB + suc n) →
            gL τ UP.⋯ₚ ((θ ↑) ↑* sB) ≡ gR (λ i → τ i ⋯ ((θ ↑) ↑* sB))
    contH τ =
        subst-⋯ₚ-dom (+-suc sB n) (f (Y τ)) Θ
      ■ cong (f (Y τ) UP.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-cod (sym (+-suc sB n′)) (f (Y τ)) (θ ↑* suc sB)
      ■ cong (subst UP.Proc (sym (+-suc sB n′))) (h (Y τ) ■ cong f′ (Yeq τ))

------------------------------------------------------------------------
-- The translation commutes with renaming of its TARGET (output).
------------------------------------------------------------------------

U-σ⋯ : (P : TP.Proc m) {σ : m →ₛ n} {ρ : n →ᵣ n′} → U[ P ] σ UP.⋯ₚ ρ ≡ U[ P ] (σ ·ₖ ρ)
U-σ⋯ TP.⟪ e ⟫ {σ} {ρ} = cong UP.⟪_⟫ (fusion e σ ρ)
U-σ⋯ (P TP.∥ Q)       = cong₂ UP._∥_ (U-σ⋯ P) (U-σ⋯ Q)
U-σ⋯ {n = n} {n′ = n′} (TP.ν B₁ B₂ P) {σ} {ρ} =
  cong UP.ν
    (UB-nat B₁ (K `unit , 0F , K `unit) (ρ ↑* 2) {f′ = f₁′}
       (λ τ₁ →
          UB-nat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) Ξ₁ {f′ = f₂′ (λ i → τ₁ i ⋯ Ξ₁)}
            (λ τ₂ → U-σ⋯ P ■ U-cong P (outdist τ₁ τ₂))
          ■ cong (λ cc → UB[ B₂ ] cc (f₂′ (λ i → τ₁ i ⋯ Ξ₁))) cc₂Eq)
     ■ cong (λ cc → UB[ B₁ ] cc f₁′) refl)
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Ξ₁ : (sB₁ + (2 + n)) →ᵣ (sB₁ + (2 + n′))
    Ξ₁ = (ρ ↑* 2) ↑* sB₁
    Ξ₂ : (sB₂ + (sB₁ + (2 + n))) →ᵣ (sB₂ + (sB₁ + (2 + n′)))
    Ξ₂ = Ξ₁ ↑* sB₂
    f₂′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → (sum B₂ →ₛ sB₂ + (sB₁ + (2 + n′))) → UP.Proc (sB₂ + (sB₁ + (2 + n′)))
    f₂′ σ₁ σ₂ = U[ P ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ σ₂)
                       ++ₛ (λ i → (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    f₁′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → UP.Proc (sB₁ + (2 + n′))
    f₁′ σ₁ = UB[ B₂ ] (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) (f₂′ σ₁)
    cc₂Eq : mapᶜ Ξ₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit)
    cc₂Eq = cong₂ _,_ refl (cong₂ _,_ (varΘ sB₁ (ρ ↑* 2) 1F) refl)
    outdist : ∀ (τ₁ : sum B₁ →ₛ sB₁ + (2 + n)) (τ₂ : sum B₂ →ₛ sB₂ + (sB₁ + (2 + n))) →
              (((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
                ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)) ·ₖ Ξ₂
              ≗ ((λ i → (λ j → τ₁ j ⋯ Ξ₁) i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂))
                ++ₛ (λ i → (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    outdist τ₁ τ₂ j =
        ++ₛ-⋯ ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂)
              (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) Ξ₂ j
      ■ [,]-cong compA compB (splitAt (sum B₁ + sum B₂) j)
      where
        compA : ∀ i → ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ τ₂) i ⋯ Ξ₂
                      ≡ ((λ i → (τ₁ i ⋯ Ξ₁) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ (λ i → τ₂ i ⋯ Ξ₂)) i
        compA i = ++ₛ-⋯ (λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) τ₂ Ξ₂ i
                ■ [,]-cong (λ j → sym (⋯-↑*-wk (τ₁ j) Ξ₁ sB₂)) (λ j → refl) (splitAt (sum B₁) i)
        compB : ∀ i → (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ Ξ₂
                      ≡ (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        compB i = sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) Ξ₁ sB₂)
                ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (ρ ↑* 2) sB₁))
                ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (sym (⋯-↑*-wk (σ i) ρ 2))

------------------------------------------------------------------------
-- Reduction-variant of the φ-nest congruence (threads VSub for sim→).
------------------------------------------------------------------------

VChan : UChan n → Set
VChan (e₁ , _ , e₂) = Value e₁ × Value e₂

VSub-subst : ∀ {a b D} (eq : a ≡ b) {σ : D →ₛ a} → VSub σ → VSub (subst (D →ₛ_) eq σ)
VSub-subst refl Vσ = Vσ

─→-subst : {a b : ℕ} (eq : a ≡ b) {x y : UP.Proc a} → x UR.─→ₚ y → subst UP.Proc eq x UR.─→ₚ subst UP.Proc eq y
─→-subst refl xy = xy

chanTriple-V : (cc : UChan n) → VChan cc → Value (chanTriple cc)
chanTriple-V (e₁ , c , e₂) (Ve₁ , Ve₂) = V-⊗ (V-⊗ Ve₁ V-`) Ve₂

Ub-V : (b : ℕ) (e₁ : Tm n) (c : 𝔽 n) (e₂ : Tm n) → Value e₁ → (j : 𝔽 b) → Value (Ub[ b ] (e₁ , c , e₂) j)
Ub-V (suc b) e₁ c e₂ Ve₁ zero    = V-⊗ (V-⊗ Ve₁ V-`) V-K
Ub-V (suc b) e₁ c e₂ Ve₁ (suc j) = Ub-V b (K `unit) c e₂ V-K j

Value-subst : ∀ {a b} (eq : a ≡ b) {t : Tm a} → Value t → Value (subst Tm eq t)
Value-subst refl Vt = Vt

UB-cong-─→ : (B : TP.BindGroup) (cc : UChan n) → VChan cc →
             {f g : (sum B →ₛ syncs B + n) → UP.Proc (syncs B + n)} →
             (∀ σ → VSub σ → f σ UR.─→ₚ g σ) → UB[ B ] cc f UR.─→ₚ UB[ B ] cc g
UB-cong-─→ [] cc Vcc h = h _ (λ ())
UB-cong-─→ (b ∷ []) cc Vcc h = h _ (λ _ → chanTriple-V cc Vcc)
UB-cong-─→ {n} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) (Ve₁ , Ve₂) h =
  UR.RU-Sync
    (UB-cong-─→ B (` 0F , suc x , e₂ ⋯ weakenᵣ) (V-` , Ve₂ ⋯ᵛ weakenᵣ)
      (λ σ Vσ → ─→-subst (sym (+-suc (syncs B) _))
        (h _ (λ y → Value-subst (+-suc (syncs B) _) (argV σ Vσ (splitAt b y))))))
  where
    UbV : (j : 𝔽 b) → Value ((Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)) j)
    UbV j = value-⋯ (Ub-V b (e₁ ⋯ weakenᵣ) (suc x) (` 0F) (Ve₁ ⋯ᵛ weakenᵣ) j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ z → V-`)
    argV : (σ : sum B →ₛ syncs B + suc n) (Vσ : VSub σ)
           (s : 𝔽 b ⊎ 𝔽 (sum B)) →
           Value ([ Ub[ b ] (e₁ ⋯ weakenᵣ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B) , σ ]′ s)
    argV σ Vσ (inj₁ j) = UbV j
    argV σ Vσ (inj₂ k) = Vσ k
