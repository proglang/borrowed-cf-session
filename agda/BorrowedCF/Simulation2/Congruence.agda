module BorrowedCF.Simulation2.Congruence where

-- | The (reworked) translation U[_] respects the typed structural congruence ≋.
--   Ported to the NEW (simpler) translation on git main: φ is a single Flag
--   binder; the heavy φ^ engine of the old development is gone.

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as T
import BorrowedCF.Processes.Untyped as U
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import BorrowedCF.Simulation2.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation2.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; R2; R2'; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; wk·assocSwap; toℕ-weaken*ᵣ; weaken*ᵣ~↑ʳ
        ; toℕ-swapᵣ-lt; toℕ-swapᵣ-mid; toℕ-swapᵣ-ge
        ; toℕ-assoc-lt; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-reduce≥
        ; swap-place-A; swap-place-B; swap-place-tail; R'-fix-ge; toℕ-↑*-ge; toℕ-↑*-lt
        ; commuteS; wkSwap-cancel; assocSwap-invol
        ; toℕ-assoc↑*-fix-ge; toℕ-assoc↑*-lt; toℕ-wk↑*-lt; toℕ-wk↑*-ge; toℕ-swap↑*-ge
        ; assoc-place-lo; assoc-place-mid; assoc-place-tail )

open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

-- moving a (p+q+2)-block past an (r+s+2)-block (pure ℕ arithmetic).
blockComm : ∀ p q r s Y →
            p + (q + (2 + (r + (s + (2 + Y)))))
            ≡ r + (s + (2 + (p + (q + (2 + Y)))))
blockComm p q r s Y =
  solve 5 (λ p q r s Y →
             p :+ (q :+ (con 2 :+ (r :+ (s :+ (con 2 :+ Y)))))
             := r :+ (s :+ (con 2 :+ (p :+ (q :+ (con 2 :+ Y))))))
        refl p q r s Y
  where open +-*-Solver

private
  variable
    P Q : T.Proc m

-- local stub: congruence of UB[_] in its continuation argument.
-- (will be deduplicated against TranslationProperties.UB-cong once it lands)
local-UB-cong : (B : BindGroup) (cc : UChan n)
  {f g : (sum B →ₛ syncs B + n) → U.Proc (syncs B + n)} →
  (∀ τ → f τ ≡ g τ) → UB[ B ] cc f ≡ UB[ B ] cc g
local-UB-cong []              cc h = h _
local-UB-cong (b ∷ [])        cc h = h _
local-UB-cong (b ∷ B@(_ ∷ _)) (e1 , x , e2) h =
  cong (U.φ ϕ[ b ]) (local-UB-cong B _ (λ τ → cong (subst U.Proc _) (h _)))

subst-≋ : ∀ {a b} (eq : a ≡ b) {P Q : U.Proc a} → P U.≋ Q →
          subst U.Proc eq P U.≋ subst U.Proc eq Q
subst-≋ refl r = r

-- local stub: ≋-valued congruence of UB[_] in its continuation.
local-UB-≋ : (B : BindGroup) (cc : UChan n)
  {f g : (sum B →ₛ syncs B + n) → U.Proc (syncs B + n)} →
  (∀ τ → f τ U.≋ g τ) → UB[ B ] cc f U.≋ UB[ B ] cc g
local-UB-≋ []              cc h = h _
local-UB-≋ (b ∷ [])        cc h = h _
local-UB-≋ (b ∷ B@(_ ∷ _)) (e1 , x , e2) h =
  Eq*.gmap (U.φ ϕ[ b ]) U.φ-cong′
    (local-UB-≋ B _ (λ τ → subst-≋ _ (h _)))

------------------------------------------------------------------------
-- generic transport / weakening plumbing (local; cf. old SubstLemmas)
------------------------------------------------------------------------

≡→≋ : {P Q : U.Proc n} → P ≡ Q → P U.≋ Q
≡→≋ refl = ε

local-⋯ₚ-id : (P : U.Proc m) {ρ : m →ᵣ m} → ρ ≗ idₖ → P U.⋯ₚ ρ ≡ P
local-⋯ₚ-id U.⟪ e ⟫   eq = cong U.⟪_⟫ (⋯-id e eq)
local-⋯ₚ-id (P U.∥ Q) eq = cong₂ U._∥_ (local-⋯ₚ-id P eq) (local-⋯ₚ-id Q eq)
local-⋯ₚ-id (U.ν P)   eq = cong U.ν (local-⋯ₚ-id P (id↑* 2 eq))
local-⋯ₚ-id (U.φ x P) eq = cong (U.φ x) (local-⋯ₚ-id P (id↑ eq))

subst-∥ : {a b : ℕ} (eq : a ≡ b) (A B : U.Proc a) →
          subst U.Proc eq (A U.∥ B) ≡ subst U.Proc eq A U.∥ subst U.Proc eq B
subst-∥ refl A B = refl

subst-⋯ₚ-cod : ∀ {a c d} (q : c ≡ d) (Q : U.Proc a) (θ : a →ᵣ c) →
               Q U.⋯ₚ subst (λ z → a →ᵣ z) q θ ≡ subst U.Proc q (Q U.⋯ₚ θ)
subst-⋯ₚ-cod refl Q θ = refl

subst-flip : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {a : F x} {b : F y} →
             subst F q a ≡ b → a ≡ subst F (sym q) b
subst-flip refl eq = eq

subst-ren-cod : ∀ {a c d} (q : c ≡ d) (ρ : a →ᵣ c) (x : 𝔽 a) →
                subst (λ z → a →ᵣ z) q ρ x ≡ subst 𝔽 q (ρ x)
subst-ren-cod refl ρ x = refl

substFinSuc : ∀ {a b} (p : a ≡ b) (y : 𝔽 a) → subst 𝔽 (cong suc p) (suc y) ≡ suc (subst 𝔽 p y)
substFinSuc refl y = refl

weaken*~↑ʳ : ∀ (k : ℕ) {nn} (x : 𝔽 nn) → weaken* ⦃ Kᵣ ⦄ k x ≡ k ↑ʳ x
weaken*~↑ʳ zero    x = refl
weaken*~↑ʳ (suc k) x = cong suc (weaken*~↑ʳ k x)

↑ʳ-suc : ∀ k {nn} (x : 𝔽 nn) → subst 𝔽 (+-suc k nn) (k ↑ʳ suc x) ≡ suc (k ↑ʳ x)
↑ʳ-suc zero    x = refl
↑ʳ-suc (suc j) x = substFinSuc (+-suc j _) (j ↑ʳ suc x) ■ cong suc (↑ʳ-suc j x)

-- (Rp ⋯ wk 1) ⋯ wk k  =  subst (Rp ⋯ wk (suc k))  (modulo +-suc)
weakenComp : ∀ {nn} k (Rp : U.Proc nn) →
             (Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ k
             ≡ subst U.Proc (sym (+-suc k nn)) (Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc k))
weakenComp {nn} k Rp =
    U.fusionₚ Rp (weaken* ⦃ Kᵣ ⦄ 1) (weaken* ⦃ Kᵣ ⦄ k)
  ■ U.⋯ₚ-cong Rp wkrenEq
  ■ subst-⋯ₚ-cod (sym (+-suc k nn)) Rp (weaken* ⦃ Kᵣ ⦄ (suc k))
  where
    wkrenEq : weaken* ⦃ Kᵣ ⦄ 1 ·ₖ weaken* ⦃ Kᵣ ⦄ k
              ≗ subst (λ z → nn →ᵣ z) (sym (+-suc k nn)) (weaken* ⦃ Kᵣ ⦄ (suc k))
    wkrenEq x =
        cong (weaken* ⦃ Kᵣ ⦄ k) (weaken*~↑ʳ 1 x)
      ■ weaken*~↑ʳ k (suc x)
      ■ subst-flip (+-suc k nn) (↑ʳ-suc k x)
      ■ cong (subst 𝔽 (sym (+-suc k nn))) (sym (weaken*~↑ʳ (suc k) x))
      ■ sym (subst-ren-cod (sym (+-suc k nn)) (weaken* ⦃ Kᵣ ⦄ (suc k)) x)

-- the translation commutes with renaming of its target (output).
local-U-σ⋯ : (P : T.Proc m) {σ : m →ₛ n} {ρ : n →ᵣ n′} →
             U[ P ] σ U.⋯ₚ ρ ≡ U[ P ] (σ ·ₖ ρ)
local-U-σ⋯ T.⟪ e ⟫ {σ} {ρ} = cong U.⟪_⟫ (fusion e σ ρ)
local-U-σ⋯ (P T.∥ Q)       = cong₂ U._∥_ (local-U-σ⋯ P) (local-U-σ⋯ Q)
local-U-σ⋯ {n = n} {n′ = n′} (T.ν B₁ B₂ P) {σ} {ρ} =
  cong U.ν
    (UB-nat B₁ (K `unit , 0F , K `unit) (ρ ↑* 2) {f′ = f₁′}
       (λ τ₁ →
          UB-nat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB₁ 1F , K `unit) Ξ₁ {f′ = f₂′ (λ i → τ₁ i ⋯ Ξ₁)}
            (λ τ₂ → local-U-σ⋯ P ■ U-cong P (outdist τ₁ τ₂))
          ■ cong (λ cc → UB[ B₂ ] cc (f₂′ (λ i → τ₁ i ⋯ Ξ₁))) cc₂Eq)
     ■ cong (λ cc → UB[ B₁ ] cc f₁′) refl)
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Ξ₁ : (sB₁ + (2 + n)) →ᵣ (sB₁ + (2 + n′))
    Ξ₁ = (ρ ↑* 2) ↑* sB₁
    Ξ₂ : (sB₂ + (sB₁ + (2 + n))) →ᵣ (sB₂ + (sB₁ + (2 + n′)))
    Ξ₂ = Ξ₁ ↑* sB₂
    f₂′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → (sum B₂ →ₛ sB₂ + (sB₁ + (2 + n′))) → U.Proc (sB₂ + (sB₁ + (2 + n′)))
    f₂′ σ₁ σ₂ = U[ P ] (((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ++ₛ σ₂)
                       ++ₛ (λ i → (σ ·ₖ ρ) i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    f₁′ : (sum B₁ →ₛ sB₁ + (2 + n′)) → U.Proc (sB₁ + (2 + n′))
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
-- ν-permutation lemmas
------------------------------------------------------------------------

-- push a left parallel component Rp into the φ-telescope of UB[ B ]
UB-ext : (B : BindGroup) (cc : UChan n) (Rp : U.Proc n)
         (f : (sum B →ₛ syncs B + n) → U.Proc (syncs B + n)) →
         (Rp U.∥ UB[ B ] cc f) U.≋
         UB[ B ] cc (λ τ → (Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B)) U.∥ f τ)
UB-ext []       cc Rp f = ≡→≋ (cong (U._∥ f _) (sym (local-⋯ₚ-id Rp (λ _ → refl))))
UB-ext (b ∷ []) cc Rp f = ≡→≋ (cong (U._∥ f _) (sym (local-⋯ₚ-id Rp (λ _ → refl))))
UB-ext (b ∷ B@(_ ∷ _)) (e1 , x , e2) Rp f =
  Eq*.return U.φ-ext′
  ◅◅ U.φ-cong
       ( UB-ext B cc' (Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) f'
       ◅◅ ≡→≋ (local-UB-cong B cc' perτ) )
  where
    sB = syncs B
    cc' : UChan (suc _)
    cc' = (` 0F , suc x , wk e2)
    f' : (sum B →ₛ sB + suc _) → U.Proc (sB + suc _)
    f' τ = subst U.Proc (sym (+-suc sB _))
             (f (λ y → subst Tm (+-suc sB _)
                   ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB , τ ]′ (Fin.splitAt b y))))
    perτ : ∀ τ → ((Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 1) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ sB) U.∥ f' τ
                 ≡ subst U.Proc (sym (+-suc sB _))
                     ((Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc sB)) U.∥
                      f (λ y → subst Tm (+-suc sB _)
                            ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB , τ ]′ (Fin.splitAt b y))))
    perτ τ =
        cong (U._∥ f' τ) (weakenComp sB Rp)
      ■ sym (subst-∥ (sym (+-suc sB _)) (Rp U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (suc sB)) _)

------------------------------------------------------------------------
-- φ-block infrastructure (flag-aware iterated φ binder)
------------------------------------------------------------------------

-- the φ-prefix produced by UB[ B ] (the syncs B async binders), B-indexed so
-- it matches the codomain syncs B + n of the leaf continuation exactly.
Bφ : ∀ {n} (B : BindGroup) → U.Proc (syncs B + n) → U.Proc n
Bφ []            P = P
Bφ (b ∷ [])      P = P
Bφ {n} (b ∷ B@(_ ∷ _)) P = U.φ ϕ[ b ] (Bφ B (subst U.Proc (sym (+-suc (syncs B) n)) P))

Bφ-cong : ∀ {n} (B : BindGroup) {P Q : U.Proc (syncs B + n)} →
          P U.≋ Q → Bφ {n} B P U.≋ Bφ B Q
Bφ-cong []            pq = pq
Bφ-cong (b ∷ [])      pq = pq
Bφ-cong {n} (b ∷ B@(_ ∷ _)) pq = U.φ-cong (Bφ-cong B (subst-≋ (sym (+-suc (syncs B) n)) pq))

-- the canonical leaf substitution fed to f by UB[ B ]
canonₛ : ∀ {n} (B : BindGroup) → UChan n → (sum B →ₛ syncs B + n)
canonₛ []            cc = λ ()
canonₛ (b ∷ [])      cc = Ub[ b + 0 ] cc
canonₛ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)
           , canonₛ B (` 0F , suc x , wk e2) ]′ (Fin.splitAt b y))

-- naturality of the subst-bracketed Θ-shift used inside canonₛ.
private
  ΘrelEqᵍ : ∀ {a bb} sB (ρ : a →ᵣ bb) (t : Tm (sB + suc a)) →
            subst Tm (+-suc sB a) t ⋯ (ρ ↑* suc sB)
            ≡ subst Tm (+-suc sB bb) (t ⋯ ((ρ ↑) ↑* sB))
  ΘrelEqᵍ {a} {bb} sB ρ t =
      subst-⋯-dom-local (+-suc sB a) t (ρ ↑* suc sB)
    ■ sym ( cong (λ r → subst Tm (+-suc sB bb) (t ⋯ r)) ΘθEq
          ■ cong (subst Tm (+-suc sB bb)) (subst-⋯-cod-local (sym (+-suc sB bb)) t θ⁻)
          ■ subst-subst-sym-local (+-suc sB bb) )
    where
      θ⁻ : (sB + suc a) →ᵣ suc (sB + bb)
      θ⁻ = subst (λ z → z →ᵣ suc (sB + bb)) (sym (+-suc sB a)) (ρ ↑* suc sB)
      ΘθEq : (ρ ↑) ↑* sB ≡ subst (λ z → (sB + suc a) →ᵣ z) (sym (+-suc sB bb)) θ⁻
      ΘθEq = sym ( sym (subst₂→ (sym (+-suc sB a)) (sym (+-suc sB bb)) (ρ ↑* suc sB))
                 ■ cong (subst₂ _→ᵣ_ (sym (+-suc sB a)) (sym (+-suc sB bb))) (sym (liftCast sB ρ))
                 ■ subst₂-cancel-local (+-suc sB a) (+-suc sB bb) ((ρ ↑) ↑* sB) )

  chReqᵍ : ∀ {a bb} sB (e1 : Tm a) (x : 𝔽 a) (ρ : a →ᵣ bb) →
           (chanTriple (wk e1 , suc x , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ((ρ ↑) ↑* sB)
           ≡ chanTriple (wk (e1 ⋯ ρ) , suc (ρ x) , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB
  chReqᵍ sB e1 x ρ = cong₂ _⊗_
      (cong₂ _⊗_
        (sym (⋯-↑*-wk (wk e1) (ρ ↑) sB) ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (⋯-↑-wk e1 ρ)))
        (cong `_ (varΘ sB (ρ ↑) (suc x))))
      (cong `_ (varΘ sB (ρ ↑) 0F))

  UbReqᵍ : ∀ {a bb} b sB (e1 : Tm a) (x : 𝔽 a) (ρ : a →ᵣ bb) (j : 𝔽 b) →
           (Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j ⋯ ((ρ ↑) ↑* sB)
           ≡ (Ub[ b ] (wk (e1 ⋯ ρ) , suc (ρ x) , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j
  UbReqᵍ b sB e1 x ρ j =
      sym (⋯-↑*-wk (Ub[ b ] (wk e1 , suc x , ` 0F) j) (ρ ↑) sB)
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (Ub-nat b (wk e1 , suc x , ` 0F) (ρ ↑) j)
    ■ cong (λ cc → Ub[ b ] cc j ⋯ weaken* ⦃ Kᵣ ⦄ sB)
        (cong₂ _,_ (sym (⋯-↑-wk e1 ρ)) refl)

-- canonₛ is natural in its channel triple under target renamings.
canonₛ-nat : ∀ {a bb} (B : BindGroup) (cc : UChan a) (ρ : a →ᵣ bb) (i : 𝔽 (sum B)) →
             canonₛ B cc i ⋯ (ρ ↑* syncs B) ≡ canonₛ B (mapᶜ ρ cc) i
canonₛ-nat []            cc ρ ()
canonₛ-nat (b ∷ [])      (e1 , x , e2) ρ i = Ub-nat (b + 0) (e1 , x , e2) ρ i
canonₛ-nat {a} {bb} (b ∷ B@(_ ∷ _)) (e1 , x , e2) ρ i
  with Fin.splitAt b i | canonₛ-nat B (` 0F , suc x , wk e2) (ρ ↑)
... | inj₁ j | _  = ΘrelEqᵍ (syncs B) ρ ((Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)) j)
                  ■ cong (subst Tm (+-suc (syncs B) bb)) (UbReqᵍ b (syncs B) e1 x ρ j)
... | inj₂ k | ih = ΘrelEqᵍ (syncs B) ρ (canonₛ B (` 0F , suc x , wk e2) k)
                  ■ cong (subst Tm (+-suc (syncs B) bb))
                      ( ih k
                      ■ cong (λ cc → canonₛ B cc k)
                          (cong₂ _,_ refl (cong₂ _,_ refl (sym (⋯-↑-wk e2 ρ)))) )

-- UB[ B ] unfolds to its φ-prefix wrapped around the leaf at the canonical sub.
UB-flat : ∀ {n} (B : BindGroup) (cc : UChan n)
          (f : (sum B →ₛ syncs B + n) → U.Proc (syncs B + n)) →
          UB[ B ] cc f ≡ Bφ B (f (canonₛ B cc))
UB-flat []            cc f = refl
UB-flat (b ∷ [])      cc f = refl
UB-flat {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) f =
  cong (U.φ ϕ[ b ]) (UB-flat B (` 0F , suc x , wk e2) leaffn)
  where
    sB = syncs B
    leaffn : (sum B →ₛ sB + suc n) → U.Proc (sB + suc n)
    leaffn = λ τ → subst U.Proc (sym (+-suc sB n))
               (f (λ y → subst Tm (+-suc sB n)
                     ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB , τ ]′ (Fin.splitAt b y))))

-- the leaf substitution of a flattened ν-block
leafσ : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) →
        (sum B₁ + sum B₂ + m →ₛ syncs B₂ + (syncs B₁ + (2 + n)))
leafσ {m} {n} σ B₁ B₂ =
  ((λ i → canonₛ B₁ (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ
    canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit))
   ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))

Uν-flat : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) (P : T.Proc (sum B₁ + sum B₂ + m)) →
          U[ T.ν B₁ B₂ P ] σ ≡ U.ν (Bφ B₁ (Bφ B₂ (U[ P ] (leafσ σ B₁ B₂))))
Uν-flat {m} {n} σ B₁ B₂ P =
  cong U.ν
    ( UB-flat B₁ (K `unit , 0F , K `unit) g
    ■ cong (Bφ B₁) (UB-flat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
                      (leaf (canonₛ B₁ (K `unit , 0F , K `unit)))) )
  where
    leaf : (sum B₁ →ₛ syncs B₁ + (2 + n)) → (sum B₂ →ₛ syncs B₂ + (syncs B₁ + (2 + n))) →
           U.Proc (syncs B₂ + (syncs B₁ + (2 + n)))
    leaf τ₁ τ₂ = U[ P ] (((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂)
                   ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)))
    g : (sum B₁ →ₛ syncs B₁ + (2 + n)) → U.Proc (syncs B₁ + (2 + n))
    g τ₁ = UB[ B₂ ] (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) (leaf τ₁)

------------------------------------------------------------------------
-- φ-binder block transpose engine (against Bφ directly)
------------------------------------------------------------------------

-- Bφ commutes with renaming of its body (naturality), modulo ↑* over the
-- syncs B local binders.
Bφ-⋯ : ∀ {n n′} (B : BindGroup) (P : U.Proc (syncs B + n)) (ρ : n →ᵣ n′) →
       Bφ B P U.⋯ₚ ρ ≡ Bφ B (P U.⋯ₚ (ρ ↑* syncs B))
Bφ-⋯ []            P ρ = refl
Bφ-⋯ (b ∷ [])      P ρ = refl
Bφ-⋯ {n} {n′} (b ∷ B@(_ ∷ _)) P ρ =
  cong (U.φ ϕ[ b ])
    ( Bφ-⋯ B (subst U.Proc (sym (+-suc (syncs B) n)) P) (ρ ↑)
    ■ cong (Bφ B) bodyeq )
  where
    sB = syncs B
    Θ : (sB + suc n) →ᵣ (sB + suc n′)
    Θ = (ρ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ᵣ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ᵣ z) (sym (+-suc sB n′)) (ρ ↑* suc sB)
    Θ⁺eq = subst-flip (+-suc sB n′) (sym (subst₂→ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCast sB ρ)
    bodyeq : (subst U.Proc (sym (+-suc sB n)) P) U.⋯ₚ ((ρ ↑) ↑* sB)
             ≡ subst U.Proc (sym (+-suc sB n′)) (P U.⋯ₚ (ρ ↑* suc sB))
    bodyeq =
        TP-subst-⋯ₚ-dom (+-suc sB n) P Θ
      ■ cong (P U.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-cod (sym (+-suc sB n′)) P (ρ ↑* suc sB)

-- subst over U.Proc commutes through a φ-binder.
subst-φ : ∀ {a b} (eq : a ≡ b) {z : U.Flag} (Q : U.Proc (suc a)) →
          subst U.Proc eq (U.φ z Q) ≡ U.φ z (subst U.Proc (cong suc eq) Q)
subst-φ refl Q = refl

-- transport a renaming through substs on both ends when the renamings agree
-- pointwise modulo the index coercions.
substⱼ-⋯ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (X : U.Proc a′)
           (ρ : a →ᵣ b) (ρ′ : a′ →ᵣ b′) →
           (∀ x → ρ x ≡ subst 𝔽 (sym q) (ρ′ (subst 𝔽 p x))) →
           subst U.Proc (sym p) X U.⋯ₚ ρ ≡ subst U.Proc (sym q) (X U.⋯ₚ ρ′)
substⱼ-⋯ refl refl X ρ ρ′ h = U.⋯ₚ-cong X h

-- Tm-level analogue of substⱼ-⋯.
substⱼ-⋯ₜ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (t : Tm a′)
            (ρ : a →ᵣ b) (ρ′ : a′ →ᵣ b′) →
            (∀ x → ρ x ≡ subst 𝔽 (sym q) (ρ′ (subst 𝔽 p x))) →
            subst Tm (sym p) t ⋯ ρ ≡ subst Tm (sym q) (t ⋯ ρ′)
substⱼ-⋯ₜ refl refl t ρ ρ′ h = ⋯-cong t h

-- Push a single φ binder past a whole Bφ B block (the heart of the swap).
φ-past-Bφ : (B : BindGroup) (z : U.Flag) {n : ℕ} (X : U.Proc (syncs B + suc n)) →
            U.φ z (Bφ B X) U.≋
            Bφ B (U.φ z (X U.⋯ₚ assocSwapᵣ (syncs B) 1))
φ-past-Bφ []            z X = ≡→≋ (cong (U.φ z) (sym (local-⋯ₚ-id X assocSwap-01)))
φ-past-Bφ (b ∷ [])      z X = ≡→≋ (cong (U.φ z) (sym (local-⋯ₚ-id X assocSwap-01)))
φ-past-Bφ (b ∷ B@(_ ∷ _)) z {n} X =
     Eq*.return U.φ-comm′
  ◅◅ U.φ-cong
       ( U.φ-cong (≡→≋ (Bφ-⋯ B W (assocSwapᵣ 1 1)))
       ◅◅ φ-past-Bφ B z (W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sB'))
       ◅◅ Bφ-cong B (≡→≋ bodyren) )
  where
    sB' = syncs B
    W : U.Proc (sB' + suc (suc n))
    W = subst U.Proc (sym (+-suc sB' (suc n))) X
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl
    cast≡subst : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.cast e y ≡ subst 𝔽 e y
    cast≡subst refl y = Fin.cast-is-id refl y
    ρ₁ : (sB' + suc (suc n)) →ᵣ suc (sB' + suc n)
    ρ₁ = (assocSwapᵣ 1 1 {n} ↑* sB') ·ₖ assocSwapᵣ sB' 1 {suc n}
    ptwise : ∀ x → ρ₁ x ≡ subst 𝔽 (cong suc (sym (+-suc sB' n)))
                          (assocSwapᵣ (suc sB') 1 {n} (subst 𝔽 (+-suc sB' (suc n)) x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R3 sB' x
      ■ cong (λ w → Fin.toℕ (assocSwapᵣ (suc sB') 1 w)) (cast≡subst (+-suc sB' (suc n)) x)
      ■ sym (toℕ-subst𝔽 (cong suc (sym (+-suc sB' n)))
               (assocSwapᵣ (suc sB') 1 (subst 𝔽 (+-suc sB' (suc n)) x))) )
    bodyren : U.φ z ((W U.⋯ₚ (assocSwapᵣ 1 1 ↑* sB')) U.⋯ₚ assocSwapᵣ sB' 1)
              ≡ subst U.Proc (sym (+-suc sB' n))
                  (U.φ z (X U.⋯ₚ assocSwapᵣ (suc sB') 1))
    qq : suc (suc (sB' + n)) ≡ suc (sB' + suc n)
    qq = cong suc (sym (+-suc sB' n))
    bodyren =
        cong (U.φ z) (U.fusionₚ W (assocSwapᵣ 1 1 ↑* sB') (assocSwapᵣ sB' 1))
      ■ cong (U.φ z) (substⱼ-⋯ (+-suc sB' (suc n)) (sym qq) X ρ₁ (assocSwapᵣ (suc sB') 1)
                       (λ x → ptwise x ■ cong (λ e → subst 𝔽 e (assocSwapᵣ (suc sB') 1 (subst 𝔽 (+-suc sB' (suc n)) x)))
                                            (≡-irrelevant qq (sym (sym qq)))))
      ■ cong (U.φ z) (cong (λ e → subst U.Proc e (X U.⋯ₚ assocSwapᵣ (suc sB') 1)) (≡-irrelevant (sym (sym qq)) qq))
      ■ sym (subst-φ (sym (+-suc sB' n)) (X U.⋯ₚ assocSwapᵣ (suc sB') 1))

-- subst over U.Proc commutes through a ν-binder.
subst-ν : ∀ {a b} (eq : a ≡ b) (Q : U.Proc (2 + a)) →
          subst U.Proc eq (U.ν Q) ≡ U.ν (subst U.Proc (cong (2 +_) eq) Q)
subst-ν refl Q = refl

-- Push a single ν binder (binds 2) past a whole Bφ B block.
ν-past-Bφ : (B : BindGroup) {n : ℕ} (X : U.Proc (syncs B + (2 + n))) →
            U.ν (Bφ B X) U.≋
            Bφ B (U.ν (X U.⋯ₚ assocSwapᵣ (syncs B) 2))
ν-past-Bφ []            X = ≡→≋ (cong U.ν (sym (local-⋯ₚ-id X (assocSwap-0a 2))))
ν-past-Bφ (b ∷ [])      X = ≡→≋ (cong U.ν (sym (local-⋯ₚ-id X (assocSwap-0a 2))))
ν-past-Bφ (b ∷ B@(_ ∷ _)) {n} X =
     Eq*.return U.νφ-comm′
  ◅◅ U.φ-cong
       ( U.ν-cong (≡→≋ (Bφ-⋯ B W (assocSwapᵣ 1 2)))
       ◅◅ ν-past-Bφ B (W U.⋯ₚ (assocSwapᵣ 1 2 ↑* sB'))
       ◅◅ Bφ-cong B (≡→≋ bodyren) )
  where
    sB' = syncs B
    W : U.Proc (sB' + (2 + suc n))
    W = subst U.Proc (sym (+-suc sB' (2 + n))) X
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl
    cast≡subst : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.cast e y ≡ subst 𝔽 e y
    cast≡subst refl y = Fin.cast-is-id refl y
    ρ₁ : (sB' + (2 + suc n)) →ᵣ 2 + (sB' + suc n)
    ρ₁ = (assocSwapᵣ 1 2 {n} ↑* sB') ·ₖ assocSwapᵣ sB' 2 {suc n}
    ptwise : ∀ x → ρ₁ x ≡ subst 𝔽 (cong (2 +_) (sym (+-suc sB' n)))
                          (assocSwapᵣ (suc sB') 2 {n} (subst 𝔽 (+-suc sB' (2 + n)) x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R3₂ sB' x
      ■ cong (λ w → Fin.toℕ (assocSwapᵣ (suc sB') 2 w)) (cast≡subst (+-suc sB' (2 + n)) x)
      ■ sym (toℕ-subst𝔽 (cong (2 +_) (sym (+-suc sB' n)))
               (assocSwapᵣ (suc sB') 2 (subst 𝔽 (+-suc sB' (2 + n)) x))) )
    qq2 : (2 + suc (sB' + n)) ≡ (2 + (sB' + suc n))
    qq2 = cong (2 +_) (sym (+-suc sB' n))
    bodyren : U.ν ((W U.⋯ₚ (assocSwapᵣ 1 2 ↑* sB')) U.⋯ₚ assocSwapᵣ sB' 2)
              ≡ subst U.Proc (sym (+-suc sB' n))
                  (U.ν (X U.⋯ₚ assocSwapᵣ (suc sB') 2))
    bodyren =
        cong U.ν (U.fusionₚ W (assocSwapᵣ 1 2 ↑* sB') (assocSwapᵣ sB' 2))
      ■ cong U.ν (substⱼ-⋯ (+-suc sB' (2 + n)) (sym qq2) X ρ₁ (assocSwapᵣ (suc sB') 2)
                   (λ x → ptwise x ■ cong (λ e → subst 𝔽 e (assocSwapᵣ (suc sB') 2 (subst 𝔽 (+-suc sB' (2 + n)) x)))
                                        (≡-irrelevant (cong (2 +_) (sym (+-suc sB' n))) (sym (sym qq2)))))
      ■ cong U.ν (cong (λ e → subst U.Proc e (X U.⋯ₚ assocSwapᵣ (suc sB') 2)) (≡-irrelevant (sym (sym qq2)) qq2))
      ■ sym (subst-ν (sym (+-suc sB' n)) (X U.⋯ₚ assocSwapᵣ (suc sB') 2))

-- Pull a ν binder OUT of a Bφ B block (reverse of ν-past-Bφ).
Bφ-past-ν : (B : BindGroup) {n : ℕ} (Y : U.Proc (2 + (syncs B + n))) →
            Bφ B (U.ν Y) U.≋
            U.ν (Bφ B (Y U.⋯ₚ assocSwapᵣ 2 (syncs B)))
Bφ-past-ν B {n} Y =
     Eq*.symmetric _
       ( ν-past-Bφ B (Y U.⋯ₚ assocSwapᵣ 2 (syncs B))
       ◅◅ Bφ-cong B (U.ν-cong (≡→≋ bodyid)) )
  where
    bodyid : (Y U.⋯ₚ assocSwapᵣ 2 (syncs B)) U.⋯ₚ assocSwapᵣ (syncs B) 2 ≡ Y
    bodyid = U.fusionₚ Y (assocSwapᵣ 2 (syncs B)) (assocSwapᵣ (syncs B) 2)
           ■ local-⋯ₚ-id Y (assocSwap-invol 2 (syncs B))

-- subst over U.Proc commutes through a whole Bφ block.
subst-Bφ : ∀ {a a′} (e : a ≡ a′) (B : BindGroup) (Y : U.Proc (syncs B + a)) →
           subst U.Proc e (Bφ B Y) ≡ Bφ B (subst U.Proc (cong (syncs B +_) e) Y)
subst-Bφ refl B Y = refl

-- Block transpose: swap two Bφ blocks, accumulating an assocSwap on the body.
Bφ-transpose : (B₁ B₂ : BindGroup) {n : ℕ} (X : U.Proc (syncs B₂ + (syncs B₁ + n))) →
               Bφ B₁ (Bφ B₂ X) U.≋
               Bφ B₂ (Bφ B₁ (X U.⋯ₚ assocSwapᵣ (syncs B₂) (syncs B₁)))
Bφ-transpose []            B₂ X =
  ≡→≋ (cong (Bφ B₂) (sym (local-⋯ₚ-id X (R-base-b0 (syncs B₂)))))
Bφ-transpose (b ∷ [])      B₂ X =
  ≡→≋ (cong (Bφ B₂) (sym (local-⋯ₚ-id X (R-base-b0 (syncs B₂)))))
Bφ-transpose (b ∷ B₁@(_ ∷ _)) B₂ {n} X =
     ≡→≋ (cong (U.φ ϕ[ b ]) (cong (Bφ B₁) (subst-Bφ (sym (+-suc sA' n)) B₂ X)))
  ◅◅ U.φ-cong (Bφ-transpose B₁ B₂ X₁)
  ◅◅ φ-past-Bφ B₂ ϕ[ b ] (Bφ B₁ (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA'))
  ◅◅ Bφ-cong B₂ (U.φ-cong (≡→≋ (Bφ-⋯ B₁ (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') (assocSwapᵣ sB₂ 1))))
  ◅◅ Bφ-cong B₂ (≡→≋ reconcile)
  where
    sA' = syncs B₁
    sB₂ = syncs B₂
    pc = cong (sB₂ +_) (+-suc sA' n)
    X₁ : U.Proc (sB₂ + (sA' + suc n))
    X₁ = subst U.Proc (cong (sB₂ +_) (sym (+-suc sA' n))) X
    X₁≡ : X₁ ≡ subst U.Proc (sym pc) X
    X₁≡ = cong (λ e → subst U.Proc e X) (≡-irrelevant (cong (sB₂ +_) (sym (+-suc sA' n))) (sym pc))
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl
    cast≡subst : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.cast e y ≡ subst 𝔽 e y
    cast≡subst refl y = Fin.cast-is-id refl y
    ρ₂ : (sB₂ + (sA' + suc n)) →ᵣ sA' + (1 + (sB₂ + n))
    ρ₂ = assocSwapᵣ sB₂ sA' ·ₖ (assocSwapᵣ sB₂ 1 ↑* sA')
    ptwise : ∀ x → ρ₂ x ≡ subst 𝔽 (sym (+-suc sA' (sB₂ + n)))
                         (assocSwapᵣ sB₂ (suc sA') (subst 𝔽 pc x))
    ptwise x = Fin.toℕ-injective
      ( toℕ-R4 sB₂ sA' x
      ■ cong (λ w → Fin.toℕ (assocSwapᵣ sB₂ (suc sA') w)) (cast≡subst pc x)
      ■ sym (toℕ-subst𝔽 (sym (+-suc sA' (sB₂ + n)))
               (assocSwapᵣ sB₂ (suc sA') (subst 𝔽 pc x))) )
    bodyEq : (X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')
             ≡ subst U.Proc (sym (+-suc sA' (sB₂ + n))) (X U.⋯ₚ assocSwapᵣ sB₂ (suc sA'))
    bodyEq =
        cong (λ z → (z U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')) X₁≡
      ■ U.fusionₚ (subst U.Proc (sym pc) X) (assocSwapᵣ sB₂ sA') (assocSwapᵣ sB₂ 1 ↑* sA')
      ■ substⱼ-⋯ pc (+-suc sA' (sB₂ + n)) X ρ₂ (assocSwapᵣ sB₂ (suc sA')) ptwise
    reconcile : U.φ ϕ[ b ] (Bφ B₁ ((X₁ U.⋯ₚ assocSwapᵣ sB₂ sA') U.⋯ₚ (assocSwapᵣ sB₂ 1 ↑* sA')))
                ≡ Bφ (b ∷ B₁) (X U.⋯ₚ assocSwapᵣ sB₂ (suc sA'))
    reconcile = cong (U.φ ϕ[ b ]) (cong (Bφ B₁) bodyEq)

------------------------------------------------------------------------
-- leaf-substitution reconcile for the ν-swap case
------------------------------------------------------------------------

-- read off leafσ at an index whose outer splitAt is known to land in the
-- B-region (inj₁) and whose inner splitAt is known.
leafσ-B₁ : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) (y : 𝔽 (sum B₁ + sum B₂ + m))
           (z : 𝔽 (sum B₁ + sum B₂)) (k : 𝔽 (sum B₂)) →
           Fin.splitAt (sum B₁ + sum B₂) y ≡ inj₁ z → Fin.splitAt (sum B₁) z ≡ inj₂ k →
           leafσ σ B₁ B₂ y ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) k
leafσ-B₁ σ B₁ B₂ y z k e1 e2 =
  cong [ _ , _ ]′ e1 ■ cong [ _ , _ ]′ e2

leafσ-A₁ : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) (y : 𝔽 (sum B₁ + sum B₂ + m))
           (z : 𝔽 (sum B₁ + sum B₂)) (j : 𝔽 (sum B₁)) →
           Fin.splitAt (sum B₁ + sum B₂) y ≡ inj₁ z → Fin.splitAt (sum B₁) z ≡ inj₁ j →
           leafσ σ B₁ B₂ y ≡ canonₛ B₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
leafσ-A₁ σ B₁ B₂ y z j e1 e2 =
  cong [ _ , _ ]′ e1 ■ cong [ _ , _ ]′ e2

leafσ-tail : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) (y : 𝔽 (sum B₁ + sum B₂ + m))
             (i : 𝔽 m) → Fin.splitAt (sum B₁ + sum B₂) y ≡ inj₂ i →
             leafσ σ B₁ B₂ y ≡ σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
leafσ-tail σ B₁ B₂ y i e1 = cong [ _ , _ ]′ e1

-- the swapᵣ 1 1 lifted past j inert binders lowers (weaken* j 1F) to (weaken* j 0F).
swap-lower : ∀ j {p} → (swapᵣ 1 1 {p} ↑* j) (weaken* ⦃ Kᵣ ⦄ j (Fin.suc (Fin.zero {n = p})))
                       ≡ weaken* ⦃ Kᵣ ⦄ j (Fin.zero {n = suc p})
swap-lower j {p} = Fin.toℕ-injective
  ( toℕ-↑*-ge (swapᵣ 1 1 {p}) j (weaken* ⦃ Kᵣ ⦄ j (Fin.suc Fin.zero)) q
  ■ cong (j +_) ( cong (λ z → Fin.toℕ (swapᵣ 1 1 z)) red≡fin
                ■ toℕ-swapᵣ-mid 1 1 (Fin.suc (Fin.zero {n = p})) (Nat.s≤s Nat.z≤n) (Nat.s≤s (Nat.s≤s Nat.z≤n)) )
  ■ cong (j +_) refl
  ■ sym (toℕ-weaken*ᵣ j (Fin.zero {n = suc p})) )
  where
    q : j Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ j (Fin.suc (Fin.zero {n = p})))
    q = subst (j Nat.≤_) (sym (toℕ-weaken*ᵣ j (Fin.suc (Fin.zero {n = p})))) (Nat.m≤m+n j 1)
    red≡fin : Fin.reduce≥ (weaken* ⦃ Kᵣ ⦄ j (Fin.suc (Fin.zero {n = p}))) q ≡ Fin.suc (Fin.zero {n = p})
    red≡fin = Fin.toℕ-injective (toℕ-reduce≥ (weaken* ⦃ Kᵣ ⦄ j (Fin.suc Fin.zero)) q
                ■ cong (Nat._∸ j) (toℕ-weaken*ᵣ j (Fin.suc (Fin.zero {n = p}))) ■ Nat.m+n∸m≡n j 1)

-- region-B₂ leaf reconcile, generalised over the B₁-block width j.
canonₛ-Swk : ∀ {p} (B : BindGroup) (j : ℕ) (k : 𝔽 (sum B)) →
  canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ j (Fin.suc (Fin.zero {n = p})) , K `unit) k
    ⋯ assocSwapᵣ (syncs B) j
    ⋯ ((swapᵣ 1 1 {p} ↑* (syncs B)) ↑* j)
  ≡ canonₛ B (K `unit , 0F , K `unit) k ⋯ weaken* ⦃ Kᵣ ⦄ j
canonₛ-Swk {p} B j k =
    fusion (canonₛ B ccL k) (assocSwapᵣ sB j) R'
  ■ ⋯-cong (canonₛ B ccL k) (commuteS sB j)
  ■ sym (fusion (canonₛ B ccL k) ((swapᵣ 1 1 {p} ↑* j) ↑* sB) (assocSwapᵣ sB j))
  ■ cong (_⋯ assocSwapᵣ sB j) (canonₛ-nat B ccL (swapᵣ 1 1 {p} ↑* j) k)
  ■ cong (λ cc → canonₛ B cc k ⋯ assocSwapᵣ sB j) ccM≡
  ■ cong (_⋯ assocSwapᵣ sB j) (sym (canonₛ-nat B (K `unit , 0F , K `unit) (weaken* ⦃ Kᵣ ⦄ j) k))
  ■ fusion (canonₛ B (K `unit , 0F , K `unit) k) (weaken* ⦃ Kᵣ ⦄ j ↑* sB) (assocSwapᵣ sB j)
  ■ ⋯-cong (canonₛ B (K `unit , 0F , K `unit) k) (wkSwap-cancel sB j)
  where
    sB = syncs B
    ccL = (K `unit , weaken* ⦃ Kᵣ ⦄ j (Fin.suc (Fin.zero {n = p})) , K `unit)
    R'  = (swapᵣ 1 1 {p} ↑* sB) ↑* j
    ccM≡ : mapᶜ (swapᵣ 1 1 {p} ↑* j) ccL ≡ mapᶜ (weaken* ⦃ Kᵣ ⦄ j) (K `unit , 0F , K `unit)
    ccM≡ = cong (λ z → (K `unit , z , K `unit)) (swap-lower j)

-- region-B₂ leaf reconcile (the channel of canonₛ B₂ is the B₁-side flag, which
-- the assocSwap/swap renaming must lower from weaken* sB₁ 1F back to 0F).
canonₛ-B₂-reconcile : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) (k : 𝔽 (sum B₂)) →
  canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) (Fin.suc (Fin.zero {n = n})) , K `unit) k
    ⋯ assocSwapᵣ (syncs B₂) (syncs B₁)
    ⋯ ((swapᵣ 1 1 ↑* (syncs B₂)) ↑* (syncs B₁))
  ≡ canonₛ B₂ (K `unit , 0F , K `unit) k ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)
canonₛ-B₂-reconcile σ B₁ B₂ k = canonₛ-Swk B₂ (syncs B₁) k

-- the combined renaming on the body
subEq-gen : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ : BindGroup) →
            (leafσ σ B₁ B₂ ·ₖ assocSwapᵣ (syncs B₂) (syncs B₁))
              ·ₖ ((swapᵣ 1 1 ↑* (syncs B₂)) ↑* (syncs B₁))
            ≗ swapᵣ (sum B₁) (sum B₂) ·ₖ leafσ σ B₂ B₁
subEq-gen {m} {n} σ B₁ B₂ i = body
  where
    b1 = sum B₁
    b2 = sum B₂
    sB1 = syncs B₁
    sB2 = syncs B₂
    R' : (sB1 + (sB2 + (2 + n))) →ᵣ (sB1 + (sB2 + (2 + n)))
    R' = (swapᵣ 1 1 ↑* sB2) ↑* sB1
    cc₀ : UChan (2 + n)
    cc₀ = (K `unit , 0F , K `unit)
    -- region-B₁ renaming reconcile: weaken* sB2 ·ₖ (assocSwap ·ₖ R') = (swapᵣ11 ·ₖ weaken* sB2) ↑* sB1
    lemA : ((weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ assocSwapᵣ sB2 sB1) ·ₖ R')
           ≗ (swapᵣ 1 1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ↑* sB1
    lemA x =
        cong R' (wk·assocSwap sB2 sB1 x)
      ■ sym (dist-↑*-· sB1 (weaken* ⦃ Kᵣ ⦄ sB2) (swapᵣ 1 1 ↑* sB2) x)
      ■ cong (λ ρ → (ρ ↑* sB1) x) (sym (funext (λ y → ↑*-wk (swapᵣ 1 1) sB2 y)))
    -- LHS reduced: leafσ σ B₁ B₂ i ⋯ assocSwapᵣ sB2 sB1 ⋯ R'
    body : ((leafσ σ B₁ B₂ ·ₖ assocSwapᵣ sB2 sB1) ·ₖ R') i
           ≡ (swapᵣ b1 b2 ·ₖ leafσ σ B₂ B₁) i
    body with Fin.splitAt (b1 + b2) i in eqo
    ... | inj₂ ii = lhsTail ■ sym rhsTail
      where
        i≡ : (b1 + b2) ↑ʳ ii ≡ i
        i≡ = Fin.splitAt⁻¹-↑ʳ eqo
        -- LHS region tail
        lhsTail : (σ ii ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                    ⋯ assocSwapᵣ sB2 sB1 ⋯ R'
                  ≡ σ ii ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1
        lhsTail =
            fuse5
          ■ ⋯-cong (σ ii) tailRen
          ■ sym fuse3
          where
            -- combine the five LHS renamings into one applied to σ ii
            ren5 : n →ᵣ (sB1 + (sB2 + (2 + n)))
            ren5 = (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ assocSwapᵣ sB2 sB1) ·ₖ R'
            ren3 : n →ᵣ (sB1 + (sB2 + (2 + n)))
            ren3 = (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1
            fuse5 : σ ii ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ assocSwapᵣ sB2 sB1 ⋯ R'
                    ≡ σ ii ⋯ ren5
            fuse5 =
                cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ assocSwapᵣ sB2 sB1 ⋯ R') (fusion (σ ii) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
              ■ cong (λ t → t ⋯ assocSwapᵣ sB2 sB1 ⋯ R') (fusion (σ ii) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
              ■ cong (_⋯ R') (fusion (σ ii) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) (assocSwapᵣ sB2 sB1))
              ■ fusion (σ ii) (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ assocSwapᵣ sB2 sB1) R'
            fuse3 : σ ii ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ≡ σ ii ⋯ ren3
            fuse3 =
                cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB1) (fusion (σ ii) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB2))
              ■ fusion (σ ii) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ sB1)
            -- the underlying renaming identity (true because every index lands ≥ 2)
            tailRen : ren5 ≗ ren3
            tailRen y = Fin.toℕ-injective (lhsN ■ sym rhsN)
              where
                w0 = weaken* ⦃ Kᵣ ⦄ 2 y
                w1 = weaken* ⦃ Kᵣ ⦄ sB1 w0
                w12 = weaken* ⦃ Kᵣ ⦄ sB2 w1
                as = assocSwapᵣ sB2 sB1 w12
                w0N : Fin.toℕ w0 ≡ 2 + Fin.toℕ y
                w0N = toℕ-weaken*ᵣ 2 y
                w1N : Fin.toℕ w1 ≡ sB1 + (2 + Fin.toℕ y)
                w1N = toℕ-weaken*ᵣ sB1 w0 ■ cong (sB1 +_) w0N
                w12N : Fin.toℕ w12 ≡ sB2 + (sB1 + (2 + Fin.toℕ y))
                w12N = toℕ-weaken*ᵣ sB2 w1 ■ cong (sB2 +_) w1N
                asN : Fin.toℕ as ≡ sB2 + (sB1 + (2 + Fin.toℕ y))
                asN = toℕ-assoc-ge sB2 sB1 w12
                        (subst (sB2 + sB1 Nat.≤_) (sym w12N)
                          (Nat.+-monoʳ-≤ sB2 (Nat.m≤m+n sB1 (2 + Fin.toℕ y))))
                      ■ w12N
                geR : sB1 + (sB2 + 2) Nat.≤ Fin.toℕ as
                geR = subst (sB1 + (sB2 + 2) Nat.≤_) (sym asN)
                        (subst (Nat._≤ sB2 + (sB1 + (2 + Fin.toℕ y))) (sym assoc-eq)
                          (Nat.+-monoʳ-≤ sB2 (Nat.+-monoʳ-≤ sB1 (Nat.+-monoʳ-≤ 2 (Nat.z≤n {Fin.toℕ y})))))
                  where assoc-eq : sB1 + (sB2 + 2) ≡ sB2 + (sB1 + 2)
                        assoc-eq = sym (Nat.+-assoc sB1 sB2 2) ■ cong (Nat._+ 2) (Nat.+-comm sB1 sB2) ■ Nat.+-assoc sB2 sB1 2
                lhsN : Fin.toℕ (ren5 y) ≡ sB2 + (sB1 + (2 + Fin.toℕ y))
                lhsN = R'-fix-ge sB1 sB2 as geR ■ asN
                rhsN : Fin.toℕ (ren3 y) ≡ sB2 + (sB1 + (2 + Fin.toℕ y))
                rhsN = toℕ-weaken*ᵣ sB1 (weaken* ⦃ Kᵣ ⦄ sB2 w0) ■ cong (sB1 +_) (toℕ-weaken*ᵣ sB2 w0 ■ cong (sB2 +_) w0N)
                     ■ (sym (Nat.+-assoc sB1 sB2 (2 + Fin.toℕ y)) ■ cong (Nat._+ (2 + Fin.toℕ y)) (Nat.+-comm sB1 sB2) ■ Nat.+-assoc sB2 sB1 (2 + Fin.toℕ y))
        rhsTail : leafσ σ B₂ B₁ ((b2 + b1) ↑ʳ ii)
                  ≡ σ ii ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1
        rhsTail = leafσ-tail σ B₂ B₁ ((b2 + b1) ↑ʳ ii) ii (Fin.splitAt-↑ʳ (b2 + b1) m ii)
    ... | inj₁ z with Fin.splitAt b1 z in eqi
    ...   | inj₁ j = lhsB₁ ■ sym rhsB₁
      where
        lhsB₁ : (canonₛ B₁ cc₀ j ⋯ weaken* ⦃ Kᵣ ⦄ sB2) ⋯ assocSwapᵣ sB2 sB1 ⋯ R'
                ≡ canonₛ B₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB2 (Fin.suc Fin.zero) , K `unit) j
        lhsB₁ =
            cong (_⋯ R') (fusion (canonₛ B₁ cc₀ j) (weaken* ⦃ Kᵣ ⦄ sB2) (assocSwapᵣ sB2 sB1))
          ■ fusion (canonₛ B₁ cc₀ j) (weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ assocSwapᵣ sB2 sB1) R'
          ■ ⋯-cong (canonₛ B₁ cc₀ j) lemA
          ■ canonₛ-nat B₁ cc₀ (swapᵣ 1 1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) j
          ■ cong (λ cc → canonₛ B₁ cc j) mapcc
          where
            mapcc : mapᶜ (swapᵣ 1 1 ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) cc₀
                    ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB2 (Fin.suc Fin.zero) , K `unit)
            mapcc = cong₂ _,_ refl (cong₂ _,_ refl refl)
        rhsB₁ : leafσ σ B₂ B₁ ((b2 ↑ʳ j) ↑ˡ m)
                ≡ canonₛ B₁ (K `unit , weaken* ⦃ Kᵣ ⦄ sB2 (Fin.suc Fin.zero) , K `unit) j
        rhsB₁ =
            leafσ-B₁ σ B₂ B₁ ((b2 ↑ʳ j) ↑ˡ m) (b2 ↑ʳ j) j
              (Fin.splitAt-↑ˡ (b2 + b1) (b2 ↑ʳ j) m) (Fin.splitAt-↑ʳ b2 b1 j)
    ...   | inj₂ k = lhsB₂ ■ sym rhsB₂
      where
        i≡ : (b1 ↑ʳ k) ↑ˡ m ≡ i
        i≡ = cong (_↑ˡ m) (Fin.splitAt⁻¹-↑ʳ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo
        lhsB₂ : canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 (Fin.suc Fin.zero) , K `unit) k
                  ⋯ assocSwapᵣ sB2 sB1 ⋯ R'
                ≡ canonₛ B₂ (K `unit , 0F , K `unit) k ⋯ weaken* ⦃ Kᵣ ⦄ sB1
        lhsB₂ = canonₛ-B₂-reconcile σ B₁ B₂ k
        rhsB₂ : leafσ σ B₂ B₁ ((k ↑ˡ b1) ↑ˡ m)
                ≡ canonₛ B₂ (K `unit , 0F , K `unit) k ⋯ weaken* ⦃ Kᵣ ⦄ sB1
        rhsB₂ =
            leafσ-A₁ σ B₂ B₁ ((k ↑ˡ b1) ↑ˡ m) (k ↑ˡ b1) k
              (Fin.splitAt-↑ˡ (b2 + b1) (k ↑ˡ b1) m) (Fin.splitAt-↑ˡ b2 k b1)

-- The remaining ν-reordering lemmas reduce — via the flattening Uν-flat above —
-- to the φ-binder BLOCK-TRANSPOSE engine plus a leaf-substitution reconcile:
--
--   Bφ B₁ (Bφ B₂ X) ≋ Bφ B₂ (Bφ B₁ (X ⋯ₚ assocSwapᵣ (syncs B₁) (syncs B₂)))
--
-- proved by induction over the φ-blocks with U.φ-comm′ (each step contributes an
-- assocSwapᵣ 1 1 on the body, accumulated by the renaming laws R2/R2'), followed
-- by U.ν-swap′ / U.ν-comm′ on the two data channels and the canonₛ-naturality
-- reconciliation of the leaf U[ P ] (leafσ …) (via U-⋯ₚ + U-cong + canonₛ-nat).
-- This is exactly the old BlockSwap+BlockPermutation+NuSwap/NuComm engine
-- (~760 ln there); against the simpler new translation the φ-blocks carry no
-- flag cells, so only the binder permutation + leaf reconcile remain.
-- The infrastructure (Uν-flat, leafσ, Bφ, Bφ-cong, UB-flat, canonₛ) is in place.

U-ν-swap : (σ : m →ₛ n) {B₁ B₂ : BindGroup} {P : T.Proc (sum B₁ + sum B₂ + m)} →
           U[ T.ν B₁ B₂ P ] σ U.≋ U[ T.ν B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂)) ] σ
U-ν-swap {m = m} {n = n} σ {B₁} {B₂} {P} =
     ≡→≋ (Uν-flat σ B₁ B₂ P)
  ◅◅ U.ν-cong (Bφ-transpose B₁ B₂ (U[ P ] (leafσ σ B₁ B₂)))
  ◅◅ Eq*.return U.ν-swap′
  ◅◅ U.ν-cong (≡→≋ (Bφ-⋯ B₂ (Bφ B₁ Xs) (swapᵣ 1 1)))
  ◅◅ U.ν-cong (Bφ-cong B₂ (≡→≋ (Bφ-⋯ B₁ Xs (swapᵣ 1 1 ↑* sB₂))))
  ◅◅ U.ν-cong (Bφ-cong B₂ (Bφ-cong B₁ (≡→≋ leafEq)))
  ◅◅ ≡→≋ (sym (Uν-flat σ B₂ B₁ (P T.⋯ₚ swapᵣ (sum B₁) (sum B₂))))
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Xs : U.Proc (sB₁ + (sB₂ + (2 + n)))
    Xs = U[ P ] (leafσ σ B₁ B₂) U.⋯ₚ assocSwapᵣ sB₂ sB₁
    leafEq : (Xs U.⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁))
             ≡ U[ P T.⋯ₚ swapᵣ (sum B₁) (sum B₂) ] (leafσ σ B₂ B₁)
    leafEq =
        cong (U._⋯ₚ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)) (local-U-σ⋯ P)
      ■ local-U-σ⋯ P
      ■ U-cong P subEq
      ■ sym (U-⋯ₚ P)
      where
        subEq : (leafσ σ B₁ B₂ ·ₖ assocSwapᵣ sB₂ sB₁) ·ₖ ((swapᵣ 1 1 ↑* sB₂) ↑* sB₁)
                ≗ swapᵣ (sum B₁) (sum B₂) ·ₖ leafσ σ B₂ B₁
        subEq = subEq-gen σ B₁ B₂

-- a toℕ-fixing renaming stays toℕ-fixing after lifting past k inert binders.
lift-fix-ge : ∀ {a a′} (ρ : a →ᵣ a′) (k T : ℕ) →
              (∀ y → T Nat.≤ Fin.toℕ y → Fin.toℕ (ρ y) ≡ Fin.toℕ y) →
              ∀ (z : 𝔽 (k + a)) → k + T Nat.≤ Fin.toℕ z →
              Fin.toℕ ((ρ ↑* k) z) ≡ Fin.toℕ z
lift-fix-ge ρ k T h z ge =
    toℕ-↑*-ge ρ k z q1
  ■ cong (k +_) (h (Fin.reduce≥ z q1) Tred)
  ■ cong (k +_) (toℕ-reduce≥ z q1)
  ■ Nat.m+[n∸m]≡n q1
  where
    q1 : k Nat.≤ Fin.toℕ z
    q1 = Nat.≤-trans (Nat.m≤m+n k T) ge
    Tred : T Nat.≤ Fin.toℕ (Fin.reduce≥ z q1)
    Tred = subst (T Nat.≤_) (sym (toℕ-reduce≥ z q1))
             (subst (Nat._≤ Fin.toℕ z Nat.∸ k) (Nat.m+n∸m≡n k T) (Nat.∸-monoˡ-≤ k ge))

-- the inner ρb = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 ↑* sB1) fixes toℕ on indices ≥ sB1+(2+2).
ρb-fix-ge : ∀ {n} (sB1 : ℕ) (y : 𝔽 (2 + (sB1 + (2 + n)))) → 2 + (sB1 + 2) Nat.≤ Fin.toℕ y →
            Fin.toℕ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) y) ≡ Fin.toℕ y
ρb-fix-ge {n} sB1 y ge =
    lift-fix-ge (assocSwapᵣ 2 2 {n}) sB1 (2 + 2)
      (λ w q → toℕ-assoc-ge 2 2 w q) (assocSwapᵣ 2 sB1 y) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB1 y) ≡ Fin.toℕ y
    aSwN = toℕ-assoc-ge 2 sB1 y (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 2)) ge)
    geInner : sB1 + (2 + 2) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 y)
    geInner = subst (sB1 + (2 + 2) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ y) reassoc ge)
      where reassoc : 2 + (sB1 + 2) ≡ sB1 + (2 + 2)
            reassoc = solve 1 (λ s → con 2 :+ (s :+ con 2) := s :+ (con 2 :+ con 2)) refl sB1
              where open +-*-Solver

-- toℕ-preservation of the body permutation ρacc on indices at/above its prefix.
ρacc-fix-ge : ∀ {n} (sB1 sB2 : ℕ) (x : 𝔽 (2 + (sB2 + (sB1 + (2 + n))))) →
              2 + (sB2 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
              Fin.toℕ ((assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)) x)
              ≡ Fin.toℕ x
ρacc-fix-ge {n} sB1 sB2 x ge =
    lift-fix-ge (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) sB2 (2 + (sB1 + 2))
      (λ w q → ρb-fix-ge sB1 w q) (assocSwapᵣ 2 sB2 x) geInner
  ■ aSwN
  where
    aSwN : Fin.toℕ (assocSwapᵣ 2 sB2 x) ≡ Fin.toℕ x
    aSwN = toℕ-assoc-ge 2 sB2 x (Nat.≤-trans (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB2 (sB1 + 2))) ge)
    geInner : sB2 + (2 + (sB1 + 2)) Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 x)
    geInner = subst (sB2 + (2 + (sB1 + 2)) Nat.≤_) (sym aSwN) (subst (Nat._≤ Fin.toℕ x) reassoc ge)
      where reassoc : 2 + (sB2 + (sB1 + 2)) ≡ sB2 + (2 + (sB1 + 2))
            reassoc = solve 2 (λ u v → con 2 :+ (u :+ (v :+ con 2))
                               := u :+ (con 2 :+ (v :+ con 2))) refl sB2 sB1
              where open +-*-Solver

-- the inner L₃ = (assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2 fixes toℕ ≥ sA2+(sA1+2).
ωL3-fix-ge : ∀ {p} (sA1 sA2 : ℕ) (y : 𝔽 (sA2 + (sA1 + (2 + p)))) → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ y →
             Fin.toℕ (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2 {sA1 + p}) y) ≡ Fin.toℕ y
ωL3-fix-ge {p} sA1 sA2 y ge =
    toℕ-assoc-ge sA2 2 ((assocSwapᵣ sA1 2 {p} ↑* sA2) y)
      (subst (sA2 + 2 Nat.≤_) (sym m1N) (Nat.≤-trans le1 ge))
  ■ m1N
  where
    m1N : Fin.toℕ ((assocSwapᵣ sA1 2 {p} ↑* sA2) y) ≡ Fin.toℕ y
    m1N = toℕ-assoc↑*-fix-ge sA2 sA1 2 y ge
    le1 : sA2 + 2 Nat.≤ sA2 + (sA1 + 2)
    le1 = Nat.+-monoʳ-≤ sA2 (Nat.m≤n+m 2 sA1)

-- the body permutation ρω fixes toℕ on indices ≥ sA2+(sA1+(sB1+2)).
ρω-fix-ge : ∀ {p} (sA1 sA2 sB1 : ℕ) (x : 𝔽 (sA2 + (sA1 + (sB1 + (2 + p))))) →
            sA2 + (sA1 + (sB1 + 2)) Nat.≤ Fin.toℕ x →
            Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                      ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                          (((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x)
            ≡ Fin.toℕ x
ρω-fix-ge {p} sA1 sA2 sB1 x ge = l3N ■ z2N ■ z1N
  where
    z1 = (assocSwapᵣ sA1 sB1 ↑* sA2) x
    z1N : Fin.toℕ z1 ≡ Fin.toℕ x
    z1N = toℕ-assoc↑*-fix-ge sA2 sA1 sB1 x
            (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 2))) ge)
    z2 = assocSwapᵣ sA2 sB1 z1
    z2N : Fin.toℕ z2 ≡ Fin.toℕ z1
    z2N = toℕ-assoc-ge sA2 sB1 z1
            (subst (sA2 + sB1 Nat.≤_) (sym z1N)
              (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB1 2) (Nat.m≤n+m (sB1 + 2) sA1))) ge))
    l3N : Fin.toℕ ((((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2) ≡ Fin.toℕ z2
    l3N = lift-fix-ge ((assocSwapᵣ sA1 2 {p} ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 (sA2 + (sA1 + 2))
            (λ w q → ωL3-fix-ge sA1 sA2 w q) z2 geL3
      where
        geL3 : sB1 + (sA2 + (sA1 + 2)) Nat.≤ Fin.toℕ z2
        geL3 = subst (sB1 + (sA2 + (sA1 + 2)) Nat.≤_) (sym (z2N ■ z1N))
                 (subst (Nat._≤ Fin.toℕ x) reassoc ge)
          where reassoc : sA2 + (sA1 + (sB1 + 2)) ≡ sB1 + (sA2 + (sA1 + 2))
                reassoc = solve 3 (λ u v w → u :+ (v :+ (w :+ con 2)) := w :+ (u :+ (v :+ con 2)))
                            refl sA2 sA1 sB1
                  where open +-*-Solver

-- top-level rebuild of the composite body permutation Φ of subEqComm-gen,
-- parameterised purely by the four syncs counts.  (Definitionally equal to the
-- in-where Φ once the counts are instantiated.)
module _ (sA1 sA2 sB1 sB2 : ℕ) {n : ℕ} where
  Φᵗ : (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
       →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
  Φᵗ = (((((ρaccᵗ ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ωᵗ)
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2

  -- A-region: an index strictly below the A sync-prefix (sA2+sA1) is shifted
  -- right by the whole B-prefix (sB2+sB1+2).  (The two A data channels at
  -- [sA2+sA1, sA2+sA1+2) do NOT follow this flat shift; they are reconciled
  -- separately at the leaf level, so they are deliberately excluded here.)
  Φᵗ-A : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
         → Fin.toℕ x Nat.< sA2 + sA1
         → Fin.toℕ (Φᵗ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
  Φᵗ-A x lt = bridge ■ Φ-A-body
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      -- the two A data channels (sA2+sA1 ≤ toℕ x) are excluded by Φᵗ-A's
      -- hypothesis lt : toℕ x < sA2+sA1, so this case is vacuous.
      A3 : sA2 + sA1 Nat.≤ Fin.toℕ x → Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      A3 ge = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans lt ge))
      A23 : sA2 Nat.≤ Fin.toℕ x → Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      A23 a2le with Nat.<-cmp (Fin.toℕ x) (sA2 + sA1)
      ... | tri< xltA21 _ _ = A2
        where
          dx = Fin.toℕ x Nat.∸ sA2
          xd : sA2 + dx ≡ Fin.toℕ x
          xd = Nat.m+[n∸m]≡n a2le
          dltA1 : dx Nat.< sA1
          dltA1 = Nat.+-cancelˡ-< sA2 dx sA1 (subst (Nat._< sA2 + sA1) (sym xd) xltA21)
          xr = Fin.reduce≥ x a2le
          xrd : Fin.toℕ xr ≡ dx
          xrd = toℕ-reduce≥ x a2le
          -- x1 : F1 fixes (inner lift sA1 lt)
          x1N : Fin.toℕ x1 ≡ Fin.toℕ x
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-lt ρaccᵗ sA1 xr (subst (Nat._< sA1) (sym xrd) dltA1) ■ xrd)
              ■ xd
          x2N : Fin.toℕ x2 ≡ sA2 + (sB2 + dx)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 sB2 {sB1 + (2 + (2 + n))} (Fin.reduce≥ x1 a2lex1) dltA1r ■ cong (sB2 +_) reddx)
            where a2lex1 : sA2 Nat.≤ Fin.toℕ x1
                  a2lex1 = subst (sA2 Nat.≤_) (sym x1N) a2le
                  reddx : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ dx
                  reddx = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ cong (Nat._∸ sA2) (sym xd) ■ Nat.m+n∸m≡n sA2 dx
                  dltA1r : Fin.toℕ (Fin.reduce≥ x1 a2lex1) Nat.< sA1
                  dltA1r = subst (Nat._< sA1) (sym reddx) dltA1
          x3N : Fin.toℕ x3 ≡ sA2 + (sB2 + dx)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sB2 dx))) ■ x2N
          q : sB2 Nat.≤ Fin.toℕ x3
          q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤m+n sB2 dx) (Nat.m≤n+m (sB2 + dx) sA2))
          r = Fin.reduce≥ x3 q
          rN : Fin.toℕ r ≡ sA2 + dx
          rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sB2 + dx)) Nat.∸ sB2 ≡ sA2 + dx
                  reassoc = cong (Nat._∸ sB2) (solve 3 (λ a b e → a :+ (b :+ e) := b :+ (a :+ e)) refl sA2 sB2 dx) ■ Nat.m+n∸m≡n sB2 (sA2 + dx)
          rge : sA2 Nat.≤ Fin.toℕ r
          rge = subst (sA2 Nat.≤_) (sym rN) (Nat.m≤m+n sA2 dx)
          rr = Fin.reduce≥ r rge
          rrN : Fin.toℕ rr ≡ dx
          rrN = toℕ-reduce≥ r rge ■ cong (Nat._∸ sA2) rN ■ Nat.m+n∸m≡n sA2 dx
          rrltA1 : Fin.toℕ rr Nat.< sA1
          rrltA1 = subst (Nat._< sA1) (sym rrN) dltA1
          -- Omega_inner r : g1 ge(aS lt), g2 ge, g3 ge(L3: ge then aS ge)
          g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
          g1N : Fin.toℕ g1 ≡ sA2 + (sB1 + dx)
          g1N = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 r rge
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 sB1 rr rrltA1 ■ cong (sB1 +_) rrN)
          g2 = assocSwapᵣ sA2 sB1 g1
          g2N : Fin.toℕ g2 ≡ sA2 + (sB1 + dx)
          g2N = toℕ-assoc-ge sA2 sB1 g1 (subst (sA2 + sB1 Nat.≤_) (sym g1N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sB1 dx))) ■ g1N
          g3q : sB1 Nat.≤ Fin.toℕ g2
          g3q = subst (sB1 Nat.≤_) (sym g2N) (Nat.≤-trans (Nat.m≤m+n sB1 dx) (Nat.m≤n+m (sB1 + dx) sA2))
          g3r = Fin.reduce≥ g2 g3q
          g3rN : Fin.toℕ g3r ≡ sA2 + dx
          g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sB1 + dx)) Nat.∸ sB1 ≡ sA2 + dx
                  reassoc = cong (Nat._∸ sB1) (solve 3 (λ a b e → a :+ (b :+ e) := b :+ (a :+ e)) refl sA2 sB1 dx) ■ Nat.m+n∸m≡n sB1 (sA2 + dx)
          g3rge : sA2 Nat.≤ Fin.toℕ g3r
          g3rge = subst (sA2 Nat.≤_) (sym g3rN) (Nat.m≤m+n sA2 dx)
          g3rr = Fin.reduce≥ g3r g3rge
          g3rrN : Fin.toℕ g3rr ≡ dx
          g3rrN = toℕ-reduce≥ g3r g3rge ■ cong (Nat._∸ sA2) g3rN ■ Nat.m+n∸m≡n sA2 dx
          g3rrltA1 : Fin.toℕ g3rr Nat.< sA1
          g3rrltA1 = subst (Nat._< sA1) (sym g3rrN) dltA1
          -- L3 g3r = aS(sA2,2)((aS(sA1,2)↑*sA2) g3r) ; both ge -> sA2+(2+dx)
          l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
          l1N : Fin.toℕ l1 ≡ sA2 + (2 + dx)
          l1N = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 g3r g3rge
              ■ cong (sA2 +_) (toℕ-assoc-lt sA1 2 g3rr g3rrltA1 ■ cong (2 +_) g3rrN)
          l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ sA2 + (2 + dx)
          l2N = toℕ-assoc-ge sA2 2 l1 (subst (sA2 + 2 Nat.≤_) (sym l1N) (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n 2 dx))) ■ l1N
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                 ≡ sB1 + (sA2 + (2 + dx))
          omN = toℕ-↑*-ge _ sB1 g2 g3q ■ cong (sB1 +_) l2N
          A2 : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          A2 = toℕ-↑*-ge _ sB2 x3 q
             ■ cong (sB2 +_) omN
             ■ final
            where open +-*-Solver
                  final : sB2 + (sB1 + (sA2 + (2 + dx))) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
                  final = (solve 4 (λ b2 b1 a2 e → b2 :+ (b1 :+ (a2 :+ (con 2 :+ e))) := (b2 :+ (b1 :+ con 2)) :+ (a2 :+ e)) refl sB2 sB1 sA2 dx) ■ cong ((sB2 + (sB1 + 2)) +_) xd
      ... | tri≈ _ xeqA21 _ = A3 (Nat.≤-reflexive (sym xeqA21))
      ... | tri> _ _ xgtA21 = A3 (Nat.<⇒≤ xgtA21)
      Φ-A-body : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      Φ-A-body with Nat.<-cmp (Fin.toℕ x) sA2
      ... | tri< xltA2 _ _ = A1
        where
          -- x < sA2
          x1N : Fin.toℕ x1 ≡ Fin.toℕ x
          x1N = toℕ-↑*-lt (ρaccᵗ ↑* sA1) sA2 x xltA2
          x2N : Fin.toℕ x2 ≡ Fin.toℕ x
          x2N = toℕ-↑*-lt (assocSwapᵣ sA1 sB2) sA2 x1 (subst (Nat._< sA2) (sym x1N) xltA2) ■ x1N
          x3N : Fin.toℕ x3 ≡ sB2 + Fin.toℕ x
          x3N = toℕ-assoc-lt sA2 sB2 x2 (subst (Nat._< sA2) (sym x2N) xltA2) ■ cong (sB2 +_) x2N
          A1 : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          A1 = toℕ-↑*-ge _ sB2 x3 q
             ■ cong (sB2 +_) omN
             ■ sym (Nat.+-assoc sB2 (sB1 + 2) (Fin.toℕ x))
            where
              q : sB2 Nat.≤ Fin.toℕ x3
              q = subst (sB2 Nat.≤_) (sym x3N) (Nat.m≤m+n sB2 (Fin.toℕ x))
              r = Fin.reduce≥ x3 q
              rN : Fin.toℕ r ≡ Fin.toℕ x
              rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ Nat.m+n∸m≡n sB2 (Fin.toℕ x)
              rltA2 : Fin.toℕ r Nat.< sA2
              rltA2 = subst (Nat._< sA2) (sym rN) xltA2
              -- Omega_inner r : g1 lt, g2 lt, g3 ge(reduce L3 lt then aS lt)
              g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
              g1N : Fin.toℕ g1 ≡ Fin.toℕ x
              g1N = toℕ-↑*-lt (assocSwapᵣ sA1 sB1) sA2 r rltA2 ■ rN
              g2 = assocSwapᵣ sA2 sB1 g1
              g2N : Fin.toℕ g2 ≡ sB1 + Fin.toℕ x
              g2N = toℕ-assoc-lt sA2 sB1 g1 (subst (Nat._< sA2) (sym g1N) xltA2) ■ cong (sB1 +_) g1N
              g3q : sB1 Nat.≤ Fin.toℕ g2
              g3q = subst (sB1 Nat.≤_) (sym g2N) (Nat.m≤m+n sB1 (Fin.toℕ x))
              g3r = Fin.reduce≥ g2 g3q
              g3rN : Fin.toℕ g3r ≡ Fin.toℕ x
              g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ Nat.m+n∸m≡n sB1 (Fin.toℕ x)
              g3rltA2 : Fin.toℕ g3r Nat.< sA2
              g3rltA2 = subst (Nat._< sA2) (sym g3rN) xltA2
              l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
              l1N : Fin.toℕ l1 ≡ Fin.toℕ x
              l1N = toℕ-↑*-lt (assocSwapᵣ sA1 2) sA2 g3r g3rltA2 ■ g3rN
              l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ 2 + Fin.toℕ x
              l2N = toℕ-assoc-lt sA2 2 l1 (subst (Nat._< sA2) (sym l1N) xltA2) ■ cong (2 +_) l1N
              omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                              ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                                  (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                     ≡ (sB1 + 2) + Fin.toℕ x
              omN = toℕ-↑*-ge _ sB1 g2 g3q
                  ■ cong (sB1 +_) l2N
                  ■ sym (Nat.+-assoc sB1 2 (Fin.toℕ x))
      ... | tri≈ _ xeqA2 _ = A23 (Nat.≤-reflexive (sym xeqA2))
      ... | tri> _ _ xgtA2 = A23 (Nat.<⇒≤ xgtA2)

  -- A-data region: the two A data channels at [sA2+sA1, sA2+sA1+2) follow the
  -- SAME flat shift as the A sync prefix (right by sB2+sB1+2).
  Φᵗ-Adata : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
             → sA2 + sA1 Nat.≤ Fin.toℕ x
             → Fin.toℕ x Nat.< sA2 + sA1 + 2
             → Fin.toℕ (Φᵗ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
  Φᵗ-Adata x age alt = bridge ■ body
    where
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      de = Fin.toℕ x Nat.∸ (sA2 + sA1)
      a2le : sA2 Nat.≤ Fin.toℕ x
      a2le = Nat.≤-trans (Nat.m≤m+n sA2 sA1) age
      dx = sA1 + de
      xd : Fin.toℕ x ≡ sA2 + dx
      xd = sym (Nat.m+[n∸m]≡n a2le) ■ cong (sA2 +_) red-dx
        where red-dx : Fin.toℕ x Nat.∸ sA2 ≡ sA1 + de
              red-dx = cong (Nat._∸ sA2) (sym (Nat.m+[n∸m]≡n age))
                     ■ cong (Nat._∸ sA2) (Nat.+-assoc sA2 sA1 de) ■ Nat.m+n∸m≡n sA2 (sA1 + de)
      elt2 : de Nat.< 2
      elt2 = Nat.+-cancelˡ-< (sA2 + sA1) de 2
               (subst (Nat._< sA2 + sA1 + 2) (sym (Nat.m+[n∸m]≡n age)) alt)
      dxge : sA1 Nat.≤ dx
      dxge = Nat.m≤m+n sA1 de
      dxlt2 : dx Nat.< sA1 + 2
      dxlt2 = Nat.+-monoʳ-< sA1 elt2
      -- F1: ρaccᵗ fires on the data channel index w (toℕ w < 2).
      ρae : ∀ (w : 𝔽 (2 + (sB2 + (sB1 + (2 + n))))) → Fin.toℕ w Nat.< 2
            → Fin.toℕ (ρaccᵗ w) ≡ sB2 + (sB1 + (2 + Fin.toℕ w))
      ρae w wlt =
          toℕ-↑*-ge (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) sB2 (assocSwapᵣ 2 sB2 w) sb2le
        ■ cong (sB2 +_) inner
        where
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 w) ≡ sB2 + Fin.toℕ w
          asN = toℕ-assoc-lt 2 sB2 w wlt
          sb2le : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 w)
          sb2le = subst (sB2 Nat.≤_) (sym asN) (Nat.m≤m+n sB2 (Fin.toℕ w))
          r0 = Fin.reduce≥ (assocSwapᵣ 2 sB2 w) sb2le
          r0N : Fin.toℕ r0 ≡ Fin.toℕ w
          r0N = toℕ-reduce≥ (assocSwapᵣ 2 sB2 w) sb2le ■ cong (Nat._∸ sB2) asN ■ Nat.m+n∸m≡n sB2 (Fin.toℕ w)
          r0lt : Fin.toℕ r0 Nat.< 2
          r0lt = subst (Nat._< 2) (sym r0N) wlt
          inner : Fin.toℕ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) r0) ≡ sB1 + (2 + Fin.toℕ w)
          inner = toℕ-↑*-ge (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 r0) sb1le
                ■ cong (sB1 +_) inner2
            where
              as2N : Fin.toℕ (assocSwapᵣ 2 sB1 r0) ≡ sB1 + Fin.toℕ r0
              as2N = toℕ-assoc-lt 2 sB1 r0 r0lt
              sb1le : sB1 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 r0)
              sb1le = subst (sB1 Nat.≤_) (sym as2N) (Nat.m≤m+n sB1 (Fin.toℕ r0))
              r1 = Fin.reduce≥ (assocSwapᵣ 2 sB1 r0) sb1le
              r1N : Fin.toℕ r1 ≡ Fin.toℕ w
              r1N = toℕ-reduce≥ (assocSwapᵣ 2 sB1 r0) sb1le ■ cong (Nat._∸ sB1) as2N ■ Nat.m+n∸m≡n sB1 (Fin.toℕ r0) ■ r0N
              r1lt : Fin.toℕ r1 Nat.< 2
              r1lt = subst (Nat._< 2) (sym r1N) wlt
              inner2 : Fin.toℕ (assocSwapᵣ 2 2 {n} r1) ≡ 2 + Fin.toℕ w
              inner2 = toℕ-assoc-lt 2 2 r1 r1lt ■ cong (2 +_) r1N
      -- F1: x1
      x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
          ■ cong (sA2 +_) inner1
        where
          xr = Fin.reduce≥ x a2le
          xrN : Fin.toℕ xr ≡ dx
          xrN = toℕ-reduce≥ x a2le ■ cong (Nat._∸ sA2) xd ■ Nat.m+n∸m≡n sA2 dx
          xrge : sA1 Nat.≤ Fin.toℕ xr
          xrge = subst (sA1 Nat.≤_) (sym xrN) dxge
          inner1 : Fin.toℕ ((ρaccᵗ ↑* sA1) xr) ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          inner1 = toℕ-↑*-ge ρaccᵗ sA1 xr xrge ■ cong (sA1 +_) (ρae r2 r2lt ■ cong (λ z → sB2 + (sB1 + (2 + z))) r2N)
            where
              r2 = Fin.reduce≥ xr xrge
              r2N : Fin.toℕ r2 ≡ de
              r2N = toℕ-reduce≥ xr xrge ■ cong (Nat._∸ sA1) xrN ■ Nat.m+n∸m≡n sA1 de
              r2lt : Fin.toℕ r2 Nat.< 2
              r2lt = subst (Nat._< 2) (sym r2N) elt2
      x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1 ■ cong (sA2 +_) inner2
        where
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 _)
          r1 = Fin.reduce≥ x1 a2lex1
          r1N : Fin.toℕ r1 ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          r1N = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + (sB2 + (sB1 + (2 + de))))
          r1ge : sA1 + sB2 Nat.≤ Fin.toℕ r1
          r1ge = subst (sA1 + sB2 Nat.≤_) (sym r1N) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB2 (sB1 + (2 + de))))
          inner2 : Fin.toℕ (assocSwapᵣ sA1 sB2 r1) ≡ sA1 + (sB2 + (sB1 + (2 + de)))
          inner2 = toℕ-assoc-ge sA1 sB2 r1 r1ge ■ r1N
      x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))
      x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
              (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + (2 + de))) (Nat.m≤n+m _ sA1)))) ■ x2N
      body : Fin.toℕ (Ωᵗ x3) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
      body = toℕ-↑*-ge _ sB2 x3 q ■ cong (sB2 +_) omN ■ final
        where
          q : sB2 Nat.≤ Fin.toℕ x3
          q = subst (sB2 Nat.≤_) (sym x3N)
                (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + (2 + de)))
                  (Nat.≤-trans (Nat.m≤n+m _ sA1) (Nat.m≤n+m _ sA2)))
          r = Fin.reduce≥ x3 q
          rN : Fin.toℕ r ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          rN = toℕ-reduce≥ x3 q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + (sB2 + (sB1 + (2 + de))))) Nat.∸ sB2 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
                  reassoc = cong (Nat._∸ sB2) (solve 5 (λ a2 a1 b2 b1 t →
                                a2 :+ (a1 :+ (b2 :+ (b1 :+ (con 2 :+ t))))
                                := b2 :+ (a2 :+ (a1 :+ (b1 :+ (con 2 :+ t))))) refl sA2 sA1 sB2 sB1 de)
                          ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + (sB1 + (2 + de))))
          rge : sA2 Nat.≤ Fin.toℕ r
          rge = subst (sA2 Nat.≤_) (sym rN) (Nat.m≤m+n sA2 _)
          g1 = (assocSwapᵣ sA1 sB1 ↑* sA2) r
          g1N : Fin.toℕ g1 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          g1N = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 r rge ■ cong (sA2 +_) inner-g1
            where
              rr = Fin.reduce≥ r rge
              rrN : Fin.toℕ rr ≡ sA1 + (sB1 + (2 + de))
              rrN = toℕ-reduce≥ r rge ■ cong (Nat._∸ sA2) rN ■ Nat.m+n∸m≡n sA2 (sA1 + (sB1 + (2 + de)))
              rrge : sA1 + sB1 Nat.≤ Fin.toℕ rr
              rrge = subst (sA1 + sB1 Nat.≤_) (sym rrN) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 (2 + de)))
              inner-g1 : Fin.toℕ (assocSwapᵣ sA1 sB1 rr) ≡ sA1 + (sB1 + (2 + de))
              inner-g1 = toℕ-assoc-ge sA1 sB1 rr rrge ■ rrN
          g2 = assocSwapᵣ sA2 sB1 g1
          g2N : Fin.toℕ g2 ≡ sA2 + (sA1 + (sB1 + (2 + de)))
          g2N = toℕ-assoc-ge sA2 sB1 g1 (subst (sA2 + sB1 Nat.≤_) (sym g1N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n sB1 (2 + de)) (Nat.m≤n+m _ sA1)))) ■ g1N
          g3q : sB1 Nat.≤ Fin.toℕ g2
          g3q = subst (sB1 Nat.≤_) (sym g2N)
                  (Nat.≤-trans (Nat.m≤m+n sB1 (2 + de))
                    (Nat.≤-trans (Nat.m≤n+m _ sA1) (Nat.m≤n+m _ sA2)))
          g3r = Fin.reduce≥ g2 g3q
          g3rN : Fin.toℕ g3r ≡ sA2 + (sA1 + (2 + de))
          g3rN = toℕ-reduce≥ g2 g3q ■ cong (Nat._∸ sB1) g2N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + (sB1 + (2 + de)))) Nat.∸ sB1 ≡ sA2 + (sA1 + (2 + de))
                  reassoc = cong (Nat._∸ sB1) (solve 4 (λ a2 a1 b1 t →
                                a2 :+ (a1 :+ (b1 :+ (con 2 :+ t)))
                                := b1 :+ (a2 :+ (a1 :+ (con 2 :+ t)))) refl sA2 sA1 sB1 de)
                          ■ Nat.m+n∸m≡n sB1 (sA2 + (sA1 + (2 + de)))
          g3rge : sA2 Nat.≤ Fin.toℕ g3r
          g3rge = subst (sA2 Nat.≤_) (sym g3rN) (Nat.m≤m+n sA2 _)
          l1 = (assocSwapᵣ sA1 2 ↑* sA2) g3r
          l1N : Fin.toℕ l1 ≡ sA2 + (sA1 + (2 + de))
          l1N = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 g3r g3rge ■ cong (sA2 +_) inner-l1
            where
              gg = Fin.reduce≥ g3r g3rge
              ggN : Fin.toℕ gg ≡ sA1 + (2 + de)
              ggN = toℕ-reduce≥ g3r g3rge ■ cong (Nat._∸ sA2) g3rN ■ Nat.m+n∸m≡n sA2 (sA1 + (2 + de))
              ggge : sA1 + 2 Nat.≤ Fin.toℕ gg
              ggge = subst (sA1 + 2 Nat.≤_) (sym ggN) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n 2 de))
              inner-l1 : Fin.toℕ (assocSwapᵣ sA1 2 gg) ≡ sA1 + (2 + de)
              inner-l1 = toℕ-assoc-ge sA1 2 gg ggge ■ ggN
          l2N : Fin.toℕ (assocSwapᵣ sA2 2 l1) ≡ sA2 + (sA1 + (2 + de))
          l2N = toℕ-assoc-ge sA2 2 l1 (subst (sA2 + 2 Nat.≤_) (sym l1N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤m+n 2 de) (Nat.m≤n+m _ sA1)))) ■ l1N
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) r)
                 ≡ sB1 + (sA2 + (sA1 + (2 + de)))
          omN = toℕ-↑*-ge _ sB1 g2 g3q ■ cong (sB1 +_) l2N
          final : sB2 + (sB1 + (sA2 + (sA1 + (2 + de)))) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
          final = solveF ■ cong ((sB2 + (sB1 + 2)) +_) (sym xd)
            where open +-*-Solver
                  solveF : sB2 + (sB1 + (sA2 + (sA1 + (2 + de)))) ≡ (sB2 + (sB1 + 2)) + (sA2 + (sA1 + de))
                  solveF = solve 5 (λ b2 b1 a2 a1 t →
                      b2 :+ (b1 :+ (a2 :+ (a1 :+ (con 2 :+ t))))
                      := (b2 :+ (b1 :+ con 2)) :+ (a2 :+ (a1 :+ t))) refl sB2 sB1 sA2 sA1 de

  -- B-region: an index in [sA2+sA1+2, sA2+sA1+2 + (sB2+sB1+2)) is shifted left
  -- by the whole A-prefix.
  Φᵗ-B : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
         → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ x
         → Fin.toℕ x Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
         → Fin.toℕ (Φᵗ x) ≡ Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
  Φᵗ-B x ge lt = bridge ■ Φ-B-body
    where
      ra-inner = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)
      ρaccᵗ = assocSwapᵣ 2 sB2 ·ₖ (ra-inner ↑* sB2)
      Ωᵗ = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
      x1 = ((ρaccᵗ ↑* sA1) ↑* sA2) x
      x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
      x3 = assocSwapᵣ sA2 sB2 x2
      bridge : Fin.toℕ (Φᵗ x) ≡ Fin.toℕ (Ωᵗ x3)
      bridge = refl
      f = Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
      a2le : sA2 Nat.≤ Fin.toℕ x
      a2le = Nat.≤-trans (Nat.m≤m+n sA2 (sA1 + 2)) ge
      -- toℕ x = sA2 + (sA1 + (2 + f))
      xeq : Fin.toℕ x ≡ sA2 + (sA1 + (2 + f))
      xeq = sym (Nat.m+[n∸m]≡n ge) ■ Nat.+-assoc sA2 (sA1 + 2) f ■ cong (sA2 +_) (Nat.+-assoc sA1 2 f)
      fltBpre : f Nat.< sB2 + (sB1 + 2)
      fltBpre = Nat.+-cancelˡ-< sA2 f (sB2 + (sB1 + 2))
                  (Nat.+-cancelˡ-< sA1 (sA2 + f) _
                    (Nat.+-cancelˡ-< 2 (sA1 + (sA2 + f)) _ goal2))
        where -- 2 + (sA1 + (sA2 + f)) < 2 + (sA1 + (sA2 + (sB2+sB1+2)))  (= toℕx-region reassociated)
              goal2 : 2 + (sA1 + (sA2 + f)) Nat.< 2 + (sA1 + (sA2 + (sB2 + (sB1 + 2))))
              goal2 = subst₂ Nat._<_ lhseq rhseq (subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) xeq lt)
                where lhseq : sA2 + (sA1 + (2 + f)) ≡ 2 + (sA1 + (sA2 + f))
                      lhseq = solve 3 (λ a2 a1 t → a2 :+ (a1 :+ (con 2 :+ t)) := con 2 :+ (a1 :+ (a2 :+ t))) refl sA2 sA1 f
                        where open +-*-Solver
                      rhseq : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) ≡ 2 + (sA1 + (sA2 + (sB2 + (sB1 + 2))))
                      rhseq = solve 4 (λ a2 a1 b2 b1 → a2 :+ (a1 :+ (con 2 :+ (b2 :+ (b1 :+ con 2)))) := con 2 :+ (a1 :+ (a2 :+ (b2 :+ (b1 :+ con 2))))) refl sA2 sA1 sB2 sB1
                        where open +-*-Solver
      -- common reduction of F1 down to the "2"-block: xr = reduce x past sA2 then sA1
      xrA = Fin.reduce≥ x a2le
      xrAN : Fin.toℕ xrA ≡ sA1 + (2 + f)
      xrAN = toℕ-reduce≥ x a2le ■ cong (Nat._∸ sA2) xeq ■ Nat.m+n∸m≡n sA2 (sA1 + (2 + f))
      xrAge : sA1 Nat.≤ Fin.toℕ xrA
      xrAge = subst (sA1 Nat.≤_) (sym xrAN) (Nat.m≤m+n sA1 (2 + f))
      xrB = Fin.reduce≥ xrA xrAge
      xrBN : Fin.toℕ xrB ≡ 2 + f
      xrBN = toℕ-reduce≥ xrA xrAge ■ cong (Nat._∸ sA1) xrAN ■ Nat.m+n∸m≡n sA1 (2 + f)
      B1 : f Nat.< sB2 → Fin.toℕ (Ωᵗ x3) ≡ f
      B1 flt2 = toℕ-↑*-lt _ sB2 x3 (subst (Nat._< sB2) (sym x3N) flt2) ■ x3N
        where
          -- ρaccᵗ on xrB (toℕ = 2+f) with f<sB2: aS(2,sB2) mid -> f ; lift sB2 lt -> f
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-lt _ sB2 (assocSwapᵣ 2 sB2 xrB) red
             ■ asN
            where asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ f
                  asN = toℕ-assoc-mid 2 sB2 xrB
                          (subst (2 Nat.≤_) (sym xrBN) (Nat.m≤m+n 2 f))
                          (subst (Nat._< 2 + sB2) (sym xrBN) (Nat.+-monoʳ-< 2 flt2))
                      ■ cong (Nat._∸ 2) xrBN ■ Nat.m+n∸m≡n 2 f
                  red : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) Nat.< sB2
                  red = subst (Nat._< sB2) (sym asN) flt2
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          -- x2 : F2 aS(sA1,sB2) on (sA1+f) mid -> f ; toℕ x2 = sA2 + f
          x2N : Fin.toℕ x2 ≡ sA2 + f
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-mid sA1 sB2 (Fin.reduce≥ x1 a2lex1) midlo midhi ■ cong (Nat._∸ sA1) redf ■ Nat.m+n∸m≡n sA1 f)
            where a2lex1 : sA2 Nat.≤ Fin.toℕ x1
                  a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
                  redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
                  redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
                  midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ x1 a2lex1)
                  midlo = subst (sA1 Nat.≤_) (sym redf) (Nat.m≤m+n sA1 f)
                  midhi : Fin.toℕ (Fin.reduce≥ x1 a2lex1) Nat.< sA1 + sB2
                  midhi = subst (Nat._< sA1 + sB2) (sym redf) (Nat.+-monoʳ-< sA1 flt2)
          x3N : Fin.toℕ x3 ≡ f
          x3N = toℕ-assoc-mid sA2 sB2 x2 (subst (sA2 Nat.≤_) (sym x2N) (Nat.m≤m+n sA2 f))
                  (subst (Nat._< sA2 + sB2) (sym x2N) (Nat.+-monoʳ-< sA2 flt2))
              ■ cong (Nat._∸ sA2) x2N ■ Nat.m+n∸m≡n sA2 f
      B2 : sB2 Nat.≤ f → f Nat.< sB2 + sB1 → Fin.toℕ (Ωᵗ x3) ≡ f
      B2 ge2 flt21 = toℕ-↑*-ge _ sB2 x3 x3q ■ cong (sB2 +_) omN ■ Nat.m+[n∸m]≡n ge2
        where
          f1 = f Nat.∸ sB2
          f1eq : sB2 + f1 ≡ f
          f1eq = Nat.m+[n∸m]≡n ge2
          f1ltB1 : f1 Nat.< sB1
          f1ltB1 = Nat.+-cancelˡ-< sB2 f1 sB1 (subst (Nat._< sB2 + sB1) (sym f1eq) flt21)
          -- ρaccᵗ on xrB (=2+f) ; sB2≤f<sB2+sB1 -> f
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ 2 + f
          asN = toℕ-assoc-ge 2 sB2 xrB (subst (2 + sB2 Nat.≤_) (sym xrBN) (Nat.+-monoʳ-≤ 2 ge2)) ■ xrBN
          asge : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 xrB)
          asge = subst (sB2 Nat.≤_) (sym asN) (Nat.≤-trans (Nat.m≤n+m sB2 2) (Nat.+-monoʳ-≤ 2 ge2))
          asr = Fin.reduce≥ (assocSwapᵣ 2 sB2 xrB) asge
          asrN : Fin.toℕ asr ≡ 2 + f1
          asrN = toℕ-reduce≥ (assocSwapᵣ 2 sB2 xrB) asge ■ cong (Nat._∸ sB2) asN ■ reassoc
            where reassoc : (2 + f) Nat.∸ sB2 ≡ 2 + f1
                  reassoc = cong (Nat._∸ sB2) (cong (2 +_) (sym f1eq) ■ sym (Nat.+-assoc 2 sB2 f1) ■ cong (Nat._+ f1) (Nat.+-comm 2 sB2) ■ Nat.+-assoc sB2 2 f1) ■ Nat.m+n∸m≡n sB2 (2 + f1)
          -- ra_inner on (2+f1) = aS(2,sB1)·ₖ(aS(2,2)↑*sB1) ; aS(2,sB1) mid -> f1 ; lift lt -> f1
          rai-asN : Fin.toℕ (assocSwapᵣ 2 sB1 asr) ≡ f1
          rai-asN = toℕ-assoc-mid 2 sB1 asr (subst (2 Nat.≤_) (sym asrN) (Nat.m≤m+n 2 f1))
                      (subst (Nat._< 2 + sB1) (sym asrN) (Nat.+-monoʳ-< 2 f1ltB1))
                  ■ cong (Nat._∸ 2) asrN ■ Nat.m+n∸m≡n 2 f1
          raiN : Fin.toℕ (ra-inner asr) ≡ f1
          raiN = toℕ-↑*-lt (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 asr) (subst (Nat._< sB1) (sym rai-asN) f1ltB1) ■ rai-asN
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-ge ra-inner sB2 (assocSwapᵣ 2 sB2 xrB) asge ■ cong (sB2 +_) raiN ■ f1eq
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          -- F2 aS(sA1,sB2) on (sA1+f) ge (f≥sB2) -> unchanged ; x2 = sA2+(sA1+f)
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
          redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
          redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
          x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + f)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB2 (Fin.reduce≥ x1 a2lex1)
                  (subst (sA1 + sB2 Nat.≤_) (sym redf) (Nat.+-monoʳ-≤ sA1 ge2)) ■ redf)
          x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + f)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB2 sA1) (Nat.+-monoʳ-≤ sA1 ge2)))) ■ x2N
          x3q : sB2 Nat.≤ Fin.toℕ x3
          x3q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤n+m sB2 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) ge2) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 f))))
          x3r = Fin.reduce≥ x3 x3q
          x3rN : Fin.toℕ x3r ≡ sA2 + (sA1 + f1)
          x3rN = toℕ-reduce≥ x3 x3q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + f)) Nat.∸ sB2 ≡ sA2 + (sA1 + f1)
                  reassoc = cong (Nat._∸ sB2) (cong (λ z → sA2 + (sA1 + z)) (sym f1eq) ■ solve 4 (λ a2 a1 b2 t → a2 :+ (a1 :+ (b2 :+ t)) := b2 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB2 f1) ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + f1))
          -- Omega_inner x3r : g1 aS(sA1,sB1) mid -> f1 ; g2 aS(sA2,sB1) mid -> f1 ; g3 lift lt
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x3r)
                 ≡ f1
          omN = z3 ■ z2
            where
              z1f = (assocSwapᵣ sA1 sB1 ↑* sA2) x3r
              z1 : Fin.toℕ z1f ≡ sA2 + f1
              z1 = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 x3r x3rge
                 ■ cong (sA2 +_) (toℕ-assoc-mid sA1 sB1 (Fin.reduce≥ x3r x3rge) midlo midhi ■ cong (Nat._∸ sA1) redx3 ■ Nat.m+n∸m≡n sA1 f1)
                where x3rge : sA2 Nat.≤ Fin.toℕ x3r
                      x3rge = subst (sA2 Nat.≤_) (sym x3rN) (Nat.m≤m+n sA2 (sA1 + f1))
                      redx3 : Fin.toℕ (Fin.reduce≥ x3r x3rge) ≡ sA1 + f1
                      redx3 = toℕ-reduce≥ x3r x3rge ■ cong (Nat._∸ sA2) x3rN ■ Nat.m+n∸m≡n sA2 (sA1 + f1)
                      midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ x3r x3rge)
                      midlo = subst (sA1 Nat.≤_) (sym redx3) (Nat.m≤m+n sA1 f1)
                      midhi : Fin.toℕ (Fin.reduce≥ x3r x3rge) Nat.< sA1 + sB1
                      midhi = subst (Nat._< sA1 + sB1) (sym redx3) (Nat.+-monoʳ-< sA1 f1ltB1)
              z2f = assocSwapᵣ sA2 sB1 z1f
              z2 : Fin.toℕ z2f ≡ f1
              z2 = toℕ-assoc-mid sA2 sB1 z1f (subst (sA2 Nat.≤_) (sym z1) (Nat.m≤m+n sA2 f1))
                     (subst (Nat._< sA2 + sB1) (sym z1) (Nat.+-monoʳ-< sA2 f1ltB1))
                 ■ cong (Nat._∸ sA2) z1 ■ Nat.m+n∸m≡n sA2 f1
              z3 : Fin.toℕ ((((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2f) ≡ Fin.toℕ z2f
              z3 = toℕ-↑*-lt ((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 z2f (subst (Nat._< sB1) (sym z2) f1ltB1)
      B3 : sB2 + sB1 Nat.≤ f → Fin.toℕ (Ωᵗ x3) ≡ f
      B3 ge21 = toℕ-↑*-ge _ sB2 x3 x3q ■ cong (sB2 +_) omN ■ f2eq
        where
          f2 = f Nat.∸ (sB2 + sB1)
          f2eqB : (sB2 + sB1) + f2 ≡ f
          f2eqB = Nat.m+[n∸m]≡n ge21
          f2lt2 : f2 Nat.< 2
          f2lt2 = Nat.+-cancelˡ-< (sB2 + sB1) f2 2 (subst (Nat._< (sB2 + sB1) + 2) (sym f2eqB)
                    (subst (f Nat.<_) (sym (Nat.+-assoc sB2 sB1 2)) fltBpre))
          ge2 : sB2 Nat.≤ f
          ge2 = Nat.≤-trans (Nat.m≤m+n sB2 sB1) ge21
          f2eq : sB2 + (sB1 + f2) ≡ f
          f2eq = sym (Nat.+-assoc sB2 sB1 f2) ■ f2eqB
          -- ρaccᵗ on xrB (=2+f) ; f≥sB2+sB1 -> f
          asN : Fin.toℕ (assocSwapᵣ 2 sB2 xrB) ≡ 2 + f
          asN = toℕ-assoc-ge 2 sB2 xrB (subst (2 + sB2 Nat.≤_) (sym xrBN) (Nat.+-monoʳ-≤ 2 ge2)) ■ xrBN
          asge : sB2 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB2 xrB)
          asge = subst (sB2 Nat.≤_) (sym asN) (Nat.≤-trans (Nat.m≤n+m sB2 2) (Nat.+-monoʳ-≤ 2 ge2))
          asr = Fin.reduce≥ (assocSwapᵣ 2 sB2 xrB) asge
          asrN : Fin.toℕ asr ≡ 2 + (sB1 + f2)
          asrN = toℕ-reduce≥ (assocSwapᵣ 2 sB2 xrB) asge ■ cong (Nat._∸ sB2) asN ■ reassoc
            where open +-*-Solver
                  reassoc : (2 + f) Nat.∸ sB2 ≡ 2 + (sB1 + f2)
                  reassoc = cong (Nat._∸ sB2) (cong (2 +_) (sym f2eq) ■ solve 3 (λ b2 b1 t → con 2 :+ (b2 :+ (b1 :+ t)) := b2 :+ (con 2 :+ (b1 :+ t))) refl sB2 sB1 f2) ■ Nat.m+n∸m≡n sB2 (2 + (sB1 + f2))
          -- ra_inner on (2+(sB1+f2)) : aS(2,sB1) ge ; (aS(2,2)↑sB1) ge reduce ; aS(2,2) mid -> sB1+f2
          rai-asN : Fin.toℕ (assocSwapᵣ 2 sB1 asr) ≡ 2 + (sB1 + f2)
          rai-asN = toℕ-assoc-ge 2 sB1 asr (subst (2 + sB1 Nat.≤_) (sym asrN) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 f2))) ■ asrN
          raisge : sB1 Nat.≤ Fin.toℕ (assocSwapᵣ 2 sB1 asr)
          raisge = subst (sB1 Nat.≤_) (sym rai-asN) (Nat.≤-trans (Nat.m≤n+m sB1 2) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB1 f2)))
          raisr = Fin.reduce≥ (assocSwapᵣ 2 sB1 asr) raisge
          raisrN : Fin.toℕ raisr ≡ 2 + f2
          raisrN = toℕ-reduce≥ (assocSwapᵣ 2 sB1 asr) raisge ■ cong (Nat._∸ sB1) rai-asN ■ reassoc
            where open +-*-Solver
                  reassoc : (2 + (sB1 + f2)) Nat.∸ sB1 ≡ 2 + f2
                  reassoc = cong (Nat._∸ sB1) (solve 2 (λ b1 t → con 2 :+ (b1 :+ t) := b1 :+ (con 2 :+ t)) refl sB1 f2) ■ Nat.m+n∸m≡n sB1 (2 + f2)
          raiN : Fin.toℕ (ra-inner asr) ≡ sB1 + f2
          raiN = toℕ-↑*-ge (assocSwapᵣ 2 2 {n}) sB1 (assocSwapᵣ 2 sB1 asr) raisge
               ■ cong (sB1 +_) (toℕ-assoc-mid 2 2 raisr (subst (2 Nat.≤_) (sym raisrN) (Nat.m≤m+n 2 f2)) (subst (Nat._< 2 + 2) (sym raisrN) (Nat.+-monoʳ-< 2 f2lt2)) ■ cong (Nat._∸ 2) raisrN ■ Nat.m+n∸m≡n 2 f2)
          ρe : Fin.toℕ (ρaccᵗ xrB) ≡ f
          ρe = toℕ-↑*-ge ra-inner sB2 (assocSwapᵣ 2 sB2 xrB) asge ■ cong (sB2 +_) raiN ■ f2eq
          x1N : Fin.toℕ x1 ≡ sA2 + (sA1 + f)
          x1N = toℕ-↑*-ge (ρaccᵗ ↑* sA1) sA2 x a2le
              ■ cong (sA2 +_) (toℕ-↑*-ge ρaccᵗ sA1 xrA xrAge ■ cong (sA1 +_) ρe)
          a2lex1 : sA2 Nat.≤ Fin.toℕ x1
          a2lex1 = subst (sA2 Nat.≤_) (sym x1N) (Nat.m≤m+n sA2 (sA1 + f))
          redf : Fin.toℕ (Fin.reduce≥ x1 a2lex1) ≡ sA1 + f
          redf = toℕ-reduce≥ x1 a2lex1 ■ cong (Nat._∸ sA2) x1N ■ Nat.m+n∸m≡n sA2 (sA1 + f)
          x2N : Fin.toℕ x2 ≡ sA2 + (sA1 + f)
          x2N = toℕ-↑*-ge (assocSwapᵣ sA1 sB2) sA2 x1 a2lex1
              ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB2 (Fin.reduce≥ x1 a2lex1)
                  (subst (sA1 + sB2 Nat.≤_) (sym redf) (Nat.+-monoʳ-≤ sA1 ge2)) ■ redf)
          x3N : Fin.toℕ x3 ≡ sA2 + (sA1 + f)
          x3N = toℕ-assoc-ge sA2 sB2 x2 (subst (sA2 + sB2 Nat.≤_) (sym x2N)
                  (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB2 sA1) (Nat.+-monoʳ-≤ sA1 ge2)))) ■ x2N
          x3q : sB2 Nat.≤ Fin.toℕ x3
          x3q = subst (sB2 Nat.≤_) (sym x3N) (Nat.≤-trans (Nat.m≤n+m sB2 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) ge2) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 f))))
          x3r = Fin.reduce≥ x3 x3q
          x3rN : Fin.toℕ x3r ≡ sA2 + (sA1 + (sB1 + f2))
          x3rN = toℕ-reduce≥ x3 x3q ■ cong (Nat._∸ sB2) x3N ■ reassoc
            where open +-*-Solver
                  reassoc : (sA2 + (sA1 + f)) Nat.∸ sB2 ≡ sA2 + (sA1 + (sB1 + f2))
                  reassoc = cong (Nat._∸ sB2) (cong (λ z → sA2 + (sA1 + z)) (sym f2eq) ■ solve 4 (λ a2 a1 b2 t → a2 :+ (a1 :+ (b2 :+ t)) := b2 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB2 (sB1 + f2)) ■ Nat.m+n∸m≡n sB2 (sA2 + (sA1 + (sB1 + f2)))
          omN : Fin.toℕ (((assocSwapᵣ sA1 sB1 ↑* sA2)
                          ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ
                              (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) x3r)
                 ≡ sB1 + f2
          omN = z3 ■ cong (sB1 +_) l2
            where
              x3rge : sA2 Nat.≤ Fin.toℕ x3r
              x3rge = subst (sA2 Nat.≤_) (sym x3rN) (Nat.m≤m+n sA2 (sA1 + (sB1 + f2)))
              z1f = (assocSwapᵣ sA1 sB1 ↑* sA2) x3r
              z1 : Fin.toℕ z1f ≡ sA2 + (sA1 + (sB1 + f2))
              z1 = toℕ-↑*-ge (assocSwapᵣ sA1 sB1) sA2 x3r x3rge
                 ■ cong (sA2 +_) (toℕ-assoc-ge sA1 sB1 (Fin.reduce≥ x3r x3rge)
                     (subst (sA1 + sB1 Nat.≤_) (sym redx3) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 f2))) ■ redx3)
                where redx3 : Fin.toℕ (Fin.reduce≥ x3r x3rge) ≡ sA1 + (sB1 + f2)
                      redx3 = toℕ-reduce≥ x3r x3rge ■ cong (Nat._∸ sA2) x3rN ■ Nat.m+n∸m≡n sA2 (sA1 + (sB1 + f2))
              z2f = assocSwapᵣ sA2 sB1 z1f
              z2 : Fin.toℕ z2f ≡ sA2 + (sA1 + (sB1 + f2))
              z2 = toℕ-assoc-ge sA2 sB1 z1f (subst (sA2 + sB1 Nat.≤_) (sym z1)
                     (Nat.+-monoʳ-≤ sA2 (Nat.≤-trans (Nat.m≤n+m sB1 sA1) (Nat.+-monoʳ-≤ sA1 (Nat.m≤m+n sB1 f2))))) ■ z1
              z2q : sB1 Nat.≤ Fin.toℕ z2f
              z2q = subst (sB1 Nat.≤_) (sym z2) (Nat.≤-trans (Nat.m≤n+m sB1 (sA2 + sA1)) (Nat.≤-trans (Nat.+-monoʳ-≤ (sA2 + sA1) (Nat.m≤m+n sB1 f2)) (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 (sB1 + f2)))))
              z2r = Fin.reduce≥ z2f z2q
              z2rN : Fin.toℕ z2r ≡ sA2 + (sA1 + f2)
              z2rN = toℕ-reduce≥ z2f z2q ■ cong (Nat._∸ sB1) z2 ■ reassoc
                where open +-*-Solver
                      reassoc : (sA2 + (sA1 + (sB1 + f2))) Nat.∸ sB1 ≡ sA2 + (sA1 + f2)
                      reassoc = cong (Nat._∸ sB1) (solve 4 (λ a2 a1 b1 t → a2 :+ (a1 :+ (b1 :+ t)) := b1 :+ (a2 :+ (a1 :+ t))) refl sA2 sA1 sB1 f2) ■ Nat.m+n∸m≡n sB1 (sA2 + (sA1 + f2))
              -- L3 on z2r (= sA2+(sA1+f2)) : aS(sA1,2) mid -> f2 ; aS(sA2,2) mid -> f2
              z2rge : sA2 Nat.≤ Fin.toℕ z2r
              z2rge = subst (sA2 Nat.≤_) (sym z2rN) (Nat.m≤m+n sA2 (sA1 + f2))
              l1f = (assocSwapᵣ sA1 2 ↑* sA2) z2r
              l1 : Fin.toℕ l1f ≡ sA2 + f2
              l1 = toℕ-↑*-ge (assocSwapᵣ sA1 2) sA2 z2r z2rge
                 ■ cong (sA2 +_) (toℕ-assoc-mid sA1 2 (Fin.reduce≥ z2r z2rge) midlo midhi ■ cong (Nat._∸ sA1) redz ■ Nat.m+n∸m≡n sA1 f2)
                where redz : Fin.toℕ (Fin.reduce≥ z2r z2rge) ≡ sA1 + f2
                      redz = toℕ-reduce≥ z2r z2rge ■ cong (Nat._∸ sA2) z2rN ■ Nat.m+n∸m≡n sA2 (sA1 + f2)
                      midlo : sA1 Nat.≤ Fin.toℕ (Fin.reduce≥ z2r z2rge)
                      midlo = subst (sA1 Nat.≤_) (sym redz) (Nat.m≤m+n sA1 f2)
                      midhi : Fin.toℕ (Fin.reduce≥ z2r z2rge) Nat.< sA1 + 2
                      midhi = subst (Nat._< sA1 + 2) (sym redz) (Nat.+-monoʳ-< sA1 f2lt2)
              l2 : Fin.toℕ (assocSwapᵣ sA2 2 l1f) ≡ f2
              l2 = toℕ-assoc-mid sA2 2 l1f (subst (sA2 Nat.≤_) (sym l1) (Nat.m≤m+n sA2 f2))
                     (subst (Nat._< sA2 + 2) (sym l1) (Nat.+-monoʳ-< sA2 f2lt2))
                 ■ cong (Nat._∸ sA2) l1 ■ Nat.m+n∸m≡n sA2 f2
              z3 : Fin.toℕ ((((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1) z2f) ≡ sB1 + Fin.toℕ (assocSwapᵣ sA2 2 l1f)
              z3 = toℕ-↑*-ge ((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) sB1 z2f z2q
      Φ-B-body : Fin.toℕ (Ωᵗ x3) ≡ f
      Φ-B-body with Nat.<-cmp f sB2 | Nat.<-cmp f (sB2 + sB1)
      ... | tri< flt2 _ _ | _ = B1 flt2
      ... | tri≈ _ feq2 _ | tri< flt21 _ _ = B2 (Nat.≤-reflexive (sym feq2)) flt21
      ... | tri> _ _ fgt2 | tri< flt21 _ _ = B2 (Nat.<⇒≤ fgt2) flt21
      ... | tri≈ _ feq2 _ | tri≈ _ feq21 _ = B3 (Nat.≤-reflexive (sym feq21))
      ... | tri≈ _ feq2 _ | tri> _ _ fgt21 = B3 (Nat.<⇒≤ fgt21)
      ... | tri> _ _ fgt2 | tri≈ _ feq21 _ = B3 (Nat.≤-reflexive (sym feq21))
      ... | tri> _ _ fgt2 | tri> _ _ fgt21 = B3 (Nat.<⇒≤ fgt21)

-- leaf reconcile for the ν-comm case (the nested analogue of subEq-gen).
subEqComm-gen : ∀ {m n} (σ : m →ₛ n) (A₁ A₂ B₁ B₂ : BindGroup) →
  let sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
      ρacc = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
      Ω = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
  in (((leafσ (leafσ σ B₁ B₂) A₁ A₂ ·ₖ ((ρacc ↑* sA1) ↑* sA2))
         ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω
     ≗ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂) ·ₖ leafσ (leafσ σ A₁ A₂) B₁ B₂
subEqComm-gen {m} {n} σ A₁ A₂ B₁ B₂ i = body
  where
    a1 = sum A₁ ; a2 = sum A₂ ; b1 = sum B₁ ; b2 = sum B₂
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
    ρacc = assocSwapᵣ 2 sB2 ·ₖ ((assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)) ↑* sB2)
    Ω = ((assocSwapᵣ sA1 sB1 ↑* sA2) ·ₖ (assocSwapᵣ sA2 sB1 ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sB1))) ↑* sB2
    -- the full body-renaming chain as a single composite
    Φ : (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
        →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
    Φ = (((((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω)
    -- Φ fixes the toℕ of any index that lies at or above the whole permuted prefix.
    Φ-fix-ge : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
               → sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ x
               → Fin.toℕ (Φ x) ≡ Fin.toℕ x
    Φ-fix-ge x ge = lΩ ■ l3 ■ l2 ■ l1
      where
        x1 = ((ρacc ↑* sA1) ↑* sA2) x
        x1N : Fin.toℕ x1 ≡ Fin.toℕ x
        x1N = lift-fix-ge (ρacc ↑* sA1) sA2 (sA1 + (2 + (sB2 + (sB1 + 2))))
                (λ w q → lift-fix-ge ρacc sA1 (2 + (sB2 + (sB1 + 2)))
                           (λ u q′ → ρacc-fix-ge sB1 sB2 u q′) w q) x ge
        x2 = (assocSwapᵣ sA1 sB2 ↑* sA2) x1
        x2N : Fin.toℕ x2 ≡ Fin.toℕ x1
        x2N = toℕ-assoc↑*-fix-ge sA2 sA1 sB2 x1
                (subst (sA2 + (sA1 + sB2) Nat.≤_) (sym x1N)
                  (Nat.≤-trans (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1
                    (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2)) (Nat.m≤n+m (sB2 + (sB1 + 2)) 2)))) ge))
        x3 = assocSwapᵣ sA2 sB2 x2
        x3N : Fin.toℕ x3 ≡ Fin.toℕ x2
        x3N = toℕ-assoc-ge sA2 sB2 x2
                (subst (sA2 + sB2 Nat.≤_) (sym (x2N ■ x1N))
                  (Nat.≤-trans (Nat.+-monoʳ-≤ sA2
                    (Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2))
                      (Nat.≤-trans (Nat.m≤n+m (sB2 + (sB1 + 2)) 2) (Nat.m≤n+m _ sA1)))) ge))
        lΩ : Fin.toℕ (Ω x3) ≡ Fin.toℕ x3
        lΩ = lift-fix-ge _ sB2 (sA2 + (sA1 + (sB1 + 2)))
               (λ w q → ρω-fix-ge sA1 sA2 sB1 w q) x3 geΩ
          where
            geΩ : sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤ Fin.toℕ x3
            geΩ = subst (sB2 + (sA2 + (sA1 + (sB1 + 2))) Nat.≤_) (sym (x3N ■ x2N ■ x1N))
                    (Nat.≤-trans (Nat.≤-reflexive reassoc) (Nat.≤-trans bump ge))
              where reassoc : sB2 + (sA2 + (sA1 + (sB1 + 2))) ≡ sA2 + (sA1 + (sB2 + (sB1 + 2)))
                    reassoc = solve 4 (λ w u v t →
                                w :+ (u :+ (v :+ (t :+ con 2)))
                                := u :+ (v :+ (w :+ (t :+ con 2)))) refl sB2 sA2 sA1 sB1
                      where open +-*-Solver
                    bump : sA2 + (sA1 + (sB2 + (sB1 + 2))) Nat.≤ sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                    bump = Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.m≤n+m (sB2 + (sB1 + 2)) 2))
        l1 : Fin.toℕ x1 ≡ Fin.toℕ x
        l1 = x1N
        l2 : Fin.toℕ x2 ≡ Fin.toℕ x1
        l2 = x2N
        l3 : Fin.toℕ x3 ≡ Fin.toℕ x2
        l3 = x3N
    -- Φ reuses the module-level positional lemmas Φᵗ-A / Φᵗ-B.
    Φ-toℕ-A : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
              → Fin.toℕ x Nat.< sA2 + sA1
              → Fin.toℕ (Φ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
    Φ-toℕ-A x lt = Φᵗ-A sA1 sA2 sB1 sB2 x lt
    Φ-toℕ-B : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
              → sA2 + (sA1 + 2) Nat.≤ Fin.toℕ x
              → Fin.toℕ x Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
              → Fin.toℕ (Φ x) ≡ Fin.toℕ x Nat.∸ (sA2 + (sA1 + 2))
    Φ-toℕ-B x ge lt = Φᵗ-B sA1 sA2 sB1 sB2 x ge lt
    Φ-toℕ-Adata : ∀ (x : 𝔽 (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
                  → sA2 + sA1 Nat.≤ Fin.toℕ x
                  → Fin.toℕ x Nat.< sA2 + sA1 + 2
                  → Fin.toℕ (Φ x) ≡ (sB2 + (sB1 + 2)) + Fin.toℕ x
    Φ-toℕ-Adata x ge lt = Φᵗ-Adata sA1 sA2 sB1 sB2 x ge lt
    -- fuse the four body-renaming factors applied to a term into a single Φ.
    fuseΦ : (t : Tm (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))))
            → t ⋯ ((ρacc ↑* sA1) ↑* sA2) ⋯ (assocSwapᵣ sA1 sB2 ↑* sA2) ⋯ assocSwapᵣ sA2 sB2 ⋯ Ω
            ≡ t ⋯ Φ
    fuseΦ t =
        cong (λ z → z ⋯ assocSwapᵣ sA2 sB2 ⋯ Ω)
          (fusion t ((ρacc ↑* sA1) ↑* sA2) (assocSwapᵣ sA1 sB2 ↑* sA2))
      ■ cong (_⋯ Ω)
          (fusion t (((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) (assocSwapᵣ sA2 sB2))
      ■ fusion t ((((ρacc ↑* sA1) ↑* sA2) ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) Ω
    body : ((((leafσ (leafσ σ B₁ B₂) A₁ A₂ ·ₖ ((ρacc ↑* sA1) ↑* sA2))
               ·ₖ (assocSwapᵣ sA1 sB2 ↑* sA2)) ·ₖ assocSwapᵣ sA2 sB2) ·ₖ Ω) i
           ≡ (assocSwapᵣ (a1 + a2) (b1 + b2) ·ₖ leafσ (leafσ σ A₁ A₂) B₁ B₂) i
    body with Fin.splitAt (a1 + a2) i in eqo
    ... | inj₂ ii with Fin.splitAt (b1 + b2) ii in eqt
    ...   | inj₁ w with Fin.splitAt b1 w in eqw
    ...     | inj₁ jb =
                fuseΦ cB1t
              ■ midB1
              ■ sym rhsB1
              where
                cc₀ : UChan (2 + n)
                cc₀ = (K `unit , 0F , K `unit)
                cB1t = canonₛ B₁ cc₀ jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                         ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsB1 : leafσ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m))
                        ≡ canonₛ B₁ (K `unit , 0F , K `unit) jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsB1 =
                  leafσ-A₁ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m)) w jb
                    (Fin.splitAt-↑ˡ (b1 + b2) w (a1 + a2 + m)) eqw
                c₁ = canonₛ B₁ cc₀ jb
                assoc3 : (sA2 + (sA1 + 2)) + n ≡ sA2 + (sA1 + (2 + n))
                assoc3 = Nat.+-assoc sA2 (sA1 + 2) n ■ cong (sA2 +_) (Nat.+-assoc sA1 2 n)
                ρ₁ : (2 + n) →ᵣ (2 + (sA2 + (sA1 + (2 + n))))
                ρ₁ = λ y → Fin.cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) y)
                ρ₁0F : ρ₁ 0F ≡ 0F
                ρ₁0F = Fin.toℕ-injective (Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) 0F))
                ρ₁tailN : ∀ (k : 𝔽 n) → Fin.toℕ (ρ₁ (2 ↑ʳ k)) ≡ 2 + ((sA2 + (sA1 + 2)) + Fin.toℕ k)
                ρ₁tailN k = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) (2 ↑ʳ k))
                          ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 (2 ↑ʳ k) q2
                          ■ cong (2 +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ (2 ↑ʳ k) q2) ■ cong ((sA2 + (sA1 + 2)) +_) redk)
                  where q2 : 2 Nat.≤ Fin.toℕ (2 ↑ʳ k)
                        q2 = subst (2 Nat.≤_) (sym (Fin.toℕ-↑ʳ 2 k)) (Nat.m≤m+n 2 (Fin.toℕ k))
                        redk : Fin.toℕ (Fin.reduce≥ (2 ↑ʳ k) q2) ≡ Fin.toℕ k
                        redk = toℕ-reduce≥ (2 ↑ʳ k) q2 ■ cong (Nat._∸ 2) (Fin.toℕ-↑ʳ 2 k) ■ Nat.m+n∸m≡n 2 (Fin.toℕ k)
                wk4c : (sB1 + (2 + n)) →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
                wk4c = (((weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                Λ : (sB1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ = wk4c ·ₖ Φ
                wkc4eq : cB1t ≡ c₁ ⋯ wk4c
                wkc4eq =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
                  ■ fusion c₁ ((weaken* ⦃ Kᵣ ⦄ sB2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2)
                fuseΛ : cB1t ⋯ Φ ≡ c₁ ⋯ Λ
                fuseΛ = cong (_⋯ Φ) wkc4eq ■ fusion c₁ wk4c Φ
                ΛEq : Λ ≗ (ρ₁ ↑* sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
                ΛEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    wk4cN : Fin.toℕ (wk4c y) ≡ sA2 + (sA1 + (2 + (sB2 + Fin.toℕ y)))
                    wk4cN = toℕ-weaken*ᵣ sA2 _
                          ■ cong (sA2 +_) (toℕ-weaken*ᵣ sA1 _
                          ■ cong (sA1 +_) (cong (2 +_) (toℕ-weaken*ᵣ sB2 y)))
                    rhsN : Fin.toℕ (((ρ₁ ↑* sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) y)
                           ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    rhsN = toℕ-weaken*ᵣ sB2 ((ρ₁ ↑* sB1) y)
                    assocB : ∀ X → sA2 + (sA1 + (2 + X)) ≡ (sA2 + (sA1 + 2)) + X
                    assocB X = cong (sA2 +_) (sym (Nat.+-assoc sA1 2 X)) ■ sym (Nat.+-assoc sA2 (sA1 + 2) X)
                    ρ₁liftData : Fin.toℕ y Nat.< sB1 + 2 → sB1 Nat.≤ Fin.toℕ y → Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ Fin.toℕ y
                    ρ₁liftData ylt ge1 = toℕ-↑*-ge ρ₁ sB1 y ge1 ■ cong (sB1 +_) ρ₁red ■ Nat.m+[n∸m]≡n ge1
                      where
                        dd = Fin.toℕ y Nat.∸ sB1
                        dlt2 : dd Nat.< 2
                        dlt2 = Nat.+-cancelˡ-< sB1 dd 2 (subst (Nat._< sB1 + 2) (sym (Nat.m+[n∸m]≡n ge1)) ylt)
                        ρ₁red : Fin.toℕ (ρ₁ (Fin.reduce≥ y ge1)) ≡ dd
                        ρ₁red = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) (Fin.reduce≥ y ge1))
                              ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 (Fin.reduce≥ y ge1)
                                  (subst (Nat._< 2) (sym redy) dlt2)
                              ■ redy
                          where redy : Fin.toℕ (Fin.reduce≥ y ge1) ≡ dd
                                redy = toℕ-reduce≥ y ge1
                    ρ₁liftLow : Fin.toℕ y Nat.< sB1 + 2 → Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ Fin.toℕ y
                    ρ₁liftLow ylt with Nat.<-cmp (Fin.toℕ y) sB1
                    ... | tri< ylt1 _ _ = toℕ-↑*-lt ρ₁ sB1 y ylt1
                    ... | tri≈ _ yeq1 _ = ρ₁liftData ylt (Nat.≤-reflexive (sym yeq1))
                    ... | tri> _ _ ygt1 = ρ₁liftData ylt (Nat.<⇒≤ ygt1)
                    tailEq : sB1 + 2 Nat.≤ Fin.toℕ y → Fin.toℕ (Λ y) ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    tailEq ge2 = Φ-fix-ge (wk4c y) geΦ ■ wk4cN ■ assocFinal ■ sym (cong (sB2 +_) ρ₁high)
                      where
                        d2 = Fin.toℕ y Nat.∸ (sB1 + 2)
                        yd : (sB1 + 2) + d2 ≡ Fin.toℕ y
                        yd = Nat.m+[n∸m]≡n ge2
                        ge1 : sB1 Nat.≤ Fin.toℕ y
                        ge1 = Nat.≤-trans (Nat.m≤m+n sB1 2) ge2
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (wk4c y)
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wk4cN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2
                                  (Nat.+-monoʳ-≤ sB2 ge2))))
                        z = Fin.reduce≥ y ge1
                        zN : Fin.toℕ z ≡ 2 + d2
                        zN = toℕ-reduce≥ y ge1 ■ red2
                          where red2 : Fin.toℕ y Nat.∸ sB1 ≡ 2 + d2
                                red2 = cong (Nat._∸ sB1) (sym yd) ■ cong (Nat._∸ sB1) (Nat.+-assoc sB1 2 d2) ■ Nat.m+n∸m≡n sB1 (2 + d2)
                        z2 : 2 Nat.≤ Fin.toℕ z
                        z2 = subst (2 Nat.≤_) (sym zN) (Nat.m≤m+n 2 d2)
                        ρ₁zN : Fin.toℕ (ρ₁ z) ≡ 2 + ((sA2 + (sA1 + 2)) + d2)
                        ρ₁zN = Fin.toℕ-cast (cong (2 +_) assoc3) ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* 2) z)
                             ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) 2 z z2
                             ■ cong (2 +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ z z2)
                                 ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ z z2 ■ cong (Nat._∸ 2) zN ■ Nat.m+n∸m≡n 2 d2))
                        ρ₁high : Fin.toℕ ((ρ₁ ↑* sB1) y) ≡ sB1 + (2 + ((sA2 + (sA1 + 2)) + d2))
                        ρ₁high = toℕ-↑*-ge ρ₁ sB1 y ge1 ■ cong (sB1 +_) ρ₁zN
                        assocFinal : sA2 + (sA1 + (2 + (sB2 + Fin.toℕ y))) ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d2)))
                        assocFinal = cong (λ w → sA2 + (sA1 + (2 + (sB2 + w)))) (sym yd) ■ solveFinal
                          where open +-*-Solver
                                solveFinal : sA2 + (sA1 + (2 + (sB2 + ((sB1 + 2) + d2))))
                                             ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d2)))
                                solveFinal = solve 5 (λ a2 a1 b2 b1 t →
                                                a2 :+ (a1 :+ (con 2 :+ (b2 :+ ((b1 :+ con 2) :+ t))))
                                                := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ t))))
                                              refl sA2 sA1 sB2 sB1 d2
                    lhsN : Fin.toℕ (Λ y) ≡ sB2 + Fin.toℕ ((ρ₁ ↑* sB1) y)
                    lhsN with Nat.<-cmp (Fin.toℕ y) (sB1 + 2)
                    ... | tri< ylt _ _ =
                            Φ-toℕ-B (wk4c y) geB ltB
                          ■ cong (Nat._∸ (sA2 + (sA1 + 2))) (wk4cN ■ assocB (sB2 + Fin.toℕ y))
                          ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ y)
                          ■ sym (cong (sB2 +_) (ρ₁liftLow ylt))
                      where
                        geB : sA2 + (sA1 + 2) Nat.≤ Fin.toℕ (wk4c y)
                        geB = subst (sA2 + (sA1 + 2) Nat.≤_) (sym wk4cN)
                                (subst (sA2 + (sA1 + 2) Nat.≤_) (sym (assocB (sB2 + Fin.toℕ y)))
                                  (Nat.m≤m+n (sA2 + (sA1 + 2)) (sB2 + Fin.toℕ y)))
                        ltB : Fin.toℕ (wk4c y) Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                        ltB = subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) (sym wk4cN)
                                (Nat.+-monoʳ-< sA2 (Nat.+-monoʳ-< sA1 (Nat.+-monoʳ-< 2
                                  (Nat.+-monoʳ-< sB2 ylt))))
                    ... | tri≈ _ yeq _ = tailEq (Nat.≤-reflexive (sym yeq))
                    ... | tri> _ _ ygt = tailEq (Nat.<⇒≤ ygt)
                mapcc : mapᶜ ρ₁ cc₀ ≡ (K `unit , 0F , K `unit)
                mapcc = cong₂ _,_ refl (cong₂ _,_ ρ₁0F refl)
                midB1 : cB1t ⋯ Φ ≡ canonₛ B₁ (K `unit , 0F , K `unit) jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midB1 =
                    fuseΛ
                  ■ ⋯-cong (canonₛ B₁ cc₀ jb) ΛEq
                  ■ sym (fusion (canonₛ B₁ cc₀ jb) (ρ₁ ↑* sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2) (canonₛ-nat B₁ cc₀ ρ₁ jb)
                  ■ cong (λ c → canonₛ B₁ c jb ⋯ weaken* ⦃ Kᵣ ⦄ sB2) mapcc
    ...     | inj₂ kb =
                fuseΦ cB2t
              ■ midB2
              ■ sym rhsB2
              where
                flagIdx : 𝔽 (sB1 + (2 + n))
                flagIdx = weaken* ⦃ Kᵣ ⦄ sB1 1F
                cc₂ : UChan (sB1 + (2 + n))
                cc₂ = (K `unit , flagIdx , K `unit)
                c₂ = canonₛ B₂ cc₂ kb
                cB2t = c₂ ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsB2 : leafσ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m))
                        ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) kb
                rhsB2 =
                  leafσ-B₁ (leafσ σ A₁ A₂) B₁ B₂ (w ↑ˡ (a1 + a2 + m)) w kb
                    (Fin.splitAt-↑ˡ (b1 + b2) w (a1 + a2 + m)) eqw
                assoc3 : (sA2 + (sA1 + 2)) + n ≡ sA2 + (sA1 + (2 + n))
                assoc3 = Nat.+-assoc sA2 (sA1 + 2) n ■ cong (sA2 +_) (Nat.+-assoc sA1 2 n)
                assocIn : (sB1 + 2) + n ≡ sB1 + (2 + n)
                assocIn = Nat.+-assoc sB1 2 n
                assocOut : (sB1 + 2) + ((sA2 + (sA1 + 2)) + n) ≡ sB1 + (2 + (sA2 + (sA1 + (2 + n))))
                assocOut = Nat.+-assoc sB1 2 ((sA2 + (sA1 + 2)) + n) ■ cong (sB1 +_) (cong (2 +_) assoc3)
                ρ₂ : (sB1 + (2 + n)) →ᵣ (sB1 + (2 + (sA2 + (sA1 + (2 + n)))))
                ρ₂ = λ y → Fin.cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) y))
                flagN : Fin.toℕ flagIdx ≡ sB1 + 1
                flagN = toℕ-weaken*ᵣ sB1 1F
                ρ₂flag : ρ₂ flagIdx ≡ weaken* ⦃ Kᵣ ⦄ sB1 1F
                ρ₂flag = Fin.toℕ-injective
                  ( Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) flagIdx))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) flagIdx) flagLt
                  ■ castN
                  ■ sym (toℕ-weaken*ᵣ sB1 1F) )
                  where castN : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) ≡ sB1 + 1
                        castN = Fin.toℕ-cast (sym assocIn) flagIdx ■ flagN
                        flagLt : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) Nat.< sB1 + 2
                        flagLt = subst (Nat._< sB1 + 2) (sym castN) (Nat.+-monoʳ-< sB1 (Nat.s≤s (Nat.s≤s Nat.z≤n)))
                wk3c : (sB2 + (sB1 + (2 + n))) →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
                wk3c = ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                Λ₂ : (sB2 + (sB1 + (2 + n))) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ₂ = wk3c ·ₖ Φ
                wkc3eq : cB2t ≡ c₂ ⋯ wk3c
                wkc3eq =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                      (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
                  ■ fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2)
                fuseΛ₂ : cB2t ⋯ Φ ≡ c₂ ⋯ Λ₂
                fuseΛ₂ = cong (_⋯ Φ) wkc3eq ■ fusion c₂ wk3c Φ
                ρ₂N-low : ∀ (z : 𝔽 (sB1 + (2 + n))) → Fin.toℕ z Nat.< sB1 + 2 → Fin.toℕ (ρ₂ z) ≡ Fin.toℕ z
                ρ₂N-low z zlt =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) z))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) z)
                      (subst (Nat._< sB1 + 2) (sym (Fin.toℕ-cast (sym assocIn) z)) zlt)
                  ■ Fin.toℕ-cast (sym assocIn) z
                ρ₂N-high : ∀ (z : 𝔽 (sB1 + (2 + n))) → sB1 + 2 Nat.≤ Fin.toℕ z →
                           Fin.toℕ (ρ₂ z) ≡ sB1 + (2 + ((sA2 + (sA1 + 2)) + (Fin.toℕ z Nat.∸ (sB1 + 2))))
                ρ₂N-high z zge =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2)) ↑* (sB1 + 2)) (Fin.cast (sym assocIn) z))
                  ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sA2 + (sA1 + 2))) (sB1 + 2) (Fin.cast (sym assocIn) z) zge'
                  ■ cong ((sB1 + 2) +_) (toℕ-weaken*ᵣ (sA2 + (sA1 + 2)) (Fin.reduce≥ (Fin.cast (sym assocIn) z) zge')
                      ■ cong ((sA2 + (sA1 + 2)) +_) (toℕ-reduce≥ (Fin.cast (sym assocIn) z) zge' ■ cong (Nat._∸ (sB1 + 2)) (Fin.toℕ-cast (sym assocIn) z)))
                  ■ Nat.+-assoc sB1 2 ((sA2 + (sA1 + 2)) + (Fin.toℕ z Nat.∸ (sB1 + 2)))
                  where zge' : sB1 + 2 Nat.≤ Fin.toℕ (Fin.cast (sym assocIn) z)
                        zge' = subst (sB1 + 2 Nat.≤_) (sym (Fin.toℕ-cast (sym assocIn) z)) zge
                Λ₂Eq : Λ₂ ≗ ρ₂ ↑* sB2
                Λ₂Eq y = Fin.toℕ-injective lhsN
                  where
                    wk3cN : Fin.toℕ (wk3c y) ≡ sA2 + (sA1 + (2 + Fin.toℕ y))
                    wk3cN = toℕ-weaken*ᵣ sA2 _
                          ■ cong (sA2 +_) (toℕ-weaken*ᵣ sA1 _ ■ cong (sA1 +_) (toℕ-weaken*ᵣ 2 y))
                    assocB : ∀ X → sA2 + (sA1 + (2 + X)) ≡ (sA2 + (sA1 + 2)) + X
                    assocB X = cong (sA2 +_) (sym (Nat.+-assoc sA1 2 X)) ■ sym (Nat.+-assoc sA2 (sA1 + 2) X)
                    ρ₂liftData : Fin.toℕ y Nat.< sB2 + (sB1 + 2) → sB2 Nat.≤ Fin.toℕ y → Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ Fin.toℕ y
                    ρ₂liftData ylt ge1 = toℕ-↑*-ge ρ₂ sB2 y ge1 ■ cong (sB2 +_) (ρ₂N-low (Fin.reduce≥ y ge1) redlt ■ toℕ-reduce≥ y ge1) ■ Nat.m+[n∸m]≡n ge1
                      where redlt : Fin.toℕ (Fin.reduce≥ y ge1) Nat.< sB1 + 2
                            redlt = subst (Nat._< sB1 + 2) (sym (toℕ-reduce≥ y ge1))
                                      (Nat.+-cancelˡ-< sB2 _ (sB1 + 2)
                                        (subst (Nat._< sB2 + (sB1 + 2)) (sym (Nat.m+[n∸m]≡n ge1)) ylt))
                    ρ₂liftLow : Fin.toℕ y Nat.< sB2 + (sB1 + 2) → Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ Fin.toℕ y
                    ρ₂liftLow ylt with Nat.<-cmp (Fin.toℕ y) sB2
                    ... | tri< ylt1 _ _ = toℕ-↑*-lt ρ₂ sB2 y ylt1
                    ... | tri≈ _ yeq1 _ = ρ₂liftData ylt (Nat.≤-reflexive (sym yeq1))
                    ... | tri> _ _ ygt1 = ρ₂liftData ylt (Nat.<⇒≤ ygt1)
                    tailEq : sB2 + (sB1 + 2) Nat.≤ Fin.toℕ y → Fin.toℕ (Λ₂ y) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                    tailEq ge3 = Φ-fix-ge (wk3c y) geΦ ■ wk3cN ■ tailEq2
                      where
                        d3 = Fin.toℕ y Nat.∸ (sB2 + (sB1 + 2))
                        yd : (sB2 + (sB1 + 2)) + d3 ≡ Fin.toℕ y
                        yd = Nat.m+[n∸m]≡n ge3
                        ge2 : sB2 Nat.≤ Fin.toℕ y
                        ge2 = Nat.≤-trans (Nat.m≤m+n sB2 (sB1 + 2)) ge3
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (wk3c y)
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wk3cN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 ge3)))
                        z = Fin.reduce≥ y ge2
                        zN : Fin.toℕ z ≡ (sB1 + 2) + d3
                        zN = toℕ-reduce≥ y ge2 ■ red2
                          where red2 : Fin.toℕ y Nat.∸ sB2 ≡ (sB1 + 2) + d3
                                red2 = cong (Nat._∸ sB2) (sym yd) ■ cong (Nat._∸ sB2) (Nat.+-assoc sB2 (sB1 + 2) d3) ■ Nat.m+n∸m≡n sB2 ((sB1 + 2) + d3)
                        zge : sB1 + 2 Nat.≤ Fin.toℕ z
                        zge = subst (sB1 + 2 Nat.≤_) (sym zN) (Nat.m≤m+n (sB1 + 2) d3)
                        ρ₂high : Fin.toℕ ((ρ₂ ↑* sB2) y) ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d3)))
                        ρ₂high = toℕ-↑*-ge ρ₂ sB2 y ge2 ■ cong (sB2 +_) (ρ₂N-high z zge ■ cong (λ w → sB1 + (2 + ((sA2 + (sA1 + 2)) + w))) zd3)
                          where zd3 : Fin.toℕ z Nat.∸ (sB1 + 2) ≡ d3
                                zd3 = cong (Nat._∸ (sB1 + 2)) zN ■ Nat.m+n∸m≡n (sB1 + 2) d3
                        tailEq2 : sA2 + (sA1 + (2 + Fin.toℕ y)) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                        tailEq2 = cong (λ w → sA2 + (sA1 + (2 + w))) (sym yd) ■ solveT ■ sym ρ₂high
                          where open +-*-Solver
                                solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + d3)))
                                         ≡ sB2 + (sB1 + (2 + ((sA2 + (sA1 + 2)) + d3)))
                                solveT = solve 5 (λ a2 a1 b2 b1 t →
                                            a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ t)))
                                            := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ t))))
                                          refl sA2 sA1 sB2 sB1 d3
                    lhsN : Fin.toℕ (Λ₂ y) ≡ Fin.toℕ ((ρ₂ ↑* sB2) y)
                    lhsN with Nat.<-cmp (Fin.toℕ y) (sB2 + (sB1 + 2))
                    ... | tri< ylt _ _ =
                            Φ-toℕ-B (wk3c y) geB ltB
                          ■ cong (Nat._∸ (sA2 + (sA1 + 2))) (wk3cN ■ assocB (Fin.toℕ y))
                          ■ Nat.m+n∸m≡n (sA2 + (sA1 + 2)) (Fin.toℕ y)
                          ■ sym (ρ₂liftLow ylt)
                      where
                        geB : sA2 + (sA1 + 2) Nat.≤ Fin.toℕ (wk3c y)
                        geB = subst (sA2 + (sA1 + 2) Nat.≤_) (sym wk3cN)
                                (subst (sA2 + (sA1 + 2) Nat.≤_) (sym (assocB (Fin.toℕ y)))
                                  (Nat.m≤m+n (sA2 + (sA1 + 2)) (Fin.toℕ y)))
                        ltB : Fin.toℕ (wk3c y) Nat.< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))
                        ltB = subst (Nat._< sA2 + (sA1 + (2 + (sB2 + (sB1 + 2))))) (sym wk3cN)
                                (Nat.+-monoʳ-< sA2 (Nat.+-monoʳ-< sA1 (Nat.+-monoʳ-< 2 ylt)))
                    ... | tri≈ _ yeq _ = tailEq (Nat.≤-reflexive (sym yeq))
                    ... | tri> _ _ ygt = tailEq (Nat.<⇒≤ ygt)
                mapcc2 : mapᶜ ρ₂ cc₂ ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit)
                mapcc2 = cong₂ _,_ refl (cong₂ _,_ ρ₂flag refl)
                midB2 : cB2t ⋯ Φ ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sB1 1F , K `unit) kb
                midB2 =
                    fuseΛ₂
                  ■ ⋯-cong c₂ Λ₂Eq
                  ■ canonₛ-nat B₂ cc₂ ρ₂ kb
                  ■ cong (λ c → canonₛ B₂ c kb) mapcc2
    body | inj₂ ii | inj₂ jj =
        fuseΦ wk6t
      ■ fuseWk
      ■ ⋯-cong (σ jj) renEq
      ■ sym fuseSmall
      ■ sym rhsσ
      where
        wk6t = σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                      ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
        wk6c : n →ᵣ (sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + n))))))
        wk6c = (((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
                 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
        renSmall : n →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
        renSmall = ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2)
                   ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
        -- fuse the 6 weakens into wk6c (so wk6t ⋯ Φ = σ jj ⋯ (wk6c ·ₖ Φ))
        fuseWk : wk6t ⋯ Φ ≡ σ jj ⋯ (wk6c ·ₖ Φ)
        fuseWk =
            cong (λ t → t ⋯ Φ)
              ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) (weaken* ⦃ Kᵣ ⦄ 2))
              ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2)
                  (fusion (σ jj) (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
              ■ fusion (σ jj) ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2) )
          ■ fusion (σ jj) wk6c Φ
        -- the key renaming identity (all images land high; Φ fixes them).
        renEq : (wk6c ·ₖ Φ) ≗ renSmall
        renEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
          where
            w6 = wk6c y
            highw6 : Fin.toℕ w6 ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            highw6 =
                toℕ-weaken*ᵣ sA2 _
              ■ cong (sA2 +_) ( toℕ-weaken*ᵣ sA1 _
              ■ cong (sA1 +_) (cong (2 +_) ( toℕ-weaken*ᵣ sB2 _
              ■ cong (sB2 +_) ( toℕ-weaken*ᵣ sB1 _
              ■ cong (sB1 +_) refl ) )) )
            geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ w6
            geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym highw6)
                    (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2
                      (Nat.+-monoʳ-≤ sB2 (Nat.+-monoʳ-≤ sB1 (Nat.+-monoʳ-≤ 2 Nat.z≤n))))))
            lhsN : Fin.toℕ ((wk6c ·ₖ Φ) y) ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            lhsN = Φ-fix-ge w6 geΦ ■ highw6
            rhsN : Fin.toℕ (renSmall y) ≡ sA2 + (sA1 + (2 + (sB2 + (sB1 + (2 + Fin.toℕ y)))))
            rhsN =
                ( toℕ-weaken*ᵣ sB2 _
                ■ cong (sB2 +_) ( toℕ-weaken*ᵣ sB1 _
                ■ cong (sB1 +_) (cong (2 +_) ( toℕ-weaken*ᵣ sA2 _
                ■ cong (sA2 +_) ( toℕ-weaken*ᵣ sA1 _
                ■ cong (sA1 +_) refl ) )) ) )
              ■ blockComm sB2 sB1 sA2 sA1 (Fin.toℕ y)
        fuseSmall : σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                    ≡ σ jj ⋯ renSmall
        fuseSmall =
            cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sA1))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) (weaken* ⦃ Kᵣ ⦄ sA2))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2))
          ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (fusion (σ jj) (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
          ■ fusion (σ jj) ((((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2)
        rhsσ : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ ((a1 + a2) ↑ʳ jj))
               ≡ σ jj ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sA1 ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                       ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
        rhsσ =
            leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ ((a1 + a2) ↑ʳ jj)) ((a1 + a2) ↑ʳ jj)
              (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) ((a1 + a2) ↑ʳ jj))
          ■ cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
              (leafσ-tail σ A₁ A₂ ((a1 + a2) ↑ʳ jj) jj (Fin.splitAt-↑ʳ (a1 + a2) m jj))
    body | inj₁ z with Fin.splitAt a1 z in eqi
    ...   | inj₁ j =
                fuseΦ cA1t
              ■ midA1
              ■ sym rhsA1
              where
                cc₀ : UChan (2 + n)
                cc₀ = (K `unit , 0F , K `unit)
                cc₀big : UChan (2 + (sB2 + (sB1 + (2 + n))))
                cc₀big = (K `unit , 0F , K `unit)
                cA1t = canonₛ A₁ cc₀big j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                rhsA1 : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m))
                        ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsA1 =
                    leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m)) (z ↑ˡ m)
                      (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) (z ↑ˡ m))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                      (leafσ-A₁ σ A₁ A₂ (z ↑ˡ m) z j (Fin.splitAt-↑ˡ (a1 + a2) z m) eqi)
                c₁ = canonₛ A₁ cc₀ j
                assoc-A : (sB2 + (sB1 + 2)) + n ≡ sB2 + (sB1 + (2 + n))
                assoc-A = Nat.+-assoc sB2 (sB1 + 2) n ■ cong (sB2 +_) (Nat.+-assoc sB1 2 n)
                ρA : (2 + n) →ᵣ (2 + (sB2 + (sB1 + (2 + n))))
                ρA = λ y → Fin.cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) y)
                ρA0F : ρA 0F ≡ 0F
                ρA0F = Fin.toℕ-injective (Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) 0F))
                mapcc : mapᶜ ρA cc₀ ≡ (K `unit , 0F , K `unit)
                mapcc = cong₂ _,_ refl (cong₂ _,_ ρA0F refl)
                ΨLHS : (sA1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                ΨLHS = ((ρA ↑* sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) ·ₖ Φ
                ΨRHS : (sA1 + (2 + n)) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                ΨRHS = ((weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2
                fuseL : cA1t ⋯ Φ ≡ c₁ ⋯ ΨLHS
                fuseL =
                    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sA2 ⋯ Φ)
                      (sym (canonₛ-nat A₁ cc₀ ρA j ■ cong (λ c → canonₛ A₁ c j) mapcc))
                  ■ cong (_⋯ Φ) (fusion c₁ (ρA ↑* sA1) (weaken* ⦃ Kᵣ ⦄ sA2))
                  ■ fusion c₁ ((ρA ↑* sA1) ·ₖ weaken* ⦃ Kᵣ ⦄ sA2) Φ
                fuseR : c₁ ⋯ ΨRHS
                        ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                fuseR =
                    sym ( cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                            (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sA2) (weaken* ⦃ Kᵣ ⦄ 2))
                        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                            (fusion c₁ (weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1))
                        ■ fusion c₁ ((weaken* ⦃ Kᵣ ⦄ sA2 ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2) )
                ΨEq : ΨLHS ≗ ΨRHS
                ΨEq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    t = Fin.toℕ y
                    rhsN : Fin.toℕ (ΨRHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    rhsN = toℕ-weaken*ᵣ sB2 _
                         ■ cong (sB2 +_) (toℕ-weaken*ᵣ sB1 _
                         ■ cong (sB1 +_) (toℕ-weaken*ᵣ 2 _
                         ■ cong (2 +_) (toℕ-weaken*ᵣ sA2 y)))
                    dataEq : sA1 Nat.≤ t → t Nat.< sA1 + 2 → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    dataEq ge2 lt2 = Φ-toℕ-Adata (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) wge wlt
                                   ■ cong ((sB2 + (sB1 + 2)) +_) wN
                                   ■ solveD
                      where
                        dd = t Nat.∸ sA1
                        td : sA1 + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge2
                        ddlt2 : dd Nat.< 2
                        ddlt2 = Nat.+-cancelˡ-< sA1 dd 2 (subst (Nat._< sA1 + 2) (sym td) lt2)
                        ρAred : Fin.toℕ (ρA (Fin.reduce≥ y ge2)) ≡ dd
                        ρAred = Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) (Fin.reduce≥ y ge2))
                              ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) 2 (Fin.reduce≥ y ge2)
                                  (subst (Nat._< 2) (sym redy) ddlt2)
                              ■ redy
                          where redy : Fin.toℕ (Fin.reduce≥ y ge2) ≡ dd
                                redy = toℕ-reduce≥ y ge2
                        ρAhigh : Fin.toℕ ((ρA ↑* sA1) y) ≡ t
                        ρAhigh = toℕ-↑*-ge ρA sA1 y ge2 ■ cong (sA1 +_) ρAred ■ td
                        wN : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + t
                        wN = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) ρAhigh
                        wge : sA2 + sA1 Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y))
                        wge = subst (sA2 + sA1 Nat.≤_) (sym wN) (Nat.+-monoʳ-≤ sA2 ge2)
                        wlt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) Nat.< sA2 + sA1 + 2
                        wlt = subst (Nat._< sA2 + sA1 + 2) (sym wN)
                                (subst (Nat._< sA2 + sA1 + 2) (Nat.+-assoc sA2 sA1 dd ■ cong (sA2 +_) td)
                                  (Nat.+-monoʳ-< (sA2 + sA1) ddlt2))
                        open +-*-Solver
                        solveD : (sB2 + (sB1 + 2)) + (sA2 + t) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        solveD = solve 4 (λ b2 b1 a2 s →
                                    (b2 :+ (b1 :+ con 2)) :+ (a2 :+ s)
                                    := b2 :+ (b1 :+ (con 2 :+ (a2 :+ s)))) refl sB2 sB1 sA2 t
                    tailEq : sA1 + 2 Nat.≤ t → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    tailEq ge2 = Φ-fix-ge (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) geΦ ■ wN ■ solveT
                      where
                        dd = t Nat.∸ (sA1 + 2)
                        td : (sA1 + 2) + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge2
                        ge1 : sA1 Nat.≤ t
                        ge1 = Nat.≤-trans (Nat.m≤m+n sA1 2) ge2
                        red0 = Fin.reduce≥ y ge1
                        red0N : Fin.toℕ red0 ≡ 2 + dd
                        red0N = toℕ-reduce≥ y ge1 ■ red2
                          where red2 : t Nat.∸ sA1 ≡ 2 + dd
                                red2 = cong (Nat._∸ sA1) (sym td) ■ cong (Nat._∸ sA1) (Nat.+-assoc sA1 2 dd) ■ Nat.m+n∸m≡n sA1 (2 + dd)
                        red0ge2 : 2 Nat.≤ Fin.toℕ red0
                        red0ge2 = subst (2 Nat.≤_) (sym red0N) (Nat.m≤m+n 2 dd)
                        ρAred : Fin.toℕ (ρA red0) ≡ 2 + ((sB2 + (sB1 + 2)) + dd)
                        ρAred = Fin.toℕ-cast (cong (2 +_) assoc-A) ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* 2) red0)
                              ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) 2 red0 red0ge2
                              ■ cong (2 +_) (toℕ-weaken*ᵣ (sB2 + (sB1 + 2)) (Fin.reduce≥ red0 red0ge2)
                                  ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ red0 red0ge2 ■ cong (Nat._∸ 2) red0N ■ Nat.m+n∸m≡n 2 dd))
                        ρAhigh : Fin.toℕ ((ρA ↑* sA1) y) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))
                        ρAhigh = toℕ-↑*-ge ρA sA1 y ge1 ■ cong (sA1 +_) ρAred
                        wN : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd)))
                        wN = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) ρAhigh
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y))
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym wN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n (sB2 + (sB1 + 2)) dd))))
                        open +-*-Solver
                        solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        solveT = solve 5 (λ a2 a1 b2 b1 w →
                                    a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ w)))
                                    := b2 :+ (b1 :+ (con 2 :+ (a2 :+ ((a1 :+ con 2) :+ w))))) refl sA2 sA1 sB2 sB1 dd
                               ■ cong (λ w → sB2 + (sB1 + (2 + (sA2 + w)))) td
                    lhsN : Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                    lhsN with Nat.<-cmp t sA1
                    ... | tri< tlt _ _ = lowEq
                      where
                        lA : Fin.toℕ ((ρA ↑* sA1) y) ≡ t
                        lA = toℕ-↑*-lt ρA sA1 y tlt
                        wA : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) ≡ sA2 + t
                        wA = toℕ-weaken*ᵣ sA2 _ ■ cong (sA2 +_) lA
                        wlt : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) Nat.< sA2 + sA1
                        wlt = subst (Nat._< sA2 + sA1) (sym wA) (Nat.+-monoʳ-< sA2 tlt)
                        lowEq : Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        lowEq = Φ-toℕ-A (weaken* ⦃ Kᵣ ⦄ sA2 ((ρA ↑* sA1) y)) wlt
                              ■ cong ((sB2 + (sB1 + 2)) +_) wA
                              ■ solveLow
                          where open +-*-Solver
                                solveLow : (sB2 + (sB1 + 2)) + (sA2 + t) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                                solveLow = solve 4 (λ b2 b1 a2 s →
                                              (b2 :+ (b1 :+ con 2)) :+ (a2 :+ s)
                                              := b2 :+ (b1 :+ (con 2 :+ (a2 :+ s)))) refl sB2 sB1 sA2 t
                    ... | tri≈ _ teq _ = dataEq (Nat.≤-reflexive (sym teq))
                                          (subst (Nat._< sA1 + 2) (sym teq) sA1<sA1+2)
                      where sA1<sA1+2 : sA1 Nat.< sA1 + 2
                            sA1<sA1+2 = Nat.≤-<-trans (Nat.≤-reflexive (sym (Nat.+-identityʳ sA1))) (Nat.+-monoʳ-< sA1 (Nat.s≤s Nat.z≤n))
                    ... | tri> _ _ tgt = highEq tgt
                      where
                        highEq : sA1 Nat.< t → Fin.toℕ (ΨLHS y) ≡ sB2 + (sB1 + (2 + (sA2 + t)))
                        highEq tg with Nat.<-cmp t (sA1 + 2)
                        ... | tri< tlt2 _ _ = dataEq (Nat.<⇒≤ tg) tlt2
                        ... | tri≈ _ teq2 _ = tailEq (Nat.≤-reflexive (sym teq2))
                        ... | tri> _ _ tgt2 = tailEq (Nat.<⇒≤ tgt2)
                midA1 : cA1t ⋯ Φ ≡ canonₛ A₁ (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sA2
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midA1 = fuseL ■ ⋯-cong c₁ ΨEq ■ fuseR
    ...   | inj₂ k =
                fuseΦ cA2t
              ■ midA2
              ■ sym rhsA2
              where
                flagIdx : 𝔽 (sA1 + (2 + n))
                flagIdx = weaken* ⦃ Kᵣ ⦄ sA1 1F
                cc₂big : UChan (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
                cc₂big = (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                cc₂ : UChan (sA1 + (2 + n))
                cc₂ = (K `unit , flagIdx , K `unit)
                c₂ = canonₛ A₂ cc₂ k
                cA2t = canonₛ A₂ cc₂big k
                rhsA2 : leafσ (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m))
                        ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) k
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                rhsA2 =
                    leafσ-tail (leafσ σ A₁ A₂) B₁ B₂ ((b1 + b2) ↑ʳ (z ↑ˡ m)) (z ↑ˡ m)
                      (Fin.splitAt-↑ʳ (b1 + b2) (a1 + a2 + m) (z ↑ˡ m))
                  ■ cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2)
                      (leafσ-B₁ σ A₁ A₂ (z ↑ˡ m) z k (Fin.splitAt-↑ˡ (a1 + a2) z m) eqi)
                assocIn : (sA1 + 2) + n ≡ sA1 + (2 + n)
                assocIn = Nat.+-assoc sA1 2 n
                assocOut : (sA1 + 2) + ((sB2 + (sB1 + 2)) + n) ≡ sA1 + (2 + (sB2 + (sB1 + (2 + n))))
                assocOut = Nat.+-assoc sA1 2 ((sB2 + (sB1 + 2)) + n)
                         ■ cong (sA1 +_) (cong (2 +_) (Nat.+-assoc sB2 (sB1 + 2) n ■ cong (sB2 +_) (Nat.+-assoc sB1 2 n)))
                ρ₂ : (sA1 + (2 + n)) →ᵣ (sA1 + (2 + (sB2 + (sB1 + (2 + n)))))
                ρ₂ = λ y → Fin.cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) y))
                flagN : Fin.toℕ flagIdx ≡ sA1 + 1
                flagN = toℕ-weaken*ᵣ sA1 1F
                ρ₂flag : ρ₂ flagIdx ≡ weaken* ⦃ Kᵣ ⦄ sA1 1F
                ρ₂flag = Fin.toℕ-injective
                  ( Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) flagIdx))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) flagIdx) flagLt
                  ■ castN
                  ■ sym (toℕ-weaken*ᵣ sA1 1F) )
                  where castN : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) ≡ sA1 + 1
                        castN = Fin.toℕ-cast (sym assocIn) flagIdx ■ flagN
                        flagLt : Fin.toℕ (Fin.cast (sym assocIn) flagIdx) Nat.< sA1 + 2
                        flagLt = subst (Nat._< sA1 + 2) (sym castN) (Nat.+-monoʳ-< sA1 (Nat.s≤s (Nat.s≤s Nat.z≤n)))
                mapcc2 : mapᶜ ρ₂ cc₂ ≡ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit)
                mapcc2 = cong₂ _,_ refl (cong₂ _,_ ρ₂flag refl)
                Λ₂ : (sA2 + (sA1 + (2 + n))) →ᵣ (sB2 + (sB1 + (2 + (sA2 + (sA1 + (2 + n))))))
                Λ₂ = (ρ₂ ↑* sA2) ·ₖ Φ
                fuseL : cA2t ⋯ Φ ≡ c₂ ⋯ Λ₂
                fuseL =
                    cong (_⋯ Φ)
                      (sym (canonₛ-nat A₂ cc₂ ρ₂ k ■ cong (λ c → canonₛ A₂ c k) mapcc2))
                  ■ fusion c₂ (ρ₂ ↑* sA2) Φ
                ρ₂N-low : ∀ (z′ : 𝔽 (sA1 + (2 + n))) → Fin.toℕ z′ Nat.< sA1 + 2 → Fin.toℕ (ρ₂ z′) ≡ Fin.toℕ z′
                ρ₂N-low z′ zlt =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) z′))
                  ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) z′)
                      (subst (Nat._< sA1 + 2) (sym (Fin.toℕ-cast (sym assocIn) z′)) zlt)
                  ■ Fin.toℕ-cast (sym assocIn) z′
                ρ₂N-high : ∀ (z′ : 𝔽 (sA1 + (2 + n))) → sA1 + 2 Nat.≤ Fin.toℕ z′ →
                           Fin.toℕ (ρ₂ z′) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + (Fin.toℕ z′ Nat.∸ (sA1 + 2))))
                ρ₂N-high z′ zge =
                    Fin.toℕ-cast assocOut ((weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2)) ↑* (sA1 + 2)) (Fin.cast (sym assocIn) z′))
                  ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ (sB2 + (sB1 + 2))) (sA1 + 2) (Fin.cast (sym assocIn) z′) zge'
                  ■ cong ((sA1 + 2) +_) (toℕ-weaken*ᵣ (sB2 + (sB1 + 2)) (Fin.reduce≥ (Fin.cast (sym assocIn) z′) zge')
                      ■ cong ((sB2 + (sB1 + 2)) +_) (toℕ-reduce≥ (Fin.cast (sym assocIn) z′) zge' ■ cong (Nat._∸ (sA1 + 2)) (Fin.toℕ-cast (sym assocIn) z′)))
                  ■ Nat.+-assoc sA1 2 ((sB2 + (sB1 + 2)) + (Fin.toℕ z′ Nat.∸ (sA1 + 2)))
                  where zge' : sA1 + 2 Nat.≤ Fin.toℕ (Fin.cast (sym assocIn) z′)
                        zge' = subst (sA1 + 2 Nat.≤_) (sym (Fin.toℕ-cast (sym assocIn) z′)) zge
                Λ₂Eq : Λ₂ ≗ ((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2)
                Λ₂Eq y = Fin.toℕ-injective (lhsN ■ sym rhsN)
                  where
                    t = Fin.toℕ y
                    v = (ρ₂ ↑* sA2) y
                    rhsN : Fin.toℕ (((weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) ·ₖ weaken* ⦃ Kᵣ ⦄ sB2) y)
                           ≡ sB2 + (sB1 + (2 + t))
                    rhsN = toℕ-weaken*ᵣ sB2 _ ■ cong (sB2 +_) (toℕ-weaken*ᵣ sB1 _ ■ cong (sB1 +_) (toℕ-weaken*ᵣ 2 y))
                    -- v fixes toℕ for the low region (t < sA2+(sA1+2)).
                    vlowGe : t Nat.< sA2 + (sA1 + 2) → sA2 Nat.≤ t → Fin.toℕ v ≡ t
                    vlowGe tlt tge = toℕ-↑*-ge ρ₂ sA2 y tge ■ cong (sA2 +_) (ρ₂N-low (Fin.reduce≥ y tge) redlt ■ redN) ■ Nat.m+[n∸m]≡n tge
                      where redN : Fin.toℕ (Fin.reduce≥ y tge) ≡ t Nat.∸ sA2
                            redN = toℕ-reduce≥ y tge
                            redlt : Fin.toℕ (Fin.reduce≥ y tge) Nat.< sA1 + 2
                            redlt = subst (Nat._< sA1 + 2) (sym redN)
                                      (Nat.+-cancelˡ-< sA2 (t Nat.∸ sA2) (sA1 + 2)
                                        (subst (Nat._< sA2 + (sA1 + 2)) (sym (Nat.m+[n∸m]≡n tge)) tlt))
                    vlow : t Nat.< sA2 + (sA1 + 2) → Fin.toℕ v ≡ t
                    vlow tlt with Nat.<-cmp t sA2
                    ... | tri< tlt1 _ _ = toℕ-↑*-lt ρ₂ sA2 y tlt1
                    ... | tri≈ _ teq1 _ = vlowGe tlt (Nat.≤-reflexive (sym teq1))
                    ... | tri> _ _ tgt1 = vlowGe tlt (Nat.<⇒≤ tgt1)
                    dataEq : sA2 + sA1 Nat.≤ t → t Nat.< sA2 + sA1 + 2 → Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    dataEq ge2 lt2 = Φ-toℕ-Adata v (subst (sA2 + sA1 Nat.≤_) (sym vN) ge2) (subst (Nat._< sA2 + sA1 + 2) (sym vN) lt2)
                                   ■ cong ((sB2 + (sB1 + 2)) +_) vN ■ solveD
                      where vN : Fin.toℕ v ≡ t
                            vN = vlow (Nat.<-≤-trans lt2 (Nat.≤-reflexive (Nat.+-assoc sA2 sA1 2)))
                            open +-*-Solver
                            solveD : (sB2 + (sB1 + 2)) + t ≡ sB2 + (sB1 + (2 + t))
                            solveD = solve 3 (λ b2 b1 s →
                                        (b2 :+ (b1 :+ con 2)) :+ s := b2 :+ (b1 :+ (con 2 :+ s))) refl sB2 sB1 t
                    tailEq : sA2 + sA1 + 2 Nat.≤ t → Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    tailEq ge2 = Φ-fix-ge v geΦ ■ vN ■ solveT
                      where
                        ge1 : sA2 + (sA1 + 2) Nat.≤ t
                        ge1 = subst (Nat._≤ t) (Nat.+-assoc sA2 sA1 2) ge2
                        dd = t Nat.∸ (sA2 + (sA1 + 2))
                        td : (sA2 + (sA1 + 2)) + dd ≡ t
                        td = Nat.m+[n∸m]≡n ge1
                        tge2 : sA2 Nat.≤ t
                        tge2 = Nat.≤-trans (Nat.m≤m+n sA2 (sA1 + 2)) ge1
                        red = Fin.reduce≥ y tge2
                        redN : Fin.toℕ red ≡ sA1 + 2 + dd
                        redN = toℕ-reduce≥ y tge2 ■ red2
                          where red2 : t Nat.∸ sA2 ≡ sA1 + 2 + dd
                                red2 = cong (Nat._∸ sA2) (sym td)
                                     ■ cong (Nat._∸ sA2) (Nat.+-assoc sA2 (sA1 + 2) dd)
                                     ■ Nat.m+n∸m≡n sA2 (sA1 + 2 + dd)
                        redge : sA1 + 2 Nat.≤ Fin.toℕ red
                        redge = subst (sA1 + 2 Nat.≤_) (sym redN) (Nat.m≤m+n (sA1 + 2) dd)
                        ρ₂redN : Fin.toℕ (ρ₂ red) ≡ sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))
                        ρ₂redN = ρ₂N-high red redge ■ cong (λ w → sA1 + (2 + ((sB2 + (sB1 + 2)) + w))) redd
                          where redd : Fin.toℕ red Nat.∸ (sA1 + 2) ≡ dd
                                redd = cong (Nat._∸ (sA1 + 2)) redN ■ Nat.m+n∸m≡n (sA1 + 2) dd
                        vN : Fin.toℕ v ≡ sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd)))
                        vN = toℕ-↑*-ge ρ₂ sA2 y tge2 ■ cong (sA2 +_) ρ₂redN
                        geΦ : sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤ Fin.toℕ v
                        geΦ = subst (sA2 + (sA1 + (2 + (sB2 + (sB1 + 2)))) Nat.≤_) (sym vN)
                                (Nat.+-monoʳ-≤ sA2 (Nat.+-monoʳ-≤ sA1 (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n (sB2 + (sB1 + 2)) dd))))
                        open +-*-Solver
                        solveT : sA2 + (sA1 + (2 + ((sB2 + (sB1 + 2)) + dd))) ≡ sB2 + (sB1 + (2 + t))
                        solveT = solve 5 (λ a2 a1 b2 b1 w →
                                    a2 :+ (a1 :+ (con 2 :+ ((b2 :+ (b1 :+ con 2)) :+ w)))
                                    := b2 :+ (b1 :+ (con 2 :+ ((a2 :+ (a1 :+ con 2)) :+ w)))) refl sA2 sA1 sB2 sB1 dd
                               ■ cong (λ w → sB2 + (sB1 + (2 + w))) td
                    lhsN : Fin.toℕ (Λ₂ y) ≡ sB2 + (sB1 + (2 + t))
                    lhsN with Nat.<-cmp t (sA2 + sA1)
                    ... | tri< tlt _ _ =
                            Φ-toℕ-A v (subst (Nat._< sA2 + sA1) (sym vN) tlt)
                          ■ cong ((sB2 + (sB1 + 2)) +_) vN
                          ■ solveLow
                      where vlt : t Nat.< sA2 + (sA1 + 2)
                            vlt = Nat.<-≤-trans tlt (Nat.+-monoʳ-≤ sA2 (Nat.m≤m+n sA1 2))
                            vN : Fin.toℕ v ≡ t
                            vN = vlow vlt
                            open +-*-Solver
                            solveLow : (sB2 + (sB1 + 2)) + t ≡ sB2 + (sB1 + (2 + t))
                            solveLow = solve 3 (λ b2 b1 s →
                                          (b2 :+ (b1 :+ con 2)) :+ s := b2 :+ (b1 :+ (con 2 :+ s))) refl sB2 sB1 t
                    ... | tri≈ _ teq _ = dataEq (Nat.≤-reflexive (sym teq)) (subst (Nat._< sA2 + sA1 + 2) (sym teq) data<)
                      where data< : sA2 + sA1 Nat.< sA2 + sA1 + 2
                            data< = Nat.≤-<-trans (Nat.≤-reflexive (sym (Nat.+-identityʳ (sA2 + sA1)))) (Nat.+-monoʳ-< (sA2 + sA1) (Nat.s≤s Nat.z≤n))
                    ... | tri> _ _ tgt with Nat.<-cmp t (sA2 + sA1 + 2)
                    ...   | tri< tlt2 _ _ = dataEq (Nat.<⇒≤ tgt) tlt2
                    ...   | tri≈ _ teq2 _ = tailEq (Nat.≤-reflexive (sym teq2))
                    ...   | tri> _ _ tgt2 = tailEq (Nat.<⇒≤ tgt2)
                midA2 : cA2t ⋯ Φ ≡ canonₛ A₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sA1 1F , K `unit) k
                          ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB1 ⋯ weaken* ⦃ Kᵣ ⦄ sB2
                midA2 =
                    fuseL
                  ■ ⋯-cong c₂ Λ₂Eq
                  ■ sym (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2 ·ₖ weaken* ⦃ Kᵣ ⦄ sB1) (weaken* ⦃ Kᵣ ⦄ sB2))
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB2) (sym (fusion c₂ (weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ sB1)))

U-ν-comm : (σ : m →ₛ n) {B₁ B₂ A₁ A₂ : BindGroup} {P : T.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + m))} →
           U[ T.ν B₁ B₂ (T.ν A₁ A₂ P) ] σ U.≋
           U[ T.ν A₁ A₂ (T.ν B₁ B₂ (P T.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))) ] σ
U-ν-comm {m = m} {n = n} σ {B₁} {B₂} {A₁} {A₂} {P} =
     ≡→≋ (Uν-flat σ B₁ B₂ (T.ν A₁ A₂ P))
  ◅◅ U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (Uν-flat (leafσ σ B₁ B₂) A₁ A₂ P))))
  ◅◅ U.ν-cong (Bφ-cong B₁ (Bφ-past-ν B₂ YA))
  ◅◅ U.ν-cong (Bφ-past-ν B₁ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2)))
  ◅◅ Eq*.return U.ν-comm′
  ◅◅ U.ν-cong (U.ν-cong (≡→≋ (Bφ-⋯ B₁ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2) U.⋯ₚ assocSwapᵣ 2 sB1) (assocSwapᵣ 2 2 {n}))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (≡→≋ (U.fusionₚ (Bφ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2)) (assocSwapᵣ 2 sB1) (assocSwapᵣ 2 2 {n} ↑* sB1)))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (≡→≋ (Bφ-⋯ B₂ (YA U.⋯ₚ assocSwapᵣ 2 sB2) (assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (U.fusionₚ YA (assocSwapᵣ 2 sB2) (ρ2 ↑* sB2))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ (Bφ-⋯ A₁ (Bφ A₂ LeafL) ρacc)))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong B₂ (Bφ-cong A₁ (≡→≋ (Bφ-⋯ A₂ LeafL (ρacc ↑* sA1)))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-transpose B₂ A₁ (Bφ A₂ LeafL'))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong A₁ (Bφ-cong B₂ (≡→≋ (Bφ-⋯ A₂ LeafL' (assocSwapᵣ sA1 sB2)))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong B₁ (Bφ-cong A₁ (Bφ-transpose B₂ A₂ (LeafL' U.⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-transpose B₁ A₁ (Bφ A₂ (Bφ B₂ W2))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong A₁ (Bφ-cong B₁ (≡→≋ (Bφ-⋯ A₂ (Bφ B₂ W2) (assocSwapᵣ sA1 sB1))))))
  ◅◅ U.ν-cong (U.ν-cong (Bφ-cong A₁ (Bφ-transpose B₁ A₂ (Bφ B₂ W2 U.⋯ₚ (assocSwapᵣ sA1 sB1 ↑* sA2)))))
  ◅◅ U.ν-cong (ν-past-Bφ A₁ _)
  ◅◅ U.ν-cong (Bφ-cong A₁ (U.ν-cong (≡→≋ (Bφ-⋯ A₂ _ (assocSwapᵣ sA1 2)))))
  ◅◅ U.ν-cong (Bφ-cong A₁ (ν-past-Bφ A₂ _))
  ◅◅ U.ν-cong (Bφ-cong A₁ (Bφ-cong A₂ (U.ν-cong bodyReconcile)))
  ◅◅ ≡→≋ (sym flatR)
  where
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sB1 = syncs B₁ ; sB2 = syncs B₂
    LeafL = U[ P ] (leafσ (leafσ σ B₁ B₂) A₁ A₂)
    YA = Bφ A₁ (Bφ A₂ LeafL)
    ρ2 = assocSwapᵣ 2 sB1 ·ₖ (assocSwapᵣ 2 2 {n} ↑* sB1)
    ρacc = assocSwapᵣ 2 sB2 ·ₖ (ρ2 ↑* sB2)
    LeafL' = LeafL U.⋯ₚ ((ρacc ↑* sA1) ↑* sA2)
    W2 = (LeafL' U.⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2)) U.⋯ₚ assocSwapᵣ sA2 sB2
    P′ = P T.⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)
    flatR : U[ T.ν A₁ A₂ (T.ν B₁ B₂ P′) ] σ
            ≡ U.ν (Bφ A₁ (Bφ A₂ (U.ν (Bφ B₁ (Bφ B₂ (U[ P′ ] (leafσ (leafσ σ A₁ A₂) B₁ B₂)))))))
    flatR = Uν-flat σ A₁ A₂ (T.ν B₁ B₂ P′)
          ■ cong U.ν (cong (Bφ A₁) (cong (Bφ A₂) (Uν-flat (leafσ σ A₁ A₂) B₁ B₂ P′)))
    Q₁ = assocSwapᵣ sA1 sB1 ↑* sA2
    Q₂ = assocSwapᵣ sA2 sB1
    Q₃ = assocSwapᵣ sA1 2 ↑* sA2
    Q₄ = assocSwapᵣ sA2 2
    Ω = (Q₁ ·ₖ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))) ↑* sB2
    leafEqComm : W2 U.⋯ₚ Ω ≡ U[ P′ ] (leafσ (leafσ σ A₁ A₂) B₁ B₂)
    leafEqComm =
        cong (U._⋯ₚ Ω) ( cong (U._⋯ₚ assocSwapᵣ sA2 sB2)
                           (cong (U._⋯ₚ (assocSwapᵣ sA1 sB2 ↑* sA2)) (local-U-σ⋯ P)
                            ■ local-U-σ⋯ P)
                       ■ local-U-σ⋯ P )
      ■ local-U-σ⋯ P
      ■ U-cong P (subEqComm-gen σ A₁ A₂ B₁ B₂)
      ■ sym (U-⋯ₚ P)
    bodyReconcile =
         ≡→≋ ( U.fusionₚ (Bφ B₁ ((Bφ B₂ W2 U.⋯ₚ Q₁) U.⋯ₚ Q₂)) Q₃ Q₄
             ■ Bφ-⋯ B₁ ((Bφ B₂ W2 U.⋯ₚ Q₁) U.⋯ₚ Q₂) (Q₃ ·ₖ Q₄)
             ■ cong (Bφ B₁) ( U.fusionₚ (Bφ B₂ W2 U.⋯ₚ Q₁) Q₂ ((Q₃ ·ₖ Q₄) ↑* sB1)
                            ■ U.fusionₚ (Bφ B₂ W2) Q₁ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))
                            ■ Bφ-⋯ B₂ W2 (Q₁ ·ₖ (Q₂ ·ₖ ((Q₃ ·ₖ Q₄) ↑* sB1))) ) )
      ◅◅ Bφ-cong B₁ (Bφ-cong B₂ (≡→≋ leafEqComm))

U-ν-ext : (σ : m →ₛ n) (P : T.Proc m) (B₁ B₂ : BindGroup) (Q : T.Proc (sum B₁ + sum B₂ + m)) →
          U[ P T.∥ T.ν B₁ B₂ Q ] σ U.≋
          U[ T.ν B₁ B₂ ((P T.⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) T.∥ Q) ] σ
U-ν-ext {m = m} {n = n} σ P B₁ B₂ Q =
  Eq*.return U.ν-ext′
  ◅◅ U.ν-cong
       ( UB-ext B₁ (K `unit , 0F , K `unit) (U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) _
       ◅◅ local-UB-≋ B₁ _ (λ τ₁ →
            UB-ext B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit)
              ((U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁)) _)
       ◅◅ local-UB-≋ B₁ _ (λ τ₁ → local-UB-≋ B₂ _ (λ τ₂ →
            ≡→≋ (cong (U._∥ U[ Q ] (σ′ τ₁ τ₂)) (step4eq τ₁ τ₂)))) )
  where
    wkK = weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)
    Bσ : m →ₛ syncs B₂ + (syncs B₁ + (2 + n))
    Bσ = λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
    σ′ : (sum B₁ →ₛ syncs B₁ + (2 + n)) → (sum B₂ →ₛ syncs B₂ + (syncs B₁ + (2 + n))) →
         (sum B₁ + sum B₂ + m →ₛ syncs B₂ + (syncs B₁ + (2 + n)))
    σ′ τ₁ τ₂ = ((λ i → τ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ τ₂) ++ₛ Bσ
    wkσ′≗Bσ : ∀ τ₁ τ₂ → wkK ·ₖ σ′ τ₁ τ₂ ≗ Bσ
    wkσ′≗Bσ τ₁ τ₂ i =
        cong (σ′ τ₁ τ₂) (weaken*~↑ʳ (sum B₁ + sum B₂) i)
      ■ cong [ _ , _ ]′ (splitAt-↑ʳ (sum B₁ + sum B₂) _ i)
    step4eq : ∀ τ₁ τ₂ →
              ((U[ P ] σ U.⋯ₚ weaken* ⦃ Kᵣ ⦄ 2) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁))
                U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)
              ≡ U[ P T.⋯ₚ wkK ] (σ′ τ₁ τ₂)
    step4eq τ₁ τ₂ =
        ( cong (λ z → z U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₁) U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (local-U-σ⋯ P)
        ■ cong (λ z → z U.⋯ₚ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (local-U-σ⋯ P)
        ■ local-U-σ⋯ P )
      ■ sym (U-⋯ₚ P ■ U-cong P (wkσ′≗Bσ τ₁ τ₂))

------------------------------------------------------------------------
-- the dispatcher
------------------------------------------------------------------------

U-≋′ : (σ : m →ₛ n) {P Q : T.Proc m} → P T.≋′ Q → U[ P ] σ U.≋ U[ Q ] σ
U-≋′ σ T.∥-comm′        = U.∥-comm
U-≋′ σ T.∥-assoc′       = U.∥-assoc
U-≋′ σ T.∥-unit′        = U.∥-unitˡ
U-≋′ σ (T.∥-cong′ x)    = U.∥-cong (U-≋′ σ x) ε
U-≋′ σ (T.ν-cong′ {B₁} {B₂} x) =
  Eq*.gmap U.ν U.ν-cong′ (local-UB-≋ B₁ _ (λ τ1 → local-UB-≋ B₂ _ (λ τ2 → U-≋′ _ x)))
U-≋′ σ (T.ν-swap′ {B₁} {B₂} {P}) = U-ν-swap σ {B₁} {B₂} {P}
U-≋′ σ (T.ν-comm′ {B₁} {B₂} {A₁} {A₂} {P}) = U-ν-comm σ {B₁} {B₂} {A₁} {A₂} {P}
U-≋′ σ (T.ν-ext′ {P} {B₁} {B₂} {Q}) = U-ν-ext σ P B₁ B₂ Q

U-≋ : (σ : m →ₛ n) {P Q : T.Proc m} → P T.≋ Q → U[ P ] σ U.≋ U[ Q ] σ
U-≋ σ = kleisliStar (λ P → U[ P ] σ)
          λ { (fwd s) → U-≋′ σ s ; (bwd s) → Eq*.symmetric _ (U-≋′ σ s) }
