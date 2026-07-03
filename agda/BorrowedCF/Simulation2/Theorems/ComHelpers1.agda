module BorrowedCF.Simulation2.Theorems.ComHelpers1 where

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

import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Context.Base using (_⸴*_; _⸴_)
open T using (inv-∥; inv-ν; inv-⟪⟫; BindCtx; BindCtx′; bindCtx⇒chanCtx)
open import BorrowedCF.Reduction.Base using (ChanCx)
open import BorrowedCF.Simulation2.InvFrame using (inv-app; inv-pair; arg-type; strengthen-frame)
open import BorrowedCF.Types using (Bounded; ≃-bounded; Skips; skips⊥bounded)
open import BorrowedCF.Context.Join using (biasedDir)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Simulation2.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation2.TranslationProperties using (VChan; chanTriple-V; Value-subst)

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

-- syncs ignores the head count: needed to bridge the LHS (suc-headed) and RHS
-- (decremented) bind groups, whose syncs are equal but stuck on B's shape.
syncs-cons-irrel : (h₁ h₂ : ℕ) (B : BindGroup) → syncs (h₁ ∷ B) ≡ syncs (h₂ ∷ B)
syncs-cons-irrel h₁ h₂ []        = refl
syncs-cons-irrel h₁ h₂ (_ ∷ _)   = refl

-- Two suc-headed bind groups (ϕ[suc _] = drop) with the same tail produce the
-- same φ-prefix, modulo the syncs head-irrelevance transport on the leaf.
Bφ-suc-head≡ : ∀ {n} (a c : ℕ) (B : BindGroup)
             → (X : U.Proc (syncs (suc a ∷ B) + n))
             → Bφ {n} (suc a ∷ B) X
               ≡ Bφ {n} (suc c ∷ B) (subst (λ z → U.Proc (z + n)) (syncs-cons-irrel (suc a) (suc c) B) X)
Bφ-suc-head≡ a c []        X = refl
Bφ-suc-head≡ a c (d ∷ B)   X = refl

-- the canonical leaf substitution fed to f by UB[ B ]
canonₛ : ∀ {n} (B : BindGroup) → UChan n → (sum B →ₛ syncs B + n)
canonₛ []            cc = λ ()
canonₛ (b ∷ [])      cc = Ub[ b + 0 ] cc
canonₛ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)
           , canonₛ B (` 0F , suc x , wk e2) ]′ (Fin.splitAt b y))

-- prepending one slot to a *-headed data block (Ub[_] on the unit triple) does
-- not change the value at a shifted index.
Ub-suc-shift : ∀ {N} (m : ℕ) (x : 𝔽 N) (e2 : Tm N) (j : 𝔽 m) →
               Ub[ suc m ] (* , x , e2) (Fin.suc j) ≡ Ub[ m ] (* , x , e2) j
Ub-suc-shift zero    x e2 ()
Ub-suc-shift (suc m) x e2 j = refl

-- head-count insertion: prepending one slot to the head block of canonₛ (whose
-- head-block value is constant) does not change the value at a shifted index.
canonₛ-suc-shift : ∀ {N} (b : ℕ) (B : BindGroup) (x : 𝔽 N) (e2 : Tm N) (j : 𝔽 (b + sum B)) →
                   canonₛ (suc b ∷ B) (K `unit , x , e2) (Fin.suc j)
                   ≡ subst (λ z → Tm (z + N)) (syncs-cons-irrel b (suc b) B) (canonₛ (b ∷ B) (K `unit , x , e2) j)
canonₛ-suc-shift b []          x e2 j = Ub-suc-shift (b + 0) x e2 j
canonₛ-suc-shift {N} b (d ∷ B) x e2 j
  with Fin.splitAt b j
... | inj₁ j′ = cong (λ t → subst Tm (+-suc (syncs (d ∷ B)) N) (t ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (d ∷ B))))
                     (Ub-suc-shift b (suc x) (` 0F) j′)
... | inj₂ _  = refl

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

  chReqᵍ : ∀ {a bb} (b : ℕ) sB (e1 : Tm a) (x : 𝔽 a) (ρ : a →ᵣ bb) (j : 𝔽 b) →
           ((Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j) ⋯ ((ρ ↑) ↑* sB)
           ≡ (Ub[ b ] (wk (e1 ⋯ ρ) , suc (ρ x) , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j
  chReqᵍ b sB e1 x ρ j =
      sym (⋯-↑*-wk (Ub[ b ] (wk e1 , suc x , ` 0F) j) (ρ ↑) sB)
    ■ cong (_⋯ᵣ weaken* ⦃ Kᵣ ⦄ sB) (Ub-nat b (wk e1 , suc x , ` 0F) (ρ ↑) j)
    ■ cong (λ cc → Ub[ b ] cc j ⋯ᵣ weaken* ⦃ Kᵣ ⦄ sB) ccUbEq
    where
      ccUbEq : mapᶜ (ρ ↑) (wk e1 , suc x , ` 0F) ≡ (wk (e1 ⋯ ρ) , suc (ρ x) , ` 0F)
      ccUbEq = cong₂ _,_ (sym (⋯-↑-wk e1 ρ)) refl

-- canonₛ is natural in its channel triple under target renamings.
canonₛ-nat : ∀ {a bb} (B : BindGroup) (cc : UChan a) (ρ : a →ᵣ bb) (i : 𝔽 (sum B)) →
             canonₛ B cc i ⋯ (ρ ↑* syncs B) ≡ canonₛ B (mapᶜ ρ cc) i
canonₛ-nat []            cc ρ ()
canonₛ-nat (b ∷ [])      (e1 , x , e2) ρ i = Ub-nat (b + 0) (e1 , x , e2) ρ i
canonₛ-nat {a} {bb} (b ∷ B@(_ ∷ _)) (e1 , x , e2) ρ i
  with Fin.splitAt b i | canonₛ-nat B (` 0F , suc x , wk e2) (ρ ↑)
... | inj₁ j | _  = ΘrelEqᵍ (syncs B) ρ ((Ub[ b ] (wk e1 , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)) j)
                  ■ cong (subst Tm (+-suc (syncs B) bb)) (chReqᵍ b (syncs B) e1 x ρ j)
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
