module BorrowedCF.Simulation2.Theorems.Com where

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

------------------------------------------------------------------------
-- Typing crux: a msg/brn-headed borrow is never the terminal ret, so the
-- head count is >= 2, i.e. b1 >= 1 (dually b2 >= 1).
------------------------------------------------------------------------

msg-not-Bounded : ∀ {p TT} → ¬ Bounded (msg {0} p TT)
msg-not-Bounded ()

fn-send-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `send ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ∃[ Tᵐ ] (Tᵐ ⊗¹ ⟨ msg ‼ Tᵐ ⟩) ≃ Tᵈ
fn-send-dom (T-Const (`send {T = Tᵐ} _)) = Tᵐ , ≃-refl
fn-send-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let Tᵐ , eq = fn-send-dom d in Tᵐ , ≃-trans eq dom≃
fn-send-dom (T-Weaken _ d) = fn-send-dom d

fn-recv-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `recv ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ∃[ Tᵐ ] ⟨ msg ⁇ Tᵐ ⟩ ≃ Tᵈ
fn-recv-dom (T-Const (`recv {T = Tᵐ} _)) = Tᵐ , ≃-refl
fn-recv-dom (T-Conv (dom≃ `→ cod≃) _ d) =
  let Tᵐ , eq = fn-recv-dom d in Tᵐ , ≃-trans eq dom≃
fn-recv-dom (T-Weaken _ d) = fn-recv-dom d

pair1-handle : ∀ {N} {Γ : Ctx N} {β : Struct N} {ee}{x : 𝔽 N}{T ϵ}
  → Γ ; β ⊢ ((` x) ⊗ ee) ∶ T ∣ ϵ
  → ∃[ Tx ] ∃[ d ] ∃[ Te ] (T ≃ (Tx ⊗⟨ d ⟩ Te)) × (Γ x ≃ Tx)
pair1-handle (T-Pair {T = Tx} {U = Te} p/s _ ⊢x ⊢e) =
  Tx , biasedDir p/s , Te , ≃-refl , arg-type ⊢x
pair1-handle (T-Conv T≃ _ d) =
  let Tx , dd , Te , Teq , Heq = pair1-handle d in
  Tx , dd , Te , ≃-trans (≃-sym T≃) Teq , Heq
pair1-handle (T-Weaken _ d) = pair1-handle d

⊗≃₁ : ∀ {Ta Ua Tb Ub d} → (Ta ⊗⟨ d ⟩ Ua) ≃ (Tb ⊗⟨ d ⟩ Ub) → Ta ≃ Tb
⊗≃₁ (eq ⊗ _) = eq

⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
⟨⟩≃ ⟨ eq ⟩ = eq

-- Invert Bounded of a sequencing whose right component Skips: the left is Bounded.
bounded-seqL : ∀ {sa sb : 𝕊 0} → Bounded (sa ; sb) → Skips sb → Bounded sa
bounded-seqL (b ;₁ _) _   = b
bounded-seqL (-;₂ b)  Sk  = ⊥-elim (skips⊥bounded Sk b)

bd-end : ∀ {n}{s : 𝕊 n}{p} → Bounded (s ; end p)
bd-end = -;₂ end

open T using (last; cons-ret/acq; cons-acq; nil; cons)

-- Off-by-one for the new (chain-aware) BindCtx: a Bounded session whose bind group
-- has head (suc b₁) and count 1 (b₁=0) forces the head channel 0F to a Bounded session.
head-bounded : ∀ {s b₁}{B₁ : BindGroup}{Γ₁ : Ctx (sum (suc b₁ ∷ B₁))}
  → Bounded s
  → BindCtx s (suc b₁ ∷ B₁) Γ₁ → b₁ ≡ 0
  → ∃[ s'' ] (Γ₁ 0F ≡ ⟨ s'' ⟩) × Bounded s''
head-bounded Bs (last (cons {s₁ = s₁ˡ} {s₂ = s₂ˡ} ¬sk s≃ˡ Γ≗ˡ (nil Skˡ))) refl =
  s₁ˡ , sym (Γ≗ˡ 0F)
  , bounded-seqL (≃-bounded (≃-sym s≃ˡ) Bs) Skˡ
head-bounded Bs (cons-ret/acq {s₁ = sh} {s₂ = st} s≃ Γ≗
                  (cons {s₁ = s₁''} {s₂ = s₂''} ¬sk s≃' Γ≗' (nil Sk)) rest) refl =
  s₁'' , (sym (Γ≗ 0F) ■ sym (Γ≗' 0F))
  , bounded-seqL (≃-bounded (≃-sym s≃') (-;₂ ret)) Sk

-- recv handle (bare variable y): Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩.
recv-handle-≃msg : ∀ {N} {Δ : Ctx N}{α β}{y : 𝔽 N}{a Targ U ϵ₁ ϵ₂}
  → Δ ; α ⊢ K `recv ∶ Targ ⟨ a ⟩→ U ∣ ϵ₁
  → Δ ; β ⊢ (` y) ∶ Targ ∣ ϵ₂
  → ∃[ Tᵐ ] (Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩)
recv-handle-≃msg {y = y} ⊢fn ⊢arg
  with fn-recv-dom ⊢fn
... | Tᵐ , dom≃ = Tᵐ , ≃-trans (arg-type ⊢arg) (≃-sym dom≃)

recv-handle-≃msg-app : ∀ {N} {Δ : Ctx N}{β}{y : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `recv · (` y) ∶ U ∣ ϵ
  → ∃[ Tᵐ ] (Δ y ≃ ⟨ msg ⁇ Tᵐ ⟩)
recv-handle-≃msg-app (T-AppUnr   _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-AppLin   _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-AppLeft  _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-AppRight _ _ ⊢fn ⊢arg) = recv-handle-≃msg ⊢fn ⊢arg
recv-handle-≃msg-app (T-Conv _ _ d) = recv-handle-≃msg-app d
recv-handle-≃msg-app (T-Weaken _ d) = recv-handle-≃msg-app d

open T using (_;_⊢ₚ_)

-- Symmetric crux for the recv side: b₂ ≥ 1.
com-head≥2 : ∀ {m} {Γ : Ctx m} {γ}{b₁ b₂}{B₁ B₂ : BindGroup}{e}{E₁ E₂}{P}(V : Value e) →
    Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((T.⟪ E₁ ⋯ᶠ* TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `send · ((e ⋯ TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) ⊗ (` 0F)) ]* ⟫
        T.∥ T.⟪ E₂ ⋯ᶠ* TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `recv · (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        T.∥ (P T.⋯ₚ TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)))
      → ∃[ b₂' ] (b₂ ≡ suc b₂')
com-head≥2 {b₂ = suc b₂'} V ⊢P = b₂' , refl
com-head≥2 {m = m} {b₁ = b₁} {b₂ = zero} {B₁ = B₁} {B₂ = B₂} {E₂ = E₂} V ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , s , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢sr , _
  with inv-∥ ⊢sr
... | _ , _ , _ , _ , ⊢recvT
  with strengthen-frame (E₂ ⋯ᶠ* TR.wkₚ (b₁ + sum B₁) (zero + sum B₂)) (inv-⟪⟫ ⊢recvT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-bounded bd-end C′ refl
... | s'' , Δ0≡ , Bs''
  with recv-handle-≃msg-app ⊢plug
... | Tᵐ , Δr≃msg = ⊥-elim (msg-not-Bounded (≃-bounded (⟨⟩≃ (≃-trans (≃-reflexive (sym Δr≡)) Δr≃msg)) Bs''))
  where
    Δr≡ : ((Γ₁ ⸴* Γ₂) ⸴* _) (wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ≡ ⟨ s'' ⟩
    Δr≡ =
        cong [ Γ₁ ⸴* Γ₂ , _ ]′ (Fin.splitAt-↑ˡ (sum (suc b₁ ∷ B₁) + sum (suc zero ∷ B₂)) (sum (suc b₁ ∷ B₁) ↑ʳ 0F) m)
      ■ cong [ Γ₁ , Γ₂ ]′ (Fin.splitAt-↑ʳ (sum (suc b₁ ∷ B₁)) (sum (suc zero ∷ B₂)) 0F)
      ■ Δ0≡

------------------------------------------------------------------------
-- Send-side crux: b₁ ≥ 1.  The send handle 0F is msg-typed (non-ret), so when
-- b₁ = 0 the head chain forces a Bounded session at 0F — contradiction.
------------------------------------------------------------------------

⊗≃₂ : ∀ {Ta Ua Tb Ub d} → (Ta ⊗⟨ d ⟩ Ua) ≃ (Tb ⊗⟨ d ⟩ Ub) → Ua ≃ Ub
⊗≃₂ (_ ⊗ eq) = eq

pair₂-handle : ∀ {N} {Γ : Ctx N} {β : Struct N} {ee}{x : 𝔽 N}{T ϵ}
  → Γ ; β ⊢ (ee ⊗ (` x)) ∶ T ∣ ϵ
  → ∃[ Te ] ∃[ d ] ∃[ Tx ] (T ≃ (Te ⊗⟨ d ⟩ Tx)) × (Γ x ≃ Tx)
pair₂-handle (T-Pair {T = Te} {U = Tx} p/s _ ⊢e ⊢x) =
  Te , biasedDir p/s , Tx , ≃-refl , arg-type ⊢x
pair₂-handle (T-Conv T≃ _ d) =
  let Te , dd , Tx , Teq , Heq = pair₂-handle d in
  Te , dd , Tx , ≃-trans (≃-sym T≃) Teq , Heq
pair₂-handle (T-Weaken _ d) = pair₂-handle d

-- send handle (second component of the message pair): Δ x ≃ ⟨ msg ‼ Tᵐ ⟩.
send-handle-≃msg : ∀ {N} {Δ : Ctx N}{α β}{ee}{x : 𝔽 N}{a Targ U ϵ₁ ϵ₂}
  → Δ ; α ⊢ K `send ∶ Targ ⟨ a ⟩→ U ∣ ϵ₁
  → Δ ; β ⊢ (ee ⊗ (` x)) ∶ Targ ∣ ϵ₂
  → ∃[ Tᵐ ] (Δ x ≃ ⟨ msg ‼ Tᵐ ⟩)
send-handle-≃msg ⊢fn ⊢arg
  with fn-send-dom ⊢fn | pair₂-handle ⊢arg
... | Tᵐ , dom≃ | Te , d , Tx , T≃ , Hx≃
  with ≃-trans (≃-sym T≃) (≃-sym dom≃)
... | (_ ⊗ eq) = Tᵐ , ≃-trans Hx≃ eq

send-handle-≃msg-app : ∀ {N} {Δ : Ctx N}{β}{ee}{x : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `send · (ee ⊗ (` x)) ∶ U ∣ ϵ
  → ∃[ Tᵐ ] (Δ x ≃ ⟨ msg ‼ Tᵐ ⟩)
send-handle-≃msg-app (T-AppUnr   _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-AppLin   _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-AppLeft  _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-AppRight _ _ ⊢fn ⊢arg) = send-handle-≃msg ⊢fn ⊢arg
send-handle-≃msg-app (T-Conv _ _ d) = send-handle-≃msg-app d
send-handle-≃msg-app (T-Weaken _ d) = send-handle-≃msg-app d

msg‼-not-Bounded : ∀ {p TT} → ¬ Bounded (msg {0} p TT)
msg‼-not-Bounded ()

com-head≥1 : ∀ {m} {Γ : Ctx m} {γ}{b₁ b₂}{B₁ B₂ : BindGroup}{e}{E₁ E₂}{P}(V : Value e) →
    Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
      ((T.⟪ E₁ ⋯ᶠ* TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `send · ((e ⋯ TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)) ⊗ (` 0F)) ]* ⟫
        T.∥ T.⟪ E₂ ⋯ᶠ* TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) [ K `recv · (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
        T.∥ (P T.⋯ₚ TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)))
      → ∃[ b₁' ] (b₁ ≡ suc b₁')
com-head≥1 {b₁ = suc b₁'} V ⊢P = b₁' , refl
com-head≥1 {m = m} {b₁ = zero} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} V ⊢P
  with inv-ν ⊢P
... | Γ₁ , Γ₂ , s , N , ⊢B₁ , ⊢B₂ , C , C′ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢sr , _
  with inv-∥ ⊢sr
... | _ , _ , _ , ⊢sendT , _
  with strengthen-frame (E₁ ⋯ᶠ* TR.wkₚ (zero + sum B₁) (b₂ + sum B₂)) (inv-⟪⟫ ⊢sendT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-bounded bd-end C refl
... | s'' , Δ0≡ , Bs''
  with send-handle-≃msg-app ⊢plug
... | Tᵐ , Δs≃msg = ⊥-elim (msg‼-not-Bounded (≃-bounded (⟨⟩≃ (≃-trans (≃-reflexive (sym Δ0≡)) Δs≃msg)) Bs''))

------------------------------------------------------------------------
-- Ported helpers (verbatim from Theorems/Choice) for the U-com assembly.
------------------------------------------------------------------------

infix 4 _UR─→ₚ*_
_UR─→ₚ*_ : {n : ℕ} → U.Proc n → U.Proc n → Set
_UR─→ₚ*_ = Star UR._─→ₚ_

wrapNE : {n : ℕ} {w x y′ z : U.Proc n} → w U.≋ x →
         {s₀tgt : U.Proc n} → x UR.─→ₚ s₀tgt → s₀tgt UR─→ₚ* y′ → y′ U.≋ z →
         w UR─→ₚ* z
wrapNE front s₀ ε        back = UR.RU-Struct front s₀ back ◅ ε
wrapNE front s₀ (t ◅ ts) back = UR.RU-Struct front s₀ ε ◅ wrapNE ε t ts back

≋-wrap-⊎ : {n : ℕ} {w x y z : U.Proc n} → w U.≋ x → x UR─→ₚ* y → y U.≋ z →
           (w UR─→ₚ* z) ⊎ (w U.≋ z)
≋-wrap-⊎ front ε        back = inj₂ (front ◅◅ back)
≋-wrap-⊎ front (s ◅ ss) back = inj₁ (wrapNE front s ss back)

Bφ-lift-step : (B : BindGroup) {n : ℕ} {P Q : U.Proc (syncs B + n)} →
               P UR.─→ₚ Q → Bφ {n} B P UR.─→ₚ Bφ B Q
Bφ-lift-step []            r = r
Bφ-lift-step (b ∷ [])      r = r
Bφ-lift-step (b ∷ B@(_ ∷ _)) {n} r =
  UR.RU-Sync (Bφ-lift-step B (subst-→ₚ (sym (+-suc (syncs B) n)) r))
  where
    subst-→ₚ : ∀ {a c} (eq : a ≡ c) {P Q : U.Proc a} → P UR.─→ₚ Q →
               subst U.Proc eq P UR.─→ₚ subst U.Proc eq Q
    subst-→ₚ refl r = r

VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ j → Ub-V (b + 0) e1 x e2 Ve1 Ve2 j
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ j → value-⋯ (Ub-V b (wk e1) (suc x) (` 0F) (Ve1 ⋯ᵛ weakenᵣ) V-` j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

canonₛ-head-triple : ∀ {N} (b : ℕ) (B : BindGroup) (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs (suc b ∷ B) + N) ] Σ[ c ∈ Tm (syncs (suc b ∷ B) + N) ]
  Σ[ j ∈ 𝔽 (syncs (suc b ∷ B) + N) ]
    (canonₛ (suc b ∷ B) (e1 , x , e2) 0F ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (suc b ∷ B) + Fin.toℕ x)
canonₛ-head-triple zero    []  e1 e2 x =
  e1 , e2 , x , refl , refl
canonₛ-head-triple (suc b) []  e1 e2 x =
  e1 , * , x , refl , refl
canonₛ-head-triple {N} zero (c′ ∷ B) e1 e2 x =
  ( subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq
  , junceq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc zero ∷ c′ ∷ B) (e1 , x , e2) 0F
             ≡ (subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)))
             ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl
canonₛ-head-triple {N} (suc b) (c′ ∷ B) e1 e2 x =
  ( subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq
  , junceq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc (suc b) ∷ c′ ∷ B) (e1 , x , e2) 0F
             ≡ (subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)))
             ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
           ■ toℕ-weaken*ᵣ sB (suc x)
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl

assocPush-junc : ∀ (sA sB d : ℕ) {nn} (j : 𝔽 (sB + (sA + (2 + nn)))) →
                 Fin.toℕ j ≡ sB + (sA + d) → d Nat.< 2 →
                 Fin.toℕ ((assocSwapᵣ sB 2 {sA + nn}) ((assocSwapᵣ sA 2 {nn} ↑* sB) j)) ≡ d
assocPush-junc sA sB d {nn} j jeq d<2 =
    toℕ-assoc-mid sB 2 {sA + nn} ((assocSwapᵣ sA 2 {nn} ↑* sB) j) geB ltB
  ■ aritheq
  where
    q1 : sB Nat.≤ Fin.toℕ j
    q1 = subst (sB Nat.≤_) (sym jeq) (Nat.m≤m+n sB (sA + d))
    redeq : Fin.toℕ (Fin.reduce≥ j q1) ≡ sA + d
    redeq = toℕ-reduce≥ j q1 ■ cong (Nat._∸ sB) jeq ■ Nat.m+n∸m≡n sB (sA + d)
    geA : sA Nat.≤ Fin.toℕ (Fin.reduce≥ j q1)
    geA = subst (sA Nat.≤_) (sym redeq) (Nat.m≤m+n sA d)
    ltA : Fin.toℕ (Fin.reduce≥ j q1) Nat.< sA + 2
    ltA = subst (Nat._< sA + 2) (sym redeq) (Nat.+-monoʳ-< sA d<2)
    midA : Fin.toℕ (assocSwapᵣ sA 2 {nn} (Fin.reduce≥ j q1)) ≡ d
    midA = toℕ-assoc-mid sA 2 {nn} (Fin.reduce≥ j q1) geA ltA
         ■ cong (Nat._∸ sA) redeq ■ Nat.m+n∸m≡n sA d
    step1 : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) ≡ sB + d
    step1 = toℕ-↑*-ge (assocSwapᵣ sA 2 {nn}) sB j q1 ■ cong (sB +_) midA
    geB : sB Nat.≤ Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j)
    geB = subst (sB Nat.≤_) (sym step1) (Nat.m≤m+n sB d)
    ltB : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) Nat.< sB + 2
    ltB = subst (Nat._< sB + 2) (sym step1) (Nat.+-monoʳ-< sB d<2)
    aritheq : Fin.toℕ ((assocSwapᵣ sA 2 {nn} ↑* sB) j) Nat.∸ sB ≡ d
    aritheq = cong (Nat._∸ sB) step1 ■ Nat.m+n∸m≡n sB d

frame-plug*ᵣ : (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

------------------------------------------------------------------------
-- The exported forward-simulation case R-Com.
------------------------------------------------------------------------

U-com : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
  → {E₁ E₂ : Frame* (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {P : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → {e : Tm (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)}
  → (V : Value e)
  → (let wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
       ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send · ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
         T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv · (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
         T.∥ (P T.⋯ₚ wkρ)))
  → (let wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂) in
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send · ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv · (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
                T.∥ (P T.⋯ₚ wkρ)) ] σ
       UR─→ₚ*
      U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ)
     ⊎
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ ⋯ᶠ* wkρ [ K `send · ((e ⋯ wkρ) ⊗ (` 0F)) ]* ⟫
                T.∥ T.⟪ E₂ ⋯ᶠ* wkρ [ K `recv · (` wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)) ]* ⟫)
                T.∥ (P T.⋯ₚ wkρ)) ] σ
       U.≋
      U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ))
U-com {m} {n} σ Vσ Γ-S {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {E₁ = E₁} {E₂ = E₂} {P = P} {e = e} V ⊢P
  with com-head≥1 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = e} {E₁ = E₁} {E₂ = E₂} {P = P} V ⊢P
     | com-head≥2 {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {e = e} {E₁ = E₁} {E₂ = E₂} {P = P} V ⊢P
... | b₁' , refl | b₂' , refl =
  ≋-wrap-⊎ front fire back
  where
    wkρ : (b₁ + sum B₁) + (b₂ + sum B₂) + m →ᵣ sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m
    wkρ = TR.wkₚ (b₁ + sum B₁) (b₂ + sum B₂)
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂
    yv : 𝔽 (sum B₁′ + sum B₂′ + m)
    yv = wkʳ m (wkˡ ⦃ Kᵣ ⦄ (suc b₁ + sum B₁) 0F)
    EE₁ EE₂ : Frame* (sum B₁′ + sum B₂′ + m)
    EE₁ = E₁ ⋯ᶠ* wkρ
    EE₂ = E₂ ⋯ᶠ* wkρ
    ee : Tm (sum B₁′ + sum B₂′ + m)
    ee = e ⋯ wkρ
    PP : T.Proc (sum B₁′ + sum B₂′ + m)
    PP = P T.⋯ₚ wkρ
    QL : T.Proc (sum B₁′ + sum B₂′ + m)
    QL = (T.⟪ EE₁ [ K `send · (ee ⊗ (` 0F)) ]* ⟫ T.∥ T.⟪ EE₂ [ K `recv · (` yv) ]* ⟫) T.∥ PP
    τ : sum B₁′ + sum B₂′ + m →ₛ syncs B₂′ + (syncs B₁′ + (2 + n))
    τ = leafσ σ B₁′ B₂′
    XL : U.Proc (syncs B₂′ + (syncs B₁′ + (2 + n)))
    XL = U[ QL ] τ
    sA sB : ℕ
    sA = syncs B₁′
    sB = syncs B₂′
    push : ∀ {k} → U.Proc (sB + (sA + (2 + k))) → U.Proc (2 + (sB + (sA + k)))
    push {k} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    YL : U.Proc (2 + (sB + (sA + n)))
    YL = push XL
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ B₁′ (Bφ B₂′ X)) U.≋ Bφ B₁′ (Bφ B₂′ (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ B₁′ (Bφ B₂′ X)
      ◅◅ Bφ-cong B₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B₂′ X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong B₁′ (ν-past-Bφ B₂′ (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν B₁′ B₂′ QL ] σ U.≋ Bφ B₁′ (Bφ B₂′ (U.ν YL))
    front = ≡→≋ (Uν-flat σ B₁′ B₂′ QL) ◅◅ ν↓ XL
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ B₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    τyv≡ : τ yv ≡ canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) 0F
    τyv≡ = cong [ _ , _ ]′ split-outer ■ cong [ _ , _ ]′ split-inner
      where
        z0 : 𝔽 (sum B₂′)
        z0 = 0F
        split-outer : Fin.splitAt (sum B₁′ + sum B₂′) yv ≡ inj₁ (sum B₁′ ↑ʳ z0)
        split-outer = Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) (sum B₁′ ↑ʳ z0) m
        split-inner : Fin.splitAt (sum B₁′) (sum B₁′ ↑ʳ z0) ≡ inj₂ z0
        split-inner = Fin.splitAt-↑ʳ (sum B₁′) (sum B₂′) z0
    tr₀ : Σ[ a ∈ Tm (syncs B₁′ + (2 + n)) ] Σ[ c ∈ Tm (syncs B₁′ + (2 + n)) ]
          Σ[ j ∈ 𝔽 (syncs B₁′ + (2 + n)) ]
            (canonₛ B₁′ (K `unit , 0F , K `unit) 0F ≡ (a ⊗ (` j)) ⊗ c)
            × (Fin.toℕ j ≡ syncs B₁′ + Fin.toℕ (Fin.zero {n = 1 + n}))
    tr₀ = canonₛ-head-triple b₁ B₁ (K `unit) (K `unit) 0F
    tr₁ : Σ[ a ∈ Tm (syncs B₂′ + (sA + (2 + n))) ] Σ[ c ∈ Tm (syncs B₂′ + (sA + (2 + n))) ]
          Σ[ j ∈ 𝔽 (syncs B₂′ + (sA + (2 + n))) ]
            (canonₛ B₂′ (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) 0F ≡ (a ⊗ (` j)) ⊗ c)
            × (Fin.toℕ j ≡ syncs B₂′ + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sA (Fin.suc (Fin.zero {n = n}))))
    tr₁ = canonₛ-head-triple b₂ B₂ (K `unit) (K `unit) (weaken* ⦃ Kᵣ ⦄ sA 1F)
    tA0 tB0 tA1 tB1 : Tm (2 + (sB + (sA + n)))
    tA0 = rn (proj₁ tr₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tB0 = rn (proj₁ (proj₂ tr₀) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tA1 = rn (proj₁ tr₁)
    tB1 = rn (proj₁ (proj₂ tr₁))
    cc₀ cc₁ : Tm (2 + (sB + (sA + n)))
    cc₀ = (tA0 ⊗ (` 0F)) ⊗ tB0
    cc₁ = (tA1 ⊗ (` 1F)) ⊗ tB1
    rn-trip : (a c : Tm (sB + (sA + (2 + n)))) (j : 𝔽 (sB + (sA + (2 + n)))) →
              rn ((a ⊗ (` j)) ⊗ c) ≡ (rn a ⊗ (` (assocSwapᵣ sB 2 ((assocSwapᵣ sA 2 ↑* sB) j)))) ⊗ rn c
    rn-trip a c j = refl
    cc₀-eq : rn (τ 0F) ≡ cc₀
    cc₀-eq =
          cong rn (cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ tr₀)))))
        ■ rn-trip (proj₁ tr₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ tr₀) ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀))))
        ■ cong (λ z → (tA0 ⊗ (` z)) ⊗ tB0)
            (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ tr₀)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ tr₀))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ tr₀))))
    cc₁-eq : rn (τ yv) ≡ cc₁
    cc₁-eq =
          cong rn (τyv≡ ■ proj₁ (proj₂ (proj₂ (proj₂ tr₁))))
        ■ rn-trip (proj₁ tr₁) (proj₁ (proj₂ tr₁)) (proj₁ (proj₂ (proj₂ tr₁)))
        ■ cong (λ z → (tA1 ⊗ (` z)) ⊗ tB1)
            (Fin.toℕ-injective (assocPush-junc sA sB 1 (proj₁ (proj₂ (proj₂ tr₁))) jvtoℕ (Nat.s≤s (Nat.s≤s Nat.z≤n))))
      where
        jvtoℕ : Fin.toℕ (proj₁ (proj₂ (proj₂ tr₁))) ≡ sB + (sA + 1)
        jvtoℕ = proj₂ (proj₂ (proj₂ (proj₂ tr₁))) ■ cong (sB +_) (toℕ-weaken*ᵣ sA 1F)
    F₁ F₂ : Frame* (2 + (sB + (sA + n)))
    F₁ = (frame*-⋯ EE₁ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    F₂ = (frame*-⋯ EE₂ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ PP ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    eM : Tm (2 + (sB + (sA + n)))
    eM = rn (ee ⋯ τ)
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = (U.⟪ F₁ [ K `send · (eM ⊗ cc₀) ]* ⟫ U.∥ (U.⟪ F₂ [ K `recv · cc₁ ]* ⟫ U.∥ RP))
    contractumR : U.Proc (2 + (sB + (sA + n)))
    contractumR = (U.⟪ F₁ [ * ]* ⟫ U.∥ (U.⟪ F₂ [ eM ]* ⟫ U.∥ RP))
    VeM : Value eM
    VeM = (value-⋯ (V ⋯ᵛ wkρ) τ Vτ ⋯ᵛ ρ₁) ⋯ᵛ ρ₂
    comStep : U.ν redexL UR.─→ₚ U.ν contractumR
    comStep = UR.RU-Com F₁ F₂ VeM {e₁ = tA0} {e₁′ = tB0} {e₂ = tA1} {e₂′ = tB1}
    threadEq : (E : Frame* (sum B₁′ + sum B₂′ + m)) (p : Tm (sum B₁′ + sum B₂′ + m)) →
               (U[ T.⟪ E [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq E p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* E τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ E τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    thread₁≡ : (U[ T.⟪ EE₁ [ K `send · (ee ⊗ (` 0F)) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₁ [ K `send · (eM ⊗ cc₀) ]* ⟫
    thread₁≡ = threadEq EE₁ (K `send · (ee ⊗ (` 0F)))
             ■ cong (λ t → U.⟪ F₁ [ K `send · (eM ⊗ t) ]* ⟫) cc₀-eq
    thread₂≡ : (U[ T.⟪ EE₂ [ K `recv · (` yv) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₂ [ K `recv · cc₁ ]* ⟫
    thread₂≡ = threadEq EE₂ (K `recv · (` yv))
             ■ cong (λ t → U.⟪ F₂ [ K `recv · t ]* ⟫) cc₁-eq
    YL≡ : YL ≡ (U.⟪ F₁ [ K `send · (eM ⊗ cc₀) ]* ⟫ U.∥ U.⟪ F₂ [ K `recv · cc₁ ]* ⟫) U.∥ RP
    YL≡ = cong₂ U._∥_ (cong₂ U._∥_ thread₁≡ thread₂≡) refl
    frontL : U.ν YL U.≋ U.ν redexL
    frontL = U.ν-cong (≡→≋ YL≡ ◅◅ Eq*.symmetric _ U.∥-assoc)
    YR : U.Proc (2 + (sB + (sA + n)))
    YR = (U.⟪ F₁ [ * ]* ⟫ U.∥ U.⟪ F₂ [ eM ]* ⟫) U.∥ RP
    backR : U.ν contractumR U.≋ U.ν YR
    backR = U.ν-cong (U.∥-assoc ◅◅ ≡→≋ (sym YR≡))
      where
        YR≡ : YR ≡ (U.⟪ F₁ [ * ]* ⟫ U.∥ U.⟪ F₂ [ eM ]* ⟫) U.∥ RP
        YR≡ = refl
    leaf-fire : U.ν YL UR.─→ₚ U.ν YR
    leaf-fire = UR.RU-Struct frontL comStep backR
    fire : Bφ B₁′ (Bφ B₂′ (U.ν YL)) UR─→ₚ* Bφ B₁′ (Bφ B₂′ (U.ν YR))
    fire = Bφ-lift-step B₁′ (Bφ-lift-step B₂′ leaf-fire) ◅ ε
    QR : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m)
    QR = (T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P
    sA≡ : syncs (b₁ ∷ B₁) ≡ sA
    sA≡ = syncs-cons-irrel b₁ (suc b₁) B₁
    sB≡ : syncs (b₂ ∷ B₂) ≡ sB
    sB≡ = syncs-cons-irrel b₂ (suc b₂) B₂
    τR : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n))
    τR = leafσ σ (b₁ ∷ B₁) (b₂ ∷ B₂)
    XR₀ : U.Proc (syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)))
    XR₀ = U[ QR ] τR
    eqAB : syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (sA + (2 + n))
    eqAB = cong₂ (λ u v → u + (v + (2 + n))) sB≡ sA≡
    XR : U.Proc (sB + (sA + (2 + n)))
    XR = subst U.Proc eqAB XR₀
    ν↓R : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
          U.ν (Bφ B₁′ (Bφ B₂′ X)) U.≋ Bφ B₁′ (Bφ B₂′ (U.ν (push X)))
    ν↓R X =
         ν-past-Bφ B₁′ (Bφ B₂′ X)
      ◅◅ Bφ-cong B₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B₂′ X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong B₁′ (ν-past-Bφ B₂′ (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    -- the RHS flatten, transported into the sA/sB (B₁′/B₂′) shape via the
    -- head-irrelevance of syncs and the head-irrelevance of the φ-prefix (drop).
    bridge-in : Bφ (b₂ ∷ B₂) XR₀
              ≡ Bφ B₂′ (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
    bridge-in = Bφ-suc-head≡ b₂' (suc b₂') B₂ XR₀
    flatR≡ : U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂) QR ] σ ≡ U.ν (Bφ B₁′ (Bφ B₂′ XR))
    flatR≡ =
        Uν-flat σ (b₁ ∷ B₁) (b₂ ∷ B₂) QR
      ■ cong U.ν
          ( Bφ-suc-head≡ b₁' (suc b₁') B₁ (Bφ (b₂ ∷ B₂) XR₀)
          ■ cong (Bφ B₁′) bridge2 )
      where
        subst-fn-≡ : ∀ {a a′} (e : a ≡ a′) {K} (Y : U.Proc (a + K)) →
                     subst (λ z → U.Proc (z + K)) e Y ≡ subst U.Proc (cong (_+ K) e) Y
        subst-fn-≡ refl Y = refl
        bridge2 : subst (λ z → U.Proc (z + (2 + n))) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)
                    (Bφ (b₂ ∷ B₂) XR₀)
                  ≡ Bφ B₂′ XR
        bridge2 =
            cong (subst (λ z → U.Proc (z + (2 + n))) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)) bridge-in
          ■ subst-fn-≡ (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁) (Bφ B₂′ (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀))
          ■ subst-Bφ (cong (_+ (2 + n)) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁)) B₂′
              (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
          ■ cong (Bφ B₂′) substComp
          where
            q₁ : syncs (b₂ ∷ B₂) + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (syncs (b₁ ∷ B₁) + (2 + n))
            q₁ = cong (_+ (syncs (b₁ ∷ B₁) + (2 + n))) sB≡
            q₂ : sB + (syncs (b₁ ∷ B₁) + (2 + n)) ≡ sB + (sA + (2 + n))
            q₂ = cong (syncs B₂′ +_) (cong (_+ (2 + n)) (syncs-cons-irrel (suc b₁') (suc (suc b₁')) B₁))
            substComp : subst U.Proc q₂
                          (subst (λ z → U.Proc (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ XR₀)
                        ≡ subst U.Proc eqAB XR₀
            substComp =
                cong (subst U.Proc q₂) (subst-fn-≡ sB≡ XR₀)
              ■ subst-subst q₁ {q₂} {XR₀}
              ■ cong (λ e → subst U.Proc e XR₀) (≡-irrelevant (q₁ ■ q₂) eqAB)
    -- QL' : the contractum at the BIG scope = QR weakened by wkρ.
    QL' : T.Proc (sum B₁′ + sum B₂′ + m)
    QL' = (T.⟪ EE₁ [ K `unit ]* ⟫ T.∥ T.⟪ EE₂ [ ee ]* ⟫) T.∥ PP
    WR : U.Proc (sB + (sA + (2 + n)))
    WR = U[ QL' ] τ
    -- YR is the push of WR (the * / ee threads, frames carry the τ already).
    *⋯τ≡ : K `unit ⋯ τ ≡ K `unit
    *⋯τ≡ = refl
    rn*≡ : rn (K `unit ⋯ τ) ≡ K `unit
    rn*≡ = refl
    YR≡pushWR : YR ≡ push WR
    YR≡pushWR = cong₂ U._∥_
        (cong₂ U._∥_
          (sym (threadEq EE₁ (K `unit) ■ cong (λ t → U.⟪ F₁ [ t ]* ⟫) rn*≡))
          (sym (threadEq EE₂ ee)))
        refl
    -- QL' = QR ⋯ₚ wkρ  (the contractum weakening: *, ee, PP are the wkρ-images).
    QL'≡ : QL' ≡ QR T.⋯ₚ wkρ
    QL'≡ = cong₂ T._∥_
             (cong₂ T._∥_
               (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₁ wkρ)))
               (cong T.⟪_⟫ (sym (frame-plug*ᵣ E₂ wkρ))))
             refl
    -- subst commutes through U[_] on the codomain.
    U-subst-cod : ∀ {c d} (eq : c ≡ d) (Q : T.Proc (sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m))
                  (ρ : sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ c) →
                  subst U.Proc eq (U[ Q ] ρ) ≡ U[ Q ] (subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eq ρ)
    U-subst-cod refl Q ρ = refl
    -- THE wkρ-cancellation: weakening then big leaf = (transported) small leaf.
    subst-σ-app : ∀ {c d D} (eq : c ≡ d) (ρ : D →ₛ c) (x : 𝔽 D) →
                  subst (λ z → D →ₛ z) eq ρ x ≡ subst Tm eq (ρ x)
    subst-σ-app refl ρ x = refl
    a₀ c₀ : ℕ
    a₀ = b₁ + sum B₁
    c₀ = b₂ + sum B₂
    -- wkρ acts as the head-slot insertion on each group: +1 below a₀, +2 at/above.
    -- inner: wkρ x = cast (((weakenᵣ ↑* suc a₀)) (cast (weakenᵣ x))); casts/weakenᵣ
    -- preserve/shift toℕ.  Express via weaken* 1 = (1 ↑ʳ_) on the inner weakenᵣ.
    wkₚ-step : (x : 𝔽 (a₀ + c₀ + m)) →
               Fin.toℕ (wkρ x)
               ≡ Fin.toℕ ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀) (Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))
    wkₚ-step x = Fin.toℕ-cast (sym (+-assoc (suc a₀) (suc c₀) m))
                   ((weaken* ⦃ Kᵣ ⦄ 1 ↑* suc a₀) (Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)))
    toℕ-wkρ-lt : (x : 𝔽 (a₀ + c₀ + m)) → Fin.toℕ x Nat.< a₀ → Fin.toℕ (wkρ x) ≡ suc (Fin.toℕ x)
    toℕ-wkρ-lt x lt =
        wkₚ-step x
      ■ toℕ-↑*-lt (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀) zc zclt
      ■ czN
      where
        zc = Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zclt : Fin.toℕ zc Nat.< suc a₀
        zclt = subst (Nat._< suc a₀) (sym czN) (Nat.s≤s lt)
    toℕ-wkρ-ge : (x : 𝔽 (a₀ + c₀ + m)) → a₀ Nat.≤ Fin.toℕ x → Fin.toℕ (wkρ x) ≡ 2 + Fin.toℕ x
    toℕ-wkρ-ge x ge =
        wkₚ-step x
      ■ toℕ-↑*-ge (weaken* ⦃ Kᵣ ⦄ 1) (suc a₀) zc zcge
      ■ cong (suc a₀ +_) (toℕ-weaken*ᵣ 1 (Fin.reduce≥ zc zcge) ■ cong suc redN)
      ■ arith
      where
        zc = Fin.cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
        czN : Fin.toℕ zc ≡ suc (Fin.toℕ x)
        czN = Fin.toℕ-cast (cong suc (+-assoc a₀ c₀ m)) (weaken* ⦃ Kᵣ ⦄ 1 x)
            ■ toℕ-weaken*ᵣ 1 x
        zcge : suc a₀ Nat.≤ Fin.toℕ zc
        zcge = subst (suc a₀ Nat.≤_) (sym czN) (Nat.s≤s ge)
        redN : Fin.toℕ (Fin.reduce≥ zc zcge) ≡ Fin.toℕ x Nat.∸ a₀
        redN = toℕ-reduce≥ zc zcge ■ cong (Nat._∸ suc a₀) czN ■ refl
        arith : suc a₀ + suc (Fin.toℕ x Nat.∸ a₀) ≡ 2 + Fin.toℕ x
        arith = cong suc (Nat.+-suc a₀ (Fin.toℕ x Nat.∸ a₀))
              ■ cong (λ z → suc (suc z)) (Nat.m+[n∸m]≡n ge)
    -- (wkρ ·ₖ τ) x = τ (wkρ x).
    compEq : (x : 𝔽 (a₀ + c₀ + m)) → (wkρ ·ₖ τ) x ≡ τ (wkρ x)
    compEq x = refl
    -- RHS subst pushed to Tm.
    rhsEq : (x : 𝔽 (a₀ + c₀ + m)) →
            subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eqAB τR x ≡ subst Tm eqAB (τR x)
    rhsEq x = subst-σ-app eqAB τR x
    -- the three region maps of wkρ, by Fin.toℕ-injective from toℕ-wkρ-lt/ge.
    wkρ-map-tail : (i : 𝔽 m) → wkρ ((a₀ + c₀) ↑ʳ i) ≡ (suc a₀ + suc c₀) ↑ʳ i
    wkρ-map-tail i = Fin.toℕ-injective
      ( toℕ-wkρ-ge ((a₀ + c₀) ↑ʳ i) geq
      ■ cong (2 +_) (Fin.toℕ-↑ʳ (a₀ + c₀) i)
      ■ sym (Fin.toℕ-↑ʳ (suc a₀ + suc c₀) i ■ arith) )
      where
        geq : a₀ Nat.≤ Fin.toℕ ((a₀ + c₀) ↑ʳ i)
        geq = subst (a₀ Nat.≤_) (sym (Fin.toℕ-↑ʳ (a₀ + c₀) i)) (Nat.≤-trans (Nat.m≤m+n a₀ c₀) (Nat.m≤m+n (a₀ + c₀) (Fin.toℕ i)))
        arith : suc a₀ + suc c₀ + Fin.toℕ i ≡ 2 + ((a₀ + c₀) + Fin.toℕ i)
        arith = solve 3 (λ A C I → con 1 :+ A :+ (con 1 :+ C) :+ I := con 2 :+ ((A :+ C) :+ I)) refl a₀ c₀ (Fin.toℕ i)
          where open +-*-Solver
    wkρ-leafσ : (wkρ ·ₖ τ) ≗ subst (λ z → sum (b₁ ∷ B₁) + sum (b₂ ∷ B₂) + m →ₛ z) eqAB τR
    wkρ-leafσ x = compEq x ■ coreEq ■ sym (rhsEq x)
      where
        coreEq : τ (wkρ x) ≡ subst Tm eqAB (τR x)
        coreEq with Fin.splitAt (a₀ + c₀) x in eqo
        ... | inj₂ i =
              leafσ-tail σ B₁′ B₂′ (wkρ x) i splitWkρ
            ■ tailReconcile
          where
            x≡ : x ≡ (a₀ + c₀) ↑ʳ i
            x≡ = sym (Fin.splitAt⁻¹-↑ʳ eqo)
            wkρx≡ : wkρ x ≡ (suc a₀ + suc c₀) ↑ʳ i
            wkρx≡ = cong wkρ x≡ ■ wkρ-map-tail i
            splitWkρ : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₂ i
            splitWkρ = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                     ■ Fin.splitAt-↑ʳ (sum B₁′ + sum B₂′) m i
            -- syncs ignores the head, so the LHS/RHS differ only by the eqAB cast.
            tailReconcile :
              σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁′) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
              ≡ subst Tm eqAB (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
            tailReconcile = J-tail sB≡ sA≡
              where
                J-tail : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                       → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sb₁ ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                         ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                             (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                J-tail refl refl = refl
        ... | inj₁ z with Fin.splitAt a₀ z in eqi
        ...   | inj₁ j =
                  leafσ-A₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc j) splitWkρ-outer splitWkρ-inner
                ■ B₁reconcile
              where
                x≡ : x ≡ (j ↑ˡ c₀) ↑ˡ m
                x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ˡ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
                toℕj< : Fin.toℕ j Nat.< a₀
                toℕj< = Fin.toℕ<n j
                toℕx< : Fin.toℕ x Nat.< a₀
                toℕx< = subst (Nat._< a₀) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀) m ■ Fin.toℕ-↑ˡ j c₀)) toℕj<
                zB : 𝔽 (sum B₁′ + sum B₂′)
                zB = (Fin.suc j) ↑ˡ sum B₂′
                wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
                wkρx≡ = Fin.toℕ-injective
                  ( toℕ-wkρ-lt x toℕx<
                  ■ cong suc (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (j ↑ˡ c₀) m ■ Fin.toℕ-↑ˡ j c₀)
                  ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ˡ (Fin.suc j) (sum B₂′) ) )
                splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
                splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                               ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
                splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₁ (Fin.suc j)
                splitWkρ-inner = Fin.splitAt-↑ˡ (sum B₁′) (Fin.suc j) (sum B₂′)
                B₁reconcile :
                  canonₛ B₁′ (K `unit , 0F , K `unit) (Fin.suc j) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)
                  ≡ subst Tm eqAB (canonₛ (b₁ ∷ B₁) (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                B₁reconcile =
                    cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂′)) (canonₛ-suc-shift b₁ B₁ 0F (K `unit) j)
                  ■ J-A₁ sB≡ sA≡
                  where
                    ccA : UChan (2 + n)
                    ccA = (K `unit , 0F , K `unit)
                    J-A₁ : ∀ {sb₂ sb₁} (e₂ : syncs (b₂ ∷ B₂) ≡ sb₂) (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                         → subst (λ z → Tm (z + (2 + n))) e₁ (canonₛ (b₁ ∷ B₁) ccA j) ⋯ weaken* ⦃ Kᵣ ⦄ sb₂
                           ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e₂ e₁)
                               (canonₛ (b₁ ∷ B₁) ccA j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (b₂ ∷ B₂)))
                    J-A₁ refl refl = refl
        ...   | inj₂ k =
                  leafσ-B₁ σ B₁′ B₂′ (wkρ x) zB (Fin.suc k) splitWkρ-outer splitWkρ-inner
                ■ B₂reconcile
              where
                x≡ : x ≡ (a₀ ↑ʳ k) ↑ˡ m
                x≡ = sym (cong (Fin._↑ˡ m) (Fin.splitAt⁻¹-↑ʳ eqi) ■ Fin.splitAt⁻¹-↑ˡ eqo)
                toℕx≥ : a₀ Nat.≤ Fin.toℕ x
                toℕx≥ = subst (a₀ Nat.≤_) (sym (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ k)) (Nat.m≤m+n a₀ (Fin.toℕ k))
                zB : 𝔽 (sum B₁′ + sum B₂′)
                zB = sum B₁′ ↑ʳ (Fin.suc k)
                wkρx≡ : wkρ x ≡ (zB ↑ˡ m)
                wkρx≡ = Fin.toℕ-injective
                  ( toℕ-wkρ-ge x toℕx≥
                  ■ cong (2 +_) (cong Fin.toℕ x≡ ■ Fin.toℕ-↑ˡ (a₀ ↑ʳ k) m ■ Fin.toℕ-↑ʳ a₀ k)
                  ■ arith
                  ■ sym ( Fin.toℕ-↑ˡ zB m ■ Fin.toℕ-↑ʳ (sum B₁′) (Fin.suc k) ) )
                  where
                    arith : 2 + (a₀ + Fin.toℕ k) ≡ suc a₀ + suc (Fin.toℕ k)
                    arith = solve 2 (λ A K → con 2 :+ (A :+ K) := con 1 :+ A :+ (con 1 :+ K)) refl a₀ (Fin.toℕ k)
                      where open +-*-Solver
                splitWkρ-outer : Fin.splitAt (sum B₁′ + sum B₂′) (wkρ x) ≡ inj₁ zB
                splitWkρ-outer = cong (Fin.splitAt (sum B₁′ + sum B₂′)) wkρx≡
                               ■ Fin.splitAt-↑ˡ (sum B₁′ + sum B₂′) zB m
                splitWkρ-inner : Fin.splitAt (sum B₁′) zB ≡ inj₂ (Fin.suc k)
                splitWkρ-inner = Fin.splitAt-↑ʳ (sum B₁′) (sum B₂′) (Fin.suc k)
                ccB : ∀ (s : ℕ) → UChan (s + (2 + n))
                ccB s = (K `unit , weaken* ⦃ Kᵣ ⦄ s 1F , K `unit)
                B₂reconcile :
                  canonₛ B₂′ (ccB (syncs B₁′)) (Fin.suc k)
                  ≡ subst Tm eqAB (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
                B₂reconcile = J-B₂ sA≡
                  where
                    -- bridge the inner-scope flag arg from syncs(b₁∷B₁) to sA (= syncs B₁′),
                    -- absorbing the canonₛ-suc-shift outer subst (≡ sB≡ by ≡-irrelevance).
                    J-B₂ : ∀ {sb₁} (e₁ : syncs (b₁ ∷ B₁) ≡ sb₁)
                         → canonₛ (suc b₂ ∷ B₂) (ccB sb₁) (Fin.suc k)
                           ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ e₁)
                               (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k)
                    J-B₂ refl =
                        canonₛ-suc-shift b₂ B₂ (weaken* ⦃ Kᵣ ⦄ (syncs (b₁ ∷ B₁)) 1F) (K `unit) k
                      ■ cong (λ e → subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e
                                      (canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k))
                          (≡-irrelevant (syncs-cons-irrel b₂ (suc b₂) B₂) sB≡)
                      ■ substReshape
                      where
                        T₀ = canonₛ (b₂ ∷ B₂) (ccB (syncs (b₁ ∷ B₁))) k
                        substReshape :
                          subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) sB≡ T₀
                          ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) sB≡ refl) T₀
                        substReshape = subst-fn-≡′ sB≡ T₀
                          where
                            subst-fn-≡′ : ∀ {a a′} (e : a ≡ a′) (t : Tm (a + (syncs (b₁ ∷ B₁) + (2 + n)))) →
                                          subst (λ z → Tm (z + (syncs (b₁ ∷ B₁) + (2 + n)))) e t
                                          ≡ subst Tm (cong₂ (λ u v → u + (v + (2 + n))) e refl) t
                            subst-fn-≡′ refl t = refl
    WR≡XR : WR ≡ XR
    WR≡XR =
        cong (λ Q → U[ Q ] τ) QL'≡
      ■ U-⋯ₚ QR
      ■ U-cong QR wkρ-leafσ
      ■ sym (U-subst-cod eqAB QR τR)
    leafEq : YR ≡ push XR
    leafEq = YR≡pushWR ■ cong push WR≡XR
    back : Bφ B₁′ (Bφ B₂′ (U.ν YR)) U.≋ U[ T.ν (b₁ ∷ B₁) (b₂ ∷ B₂)
              ((T.⟪ E₁ [ K `unit ]* ⟫ T.∥ T.⟪ E₂ [ e ]* ⟫) T.∥ P) ] σ
    back =
         Bφ-cong B₁′ (Bφ-cong B₂′ (U.ν-cong (≡→≋ leafEq)))
      ◅◅ Eq*.symmetric _ (ν↓R XR)
      ◅◅ ≡→≋ (sym flatR≡)
