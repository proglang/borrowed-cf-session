module BorrowedCF.Simulation2.Theorems.SplitsH1 where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation2.SplitConfine using (lsplit-confine; rsplit-confine)
open import BorrowedCF.Simulation2.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation2.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ
        ; VChan; chanTriple-V; Value-subst; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation2.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation2.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation2.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)

-- COPIED transpose engine from Simulation2.Congruence (hole-free prefix).
subst-≋ : ∀ {a b} (eq : a ≡ b) {P Q : U.Proc a} → P U.≋ Q →
          subst U.Proc eq P U.≋ subst U.Proc eq Q
subst-≋ refl r = r

≡→≋ : {P Q : U.Proc n} → P ≡ Q → P U.≋ Q
≡→≋ refl = ε

local-⋯ₚ-id : (P : U.Proc m) {ρ : m →ᵣ m} → ρ ≗ idₖ → P U.⋯ₚ ρ ≡ P
local-⋯ₚ-id U.⟪ e ⟫   eq = cong U.⟪_⟫ (⋯-id e eq)
local-⋯ₚ-id (P U.∥ Q) eq = cong₂ U._∥_ (local-⋯ₚ-id P eq) (local-⋯ₚ-id Q eq)
local-⋯ₚ-id (U.ν P)   eq = cong U.ν (local-⋯ₚ-id P (id↑* 2 eq))
local-⋯ₚ-id (U.φ x P) eq = cong (U.φ x) (local-⋯ₚ-id P (id↑ eq))

subst-⋯ₚ-cod : ∀ {a c d} (q : c ≡ d) (Q : U.Proc a) (θ : a →ᵣ c) →
               Q U.⋯ₚ subst (λ z → a →ᵣ z) q θ ≡ subst U.Proc q (Q U.⋯ₚ θ)
subst-⋯ₚ-cod refl Q θ = refl

subst-flip : {A : Set} {F : A → Set} {x y : A} (q : x ≡ y) {a : F x} {b : F y} →
             subst F q a ≡ b → a ≡ subst F (sym q) b
subst-flip refl eq = eq

-- ⋯ₚ with a subst₂-coerced renaming: re-coerce X's domain and the codomain.
cast-⋯2 : ∀ {A A′ B B′} (pA : A′ ≡ A) (pB : B ≡ B′) (Y : U.Proc A′) (ρ : A →ᵣ B) →
          Y U.⋯ₚ subst₂ _→ᵣ_ (sym pA) pB ρ
          ≡ subst U.Proc pB (subst U.Proc pA Y U.⋯ₚ ρ)
cast-⋯2 refl refl Y ρ = refl

Bφ : ∀ {n} (B : BindGroup) → U.Proc (syncs B + n) → U.Proc n
Bφ []            P = P
Bφ (b ∷ [])      P = P
Bφ {n} (b ∷ B@(_ ∷ _)) P = U.φ ϕ[ b ] (Bφ B (subst U.Proc (sym (+-suc (syncs B) n)) P))

Bφ-cong : ∀ {n} (B : BindGroup) {P Q : U.Proc (syncs B + n)} →
          P U.≋ Q → Bφ {n} B P U.≋ Bφ B Q
Bφ-cong []            pq = pq
Bφ-cong (b ∷ [])      pq = pq
Bφ-cong {n} (b ∷ B@(_ ∷ _)) pq = U.φ-cong (Bφ-cong B (subst-≋ (sym (+-suc (syncs B) n)) pq))

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

  chReqᵍ : ∀ {a bb} b sB (e1 : Tm a) (x : 𝔽 a) (ρ : a →ᵣ bb) (j : 𝔽 b) →
           (Ub[ b ] (wk e1 , suc x , ` 0F) j ⋯ weaken* ⦃ Kᵣ ⦄ sB) ⋯ ((ρ ↑) ↑* sB)
           ≡ Ub[ b ] (wk (e1 ⋯ ρ) , suc (ρ x) , ` 0F) j ⋯ weaken* ⦃ Kᵣ ⦄ sB
  chReqᵍ b sB e1 x ρ j =
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
... | inj₁ j | _  = ΘrelEqᵍ (syncs B) ρ chL
                  ■ cong (subst Tm (+-suc (syncs B) bb)) (chReqᵍ b (syncs B) e1 x ρ j)
  where chL = Ub[ b ] (wk e1 , suc x , ` 0F) j ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
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
-- φ-binder block transpose engine (against Bφ directly)
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
-- leaf-substitution reconcile for the ν-swap case
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
-- Translation-independent arithmetic / renaming plumbing for the split-handle
-- (ported from Simulation/Theorems/LSplit.agda; ↑*-lo/hi → BlockPerm toℕ-↑*-lt/ge).
subst-⊗ : ∀ {a b} (eq : a ≡ b) (p r : Tm a) →
          subst Tm eq (p ⊗ r) ≡ subst Tm eq p ⊗ subst Tm eq r
subst-⊗ refl p r = refl

subst-` : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
subst-` refl q = refl

subst-Kunit : ∀ {a b} (eq : a ≡ b) → subst Tm eq (K `unit) ≡ K `unit
subst-Kunit refl = refl

pos-split : ∀ a (B₁′ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) →
  Fin.cast (sym (sum-++ (a ∷ B₁′) (suc b₁ ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ 0F)
    ≡ a ↑ʳ Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F)
pos-split a B₁′ b₁ B₂ = Fin.toℕ-injective
  ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁′) (suc b₁ ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ 0F)
  ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁′)) 0F
  ■ +-assoc a (sum B₁′) 0
  ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F))
        ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ B₁′ (suc b₁ ∷ B₂))) (sum B₁′ ↑ʳ 0F)
                      ■ Fin.toℕ-↑ʳ (sum B₁′) 0F ) ) )

pos-split-gen : ∀ a (B₁′ : T.BindGroup) (c : ℕ) (B₂ : T.BindGroup) (i : 𝔽 (sum (c ∷ B₂))) →
  Fin.cast (sym (sum-++ (a ∷ B₁′) (c ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ i)
    ≡ a ↑ʳ Fin.cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i)
pos-split-gen a B₁′ c B₂ i = Fin.toℕ-injective
  ( Fin.toℕ-cast (sym (sum-++ (a ∷ B₁′) (c ∷ B₂))) (sum (a ∷ B₁′) ↑ʳ i)
  ■ Fin.toℕ-↑ʳ (sum (a ∷ B₁′)) i
  ■ +-assoc a (sum B₁′) (Fin.toℕ i)
  ■ sym ( Fin.toℕ-↑ʳ a (Fin.cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i))
        ■ cong (a +_) ( Fin.toℕ-cast (sym (sum-++ B₁′ (c ∷ B₂))) (sum B₁′ ↑ʳ i)
                      ■ Fin.toℕ-↑ʳ (sum B₁′) i ) ) )

dlwk : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) →
       sum (B₁ ++ suc b₁ ∷ B₂) →ᵣ sum (B₁ ++ suc (suc b₁) ∷ B₂)
dlwk []        b₁ B₂ i = (weakenᵣ ↑* 1) i
dlwk (a ∷ B₁') b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ suc (suc b₁) ∷ B₂)) , (λ r → a ↑ʳ dlwk B₁' b₁ B₂ r) ]′ (splitAt a i)

-- dlwk inserts a slot at flat position `sum B₁ + 1`: below it, toℕ is preserved; above, +1.
dlwk-lo : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          Fin.toℕ j Nat.< sum B₁ + 1 → Fin.toℕ (dlwk B₁ b₁ B₂ j) ≡ Fin.toℕ j
dlwk-lo []        b₁ B₂ j lt = toℕ-↑*-lt weakenᵣ 1 j lt
dlwk-lo (a ∷ B₁') b₁ B₂ j lt with dlwk-lo B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : Fin.toℕ r Nat.< sum B₁' + 1
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁' + 1)
                   (subst (Nat._< a + (sum B₁' + 1)) jℕ
                     (subst (Fin.toℕ j Nat.<_) (Nat.+-assoc a (sum B₁') 1) lt))
dlwk-hi : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          sum B₁ + 1 Nat.≤ Fin.toℕ j → Fin.toℕ (dlwk B₁ b₁ B₂ j) ≡ suc (Fin.toℕ j)
dlwk-hi []        b₁ B₂ j h =
    toℕ-↑*-ge weakenᵣ 1 j h
  ■ cong (1 +_) (cong suc (toℕ-reduce≥ j h))
  ■ cong suc (Nat.m+[n∸m]≡n h)
dlwk-hi (a ∷ B₁') b₁ B₂ j h with dlwk-hi B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁' + 1))) (subst (Nat._≤ Fin.toℕ j) (Nat.+-assoc a (sum B₁') 1) h)))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (dlwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : sum B₁' + 1 Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁' + 1) (Fin.toℕ r)
                   (subst (a + (sum B₁' + 1) Nat.≤_) jℕ
                     (subst (Nat._≤ Fin.toℕ j) (Nat.+-assoc a (sum B₁') 1) h))

𝐒lwk-lo : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            Fin.toℕ x Nat.< sum B₁ + 1 →
            Fin.toℕ (TR.SplitRenamings.lwk B₁ B₂ B {b₁} {m} x) ≡ Fin.toℕ x
𝐒lwk-lo B₁ B₂ B {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-lt weakenᵣ (sum B₁ + 1) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁ + 1
        lt′ = subst (Nat._< sum B₁ + 1) (sym (Fin.toℕ-cast _ x)) lt

𝐒lwk-hi : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            sum B₁ + 1 Nat.≤ Fin.toℕ x →
            Fin.toℕ (TR.SplitRenamings.lwk B₁ B₂ B {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒lwk-hi B₁ B₂ B {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-ge weakenᵣ (sum B₁ + 1) (Fin.cast _ x) h′
  ■ cong (sum B₁ + 1 +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ (sum B₁ + 1)) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁ + 1) (Fin.toℕ x Nat.∸ (sum B₁ + 1))
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ + 1 Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ + 1 Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

-- The grown bind group has exactly one more data slot.
sum-lwk : ∀ (B₁ : T.BindGroup) {b₁ B₂} →
          sum (B₁ ++ suc (suc b₁) ∷ B₂) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂))
sum-lwk B₁ {b₁} {B₂} = sum-++ B₁ (suc (suc b₁) ∷ B₂)
                     ■ Nat.+-suc (sum B₁) (sum (suc b₁ ∷ B₂))
                     ■ cong suc (sym (sum-++ B₁ (suc b₁ ∷ B₂)))

sB₁≤sumC₁ : ∀ (B₁ : T.BindGroup) {b₁ B₂} → sum B₁ + 1 Nat.≤ sum (B₁ ++ suc b₁ ∷ B₂)
sB₁≤sumC₁ B₁ {b₁} {B₂} =
  subst (sum B₁ + 1 Nat.≤_) (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (Nat.+-monoʳ-≤ (sum B₁) (Nat.s≤s Nat.z≤n))
P1 : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
     TR.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
     ≡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1 B₁ B₂ B {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁ + 1
... | yes lt = Fin.toℕ-injective
      ( 𝐒lwk-lo B₁ B₂ B _ (subst (Nat._< sum B₁ + 1) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ dlwk-lo B₁ b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ dlwk-hi B₁ b₁ B₂ d h≤) )
  where h≤ : sum B₁ + 1 Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((dlwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (dlwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (dlwk B₁ b₁ B₂ d) (sum B)

P2 : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (w : 𝔽 (sum B)) →
     TR.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m)
     ≡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m
P2 B₁ B₂ B {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁≤sumC₁ B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-lwk B₁)

P3 : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (u : 𝔽 m) →
     TR.SplitRenamings.lwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u)
     ≡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) ↑ʳ u
P3 B₁ B₂ B {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒lwk-hi B₁ B₂ B _ (subst (sum B₁ + 1 Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁≤sumC₁ B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-lwk B₁)
syncs-lwk : ∀ (B₁ : T.BindGroup) {b₁ : ℕ} {B₂ : T.BindGroup} →
            syncs (B₁ ++ suc b₁ ∷ B₂) ≡ syncs (B₁ ++ suc (suc b₁) ∷ B₂)
syncs-lwk []            {b₁} {[]}      = refl
syncs-lwk []            {b₁} {b' ∷ B'} = refl
syncs-lwk (a ∷ [])      {b₁} {B₂}      = cong suc (syncs-lwk [] {b₁} {B₂})
syncs-lwk (a ∷ d ∷ B₁″) {b₁} {B₂}      = cong suc (syncs-lwk (d ∷ B₁″) {b₁} {B₂})

-- A single untyped step lifts through a Bφ prefix (φ-nest) via RU-Sync. (Choice)
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

-- VSub of canonₛ (Choice).
VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ j → Ub-V (b + 0) e1 x e2 Ve1 Ve2 j
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ j → value-⋯ (Ub-V b (wk e1) (suc x) (` 0F) (Ve1 ⋯ᵛ weakenᵣ) V-` j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

-- canonₛ (suc b ∷ B) cc at index 0F is a chanTriple with junction at syncs+toℕ x. (Choice)
canonₛ-head-triple : ∀ {N} (b : ℕ) (B : BindGroup) (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs (suc b ∷ B) + N) ] Σ[ c ∈ Tm (syncs (suc b ∷ B) + N) ]
  Σ[ j ∈ 𝔽 (syncs (suc b ∷ B) + N) ]
    (canonₛ (suc b ∷ B) (e1 , x , e2) 0F ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (suc b ∷ B) + Fin.toℕ x)
canonₛ-head-triple zero        []        e1 e2 x =
  e1 , e2 , x , refl , refl
canonₛ-head-triple (suc b)     []        e1 e2 x =
  e1 , * , x , refl , refl
canonₛ-head-triple {N} zero (c′ ∷ B) e1 e2 x =
  ( subst Tm (+-suc sB N) (wk e1 ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , tripeq
  , junceq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (1 ∷ c′ ∷ B) (e1 , x , e2) 0F
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

-- The push composite sends a junction var at flat position sB+(sA+d) to d. (Choice)
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

-- frame-plug for a plain renaming. (Choice)
frame-plug*ᵣ : (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

-- Codomain: the multi-step / silent disjunction (copied from Theorems).
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

-- canonₛ at the lsplit handle position (head of the suc b₁ block embedded after
-- B₁) is a chanTriple whose junction sits at flat position syncs C₁ + toℕ x.
-- Induction on B₁ (split [] / a∷[] / a∷d∷B₁″ so syncs reduces), base = canonₛ-head-triple.
canonₛ-handle : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N) ]
    (canonₛ (B₁ ++ suc b₁ ∷ B₂) (e₁ , x , e₂) (Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F))
       ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ x)
canonₛ-handle []        {N} e₁ x e₂ b₁ B₂ =
  proj₁ h , proj₁ (proj₂ h) , proj₁ (proj₂ (proj₂ h))
  , castidx (proj₁ (proj₂ (proj₂ (proj₂ h))))
  , proj₂ (proj₂ (proj₂ (proj₂ h)))
  where
    h = canonₛ-head-triple b₁ B₂ e₁ e₂ x
    castidx : canonₛ (suc b₁ ∷ B₂) (e₁ , x , e₂) 0F
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h) →
              canonₛ (suc b₁ ∷ B₂) (e₁ , x , e₂)
                (Fin.cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F))
                ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h)
    castidx = subst (λ z → canonₛ (suc b₁ ∷ B₂) (e₁ , x , e₂) z
                            ≡ (proj₁ h ⊗ (` proj₁ (proj₂ (proj₂ h)))) ⊗ proj₁ (proj₂ h))
                (sym (Fin.toℕ-injective (Fin.toℕ-cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F))))
canonₛ-handle (a ∷ []) {N} e₁ x e₂ b₁ B₂
  with canonₛ-handle ([]) (` 0F) (suc x) (wk e₂) b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs (([]) ++ suc b₁ ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ ([])) (suc b₁ ∷ B₂))) (sum (a ∷ ([])) ↑ʳ 0F)
    cp′ = Fin.cast (sym (sum-++ ([]) (suc b₁ ∷ B₂))) (sum ([]) ↑ʳ 0F)
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split a ([]) b₁ B₂)
            ■ Fin.splitAt-↑ʳ a (sum (([]) ++ suc b₁ ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ ([]) ++ suc b₁ ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ (([]) ++ suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTrip (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl
canonₛ-handle (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂
  with canonₛ-handle (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq
  , junceq
  where
    sB = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ (d ∷ B₁″)) (suc b₁ ∷ B₂))) (sum (a ∷ (d ∷ B₁″)) ↑ʳ 0F)
    cp′ = Fin.cast (sym (sum-++ (d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 0F)
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split a (d ∷ B₁″) b₁ B₂)
            ■ Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ (d ∷ B₁″) ++ suc b₁ ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTrip (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq ((A ⊗ (` jj)) ⊗ C)
                    ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl A jj C = refl
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-subst𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec)))
           ■ +-suc sB (Fin.toℕ x)
      where
        toℕ-subst𝔽 : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽 refl y = refl

-- canonₛ on the grown bind group, off the consumed handle, equals the transported
-- ungrown canonₛ.  All slots of the head data-block map to the SAME const triple,
-- so growth by one slot is invisible away from the handle.
subst-Π-T : ∀ {DA} {a b} (eq : a ≡ b) (g : 𝔽 DA → Tm a) (i : 𝔽 DA) →
            subst (λ z → 𝔽 DA → Tm z) eq g i ≡ subst Tm eq (g i)
subst-Π-T refl g i = refl

ss-T : ∀ {A : Set} {F : A → Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) {t : F x} →
       subst F q (subst F p t) ≡ subst F (p ■ q) t
ss-T refl refl = refl

uipℕ : {x y : ℕ} (p q : x ≡ y) → p ≡ q
uipℕ refl refl = refl

chainLwk : ∀ {N} {sT sT′ : ℕ} (sl : sT ≡ sT′)
           {DA DB : Set} (g : DA → Tm (sT + suc N)) (g′ : DB → Tm (sT′ + suc N))
           (i : DA) (di : DB) →
           subst Tm (cong (_+ suc N) sl) (g i) ≡ g′ di →
           subst Tm (cong (_+ N) (cong suc sl)) (subst Tm (+-suc sT N) (g i))
           ≡ subst Tm (+-suc sT′ N) (g′ di)
chainLwk {N} {sT} {sT′} sl g g′ i di innerT =
    ss-T (+-suc sT N) (cong (_+ N) (cong suc sl))
  ■ cong (λ pf → subst Tm pf (g i)) (uipℕ _ _)
  ■ sym (ss-T (cong (_+ suc N) sl) (+-suc sT′ N))
  ■ cong (subst Tm (+-suc sT′ N)) innerT

canonₛ-lwk : ∀ (B₁ : BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F) →
             subst Tm (cong (_+ N) (syncs-lwk B₁)) (canonₛ (B₁ ++ suc b₁ ∷ B₂) cc i)
             ≡ canonₛ (B₁ ++ suc (suc b₁) ∷ B₂) cc (dlwk B₁ b₁ B₂ i)
canonₛ-lwk []            cc zero       []      i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
canonₛ-lwk []            cc (suc b₁)   []      i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
... | suc i′ with Fin.splitAt (suc b₁) i′
...   | inj₁ k′ = refl
...   | inj₂ ()
canonₛ-lwk []            (e₁ , x , e₂) zero     (b ∷ B) i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
... | suc i′ = refl
canonₛ-lwk []            (e₁ , x , e₂) (suc b₁) (b ∷ B) i i≢ with i
... | 0F = ⊥-elim (i≢ refl)
... | suc i′ with Fin.splitAt (suc b₁) i′
...   | inj₁ k′ = refl
...   | inj₂ q  = refl
canonₛ-lwk (a ∷ []) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-lwk ([]) (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum (([]) ++ suc (suc b₁) ∷ B₂)))))
  where
    sT  = syncs (([]) ++ suc b₁ ∷ B₂)
    sT′ = syncs (([]) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk ([]) {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ suc (suc b₁) ∷ B₂) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (dlwk ([]) b₁ B₂ r))
        (rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum (([]) ++ suc b₁ ∷ B₂)) i)
                          ■ cong (Fin.join a (sum (([]) ++ suc b₁ ∷ B₂))) seq
                          ■ cong (a ↑ʳ_) r≡
                          ■ sym (pos-split a ([]) b₁ B₂) )))
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum (([]) ++ suc (suc b₁) ∷ B₂)) (dlwk ([]) b₁ B₂ r))))
  where
    sT  = syncs (([]) ++ suc b₁ ∷ B₂)
    sT′ = syncs (([]) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk ([]) {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} (([]) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} (([]) ++ suc (suc b₁) ∷ B₂) cc-r ]′
canonₛ-lwk (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-lwk (d ∷ B₁″) (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p =
      chainLwk sl G G′ (inj₁ p) (inj₁ p) headCoh
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)))))
  where
    sT  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk (d ∷ B₁″) {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r ]′
    headCoh : subst Tm (cong (_+ suc N) sl) (G (inj₁ p)) ≡ G′ (inj₁ p)
    headCoh = triCoh sl
      where
        triCoh : ∀ {ss ss′} (e : ss ≡ ss′) →
                 subst Tm (cong (_+ suc N) e)
                   (Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss)
                 ≡ Ub[ a ] (wk e₁ , suc x , ` 0F) p ⋯ weaken* ⦃ Kᵣ ⦄ ss′
        triCoh refl = refl
... | inj₂ r =
      chainLwk sl G G′ (inj₂ r) (inj₂ (dlwk (d ∷ B₁″) b₁ B₂ r))
        (rec r (λ r≡ → i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) i)
                          ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) seq
                          ■ cong (a ↑ʳ_) r≡
                          ■ sym (pos-split a (d ∷ B₁″) b₁ B₂) )))
    ■ cong (subst Tm (+-suc sT′ N)) (sym (cong G′ (Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) (dlwk (d ∷ B₁″) b₁ B₂ r))))
  where
    sT  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sT′ = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    sl   = syncs-lwk (d ∷ B₁″) {b₁} {B₂}
    triL = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT
    triR = Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sT′
    cc-r = ((` 0F) , suc x , e₂ ⋯ weakenᵣ)
    G  = [ triL , canonₛ {n = suc N} ((d ∷ B₁″) ++ suc b₁ ∷ B₂) cc-r ]′
    G′ = [ triR , canonₛ {n = suc N} ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) cc-r ]′

-- transport of U[P] along a codomain scope equality.
U-cod-transport : ∀ {aa} (P : T.Proc aa) (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (σ : aa →ₛ h x) →
                  subst (λ z → U.Proc (h z)) eq (U[ P ] σ)
                  ≡ U[ P ] (subst (λ z → aa →ₛ h z) eq σ)
U-cod-transport P h refl σ = refl

