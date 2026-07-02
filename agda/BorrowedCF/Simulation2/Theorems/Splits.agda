module BorrowedCF.Simulation2.Theorems.Splits where

-- | Forward-simulation cases R-LSplit and R-RSplit for the reworked
--   paper-matching process definitions.  Exports U-lsplit and U-rsplit.
--
--   The route mirrors the (un-importable, hole-gated) Simulation2.Congruence
--   transpose engine: U[ ν (B₁++suc b₁∷B₂) B (…) ]σ flattens (Uν-flat) to
--   ν (Bφ 𝔅 (Bφ B (leaf))); the outer ν is pushed past both φ-nests to the
--   leaf (ν-past-Bφ), RU-LSplit/RU-RSplit fires on the leaf ν, then the ν is
--   pulled back out.  The transpose engine (Bφ/canonₛ/ν-past-Bφ/Bφ-transpose…)
--   is COPIED here verbatim from Congruence's hole-free prefix because
--   Congruence carries open interaction metas downstream and is unimportable.

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

subst-∥f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (P Q : U.Proc (h x)) →
           subst (λ z → U.Proc (h z)) eq (P U.∥ Q)
           ≡ subst (λ z → U.Proc (h z)) eq P U.∥ subst (λ z → U.Proc (h z)) eq Q
subst-∥f h refl P Q = refl

subst-⟪⟫f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (e : Tm (h x)) →
            subst (λ z → U.Proc (h z)) eq U.⟪ e ⟫ ≡ U.⟪ subst (λ z → Tm (h z)) eq e ⟫
subst-⟪⟫f h refl e = refl

subst-frame-plug : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (F : Frame* (h x)) (t : Tm (h x)) →
                   subst (λ z → Tm (h z)) eq (F [ t ]*)
                   ≡ subst (λ z → Frame* (h z)) eq F [ subst (λ z → Tm (h z)) eq t ]*
subst-frame-plug h refl F t = refl

subst-⊗f : (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) (a b : Tm (h x)) →
           subst (λ z → Tm (h z)) eq (a ⊗ b)
           ≡ subst (λ z → Tm (h z)) eq a ⊗ subst (λ z → Tm (h z)) eq b
subst-⊗f h refl a b = refl

transport-⋯t : {kk kk′ : ℕ} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′)
               (t : Tm (fg kk)) →
               subst (λ j → Tm (gg j)) eq (t ⋯ ρ kk)
               ≡ (subst (λ j → Tm (fg j)) eq t) ⋯ ρ kk′
transport-⋯t fg gg ρ refl t = refl

ss-U : ∀ {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) {t : U.Proc x} →
       subst U.Proc q (subst U.Proc p t) ≡ subst U.Proc (p ■ q) t
ss-U refl refl = refl

-- Bφ on the grown bind group equals Bφ on the ungrown one (the flag-list shapes
-- match; only the domain scope shifts by syncs-lwk).  Induction on B₁.
Bφ-lwk : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
         (Y : U.Proc (syncs (B₁ ++ suc b₁ ∷ B₂) + a)) →
         Bφ (B₁ ++ suc b₁ ∷ B₂) Y
         ≡ Bφ (B₁ ++ suc (suc b₁) ∷ B₂) (subst U.Proc (cong (_+ a) (syncs-lwk B₁)) Y)
Bφ-lwk []        {b₁} {[]}      Y = refl
Bφ-lwk []        {b₁} {b' ∷ B'} Y = refl
Bφ-lwk (a ∷ [])      {b₁} {B₂} {aa} Y =
  cong (U.φ ϕ[ a ])
    ( Bφ-lwk [] {b₁} {B₂} (subst U.Proc (sym (+-suc (syncs ([] ++ suc b₁ ∷ B₂)) aa)) Y)
    ■ cong (Bφ ([] ++ suc (suc b₁) ∷ B₂)) bodyeq )
  where
    aa-eq = cong (_+ aa) (syncs-lwk (a ∷ []) {b₁} {B₂})
    bodyeq : subst U.Proc (cong (_+ suc aa) (syncs-lwk [] {b₁} {B₂}))
               (subst U.Proc (sym (+-suc (syncs ([] ++ suc b₁ ∷ B₂)) aa)) Y)
             ≡ subst U.Proc (sym (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) aa))
                 (subst U.Proc aa-eq Y)
    bodyeq = ss-U (sym (+-suc (syncs ([] ++ suc b₁ ∷ B₂)) aa)) (cong (_+ suc aa) (syncs-lwk [] {b₁} {B₂})) {t = Y}
           ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
           ■ sym (ss-U aa-eq (sym (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) aa)) {t = Y})
Bφ-lwk (a ∷ d ∷ B₁″) {b₁} {B₂} {aa} Y =
  cong (U.φ ϕ[ a ])
    ( Bφ-lwk (d ∷ B₁″) {b₁} {B₂} (subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) aa)) Y)
    ■ cong (Bφ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) bodyeq )
  where
    aa-eq = cong (_+ aa) (syncs-lwk (a ∷ d ∷ B₁″) {b₁} {B₂})
    bodyeq : subst U.Proc (cong (_+ suc aa) (syncs-lwk (d ∷ B₁″) {b₁} {B₂}))
               (subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) aa)) Y)
             ≡ subst U.Proc (sym (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) aa))
                 (subst U.Proc aa-eq Y)
    bodyeq = ss-U (sym (+-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) aa)) (cong (_+ suc aa) (syncs-lwk (d ∷ B₁″) {b₁} {B₂})) {t = Y}
           ■ cong (λ e → subst U.Proc e Y) (uipℕ _ _)
           ■ sym (ss-U aa-eq (sym (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) aa)) {t = Y})

subst-wkB : ∀ (sB : ℕ) {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
            subst (λ j → Tm (sB + (j + N))) eq (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
            ≡ (subst (λ j → Tm (j + N)) eq t) ⋯ weaken* ⦃ Kᵣ ⦄ sB
subst-wkB sB refl t = refl

subst-cong+ : ∀ {a b N} (eq : a ≡ b) (t : Tm (a + N)) →
              subst Tm (cong (_+ N) eq) t ≡ subst (λ j → Tm (j + N)) eq t
subst-cong+ refl t = refl

-- leafσ on the grown bind group agrees with the transported ungrown leafσ away
-- from the consumed handle inj 0F (lwk just inserts the new data slot).
leafσ-lwk-id : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ B : BindGroup) (b₁ : ℕ)
               (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
               i ≢ TR.SplitRenamings.inj B₁ B₂ B {suc b₁ ∷ []} {m} 0F →
               subst (λ j → Tm (syncs B + (j + (2 + n)))) (syncs-lwk B₁)
                 (leafσ σ (B₁ ++ suc b₁ ∷ B₂) B i)
               ≡ leafσ σ (B₁ ++ suc (suc b₁) ∷ B₂) B (TR.SplitRenamings.lwk B₁ B₂ B i)
leafσ-lwk-id {m} {n} σ B₁ B₂ B b₁ i i≢
  with Fin.splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) i in seqo
... | inj₂ u
  rewrite leafσ-tail {n = n} σ (B₁ ++ suc b₁ ∷ B₂) B i u seqo
        | leafσ-tail {n = n} σ (B₁ ++ suc (suc b₁) ∷ B₂) B (TR.SplitRenamings.lwk B₁ B₂ B i) u
            (cong (Fin.splitAt (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B))
               (cong (TR.SplitRenamings.lwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo) ■ P3 B₁ B₂ B u)
            ■ Fin.splitAt-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) m u) = σ-coh
  where
    sA  = syncs (B₁ ++ suc b₁ ∷ B₂)
    sA′ = syncs (B₁ ++ suc (suc b₁) ∷ B₂)
    sB  = syncs B
    ieq : i ≡ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u
    ieq = sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i)
        ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo
    σfn : (j : ℕ) → Tm (sB + (j + (2 + n)))
    σfn j = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ j ⋯ weaken* ⦃ Kᵣ ⦄ sB
    σ-coh : subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwk B₁) (σfn sA) ≡ σfn sA′
    σ-coh = cohh (syncs-lwk B₁)
      where cohh : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (sB + (j + (2 + n)))) eq (σfn sA) ≡ σfn s′
            cohh refl = refl
... | inj₁ db with Fin.splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) db in seqi
...   | inj₂ w
  rewrite leafσ-B₁ σ (B₁ ++ suc b₁ ∷ B₂) B i db w seqo seqi
        | leafσ-B₁ σ (B₁ ++ suc (suc b₁) ∷ B₂) B (TR.SplitRenamings.lwk B₁ B₂ B i) (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) w
            (cong (Fin.splitAt (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B)) (cong (TR.SplitRenamings.lwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ P2 B₁ B₂ B w)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) (sum (B₁ ++ suc (suc b₁) ∷ B₂) ↑ʳ w) m)
            (Fin.splitAt-↑ʳ (sum (B₁ ++ suc (suc b₁) ∷ B₂)) (sum B) w) = canonB-coh
  where
    sA  = syncs (B₁ ++ suc b₁ ∷ B₂)
    sA′ = syncs (B₁ ++ suc (suc b₁) ∷ B₂)
    sB  = syncs B
    cfn : (j : ℕ) → Tm (sB + (j + (2 + n)))
    cfn j = canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ j 1F , K `unit) w
    canonB-coh : subst (λ j → Tm (sB + (j + (2 + n)))) (syncs-lwk B₁) (cfn sA) ≡ cfn sA′
    canonB-coh = cohh (syncs-lwk B₁)
      where cohh : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (sB + (j + (2 + n)))) eq (cfn sA) ≡ cfn s′
            cohh refl = refl
...   | inj₁ d
  rewrite leafσ-A₁ σ (B₁ ++ suc b₁ ∷ B₂) B i db d seqo seqi
        | leafσ-A₁ σ (B₁ ++ suc (suc b₁) ∷ B₂) B (TR.SplitRenamings.lwk B₁ B₂ B i) (dlwk B₁ b₁ B₂ d ↑ˡ sum B) (dlwk B₁ b₁ B₂ d)
            (cong (Fin.splitAt (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B)) (cong (TR.SplitRenamings.lwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ P1 B₁ B₂ B d)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ suc (suc b₁) ∷ B₂) + sum B) (dlwk B₁ b₁ B₂ d ↑ˡ sum B) m)
            (Fin.splitAt-↑ˡ (sum (B₁ ++ suc (suc b₁) ∷ B₂)) (dlwk B₁ b₁ B₂ d) (sum B)) =
      subst-wkB (syncs B) (syncs-lwk B₁) (canonₛ (B₁ ++ suc b₁ ∷ B₂) (K `unit , 0F , K `unit) d)
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
        ( sym (subst-cong+ (syncs-lwk B₁) (canonₛ (B₁ ++ suc b₁ ∷ B₂) (K `unit , 0F , K `unit) d))
        ■ canonₛ-lwk B₁ (K `unit , 0F , K `unit) b₁ B₂ d
            (λ d≡ → i≢ ((sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡)) )

substP-∘ : ∀ {kk kk′} (fg : ℕ → ℕ) (e : kk ≡ kk′) (X : U.Proc (fg kk)) →
           subst U.Proc (cong fg e) X ≡ subst (λ j → U.Proc (fg j)) e X
substP-∘ fg refl X = refl

transport-⋯ₚ : ∀ {kk kk′} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′) (X : U.Proc (fg kk)) →
               subst (λ j → U.Proc (gg j)) eq (X U.⋯ₚ ρ kk)
               ≡ (subst (λ j → U.Proc (fg j)) eq X) U.⋯ₚ ρ kk′
transport-⋯ₚ fg gg ρ refl X = refl

-- Grown-handle borrow-1 triple: the SECOND borrow of a grown (width ≥ 2) handle
-- chain, at flat position sum B₁ ↑ʳ 1F.  Mirrors canonₛ-handle (borrow-0) but at
-- index 1F; since the singleton leaf now DISTRIBUTES (Ub[ b+0 ]) the last chain
-- behaves like any Ub head (left slot *, right slot the threaded e₂/` 0F/*).
private
  substTripⱼ : ∀ {p q} (eq : p ≡ q) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
               subst Tm eq ((A ⊗ (` jj)) ⊗ C) ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
  substTripⱼ refl A jj C = refl
  toℕ-substᶠ : ∀ {p q} (e : p ≡ q) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
  toℕ-substᶠ refl y = refl
  -- lift a slot-equality (at scope suc N) through the +-suc scope-shuffle that
  -- canonₛ-handle / canonₛ-handle-b1 apply when peeling a B₁ chain (scope N).
  chainT : ∀ {N s s′} (e : s ≡ s′) {X : Tm (s + suc N)} {Y : Tm (s′ + suc N)} →
           subst Tm (cong (_+ suc N) e) X ≡ Y →
           subst Tm (cong (_+ N) (cong suc e)) (subst Tm (+-suc s N) X) ≡ subst Tm (+-suc s′ N) Y
  chainT {N} refl {X} refl = refl
  -- convert a borrow-1 computation stated at flat index 1F into the ↑ʳ-cast form
  -- canonₛ-handle-b1 needs (B₁ = [] case only).
  cast0-1F : ∀ {N} (w : ℕ) (B₂ : BindGroup) (cc : UChan N)
             {T : Tm (syncs (suc (suc w) ∷ B₂) + N)} →
             canonₛ (suc (suc w) ∷ B₂) cc 1F ≡ T →
             canonₛ (suc (suc w) ∷ B₂) cc
               (Fin.cast (sym (sum-++ [] (suc (suc w) ∷ B₂))) (sum [] ↑ʳ 1F)) ≡ T
  cast0-1F {N} w B₂ cc {T} eq =
    subst (λ z → canonₛ (suc (suc w) ∷ B₂) cc z ≡ T)
      (sym (Fin.toℕ-injective (Fin.toℕ-cast (sym (sum-++ [] (suc (suc w) ∷ B₂))) (sum [] ↑ʳ jj)
           ■ Fin.toℕ-↑ʳ (sum []) jj))) eq
    where jj : 𝔽 (sum (suc (suc w) ∷ B₂))
          jj = 1F

canonₛ-handle-b1 : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ a ∈ Tm (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
  Σ[ c ∈ Tm (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
  Σ[ j ∈ 𝔽 (syncs (B₁ ++ suc (suc b₁) ∷ B₂) + N) ]
    (canonₛ (B₁ ++ suc (suc b₁) ∷ B₂) (e₁ , x , e₂)
        (Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 1F))
       ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (B₁ ++ suc (suc b₁) ∷ B₂) + Fin.toℕ x)
canonₛ-handle-b1 [] {N} e₁ x e₂ zero []  =
  * , e₂ , x , cast0-1F zero [] (e₁ , x , e₂) refl , refl
canonₛ-handle-b1 [] {N} e₁ x e₂ (suc b₁) []  =
  * , * , x , cast0-1F (suc b₁) [] (e₁ , x , e₂) refl , refl
canonₛ-handle-b1 [] {N} e₁ x e₂ zero (c′ ∷ B) =
  subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , cast0-1F zero (c′ ∷ B) (e₁ , x , e₂) tripeq , junceq
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc (suc zero) ∷ c′ ∷ B) (e₁ , x , e₂) 1F
             ≡ (subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTripⱼ (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ■ toℕ-weaken*ᵣ sB (suc x) ■ +-suc sB (Fin.toℕ x)
canonₛ-handle-b1 [] {N} e₁ x e₂ (suc b₁) (c′ ∷ B) =
  subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))
  , cast0-1F (suc b₁) (c′ ∷ B) (e₁ , x , e₂) tripeq , junceq
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc (suc (suc b₁)) ∷ c′ ∷ B) (e₁ , x , e₂) 1F
             ≡ (subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
                 ⊗ (` subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))))
                 ⊗ subst Tm (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTripⱼ (+-suc sB N) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (weaken* ⦃ Kᵣ ⦄ sB (suc x)) ■ toℕ-weaken*ᵣ sB (suc x) ■ +-suc sB (Fin.toℕ x)
canonₛ-handle-b1 (a ∷ [])      {N} e₁ x e₂ b₁ B₂
  with canonₛ-handle-b1 [] (` 0F) (suc x) (wk e₂) b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq , junceq
  where
    sB = syncs ([] ++ suc (suc b₁) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ []) (suc (suc b₁) ∷ B₂))) (sum (a ∷ []) ↑ʳ 1F)
    cp′ = Fin.cast (sym (sum-++ [] (suc (suc b₁) ∷ B₂))) (sum [] ↑ʳ 1F)
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a [] (suc (suc b₁)) B₂ 1F)
            ■ Fin.splitAt-↑ʳ a (sum ([] ++ suc (suc b₁) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ [] ++ suc (suc b₁) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ ([] ++ suc (suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripⱼ (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec))) ■ +-suc sB (Fin.toℕ x)
canonₛ-handle-b1 (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂
  with canonₛ-handle-b1 (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂
... | rec =
  subst Tm (+-suc sB N) (proj₁ rec)
  , subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
  , subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
  , tripeq , junceq
  where
    sB = syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)
    cp  = Fin.cast (sym (sum-++ (a ∷ d ∷ B₁″) (suc (suc b₁) ∷ B₂))) (sum (a ∷ d ∷ B₁″) ↑ʳ 1F)
    cp′ = Fin.cast (sym (sum-++ (d ∷ B₁″) (suc (suc b₁) ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 1F)
    spliteq : Fin.splitAt a cp ≡ inj₂ cp′
    spliteq = cong (Fin.splitAt a) (pos-split-gen a (d ∷ B₁″) (suc (suc b₁)) B₂ 1F)
            ■ Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) cp′
    tripeq : canonₛ (a ∷ (d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) (e₁ , x , e₂) cp
             ≡ (subst Tm (+-suc sB N) (proj₁ rec)
                 ⊗ (` subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))))
                 ⊗ subst Tm (+-suc sB N) (proj₁ (proj₂ rec))
    tripeq = cong (subst Tm (+-suc sB N))
               (cong [ Ub[ a ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB
                     , canonₛ ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂) (` 0F , suc x , wk e₂) ]′ spliteq
               ■ proj₁ (proj₂ (proj₂ (proj₂ rec))))
           ■ substTripⱼ (+-suc sB N) (proj₁ rec) (proj₁ (proj₂ (proj₂ rec))) (proj₁ (proj₂ rec))
    junceq : Fin.toℕ (subst 𝔽 (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))) ≡ suc sB + Fin.toℕ x
    junceq = toℕ-substᶠ (+-suc sB N) (proj₁ (proj₂ (proj₂ rec)))
           ■ proj₂ (proj₂ (proj₂ (proj₂ rec))) ■ +-suc sB (Fin.toℕ x)

-- ungrown handle left slot = grown handle borrow-0 left slot (invariant under growth).
handle-L-lwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (_+ N) (syncs-lwk B₁))
    (proj₁ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂))
  ≡ proj₁ (canonₛ-handle B₁ e₁ x e₂ (suc b₁) B₂)
handle-L-lwk []        {N} e₁ x e₂ zero    []      = refl
handle-L-lwk []        {N} e₁ x e₂ (suc b₁) []      = refl
handle-L-lwk []        {N} e₁ x e₂ zero    (c′ ∷ B) = refl
handle-L-lwk []        {N} e₁ x e₂ (suc b₁) (c′ ∷ B) = refl
handle-L-lwk (a ∷ [])      {N} e₁ x e₂ b₁ B₂ =
  chainT (syncs-lwk [] {b₁} {B₂}) (handle-L-lwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
handle-L-lwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
  chainT (syncs-lwk (d ∷ B₁″) {b₁} {B₂}) (handle-L-lwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)

-- ungrown handle right slot = grown handle borrow-1 right slot.
handle-R-lwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (_+ N) (syncs-lwk B₁))
    (proj₁ (proj₂ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂)))
  ≡ proj₁ (proj₂ (canonₛ-handle-b1 B₁ e₁ x e₂ b₁ B₂))
handle-R-lwk []        {N} e₁ x e₂ zero    []      = refl
handle-R-lwk []        {N} e₁ x e₂ (suc b₁) []      = refl
handle-R-lwk []        {N} e₁ x e₂ zero    (c′ ∷ B) = refl
handle-R-lwk []        {N} e₁ x e₂ (suc b₁) (c′ ∷ B) = refl
handle-R-lwk (a ∷ [])      {N} e₁ x e₂ b₁ B₂ =
  chainT (syncs-lwk [] {b₁} {B₂}) (handle-R-lwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
handle-R-lwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
  chainT (syncs-lwk (d ∷ B₁″) {b₁} {B₂}) (handle-R-lwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)

-- grown handle borrow-0 right slot is * (width ≥ 2 drops e₂).
handle-R0-* : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (proj₂ (canonₛ-handle B₁ e₁ x e₂ (suc b₁) B₂)) ≡ *
handle-R0-* []        {N} e₁ x e₂ b₁ []      = refl
handle-R0-* []        {N} e₁ x e₂ b₁ (c′ ∷ B) = subst-Kunit (+-suc (syncs (c′ ∷ B)) N)
handle-R0-* (a ∷ [])      {N} e₁ x e₂ b₁ B₂ =
  cong (subst Tm (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) N)) (handle-R0-* [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) N)
handle-R0-* (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
  cong (subst Tm (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) N)) (handle-R0-* (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) N)

-- grown handle borrow-1 left slot is * (distributing head/leaf both drop the left slot).
handle-b1-L-* : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (canonₛ-handle-b1 B₁ e₁ x e₂ b₁ B₂) ≡ *
handle-b1-L-* []        {N} e₁ x e₂ zero    []      = refl
handle-b1-L-* []        {N} e₁ x e₂ (suc b₁) []      = refl
handle-b1-L-* []        {N} e₁ x e₂ zero    (c′ ∷ B) = subst-Kunit (+-suc (syncs (c′ ∷ B)) N)
handle-b1-L-* []        {N} e₁ x e₂ (suc b₁) (c′ ∷ B) = subst-Kunit (+-suc (syncs (c′ ∷ B)) N)
handle-b1-L-* (a ∷ [])      {N} e₁ x e₂ b₁ B₂ =
  cong (subst Tm (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) N)) (handle-b1-L-* [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ([] ++ suc (suc b₁) ∷ B₂)) N)
handle-b1-L-* (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
  cong (subst Tm (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) N)) (handle-b1-L-* (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ subst-Kunit (+-suc (syncs ((d ∷ B₁″) ++ suc (suc b₁) ∷ B₂)) N)


open T using (_;_⊢ₚ_)

-- Ported frame-cong / frame-fusion-gen (verbatim from Simulation2.Theorems).
app₁-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ L → Value e₁} {V₂ : d ≡ L → Value e₂}
          → e₁ ≡ e₂ → app₁ e₁ d V₁ ≡ app₁ e₂ d V₂
app₁-cong refl = cong (app₁ _ _) (funext (λ x → Value-irr))

app₂-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ 𝟙 ⊎ d ≡ R → Value e₁} {V₂ : d ≡ 𝟙 ⊎ d ≡ R → Value e₂}
          → e₁ ≡ e₂ → app₂ e₁ d V₁ ≡ app₂ e₂ d V₂
app₂-cong refl = cong (app₂ _ _) (funext (λ x → Value-irr))

⊗□-cong : {e₁ e₂ : Tm n} {V₁ : Value e₁} {V₂ : Value e₂} → e₁ ≡ e₂ → (V₁ ⊗□) ≡ (V₂ ⊗□)
⊗□-cong refl = cong _⊗□ Value-irr

frame-cong : (E : Frame m) {ϕ ψ : m →ₛ n} (Vϕ : VSub ϕ) (Vψ : VSub ψ) → ϕ ≗ ψ →
             frame-⋯ E ϕ Vϕ ≡ frame-⋯ E ψ Vψ
frame-cong (app₁ e₂ d V?) Vϕ Vψ eq = app₁-cong (⋯-cong e₂ eq)
frame-cong (app₂ e₁ d V?) Vϕ Vψ eq = app₂-cong (⋯-cong e₁ eq)
frame-cong (□⊗ e₂)        Vϕ Vψ eq = cong □⊗_ (⋯-cong e₂ eq)
frame-cong (V₁ ⊗□)        Vϕ Vψ eq = ⊗□-cong (⋯-cong (vTm V₁) eq)
frame-cong (□; e₂)        Vϕ Vψ eq = cong □;_ (⋯-cong e₂ eq)
frame-cong (`let-`in e′)  Vϕ Vψ eq = cong `let-`in_ (⋯-cong e′ (eq ~↑))
frame-cong (`let⊗-`in e′) Vϕ Vψ eq = cong `let⊗-`in_ (⋯-cong e′ (eq ~↑* 2))
frame-cong (`inj□ i)      Vϕ Vψ eq = refl
frame-cong (`case□`of⟨ e₁ ; e₂ ⟩) Vϕ Vψ eq =
  cong₂ `case□`of⟨_;_⟩ (⋯-cong e₁ (eq ~↑)) (⋯-cong e₂ (eq ~↑))

frame-fusion-gen : ∀ {𝓕₁ 𝓕₂ 𝓕} ⦃ K₁ : Kit 𝓕₁ ⦄ ⦃ K₂ : Kit 𝓕₂ ⦄ ⦃ K : Kit 𝓕 ⦄ ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : CKit K₁ K₂ K ⦄ {m₁ p}
                   (E : Frame m) {ϕ : m –[ K₁ ]→ m₁} (Vϕ : VSub ϕ) {ξ : m₁ –[ K₂ ]→ p} (Vξ : VSub ξ)
                   (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                   frame-⋯ (frame-⋯ E ϕ Vϕ) ξ Vξ ≡ frame-⋯ E (ϕ ·ₖ ξ) Vϕξ
frame-fusion-gen (app₁ e₂ d V?) {ϕ} Vϕ {ξ} Vξ Vϕξ = app₁-cong (fusion e₂ ϕ ξ)
frame-fusion-gen (app₂ e₁ d V?) {ϕ} Vϕ {ξ} Vξ Vϕξ = app₂-cong (fusion e₁ ϕ ξ)
frame-fusion-gen (□⊗ e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □⊗_ (fusion e₂ ϕ ξ)
frame-fusion-gen (V₁ ⊗□)        {ϕ} Vϕ {ξ} Vξ Vϕξ = ⊗□-cong (fusion (vTm V₁) ϕ ξ)
frame-fusion-gen (□; e₂)        {ϕ} Vϕ {ξ} Vξ Vϕξ = cong □;_ (fusion e₂ ϕ ξ)
frame-fusion-gen (`let-`in e′)  {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let-`in_ (fusion e′ (ϕ ↑) (ξ ↑) ■ ⋯-cong e′ (λ x → sym (dist-↑-· ϕ ξ x)))
frame-fusion-gen (`let⊗-`in e′) {ϕ} Vϕ {ξ} Vξ Vϕξ = cong `let⊗-`in_ (fusion e′ (ϕ ↑* 2) (ξ ↑* 2) ■ ⋯-cong e′ (λ x → sym (dist-↑*-· 2 ϕ ξ x)))
frame-fusion-gen (`inj□ i)      {ϕ} Vϕ {ξ} Vξ Vϕξ = refl
frame-fusion-gen (`case□`of⟨ e₁ ; e₂ ⟩) {ϕ} Vϕ {ξ} Vξ Vϕξ =
  cong₂ `case□`of⟨_;_⟩ (fusion e₁ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₁ (λ x → sym (dist-↑-· ϕ ξ x)))
                        (fusion e₂ (ϕ ↑) (ξ ↑) ■ ⋯-cong e₂ (λ x → sym (dist-↑-· ϕ ξ x)))

-- The two exported simulation cases.

-- | Frame-level analogues of the U-cong / U-⋯p / transport helpers used in
--   PrestRec, for the FRAME side of redexRec (ccEqR).

frame*-cong : (E : Frame* m) {σ τ : m →ₛ n} (Vσ : VSub σ) (Vτ : VSub τ) → σ ≗ τ →
              frame*-⋯ E σ Vσ ≡ frame*-⋯ E τ Vτ
frame*-cong []       Vσ Vτ eq = refl
frame*-cong (F ∷ E*) Vσ Vτ eq = cong₂ _∷_ (frame-cong F Vσ Vτ eq) (frame*-cong E* Vσ Vτ eq)

-- frame*-⋯ of a frame renaming fuses into the substitution (frame analogue of U-⋯p).
F-⋯f*-fuse : (E : Frame* m) {p : ℕ} {ρ : m →ᵣ p} {τ : p →ₛ n} (Vτ : VSub τ) (Vρτ : VSub (ρ ·ₖ τ)) →
             frame*-⋯ (E ⋯ᶠ* ρ) τ Vτ ≡ frame*-⋯ E (ρ ·ₖ τ) Vρτ
F-⋯f*-fuse []       Vτ Vρτ = refl
F-⋯f*-fuse (F ∷ E*) {ρ} {τ} Vτ Vρτ =
  cong₂ _∷_ (frame-fusion-gen F (λ _ → V-`) Vτ Vρτ) (F-⋯f*-fuse E* Vτ Vρτ)

subst-VSub : {a : ℕ} (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y) {σ : a →ₛ h x} → VSub σ →
             VSub (subst (λ z → a →ₛ h z) eq σ)
subst-VSub h refl V = V

·ₖ-VSubᵣ : {m p n : ℕ} (ρ : m →ᵣ p) {τ : p →ₛ n} → VSub τ → VSub (ρ ·ₖ τ)
·ₖ-VSubᵣ ρ {τ} Vτ i = Vτ (ρ i)

-- transport of frame*-⋯ along a codomain scope equality (frame analogue of U-cod-transport).
F-cod-transport : {a : ℕ} (E : Frame* a) (h : ℕ → ℕ) {x y : ℕ} (eq : x ≡ y)
                  {σ : a →ₛ h x} (Vσ : VSub σ) →
                  subst (λ z → Frame* (h z)) eq (frame*-⋯ E σ Vσ)
                  ≡ frame*-⋯ E (subst (λ z → a →ₛ h z) eq σ) (subst-VSub h eq Vσ)
F-cod-transport E h refl Vσ = refl

substF-⋯ : {kk kk′ : ℕ} (fg : ℕ → ℕ) (e : kk ≡ kk′) (E : Frame* (fg kk)) →
           subst Frame* (cong fg e) E ≡ subst (λ j → Frame* (fg j)) e E
substF-⋯ fg refl E = refl

transport-⋯f* : {kk kk′ : ℕ} (fg gg : ℕ → ℕ) (ρ : ∀ j → fg j →ᵣ gg j) (eq : kk ≡ kk′)
                (E : Frame* (fg kk)) →
                subst (λ j → Frame* (gg j)) eq (E ⋯ᶠ* ρ kk)
                ≡ (subst (λ j → Frame* (fg j)) eq E) ⋯ᶠ* ρ kk′
transport-⋯f* fg gg ρ refl E = refl


U-lsplit : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {B₁ B₂ B : BindGroup} {b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → {P : T.Proc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     Γ ; γ ⊢ₚ T.ν (B₁ ++ suc b₁ ∷ B₂) B
                 (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P))
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       UR─→ₚ*
      U[ T.ν (B₁ ++ suc (suc b₁) ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)) ] σ)
     ⊎
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       U.≋
      U[ T.ν (B₁ ++ suc (suc b₁) ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)) ] σ))
U-lsplit {m} {n} σ Vσ Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with lsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq = ≋-wrap-⊎ front fire back
  where
    module 𝐒 = TR.SplitRenamings B₁ B₂ B
    C₁ C₁′ : BindGroup
    C₁  = B₁ ++ suc b₁ ∷ B₂
    C₁′ = B₁ ++ suc (suc b₁) ∷ B₂
    QL : T.Proc (sum C₁ + sum B + m)
    QL = T.⟪ E [ K (`lsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P
    QR : T.Proc (sum C₁′ + sum B + m)
    QR = T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.lwk)
    sA sA′ sB : ℕ
    sA  = syncs C₁
    sA′ = syncs C₁′
    sB  = syncs B
    τ : sum C₁ + sum B + m →ₛ syncs B + (syncs C₁ + (2 + n))
    τ = leafσ σ C₁ B
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    push : ∀ {kk} → U.Proc (sB + (sA + (2 + kk))) → U.Proc (2 + (sB + (sA + kk)))
    push {kk} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    XL : U.Proc (sB + (sA + (2 + n)))
    XL = U[ QL ] τ
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ C₁ (Bφ B X)) U.≋ Bφ C₁ (Bφ B (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ C₁ (Bφ B X)
      ◅◅ Bφ-cong C₁ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong C₁ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν C₁ B QL ] σ U.≋ Bφ C₁ (Bφ B (U.ν (push XL)))
    front = ≡→≋ (Uν-flat σ C₁ B QL) ◅◅ ν↓ XL
    castpos : 𝔽 (sum C₁)
    castpos = Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
    -- the lsplit handle translated at the leaf.
    hc = canonₛ-handle B₁ (K `unit) 0F (K `unit) b₁ B₂
    cc : Tm (2 + (sB + (sA + n)))
    cc = rn (τ (𝐒.inj 0F))
    -- τ (inj 0F) = canonₛ C₁ cc1 castpos ⋯ weaken* sB
    τinj0 : τ (𝐒.inj 0F) ≡ canonₛ C₁ (K `unit , 0F , K `unit) castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τinj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
    ccTriple : cc ≡ ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` 0F))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
    ccTriple =
        cong rn (τinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc)))))
      ■ cong (λ z → ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` z))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂))
          (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc))))
    Fr : Frame* (2 + (sB + (sA + n)))
    Fr = (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ P ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    threadEq : (Ef : Frame* (sum C₁ + sum B + m)) (p : Tm (sum C₁ + sum B + m)) →
               (U[ T.⟪ Ef [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* Ef τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ Ef τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    YL≡ : push XL ≡ U.⟪ Fr [ K (`lsplit s) ·¹ cc ]* ⟫ U.∥ RP
    YL≡ = cong₂ U._∥_
            (threadEq E (K (`lsplit s) ·¹ (` 𝐒.inj 0F)))
            refl
    ccA ccC : Tm (2 + (sB + (sA + n)))
    ccA = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccC = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccL0 ccR0 : Tm (2 + (sB + (sA + n)))
    ccL0 = ((ccA ⊗ (` 0F)) ⊗ *)
    ccR0 = ((* ⊗ (` 0F)) ⊗ ccC)
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = U.⟪ Fr [ K (`lsplit s) ·¹ cc ]* ⟫ U.∥ RP
    contractumR : U.Proc (2 + (sB + (sA + n)))
    contractumR = U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫ U.∥ RP
    lsplitStep : U.ν redexL UR.─→ₚ U.ν contractumR
    lsplitStep = subst (λ z → U.ν (U.⟪ Fr [ K (`lsplit s) ·¹ z ]* ⟫ U.∥ RP)
                              UR.─→ₚ U.ν contractumR)
                   (sym ccTriple) (UR.RU-LSplit {e₁ = ccA} {e₂ = ccC} Fr)
    leaf-fire : U.ν (push XL) UR.─→ₚ U.ν contractumR
    leaf-fire = UR.RU-Struct (U.ν-cong (≡→≋ YL≡)) lsplitStep ε
    fire : Bφ C₁ (Bφ B (U.ν (push XL))) UR─→ₚ* Bφ C₁ (Bφ B (U.ν contractumR))
    fire = Bφ-lift-step C₁ (Bφ-lift-step B leaf-fire) ◅ ε
    τ′ : sum C₁′ + sum B + m →ₛ syncs B + (syncs C₁′ + (2 + n))
    τ′ = leafσ σ C₁′ B
    Vτ′ : VSub τ′
    Vτ′ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁′ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA′ 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA′) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    XR′ : U.Proc (sB + (sA′ + (2 + n)))
    XR′ = U[ QR ] τ′
    pushR : ∀ {kk} → U.Proc (sB + (sA′ + (2 + kk))) → U.Proc (2 + (sB + (sA′ + kk)))
    pushR {kk} X = (X U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ν↓′ : ∀ (X : U.Proc (sB + (sA′ + (2 + n)))) →
          U.ν (Bφ C₁′ (Bφ B X)) U.≋ Bφ C₁′ (Bφ B (U.ν (pushR X)))
    ν↓′ X =
         ν-past-Bφ C₁′ (Bφ B X)
      ◅◅ Bφ-cong C₁′ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA′ 2))))
      ◅◅ Bφ-cong C₁′ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)))
    rhs : U[ T.ν C₁′ B QR ] σ U.≋ Bφ C₁′ (Bφ B (U.ν (pushR XR′)))
    rhs = ≡→≋ (Uν-flat σ C₁′ B QR) ◅◅ ν↓′ XR′
    e1 : sA ≡ sA′
    e1 = syncs-lwk B₁
    -- the transported contractum at the leaf must match pushR XR′.
    eqP : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
    eqP = cong (2 +_) (cong (sB +_) (cong (_+ n) e1))
    pushR-thread : U.Proc (2 + (sB + (sA′ + n)))
    pushR-thread = (U[ T.⟪ E ⋯ᶠ* 𝐒.lwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ ] τ′ U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    pushR-P : U.Proc (2 + (sB + (sA′ + n)))
    pushR-P = (U[ P T.⋯ₚ 𝐒.lwk ] τ′ U.⋯ₚ (assocSwapᵣ sA′ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ρ₁′ : (sB + (sA′ + (2 + n))) →ᵣ (sB + (2 + (sA′ + n)))
    ρ₁′ = assocSwapᵣ sA′ 2 ↑* sB
    ρ₂′ : (sB + (2 + (sA′ + n))) →ᵣ (2 + (sB + (sA′ + n)))
    ρ₂′ = assocSwapᵣ sB 2
    rn′ : Tm (sB + (sA′ + (2 + n))) → Tm (2 + (sB + (sA′ + n)))
    rn′ t = (t ⋯ ρ₁′) ⋯ ρ₂′
    Fr′ : Frame* (2 + (sB + (sA′ + n)))
    Fr′ = (frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′ ⋯ᶠ* ρ₁′) ⋯ᶠ* ρ₂′
    threadEq′ : (Ef : Frame* (sum C₁′ + sum B + m)) (p : Tm (sum C₁′ + sum B + m)) →
                (U[ T.⟪ Ef [ p ]* ⟫ ] τ′ U.⋯ₚ ρ₁′) U.⋯ₚ ρ₂′
                ≡ U.⟪ ((frame*-⋯ Ef τ′ Vτ′ ⋯ᶠ* ρ₁′) ⋯ᶠ* ρ₂′) [ rn′ (p ⋯ τ′) ]* ⟫
    threadEq′ Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁′) ⋯ ρ₂′) (frame-plug* Ef τ′ Vτ′)
      ■ cong (_⋯ ρ₂′) (frame-plug*ᵣ (frame*-⋯ Ef τ′ Vτ′) ρ₁′)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ′ Vτ′ ⋯ᶠ* ρ₁′) ρ₂′ )
    pushR-threadEq : pushR-thread ≡ U.⟪ Fr′ [ rn′ (τ′ (𝐒.inj 0F)) ⊗ rn′ (τ′ (𝐒.inj 1F)) ]* ⟫
    pushR-threadEq = threadEq′ (E ⋯ᶠ* 𝐒.lwk) ((` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F))
    -- the grown handle (inj 0F in C₁′), pushed, has junction 0F: same chanTriple shape as cc.
    hc′ = canonₛ-handle B₁ {N = 2 + n} (K `unit) 0F (K `unit) (suc b₁) B₂
    castpos′ : 𝔽 (sum C₁′)
    castpos′ = Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 0F)
    τ′inj0 : τ′ (𝐒.inj 0F) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos′ ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τ′inj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos′ ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos′ (sum B))
    ccEqR : subst U.Proc eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) ≡ pushR-thread
    ccEqR =
        cong (λ pf → subst U.Proc pf (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫)) (uipℕ eqP eqPh)
      ■ substP-∘ hF e1 (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫)
      ■ subst-⟪⟫f hF e1 (Fr [ ccL0 ⊗ ccR0 ]*)
      ■ cong U.⟪_⟫ (subst-frame-plug hF e1 Fr (ccL0 ⊗ ccR0))
      ■ cong U.⟪_⟫ (cong₂ _[_]* frameTransport bodyTransport)
      ■ sym pushR-threadEq
      where
        hF : ℕ → ℕ
        hF j = 2 + (sB + (j + n))
        eqPh : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
        eqPh = cong hF e1
        frameLeafeq : subst (λ j → Frame* (sB + (j + (2 + n)))) e1 (frame*-⋯ E τ Vτ)
                      ≡ frame*-⋯ (E ⋯ᶠ* 𝐒.lwk) τ′ Vτ′
        frameLeafeq =
            F-cod-transport E (λ j → sB + (j + (2 + n))) e1 Vτ
          ■ cong (λ EE → frame*-⋯ EE (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)
                            (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)) Eeq
          ■ F-⋯f*-fuse E₀ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ)
                       (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
          ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ (subst-VSub (λ j → sB + (j + (2 + n))) e1 Vτ))
                           (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
              (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                   ■ leafσ-lwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y))
          ■ sym (F-⋯f*-fuse E₀ (·ₖ-VSubᵣ 𝐒.lwk Vτ′) (·ₖ-VSubᵣ ρ⁻ (·ₖ-VSubᵣ 𝐒.lwk Vτ′)))
          ■ cong (λ EE → frame*-⋯ EE (𝐒.lwk ·ₖ τ′) (·ₖ-VSubᵣ 𝐒.lwk Vτ′)) (sym Eeq)
          ■ sym (F-⋯f*-fuse E Vτ′ (·ₖ-VSubᵣ 𝐒.lwk Vτ′))
          where
            substσ-app : (h : ℕ → ℕ) {x yy : ℕ} (eq : x ≡ yy) {aa : ℕ} (ϱ : aa →ₛ h x) (i : 𝔽 aa) →
                         subst (λ j → aa →ₛ h j) eq ϱ i ≡ subst (λ j → Tm (h j)) eq (ϱ i)
            substσ-app h refl ϱ i = refl
        frameTransport : subst (λ j → Frame* (hF j)) e1 Fr ≡ Fr′
        frameTransport =
            transport-⋯f* (λ j → sB + (2 + (j + n))) hF (λ j → assocSwapᵣ sB 2 {j + n}) e1 (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁)
          ■ cong (λ z → z ⋯ᶠ* assocSwapᵣ sB 2 {sA′ + n})
              ( transport-⋯f* (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) (λ j → assocSwapᵣ j 2 {n} ↑* sB) e1 (frame*-⋯ E τ Vτ)
              ■ cong (λ z → z ⋯ᶠ* (assocSwapᵣ sA′ 2 {n} ↑* sB)) frameLeafeq )
        castpos1′ : 𝔽 (sum C₁′)
        castpos1′ = Fin.cast (sym (sum-++ B₁ (suc (suc b₁) ∷ B₂))) (sum B₁ ↑ʳ 1F)
        τ′inj1 : τ′ (𝐒.inj 1F) ≡ canonₛ C₁′ (K `unit , 0F , K `unit) castpos1′ ⋯ weaken* {{ Kᵣ }} sB
        τ′inj1 =
            cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′ + sum B) (castpos1′ ↑ˡ sum B) m)
          ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁′) castpos1′ (sum B))
        -- grown handle borrow-1 triple (left slot *, right slot = grown borrow-1 R-slot).
        hb1 = canonₛ-handle-b1 B₁ {N = 2 + n} (K `unit) 0F (K `unit) b₁ B₂
        -- pushed grown borrow-0 triple: right slot is * (grown width ≥ 2).
        hc′triple : rn′ (τ′ (𝐒.inj 0F))
                    ≡ ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                      ⊗ (proj₁ (proj₂ hc′) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        hc′triple =
            cong rn′ (τ′inj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc′)))))
          ■ cong (λ z → ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` z))
                        ⊗ (proj₁ (proj₂ hc′) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
              (Fin.toℕ-injective (assocPush-junc sA′ sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′)))) jvtoℕ′ (Nat.s≤s Nat.z≤n)))
          where
            jvtoℕ′ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc′)))) ≡ sB + (sA′ + 0)
            jvtoℕ′ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc′))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc′))))
        -- pushed grown borrow-1 triple.
        hc′triple1 : rn′ (τ′ (𝐒.inj 1F))
                     ≡ ((proj₁ hb1 ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                       ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        hc′triple1 =
            cong rn′ (τ′inj1 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hb1)))))
          ■ cong (λ z → ((proj₁ hb1 ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` z))
                        ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
              (Fin.toℕ-injective (assocPush-junc sA′ sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1)))) jv1toℕ (Nat.s≤s Nat.z≤n)))
          where
            jv1toℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hb1)))) ≡ sB + (sA′ + 0)
            jv1toℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hb1))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hb1))))
        -- slot correspondences under handle growth.
        L-inv : subst Tm (cong (_+ (2 + n)) e1) (proj₁ hc) ≡ proj₁ hc′
        L-inv = handle-L-lwk B₁ (K `unit) 0F (K `unit) b₁ B₂
        R0-* : proj₁ (proj₂ hc′) ≡ *
        R0-* = handle-R0-* B₁ (K `unit) 0F (K `unit) b₁ B₂
        R-corr : subst Tm (cong (_+ (2 + n)) e1) (proj₁ (proj₂ hc)) ≡ proj₁ (proj₂ hb1)
        R-corr = handle-R-lwk B₁ (K `unit) 0F (K `unit) b₁ B₂
        L0-* : proj₁ hb1 ≡ *
        L0-* = handle-b1-L-* B₁ (K `unit) 0F (K `unit) b₁ B₂
        -- push a single ungrown slot (with its wk sB) forward to the grown side.
        pushSlot : (t : Tm (sA + (2 + n))) {t′ : Tm (sA′ + (2 + n))}
                   → subst Tm (cong (_+ (2 + n)) e1) t ≡ t′
                   → subst (λ j → Tm (hF j)) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
                     ≡ (t′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
        pushSlot t {t′} et =
            transport-⋯t (λ j → sB + (2 + (j + n))) hF (λ j → assocSwapᵣ sB 2 {j + n}) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁)
          ■ cong (_⋯ assocSwapᵣ sB 2 {sA′ + n})
              ( transport-⋯t (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) (λ j → assocSwapᵣ j 2 {n} ↑* sB) e1 (t ⋯ weaken* ⦃ Kᵣ ⦄ sB)
              ■ cong (_⋯ (assocSwapᵣ sA′ 2 {n} ↑* sB))
                  ( subst-wkB sB e1 t
                  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (sym (subst-cong+ e1 t) ■ et) ) )
        pushJunc : subst (λ j → Tm (hF j)) e1 (` 0F) ≡ (` 0F)
        pushJunc = go e1
          where go : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (2 + (sB + (j + n)))) eq (` 0F) ≡ (` 0F)
                go refl = refl
        pushKunit : subst (λ j → Tm (hF j)) e1 * ≡ *
        pushKunit = go e1
          where go : ∀ {s′} (eq : sA ≡ s′) → subst (λ j → Tm (2 + (sB + (j + n)))) eq * ≡ *
                go refl = refl
        bodyTransport : subst (λ j → Tm (hF j)) e1 (ccL0 ⊗ ccR0)
                        ≡ rn′ (τ′ (𝐒.inj 0F)) ⊗ rn′ (τ′ (𝐒.inj 1F))
        bodyTransport =
            subst-⊗f hF e1 ccL0 ccR0
          ■ cong₂ _⊗_
              ( subst-⊗f hF e1 (ccA ⊗ (` 0F)) *
              ■ cong₂ _⊗_ (subst-⊗f hF e1 ccA (` 0F) ■ cong₂ _⊗_ (pushSlot (proj₁ hc) L-inv) pushJunc)
                          pushKunit
              ■ sym hc′triple₀ )
              ( subst-⊗f hF e1 (* ⊗ (` 0F)) ccC
              ■ cong₂ _⊗_ (subst-⊗f hF e1 * (` 0F) ■ cong₂ _⊗_ pushKunit pushJunc)
                          (pushSlot (proj₁ (proj₂ hc)) R-corr)
              ■ sym hc′triple1₀ )
          where
            -- grown borrow-0 triple with right slot rewritten to *.
            hc′triple₀ : rn′ (τ′ (𝐒.inj 0F))
                         ≡ ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F)) ⊗ *
            hc′triple₀ = hc′triple
              ■ cong (λ z → ((proj₁ hc′ ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F)) ⊗ z)
                  (cong (λ w → w ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) R0-*)
            -- grown borrow-1 triple with left slot rewritten to *.
            hc′triple1₀ : rn′ (τ′ (𝐒.inj 1F))
                          ≡ ((* ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                            ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′)
            hc′triple1₀ = hc′triple1
              ■ cong (λ z → ((z ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′) ⊗ (` 0F))
                            ⊗ (proj₁ (proj₂ hb1) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁′ ⋯ ρ₂′))
                  L0-*
    redexRec : subst U.Proc eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) ≡ pushR-thread
    redexRec = ccEqR
    ρ₂F : (j : ℕ) → (sB + (2 + (j + n))) →ᵣ (2 + (sB + (j + n)))
    ρ₂F j = assocSwapᵣ sB 2 {j + n}
    ρ₁F : (j : ℕ) → (sB + (j + (2 + n))) →ᵣ (sB + (2 + (j + n)))
    ρ₁F j = assocSwapᵣ j 2 {n} ↑* sB
    Pleafeq : subst (λ j → U.Proc (sB + (j + (2 + n)))) e1 (U[ P ] τ) ≡ U[ P T.⋯ₚ 𝐒.lwk ] τ′
    Pleafeq =
        U-cod-transport P (λ j → sB + (j + (2 + n))) e1 τ
      ■ cong (λ p → U[ p ] (subst (λ j → (sum C₁ + sum B + m) →ₛ (sB + (j + (2 + n)))) e1 τ)) Peq
      ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → substσ-app (λ j → sB + (j + (2 + n))) e1 τ (ρ⁻ y)
                       ■ leafσ-lwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y))
      ■ sym (U-⋯ₚ P₀)
      ■ cong (λ p → U[ p ] (𝐒.lwk ·ₖ τ′)) (sym Peq)
      ■ sym (U-⋯ₚ P)
      where
        substσ-app : (h : ℕ → ℕ) {x yy : ℕ} (eq : x ≡ yy) {aa : ℕ} (ρ : aa →ₛ h x) (i : 𝔽 aa) →
                     subst (λ j → aa →ₛ h j) eq ρ i ≡ subst (λ j → Tm (h j)) eq (ρ i)
        substσ-app h refl ρ i = refl
    eqP′ : (2 + (sB + (sA + n))) ≡ (2 + (sB + (sA′ + n)))
    eqP′ = cong (λ j → 2 + (sB + (j + n))) e1
    PrestRec : subst U.Proc eqP RP ≡ pushR-P
    PrestRec =
        cong (λ pf → subst U.Proc pf RP) (uipℕ eqP eqP′)
      ■ substP-∘ (λ j → 2 + (sB + (j + n))) e1 RP
      ■ transport-⋯ₚ (λ j → sB + (2 + (j + n))) (λ j → 2 + (sB + (j + n))) ρ₂F e1 (U[ P ] τ U.⋯ₚ ρ₁)
      ■ cong (λ z → z U.⋯ₚ ρ₂F sA′)
          ( transport-⋯ₚ (λ j → sB + (j + (2 + n))) (λ j → sB + (2 + (j + n))) ρ₁F e1 (U[ P ] τ)
          ■ cong (λ z → z U.⋯ₚ ρ₁F sA′) Pleafeq )
    bodyReconcile : subst U.Proc eqP contractumR
                    U.≋ pushR XR′
    bodyReconcile = ≡→≋
      ( subst-∥f (λ z → z) eqP (U.⟪ Fr [ ccL0 ⊗ ccR0 ]* ⟫) RP
      ■ cong₂ U._∥_ redexRec PrestRec )
    middleReconcile : Bφ C₁ (Bφ B (U.ν contractumR)) U.≋ Bφ C₁′ (Bφ B (U.ν (pushR XR′)))
    middleReconcile =
         ≡→≋ (Bφ-lwk B₁ {b₁} {B₂} {a = n} (Bφ B (U.ν contractumR)))
      ◅◅ Bφ-cong C₁′
           ( ≡→≋ ( subst-Bφ (cong (_+ n) e1) B (U.ν contractumR)
                 ■ cong (Bφ B) (subst-ν (cong (sB +_) (cong (_+ n) e1)) contractumR) )
           ◅◅ Bφ-cong B (U.ν-cong bodyReconcile) )
    back : Bφ C₁ (Bφ B (U.ν contractumR)) U.≋ U[ T.ν C₁′ B QR ] σ
    back = middleReconcile ◅◅ Eq*.symmetric _ rhs


-- ============================================================================
--   RSPLIT-specific infrastructure.  rwk inserts a fresh data block `1 ∷` at
--   flat position `sum B₁` (vs lwk's slot-bump at `sum B₁ + 1`), so the bind
--   group GROWS by one block: C₁ᴿ = B₁ ++ 1 ∷ suc b₁ ∷ B₂.
-- ============================================================================

-- the grown rsplit bind group has exactly one more sync (ϕ[1]=drop, and the
-- inserted block is non-last).  Induction on B₁.
syncs-rwk : ∀ (B₁ : T.BindGroup) {b₁ : ℕ} {B₂ : T.BindGroup} →
            syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂))
syncs-rwk []            {b₁} {B₂}      = refl
syncs-rwk (a ∷ [])      {b₁} {B₂}      = cong suc (syncs-rwk [] {b₁} {B₂})
syncs-rwk (a ∷ d ∷ B₁″) {b₁} {B₂}      = cong suc (syncs-rwk (d ∷ B₁″) {b₁} {B₂})

-- The rsplit-grown bind group has exactly one more data slot.
sum-rwk : ∀ (B₁ : T.BindGroup) {b₁ B₂} →
          sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂))
sum-rwk B₁ {b₁} {B₂} = sum-++ B₁ (1 ∷ suc b₁ ∷ B₂)
                     ■ Nat.+-suc (sum B₁) (sum (suc b₁ ∷ B₂))
                     ■ cong suc (sym (sum-++ B₁ (suc b₁ ∷ B₂)))

sB₁≤sumC₁r : ∀ (B₁ : T.BindGroup) {b₁ B₂} → sum B₁ Nat.≤ sum (B₁ ++ suc b₁ ∷ B₂)
sB₁≤sumC₁r B₁ {b₁} {B₂} =
  subst (sum B₁ Nat.≤_) (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (Nat.m≤m+n (sum B₁) (sum (suc b₁ ∷ B₂)))

-- drwk inserts a slot at flat position `sum B₁`: below it, toℕ preserved; at/above, +1.
drwk : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) →
       sum (B₁ ++ suc b₁ ∷ B₂) →ᵣ sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)
drwk []        b₁ B₂ i = weakenᵣ i
drwk (a ∷ B₁') b₁ B₂ i =
  [ (λ p → p ↑ˡ sum (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) , (λ r → a ↑ʳ drwk B₁' b₁ B₂ r) ]′ (splitAt a i)

drwk-lo : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          Fin.toℕ j Nat.< sum B₁ → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ Fin.toℕ j
drwk-lo []        b₁ B₂ j ()
drwk-lo (a ∷ B₁') b₁ B₂ j lt with drwk-lo B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : Fin.toℕ r Nat.< sum B₁'
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁') (subst (Nat._< a + sum B₁') jℕ lt)

drwk-hi : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          sum B₁ Nat.≤ Fin.toℕ j → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ suc (Fin.toℕ j)
drwk-hi []        b₁ B₂ j h = Fin.toℕ-↑ʳ 1 j
drwk-hi (a ∷ B₁') b₁ B₂ j h with drwk-hi B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁'))) h))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : sum B₁' Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁') (Fin.toℕ r) (subst (a + sum B₁' Nat.≤_) jℕ h)

𝐒rwk-lo : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            Fin.toℕ x Nat.< sum B₁ →
            Fin.toℕ (TR.SplitRenamings.rwk B₁ B₂ B {b₁} {m} x) ≡ Fin.toℕ x
𝐒rwk-lo B₁ B₂ B {b₁} {m} x lt =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-lt weakenᵣ (sum B₁) (Fin.cast _ x) lt′
  ■ Fin.toℕ-cast _ x
  where lt′ : Fin.toℕ (Fin.cast _ x) Nat.< sum B₁
        lt′ = subst (Nat._< sum B₁) (sym (Fin.toℕ-cast _ x)) lt

𝐒rwk-hi : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ}
            (x : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
            sum B₁ Nat.≤ Fin.toℕ x →
            Fin.toℕ (TR.SplitRenamings.rwk B₁ B₂ B {b₁} {m} x) ≡ suc (Fin.toℕ x)
𝐒rwk-hi B₁ B₂ B {b₁} {m} x h =
    Fin.toℕ-cast _ _
  ■ toℕ-↑*-ge weakenᵣ (sum B₁) (Fin.cast _ x) h′
  ■ cong (sum B₁ +_) (cong suc (toℕ-reduce≥ (Fin.cast _ x) h′ ■ cong (Nat._∸ sum B₁) (Fin.toℕ-cast _ x)))
  ■ Nat.+-suc (sum B₁) (Fin.toℕ x Nat.∸ sum B₁)
  ■ cong suc (Nat.m+[n∸m]≡n h)
  where h′ : sum B₁ Nat.≤ Fin.toℕ (Fin.cast _ x)
        h′ = subst (sum B₁ Nat.≤_) (sym (Fin.toℕ-cast _ x)) h

P1r : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (d : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
     TR.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((d ↑ˡ sum B) ↑ˡ m)
     ≡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m
P1r B₁ B₂ B {b₁} {m} d with Fin.toℕ d Nat.<? sum B₁
... | yes lt = Fin.toℕ-injective
      ( 𝐒rwk-lo B₁ B₂ B _ (subst (Nat._< sum B₁) (sym posℕ) lt)
      ■ posℕ ■ sym (rhsℕ ■ drwk-lo B₁ b₁ B₂ d lt) )
  where posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d) (sum B)
... | no ¬lt = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ) h≤)
      ■ cong suc posℕ ■ sym (rhsℕ ■ drwk-hi B₁ b₁ B₂ d h≤) )
  where h≤ : sum B₁ Nat.≤ Fin.toℕ d
        h≤ = Nat.≮⇒≥ ¬lt
        posℕ : Fin.toℕ ((d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ d
        posℕ = Fin.toℕ-↑ˡ (d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ d (sum B)
        rhsℕ : Fin.toℕ ((drwk B₁ b₁ B₂ d ↑ˡ sum B) ↑ˡ m) ≡ Fin.toℕ (drwk B₁ b₁ B₂ d)
        rhsℕ = Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d ↑ˡ sum B) m ■ Fin.toℕ-↑ˡ (drwk B₁ b₁ B₂ d) (sum B)

P2r : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (w : 𝔽 (sum B)) →
     TR.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m)
     ≡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m
P2r B₁ B₂ B {b₁} {m} w = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (sB₁≤sumC₁r B₁) (Nat.m≤m+n _ (Fin.toℕ w))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w
        posℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ suc b₁ ∷ B₂) ↑ʳ w) m ■ Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂)) w
        rhsℕ : Fin.toℕ ((sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) ↑ˡ m) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + Fin.toℕ w)
        rhsℕ = Fin.toℕ-↑ˡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) m
             ■ Fin.toℕ-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) w
             ■ cong (Nat._+ Fin.toℕ w) (sum-rwk B₁)

P3r : ∀ (B₁ B₂ B : T.BindGroup) {b₁ m : ℕ} (u : 𝔽 m) →
     TR.SplitRenamings.rwk B₁ B₂ B {b₁} {m} ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u)
     ≡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u
P3r B₁ B₂ B {b₁} {m} u = Fin.toℕ-injective
      ( 𝐒rwk-hi B₁ B₂ B _ (subst (sum B₁ Nat.≤_) (sym posℕ)
                            (Nat.≤-trans (Nat.≤-trans (sB₁≤sumC₁r B₁) (Nat.m≤m+n _ (sum B))) (Nat.m≤m+n _ (Fin.toℕ u))))
      ■ cong suc posℕ ■ sym rhsℕ )
  where posℕ : Fin.toℕ ((sum (B₁ ++ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u
        posℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) u
        rhsℕ : Fin.toℕ ((sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) ↑ʳ u) ≡ suc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + Fin.toℕ u)
        rhsℕ = Fin.toℕ-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) u
             ■ cong (λ z → z + sum B + Fin.toℕ u) (sum-rwk B₁)

-- chainRwk: telescope a slot-equality (at scope suc N, shift sT) through the +-suc
-- scope-shuffle canonₛ applies when peeling a B₁ chain (scope N).  Identical shape
-- to chainLwk (reused verbatim); kept separate only for readability of the rwk side.
chainRwk : ∀ {N} {sT sT′ : ℕ} (sl : sT ≡ sT′)
           {DA DB : Set} (g : DA → Tm (sT + suc N)) (g′ : DB → Tm (sT′ + suc N))
           (i : DA) (di : DB) →
           subst Tm (cong (_+ suc N) sl) (g i) ≡ g′ di →
           subst Tm (cong (_+ N) (cong suc sl)) (subst Tm (+-suc sT N) (g i))
           ≡ subst Tm (+-suc sT′ N) (g′ di)
chainRwk = chainLwk

-- ===== canonₛ-rwk =====
-- canonₛ on the rwk-grown bind group (with a FRESH width-1 block inserted before the
-- handle chain), off the consumed handle, equals the transported ungrown canonₛ.
-- The base case (B₁ = []) is the substantive re-threading obligation the roadmap flags:
-- the inserted `1`-block becomes the new head, re-threading (` 0F, suc x, wk e₂) through
-- the whole tail — but away from slot 0F that threading is INVISIBLE (e₁ only read at 0F).
-- Ub[ b ] reads its first slot only at position 0F.  Off 0F it is e₁-independent.
Ub-e₁ : ∀ (b : ℕ) {N} (a a′ : Tm N) (c : 𝔽 N) (e₂ : Tm N) (j : 𝔽 (suc b)) → j ≢ 0F →
        Ub[ suc b ] (a , c , e₂) j ≡ Ub[ suc b ] (a′ , c , e₂) j
Ub-e₁ zero    a a′ c e₂ zero    j≢ = ⊥-elim (j≢ refl)
Ub-e₁ (suc b) a a′ c e₂ zero    j≢ = ⊥-elim (j≢ refl)
Ub-e₁ (suc b) a a′ c e₂ (suc j) j≢ = refl

-- e₁ (the head data-block's first slot) is only read at position 0F; off 0F the
-- canonical substitution is independent of it.  Induction mirrors canonₛ.
canonₛ-e₁ : ∀ (b₁ : ℕ) (B₂ : BindGroup) {N} (a a′ : Tm N) (x : 𝔽 N) (e₂ : Tm N)
            (i : 𝔽 (sum (suc b₁ ∷ B₂))) → i ≢ 0F →
            canonₛ (suc b₁ ∷ B₂) (a , x , e₂) i ≡ canonₛ (suc b₁ ∷ B₂) (a′ , x , e₂) i
canonₛ-e₁ b₁ [] {N} a a′ x e₂ i i≢ =
  Ub-e₁ (b₁ + 0) a a′ x e₂ i i≢
canonₛ-e₁ b₁ (c ∷ B₂′) {N} a a′ x e₂ i i≢
  with Fin.splitAt (suc b₁) i in seq
... | inj₁ p rewrite seq =
      cong (subst Tm (+-suc (syncs (c ∷ B₂′)) N))
        (cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c ∷ B₂′)))
          (Ub-e₁ b₁ (wk a) (wk a′) (suc x) (` 0F) p p≢))
  where
    p≢ : p ≢ 0F
    p≢ p≡ = i≢ ( sym (Fin.join-splitAt (suc b₁) (sum (c ∷ B₂′)) i)
               ■ cong (Fin.join (suc b₁) (sum (c ∷ B₂′))) seq
               ■ cong (_↑ˡ sum (c ∷ B₂′)) p≡ )
... | inj₂ r rewrite seq = refl

-- canonₛ-rwk, base case (B₁ = []): the fresh `1`-block sync (front of the tail's
-- syncs) is exactly the slot canonₛ-nat's (weakenᵣ ↑* syncs) inserts; off 0F, e₁
-- is invisible (canonₛ-e₁).  This is the substantive re-threading obligation.
canonₛ-rwk0 : ∀ {N} (cc : UChan N) (b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (suc b₁ ∷ B₂))) →
             i ≢ 0F →
             canonₛ (1 ∷ suc b₁ ∷ B₂) cc (weakenᵣ i)
             ≡ subst Tm (+-suc (syncs (suc b₁ ∷ B₂)) N)
                 (canonₛ (suc b₁ ∷ B₂) cc i ⋯ (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)))
canonₛ-rwk0 {N} (e₁ , x , e₂) b₁ B₂ i i≢ =
  cong (subst Tm (+-suc sD N))
    ( canonₛ-e₁ b₁ B₂ (` 0F) (wk e₁) (suc x) (wk e₂) i i≢
    ■ sym (canonₛ-nat (suc b₁ ∷ B₂) (e₁ , x , e₂) weakenᵣ i) )
  where sD = syncs (suc b₁ ∷ B₂)

-- syncs of a cons with a nonempty tail bumps by one (definitionally).
syncs-cons : ∀ (a : ℕ) (B₁' : BindGroup) (c : ℕ) (D : BindGroup) →
             syncs (a ∷ (B₁' ++ c ∷ D)) ≡ suc (syncs (B₁' ++ c ∷ D))
syncs-cons a []          c D = refl
syncs-cons a (b ∷ B₁'') c D = refl

-- sins: the sync-level insertion renaming, sending the ungrown group's syncs to
-- the rwk-grown group's syncs (which has ONE more φ, from the inserted 1-block).
-- Recursion on B₁ mirrors drwk: base inserts (weakenᵣ ↑* sD) retyped by +-suc;
-- the head block conjugates by the two +-suc scope shuffles.
sins : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N} →
       syncs (B₁ ++ suc b₁ ∷ B₂) + N →ᵣ syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N
sins [] b₁ B₂ {N} =
  subst (λ z → syncs (suc b₁ ∷ B₂) + N →ᵣ z) (+-suc (syncs (suc b₁ ∷ B₂)) N)
    (weakenᵣ ↑* syncs (suc b₁ ∷ B₂))
sins (a ∷ B₁') b₁ B₂ {N} =
  subst₂ _→ᵣ_
    (+-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂)))
    (+-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂))))
    (sins B₁' b₁ B₂ {suc N})

-- sins inserts a fresh sync slot at flat position syncs (suc b₁ ∷ B₂) (the
-- handle-chain's sync count, i.e. the leaf end of the handle block), regardless
-- of the B₁ prefix: at/above that position toℕ bumps by one.  Induction on B₁.
sins-toℕ-hi : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
              syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ j →
              Fin.toℕ (sins B₁ b₁ B₂ {N} j) ≡ suc (Fin.toℕ j)
sins-toℕ-hi [] b₁ B₂ {N} j h =
    toℕ-subst-cod (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) j
  ■ toℕ-↑*-ge weakenᵣ (syncs (suc b₁ ∷ B₂)) j h
  ■ cong (syncs (suc b₁ ∷ B₂) +_) (cong suc (toℕ-reduce≥ j h))
  ■ Nat.+-suc (syncs (suc b₁ ∷ B₂)) (Fin.toℕ j Nat.∸ syncs (suc b₁ ∷ B₂))
  ■ cong suc (Nat.m+[n∸m]≡n h)
sins-toℕ-hi (a ∷ B₁') b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sins B₁' b₁ B₂ {suc N}) j
  ■ sins-toℕ-hi B₁' b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-subst𝔽 (sym pL) j)) h)
  ■ cong suc (toℕ-subst𝔽 (sym pL) j)
  where
    pL = +-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂)))
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl

-- below the insertion threshold syncs (suc b₁ ∷ B₂), sins preserves toℕ.
sins-toℕ-lo : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
              Fin.toℕ j Nat.< syncs (suc b₁ ∷ B₂) →
              Fin.toℕ (sins B₁ b₁ B₂ {N} j) ≡ Fin.toℕ j
sins-toℕ-lo [] b₁ B₂ {N} j h =
    toℕ-subst-cod (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) j
  ■ toℕ-↑*-lt weakenᵣ (syncs (suc b₁ ∷ B₂)) j h
sins-toℕ-lo (a ∷ B₁') b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sins B₁' b₁ B₂ {suc N}) j
  ■ sins-toℕ-lo B₁' b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (Nat._< syncs (suc b₁ ∷ B₂)) (sym (toℕ-subst𝔽 (sym pL) j)) h)
  ■ toℕ-subst𝔽 (sym pL) j
  where
    pL = +-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂)))
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl

-- the handle-chain sync count bounds the whole grown group's sync count.
sD≤ : ∀ (B₁ : BindGroup) {b₁ B₂} → syncs (suc b₁ ∷ B₂) Nat.≤ syncs (B₁ ++ suc b₁ ∷ B₂)
sD≤ []                {b₁} {B₂} = Nat.≤-refl
sD≤ (a ∷ B₁') {b₁} {B₂} =
  subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (syncs-cons a B₁' (suc b₁) B₂))
    (Nat.≤-trans (sD≤ B₁') (Nat.n≤1+n _))

-- sins turns a weaken by the ungrown handle-group sync count into a weaken by
-- the grown one (both above the insertion threshold, so shifted by one).
sins-wk : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N} (v : 𝔽 N) →
          sins B₁ b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
          ≡ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v
sins-wk B₁ b₁ B₂ {N} v = Fin.toℕ-injective
  ( sins-toℕ-hi B₁ b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ (syncs (B₁ ++ suc b₁ ∷ B₂)) v))
        (Nat.≤-trans (sD≤ B₁) (Nat.m≤m+n (syncs (B₁ ++ suc b₁ ∷ B₂)) (Fin.toℕ v))))
  ■ cong suc (toℕ-weaken*ᵣ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
  ■ sym (toℕ-weaken*ᵣ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwk B₁)) )

-- canonₛ-rwk (general): canonₛ on the rwk-grown group, off the consumed handle,
-- equals the ungrown canonₛ post-composed with the sync-insertion renaming sins.
canonₛ-rwk : ∀ (B₁ : BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F) →
             canonₛ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) cc (drwk B₁ b₁ B₂ i)
             ≡ canonₛ (B₁ ++ suc b₁ ∷ B₂) cc i ⋯ sins B₁ b₁ B₂ {N}
canonₛ-rwk [] {N} cc b₁ B₂ i i≢ =
    canonₛ-rwk0 cc b₁ B₂ i (λ i≡ → i≢ (i≡ ■ sym cast≡))
  ■ sym (subst-⋯-cod-local (+-suc (syncs (suc b₁ ∷ B₂)) N)
           (canonₛ (suc b₁ ∷ B₂) cc i) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)))
  where
    cast≡ : Fin.cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F) ≡ 0F
    cast≡ = refl
canonₛ-rwk (a ∷ []) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk [] {suc N} (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ([] ++ 1 ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    SS  = cong suc (+-suc sD N)
    ρ0 = sins [] b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc (syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ (suc sD) v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hi [] b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (sD Nat.≤_) (sym (toℕ-weaken*ᵣ sD v)) (Nat.m≤m+n sD (Fin.toℕ v)))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ (suc sD) v) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ (suc sD)
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ([] ++ 1 ∷ suc b₁ ∷ B₂)) (weakenᵣ r) =
      cong (subst Tm SS) (rec r r≢0)
    ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    SS  = cong suc (+-suc sD N)
    ρ0 = sins [] b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc (syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    leafM = canonₛ (suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢0 : r ≢ 0F
    r≢0 r≡ = i≢ ( sym (Fin.join-splitAt a (sum ([] ++ suc b₁ ∷ B₂)) i)
                ■ cong (Fin.join a (sum ([] ++ suc b₁ ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split a [] b₁ B₂) )
canonₛ-rwk (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk (d ∷ B₁″) {suc N} (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sins (d ∷ B₁″) b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ sDʳ v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hi (d ∷ B₁″) b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ sD v))
            (Nat.≤-trans (sD≤ (d ∷ B₁″)) (Nat.m≤m+n sD (Fin.toℕ v))))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ sDʳ v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwk (d ∷ B₁″))) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ sDʳ
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) (drwk (d ∷ B₁″) b₁ B₂ r) =
      cong (subst Tm SS) (rec r r≢h)
    ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sins (d ∷ B₁″) b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    leafM = canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢h : r ≢ Fin.cast (sym (sum-++ (d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 0F)
    r≢h r≡ = i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) i)
                ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split a (d ∷ B₁″) b₁ B₂) )


-- leafσ on the grown group agrees with the ungrown leafσ post-composed with the
-- sync-insertion renaming (lifted over the B-block binders), away from the handle.
leafσ-rwk-id : ∀ {m n} (σ : m →ₛ n) (B₁ B₂ B : BindGroup) (b₁ : ℕ)
               (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)) →
               i ≢ TR.SplitRenamings.inj B₁ B₂ B {suc b₁ ∷ []} {m} 0F →
               leafσ σ (B₁ ++ suc b₁ ∷ B₂) B i ⋯ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)
               ≡ leafσ σ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B (TR.SplitRenamings.rwk B₁ B₂ B i)
leafσ-rwk-id {m} {n} σ B₁ B₂ B b₁ i i≢
  with Fin.splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) i in seqo
... | inj₂ u
  rewrite leafσ-tail {n = n} σ (B₁ ++ suc b₁ ∷ B₂) B i u seqo
        | leafσ-tail {n = n} σ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B (TR.SplitRenamings.rwk B₁ B₂ B i) u
            (cong (Fin.splitAt (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B))
               (cong (TR.SplitRenamings.rwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo) ■ P3r B₁ B₂ B u)
            ■ Fin.splitAt-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) m u) =
      sym (⋯-↑*-wk (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂))) (sins B₁ b₁ B₂ {2 + n}) (syncs B))
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) tCore
  where
    tCore : (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂))) ⋯ sins B₁ b₁ B₂ {2 + n}
            ≡ σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂))
    tCore = fusion (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2) (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂))) (sins B₁ b₁ B₂ {2 + n})
          ■ ⋯-cong (σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2) (λ v → sins-wk B₁ b₁ B₂ {2 + n} v)
... | inj₁ db with Fin.splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) db in seqi
...   | inj₂ w
  rewrite leafσ-B₁ σ (B₁ ++ suc b₁ ∷ B₂) B i db w seqo seqi
        | leafσ-B₁ σ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B (TR.SplitRenamings.rwk B₁ B₂ B i) (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) w
            (cong (Fin.splitAt (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B)) (cong (TR.SplitRenamings.rwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ P2r B₁ B₂ B w)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) ↑ʳ w) m)
            (Fin.splitAt-↑ʳ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) (sum B) w) =
      canonₛ-nat B (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) 1F , K `unit) (sins B₁ b₁ B₂ {2 + n}) w
    ■ cong (λ z → canonₛ B (K `unit , z , K `unit) w) (sins-wk B₁ b₁ B₂ {2 + n} 1F)
...   | inj₁ d
  rewrite leafσ-A₁ σ (B₁ ++ suc b₁ ∷ B₂) B i db d seqo seqi
        | leafσ-A₁ σ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B (TR.SplitRenamings.rwk B₁ B₂ B i) (drwk B₁ b₁ B₂ d ↑ˡ sum B) (drwk B₁ b₁ B₂ d)
            (cong (Fin.splitAt (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B)) (cong (TR.SplitRenamings.rwk B₁ B₂ B) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ P1r B₁ B₂ B d)
             ■ Fin.splitAt-↑ˡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + sum B) (drwk B₁ b₁ B₂ d ↑ˡ sum B) m)
            (Fin.splitAt-↑ˡ (sum (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) (drwk B₁ b₁ B₂ d) (sum B)) =
      sym (⋯-↑*-wk (canonₛ (B₁ ++ suc b₁ ∷ B₂) (K `unit , 0F , K `unit) d) (sins B₁ b₁ B₂ {2 + n}) (syncs B))
    ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
        (sym (canonₛ-rwk B₁ (K `unit , 0F , K `unit) b₁ B₂ d
          (λ d≡ → i≢ ((sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m i) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂) + sum B) m) seqo ■ cong (_↑ˡ m) (sym (Fin.join-splitAt (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B) db) ■ cong (Fin.join (sum (B₁ ++ suc b₁ ∷ B₂)) (sum B)) seqi)) ■ cong (λ z → (z ↑ˡ sum B) ↑ˡ m) d≡))))

-- The rsplit-grown bind group's Bφ-prefix carries one extra φ-drop binder (the
-- inserted `1`-block).  That binder slides down past the remaining blocks to the
-- front of the leaf body.  syncs C₁ᴿ = suc (syncs C₁); subst on a re-types Z.
ss-Uf : ∀ {h : ℕ → ℕ} {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) {t : U.Proc (h x)} →
        subst (λ j → U.Proc (h j)) q (subst (λ j → U.Proc (h j)) p t)
        ≡ subst (λ j → U.Proc (h j)) (p ■ q) t
ss-Uf refl refl = refl

-- syncs of an append with a nonempty tail splits additively (one junction per
-- B₁-block).  Fact (A) for the sw-cast index reshaping.
syncs-split : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} →
              syncs (B₁ ++ suc b₁ ∷ B₂) ≡ L.length B₁ + syncs (suc b₁ ∷ B₂)
syncs-split []            {b₁} {B₂} = refl
syncs-split (a ∷ [])      {b₁} {B₂} = cong suc (syncs-split [] {b₁} {B₂})
syncs-split (a ∷ d ∷ B₁″) {b₁} {B₂} = cong suc (syncs-split (d ∷ B₁″) {b₁} {B₂})

toℕ-subst-domM : ∀ {A A′ Bb} (e : A ≡ A′) (ρ : A →ᵣ Bb) (y : 𝔽 A′) →
                 Fin.toℕ (subst (λ z → z →ᵣ Bb) e ρ y) ≡ Fin.toℕ (ρ (subst 𝔽 (sym e) y))
toℕ-subst-domM refl ρ y = refl

-- a weakened term (image of ⋯ weakenᵣ, so avoiding 0F) commutes weaken*(suc k)
-- with the split weaken* k then weakenᵣ↑*(suc k) (across the +-suc scope bridge).
weaken-suc-shift : ∀ {N} (u : Tm N) (k : ℕ) →
  u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (suc k)
  ≡ subst Tm (+-suc k N) (u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ k) ⋯ (weakenᵣ ↑* (suc k))
weaken-suc-shift {N} u k =
    fusion u weakenᵣ (weaken* ⦃ Kᵣ ⦄ (suc k))
  ■ ⋯-cong u ptwise
  ■ sym (fusion u weakenᵣ (weaken* ⦃ Kᵣ ⦄ k ·ₖ ρ*))
  ■ sym (fusion (u ⋯ weakenᵣ) (weaken* ⦃ Kᵣ ⦄ k) ρ*)
  ■ sym (subst-⋯-dom-local (+-suc k N) (u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ k) (weakenᵣ ↑* (suc k)))
  where
    ρ* : (k + suc N) →ᵣ (suc k + suc N)
    ρ* = subst (λ z → z →ᵣ (suc k + suc N)) (sym (+-suc k N)) (weakenᵣ ↑* (suc k))
    ptwise : (weakenᵣ ·ₖ weaken* ⦃ Kᵣ ⦄ (suc k)) ≗ (weakenᵣ ·ₖ (weaken* ⦃ Kᵣ ⦄ k ·ₖ ρ*))
    ptwise v = Fin.toℕ-injective
      ( toℕ-weaken*ᵣ (suc k) (weakenᵣ v)
      ■ sym ( toℕ-subst-domM (sym (+-suc k N)) (weakenᵣ ↑* (suc k)) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
            ■ toℕ-↑*-ge weakenᵣ (suc k) w′ q
            ■ cong (suc k +_) (cong suc redw) ) )
      where
        toℕ-subst𝔽M : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽M refl y = refl
        w′ : 𝔽 (suc k + N)
        w′ = subst 𝔽 (sym (sym (+-suc k N))) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
        w′N : Fin.toℕ w′ ≡ suc (k + Fin.toℕ v)
        w′N = toℕ-subst𝔽M (sym (sym (+-suc k N))) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
            ■ toℕ-weaken*ᵣ k (weakenᵣ v) ■ Nat.+-suc k (Fin.toℕ v)
        q : suc k Nat.≤ Fin.toℕ w′
        q = subst (suc k Nat.≤_) (sym w′N) (Nat.s≤s (Nat.m≤m+n k (Fin.toℕ v)))
        redw : Fin.toℕ (Fin.reduce≥ w′ q) ≡ Fin.toℕ v
        redw = toℕ-reduce≥ w′ q ■ cong (Nat._∸ suc k) w′N ■ Nat.m+n∸m≡n k (Fin.toℕ v)

-- rsplit grown-handle L-slot: the fresh 1-channel's L-slot = ungrown handle's
-- L-slot post-composed with sins.  B₁-induction mirroring canonₛ-rwk (the
-- sins subst₂-conjugation via ⋯-subst₂ / subst-Tm-uip).
handle-L-rwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (canonₛ-handle B₁ e₁ x e₂ 0 (suc b₁ ∷ B₂))
  ≡ proj₁ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂) ⋯ sins B₁ b₁ B₂ {N}
handle-L-rwk [] {N} e₁ x e₂ zero     []       = ⋯-id (wk e₁) (λ _ → refl)
handle-L-rwk [] {N} e₁ x e₂ (suc b₁) []       = ⋯-id (wk e₁) (λ _ → refl)
handle-L-rwk [] {N} e₁ x e₂ zero     (c′ ∷ B) =
    cong (subst Tm (+-suc (suc (syncs (c′ ∷ B))) N)) (weaken-suc-shift e₁ (syncs (c′ ∷ B)))
  ■ sym (subst-⋯-cod-local (+-suc (suc (syncs (c′ ∷ B))) N)
           (subst Tm (+-suc (syncs (c′ ∷ B)) N) (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
           (weakenᵣ ↑* (suc (syncs (c′ ∷ B)))))
handle-L-rwk [] {N} e₁ x e₂ (suc b₁) (c′ ∷ B) =
    cong (subst Tm (+-suc (suc (syncs (c′ ∷ B))) N)) (weaken-suc-shift e₁ (syncs (c′ ∷ B)))
  ■ sym (subst-⋯-cod-local (+-suc (suc (syncs (c′ ∷ B))) N)
           (subst Tm (+-suc (syncs (c′ ∷ B)) N) (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
           (weakenᵣ ↑* (suc (syncs (c′ ∷ B)))))
handle-L-rwk (a ∷ []) {N} e₁ x e₂ b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ([] ++ suc b₁ ∷ B₂)
    sBᴿ = syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)
    ρ   = sins [] b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handle [] (` 0F) (suc x) (wk e₂) b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
handle-L-rwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sBᴿ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    ρ   = sins (d ∷ B₁″) b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handle (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))

ss-Tm : ∀ {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) (t : Tm x) → subst Tm q (subst Tm p t) ≡ subst Tm (p ■ q) t
ss-Tm refl refl t = refl

subst-`v : ∀ {p q} (e : p ≡ q) (v : 𝔽 p) → subst Tm e (` v) ≡ ` (subst 𝔽 e v)
subst-`v refl v = refl

-- rsplit grown-handle R-slot: the residual suc b₁-channel's R-slot (prefix B₁++[1],
-- carried to the C₁ᴿ scope by ++-assoc) = ungrown handle's R-slot ⋯ sins.
handle-R-rwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (λ z → syncs z + N) (++-assoc B₁ (1 ∷ []) (suc b₁ ∷ B₂)))
    (proj₁ (proj₂ (canonₛ-handle (B₁ ++ 1 ∷ []) e₁ x e₂ b₁ B₂)))
  ≡ proj₁ (proj₂ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂)) ⋯ sins B₁ b₁ B₂ {N}
handle-R-rwk [] {N} e₁ x e₂ zero     []       = refl
handle-R-rwk [] {N} e₁ x e₂ (suc b₁) []       = refl
handle-R-rwk [] {N} e₁ x e₂ zero     (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc sB' N))) (subst-`v (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))
  ■ subst-`v (cong suc (+-suc sB' N)) (subst 𝔽 (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))
  ■ cong `_ (Fin.toℕ-injective (toℕVL ■ sym toℕVR))
  ■ sym (cong (_⋯ sins [] zero (c′ ∷ B) {N}) (subst-`v (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F)))
  where
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl
    sB' = syncs (c′ ∷ B)
    toℕVL : Fin.toℕ (subst 𝔽 (cong suc (+-suc sB' N)) (subst 𝔽 (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))) ≡ sB'
    toℕVL = toℕ-subst𝔽 (cong suc (+-suc sB' N)) _ ■ toℕ-subst𝔽 (+-suc sB' (suc N)) _
          ■ toℕ-weaken*ᵣ sB' 0F ■ Nat.+-identityʳ sB'
    w : 𝔽 (suc sB' + N)
    w = subst 𝔽 (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F)
    wN : Fin.toℕ w ≡ sB'
    wN = toℕ-subst𝔽 (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F) ■ toℕ-weaken*ᵣ sB' 0F ■ Nat.+-identityʳ sB'
    toℕVR : Fin.toℕ (sins [] zero (c′ ∷ B) {N} w) ≡ sB'
    toℕVR = toℕ-subst-cod (+-suc (suc sB') N) (weakenᵣ ↑* suc sB') w
          ■ toℕ-↑*-lt weakenᵣ (suc sB') w (subst (Nat._< suc sB') (sym wN) (Nat.n<1+n sB'))
          ■ wN
handle-R-rwk [] {N} e₁ x e₂ (suc b₁) (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc (syncs (c′ ∷ B)) N))) (subst-Kunit (+-suc (syncs (c′ ∷ B)) (suc N)))
  ■ subst-Kunit (cong suc (+-suc (syncs (c′ ∷ B)) N))
  ■ sym (cong (_⋯ sins [] (suc b₁) (c′ ∷ B)) (subst-Kunit (+-suc (syncs (c′ ∷ B)) N)))
handle-R-rwk (a ∷ []) {N} e₁ x e₂ b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ([] ++ suc b₁ ∷ B₂)
    sBᴿ' = syncs (([] ++ 1 ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ([] ++ 1 ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handle [] (` 0F) (suc x) (wk e₂) b₁ B₂))
    ρ    = sins [] b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc [] (1 ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ []) (1 ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')
handle-R-rwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sBᴿ' = syncs (((d ∷ B₁″) ++ 1 ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ((d ∷ B₁″) ++ 1 ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handle (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂))
    ρ    = sins (d ∷ B₁″) b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc (d ∷ B₁″) (1 ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ d ∷ B₁″) (1 ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')

comm3 : ∀ x y z → x + (y + z) ≡ y + (x + z)
comm3 x y z = sym (+-assoc x y z) ■ cong (_+ z) (Nat.+-comm x y) ■ +-assoc y x z

-- the leaf swap assocSwapᵣ sD 1 at leaf scope (L.length B₁ + a) — the φ-drop
-- binder, which sits ABOVE the B₁-prefix binders (de Bruijn-checked), slides past
-- the sD suffix-binders to the leaf.  Retyped to the (syncs C₁)-relative scope.
sw-dom : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
         syncs (B₁ ++ suc b₁ ∷ B₂) + suc a ≡ syncs (suc b₁ ∷ B₂) + (1 + (L.length B₁ + a))
sw-dom B₁ {b₁} {B₂} {a} =
    cong (_+ suc a) (syncs-split B₁)
  ■ +-suc (L.length B₁ + syncs (suc b₁ ∷ B₂)) a
  ■ cong suc (+-assoc (L.length B₁) (syncs (suc b₁ ∷ B₂)) a ■ comm3 (L.length B₁) (syncs (suc b₁ ∷ B₂)) a)
  ■ sym (+-suc (syncs (suc b₁ ∷ B₂)) (L.length B₁ + a))

sw-cod : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
         1 + (syncs (suc b₁ ∷ B₂) + (L.length B₁ + a)) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂) + a)
sw-cod B₁ {b₁} {B₂} {a} =
  cong suc (comm3 (syncs (suc b₁ ∷ B₂)) (L.length B₁) a
           ■ sym (+-assoc (L.length B₁) (syncs (suc b₁ ∷ B₂)) a)
           ■ cong (_+ a) (sym (syncs-split B₁)))

sw-cast : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
          (syncs (B₁ ++ suc b₁ ∷ B₂) + suc a) →ᵣ suc (syncs (B₁ ++ suc b₁ ∷ B₂) + a)
sw-cast B₁ {b₁} {B₂} {a} =
  subst₂ _→ᵣ_ (sym (sw-dom B₁ {b₁} {B₂} {a})) (sw-cod B₁ {b₁} {B₂} {a})
    (assocSwapᵣ (syncs (suc b₁ ∷ B₂)) 1 {L.length B₁ + a})

-- Prefix fold: applies one φ-binder per B₁-block, with the leaf at the bottom.
-- (Distinct from Bφ, which drops the last block; here EVERY block is a binder.)
Pfx : ∀ {n} (B₁ : BindGroup) → U.Proc (L.length B₁ + n) → U.Proc n
Pfx []        X = X
Pfx {n} (b ∷ B₁') X =
  U.φ ϕ[ b ] (Pfx B₁' (subst U.Proc (sym (+-suc (L.length B₁') n)) X))

Pfx-cong : ∀ {n} (B₁ : BindGroup) {X Y : U.Proc (L.length B₁ + n)} →
           X U.≋ Y → Pfx {n} B₁ X U.≋ Pfx B₁ Y
Pfx-cong []        xy = xy
Pfx-cong {n} (b ∷ B₁') xy =
  U.φ-cong (Pfx-cong B₁' (subst-≋ (sym (+-suc (L.length B₁') n)) xy))

subst-Pfx : ∀ {n n′} (e : n ≡ n′) (B₁ : BindGroup) (X : U.Proc (L.length B₁ + n)) →
            subst U.Proc e (Pfx {n} B₁ X)
            ≡ Pfx {n′} B₁ (subst U.Proc (cong (L.length B₁ +_) e) X)
subst-Pfx refl B₁ X = refl

-- ⋯ₚ lifts through Pfx by ↑* (L.length B₁) over the prefix binders.
Pfx-⋯ : ∀ {n n′} (B₁ : BindGroup) (X : U.Proc (L.length B₁ + n)) (ρ : n →ᵣ n′) →
        Pfx {n} B₁ X U.⋯ₚ ρ ≡ Pfx {n′} B₁ (X U.⋯ₚ (ρ ↑* L.length B₁))
Pfx-⋯ []        X ρ = refl
Pfx-⋯ {n} {n′} (b ∷ B₁') X ρ =
  cong (U.φ ϕ[ b ])
    ( Pfx-⋯ B₁' (subst U.Proc (sym (+-suc (L.length B₁') n)) X) (ρ ↑)
    ■ cong (Pfx B₁') bodyeq )
  where
    sB = L.length B₁'
    Θ : (sB + suc n) →ᵣ (sB + suc n′)
    Θ = (ρ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ᵣ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ᵣ z) (sym (+-suc sB n′)) (ρ ↑* suc sB)
    Θ⁺eq = subst-flip (+-suc sB n′) (sym (subst₂→ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCast sB ρ)
    bodyeq : (subst U.Proc (sym (+-suc sB n)) X) U.⋯ₚ ((ρ ↑) ↑* sB)
             ≡ subst U.Proc (sym (+-suc sB n′)) (X U.⋯ₚ (ρ ↑* suc sB))
    bodyeq =
        TP-subst-⋯ₚ-dom (+-suc sB n) X Θ
      ■ cong (X U.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-cod (sym (+-suc sB n′)) X (ρ ↑* suc sB)

-- Peel: Bφ over an append (with nonempty tail c∷D′) = Pfx of B₁ over Bφ of the tail.
syncs-split-gen : ∀ (Bp : BindGroup) (cc : ℕ) (Dp : BindGroup) →
                  syncs (Bp ++ cc ∷ Dp) ≡ L.length Bp + syncs (cc ∷ Dp)
syncs-split-gen []            cc Dp = refl
syncs-split-gen (x ∷ [])      cc Dp = cong suc (syncs-split-gen [] cc Dp)
syncs-split-gen (x ∷ y ∷ Bp″) cc Dp = cong suc (syncs-split-gen (y ∷ Bp″) cc Dp)

peel-eq : ∀ (B₁ : BindGroup) (c : ℕ) (D′ : BindGroup) {a : ℕ} →
          syncs (B₁ ++ c ∷ D′) + a ≡ syncs (c ∷ D′) + (L.length B₁ + a)
peel-eq B₁ c D′ {a} =
    cong (_+ a) (syncs-split-gen B₁ c D′)
  ■ +-assoc (L.length B₁) (syncs (c ∷ D′)) a
  ■ comm3 (L.length B₁) (syncs (c ∷ D′)) a

Bφ-peel : ∀ (B₁ : BindGroup) (c : ℕ) (D′ : BindGroup) {a : ℕ}
          (Z : U.Proc (syncs (B₁ ++ c ∷ D′) + a)) →
          Bφ (B₁ ++ c ∷ D′) Z
          ≡ Pfx B₁ (Bφ (c ∷ D′) (subst U.Proc (peel-eq B₁ c D′ {a}) Z))
Bφ-peel []        c D′ {a} Z =
  cong (Bφ (c ∷ D′)) (sym (cong (λ e → subst U.Proc e Z) (uipℕ (peel-eq [] c D′ {a}) refl)))
Bφ-peel (b ∷ [])       c D′ {a} Z =
  cong (U.φ ϕ[ b ])
    ( Bφ-peel [] c D′ {suc a} (subst U.Proc (sym (+-suc sT a)) Z)
    ■ cong (Pfx [])
        ( cong (Bφ (c ∷ D′)) bodyeq
        ■ sym (subst-Bφ (sym (+-suc (L.length ([] {A = ℕ})) a)) (c ∷ D′)
                 (subst U.Proc (peel-eq (b ∷ []) c D′ {a}) Z)) ) )
  where
    sT = syncs ([] ++ c ∷ D′)
    bodyeq : subst U.Proc (peel-eq [] c D′ {suc a})
               (subst U.Proc (sym (+-suc sT a)) Z)
             ≡ subst U.Proc (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length ([] {A = ℕ})) a)))
                 (subst U.Proc (peel-eq (b ∷ []) c D′ {a}) Z)
    bodyeq = ss-U (sym (+-suc sT a)) (peel-eq [] c D′ {suc a}) {t = Z}
           ■ cong (λ e → subst U.Proc e Z) (uipℕ _ _)
           ■ sym (ss-U (peel-eq (b ∷ []) c D′ {a})
                       (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length ([] {A = ℕ})) a))) {t = Z})
Bφ-peel (b ∷ x ∷ B₁'') c D′ {a} Z =
  cong (U.φ ϕ[ b ])
    ( Bφ-peel (x ∷ B₁'') c D′ {suc a} (subst U.Proc (sym (+-suc sT a)) Z)
    ■ cong (Pfx (x ∷ B₁''))
        ( cong (Bφ (c ∷ D′)) bodyeq
        ■ sym (subst-Bφ (sym (+-suc (L.length (x ∷ B₁'')) a)) (c ∷ D′)
                 (subst U.Proc (peel-eq (b ∷ x ∷ B₁'') c D′ {a}) Z)) ) )
  where
    sT = syncs ((x ∷ B₁'') ++ c ∷ D′)
    bodyeq : subst U.Proc (peel-eq (x ∷ B₁'') c D′ {suc a})
               (subst U.Proc (sym (+-suc sT a)) Z)
             ≡ subst U.Proc (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length (x ∷ B₁'')) a)))
                 (subst U.Proc (peel-eq (b ∷ x ∷ B₁'') c D′ {a}) Z)
    bodyeq = ss-U (sym (+-suc sT a)) (peel-eq (x ∷ B₁'') c D′ {suc a}) {t = Z}
           ■ cong (λ e → subst U.Proc e Z) (uipℕ _ _)
           ■ sym (ss-U (peel-eq (b ∷ x ∷ B₁'') c D′ {a})
                       (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length (x ∷ B₁'')) a))) {t = Z})

-- Pull a single φ binder OUT of a Bφ B block (reverse of φ-past-Bφ).
Bφ-φ-comm : (B : BindGroup) (z : U.Flag) {n : ℕ} (Y : U.Proc (1 + (syncs B + n))) →
            Bφ B (U.φ z Y) U.≋
            U.φ z (Bφ B (Y U.⋯ₚ assocSwapᵣ 1 (syncs B)))
Bφ-φ-comm B z {n} Y =
     Eq*.symmetric _
       ( φ-past-Bφ B z (Y U.⋯ₚ assocSwapᵣ 1 (syncs B))
       ◅◅ Bφ-cong B (U.φ-cong (≡→≋ bodyid)) )
  where
    bodyid : (Y U.⋯ₚ assocSwapᵣ 1 (syncs B)) U.⋯ₚ assocSwapᵣ (syncs B) 1 ≡ Y
    bodyid = U.fusionₚ Y (assocSwapᵣ 1 (syncs B)) (assocSwapᵣ (syncs B) 1)
           ■ local-⋯ₚ-id Y (assocSwap-invol 1 (syncs B))

-- The inserted φ-drop binder descends to the leaf.  Non-recursive: peel B₁ as a
-- Pfx prefix, push the (1-block) φ-drop down past Bφ (suc b₁ ∷ B₂) to the leaf
-- via φ-past-Bφ, then re-peel.  The ↑* L.length B₁ on the swap comes from Pfx-⋯.
Brwk-slide : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
             (Z : U.Proc (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + a)) →
             Bφ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) Z
             U.≋ Bφ (B₁ ++ suc b₁ ∷ B₂)
                   (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                                 U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
Brwk-slide B₁ {b₁} {B₂} {a} Z =
     ≡→≋ (Bφ-peel B₁ 1 (suc b₁ ∷ B₂) {a} Z)
  ◅◅ Pfx-cong B₁ (φ-past-Bφ (suc b₁ ∷ B₂) U.drop {L.length B₁ + a} bodyW)
  ◅◅ ≡→≋
       ( cong (Pfx B₁) (cong (Bφ (suc b₁ ∷ B₂)) reconcile)
       ■ sym (Bφ-peel B₁ (suc b₁) B₂ {a}
                (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                              U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    W0 : U.Proc (syncs (1 ∷ suc b₁ ∷ B₂) + (L.length B₁ + a))
    W0 = subst U.Proc (peel-eq B₁ 1 (suc b₁ ∷ B₂) {a}) Z
    bodyW : U.Proc (sD + suc (L.length B₁ + a))
    bodyW = subst U.Proc (sym (+-suc sD (L.length B₁ + a))) W0
    reconcile : U.φ U.drop (bodyW U.⋯ₚ assocSwapᵣ sD 1 {L.length B₁ + a})
                ≡ subst U.Proc (peel-eq B₁ (suc b₁) B₂ {a})
                    (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                                  U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
    reconcile =
        cong (U.φ U.drop) reconcileBody
      ■ sym (subst-φ (peel-eq B₁ (suc b₁) B₂ {a})
               (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                 U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
      where
        raw : (sD + (1 + (L.length B₁ + a))) →ᵣ (1 + (sD + (L.length B₁ + a)))
        raw = assocSwapᵣ sD 1 {L.length B₁ + a}
        EQ : syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + a ≡ syncs (B₁ ++ suc b₁ ∷ B₂) + suc a
        EQ = cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)
        -- RHS body: subst EQ Z ⋯ sw-cast = subst (sw-cod) ((subst (EQ ■ sw-dom) Z) ⋯ raw).
        rhs≡ : subst U.Proc EQ Z U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}
               ≡ subst U.Proc (sw-cod B₁ {b₁} {B₂} {a})
                   (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)
        rhs≡ = cast-⋯2 (sw-dom B₁ {b₁} {B₂} {a}) (sw-cod B₁ {b₁} {B₂} {a}) (subst U.Proc EQ Z) raw
             ■ cong (λ w → subst U.Proc (sw-cod B₁ {b₁} {B₂} {a}) (w U.⋯ₚ raw))
                 (ss-U EQ (sw-dom B₁ {b₁} {B₂} {a}) {t = Z})
        -- LHS body: bodyW = subst (EQ ■ sw-dom) Z (same coercion, by UIP).
        bodyW≡ : bodyW ≡ subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z
        bodyW≡ = ss-U (peel-eq B₁ 1 (suc b₁ ∷ B₂) {a}) (sym (+-suc sD (L.length B₁ + a))) {t = Z}
               ■ cong (λ e → subst U.Proc e Z) (uipℕ _ (EQ ■ sw-dom B₁ {b₁} {B₂} {a}))
        reconcileBody =
            cong (U._⋯ₚ raw) bodyW≡
          ■ sym ( cong (subst U.Proc (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))) rhs≡
                ■ ss-U (sw-cod B₁ {b₁} {B₂} {a}) (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))
                       {t = subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw}
                ■ cong (λ e → subst U.Proc e (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)) (uipℕ _ refl) )

U-rsplit : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {B₁ B₂ B : BindGroup} {b₁ : ℕ} {s : 𝕊 0}
  → {E : Frame* (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → {P : T.Proc (sum (B₁ ++ suc b₁ ∷ B₂) + sum B + m)}
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     Γ ; γ ⊢ₚ T.ν (B₁ ++ suc b₁ ∷ B₂) B
                 (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P))
  → (let module 𝐒 = TR.SplitRenamings B₁ B₂ B in
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       UR─→ₚ*
      U[ T.ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)) ] σ)
     ⊎
     (U[ T.ν (B₁ ++ suc b₁ ∷ B₂) B
              (T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P) ] σ
       U.≋
      U[ T.ν (B₁ ++ 1 ∷ suc b₁ ∷ B₂) B
              (T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)) ] σ))
U-rsplit {m} {n} σ Vσ Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
  with rsplit-confine Γ-S {B₁ = B₁} {B₂ = B₂} {B = B} {b₁ = b₁} {s = s} {E = E} {P = P} ⊢P
... | k , ρ⁻ , ρ⁻-skip , E₀ , Eeq , P₀ , Peq =
      inj₁ (wrapNE front (Bφ-lift-step C₁ (Bφ-lift-step B leaf-fire)) ε back)
  where
    module 𝐒 = TR.SplitRenamings B₁ B₂ B
    C₁ C₁ᴿ : BindGroup
    C₁  = B₁ ++ suc b₁ ∷ B₂
    C₁ᴿ = B₁ ++ 1 ∷ suc b₁ ∷ B₂
    QL : T.Proc (sum C₁ + sum B + m)
    QL = T.⟪ E [ K (`rsplit s) ·¹ (` 𝐒.inj 0F) ]* ⟫ T.∥ P
    QR : T.Proc (sum C₁ᴿ + sum B + m)
    QR = T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ T.∥ (P T.⋯ₚ 𝐒.rwk)
    sA sAᴿ sB : ℕ
    sA  = syncs C₁
    sAᴿ = syncs C₁ᴿ
    sB  = syncs B
    τ : sum C₁ + sum B + m →ₛ syncs B + (syncs C₁ + (2 + n))
    τ = leafσ σ C₁ B
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sA 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sA) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    ρ₁ : (sB + (sA + (2 + n))) →ᵣ (sB + (2 + (sA + n)))
    ρ₁ = assocSwapᵣ sA 2 ↑* sB
    ρ₂ : (sB + (2 + (sA + n))) →ᵣ (2 + (sB + (sA + n)))
    ρ₂ = assocSwapᵣ sB 2
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    push : ∀ {kk} → U.Proc (sB + (sA + (2 + kk))) → U.Proc (2 + (sB + (sA + kk)))
    push {kk} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    XL : U.Proc (sB + (sA + (2 + n)))
    XL = U[ QL ] τ
    ν↓ : ∀ (X : U.Proc (sB + (sA + (2 + n)))) →
         U.ν (Bφ C₁ (Bφ B X)) U.≋ Bφ C₁ (Bφ B (U.ν (push X)))
    ν↓ X =
         ν-past-Bφ C₁ (Bφ B X)
      ◅◅ Bφ-cong C₁ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sA 2))))
      ◅◅ Bφ-cong C₁ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)))
    front : U[ T.ν C₁ B QL ] σ U.≋ Bφ C₁ (Bφ B (U.ν (push XL)))
    front = ≡→≋ (Uν-flat σ C₁ B QL) ◅◅ ν↓ XL
    castpos : 𝔽 (sum C₁)
    castpos = Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F)
    hc = canonₛ-handle B₁ (K `unit) 0F (K `unit) b₁ B₂
    cc : Tm (2 + (sB + (sA + n)))
    cc = rn (τ (𝐒.inj 0F))
    τinj0 : τ (𝐒.inj 0F) ≡ canonₛ C₁ (K `unit , 0F , K `unit) castpos ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τinj0 =
        cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum B) (castpos ↑ˡ sum B) m)
      ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castpos (sum B))
    ccTriple : cc ≡ ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` 0F))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂)
    ccTriple =
        cong rn (τinj0 ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ hc)))))
      ■ cong (λ z → ((proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂) ⊗ (` z))
                    ⊗ (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂))
          (Fin.toℕ-injective (assocPush-junc sA sB 0 (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) jvtoℕ (Nat.s≤s Nat.z≤n)))
      where
        jvtoℕ : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB (proj₁ (proj₂ (proj₂ hc)))) ≡ sB + (sA + 0)
        jvtoℕ = toℕ-weaken*ᵣ sB (proj₁ (proj₂ (proj₂ hc))) ■ cong (sB +_) (proj₂ (proj₂ (proj₂ (proj₂ hc))))
    Fr : Frame* (2 + (sB + (sA + n)))
    Fr = (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ P ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    threadEq : (Ef : Frame* (sum C₁ + sum B + m)) (p : Tm (sum C₁ + sum B + m)) →
               (U[ T.⟪ Ef [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* Ef τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ Ef τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    YL≡ : push XL ≡ U.⟪ Fr [ K (`rsplit s) ·¹ cc ]* ⟫ U.∥ RP
    YL≡ = cong₂ U._∥_
            (threadEq E (K (`rsplit s) ·¹ (` 𝐒.inj 0F)))
            refl
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = U.⟪ Fr [ K (`rsplit s) ·¹ cc ]* ⟫ U.∥ RP
    -- the two non-junction components of the handle triple cc = (ccA ⊗ ` 0F) ⊗ ccC.
    ccA ccC : Tm (2 + (sB + (sA + n)))
    ccA = proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccC = proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ sB ⋯ ρ₁ ⋯ ρ₂
    ccEq : cc ≡ UR.𝓒[ ccA × 0F × ccC ]
    ccEq = ccTriple
    -- RU-RSplit contractum: fresh φ drop, frame/P weakened by weakenᵣ, two distinct triples.
    contractumR : U.Proc (1 + (2 + (sB + (sA + n))))
    contractumR = U.⟪ (Fr ⋯ᶠ* weakenᵣ) [ UR.𝓒[ wk ccA × 1F × ` 0F ] ⊗ UR.𝓒[ ` 0F × 1F × wk ccC ] ]* ⟫
                    U.∥ (RP U.⋯ₚ weakenᵣ)
    rsplitStep : U.ν redexL UR.─→ₚ U.ν (U.φ U.drop contractumR)
    rsplitStep = subst (λ z → U.ν (U.⟪ Fr [ K (`rsplit s) ·¹ z ]* ⟫ U.∥ RP)
                              UR.─→ₚ
                              U.ν (U.φ U.drop contractumR))
                   (sym ccEq)
                   (UR.RU-RSplit {e₁ = ccA} {e₂ = ccC} Fr)
    leaf-fire : U.ν (push XL) UR.─→ₚ U.ν (U.φ U.drop contractumR)
    leaf-fire = UR.RU-Struct (U.ν-cong (≡→≋ YL≡)) rsplitStep ε
    -- ----- grown-group (RHS) flatten side -----
    τᴿ : sum C₁ᴿ + sum B + m →ₛ syncs B + (syncs C₁ᴿ + (2 + n))
    τᴿ = leafσ σ C₁ᴿ B
    Vτᴿ : VSub τᴿ
    Vτᴿ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ C₁ᴿ (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
             (VSub-canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ sAᴿ 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sAᴿ) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB) (λ _ → V-`))
    XRᴿ : U.Proc (sB + (sAᴿ + (2 + n)))
    XRᴿ = U[ QR ] τᴿ
    pushR : ∀ {kk} → U.Proc (sB + (sAᴿ + (2 + kk))) → U.Proc (2 + (sB + (sAᴿ + kk)))
    pushR {kk} X = (X U.⋯ₚ (assocSwapᵣ sAᴿ 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    ν↓ᴿ : ∀ (X : U.Proc (sB + (sAᴿ + (2 + n)))) →
          U.ν (Bφ C₁ᴿ (Bφ B X)) U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR X)))
    ν↓ᴿ X =
         ν-past-Bφ C₁ᴿ (Bφ B X)
      ◅◅ Bφ-cong C₁ᴿ (U.ν-cong (≡→≋ (Bφ-⋯ B X (assocSwapᵣ sAᴿ 2))))
      ◅◅ Bφ-cong C₁ᴿ (ν-past-Bφ B (X U.⋯ₚ (assocSwapᵣ sAᴿ 2 ↑* sB)))
    rhs : U[ T.ν C₁ᴿ B QR ] σ U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
    rhs = ≡→≋ (Uν-flat σ C₁ᴿ B QR) ◅◅ ν↓ᴿ XRᴿ

    -- ----- grown-leaf (RHS) thread expansion (mirror of lsplit pushR-thread) -----
    ρ₁ᴿ : (sB + (sAᴿ + (2 + n))) →ᵣ (sB + (2 + (sAᴿ + n)))
    ρ₁ᴿ = assocSwapᵣ sAᴿ 2 ↑* sB
    ρ₂ᴿ : (sB + (2 + (sAᴿ + n))) →ᵣ (2 + (sB + (sAᴿ + n)))
    ρ₂ᴿ = assocSwapᵣ sB 2
    rnᴿ : Tm (sB + (sAᴿ + (2 + n))) → Tm (2 + (sB + (sAᴿ + n)))
    rnᴿ t = (t ⋯ ρ₁ᴿ) ⋯ ρ₂ᴿ
    Frᴿ : Frame* (2 + (sB + (sAᴿ + n)))
    Frᴿ = (frame*-⋯ (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ⋯ᶠ* ρ₂ᴿ
    threadEqᴿ : (Ef : Frame* (sum C₁ᴿ + sum B + m)) (p : Tm (sum C₁ᴿ + sum B + m)) →
                (U[ T.⟪ Ef [ p ]* ⟫ ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
                ≡ U.⟪ ((frame*-⋯ Ef τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ⋯ᶠ* ρ₂ᴿ) [ rnᴿ (p ⋯ τᴿ) ]* ⟫
    threadEqᴿ Ef p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁ᴿ) ⋯ ρ₂ᴿ) (frame-plug* Ef τᴿ Vτᴿ)
      ■ cong (_⋯ ρ₂ᴿ) (frame-plug*ᵣ (frame*-⋯ Ef τᴿ Vτᴿ) ρ₁ᴿ)
      ■ frame-plug*ᵣ (frame*-⋯ Ef τᴿ Vτᴿ ⋯ᶠ* ρ₁ᴿ) ρ₂ᴿ )
    pushR-threadᴿ : U.Proc (2 + (sB + (sAᴿ + n)))
    pushR-threadᴿ = (U[ T.⟪ E ⋯ᶠ* 𝐒.rwk [ (` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F) ]* ⟫ ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
    pushR-Pᴿ : U.Proc (2 + (sB + (sAᴿ + n)))
    pushR-Pᴿ = (U[ P T.⋯ₚ 𝐒.rwk ] τᴿ U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ
    pushR-threadEqᴿ : pushR-threadᴿ ≡ U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫
    pushR-threadEqᴿ = threadEqᴿ (E ⋯ᶠ* 𝐒.rwk) ((` 𝐒.inj 0F) ⊗ (` 𝐒.inj 1F))
    -- U-rwk naturality: translating the rwk-renamed residual P is the same as
    -- translating P and inserting the fresh sync slot (sins ↑* syncs B), because
    -- P's variables (all images of ρ⁻) avoid the consumed handle, where τ and τᴿ
    -- agree modulo the insertion by leafσ-rwk-id.
    Prwkeq : U[ P T.⋯ₚ 𝐒.rwk ] τᴿ ≡ U[ P ] τ U.⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)
    Prwkeq =
        cong (λ p → U[ p T.⋯ₚ 𝐒.rwk ] τᴿ) Peq
      ■ cong (λ p → U[ p ] τᴿ) (T.fusionₚ P₀ ρ⁻ 𝐒.rwk)
      ■ U-⋯ₚ P₀
      ■ U-cong P₀ (λ y → sym (leafσ-rwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y)))
      ■ sym (U-σ⋯ P₀)
      ■ cong (U._⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)) (sym (U-⋯ₚ P₀))
      ■ cong (λ p → U[ p ] τ U.⋯ₚ (sins B₁ b₁ B₂ {2 + n} ↑* syncs B)) (sym Peq)

    -- ----- the residual bridge (back) -----
    -- Brwk-slide pulls C₁ᴿ's extra φ-drop binder down to the leaf, reducing the
    -- reconcile to commuting that φ-drop past (Bφ B ; ν) and matching the leaf.
    slid : Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
           U.≋ Bφ C₁ (U.φ U.drop (subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                                    U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}))
    slid = Brwk-slide B₁ {b₁} {B₂} {n} (Bφ B (U.ν (pushR XRᴿ)))
    innerReconcile : Bφ B (U.ν (U.φ U.drop contractumR))
                     U.≋ U.φ U.drop (subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                                      U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n})
    -- pushR XRᴿ splits into the grown thread + P, with the thread expanded via
    -- the proven pushR-threadEqᴿ.  (Reusable building block for leafRec.)
    pushR-bodyᴿ : pushR XRᴿ
                  ≡ U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫ U.∥ pushR-Pᴿ
    pushR-bodyᴿ = cong₂ U._∥_ pushR-threadEqᴿ refl
    leafRec : Bφ B ((U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B))
              U.≋ subst U.Proc (cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)) (Bφ B (U.ν (pushR XRᴿ)))
                    U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
    leafRec = ≡→≋ leafRec≡
      where
        EQ′ : syncs C₁ᴿ + n ≡ syncs C₁ + suc n
        EQ′ = cong (_+ n) (syncs-rwk B₁) ■ sym (+-suc (syncs C₁) n)
        sD′ : ℕ
        sD′ = syncs (suc b₁ ∷ B₂)
        rawR : (sD′ + (1 + (L.length B₁ + n))) →ᵣ (1 + (sD′ + (L.length B₁ + n)))
        rawR = assocSwapᵣ sD′ 1 {L.length B₁ + n}
        rhsR≡ : subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
                ≡ subst U.Proc (sw-cod B₁ {b₁} {B₂} {n})
                    (subst U.Proc (EQ′ ■ sw-dom B₁ {b₁} {B₂} {n}) (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ rawR)
        rhsR≡ = cast-⋯2 (sw-dom B₁ {b₁} {B₂} {n}) (sw-cod B₁ {b₁} {B₂} {n}) (subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ)))) rawR
             ■ cong (λ w → subst U.Proc (sw-cod B₁ {b₁} {B₂} {n}) (w U.⋯ₚ rawR))
                 (ss-U EQ′ (sw-dom B₁ {b₁} {B₂} {n}) {t = Bφ B (U.ν (pushR XRᴿ))})
        e2 : syncs C₁ᴿ + n ≡ sD′ + (1 + (L.length B₁ + n))
        e2 = EQ′ ■ sw-dom B₁ {b₁} {B₂} {n}
        rhsPush : subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
                  ≡ Bφ B (subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                            (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B)))
        rhsInner : subst U.Proc e2 (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ rawR
                   ≡ Bφ B (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        rhsInner =
            cong (U._⋯ₚ rawR) (subst-Bφ e2 B (U.ν (pushR XRᴿ)))
          ■ Bφ-⋯ B (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ))) rawR
        rhsPush = rhsR≡
                ■ cong (subst U.Proc (sw-cod B₁ {b₁} {B₂} {n})) rhsInner
                ■ subst-Bφ (sw-cod B₁ {b₁} {B₂} {n}) B
                    (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        rhsνOut : subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                     (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
                  ≡ U.ν (subst U.Proc (cong (2 +_) (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                          (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ)
                             U.⋯ₚ ((rawR ↑* syncs B) ↑* 2)))
        rhsνOut =
            cong (subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
              (cong (U._⋯ₚ (rawR ↑* syncs B)) (subst-ν (cong (syncs B +_) e2) (pushR XRᴿ)))
          ■ subst-ν (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
              (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ) U.⋯ₚ ((rawR ↑* syncs B) ↑* 2))
        νInner : (contractumR U.⋯ₚ assocSwapᵣ 1 2) U.⋯ₚ ((assocSwapᵣ 1 (syncs B)) ↑* 2)
                 ≡ subst U.Proc (cong (2 +_) (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                     (subst U.Proc (cong (2 +_) (cong (syncs B +_) e2)) (pushR XRᴿ)
                        U.⋯ₚ ((rawR ↑* syncs B) ↑* 2))
        SQ : ℕ → ℕ
        SQ section = suc (suc section)
        ρρ : (syncs B + (sD′ + (1 + (L.length B₁ + n)))) →ᵣ (syncs B + (1 + (sD′ + (L.length B₁ + n))))
        ρρ = (rawR ↑* syncs B)
        -- distribute RHS subst/⋯ over the ∥ of pushR-bodyᴿ
        rhsSplit : subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                     (subst U.Proc (cong SQ (cong (syncs B +_) e2)) (pushR XRᴿ) U.⋯ₚ (ρρ ↑* 2))
                   ≡ subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                       ( (subst U.Proc (cong SQ (cong (syncs B +_) e2))
                           (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
                       U.∥ (subst U.Proc (cong SQ (cong (syncs B +_) e2)) pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2)) )
        rhsSplit =
            cong (subst U.Proc (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))))
              ( cong (λ z → (subst U.Proc (cong SQ (cong (syncs B +_) e2)) z) U.⋯ₚ (ρρ ↑* 2)) pushR-bodyᴿ
              ■ cong (U._⋯ₚ (ρρ ↑* 2))
                  (subst-∥f (λ z → z) (cong SQ (cong (syncs B +_) e2))
                     (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) pushR-Pᴿ) )
        -- ===== outer renaming reconciliation (fresh-φ insertion commutes) =====
        Θ : (syncs B + (sA + (2 + n))) →ᵣ (syncs B + (sAᴿ + (2 + n)))
        Θ = sins B₁ b₁ B₂ {2 + n} ↑* syncs B
        E-dom : (2 + (syncs B + (sAᴿ + n))) ≡ SQ (syncs B + (sD′ + (1 + (L.length B₁ + n))))
        E-dom = cong SQ (cong (syncs B +_) e2)
        E-cod : SQ (syncs B + (1 + (sD′ + (L.length B₁ + n)))) ≡ SQ (syncs B + suc (sA + n))
        E-cod = cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
        θ1R : SQ (syncs B + (sAᴿ + n)) →ᵣ SQ (syncs B + (1 + (sD′ + (L.length B₁ + n))))
        θ1R = subst (λ z → z →ᵣ SQ (syncs B + (1 + (sD′ + (L.length B₁ + n))))) (sym E-dom) (ρρ ↑* 2)
        ρR' : SQ (syncs B + (sAᴿ + n)) →ᵣ SQ (syncs B + suc (sA + n))
        ρR' = subst (λ z → SQ (syncs B + (sAᴿ + n)) →ᵣ z) E-cod θ1R
        ρLtot : (syncs B + (sA + (2 + n))) →ᵣ (2 + (syncs B + (1 + (sA + n))))
        ρLtot = ρ₁ ·ₖ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
        ρRtot : (syncs B + (sA + (2 + n))) →ᵣ (2 + (syncs B + suc (sA + n)))
        ρRtot = Θ ·ₖ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR'))
        sdom : ∀ {a b c} (p : a ≡ b) (Q : U.Proc a) (θ : b →ᵣ c) →
               subst U.Proc p Q U.⋯ₚ θ ≡ Q U.⋯ₚ subst (λ z → z →ᵣ c) (sym p) θ
        sdom refl Q θ = refl
        toℕ-subst-dom : ∀ {A A′ Bb} (e : A ≡ A′) (ρ : A →ᵣ Bb) (y : 𝔽 A′) →
                        Fin.toℕ (subst (λ z → z →ᵣ Bb) e ρ y) ≡ Fin.toℕ (ρ (subst 𝔽 (sym e) y))
        toℕ-subst-dom refl ρ y = refl
        fuseL : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
                Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
                ≡ Y U.⋯ₚ ρLtot
        fuseL Y =
            U.fusionₚ (Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ) (assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2)
          ■ U.fusionₚ (Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂) weakenᵣ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))
          ■ U.fusionₚ (Y U.⋯ₚ ρ₁) ρ₂ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2)))
          ■ U.fusionₚ Y ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
        fuseR4 : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
                 Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ U.⋯ₚ ρR' ≡ Y U.⋯ₚ ρRtot
        fuseR4 Y =
            U.fusionₚ (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ) ρ₂ᴿ ρR'
          ■ U.fusionₚ (Y U.⋯ₚ Θ) ρ₁ᴿ (ρ₂ᴿ ·ₖ ρR')
          ■ U.fusionₚ Y Θ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR'))
        collapseR : ∀ (Z : U.Proc (SQ (syncs B + (sAᴿ + n)))) →
                    subst U.Proc E-cod (subst U.Proc E-dom Z U.⋯ₚ (ρρ ↑* 2))
                    ≡ Z U.⋯ₚ ρR'
        collapseR Z =
            cong (subst U.Proc E-cod) (sdom E-dom Z (ρρ ↑* 2))
          ■ sym (subst-⋯ₚ-cod E-cod Z θ1R)
        ρL≗ρR : ρLtot ≗ ρRtot
        ρL≗ρR i = go
          where
            toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
            toℕ-subst𝔽 refl y = refl
            eAR : sAᴿ ≡ suc sA
            eAR = syncs-rwk B₁
            sD′≤sA : sD′ Nat.≤ sA
            sD′≤sA = sD≤ B₁ {b₁} {B₂}
            sA≤sAᴿ : sA Nat.≤ sAᴿ
            sA≤sAᴿ = subst (sA Nat.≤_) (sym eAR) (Nat.n≤1+n sA)
            sD′≤sAᴿ : sD′ Nat.≤ sAᴿ
            sD′≤sAᴿ = Nat.≤-trans sD′≤sA sA≤sAᴿ
            sB2≤3di : syncs B Nat.≤ Fin.toℕ i → syncs B + 2 Nat.≤ 3 + Fin.toℕ i
            sB2≤3di h = Nat.≤-trans (Nat.+-monoˡ-≤ 2 h)
                          (Nat.≤-trans (Nat.+-monoʳ-≤ (Fin.toℕ i) (Nat.n≤1+n 2))
                                       (Nat.≤-reflexive (Nat.+-comm (Fin.toℕ i) 3)))
            v2R : 𝔽 (SQ (syncs B + (sAᴿ + n)))
            v2R = ρ₂ᴿ (ρ₁ᴿ (Θ i))
            w2 : 𝔽 (SQ (syncs B + (sD′ + (1 + (L.length B₁ + n)))))
            w2 = subst 𝔽 (sym (sym E-dom)) v2R
            lhsSB : Fin.toℕ i Nat.< syncs B → Fin.toℕ (ρLtot i) ≡ 2 + Fin.toℕ i
            lhsSB p =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-mid 1 (syncs B) (Fin.reduce≥ X4 q) ge lt ■ cong (Nat._∸ 1) redX)
              where
                v1 = toℕ-↑*-lt (assocSwapᵣ sA 2) (syncs B) i p
                v2 = toℕ-assoc-lt (syncs B) 2 (ρ₁ i) (subst (Nat._< syncs B) (sym v1) p) ■ cong (2 +_) v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                       (subst (3 Nat.≤_) (sym v3) (Nat.m≤m+n 3 (Fin.toℕ i))) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
                ge = subst (1 Nat.≤_) (sym redX) (Nat.s≤s Nat.z≤n)
                lt = subst (Nat._< suc (syncs B)) (sym redX) (Nat.s≤s p)
            rhsSB : Fin.toℕ i Nat.< syncs B → Fin.toℕ (ρRtot i) ≡ 2 + Fin.toℕ i
            rhsSB p =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) (toℕ-↑*-lt rawR (syncs B) (Fin.reduce≥ w2 q2) (subst (Nat._< syncs B) (sym redw2) p) ■ redw2)
              where
                r1 = toℕ-↑*-lt (sins B₁ b₁ B₂ {2 + n}) (syncs B) i p
                r2 = toℕ-↑*-lt (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) (subst (Nat._< syncs B) (sym r1) p) ■ r1
                r3 = toℕ-assoc-lt (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (Nat._< syncs B) (sym r2) p) ■ cong (2 +_) r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
            lhsSA : syncs B Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA → Fin.toℕ (ρLtot i) ≡ 3 + Fin.toℕ i
            lhsSA sB≤ di<A =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-ge 1 (syncs B) (Fin.reduce≥ X4 q) ge ■ redX)
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sA = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sA (subst (Nat._< syncs B + sA) (sym recon) di<A)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-lt sA 2 (Fin.reduce≥ i sB≤) (subst (Nat._< sA) (sym rdi≡) rd<sA) ■ cong (2 +_) rdi≡)
                   ■ comm3 (syncs B) 2 (Fin.toℕ i Nat.∸ syncs B) ■ cong (2 +_) recon
                v2 = toℕ-assoc-ge (syncs B) 2 (ρ₁ i)
                       (subst (syncs B + 2 Nat.≤_) (sym v1) (subst (Nat._≤ 2 + Fin.toℕ i) (Nat.+-comm 2 (syncs B)) (Nat.+-monoʳ-≤ 2 sB≤))) ■ v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                       (subst (3 Nat.≤_) (sym v3) (Nat.m≤m+n 3 (Fin.toℕ i))) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
                ge = subst (suc (syncs B) Nat.≤_) (sym redX) (Nat.s≤s sB≤)
            rhsSAlo : syncs B Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sD′ → Fin.toℕ (ρRtot i) ≡ 3 + Fin.toℕ i
            rhsSAlo sB≤ di<lo =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-lt sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) (subst (Nat._< sD′) (sym rr≡) rd<sD) ■ cong (1 +_) rr≡)
                            ■ comm3 (syncs B) 1 (Fin.toℕ i Nat.∸ syncs B) ■ cong (1 +_) recon )
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sD = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sD′ (subst (Nat._< syncs B + sD′) (sym recon) di<lo)
                rd<sAᴿ = Nat.<-≤-trans rd<sD sD′≤sAᴿ
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-lo B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (Nat._< sD′) (sym rdi≡) rd<sD) ■ rdi≡)
                   ■ recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) sB≤
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-lt sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (Nat._< sAᴿ) (sym redΘ) rd<sAᴿ) ■ cong (2 +_) redΘ)
                   ■ comm3 (syncs B) 2 (Fin.toℕ i Nat.∸ syncs B) ■ cong (2 +_) recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i))
                       (subst (syncs B + 2 Nat.≤_) (sym r2) (subst (Nat._≤ 2 + Fin.toℕ i) (Nat.+-comm 2 (syncs B)) (Nat.+-monoʳ-≤ 2 sB≤))) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) sB≤
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2
            rhsSAhi : syncs B Nat.≤ Fin.toℕ i → syncs B + sD′ Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA → Fin.toℕ (ρRtot i) ≡ 3 + Fin.toℕ i
            rhsSAhi sB≤ sDle di<A =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-ge sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) sD1≤rr ■ rr≡)
                            ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon )
              where
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                rd<sA = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) sA (subst (Nat._< syncs B + sA) (sym recon) di<A)
                rd≥sD = Nat.+-cancelˡ-≤ (syncs B) sD′ (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sD′ Nat.≤_) (sym recon) sDle)
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) rd≥sD) ■ cong suc rdi≡)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.+-∸-assoc 1 sB≤
                sucrd<sAᴿ = subst (suc (Fin.toℕ i Nat.∸ syncs B) Nat.<_) (sym eAR) (Nat.s≤s rd<sA)
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-lt sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (Nat._< sAᴿ) (sym redΘ) sucrd<sAᴿ) ■ cong (2 +_) redΘ)
                   ■ comm3 (syncs B) 3 (Fin.toℕ i Nat.∸ syncs B) ■ cong (3 +_) recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B + 2 Nat.≤_) (sym r2) (sB2≤3di sB≤)) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.m≤m+n 2 (1 + Fin.toℕ i))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2 ■ Nat.+-∸-assoc 1 sB≤
                sD1≤rr = Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm sD′ 1)) (subst (suc sD′ Nat.≤_) (sym rr≡) (Nat.s≤s rd≥sD))
            lhsTWO : syncs B + sA Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA + 2 → Fin.toℕ (ρLtot i) ≡ (Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA
            lhsTWO sBsA≤ di<T =
                toℕ-↑*-lt (assocSwapᵣ 1 (syncs B)) 2 X4 (subst (Nat._< 2) (sym v4) t2<2) ■ v4
              where
                sB≤ = Nat.≤-trans (Nat.m≤m+n (syncs B) sA) sBsA≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA≤rd = Nat.+-cancelˡ-≤ (syncs B) sA (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sA Nat.≤_) (sym recon) sBsA≤)
                rd<sA2 = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) (sA + 2) (subst (Nat._< syncs B + (sA + 2)) (sym recon) (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc (syncs B) sA 2) di<T))
                t2<2 = Nat.+-cancelˡ-< sA ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA) 2 (subst (Nat._< sA + 2) (sym (Nat.m+[n∸m]≡n sA≤rd)) rd<sA2)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-mid sA 2 (Fin.reduce≥ i sB≤) (subst (sA Nat.≤_) (sym rdi≡) sA≤rd) (subst (Nat._< sA + 2) (sym rdi≡) rd<sA2) ■ cong (Nat._∸ sA) rdi≡)
                v2 = toℕ-assoc-mid (syncs B) 2 (ρ₁ i) (subst (syncs B Nat.≤_) (sym v1) (Nat.m≤m+n (syncs B) _)) (subst (Nat._< syncs B + 2) (sym v1) (Nat.+-monoʳ-< (syncs B) t2<2))
                   ■ cong (Nat._∸ syncs B) v1 ■ Nat.m+n∸m≡n (syncs B) ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA)
                v3 = cong suc v2
                v4 = toℕ-assoc-mid 1 2 (weakenᵣ (ρ₂ (ρ₁ i))) (subst (1 Nat.≤_) (sym v3) (Nat.s≤s Nat.z≤n)) (subst (Nat._< 3) (sym v3) (Nat.s≤s t2<2)) ■ cong (Nat._∸ 1) v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
            rhsTWO : syncs B + sA Nat.≤ Fin.toℕ i → Fin.toℕ i Nat.< syncs B + sA + 2 → Fin.toℕ (ρRtot i) ≡ (Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA
            rhsTWO sBsA≤ di<T =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-lt ρρ 2 w2 (subst (Nat._< 2) (sym w2N) t2<2)
              ■ w2N
              where
                sB≤ = Nat.≤-trans (Nat.m≤m+n (syncs B) sA) sBsA≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA≤rd = Nat.+-cancelˡ-≤ (syncs B) sA (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + sA Nat.≤_) (sym recon) sBsA≤)
                rd<sA2 = Nat.+-cancelˡ-< (syncs B) (Fin.toℕ i Nat.∸ syncs B) (sA + 2) (subst (Nat._< syncs B + (sA + 2)) (sym recon) (subst (Fin.toℕ i Nat.<_) (Nat.+-assoc (syncs B) sA 2) di<T))
                t2<2 = Nat.+-cancelˡ-< sA ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA) 2 (subst (Nat._< sA + 2) (sym (Nat.m+[n∸m]≡n sA≤rd)) rd<sA2)
                sD≤rd = Nat.≤-trans sD′≤sA sA≤rd
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) sD≤rd) ■ cong suc rdi≡)
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.m≤m+n (syncs B) (suc (Fin.toℕ i Nat.∸ syncs B)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.m+n∸m≡n (syncs B) (suc (Fin.toℕ i Nat.∸ syncs B))
                sucrd≥sAᴿ = subst (Nat._≤ suc (Fin.toℕ i Nat.∸ syncs B)) (sym eAR) (Nat.s≤s sA≤rd)
                sucrd<sAᴿ2 = subst (suc (Fin.toℕ i Nat.∸ syncs B) Nat.<_) (sym (cong (_+ 2) eAR)) (Nat.s≤s rd<sA2)
                midEq = cong (λ z → suc (Fin.toℕ i Nat.∸ syncs B) Nat.∸ z) eAR
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-mid sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (sAᴿ Nat.≤_) (sym redΘ) sucrd≥sAᴿ) (subst (Nat._< sAᴿ + 2) (sym redΘ) sucrd<sAᴿ2) ■ cong (Nat._∸ sAᴿ) redΘ ■ midEq)
                r3 = toℕ-assoc-mid (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B Nat.≤_) (sym r2) (Nat.m≤m+n (syncs B) _)) (subst (Nat._< syncs B + 2) (sym r2) (Nat.+-monoʳ-< (syncs B) t2<2))
                   ■ cong (Nat._∸ syncs B) r2 ■ Nat.m+n∸m≡n (syncs B) ((Fin.toℕ i Nat.∸ syncs B) Nat.∸ sA)
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
            lhsN : syncs B + sA + 2 Nat.≤ Fin.toℕ i → Fin.toℕ (ρLtot i) ≡ suc (Fin.toℕ i)
            lhsN sBsA2≤ =
                toℕ-↑*-ge (assocSwapᵣ 1 (syncs B)) 2 X4 q
              ■ cong (2 +_) (toℕ-assoc-ge 1 (syncs B) (Fin.reduce≥ X4 q) (subst (1 + syncs B Nat.≤_) (sym redX) B1≤) ■ redX)
              ■ cong suc (Nat.m+[n∸m]≡n oneleq)
              where
                sB≤ = Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (syncs B) sA) (Nat.m≤m+n (syncs B + sA) 2)) sBsA2≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA2≤rd = Nat.+-cancelˡ-≤ (syncs B) (sA + 2) (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + (sA + 2) Nat.≤_) (sym recon) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤))
                sB2≤di = Nat.≤-trans (Nat.+-monoʳ-≤ (syncs B) (Nat.m≤n+m 2 sA)) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤)
                two≤di = Nat.≤-trans (Nat.m≤n+m 2 (syncs B + sA)) sBsA2≤
                oneleq = Nat.≤-trans (Nat.n≤1+n 1) two≤di
                B1≤ = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B) (Nat.s≤s Nat.z≤n) ■ Nat.+-comm (syncs B) 1) (Nat.∸-monoˡ-≤ 1 sB2≤di)
                v1 = toℕ-↑*-ge (assocSwapᵣ sA 2) (syncs B) i sB≤
                   ■ cong (syncs B +_) (toℕ-assoc-ge sA 2 (Fin.reduce≥ i sB≤) (subst (sA + 2 Nat.≤_) (sym rdi≡) sA2≤rd) ■ rdi≡) ■ recon
                v2 = toℕ-assoc-ge (syncs B) 2 (ρ₁ i) (subst (syncs B + 2 Nat.≤_) (sym v1) sB2≤di) ■ v1
                v3 = cong suc v2
                v4 = toℕ-assoc-ge 1 2 (weakenᵣ (ρ₂ (ρ₁ i))) (subst (3 Nat.≤_) (sym v3) (Nat.s≤s two≤di)) ■ v3
                X4 = assocSwapᵣ 1 2 (weakenᵣ (ρ₂ (ρ₁ i)))
                q  = subst (2 Nat.≤_) (sym v4) (Nat.≤-trans two≤di (Nat.n≤1+n (Fin.toℕ i)))
                redX = toℕ-reduce≥ X4 q ■ cong (Nat._∸ 2) v4
            rhsN : syncs B + sA + 2 Nat.≤ Fin.toℕ i → Fin.toℕ (ρRtot i) ≡ suc (Fin.toℕ i)
            rhsN sBsA2≤ =
                toℕ-subst-cod E-cod θ1R v2R
              ■ toℕ-subst-dom (sym E-dom) (ρρ ↑* 2) v2R
              ■ toℕ-↑*-ge ρρ 2 w2 q2
              ■ cong (2 +_) ( toℕ-↑*-ge rawR (syncs B) (Fin.reduce≥ w2 q2) sB≤rw
                            ■ cong (syncs B +_) (toℕ-assoc-ge sD′ 1 (Fin.reduce≥ (Fin.reduce≥ w2 q2) sB≤rw) sD1≤rr ■ rr≡)
                            ■ Nat.m+[n∸m]≡n sB≤di∸1 )
              ■ cong suc (Nat.m+[n∸m]≡n oneleq)
              where
                sB≤ = Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (syncs B) sA) (Nat.m≤m+n (syncs B + sA) 2)) sBsA2≤
                rdi≡ = toℕ-reduce≥ i sB≤
                recon = Nat.m+[n∸m]≡n sB≤
                sA2≤rd = Nat.+-cancelˡ-≤ (syncs B) (sA + 2) (Fin.toℕ i Nat.∸ syncs B) (subst (syncs B + (sA + 2) Nat.≤_) (sym recon) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤))
                sB2≤di = Nat.≤-trans (Nat.+-monoʳ-≤ (syncs B) (Nat.m≤n+m 2 sA)) (subst (Nat._≤ Fin.toℕ i) (Nat.+-assoc (syncs B) sA 2) sBsA2≤)
                two≤di = Nat.≤-trans (Nat.m≤n+m 2 (syncs B + sA)) sBsA2≤
                oneleq = Nat.≤-trans (Nat.n≤1+n 1) two≤di
                sD≤rd = Nat.≤-trans sD′≤sA (Nat.≤-trans (Nat.m≤m+n sA 2) sA2≤rd)
                r1 = toℕ-↑*-ge (sins B₁ b₁ B₂ {2 + n}) (syncs B) i sB≤
                   ■ cong (syncs B +_) (sins-toℕ-hi B₁ b₁ B₂ (Fin.reduce≥ i sB≤) (subst (sD′ Nat.≤_) (sym rdi≡) sD≤rd) ■ cong suc rdi≡)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                bnd2 = subst (syncs B Nat.≤_) (sym r1) (Nat.≤-trans sB≤ (Nat.n≤1+n (Fin.toℕ i)))
                redΘ = toℕ-reduce≥ (Θ i) bnd2 ■ cong (Nat._∸ syncs B) r1 ■ Nat.+-∸-assoc 1 sB≤
                sAᴿ2≤sucrd = subst (Nat._≤ suc (Fin.toℕ i Nat.∸ syncs B)) (sym (cong (_+ 2) eAR)) (Nat.s≤s sA2≤rd)
                r2 = toℕ-↑*-ge (assocSwapᵣ sAᴿ 2) (syncs B) (Θ i) bnd2
                   ■ cong (syncs B +_) (toℕ-assoc-ge sAᴿ 2 (Fin.reduce≥ (Θ i) bnd2) (subst (sAᴿ + 2 Nat.≤_) (sym redΘ) sAᴿ2≤sucrd) ■ redΘ)
                   ■ Nat.+-suc (syncs B) (Fin.toℕ i Nat.∸ syncs B) ■ cong suc recon
                r3 = toℕ-assoc-ge (syncs B) 2 (ρ₁ᴿ (Θ i)) (subst (syncs B + 2 Nat.≤_) (sym r2) (Nat.≤-trans sB2≤di (Nat.n≤1+n (Fin.toℕ i)))) ■ r2
                w2N = toℕ-subst𝔽 (sym (sym E-dom)) v2R ■ r3
                q2  = subst (2 Nat.≤_) (sym w2N) (Nat.≤-trans two≤di (Nat.n≤1+n (Fin.toℕ i)))
                redw2 = toℕ-reduce≥ w2 q2 ■ cong (Nat._∸ 2) w2N
                B1≤ = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B) (Nat.s≤s Nat.z≤n) ■ Nat.+-comm (syncs B) 1) (Nat.∸-monoˡ-≤ 1 sB2≤di)
                sB≤di∸1 = Nat.≤-trans (Nat.n≤1+n (syncs B)) B1≤
                sB≤rw = subst (syncs B Nat.≤_) (sym redw2) sB≤di∸1
                rr≡ = toℕ-reduce≥ (Fin.reduce≥ w2 q2) sB≤rw ■ cong (Nat._∸ syncs B) redw2
                sBsA1≤di∸1 = subst (Nat._≤ Fin.toℕ i Nat.∸ 1) (Nat.+-∸-assoc (syncs B + sA) (Nat.s≤s Nat.z≤n) ■ Nat.+-assoc (syncs B) sA 1) (Nat.∸-monoˡ-≤ 1 sBsA2≤)
                sA1≤rr = subst (Nat._≤ (Fin.toℕ i Nat.∸ 1) Nat.∸ syncs B) (Nat.m+n∸m≡n (syncs B) (sA + 1)) (Nat.∸-monoˡ-≤ (syncs B) sBsA1≤di∸1)
                sD1≤rr = subst (sD′ + 1 Nat.≤_) (sym rr≡) (Nat.≤-trans (Nat.+-monoˡ-≤ 1 sD′≤sA) sA1≤rr)
            go : ρLtot i ≡ ρRtot i
            go with Fin.toℕ i Nat.<? syncs B
            ... | yes p = Fin.toℕ-injective (lhsSB p ■ sym (rhsSB p))
            ... | no ¬p with Fin.toℕ i Nat.<? (syncs B + sD′)
            ...   | yes qlo = Fin.toℕ-injective (lhsSA (Nat.≮⇒≥ ¬p) (Nat.<-≤-trans qlo (Nat.+-monoʳ-≤ (syncs B) sD′≤sA)) ■ sym (rhsSAlo (Nat.≮⇒≥ ¬p) qlo))
            ...   | no ¬qlo with Fin.toℕ i Nat.<? (syncs B + sA)
            ...     | yes rhi = Fin.toℕ-injective (lhsSA (Nat.≮⇒≥ ¬p) rhi ■ sym (rhsSAhi (Nat.≮⇒≥ ¬p) (Nat.≮⇒≥ ¬qlo) rhi))
            ...     | no ¬rhi with Fin.toℕ i Nat.<? (syncs B + sA + 2)
            ...       | yes ttwo = Fin.toℕ-injective (lhsTWO (Nat.≮⇒≥ ¬rhi) ttwo ■ sym (rhsTWO (Nat.≮⇒≥ ¬rhi) ttwo))
            ...       | no ¬ttwo = Fin.toℕ-injective (lhsN (Nat.≮⇒≥ ¬ttwo) ■ sym (rhsN (Nat.≮⇒≥ ¬ttwo)))
        outerRec : ∀ (Y : U.Proc (syncs B + (sA + (2 + n)))) →
          Y U.⋯ₚ ρ₁ U.⋯ₚ ρ₂ U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
          ≡ subst U.Proc E-cod
              (subst U.Proc E-dom (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ) U.⋯ₚ (ρρ ↑* 2))
        outerRec Y =
            fuseL Y
          ■ U.⋯ₚ-cong Y ρL≗ρR
          ■ sym (fuseR4 Y)
          ■ sym (collapseR (Y U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ))
        pushRPᴿ-fac : pushR-Pᴿ ≡ U[ P ] τ U.⋯ₚ Θ U.⋯ₚ ρ₁ᴿ U.⋯ₚ ρ₂ᴿ
        pushRPᴿ-fac = cong (λ z → (z U.⋯ₚ ρ₁ᴿ) U.⋯ₚ ρ₂ᴿ) Prwkeq
        Prest≡ : RP U.⋯ₚ weakenᵣ U.⋯ₚ assocSwapᵣ 1 2 U.⋯ₚ (assocSwapᵣ 1 (syncs B) ↑* 2)
                 ≡ subst U.Proc E-cod (subst U.Proc E-dom pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2))
        Prest≡ =
            outerRec (U[ P ] τ)
          ■ cong (λ z → subst U.Proc E-cod (subst U.Proc E-dom z U.⋯ₚ (ρρ ↑* 2)))
              (sym pushRPᴿ-fac)
        -- ===== thread-leaf reconciliation (frame naturality + body triple) =====
        frameLeafeqᴿ : frame*-⋯ E τ Vτ ⋯ᶠ* Θ ≡ frame*-⋯ (E ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ
        frameLeafeqᴿ = sym
            ( cong (λ EE → frame*-⋯ (EE ⋯ᶠ* 𝐒.rwk) τᴿ Vτᴿ) Eeq
            ■ cong (λ EE → frame*-⋯ EE τᴿ Vτᴿ) (⋯ᶠ*-fuse E₀ ρ⁻ 𝐒.rwk)
            ■ F-⋯f*-fuse E₀ Vτᴿ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ)
            ■ frame*-cong E₀ (·ₖ-VSubᵣ (ρ⁻ ·ₖ 𝐒.rwk) Vτᴿ) (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) Θ (λ x → V-`))
                (λ y → sym (leafσ-rwk-id σ B₁ B₂ B b₁ (ρ⁻ y) (ρ⁻-skip y)))
            ■ sym (F-σ⋯ E₀ (·ₖ-VSubᵣ ρ⁻ Vτ) Θ (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vτ y) Θ (λ x → V-`)))
            ■ cong (_⋯ᶠ* Θ) (sym (F-⋯f*-fuse E₀ Vτ (·ₖ-VSubᵣ ρ⁻ Vτ)))
            ■ cong (λ EE → frame*-⋯ EE τ Vτ ⋯ᶠ* Θ) (sym Eeq) )
        frame-eq : (Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* assocSwapᵣ 1 2 ⋯ᶠ* (assocSwapᵣ 1 (syncs B) ↑* 2) ≡ Frᴿ ⋯ᶠ* ρR'
        frame-eq =
            ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁ ⋯ᶠ* ρ₂ ⋯ᶠ* weakenᵣ) (assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2)
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁ ⋯ᶠ* ρ₂) weakenᵣ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ρ₂ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2)))
          ■ ⋯ᶠ*-fuse (frame*-⋯ E τ Vτ) ρ₁ (ρ₂ ·ₖ (weakenᵣ ·ₖ (assocSwapᵣ 1 2 ·ₖ (assocSwapᵣ 1 (syncs B) ↑* 2))))
          ■ ⋯ᶠ*-cong (frame*-⋯ E τ Vτ) ρL≗ρR
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ) Θ (ρ₁ᴿ ·ₖ (ρ₂ᴿ ·ₖ ρR')))
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* Θ) ρ₁ᴿ (ρ₂ᴿ ·ₖ ρR'))
          ■ sym (⋯ᶠ*-fuse (frame*-⋯ E τ Vτ ⋯ᶠ* Θ ⋯ᶠ* ρ₁ᴿ) ρ₂ᴿ ρR')
          ■ cong (λ z → z ⋯ᶠ* ρ₁ᴿ ⋯ᶠ* ρ₂ᴿ ⋯ᶠ* ρR') frameLeafeqᴿ
        thread≡ : U.⟪ ((Fr ⋯ᶠ* weakenᵣ) [ ((wk ccA ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk ccC) ]*)
                        ⋯ assocSwapᵣ 1 2 ⋯ (assocSwapᵣ 1 (syncs B) ↑* 2) ⟫
                  ≡ subst U.Proc E-cod (subst U.Proc E-dom (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
        thread≡ =
            cong U.⟪_⟫ ( cong (_⋯ (assocSwapᵣ 1 (syncs B) ↑* 2)) (frame-plug*ᵣ (Fr ⋯ᶠ* weakenᵣ) (assocSwapᵣ 1 2))
                       ■ frame-plug*ᵣ ((Fr ⋯ᶠ* weakenᵣ) ⋯ᶠ* assocSwapᵣ 1 2) (assocSwapᵣ 1 (syncs B) ↑* 2) )
          ■ cong U.⟪_⟫ (cong₂ _[_]* frame-eq {!!})
          ■ cong U.⟪_⟫ (sym (frame-plug*ᵣ Frᴿ ρR'))
          ■ sym (collapseR (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫))
        νInner =
            cong₂ U._∥_ thread≡ Prest≡
          ■ sym ( rhsSplit
                ■ subst-∥f (λ z → z) (cong SQ (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n})))
                    (subst U.Proc (cong SQ (cong (syncs B +_) e2))
                       (U.⟪ Frᴿ [ rnᴿ (τᴿ (𝐒.inj 0F)) ⊗ rnᴿ (τᴿ (𝐒.inj 1F)) ]* ⟫) U.⋯ₚ (ρρ ↑* 2))
                    (subst U.Proc (cong SQ (cong (syncs B +_) e2)) pushR-Pᴿ U.⋯ₚ (ρρ ↑* 2)) )
        bodyEq : (U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B)
                 ≡ subst U.Proc (cong (syncs B +_) (sw-cod B₁ {b₁} {B₂} {n}))
                     (subst U.Proc (cong (syncs B +_) e2) (U.ν (pushR XRᴿ)) U.⋯ₚ (rawR ↑* syncs B))
        bodyEq = cong U.ν νInner ■ sym rhsνOut
        leafRec≡ : Bφ B ((U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2)) U.⋯ₚ assocSwapᵣ 1 (syncs B))
                   ≡ subst U.Proc EQ′ (Bφ B (U.ν (pushR XRᴿ))) U.⋯ₚ sw-cast B₁ {b₁} {B₂} {n}
        leafRec≡ = cong (Bφ B) bodyEq ■ sym rhsPush
    innerReconcile =
         Bφ-cong B (Eq*.return U.νφ-comm′)
      ◅◅ Bφ-φ-comm B U.drop (U.ν (contractumR U.⋯ₚ assocSwapᵣ 1 2))
      ◅◅ U.φ-cong leafRec
    middleReconcile : Bφ C₁ (Bφ B (U.ν (U.φ U.drop contractumR)))
                      U.≋ Bφ C₁ᴿ (Bφ B (U.ν (pushR XRᴿ)))
    middleReconcile = Bφ-cong C₁ innerReconcile ◅◅ Eq*.symmetric _ slid
    back : Bφ C₁ (Bφ B (U.ν (U.φ U.drop contractumR))) U.≋ U[ T.ν C₁ᴿ B QR ] σ
    back = middleReconcile ◅◅ Eq*.symmetric _ rhs
