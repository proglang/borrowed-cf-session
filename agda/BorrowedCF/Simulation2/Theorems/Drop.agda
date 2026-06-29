module BorrowedCF.Simulation2.Theorems.Drop where


-- | Forward-simulation case R-Drop for the reworked paper-matching process
--   definitions.  Exports U-drop.
--
--   Route (mirrors Theorems/Acq.agda): U[ ν (suc b₁ ∷ B₁) B₂ … ]σ flattens
--   (Uν-flat) to  ν (Bφ (suc b₁ ∷ B₁) (Bφ B₂ leaf)).  When B₁ is nonempty the
--   head φ ϕ[ suc b₁ ] = φ drop is pushed past the rest of the φ-nests to the
--   leaf; RU-Drop fires; the φ drop (now φ acq) is pulled back out and the leaf
--   substitution reconciled to U[RHS]σ.  When B₁ = [] the dropped chain is a
--   singleton — handled by the typing inversion (see below).
--
--   The Bφ transpose engine (lines below) is COPIED verbatim from
--   Theorems/Acq.agda (itself copied from Splits/Congruence), because those
--   modules carry open interaction metas downstream and are unimportable.

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation2.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation2.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥
        ; toℕ-↑*-ge; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation2.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation2.TranslationProperties using (VChan; Value-subst; chanTriple-V)

------------------------------------------------------------------------
-- COPIED transpose engine from Simulation2.Theorems.Splits (hole-free prefix).
------------------------------------------------------------------------

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
canonₛ (b ∷ [])      cc = λ _ → chanTriple cc
canonₛ {n} (b ∷ B@(_ ∷ _)) (e1 , x , e2) =
  λ y → subst Tm (+-suc (syncs B) n)
          ([ const (chanTriple (wk e1 , suc x , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
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

-- canonₛ is natural in its channel triple under target renamings.
canonₛ-nat : ∀ {a bb} (B : BindGroup) (cc : UChan a) (ρ : a →ᵣ bb) (i : 𝔽 (sum B)) →
             canonₛ B cc i ⋯ (ρ ↑* syncs B) ≡ canonₛ B (mapᶜ ρ cc) i
canonₛ-nat []            cc ρ ()
canonₛ-nat (b ∷ [])      (e1 , x , e2) ρ i = refl
canonₛ-nat {a} {bb} (b ∷ B@(_ ∷ _)) (e1 , x , e2) ρ i
  with Fin.splitAt b i | canonₛ-nat B (` 0F , suc x , wk e2) (ρ ↑)
... | inj₁ j | _  = ΘrelEqᵍ (syncs B) ρ (const chL j)
                  ■ cong (subst Tm (+-suc (syncs B) bb)) (chReqᵍ (syncs B) e1 x ρ)
  where chL = chanTriple (wk e1 , suc x , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
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
                     ([ const (chanTriple (wk e1 , suc x , ` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB) , τ ]′ (Fin.splitAt b y))))

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


------------------------------------------------------------------------
-- Codomain (multi-step / silent) and the leaf firing.
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

-- a reduction star transports along a scope-index equality.
─→ₚ*-subst : ∀ {a b} (eq : a ≡ b) {x y : U.Proc a} →
             x UR─→ₚ* y → subst U.Proc eq x UR─→ₚ* subst U.Proc eq y
─→ₚ*-subst refl s = s

-- single-step reduction lifts through a subst on U.Proc.
─→-subst : ∀ {a b} (eq : a ≡ b) {P Q : U.Proc a} → P UR.─→ₚ Q →
           subst U.Proc eq P UR.─→ₚ subst U.Proc eq Q
─→-subst refl r = r

-- reduction-star lifts through a Bφ block (each φ via RU-Sync; the subst on the
-- body is carried by ─→-subst).
Bφ-red : ∀ {n} (B : BindGroup) {P Q : U.Proc (syncs B + n)} →
         P UR─→ₚ* Q → Bφ {n} B P UR─→ₚ* Bφ B Q
Bφ-red []            r = r
Bφ-red (b ∷ [])      r = r
Bφ-red {n} (b ∷ B@(_ ∷ _)) r =
  ⋆-gmap (U.φ ϕ[ b ]) UR.RU-Sync
    (Bφ-red B (─→ₚ*-subst (sym (+-suc (syncs B) n)) r))

-- φ drop (⟪ F[drop · 𝓒[e × suc x × `0F]] ⟫ ∥ Q) fires RU-Drop to φ acq (⟪ F[*] ⟫ ∥ Q).
leaf-fire-drop : (F : Frame* (1 + n)) {e : Tm (1 + n)} {x : 𝔽 n} (Q : U.Proc (1 + n)) →
  U.φ U.drop (U.⟪ F [ K `drop · (((e ⊗ (` (Fin.suc x))) ⊗ (` 0F))) ]* ⟫ U.∥ Q)
    UR─→ₚ*
  U.φ U.acq (U.⟪ F [ K `unit ]* ⟫ U.∥ Q)
leaf-fire-drop F {e} {x} Q = UR.RU-Drop F ◅ ε

-- canonₛ on a triple of values is a value-substitution (copied from Splits).
VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ _ → chanTriple-V (e1 , x , e2) (Ve1 , Ve2)
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ _ → value-⋯ (chanTriple-V (wk e1 , suc x , ` 0F) (Ve1 ⋯ᵛ weakenᵣ , V-`)) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

VSub-leafσ : ∀ {m n} (σ : m →ₛ n) → VSub σ → (B₁ B₂ : BindGroup) → VSub (leafσ σ B₁ B₂)
VSub-leafσ σ Vσ B₁ B₂ = ++ₛ-VSub
  (++ₛ-VSub (weaken-VSub (syncs B₂) (VSub-canonₛ B₁ (K `unit , 0F , K `unit) (V-K , V-K)))
            (VSub-canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) (V-K , V-K)))
  (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ)))

open T using (_;_⊢ₚ_)

U-drop : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
       → {g : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
         {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
         {P : T.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)}
       → Γ ; g ⊢ₚ T.ν (suc b₁ ∷ B₁) B₂
           (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop · (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ))
       → (U[ T.ν (suc b₁ ∷ B₁) B₂
             (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop · (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ)) ] σ
            UR─→ₚ* U[ T.ν (b₁ ∷ B₁) B₂ (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
         ⊎ (U[ T.ν (suc b₁ ∷ B₁) B₂
             (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop · (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ)) ] σ
            U.≋ U[ T.ν (b₁ ∷ B₁) B₂ (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
U-drop σ Vσ Γ-S {b₁ = b₁} {B₁ = []} {B₂ = B₂} {E = E} {P = P} ⊢P = {!!}
U-drop {m} {n} σ Vσ Γ-S {b₁ = suc b₁} {B₁ = C@(_ ∷ _)} {B₂ = B₂} {E = E} {P = P} ⊢P =
  {!!}  -- b₁≥1 vacuous: ϕ[suc b₁]=drop on RHS, RU-Drop would have to produce φ drop
U-drop {m} {n} σ Vσ Γ-S {b₁ = zero} {B₁ = C@(_ ∷ _)} {B₂ = B₂} {E = E} {P = P} ⊢P =
  ≋-wrap-⊎ front fire back
  where
    Eᵂ : Frame* (sum (suc zero ∷ C) + sum B₂ + m)
    Eᵂ = E ⋯ᶠ* weakenᵣ
    Pᵂ : T.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    Pᵂ = P T.⋯ₚ weakenᵣ
    QL : T.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    QL = T.⟪ Eᵂ [ K `drop · (` 0F) ]* ⟫ T.∥ Pᵂ
    QR : T.Proc (sum (zero ∷ C) + sum B₂ + m)
    QR = T.⟪ E [ K `unit ]* ⟫ T.∥ P
    sC = syncs C
    sB₂ = syncs B₂
    LL : U.Proc (sB₂ + (suc sC + (2 + n)))
    LL = U[ QL ] (leafσ σ (suc zero ∷ C) B₂)
    flatL : U[ T.ν (suc zero ∷ C) B₂ QL ] σ
            ≡ U.ν (Bφ (suc zero ∷ C) (Bφ B₂ LL))
    flatL = Uν-flat σ (suc zero ∷ C) B₂ QL
    flatR : U[ T.ν (zero ∷ C) B₂ QR ] σ
            ≡ U.ν (Bφ (zero ∷ C) (Bφ B₂ (U[ QR ] (leafσ σ (zero ∷ C) B₂))))
    flatR = Uν-flat σ (zero ∷ C) B₂ QR
    eqC : sB₂ + suc (sC + suc (suc n)) ≡ sB₂ + (sC + suc (suc (suc n)))
    eqC = cong (sB₂ +_) (sym (+-suc sC (suc (suc n))))
    -- leaf after pushing φ drop past Bφ C then Bφ B₂
    LL₂ : U.Proc (suc (sB₂ + (sC + (2 + n))))
    LL₂ = subst U.Proc eqC LL
            U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)
            U.⋯ₚ assocSwapᵣ sB₂ 1
    mid : U.Proc n
    mid = U.ν (Bφ C (Bφ B₂ (U.φ U.drop LL₂)))
    front : U[ T.ν (suc zero ∷ C) B₂ QL ] σ U.≋ mid
    front = ≡→≋ flatL
      ◅◅ U.ν-cong (φ-past-Bφ C U.drop
           (subst U.Proc (sym (+-suc sC (suc (suc n)))) (Bφ B₂ LL)))
      ◅◅ U.ν-cong (Bφ-cong C (U.φ-cong (≡→≋
           ( cong (U._⋯ₚ assocSwapᵣ sC 1)
               (subst-Bφ (sym (+-suc sC (suc (suc n)))) B₂ LL)
           ■ Bφ-⋯ B₂ (subst U.Proc eqC LL) (assocSwapᵣ sC 1) ))))
      ◅◅ U.ν-cong (Bφ-cong C (φ-past-Bφ B₂ U.drop
           (subst U.Proc eqC LL U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂))))
    -- decompose LL₂ into ⟪ redex-thread ⟫ ∥ residual
    subst-∥ : ∀ {a b} (eq : a ≡ b) (X Y : U.Proc a) →
              subst U.Proc eq (X U.∥ Y) ≡ subst U.Proc eq X U.∥ subst U.Proc eq Y
    subst-∥ refl X Y = refl
    subst-⟪⟫ : ∀ {a b} (eq : a ≡ b) (t : Tm a) →
               subst U.Proc eq U.⟪ t ⟫ ≡ U.⟪ subst Tm eq t ⟫
    subst-⟪⟫ refl t = refl
    aTm : Tm (sB₂ + (suc sC + (2 + n)))
    aTm = (Eᵂ [ K `drop · (` 0F) ]*) ⋯ leafσ σ (suc zero ∷ C) B₂
    bPr : U.Proc (sB₂ + (suc sC + (2 + n)))
    bPr = U[ Pᵂ ] (leafσ σ (suc zero ∷ C) B₂)
    -- the redex thread after subst+renamings
    redTm : Tm (suc (sB₂ + (sC + (2 + n))))
    redTm = subst Tm eqC aTm ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
    Qᶠ : U.Proc (suc (sB₂ + (sC + (2 + n))))
    Qᶠ = subst U.Proc eqC bPr U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1
    LL₂-split : LL₂ ≡ U.⟪ redTm ⟫ U.∥ Qᶠ
    LL₂-split =
        cong (U._⋯ₚ assocSwapᵣ sB₂ 1)
          (cong (U._⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂))
            (subst-∥ eqC U.⟪ aTm ⟫ bPr
             ■ cong (U._∥ subst U.Proc eqC bPr) (subst-⟪⟫ eqC aTm)))
    -- the redex thread is a drop-redex applied to a chanTriple ending in `0F
    redShape : Σ[ F ∈ Frame* (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ e ∈ Tm (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ x ∈ 𝔽 (sB₂ + (sC + (2 + n))) ]
                 redTm ≡ F [ K `drop · (((e ⊗ (` (Fin.suc x))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))) ]*
    redShape = {! redShape !}
    Eᶠ : Frame* (suc (sB₂ + (sC + (2 + n))))
    Eᶠ = proj₁ redShape
    fired : U.Proc n
    fired = U.ν (Bφ C (Bφ B₂ (U.φ U.acq (U.⟪ Eᶠ [ K `unit ]* ⟫ U.∥ Qᶠ))))
    fire : mid UR─→ₚ* fired
    fire = ⋆-gmap U.ν UR.RU-Res
      (Bφ-red C (Bφ-red B₂
        (subst (λ z → U.φ U.drop z UR─→ₚ* U.φ U.acq (U.⟪ Eᶠ [ K `unit ]* ⟫ U.∥ Qᶠ))
          (sym (LL₂-split ■ cong (U._∥ Qᶠ) (cong U.⟪_⟫ (proj₂ (proj₂ (proj₂ redShape))))))
          (leaf-fire-drop Eᶠ {proj₁ (proj₂ redShape)} {proj₁ (proj₂ (proj₂ redShape))} Qᶠ))))
    back : fired U.≋ U[ T.ν (zero ∷ C) B₂ QR ] σ
    back = {! back !}
