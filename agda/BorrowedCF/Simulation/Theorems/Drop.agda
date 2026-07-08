module BorrowedCF.Simulation.Theorems.Drop where


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

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_) renaming (gmap to ⋆-gmap)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥
        ; toℕ-↑*-ge; commuteS; wkSwap-cancel; assocSwap-invol; toℕ-assoc-mid; toℕ-assoc-ge )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation.TranslationProperties using (VChan; Value-subst; chanTriple-V)
open T using (inv-∥; inv-ν; inv-⟪⟫; BindCtx; BindCtx′; last; cons-ret/acq; cons-acq; nil; cons)
open import BorrowedCF.Simulation.InvFrame using (inv-app; arg-type; strengthen-frame)
open import BorrowedCF.Simulation.Theorems.B1VacProbe
  using ( NoRet; new⇒noRet; noRet-≃; ¬noRet-ret
        ; RetTip; retTip-Sc-skips; noRet-front-cons; retTip-≃; noRet-;-fst )
open import BorrowedCF.Simulation.Theorems.B1VacProbe as VP using ()
open import BorrowedCF.Types.Equivalence using (_≃𝕊_; ≃𝕊-;₁; ≃𝕊-;₂; ≃𝕊-skipˡ; ≃𝕊-skipʳ; ≃𝕊-μ; ≃𝕊-assoc; ≃𝕊-distr; ≃-skips)
open import BorrowedCF.Context.Base using (_⸴*_; _⸴_)
import BorrowedCF.Types.Substitution as 𝕊S
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.Equivalence as EqC
open Bin using (_Respects_)
open import BorrowedCF.Types using (Skips)
import Data.Sum as Sum

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

-- dropping the head bind count (suc zero → zero) on a nonempty chain shifts the
-- channel substitution by one binder: canonₛ ignores the head count's actual
-- value (only its splitAt-width), so the slot at index 0 is unused.
canonₛ-shift : ∀ {N} (c′ : ℕ) (C : BindGroup) (cc : UChan N) (y : 𝔽 (sum (c′ ∷ C))) →
               canonₛ (zero ∷ c′ ∷ C) cc y ≡ canonₛ (suc zero ∷ c′ ∷ C) cc (Fin.suc y)
canonₛ-shift c′ C cc y = refl

-- a front block shrinking by one slot (bL on suc i = bR on i) does not change
-- the ((bL ++ₛ ts) ++ₛ rs) value (ported from Simulation2.Theorems.block-shift).
block-shift : ∀ p {A B N} (bL : suc p →ₛ N) (bR : p →ₛ N)
              (eq : ∀ k → bL (Fin.suc k) ≡ bR k)
              (ts : A →ₛ N) (rs : B →ₛ N) (i : 𝔽 (p + A + B)) →
              ((bL ++ₛ ts) ++ₛ rs) (Fin.suc i) ≡ ((bR ++ₛ ts) ++ₛ rs) i
block-shift p {A} {B} bL bR eq ts rs i with Fin.splitAt (p + A) i
... | inj₂ k = refl
... | inj₁ j with Fin.splitAt p j
...   | inj₁ k = eq k
...   | inj₂ k = refl

-- the outer/inner ++ₛ blocks of leafσ for (zero ∷ c′ ∷ C) and (suc zero ∷ c′ ∷ C)
-- coincide except for the canonₛ-A₁ block, where canonₛ-shift bridges them.
leafσ-shift : ∀ {m n} (σ : m →ₛ n) (c′ : ℕ) (C B₂ : BindGroup)
              (y : 𝔽 (sum (zero ∷ c′ ∷ C) + sum B₂ + m)) →
              leafσ σ (zero ∷ c′ ∷ C) B₂ y ≡ leafσ σ (suc zero ∷ c′ ∷ C) B₂ (Fin.suc y)
leafσ-shift {m} σ c′ C B₂ y =
  sym (block-shift (sum (c′ ∷ C))
         (λ i → canonₛ (suc zero ∷ c′ ∷ C) (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
         (λ i → canonₛ (zero ∷ c′ ∷ C) (K `unit , 0F , K `unit) i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
         (λ k → cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (sym (canonₛ-shift c′ C (K `unit , 0F , K `unit) k)))
         (canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ c′ ∷ C)) 1F , K `unit))
         (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (suc zero ∷ c′ ∷ C)) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))
         y)

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

-- φ drop (⟪ F[drop · 𝓒[* × suc x × `0F]] ⟫ ∥ Q) fires RU-Drop to φ acq (⟪ F[*] ⟫ ∥ Q).
leaf-fire-drop : (F : Frame* (1 + n)) {x : 𝔽 n} (Q : U.Proc (1 + n)) →
  U.φ U.drop (U.⟪ F [ K `drop ·¹ (((* ⊗ (` (Fin.suc x))) ⊗ (` 0F))) ]* ⟫ U.∥ Q)
    UR─→ₚ*
  U.φ U.acq (U.⟪ F [ K `unit ]* ⟫ U.∥ Q)
leaf-fire-drop F {x} Q = UR.RU-Drop F ◅ ε

-- canonₛ on a triple of values is a value-substitution (copied from Splits).
VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ j → Ub-V (b + 0) e1 x e2 Ve1 Ve2 j
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ j → value-⋯ (Ub-V b (wk e1) (suc x) (` 0F) (Ve1 ⋯ᵛ weakenᵣ) V-` j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

VSub-leafσ : ∀ {m n} (σ : m →ₛ n) → VSub σ → (B₁ B₂ : BindGroup) → VSub (leafσ σ B₁ B₂)
VSub-leafσ σ Vσ B₁ B₂ = ++ₛ-VSub
  (++ₛ-VSub (weaken-VSub (syncs B₂) (VSub-canonₛ B₁ (K `unit , 0F , K `unit) (V-K , V-K)))
            (VSub-canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , K `unit) (V-K , V-K)))
  (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ)))

-- The push composite (assocSwapᵣ sA w ↑* sB) then (assocSwapᵣ sB w) sends the
-- junction var (flat position sB+(sA+d), d<w) to position d.
assocPush-junc : ∀ (sA sB w d : ℕ) {nn} (j : 𝔽 (sB + (sA + (w + nn)))) →
                 Fin.toℕ j ≡ sB + (sA + d) → d Nat.< w →
                 Fin.toℕ ((assocSwapᵣ sB w {sA + nn}) ((assocSwapᵣ sA w {nn} ↑* sB) j)) ≡ d
assocPush-junc sA sB w d {nn} j jeq d<w =
    toℕ-assoc-mid sB w {sA + nn} ((assocSwapᵣ sA w {nn} ↑* sB) j) geB ltB
  ■ aritheq
  where
    q1 : sB Nat.≤ Fin.toℕ j
    q1 = subst (sB Nat.≤_) (sym jeq) (Nat.m≤m+n sB (sA + d))
    redeq : Fin.toℕ (Fin.reduce≥ j q1) ≡ sA + d
    redeq = toℕ-reduce≥ j q1 ■ cong (Nat._∸ sB) jeq ■ Nat.m+n∸m≡n sB (sA + d)
    geA : sA Nat.≤ Fin.toℕ (Fin.reduce≥ j q1)
    geA = subst (sA Nat.≤_) (sym redeq) (Nat.m≤m+n sA d)
    ltA : Fin.toℕ (Fin.reduce≥ j q1) Nat.< sA + w
    ltA = subst (Nat._< sA + w) (sym redeq) (Nat.+-monoʳ-< sA d<w)
    midA : Fin.toℕ (assocSwapᵣ sA w {nn} (Fin.reduce≥ j q1)) ≡ d
    midA = toℕ-assoc-mid sA w {nn} (Fin.reduce≥ j q1) geA ltA
         ■ cong (Nat._∸ sA) redeq ■ Nat.m+n∸m≡n sA d
    step1 : Fin.toℕ ((assocSwapᵣ sA w {nn} ↑* sB) j) ≡ sB + d
    step1 = toℕ-↑*-ge (assocSwapᵣ sA w {nn}) sB j q1 ■ cong (sB +_) midA
    geB : sB Nat.≤ Fin.toℕ ((assocSwapᵣ sA w {nn} ↑* sB) j)
    geB = subst (sB Nat.≤_) (sym step1) (Nat.m≤m+n sB d)
    ltB : Fin.toℕ ((assocSwapᵣ sA w {nn} ↑* sB) j) Nat.< sB + w
    ltB = subst (Nat._< sB + w) (sym step1) (Nat.+-monoʳ-< sB d<w)
    aritheq : Fin.toℕ ((assocSwapᵣ sA w {nn} ↑* sB) j) Nat.∸ sB ≡ d
    aritheq = cong (Nat._∸ sB) step1 ■ Nat.m+n∸m≡n sB d

frame-plug*ᵣ : ∀ {m p} (E : Frame* m) {t : Tm m} (ρ : m →ᵣ p) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

open T using (_;_⊢ₚ_)

------------------------------------------------------------------------
-- Vacuity infrastructure for the B₁=[] and b₁≥1 R-Drop branches.
-- The dropped handle 0F is forced  Γ 0F ≃ ⟨ ret ⟩  by the drop constant
-- (⊢ `drop ∶ ⟨ ret ⟩ →1M ⊤), via inversion of the redex thread typing.
------------------------------------------------------------------------

fn-drop-dom : ∀ {N} {Γ : Ctx N} {β : Struct N} {Tᵈ Uu a ϵ}
  → Γ ; β ⊢ K `drop ∶ Tᵈ ⟨ a ⟩→ Uu ∣ ϵ
  → ⟨ ret ⟩ ≃ Tᵈ
fn-drop-dom (T-Const `drop)        = ≃-refl
fn-drop-dom (T-Conv (dom≃ `→ _) _ d) = ≃-trans (fn-drop-dom d) dom≃
fn-drop-dom (T-Weaken _ d)         = fn-drop-dom d

drop-handle-≃ret : ∀ {N} {Δ : Ctx N}{β}{x : 𝔽 N}{U ϵ}
  → Δ ; β ⊢ K `drop ·¹ (` x) ∶ U ∣ ϵ
  → Δ x ≃ ⟨ ret ⟩
drop-handle-≃ret (T-AppUnr   _ _ ⊢fn ⊢arg) = ≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))
drop-handle-≃ret (T-AppLin   _ _ ⊢fn ⊢arg) = ≃-trans (arg-type ⊢arg) (≃-sym (fn-drop-dom ⊢fn))
drop-handle-≃ret (T-Conv _ _ d)            = drop-handle-≃ret d
drop-handle-≃ret (T-Weaken _ d)            = drop-handle-≃ret d

⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
⟨⟩≃ ⟨ eq ⟩ = eq

-- index 0F of the body context (Γ₁ ⸴* Γ₂) ⸴* γ lands in Γ₁ when Γ₁ is nonempty.
bodyΓ-0F : ∀ {k} (A : Ctx (suc k)) {B C : Σ ℕ Ctx} →
           ∀ (Bᶜ : Ctx (proj₁ B)) (Cᶜ : Ctx (proj₁ C)) →
           ((A ⸴* Bᶜ) ⸴* Cᶜ) 0F ≡ A 0F
bodyΓ-0F A Bᶜ Cᶜ = refl

-- head channel 0F of a `last`-block over a NoRet front session is NoRet.
head-noRet-last : ∀ {sF b}{Γ : Ctx (sum (suc b ∷ []))} →
  NoRet sF → BindCtx sF (suc b ∷ []) Γ →
  ∃[ s'' ] (Γ 0F ≡ ⟨ s'' ⟩) × NoRet s''
head-noRet-last ns (last (cons s1 _ ¬sk s≃ Γ≗ _)) =
  s1 , sym (Γ≗ 0F) , VP.noRet-;-fst (noRet-≃ (EqC.symmetric _≃𝕊_ s≃) ns)

noRet⇒≄ret : ∀ {s'' : 𝕊 0} → NoRet s'' → s'' ≃ ret → ⊥
noRet⇒≄ret ns eq = ¬noRet-ret (noRet-≃ eq ns)

U-drop : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
       → {g : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
         {E : Frame* (sum (b₁ ∷ B₁) + sum B₂ + m)}
         {P : T.Proc (sum (b₁ ∷ B₁) + sum B₂ + m)}
       → Γ ; g ⊢ₚ T.ν (suc b₁ ∷ B₁) B₂
           (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ))
       → (U[ T.ν (suc b₁ ∷ B₁) B₂
             (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ)) ] σ
            UR─→ₚ* U[ T.ν (b₁ ∷ B₁) B₂ (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
         ⊎ (U[ T.ν (suc b₁ ∷ B₁) B₂
             (T.⟪ (E ⋯ᶠ* weakenᵣ) [ K `drop ·¹ (` 0F) ]* ⟫ T.∥ (P T.⋯ₚ weakenᵣ)) ] σ
            U.≋ U[ T.ν (b₁ ∷ B₁) B₂ (T.⟪ E [ K `unit ]* ⟫ T.∥ P) ] σ)
U-drop σ Vσ Γ-S {b₁ = b₁} {B₁ = []} {B₂ = B₂} {E = E} {P = P} ⊢P
  with inv-ν ⊢P
... | _ , _ , sN , _ , N , _ , _ , C , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  with head-noRet-last (VP._;_ (new⇒noRet N) VP.end) C
... | s , Γ0≡ , Ns
  = ⊥-elim (noRet⇒≄ret Ns (⟨⟩≃ (≃-trans (≃-reflexive (sym Γ0≡)) (drop-handle-≃ret ⊢plug))))
U-drop {m} {n} σ Vσ Γ-S {b₁ = suc b₁} {B₁ = C@(_ ∷ _)} {B₂ = B₂} {E = E} {P = P} ⊢P
  with inv-ν ⊢P
... | _ , _ , sN , _ , N , _ , _
    , cons-ret/acq sh scra Γ≗ (cons s1ʰ s2ʰ ¬sk1 s≃1 Γ≗1 (cons _ _ ¬Ss s≃2 _ _)) _ , _ , ⊢body
  with inv-∥ ⊢body
... | _ , _ , _ , ⊢dropT , _
  with strengthen-frame (E ⋯ᶠ* weakenᵣ) (inv-⟪⟫ ⊢dropT)
... | _ , (_ , _ , ⊢plug) , _ , _
  = ⊥-elim (¬Ss (retTip-Sc-skips rt-borrow head≃ret))
  where
    head≃ret : s1ʰ ≃ ret
    head≃ret = ⟨⟩≃ (≃-trans (≃-reflexive (sym (sym (Γ≗ 0F) ■ sym (Γ≗1 0F)))) (drop-handle-≃ret ⊢plug))
    noRet-sh : NoRet sh
    noRet-sh = noRet-;-fst (noRet-≃ (EqC.symmetric _≃𝕊_ scra) (VP._;_ (new⇒noRet N) VP.end))
    rt-borrow : RetTip (s1ʰ ; s2ʰ)
    rt-borrow = retTip-≃ (EqC.symmetric _≃𝕊_ s≃1) (noRet-front-cons noRet-sh)
U-drop {m} {n} σ Vσ Γ-S {b₁ = zero} {B₁ = C@(cHd ∷ cTl)} {B₂ = B₂} {E = E} {P = P} ⊢P =
  ≋-wrap-⊎ front fire back
  where
    Eᵂ : Frame* (sum (suc zero ∷ C) + sum B₂ + m)
    Eᵂ = E ⋯ᶠ* weakenᵣ
    Pᵂ : T.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    Pᵂ = P T.⋯ₚ weakenᵣ
    QL : T.Proc (sum (suc zero ∷ C) + sum B₂ + m)
    QL = T.⟪ Eᵂ [ K `drop ·¹ (` 0F) ]* ⟫ T.∥ Pᵂ
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
    -- generic: push a head φ z past Bφ C then Bφ B₂ down to the leaf, keeping ν.
    pushφ-down : (z : U.Flag) (X : U.Proc (sB₂ + (suc sC + (2 + n)))) →
      U.φ z (Bφ C (subst U.Proc (sym (+-suc sC (suc (suc n)))) (Bφ B₂ X)))
        U.≋
      Bφ C (Bφ B₂ (U.φ z (subst U.Proc eqC X
                            U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)
                            U.⋯ₚ assocSwapᵣ sB₂ 1)))
    pushφ-down z X =
         φ-past-Bφ C z (subst U.Proc (sym (+-suc sC (suc (suc n)))) (Bφ B₂ X))
      ◅◅ Bφ-cong C (U.φ-cong (≡→≋
           ( cong (U._⋯ₚ assocSwapᵣ sC 1)
               (subst-Bφ (sym (+-suc sC (suc (suc n)))) B₂ X)
           ■ Bφ-⋯ B₂ (subst U.Proc eqC X) (assocSwapᵣ sC 1) )))
      ◅◅ Bφ-cong C (φ-past-Bφ B₂ z
           (subst U.Proc eqC X U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂)))
    front : U[ T.ν (suc zero ∷ C) B₂ QL ] σ U.≋ mid
    front = ≡→≋ flatL ◅◅ U.ν-cong (pushφ-down U.drop LL)
    -- decompose LL₂ into ⟪ redex-thread ⟫ ∥ residual
    subst-∥ : ∀ {a b} (eq : a ≡ b) (X Y : U.Proc a) →
              subst U.Proc eq (X U.∥ Y) ≡ subst U.Proc eq X U.∥ subst U.Proc eq Y
    subst-∥ refl X Y = refl
    subst-⟪⟫ : ∀ {a b} (eq : a ≡ b) (t : Tm a) →
               subst U.Proc eq U.⟪ t ⟫ ≡ U.⟪ subst Tm eq t ⟫
    subst-⟪⟫ refl t = refl
    aTm : Tm (sB₂ + (suc sC + (2 + n)))
    aTm = (Eᵂ [ K `drop ·¹ (` 0F) ]*) ⋯ leafσ σ (suc zero ∷ C) B₂
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
    -- the combined value-substitution applied to the redex thread
    Vleafσ : VSub (leafσ σ (suc zero ∷ C) B₂)
    Vleafσ = VSub-leafσ σ Vσ (suc zero ∷ C) B₂
    θ : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ suc (sB₂ + (sC + (2 + n)))
    θ = ((subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
          ·ₖ (assocSwapᵣ sC 1 ↑* sB₂)) ·ₖ assocSwapᵣ sB₂ 1
    Vθ-cod : ∀ {a c} {t : Tm a} (eq : a ≡ c) → Value t → Value (subst Tm eq t)
    Vθ-cod refl V = V
    subst-cod-pt : ∀ {a c} (eq : a ≡ c) (s : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                   subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
    subst-cod-pt refl s i = refl
    Vθ : VSub θ
    Vθ i = value-⋯ (value-⋯
             (subst Value (sym (subst-cod-pt eqC (leafσ σ (suc zero ∷ C) B₂) i))
               (Vθ-cod eqC (Vleafσ i)))
             (assocSwapᵣ sC 1 ↑* sB₂) (λ _ → V-`))
             (assocSwapᵣ sB₂ 1) (λ _ → V-`)
    subst-⊗ : ∀ {a b} (eq : a ≡ b) (p r : Tm a) →
              subst Tm eq (p ⊗ r) ≡ subst Tm eq p ⊗ subst Tm eq r
    subst-⊗ refl p r = refl
    subst-`F : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → subst Tm eq (` q) ≡ ` subst 𝔽 eq q
    subst-`F refl q = refl
    -- the dropped handle term under θ is a chanTriple with `suc x` middle, `0F last
    handle : Σ[ e ∈ Tm (suc (sB₂ + (sC + (2 + n)))) ]
             Σ[ x ∈ 𝔽 (sB₂ + (sC + (2 + n))) ]
               θ 0F ≡ ((e ⊗ (` (Fin.suc x))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))
    handle = handleE , handleX , handleEq
      where
        ρ1 = assocSwapᵣ sC 1 ↑* sB₂
        ρ2 = assocSwapᵣ sB₂ 1
        handleE : Tm (suc (sB₂ + (sC + (2 + n))))
        handleE = K `unit
        handleX : 𝔽 (sB₂ + (sC + (2 + n)))
        handleX = weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc n}))
        midV0 : 𝔽 (sC + suc (suc (suc n)))
        midV0 = weaken* ⦃ Kᵣ ⦄ sC (Fin.suc (Fin.zero {n = suc n}))
        lastV0 : 𝔽 (sC + suc (suc (suc n)))
        lastV0 = weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc (suc n)})
        l0≡ : leafσ σ (suc zero ∷ C) B₂ 0F
              ≡ subst Tm (+-suc sC (suc (suc n)))
                    (((K `unit) ⊗ (` midV0)) ⊗ (` lastV0))
                  ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        l0≡ = refl
        rnV : 𝔽 (sC + suc (suc (suc n))) → 𝔽 (suc (sB₂ + (sC + (2 + n))))
        rnV v = ρ2 (ρ1 (subst 𝔽 eqC
                  (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))))
        toℕ-subst𝔽 : ∀ {a b} (eq : a ≡ b) (q : 𝔽 a) → Fin.toℕ (subst 𝔽 eq q) ≡ Fin.toℕ q
        toℕ-subst𝔽 refl q = refl
        -- inner var of rnV before the ρ1/ρ2 push, with toℕ characterisation.
        innerV : 𝔽 (sC + suc (suc (suc n))) → 𝔽 (sB₂ + (sC + (1 + (2 + n))))
        innerV v = subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))
        innerV-toℕ : (v : 𝔽 (sC + suc (suc (suc n)))) (d : ℕ) →
                     Fin.toℕ v ≡ sC + d → Fin.toℕ (innerV v) ≡ sB₂ + (sC + d)
        innerV-toℕ v d veq =
            toℕ-subst𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v))
          ■ toℕ-weaken*ᵣ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) v)
          ■ cong (sB₂ +_) (toℕ-subst𝔽 (+-suc sC (suc (suc n))) v ■ veq)
        midV0-toℕ : Fin.toℕ midV0 ≡ sC + 1
        midV0-toℕ = toℕ-weaken*ᵣ sC (Fin.suc (Fin.zero {n = suc n}))
        lastV0-toℕ : Fin.toℕ lastV0 ≡ sC + 0
        lastV0-toℕ = toℕ-weaken*ᵣ sC (Fin.zero {n = suc (suc n)})
        mid≡ : rnV midV0 ≡ Fin.suc handleX
        mid≡ = Fin.toℕ-injective
          ( toℕ-assoc-ge sB₂ 1 ((assocSwapᵣ sC 1 ↑* sB₂) (innerV midV0)) geρ2
          ■ toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (innerV midV0) geB
          ■ cong (sB₂ +_) (toℕ-assoc-ge sC 1 (Fin.reduce≥ (innerV midV0) geB) geρ1)
          ■ cong (sB₂ +_) redmid
          ■ sym ( cong suc (toℕ-weaken*ᵣ sB₂ (weaken* ⦃ Kᵣ ⦄ sC (Fin.zero {n = suc n}))
                          ■ cong (sB₂ +_) (toℕ-weaken*ᵣ sC (Fin.zero {n = suc n})
                                          ■ Nat.+-identityʳ sC))
                ■ sym (Nat.+-suc sB₂ sC)
                ■ cong (sB₂ +_) (sym (Nat.+-comm sC 1)) ) )
          where
            imeq : Fin.toℕ (innerV midV0) ≡ sB₂ + (sC + 1)
            imeq = innerV-toℕ midV0 1 midV0-toℕ
            geB : sB₂ Nat.≤ Fin.toℕ (innerV midV0)
            geB = subst (sB₂ Nat.≤_) (sym imeq) (Nat.m≤m+n sB₂ (sC + 1))
            redmid : Fin.toℕ (Fin.reduce≥ (innerV midV0) geB) ≡ sC + 1
            redmid = toℕ-reduce≥ (innerV midV0) geB ■ cong (Nat._∸ sB₂) imeq ■ Nat.m+n∸m≡n sB₂ (sC + 1)
            geρ1 : sC + 1 Nat.≤ Fin.toℕ (Fin.reduce≥ (innerV midV0) geB)
            geρ1 = subst (sC + 1 Nat.≤_) (sym redmid) Nat.≤-refl
            geρ2 : sB₂ + 1 Nat.≤ Fin.toℕ ((assocSwapᵣ sC 1 ↑* sB₂) (innerV midV0))
            geρ2 = subst (sB₂ + 1 Nat.≤_)
                     (sym ( toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (innerV midV0) geB
                          ■ cong (sB₂ +_) (toℕ-assoc-ge sC 1 (Fin.reduce≥ (innerV midV0) geB) geρ1 ■ redmid) ))
                     (Nat.+-monoʳ-≤ sB₂ (subst (1 Nat.≤_) (Nat.+-comm 1 sC) (Nat.s≤s (Nat.z≤n {sC}))))
        last≡ : rnV lastV0 ≡ Fin.zero {n = sB₂ + (sC + (2 + n))}
        last≡ = Fin.toℕ-injective
          (assocPush-junc sC sB₂ 1 0 (innerV lastV0) (innerV-toℕ lastV0 0 lastV0-toℕ) (Nat.s≤s Nat.z≤n))
        θ0≡ : θ 0F ≡ subst Tm eqC (leafσ σ (suc zero ∷ C) B₂ 0F) ⋯ ρ1 ⋯ ρ2
        θ0≡ = cong (λ z → z ⋯ ρ1 ⋯ ρ2) (subst-cod-pt eqC (leafσ σ (suc zero ∷ C) B₂) 0F)
        subst-K : ∀ {a b} (eq : a ≡ b) (c : _) → subst Tm eq (K c) ≡ K c
        subst-K refl c = refl
        -- push subst (+-suc) through the chanTriple ⊗-structure
        push1 : subst Tm (+-suc sC (suc (suc n))) (((K `unit) ⊗ (` midV0)) ⊗ (` lastV0))
                ≡ ((K `unit ⊗ (` subst 𝔽 (+-suc sC (suc (suc n))) midV0))
                    ⊗ (` subst 𝔽 (+-suc sC (suc (suc n))) lastV0))
        push1 = subst-⊗ (+-suc sC (suc (suc n))) ((K `unit) ⊗ (` midV0)) (` lastV0)
              ■ cong₂ _⊗_
                  (subst-⊗ (+-suc sC (suc (suc n))) (K `unit) (` midV0)
                   ■ cong₂ _⊗_ (subst-K (+-suc sC (suc (suc n))) `unit)
                               (subst-`F (+-suc sC (suc (suc n))) midV0))
                  (subst-`F (+-suc sC (suc (suc n))) lastV0)
        -- push subst eqC through (after ⋯ weaken*sB₂, which is definitional over ⊗)
        push2 : subst Tm eqC
                  ((K `unit ⊗ (` weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0)))
                    ⊗ (` weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0)))
                ≡ ((K `unit ⊗ (` subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0))))
                    ⊗ (` subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0))))
        push2 = subst-⊗ eqC _ _
              ■ cong₂ _⊗_
                  (subst-⊗ eqC (K `unit) _
                   ■ cong₂ _⊗_ (subst-K eqC `unit)
                               (subst-`F eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) midV0))))
                  (subst-`F eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 (+-suc sC (suc (suc n))) lastV0)))
        decomp : subst Tm eqC (leafσ σ (suc zero ∷ C) B₂ 0F) ⋯ ρ1 ⋯ ρ2
                 ≡ ((K `unit ⊗ (` rnV midV0)) ⊗ (` rnV lastV0))
        decomp =
            cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρ1 ⋯ ρ2) push1
          ■ cong (λ z → subst Tm eqC z ⋯ ρ1 ⋯ ρ2) refl
          ■ cong (λ z → z ⋯ ρ1 ⋯ ρ2) push2
        handleEq : θ 0F ≡ ((handleE ⊗ (` (Fin.suc handleX))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))
        handleEq = θ0≡ ■ decomp
                 ■ cong (λ z → (K `unit ⊗ (` z)) ⊗ (` rnV lastV0)) mid≡
                 ■ cong (λ z → (K `unit ⊗ (` Fin.suc handleX)) ⊗ (` z)) last≡
    subst-⋯ₛ-cod : ∀ {a c d} (q : c ≡ d) (t : Tm a) (s : a →ₛ c) →
                   t ⋯ subst (λ z → a →ₛ z) q s ≡ subst Tm q (t ⋯ s)
    subst-⋯ₛ-cod refl t s = refl
    redTm≡θ : redTm ≡ (Eᵂ [ K `drop ·¹ (` 0F) ]*) ⋯ θ
    redTm≡θ =
        cong (λ z → z ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
          (sym (subst-⋯ₛ-cod eqC (Eᵂ [ K `drop ·¹ (` 0F) ]*) (leafσ σ (suc zero ∷ C) B₂)))
      ■ cong (_⋯ assocSwapᵣ sB₂ 1)
          (fusion (Eᵂ [ K `drop ·¹ (` 0F) ]*)
            (subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
            (assocSwapᵣ sC 1 ↑* sB₂))
      ■ fusion (Eᵂ [ K `drop ·¹ (` 0F) ]*)
          ((subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (suc zero ∷ C) B₂))
            ·ₖ (assocSwapᵣ sC 1 ↑* sB₂))
          (assocSwapᵣ sB₂ 1)
    -- the redex thread is a drop-redex applied to a chanTriple ending in `0F
    redShapeF : Frame* (suc (sB₂ + (sC + (2 + n))))
    redShapeF = frame*-⋯ Eᵂ θ Vθ
    redShapeE : Tm (suc (sB₂ + (sC + (2 + n))))
    redShapeE = proj₁ handle
    redShapeX : 𝔽 (sB₂ + (sC + (2 + n)))
    redShapeX = proj₁ (proj₂ handle)
    redShapeEq : redTm ≡ redShapeF [ K `drop ·¹ (((redShapeE ⊗ (` (Fin.suc redShapeX))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))) ]*
    redShapeEq =
        redTm≡θ
      ■ frame-plug* Eᵂ θ Vθ
      ■ cong (redShapeF [_]*) (cong (K `drop ·¹_) (proj₂ (proj₂ handle)))
    redShape : Σ[ F ∈ Frame* (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ e ∈ Tm (suc (sB₂ + (sC + (2 + n)))) ]
               Σ[ x ∈ 𝔽 (sB₂ + (sC + (2 + n))) ]
                 redTm ≡ F [ K `drop ·¹ (((e ⊗ (` (Fin.suc x))) ⊗ (` (Fin.zero {n = sB₂ + (sC + (2 + n))})))) ]*
    redShape = redShapeF , redShapeE , redShapeX , redShapeEq
    Eᶠ : Frame* (suc (sB₂ + (sC + (2 + n))))
    Eᶠ = redShapeF
    fired : U.Proc n
    fired = U.ν (Bφ C (Bφ B₂ (U.φ U.acq (U.⟪ Eᶠ [ K `unit ]* ⟫ U.∥ Qᶠ))))
    fire : mid UR─→ₚ* fired
    fire = ⋆-gmap U.ν UR.RU-Res
      (Bφ-red C (Bφ-red B₂
        (subst (λ z → U.φ U.drop z UR─→ₚ* U.φ U.acq (U.⟪ Eᶠ [ K `unit ]* ⟫ U.∥ Qᶠ))
          (sym (LL₂-split ■ cong (U._∥ Qᶠ) (cong U.⟪_⟫ (proj₂ (proj₂ (proj₂ redShape))))))
          (leaf-fire-drop Eᶠ {proj₁ (proj₂ (proj₂ redShape))} Qᶠ))))
    Yleaf : U.Proc (sB₂ + (suc sC + (2 + n)))
    Yleaf = U[ QR ] (leafσ σ (zero ∷ C) B₂)
    aR : Tm (sB₂ + (suc sC + (2 + n)))
    aR = (E [ K `unit ]*) ⋯ leafσ σ (zero ∷ C) B₂
    bR : U.Proc (sB₂ + (suc sC + (2 + n)))
    bR = U[ P ] (leafσ σ (zero ∷ C) B₂)
    Yleaf≡ : Yleaf ≡ U.⟪ aR ⟫ U.∥ bR
    Yleaf≡ = refl
    RHS-split : subst U.Proc eqC Yleaf U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1
                ≡ U.⟪ subst Tm eqC aR ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1 ⟫
                  U.∥ (subst U.Proc eqC bR U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1)
    RHS-split =
        cong (λ z → z U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1)
          (subst-∥ eqC U.⟪ aR ⟫ bR ■ cong (U._∥ subst U.Proc eqC bR) (subst-⟪⟫ eqC aR))
    reconcile : (U.⟪ Eᶠ [ K `unit ]* ⟫ U.∥ Qᶠ)
                ≡ subst U.Proc eqC Yleaf U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1
    reconcile = cong₂ U._∥_ thread resid ■ sym RHS-split
      where
        subst-cod-ptR : ∀ {a c} (eq : a ≡ c) (s : (sum (zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                        subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
        subst-cod-ptR refl s i = refl
        subst-cod-pt1 : ∀ {a c} (eq : a ≡ c) (s : (sum (suc zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                        subst (λ z → (sum (suc zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
        subst-cod-pt1 refl s i = refl
        -- dropping the head handle of leafσ (suc zero ∷ C) recovers leafσ (zero ∷ C).
        leaf-drop-head : (i : 𝔽 (sum (zero ∷ C) + sum B₂ + m)) →
                         leafσ σ (suc zero ∷ C) B₂ (weakenᵣ i) ≡ leafσ σ (zero ∷ C) B₂ i
        leaf-drop-head i = sym (leafσ-shift σ cHd cTl B₂ i)
        -- *⋯θ = * (K `unit is closed).
        unit-θ : (K `unit) ⋯ θ ≡ K `unit
        unit-θ = refl
        -- Eᶠ[*]* = (Eᵂ[*]*) ⋯ θ
        Eᶠ-plug : Eᶠ [ K `unit ]* ≡ (Eᵂ [ K `unit ]*) ⋯ θ
        Eᶠ-plug = sym (frame-plug* Eᵂ θ Vθ ■ cong (frame*-⋯ Eᵂ θ Vθ [_]*) unit-θ)
        -- Eᵂ[*]* = (E[*]*) ⋯ weakenᵣ
        Eᵂ-plug : Eᵂ [ K `unit ]* ≡ (E [ K `unit ]*) ⋯ weakenᵣ
        Eᵂ-plug = sym (frame-plug*ᵣ E weakenᵣ)
        -- the leaf-substitution agreement, pointwise, lifted through subst eqC and ρ1,ρ2
        θ-agree : (x : 𝔽 (sum (zero ∷ C) + sum B₂ + m)) →
                  θ (weakenᵣ x)
                  ≡ subst Tm eqC (leafσ σ (zero ∷ C) B₂ x)
                      ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
        θ-agree x =
            cong (λ t → t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (subst-cod-pt1 eqC (leafσ σ (suc zero ∷ C) B₂) (weakenᵣ x))
          ■ cong (λ t → subst Tm eqC t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (leaf-drop-head x)
        -- the codomain leaf substitution for the RHS (leafσ of zero ∷ C).
        θR : (sum (zero ∷ C) + sum B₂ + m) →ₛ suc (sB₂ + (sC + (2 + n)))
        θR = ((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
               ·ₖ (assocSwapᵣ sC 1 ↑* sB₂)) ·ₖ assocSwapᵣ sB₂ 1
        aR≡θR : subst Tm eqC aR ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1
                ≡ (E [ K `unit ]*) ⋯ θR
        aR≡θR =
            cong (λ z → z ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
              (sym (subst-⋯ₛ-cod eqC (E [ K `unit ]*) (leafσ σ (zero ∷ C) B₂)))
          ■ cong (_⋯ assocSwapᵣ sB₂ 1)
              (fusion (E [ K `unit ]*)
                (subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
                (assocSwapᵣ sC 1 ↑* sB₂))
          ■ fusion (E [ K `unit ]*)
              ((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC (leafσ σ (zero ∷ C) B₂))
                ·ₖ (assocSwapᵣ sC 1 ↑* sB₂))
              (assocSwapᵣ sB₂ 1)
        -- (weakenᵣ ·ₖ θ) agrees pointwise with θR (the head-handle drop).
        θ-agreeR : (weakenᵣ ·ₖ θ) ≗ θR
        θ-agreeR x = θ-agree x
                   ■ cong (λ t → t ⋯ (assocSwapᵣ sC 1 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 1)
                       (sym (subst-cod-ptR eqC (leafσ σ (zero ∷ C) B₂) x))
        thread =
          cong U.⟪_⟫
            ( Eᶠ-plug
            ■ cong (_⋯ θ) Eᵂ-plug
            ■ fusion (E [ K `unit ]*) weakenᵣ θ
            ■ ⋯-cong (E [ K `unit ]*) θ-agreeR
            ■ sym aR≡θR )
        resid : Qᶠ ≡ subst U.Proc eqC bR U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1
        resid = cong (λ z → subst U.Proc eqC z U.⋯ₚ (assocSwapᵣ sC 1 ↑* sB₂) U.⋯ₚ assocSwapᵣ sB₂ 1)
                  (U-⋯ₚ P {ρ = weakenᵣ} {σ = leafσ σ (suc zero ∷ C) B₂}
                   ■ U-cong P leaf-drop-head)
    back : fired U.≋ U[ T.ν (zero ∷ C) B₂ QR ] σ
    back =
         U.ν-cong (Bφ-cong C (Bφ-cong B₂ (U.φ-cong (≡→≋ reconcile))))
      ◅◅ Eq*.symmetric _ (U.ν-cong (pushφ-down U.acq Yleaf))
      ◅◅ ≡→≋ (sym (Uν-flat σ (zero ∷ C) B₂ QR))
