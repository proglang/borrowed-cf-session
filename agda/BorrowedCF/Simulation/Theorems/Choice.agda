module BorrowedCF.Simulation.Theorems.Choice where

-- | Forward-simulation case R-Choice (select/branch) for the reworked
--   paper-matching process definitions.  Exports U-choice.
--
--   R-Choice is the channel-pair sibling of R-Com, but it does NOT change the
--   bind groups: ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) appears on BOTH sides, and no
--   weakening/substitution touches P.  So the Bφ-prefix and the leaf
--   substitution leafσ are IDENTICAL between LHS and RHS; only the plug term of
--   the two threads differs (K(select i)·(`0F) ↦ `0F,  K branch·(`y) ↦ inj i(`y)).
--
--   Route: U[ ν B₁′ B₂′ Q ]σ flattens (Uν-flat) to ν (Bφ B₁′ (Bφ B₂′ (U[Q]τ)))
--   with τ = leafσ σ B₁′ B₂′.  The outer ν is pushed down to the leaf
--   (ν-past-Bφ twice), the leaf ν fires RU-Choice (the chanTriples land at the
--   junction flags 0F / 1F STRUCTURALLY: τ 0F is the data-0 triple, τ y the
--   data-1 triple), the single step is lifted back through the Bφ-prefix
--   (Bφ-lift-step), and the ν is pulled back out (Bφ-past-ν twice) to reach
--   U[RHS]σ.  The transpose engine is COPIED verbatim from Theorems/Splits.

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

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
-- ν-past-Bφ engine
------------------------------------------------------------------------

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

subst-φ : ∀ {a b} (eq : a ≡ b) {z : U.Flag} (Q : U.Proc (suc a)) →
          subst U.Proc eq (U.φ z Q) ≡ U.φ z (subst U.Proc (cong suc eq) Q)
subst-φ refl Q = refl

substⱼ-⋯ : ∀ {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′) (X : U.Proc a′)
           (ρ : a →ᵣ b) (ρ′ : a′ →ᵣ b′) →
           (∀ x → ρ x ≡ subst 𝔽 (sym q) (ρ′ (subst 𝔽 p x))) →
           subst U.Proc (sym p) X U.⋯ₚ ρ ≡ subst U.Proc (sym q) (X U.⋯ₚ ρ′)
substⱼ-⋯ refl refl X ρ ρ′ h = U.⋯ₚ-cong X h

subst-ν : ∀ {a b} (eq : a ≡ b) (Q : U.Proc (2 + a)) →
          subst U.Proc eq (U.ν Q) ≡ U.ν (subst U.Proc (cong (2 +_) eq) Q)
subst-ν refl Q = refl

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

------------------------------------------------------------------------
-- Codomain (multi-step / silent) disjunction.
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

-- A single untyped step lifts through a Bφ prefix (φ-nest) via RU-Sync.
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

open import BorrowedCF.Simulation.TranslationProperties using (VChan; chanTriple-V; Value-subst; Ub-V)

VSub-canonₛ : ∀ (B : BindGroup) {N} (cc : UChan N) → VChan cc → VSub (canonₛ B cc)
VSub-canonₛ []            cc            Vcc = λ ()
VSub-canonₛ (b ∷ [])      (e1 , x , e2) (Ve1 , Ve2) =
  λ j → Ub-V (b + 0) e1 x e2 Ve1 Ve2 j
VSub-canonₛ (b ∷ B@(_ ∷ _)) {N} (e1 , x , e2) (Ve1 , Ve2) i =
  Value-subst (+-suc (syncs B) N)
    (++ₛ-VSub {a = b}
       (λ j → value-⋯ (Ub-V b (wk e1) (suc x) (` 0F) (Ve1 ⋯ᵛ weakenᵣ) V-` j) (weaken* ⦃ Kᵣ ⦄ (syncs B)) (λ _ → V-`))
       (VSub-canonₛ B (` 0F , suc x , wk e2) (V-` , Ve2 ⋯ᵛ weakenᵣ)) i)

-- canonₛ (suc b ∷ B) cc at index 0F is a chanTriple whose junction var sits at
-- flat position syncs (suc b ∷ B) (= syncs B for nonempty B, 0 for empty).
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

-- The push composite (assocSwapᵣ sA 2 ↑* sB) then (assocSwapᵣ sB 2) sends the
-- data-pair junction var (flat position sB+sA+d, d∈{0,1}) to position d.
assocPush-junc : ∀ (sA sB d : ℕ) {nn} (j : 𝔽 (sB + (sA + (2 + nn)))) →
                 Fin.toℕ j ≡ sB + (sA + d) → d Nat.< 2 →
                 Fin.toℕ ((assocSwapᵣ sB 2 {sA + nn}) ((assocSwapᵣ sA 2 {nn} ↑* sB) j)) ≡ d
assocPush-junc sA sB d {nn} j jeq d<2 =
    toℕ-assoc-mid sB 2 {sA + nn} ((assocSwapᵣ sA 2 {nn} ↑* sB) j) geB ltB
  ■ aritheq
  where
    -- toℕ of (assocSwapᵣ sA 2 ↑* sB) j = sB + d
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

-- frame-plug for a plain renaming (generic over the renaming Kit).
frame-plug*ᵣ : (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

open T using (_;_⊢ₚ_)

------------------------------------------------------------------------
-- The exported simulation case.
------------------------------------------------------------------------

U-choice : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
  → {γ : Struct m} {b₁ b₂ : ℕ} {B₁ B₂ : BindGroup} {i : Side}
  → {E₁ E₂ : Frame* (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
  → {P : T.Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + m)}
  → (let x = 0F
         y = wkʳ m (wkˡ (suc b₁ + sum B₁) 0F) in
     Γ ; γ ⊢ₚ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
                 ((T.⟪ E₁ [ K (`select i) ·¹ (` x) ]* ⟫ T.∥ T.⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫) T.∥ P))
  → (let x = 0F
         y = wkʳ m (wkˡ (suc b₁ + sum B₁) 0F) in
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ [ K (`select i) ·¹ (` x) ]* ⟫ T.∥ T.⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫) T.∥ P) ] σ
       UR─→ₚ*
      U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ [ ` 0F ]* ⟫ T.∥ T.⟪ E₂ [ `inj i (` y) ]* ⟫) T.∥ P) ] σ)
     ⊎
     (U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ [ K (`select i) ·¹ (` x) ]* ⟫ T.∥ T.⟪ E₂ [ K `branch ·¹ (` y) ]* ⟫) T.∥ P) ] σ
       U.≋
      U[ T.ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂)
              ((T.⟪ E₁ [ ` 0F ]* ⟫ T.∥ T.⟪ E₂ [ `inj i (` y) ]* ⟫) T.∥ P) ] σ))
U-choice {m} {n} σ Vσ Γ-S {b₁ = b₁} {b₂ = b₂} {B₁ = B₁} {B₂ = B₂} {i = i} {E₁ = E₁} {E₂ = E₂} {P = P} ⊢P =
  ≋-wrap-⊎ front fire back
  where
    B₁′ B₂′ : BindGroup
    B₁′ = suc b₁ ∷ B₁
    B₂′ = suc b₂ ∷ B₂
    yv : 𝔽 (sum B₁′ + sum B₂′ + m)
    yv = wkʳ m (wkˡ (suc b₁ + sum B₁) 0F)
    QL : T.Proc (sum B₁′ + sum B₂′ + m)
    QL = (T.⟪ E₁ [ K (`select i) ·¹ (` 0F) ]* ⟫ T.∥ T.⟪ E₂ [ K `branch ·¹ (` yv) ]* ⟫) T.∥ P
    QR : T.Proc (sum B₁′ + sum B₂′ + m)
    QR = (T.⟪ E₁ [ ` 0F ]* ⟫ T.∥ T.⟪ E₂ [ `inj i (` yv) ]* ⟫) T.∥ P
    τ : sum B₁′ + sum B₂′ + m →ₛ syncs B₂′ + (syncs B₁′ + (2 + n))
    τ = leafσ σ B₁′ B₂′
    XL XR : U.Proc (syncs B₂′ + (syncs B₁′ + (2 + n)))
    XL = U[ QL ] τ
    XR = U[ QR ] τ
    sA sB : ℕ
    sA = syncs B₁′
    sB = syncs B₂′
    -- the renaming applied to the leaf body when pushing ν down past both blocks.
    push : ∀ {k} → U.Proc (sB + (sA + (2 + k))) → U.Proc (2 + (sB + (sA + k)))
    push {k} X = (X U.⋯ₚ (assocSwapᵣ sA 2 ↑* sB)) U.⋯ₚ assocSwapᵣ sB 2
    YL YR : U.Proc (2 + (sB + (sA + n)))
    YL = push XL
    YR = push XR
    -- generic: push ν down through Bφ B₁′ (Bφ B₂′ ·)
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
    Vρ₁ : VSub ρ₁
    Vρ₁ _ = V-`
    Vρ₂ : VSub ρ₂
    Vρ₂ _ = V-`
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
    -- a leaf term renamed by the whole push.
    rn : Tm (sB + (sA + (2 + n))) → Tm (2 + (sB + (sA + n)))
    rn t = (t ⋯ ρ₁) ⋯ ρ₂
    -- F₁ channel: τ 0F = canonₛ B₁′ (*,0F,*) 0F ⋯ weaken* sB
    τ0F≡ : τ 0F ≡ canonₛ B₁′ (K `unit , 0F , K `unit) 0F ⋯ weaken* ⦃ Kᵣ ⦄ sB
    τ0F≡ = refl
    -- F₂ channel: τ yv = canonₛ B₂′ (*, weaken* sA 1F, *) 0F
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
    -- the data-channel triples (junction at 0F / 1F) produced at the leaf.
    tA0 tB0 tA1 tB1 : Tm (2 + (sB + (sA + n)))
    tA0 = rn (proj₁ tr₀ ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tB0 = rn (proj₁ (proj₂ tr₀) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tA1 = rn (proj₁ tr₁)
    tB1 = rn (proj₁ (proj₂ tr₁))
    cc₀ cc₁ : Tm (2 + (sB + (sA + n)))
    cc₀ = (tA0 ⊗ (` 0F)) ⊗ tB0
    cc₁ = (tA1 ⊗ (` 1F)) ⊗ tB1
    -- rn distributes over a chanTriple.
    rn-trip : (a c : Tm (sB + (sA + (2 + n)))) (j : 𝔽 (sB + (sA + (2 + n)))) →
              rn ((a ⊗ (` j)) ⊗ c) ≡ (rn a ⊗ (` (assocSwapᵣ sB 2 ((assocSwapᵣ sA 2 ↑* sB) j)))) ⊗ rn c
    rn-trip a c j = refl
    cc₀-eq : rn (τ 0F) ≡ cc₀
    cc₀-eq =
          cong rn (τ0F≡ ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB) (proj₁ (proj₂ (proj₂ (proj₂ tr₀)))))
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
    F₁ = (frame*-⋯ E₁ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    F₂ = (frame*-⋯ E₂ τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂
    RP : U.Proc (2 + (sB + (sA + n)))
    RP = (U[ P ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
    redexL : U.Proc (2 + (sB + (sA + n)))
    redexL = (U.⟪ F₁ [ K (`select i) ·¹ cc₀ ]* ⟫ U.∥ (U.⟪ F₂ [ K `branch ·¹ cc₁ ]* ⟫ U.∥ RP))
    contractumR : U.Proc (2 + (sB + (sA + n)))
    contractumR = (U.⟪ F₁ [ cc₀ ]* ⟫ U.∥ (U.⟪ F₂ [ `inj i cc₁ ]* ⟫ U.∥ RP))
    choiceStep : U.ν redexL UR.─→ₚ U.ν contractumR
    choiceStep = UR.RU-Choice F₁ F₂ i {e₁ = tA0} {e₁′ = tB0} {e₂ = tA1} {e₂′ = tB1}
    -- a thread ⟪ E [ p ]* ⟫ translated by τ and pushed equals F[ p⋯τ pushed ].
    threadEq : (E : Frame* (sum B₁′ + sum B₂′ + m)) (p : Tm (sum B₁′ + sum B₂′ + m)) →
               (U[ T.⟪ E [ p ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ ((frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ⋯ᶠ* ρ₂) [ rn (p ⋯ τ) ]* ⟫
    threadEq E p = cong U.⟪_⟫
      ( cong (λ t → (t ⋯ ρ₁) ⋯ ρ₂) (frame-plug* E τ Vτ)
      ■ cong (_⋯ ρ₂) (frame-plug*ᵣ (frame*-⋯ E τ Vτ) ρ₁)
      ■ frame-plug*ᵣ (frame*-⋯ E τ Vτ ⋯ᶠ* ρ₁) ρ₂ )
    thread₁≡ : (U[ T.⟪ E₁ [ K (`select i) ·¹ (` 0F) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₁ [ K (`select i) ·¹ cc₀ ]* ⟫
    thread₁≡ = threadEq E₁ (K (`select i) ·¹ (` 0F))
             ■ cong (λ t → U.⟪ F₁ [ K (`select i) ·¹ t ]* ⟫) cc₀-eq
    thread₂≡ : (U[ T.⟪ E₂ [ K `branch ·¹ (` yv) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂
               ≡ U.⟪ F₂ [ K `branch ·¹ cc₁ ]* ⟫
    thread₂≡ = threadEq E₂ (K `branch ·¹ (` yv))
             ■ cong (λ t → U.⟪ F₂ [ K `branch ·¹ t ]* ⟫) cc₁-eq
    YL≡ : YL ≡ (U.⟪ F₁ [ K (`select i) ·¹ cc₀ ]* ⟫ U.∥ U.⟪ F₂ [ K `branch ·¹ cc₁ ]* ⟫) U.∥ RP
    YL≡ = cong₂ U._∥_ (cong₂ U._∥_ thread₁≡ thread₂≡) refl
    frontL : U.ν YL U.≋ U.ν redexL
    frontL = U.ν-cong (≡→≋ YL≡ ◅◅ Eq*.symmetric _ U.∥-assoc)
    -- RHS side: contractumR back to YR
    thread₁≡R : (U[ T.⟪ E₁ [ ` 0F ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂ ≡ U.⟪ F₁ [ cc₀ ]* ⟫
    thread₁≡R = threadEq E₁ (` 0F)
              ■ cong (λ t → U.⟪ F₁ [ t ]* ⟫) cc₀-eq
    thread₂≡R : (U[ T.⟪ E₂ [ `inj i (` yv) ]* ⟫ ] τ U.⋯ₚ ρ₁) U.⋯ₚ ρ₂ ≡ U.⟪ F₂ [ `inj i cc₁ ]* ⟫
    thread₂≡R = threadEq E₂ (`inj i (` yv))
              ■ cong (λ t → U.⟪ F₂ [ t ]* ⟫) (cong (`inj i) cc₁-eq)
    YR≡ : YR ≡ (U.⟪ F₁ [ cc₀ ]* ⟫ U.∥ U.⟪ F₂ [ `inj i cc₁ ]* ⟫) U.∥ RP
    YR≡ = cong₂ U._∥_ (cong₂ U._∥_ thread₁≡R thread₂≡R) refl
    backR : U.ν contractumR U.≋ U.ν YR
    backR = U.ν-cong (U.∥-assoc ◅◅ ≡→≋ (sym YR≡))
    leaf-fire : U.ν YL UR.─→ₚ U.ν YR
    leaf-fire = UR.RU-Struct frontL choiceStep backR
    fire : Bφ B₁′ (Bφ B₂′ (U.ν YL)) UR─→ₚ* Bφ B₁′ (Bφ B₂′ (U.ν YR))
    fire = Bφ-lift-step B₁′ (Bφ-lift-step B₂′ leaf-fire) ◅ ε
    back : Bφ B₁′ (Bφ B₂′ (U.ν YR)) U.≋ U[ T.ν B₁′ B₂′ QR ] σ
    back = Eq*.symmetric _ (≡→≋ (Uν-flat σ B₁′ B₂′ QR) ◅◅ ν↓ XR)
