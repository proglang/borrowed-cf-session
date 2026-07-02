module BorrowedCF.Simulation2.Theorems.Acq where

-- | Forward-simulation case R-Acq for the reworked paper-matching process
--   definitions.  Exports U-acq.
--
--   Route (mirrors Theorems/Splits.agda): U[ ν (zero ∷ suc b₁ ∷ B₁) B₂ … ]σ
--   flattens (Uν-flat) to  ν (φ acq (Bφ C (Bφ B₂ leaf)))  with C = suc b₁ ∷ B₁.
--   The leading φ acq is pushed past both φ-nests to the leaf (φ-past-Bφ), the
--   outer ν is pulled down to the leaf (ν-past-Bφ); RU-Acquire ; RU-Cleanup fire
--   on  ν (φ acq leaf)  (the dropped handle's chanTriple junction flag is 1F
--   STRUCTURALLY — canonₛ of a zero-head chain emits middle = suc 0F = 1F — so no
--   typing hypothesis is needed); the ν is pulled back out (Bφ-past-ν) and the
--   leaf substitution is reconciled to U[RHS]σ.
--
--   The Bφ transpose engine (lines below) is COPIED verbatim from
--   Theorems/Splits.agda's hole-free prefix (itself copied from Congruence),
--   because Splits/Congruence carry open interaction metas downstream and are
--   unimportable.

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation2.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; mapᶜ-fusion; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation2.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-assoc-lt; toℕ-↑
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol; R2' )
open import BorrowedCF.Simulation2.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation2.TranslationProperties using (VChan; chanTriple-V; Value-subst)
open import BorrowedCF.Simulation2.SplitConfine using (acq-confine)
open import BorrowedCF.Simulation2.AcqSubstNat
  using (subst₂→ₖ; subst-⋯ₚ-codₖ; subst-⋯ₚ-domₖ; liftCastₖ; subst-flipₖ
        ; subst-⋯ᵏ; subst-⋯-codᵏ; subst₂-cancelₖ; subst-subst-symᵏ; varΘ-fixₛ)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

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

local-⋯ₚ-idₖ : ⦃ K : Kit 𝓕 ⦄ (P : U.Proc m) {σ : m –[ K ]→ m} → σ ≗ idₖ → P U.⋯ₚ σ ≡ P
local-⋯ₚ-idₖ U.⟪ e ⟫   eq = cong U.⟪_⟫ (⋯-id e eq)
local-⋯ₚ-idₖ (P U.∥ Q) eq = cong₂ U._∥_ (local-⋯ₚ-idₖ P eq) (local-⋯ₚ-idₖ Q eq)
local-⋯ₚ-idₖ (U.ν P)   eq = cong U.ν (local-⋯ₚ-idₖ P (id↑* 2 eq))
local-⋯ₚ-idₖ (U.φ x P) eq = cong (U.φ x) (local-⋯ₚ-idₖ P (id↑ eq))

apply-subst-ren : ∀ {a b X} (p : a ≡ b) (f : b →ᵣ X) (v : 𝔽 a) →
                  subst (λ z → z →ᵣ X) (sym p) f v ≡ f (subst 𝔽 p v)
apply-subst-ren refl f v = refl

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

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Substitution naturality of canonₛ for closed-flag channels.
--
-- Unlike `canonₛ-nat` (which needs `mapᶜ`, hence a renaming), pushing an
-- *output substitution* τ through canonₛ is fine as long as τ fixes the
-- junction flag to a variable — which is always the case when τ is a lift
-- past the ν-binders / φ-nest.  These lemmas thread that hypothesis
-- (`τ c ≡ ` c′`) explicitly; the channel data components (e₁ , e₂) may be
-- arbitrary terms and are traversed by τ as usual.
------------------------------------------------------------------------

-- Ub-nat for a substitution τ that fixes the flag to a variable.
Ub-natₛ : ∀ {a bb} (b : ℕ) (e₁ : Tm a) (c : 𝔽 a) (e₂ : Tm a)
          (τ : a →ₛ bb) (c′ : 𝔽 bb) → τ c ≡ ` c′ → (j : 𝔽 b) →
          Ub[ b ] (e₁ , c , e₂) j ⋯ τ ≡ Ub[ b ] (e₁ ⋯ τ , c′ , e₂ ⋯ τ) j
Ub-natₛ 1             e₁ c e₂ τ c′ fc zero    =
  cong (λ z → ((e₁ ⋯ τ) ⊗ z) ⊗ (e₂ ⋯ τ)) (⋯-var c τ ■ fc)
Ub-natₛ (suc (suc b)) e₁ c e₂ τ c′ fc zero    =
  cong (λ z → ((e₁ ⋯ τ) ⊗ z) ⊗ K `unit) (⋯-var c τ ■ fc)
Ub-natₛ (suc (suc b)) e₁ c e₂ τ c′ fc (suc j) =
  Ub-natₛ (suc b) (K `unit) c e₂ τ c′ fc j

-- ΘrelEqᵍ for a substitution (Kit-polymorphic subst-bookkeeping variant).
private
  ΘrelEqᵍₛ : ∀ {a bb} sB (τ : a →ₛ bb) (t : Tm (sB + suc a)) →
             subst Tm (+-suc sB a) t ⋯ (τ ↑* suc sB)
             ≡ subst Tm (+-suc sB bb) (t ⋯ ((τ ↑) ↑* sB))
  ΘrelEqᵍₛ {a} {bb} sB τ t =
      subst-⋯ᵏ (+-suc sB a) t (τ ↑* suc sB)
    ■ sym ( cong (λ r → subst Tm (+-suc sB bb) (t ⋯ r)) ΘθEq
          ■ cong (subst Tm (+-suc sB bb)) (subst-⋯-codᵏ (sym (+-suc sB bb)) t θ⁻)
          ■ subst-subst-symᵏ (+-suc sB bb) )
    where
      θ⁻ : (sB + suc a) →ₛ suc (sB + bb)
      θ⁻ = subst (λ z → z →ₛ suc (sB + bb)) (sym (+-suc sB a)) (τ ↑* suc sB)
      ΘθEq : (τ ↑) ↑* sB ≡ subst (λ z → (sB + suc a) →ₛ z) (sym (+-suc sB bb)) θ⁻
      ΘθEq = sym ( sym (subst₂→ₖ (sym (+-suc sB a)) (sym (+-suc sB bb)) (τ ↑* suc sB))
                 ■ cong (subst₂ (λ x y → x →ₛ y) (sym (+-suc sB a)) (sym (+-suc sB bb))) (sym (liftCastₖ sB τ))
                 ■ subst₂-cancelₖ (+-suc sB a) (+-suc sB bb) ((τ ↑) ↑* sB) )

-- canonₛ is natural under a target substitution that fixes the junction flag.
canonₛ-natₛ : ∀ {a bb} (B : BindGroup) (e₁ : Tm a) (x : 𝔽 a) (e₂ : Tm a)
              (τ : a →ₛ bb) (x′ : 𝔽 bb) → τ x ≡ ` x′ → (i : 𝔽 (sum B)) →
              canonₛ B (e₁ , x , e₂) i ⋯ (τ ↑* syncs B)
              ≡ canonₛ B (e₁ ⋯ τ , x′ , e₂ ⋯ τ) i
canonₛ-natₛ []            e₁ x e₂ τ x′ fx ()
canonₛ-natₛ (b ∷ [])      e₁ x e₂ τ x′ fx i = Ub-natₛ (b + 0) e₁ x e₂ τ x′ fx i
canonₛ-natₛ {a} {bb} (b ∷ B@(_ ∷ _)) e₁ x e₂ τ x′ fx i
  with Fin.splitAt b i | canonₛ-natₛ B (` 0F) (suc x) (wk e₂) (τ ↑) (suc x′) (cong (_⋯ weakenᵣ) fx)
... | inj₁ j | _  =
      ΘrelEqᵍₛ (syncs B) τ ((Ub[ b ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ (syncs B)) j)
    ■ cong (subst Tm (+-suc (syncs B) bb)) chEq
  where
    sB = syncs B
    -- (τ↑) fixes (suc x) to the variable (suc x′).
    fsx : (τ ↑) (suc x) ≡ ` (suc x′)
    fsx = cong (_⋯ weakenᵣ) fx
    chEq : ((Ub[ b ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j) ⋯ ((τ ↑) ↑* sB)
           ≡ (Ub[ b ] (wk (e₁ ⋯ τ) , suc x′ , ` 0F) ·ₖ weaken* ⦃ Kᵣ ⦄ sB) j
    chEq =
        sym (⋯-↑*-wk (Ub[ b ] (wk e₁ , suc x , ` 0F) j) (τ ↑) sB)
      ■ cong (_⋯ᵣ weaken* ⦃ Kᵣ ⦄ sB)
          ( Ub-natₛ b (wk e₁) (suc x) (` 0F) (τ ↑) (suc x′) fsx j
          ■ cong (λ z → Ub[ b ] (z , suc x′ , ` 0F) j) (sym (⋯-↑-wk e₁ τ)) )
... | inj₂ k | ih =
      ΘrelEqᵍₛ (syncs B) τ (canonₛ B (` 0F , suc x , wk e₂) k)
    ■ cong (subst Tm (+-suc (syncs B) bb))
        ( ih k
        ■ cong (λ z → canonₛ B (` 0F , suc x′ , z) k) (sym (⋯-↑-wk e₂ τ)) )

-- canonₛ-↑transpose : absorbs the front-binder ↑-lifted swap chain
-- ρa·ρb·ρc·ρd (used by R-Acq's leaf reconcile) into the channel triple.
--
-- The four renamings, with sB = syncs B :
--   ρa = assocSwapᵣ sC 1 ↑* sB        (foldable, ↑* sB)
--   ρb = assocSwapᵣ sB 1              (cross-boundary)
--   ρc = (assocSwapᵣ sC 2 ↑* sB) ↑    (front-binder ↑-lifted, ↑* sB)
--   ρd = (assocSwapᵣ sB 2) ↑          (cross-boundary, ↑-lifted)
-- Algebra used (all global ≗):
--   ρb · ρc ≗ ρc · ρb                 (commute)
--   ρb · ρd ≗ assocSwapᵣ sB 3         (R2')
--   (weaken1 ↑* sB) · assocSwapᵣ sB 3 ≗ assocSwapᵣ sB 2 · weaken1
------------------------------------------------------------------------

-- canonₛ naturality for a front-binder ↑-lifted renaming (g ↑* sB) ↑.
-- This is the bridge that lets the ↑-lifted swap ρc be folded into the
-- channel triple, threading the +-suc codomain reassociation.
canonₛ-nat-↑ : ∀ {a bb} (B : BindGroup) (cc : UChan (suc a)) (g : a →ᵣ bb) (k : 𝔽 (sum B)) →
               subst Tm (+-suc (syncs B) a) (canonₛ B cc k) ⋯ ((g ↑* syncs B) ↑)
               ≡ subst Tm (+-suc (syncs B) bb) (canonₛ B (mapᶜ (g ↑) cc) k)
canonₛ-nat-↑ {a} {bb} B cc g k =
    ΘrelEqᵍ (syncs B) g (canonₛ B cc k)
  ■ cong (subst Tm (+-suc (syncs B) bb)) (canonₛ-nat B cc (g ↑) k)

toℕ-substF-acq : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
toℕ-substF-acq refl y = refl

private
  -- generalised commuteS: assocSwapᵣ sB 1 past a front-binder ↑-lifted ↑* sB renaming.
  -- Both sides are the block permutation [sB][1][sC][2][p], computing per region to:
  --   x<sB ↦ 1+x ;  x=sB ↦ 0 ;  C-block ↦ x+2 ;  2-block ↦ x∸sC ;  tail ↦ x.
  -- Proof = a 5-region toℕ case analysis (mirror commuteS in BlockPerm.agda).
  -- assocSwapᵣ's toℕ output depends only on the toℕ of its input.
  assoc-toℕ-cong : ∀ a b {m} (b≥1 : 1 Nat.≤ b) (i j : 𝔽 (a + (b + m))) → Fin.toℕ i ≡ Fin.toℕ j →
                   Fin.toℕ (assocSwapᵣ a b i) ≡ Fin.toℕ (assocSwapᵣ a b j)
  assoc-toℕ-cong a b b≥1 i j eq with Nat.<-cmp (Fin.toℕ i) a
  ... | tri< lt _ _ = toℕ-assoc-lt a b i lt
                    ■ cong (b +_) eq
                    ■ sym (toℕ-assoc-lt a b j (subst (Nat._< a) eq lt))
  ... | tri≈ _ e _ = toℕ-assoc-mid a b i (Nat.≤-reflexive (sym e)) a<a+b
                   ■ cong (Nat._∸ a) eq
                   ■ sym (toℕ-assoc-mid a b j (Nat.≤-reflexive (sym (sym eq ■ e)))
                       (subst (Nat._< a + b) (sym (sym eq ■ e)) a<a+b-base))
    where a<a+b-base : a Nat.< a + b
          a<a+b-base = subst (Nat._≤ a + b) (Nat.+-comm a 1) (Nat.+-monoʳ-≤ a b≥1)
          a<a+b : Fin.toℕ i Nat.< a + b
          a<a+b = subst (Nat._< a + b) (sym e) a<a+b-base
  ... | tri> _ _ gt with Nat.<-cmp (Fin.toℕ i) (a + b)
  ...   | tri< lt2 _ _ = toℕ-assoc-mid a b i (Nat.<⇒≤ gt) lt2
                       ■ cong (Nat._∸ a) eq
                       ■ sym (toℕ-assoc-mid a b j (subst (a Nat.≤_) eq (Nat.<⇒≤ gt))
                           (subst (Nat._< a + b) eq lt2))
  ...   | tri≈ _ e2 _ = toℕ-assoc-ge a b i (Nat.≤-reflexive (sym e2))
                      ■ eq
                      ■ sym (toℕ-assoc-ge a b j (Nat.≤-reflexive (sym (sym eq ■ e2))))
  ...   | tri> _ _ gt2 = toℕ-assoc-ge a b i (Nat.<⇒≤ gt2)
                       ■ eq
                       ■ sym (toℕ-assoc-ge a b j (subst (a + b Nat.≤_) eq (Nat.<⇒≤ gt2)))

  ↑-zeroℕ : ∀ {n n′} (h : n →ᵣ n′) (w : 𝔽 (suc n)) → Fin.toℕ w ≡ 0 →
            Fin.toℕ ((h ↑) w) ≡ 0
  ↑-zeroℕ h w eq = toℕ-↑ h w
    ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (h j))) ]′
        (Fin.splitAt-< 1 w (subst (Nat._< 1) (sym eq) (Nat.s≤s Nat.z≤n)))
  ↑-posℕ : ∀ {n n′} (h : n →ᵣ n′) (w : 𝔽 (suc n)) (ge : 1 Nat.≤ Fin.toℕ w) →
           Fin.toℕ ((h ↑) w) ≡ suc (Fin.toℕ (h (Fin.reduce≥ w ge)))
  ↑-posℕ h w ge = toℕ-↑ h w
    ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (h j))) ]′ (Fin.splitAt-≥ 1 w ge)

  comm-bc : ∀ sB sC {p} →
            (assocSwapᵣ sB 1 {sC + (2 + p)} ·ₖ ((assocSwapᵣ sC 2 {p} ↑* sB) ↑))
            ≗ (((assocSwapᵣ sC 2 {p} ↑) ↑* sB) ·ₖ assocSwapᵣ sB 1 {2 + (sC + p)})
  comm-bc sB sC {p} x = Fin.toℕ-injective (cb sB sC x)
    where
    -- toℕ of the LHS, x < sB :  1 + x
    cb : ∀ sB sC (x : 𝔽 (sB + (1 + (sC + (2 + p))))) →
         Fin.toℕ (((assocSwapᵣ sC 2 {p} ↑* sB) ↑) (assocSwapᵣ sB 1 x))
         ≡ Fin.toℕ (assocSwapᵣ sB 1 (((assocSwapᵣ sC 2 {p} ↑) ↑* sB) x))
    cb sB sC x with Nat.<-cmp (Fin.toℕ x) sB
    ... | tri< lt _ _ =
            -- y = assocSwapᵣ sB 1 x has toℕ (1+x); apply (g↑*sB)↑ : pred has toℕ x<sB ⇒ id ⇒ result 1+x.
            ↑-posℕ gsB y yge ■ congSucL
          ■ sym ( toℕ-assoc-lt sB 1 z zlt ■ cong (1 +_) zℕ )
      where
        g   = assocSwapᵣ sC 2 {p}
        gsB = g ↑* sB
        y   = assocSwapᵣ sB 1 {sC + (2 + p)} x
        z   = ((g ↑) ↑* sB) x
        yℕ : Fin.toℕ y ≡ 1 + Fin.toℕ x
        yℕ = toℕ-assoc-lt sB 1 x lt
        yge : 1 Nat.≤ Fin.toℕ y
        yge = subst (1 Nat.≤_) (sym yℕ) (Nat.s≤s Nat.z≤n)
        redℕ : Fin.toℕ (Fin.reduce≥ y yge) ≡ Fin.toℕ x
        redℕ = toℕ-reduce≥ y yge ■ cong (Nat._∸ 1) yℕ
        red<sB : Fin.toℕ (Fin.reduce≥ y yge) Nat.< sB
        red<sB = subst (Nat._< sB) (sym redℕ) lt
        congSucL : suc (Fin.toℕ (gsB (Fin.reduce≥ y yge))) ≡ 1 + Fin.toℕ x
        congSucL = cong suc (toℕ-↑*-lt g sB (Fin.reduce≥ y yge) red<sB ■ redℕ)
        zℕ : Fin.toℕ z ≡ Fin.toℕ x
        zℕ = toℕ-↑*-lt (g ↑) sB x lt
        zlt : Fin.toℕ z Nat.< sB
        zlt = subst (Nat._< sB) (sym zℕ) lt
    ... | tri≈ _ eq _ =
            -- y has toℕ 0 ; LHS = 0.  z has toℕ sB (mid) ; RHS = z∸sB = 0.
            ↑-zeroℕ gsB y yℕ
          ■ sym ( toℕ-assoc-mid sB 1 z zge zlt ■ cong (Nat._∸ sB) zℕ ■ Nat.n∸n≡0 sB )
      where
        g   = assocSwapᵣ sC 2 {p}
        gsB = g ↑* sB
        y   = assocSwapᵣ sB 1 {sC + (2 + p)} x
        z   = ((g ↑) ↑* sB) x
        xge : sB Nat.≤ Fin.toℕ x
        xge = Nat.≤-reflexive (sym eq)
        yℕ : Fin.toℕ y ≡ 0
        yℕ = toℕ-assoc-mid sB 1 x xge (subst (Nat._< sB + 1) (sym eq)
               (subst (sB Nat.<_) (Nat.+-comm 1 sB) (Nat.n<1+n sB)))
             ■ cong (Nat._∸ sB) eq ■ Nat.n∸n≡0 sB
        zℕ : Fin.toℕ z ≡ sB
        zℕ = toℕ-↑*-ge (g ↑) sB x xge
           ■ cong (sB +_) (↑-zeroℕ g (Fin.reduce≥ x xge)
               (toℕ-reduce≥ x xge ■ cong (Nat._∸ sB) eq ■ Nat.n∸n≡0 sB))
           ■ Nat.+-identityʳ sB
        zge : sB Nat.≤ Fin.toℕ z
        zge = subst (sB Nat.≤_) (sym zℕ) Nat.≤-refl
        zlt : Fin.toℕ z Nat.< sB + 1
        zlt = subst (Nat._< sB + 1) (sym zℕ) (subst (sB Nat.<_) (Nat.+-comm 1 sB) (Nat.n<1+n sB))
    ... | tri> _ _ gt = cbHi sB sC x gt
      where
        cbHi : ∀ sB sC (x : 𝔽 (sB + (1 + (sC + (2 + p))))) → suc sB Nat.≤ Fin.toℕ x →
               Fin.toℕ (((assocSwapᵣ sC 2 {p} ↑* sB) ↑) (assocSwapᵣ sB 1 x))
               ≡ Fin.toℕ (assocSwapᵣ sB 1 (((assocSwapᵣ sC 2 {p} ↑) ↑* sB) x))
        cbHi sB sC x sb<x =
              -- LHS : suc (sB + toℕ (g iL))
              ↑-posℕ gsB y yge
            ■ cong suc (toℕ-↑*-ge g sB (Fin.reduce≥ y yge) ry≥sB)
            ■ sym (Nat.+-suc sB (Fin.toℕ (g iL)))
              -- bridge g iL ≡ g iR (same toℕ input)
            ■ cong (λ t → sB + suc t) (assoc-toℕ-cong sC 2 (Nat.s≤s Nat.z≤n) iL iR (iLℕ ■ sym iRℕ))
              -- RHS : assocSwapᵣ sB 1 z, z ≥ sB+1 ⇒ ge ⇒ toℕ z
            ■ sym ( toℕ-assoc-ge sB 1 z zge
                  ■ toℕ-↑*-ge (g ↑) sB x sB≤x
                  ■ cong (sB +_) (↑-posℕ g (Fin.reduce≥ x sB≤x) rx≥1) )
          where
            g    = assocSwapᵣ sC 2 {p}
            gsB  = g ↑* sB
            y    = assocSwapᵣ sB 1 {sC + (2 + p)} x
            z    = ((g ↑) ↑* sB) x
            sB≤x : sB Nat.≤ Fin.toℕ x
            sB≤x = Nat.<⇒≤ sb<x
            -- LHS bookkeeping
            yℕ : Fin.toℕ y ≡ Fin.toℕ x
            yℕ = toℕ-assoc-ge sB 1 x (subst (Nat._≤ Fin.toℕ x) (Nat.+-comm 1 sB) sb<x)
            yge : 1 Nat.≤ Fin.toℕ y
            yge = subst (1 Nat.≤_) (sym yℕ) (Nat.≤-trans (Nat.s≤s Nat.z≤n) sb<x)
            redyℕ : Fin.toℕ (Fin.reduce≥ y yge) ≡ Fin.toℕ x Nat.∸ 1
            redyℕ = toℕ-reduce≥ y yge ■ cong (Nat._∸ 1) yℕ
            ry≥sB : sB Nat.≤ Fin.toℕ (Fin.reduce≥ y yge)
            ry≥sB = subst (sB Nat.≤_) (sym redyℕ)
                      (subst (Nat._≤ Fin.toℕ x Nat.∸ 1) (Nat.m+n∸n≡m sB 1)
                        (Nat.∸-monoˡ-≤ 1 (subst (Nat._≤ Fin.toℕ x) (Nat.+-comm 1 sB) sb<x)))
            iL = Fin.reduce≥ (Fin.reduce≥ y yge) ry≥sB
            iLℕ : Fin.toℕ iL ≡ Fin.toℕ x Nat.∸ 1 Nat.∸ sB
            iLℕ = toℕ-reduce≥ (Fin.reduce≥ y yge) ry≥sB ■ cong (Nat._∸ sB) redyℕ
            -- RHS bookkeeping
            rx≥1 : 1 Nat.≤ Fin.toℕ (Fin.reduce≥ x sB≤x)
            rx≥1 = subst (1 Nat.≤_) (sym (toℕ-reduce≥ x sB≤x)) (Nat.m<n⇒0<n∸m sb<x)
            iR = Fin.reduce≥ (Fin.reduce≥ x sB≤x) rx≥1
            ∸swap : Fin.toℕ x Nat.∸ sB Nat.∸ 1 ≡ Fin.toℕ x Nat.∸ 1 Nat.∸ sB
            ∸swap = Nat.∸-+-assoc (Fin.toℕ x) sB 1
                  ■ cong (Fin.toℕ x Nat.∸_) (Nat.+-comm sB 1)
                  ■ sym (Nat.∸-+-assoc (Fin.toℕ x) 1 sB)
            iRℕ : Fin.toℕ iR ≡ Fin.toℕ x Nat.∸ 1 Nat.∸ sB
            iRℕ = toℕ-reduce≥ (Fin.reduce≥ x sB≤x) rx≥1
                ■ cong (Nat._∸ 1) (toℕ-reduce≥ x sB≤x)
                ■ ∸swap
            zℕ : Fin.toℕ z ≡ sB + suc (Fin.toℕ (g iR))
            zℕ = toℕ-↑*-ge (g ↑) sB x sB≤x
               ■ cong (sB +_) (↑-posℕ g (Fin.reduce≥ x sB≤x) rx≥1)
            zge : sB + 1 Nat.≤ Fin.toℕ z
            zge = subst (sB + 1 Nat.≤_) (sym zℕ)
                    (Nat.+-monoʳ-≤ sB (Nat.s≤s Nat.z≤n))
  -- weakenᵣ on 𝔽 is suc.
  weakenᵣ≡suc : ∀ {m} (x : 𝔽 m) → Fin.toℕ (weakenᵣ x) ≡ suc (Fin.toℕ x)
  weakenᵣ≡suc x = toℕ-weaken*ᵣ 1 x
  -- toℕ of weakenᵣ ↑* sB on a high index.
  wk↑*ℕ : ∀ sB {p} (x : 𝔽 (sB + (2 + p))) (ge : sB Nat.≤ Fin.toℕ x) →
          Fin.toℕ ((weakenᵣ {n = 2 + p} ↑* sB) x) ≡ suc (Fin.toℕ x)
  wk↑*ℕ sB x ge =
      toℕ-↑*-ge weakenᵣ sB x ge
    ■ cong (sB +_) (weakenᵣ≡suc (Fin.reduce≥ x ge))
    ■ Nat.+-suc sB (Fin.toℕ (Fin.reduce≥ x ge))
    ■ cong suc ( cong (sB +_) (toℕ-reduce≥ x ge) ■ Nat.m+[n∸m]≡n ge )
  wk-swap3-hitop : ∀ sB {p} (x : 𝔽 (sB + (2 + p))) (ge : sB Nat.≤ Fin.toℕ x) →
                   sB + 2 Nat.≤ Fin.toℕ x →
                   Fin.toℕ (((weakenᵣ {n = 2 + p} ↑* sB) ·ₖ assocSwapᵣ sB 3 {p}) x)
                   ≡ Fin.toℕ ((assocSwapᵣ sB 2 {p} ·ₖ weakenᵣ) x)
  wk-swap3-hitop sB {p} x ge gesb2 =
      toℕ-assoc-ge sB 3 ((weakenᵣ {n = 2 + p} ↑* sB) x) geW
    ■ wk↑*ℕ sB x ge
    ■ sym ( weakenᵣ≡suc (assocSwapᵣ sB 2 {p} x)
          ■ cong suc (toℕ-assoc-ge sB 2 x gesb2) )
    where
      geW : sB + 3 Nat.≤ Fin.toℕ ((weakenᵣ {n = 2 + p} ↑* sB) x)
      geW = subst (sB + 3 Nat.≤_) (sym (wk↑*ℕ sB x ge))
              (subst (Nat._≤ suc (Fin.toℕ x)) (sym (Nat.+-suc sB 2)) (Nat.s≤s gesb2))
  wk-swap3-hi : ∀ sB {p} (x : 𝔽 (sB + (2 + p))) → sB Nat.≤ Fin.toℕ x →
                Fin.toℕ (((weakenᵣ {n = 2 + p} ↑* sB) ·ₖ assocSwapᵣ sB 3 {p}) x)
                ≡ Fin.toℕ ((assocSwapᵣ sB 2 {p} ·ₖ weakenᵣ) x)
  wk-swap3-hi sB {p} x ge with Nat.<-cmp (Fin.toℕ x) (sB + 2)
  ... | tri< ltsb2 _ _ =
          toℕ-assoc-mid sB 3 wval geW ltW
        ■ cong (Nat._∸ sB) (wk↑*ℕ sB x ge) ■ Nat.+-∸-assoc 1 ge
        ■ sym ( weakenᵣ≡suc (assocSwapᵣ sB 2 {p} x)
              ■ cong suc (toℕ-assoc-mid sB 2 x ge ltsb2) )
    where
      wval = (weakenᵣ {n = 2 + p} ↑* sB) x
      geW : sB Nat.≤ Fin.toℕ wval
      geW = subst (sB Nat.≤_) (sym (wk↑*ℕ sB x ge)) (Nat.≤-trans ge (Nat.n≤1+n _))
      ltW : Fin.toℕ wval Nat.< sB + 3
      ltW = subst (Nat._< sB + 3) (sym (wk↑*ℕ sB x ge))
              (subst (suc (Fin.toℕ x) Nat.<_) (sym (Nat.+-suc sB 2)) (Nat.s≤s ltsb2))
  ... | tri≈ _ eqsb2 _ = wk-swap3-hitop sB x ge (Nat.≤-reflexive (sym eqsb2))
  ... | tri> _ _ gtsb2 = wk-swap3-hitop sB x ge (Nat.<⇒≤ gtsb2)
  -- (weaken1 ↑* sB) · assocSwapᵣ sB 3 ≗ assocSwapᵣ sB 2 · weaken1
  wk-swap3 : ∀ sB {p} →
             ((weakenᵣ {n = 2 + p} ↑* sB) ·ₖ assocSwapᵣ sB 3 {p})
             ≗ (assocSwapᵣ sB 2 {p} ·ₖ weakenᵣ)
  wk-swap3 sB {p} x with Nat.<-cmp (Fin.toℕ x) sB
  ... | tri< lt _ _ = Fin.toℕ-injective
        ( toℕ-assoc-lt sB 3 ((weakenᵣ {n = 2 + p} ↑* sB) x) wlt
        ■ cong (3 +_) wltℕ
        ■ sym ( weakenᵣ≡suc (assocSwapᵣ sB 2 {p} x)
              ■ cong suc (toℕ-assoc-lt sB 2 x lt) ) )
    where
      wltℕ : Fin.toℕ ((weakenᵣ {n = 2 + p} ↑* sB) x) ≡ Fin.toℕ x
      wltℕ = toℕ-↑*-lt (weakenᵣ {n = 2 + p}) sB x lt
      wlt : Fin.toℕ ((weakenᵣ {n = 2 + p} ↑* sB) x) Nat.< sB
      wlt = subst (Nat._< sB) (sym wltℕ) lt
  ... | tri≈ _ eq _ = Fin.toℕ-injective (wk-swap3-hi sB x (Nat.≤-reflexive (sym eq)))
  ... | tri> _ _ gt = Fin.toℕ-injective (wk-swap3-hi sB x (Nat.<⇒≤ gt))

-- The R-Acq leaf transpose: absorbs ρa·ρb·ρc·ρd into the channel triple.
canonₛ-substcod : ∀ {a c} (q : a ≡ c) (B : BindGroup) (cc : UChan a) (k : 𝔽 (sum B)) →
   subst Tm (cong (syncs B +_) q) (canonₛ B cc k) ≡ canonₛ B (subst UChan q cc) k
canonₛ-substcod refl B cc k = refl

-- K `unit is fixed by subst and by any renaming.
substK-⋯ : ∀ {a c bb} (q : a ≡ c) (ρ : c →ᵣ bb) →
           subst Tm q (K `unit) ⋯ ρ ≡ K `unit
substK-⋯ refl ρ = refl

subst-UChan : ∀ {a c} (q : a ≡ c) (e₁ : Tm a) (x : 𝔽 a) (e₂ : Tm a) →
              subst UChan q (e₁ , x , e₂) ≡ (subst Tm q e₁ , subst 𝔽 q x , subst Tm q e₂)
subst-UChan refl e₁ x e₂ = refl

canonₛ-↑transpose : ∀ {sC n} (B : BindGroup) (k : 𝔽 (sum B)) →
  subst Tm (cong (syncs B +_) (sym (+-suc sC (suc (suc n)))))
    (canonₛ B (K `unit , weaken* ⦃ Kᵣ ⦄ (suc sC) 1F , K `unit) k)
    ⋯ (assocSwapᵣ sC 1 {2 + n} ↑* syncs B)
    ⋯ assocSwapᵣ (syncs B) 1 {sC + (2 + n)}
    ⋯ ((assocSwapᵣ sC 2 {n} ↑* syncs B) ↑)
    ⋯ (assocSwapᵣ (syncs B) 2 {sC + n} ↑)
  ≡ canonₛ B (K `unit , 1F , K `unit) k ⋯ assocSwapᵣ (syncs B) 2 {sC + n} ⋯ weakenᵣ
-- Non-inductive assembly, valid for ANY nonempty B (empty tail included, since
-- every step only touches the channel-triple argument via canonₛ-nat / mapᶜ):
--   1. fold ρa (= assocSwapᵣ sC 1 ↑* sB) into cc1 via canonₛ-nat.
--   2. comm-bc : ρb · ρc ≗ ((assocSwapᵣ sC 2 ↑)↑* sB) · ρb'  (move ρb right).
--   3. fold (assocSwapᵣ sC 2 ↑)↑* sB into cc via canonₛ-nat (g = assocSwapᵣ sC 2 ↑).
--   4. R2' sB 2 : ρb' · ρd ≗ assocSwapᵣ sB 3   (merge the two cross-boundary swaps).
--   5. reverse-fold the resulting triple (unit,2F,unit)=mapᶜ weaken1 (unit,1F,unit)
--      via canonₛ-nat, then wk-swap3 : (weaken1↑*sB)·assocSwapᵣ sB 3 ≗ assocSwapᵣ sB 2·weakenᵣ.
--   The subst eqC at the front is threaded with subst-⋯-dom-local / ΘrelEqᵍ.
canonₛ-↑transpose {sC} {n} (b ∷ B)       k =
    -- eliminate the front subst into the channel triple
    cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
      (canonₛ-substcod (sym (+-suc sC (2 + n))) Bg cc1 k)
    -- step 1: fold ρa
  ■ cong (λ z → z ⋯ ρb ⋯ ρc ⋯ ρd) (canonₛ-nat Bg cc1♭ (assocSwapᵣ sC 1 {2 + n}) k)
    -- step 2: commute ρb past ρc, fuse/unfuse
  ■ cong (λ z → z ⋯ ρd)
      ( fusion (canonₛ Bg cc2 k) ρb ρc
      ■ ⋯-cong (canonₛ Bg cc2 k) (comm-bc sB sC {n})
      ■ sym (fusion (canonₛ Bg cc2 k) ρc' ρb') )
    -- step 3: fold ρc'
  ■ cong (λ z → z ⋯ ρb' ⋯ ρd) (canonₛ-nat Bg cc2 (assocSwapᵣ sC 2 {n} ↑) k)
    -- step 4: merge ρb' · ρd via R2'
  ■ ( fusion (canonₛ Bg cc3 k) ρb' ρd
    ■ ⋯-cong (canonₛ Bg cc3 k) (R2' sB 2 {sC + n}) )
    -- step 5: cc3 ≡ (unit,2F,unit) ; reverse-fold ; wk-swap3
  ■ cong (λ cc → canonₛ Bg cc k ⋯ assocSwapᵣ sB 3 {sC + n}) cc3≡
  ■ cong (λ z → z ⋯ assocSwapᵣ sB 3 {sC + n})
      (sym (canonₛ-nat Bg (K `unit , 1F , K `unit) weakenᵣ k
            ■ cong (λ cc → canonₛ Bg cc k) mapwk≡))
  ■ fusion (canonₛ Bg (K `unit , 1F , K `unit) k) (weakenᵣ ↑* sB) (assocSwapᵣ sB 3 {sC + n})
  ■ ⋯-cong (canonₛ Bg (K `unit , 1F , K `unit) k) (wk-swap3 sB {sC + n})
  ■ sym (fusion (canonₛ Bg (K `unit , 1F , K `unit) k) (assocSwapᵣ sB 2 {sC + n}) weakenᵣ)
  where
    Bg  = b ∷ B
    sB  = syncs Bg
    cc1 : UChan (suc sC + (2 + n))
    cc1 = (K `unit , weaken* ⦃ Kᵣ ⦄ (suc sC) 1F , K `unit)
    ρa  = assocSwapᵣ sC 1 {2 + n} ↑* sB
    ρb  = assocSwapᵣ sB 1 {sC + (2 + n)}
    ρc  = (assocSwapᵣ sC 2 {n} ↑* sB) ↑
    ρc' = ((assocSwapᵣ sC 2 {n} ↑) ↑* sB)
    ρb' = assocSwapᵣ sB 1 {2 + (sC + n)}
    ρd  = (assocSwapᵣ sB 2 {sC + n}) ↑
    cc1♭ : UChan (sC + (1 + (2 + n)))
    cc1♭ = subst UChan (sym (+-suc sC (2 + n))) cc1
    cc2 : UChan (1 + (sC + (2 + n)))
    cc2 = mapᶜ (assocSwapᵣ sC 1 {2 + n}) cc1♭
    cc3 : UChan (suc (2 + (sC + n)))
    cc3 = mapᶜ (assocSwapᵣ sC 2 {n} ↑) cc2
    cc3≡ : cc3 ≡ (K `unit , 2F , K `unit)
    cc3≡ =
        mapᶜ-fusion (assocSwapᵣ sC 1 {2 + n}) (assocSwapᵣ sC 2 {n} ↑) cc1♭
      ■ cong (mapᶜ ρcomp) (subst-UChan qC (K `unit) (weaken* ⦃ Kᵣ ⦄ (suc sC) 1F) (K `unit))
      ■ cong₂ _,_ (substK-⋯ qC ρcomp)
          (cong₂ _,_ flag2 (substK-⋯ qC ρcomp))
      where
        qC : suc sC + (2 + n) ≡ sC + (1 + (2 + n))
        qC = sym (+-suc sC (2 + n))
        ρcomp = (assocSwapᵣ sC 1 {2 + n}) ·ₖ (assocSwapᵣ sC 2 {n} ↑)
        flag♭ : 𝔽 (sC + (1 + (2 + n)))
        flag♭ = subst 𝔽 qC (weaken* ⦃ Kᵣ ⦄ (suc sC) 1F)
        flag♭ℕ : Fin.toℕ flag♭ ≡ sC + 2
        flag♭ℕ = toℕ-substF-acq qC (weaken* ⦃ Kᵣ ⦄ (suc sC) 1F)
               ■ toℕ-weaken*ᵣ (suc sC) 1F ■ sym (+-suc sC 1)
        f1 : 𝔽 (1 + (sC + (2 + n)))
        f1 = assocSwapᵣ sC 1 {2 + n} flag♭
        f1ℕ : Fin.toℕ f1 ≡ sC + 2
        f1ℕ = toℕ-assoc-ge sC 1 flag♭
                (subst (sC + 1 Nat.≤_) (sym flag♭ℕ)
                  (subst (Nat._≤ sC + 2) refl (Nat.+-monoʳ-≤ sC (Nat.s≤s Nat.z≤n))))
            ■ flag♭ℕ
        f1ge1 : 1 Nat.≤ Fin.toℕ f1
        f1ge1 = subst (1 Nat.≤_) (sym f1ℕ) (subst (1 Nat.≤_) (sym (+-suc sC 1)) (Nat.s≤s Nat.z≤n))
        redf1 : Fin.toℕ (Fin.reduce≥ f1 f1ge1) ≡ sC + 1
        redf1 = toℕ-reduce≥ f1 f1ge1 ■ cong (Nat._∸ 1) f1ℕ
              ■ cong (Nat._∸ 1) (Nat.+-comm sC 2) ■ Nat.+-comm 1 sC
        flag2 : ρcomp flag♭ ≡ 2F
        flag2 = Fin.toℕ-injective
          ( toℕ-↑ (assocSwapᵣ sC 2 {n}) f1
          ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ sC 2 {n} j))) ]′
              (Fin.splitAt-≥ 1 f1 f1ge1)
          ■ cong suc
              ( toℕ-assoc-mid sC 2 (Fin.reduce≥ f1 f1ge1)
                  (subst (sC Nat.≤_) (sym redf1) (Nat.m≤m+n sC 1))
                  (subst (Nat._< sC + 2) (sym redf1) (Nat.+-monoʳ-< sC (Nat.s≤s (Nat.s≤s Nat.z≤n))))
              ■ cong (Nat._∸ sC) redf1 ■ Nat.m+n∸m≡n sC 1 ) )
    mapwk≡ : mapᶜ weakenᵣ (K `unit , 1F , K `unit) ≡ (K `unit , 2F , K `unit)
    mapwk≡ = cong₂ _,_ refl (cong₂ _,_ (Fin.toℕ-injective (toℕ-weaken*ᵣ 1 (Fin.suc (Fin.zero {suc (sC + n)})))) refl)


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

-- Substitution sibling of Bφ-⋯: pushing an *output substitution* through a Bφ
-- block.  Same proof as Bφ-⋯, using the Kit-polymorphic bookkeeping lemmas.
Bφ-⋯ₛ : ∀ {n n′} (B : BindGroup) (P : U.Proc (syncs B + n)) (τ : n →ₛ n′) →
        Bφ B P U.⋯ₚ τ ≡ Bφ B (P U.⋯ₚ (τ ↑* syncs B))
Bφ-⋯ₛ []            P τ = refl
Bφ-⋯ₛ (b ∷ [])      P τ = refl
Bφ-⋯ₛ {n} {n′} (b ∷ B@(_ ∷ _)) P τ =
  cong (U.φ ϕ[ b ])
    ( Bφ-⋯ₛ B (subst U.Proc (sym (+-suc (syncs B) n)) P) (τ ↑)
    ■ cong (Bφ B) bodyeq )
  where
    sB = syncs B
    Θ : (sB + suc n) →ₛ (sB + suc n′)
    Θ = (τ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ₛ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ₛ z) (sym (+-suc sB n′)) (τ ↑* suc sB)
    Θ⁺eq = subst-flipₖ (+-suc sB n′) (sym (subst₂→ₖ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCastₖ sB τ)
    bodyeq : (subst U.Proc (sym (+-suc sB n)) P) U.⋯ₚ ((τ ↑) ↑* sB)
             ≡ subst U.Proc (sym (+-suc sB n′)) (P U.⋯ₚ (τ ↑* suc sB))
    bodyeq =
        subst-⋯ₚ-domₖ (+-suc sB n) P Θ
      ■ cong (P U.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-codₖ (sym (+-suc sB n′)) P (τ ↑* suc sB)

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

-- ν (φ acq (⟪ F[acq · 𝓒[`0F × 1F × e]] ⟫ ∥ Q)) fires RU-Acquire then, under the
-- ν, RU-Cleanup, yielding ν ((⟪ F[𝓒[`0F×1F×e]] ⟫ ∥ Q) ⋯ₚ ⦅*⦆ₛ).
leaf-fire : (F : Frame* (3 + n)) {e : Tm (3 + n)} (Q : U.Proc (3 + n)) →
  U.ν (U.φ U.acq (U.⟪ F [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ e) ]* ⟫ U.∥ Q))
    UR─→ₚ*
  U.ν ((U.⟪ F [ ((` 0F) ⊗ (` 1F)) ⊗ e ]* ⟫ U.∥ Q) U.⋯ₚ ⦅ * ⦆ₛ)
leaf-fire F {e} Q = UR.RU-Acquire F ◅ UR.RU-Res UR.RU-Cleanup ◅ ε

-- Star-congruences for the untyped reduction under φ binders and substs, to
-- propagate the leaf firing back out through the Bφ blocks.
φ-fire* : {n : ℕ} (z : U.Flag) {P Q : U.Proc (suc n)} →
          P UR─→ₚ* Q → U.φ z P UR─→ₚ* U.φ z Q
φ-fire* z ε        = ε
φ-fire* z (r ◅ rs) = UR.RU-Sync r ◅ φ-fire* z rs

subst-fire* : ∀ {a b} (eq : a ≡ b) {P Q : U.Proc a} →
              P UR─→ₚ* Q → subst U.Proc eq P UR─→ₚ* subst U.Proc eq Q
subst-fire* refl r = r

Bφ-fire : ∀ {n} (B : BindGroup) {P Q : U.Proc (syncs B + n)} →
          P UR─→ₚ* Q → Bφ {n} B P UR─→ₚ* Bφ B Q
Bφ-fire []            r = r
Bφ-fire (b ∷ [])      r = r
Bφ-fire {n} (b ∷ B@(_ ∷ _)) r =
  φ-fire* ϕ[ b ] (Bφ-fire B (subst-fire* (sym (+-suc (syncs B) n)) r))

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
-- flat position syncs (suc b ∷ B) + toℕ x.
canonₛ-head-triple : ∀ {N} (b : ℕ) (B : BindGroup) (e1 e2 : Tm N) (x : 𝔽 N) →
  Σ[ a ∈ Tm (syncs (suc b ∷ B) + N) ] Σ[ c ∈ Tm (syncs (suc b ∷ B) + N) ]
  Σ[ j ∈ 𝔽 (syncs (suc b ∷ B) + N) ]
    (canonₛ (suc b ∷ B) (e1 , x , e2) 0F ≡ (a ⊗ (` j)) ⊗ c)
    × (Fin.toℕ j ≡ syncs (suc b ∷ B) + Fin.toℕ x)
canonₛ-head-triple zero        []        e1 e2 x =
  e1 , e2 , x , refl , refl
canonₛ-head-triple (suc b)     []        e1 e2 x =
  e1 , * , x , refl , refl
canonₛ-head-triple {N} zero    (c′ ∷ B) e1 e2 x =
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

-- The push composite (assocSwapᵣ sA 2 ↑* sB) then (assocSwapᵣ sB 2) sends the
-- data-pair junction var (flat position sB+sA+d, d∈{0,1}) to position d.
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

-- frame-plug for a plain renaming (generic over the renaming Kit).
frame-plug*ᵣ : (E : Frame* m) {t : Tm m} (ρ : m →ᵣ n) →
               (E [ t ]*) ⋯ ρ ≡ (E ⋯ᶠ* ρ) [ t ⋯ ρ ]*
frame-plug*ᵣ []       ρ = refl
frame-plug*ᵣ (E ∷ E*) ρ =
  frame-plug₁ E ρ (λ x → V-`) ■ cong (frame-⋯ E ρ (λ x → V-`) [_]) (frame-plug*ᵣ E* ρ)

toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
toℕ-subst𝔽 refl y = refl

-- frame congruence / fusion helpers (copied from Theorems/Splits, which is
-- unimportable because it carries downstream interaction metas).
app₁-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ L → Value e₁} {V₂ : d ≡ L → Value e₂}
          → e₁ ≡ e₂ → app₁ e₁ d V₁ ≡ app₁ e₂ d V₂
app₁-cong refl = cong (app₁ _ _) (funext λ x → Value-irr)

app₂-cong : {e₁ e₂ : Tm n} {d : Dir} {V₁ : d ≡ 𝟙 ⊎ d ≡ R → Value e₁} {V₂ : d ≡ 𝟙 ⊎ d ≡ R → Value e₂}
          → e₁ ≡ e₂ → app₂ e₁ d V₁ ≡ app₂ e₂ d V₂
app₂-cong refl = cong (app₂ _ _) (funext λ x → Value-irr)

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

frame*-cong : (E : Frame* m) {σ τ : m →ₛ n} (Vσ : VSub σ) (Vτ : VSub τ) → σ ≗ τ →
              frame*-⋯ E σ Vσ ≡ frame*-⋯ E τ Vτ
frame*-cong []       Vσ Vτ eq = refl
frame*-cong (F ∷ E*) Vσ Vτ eq = cong₂ _∷_ (frame-cong F Vσ Vτ eq) (frame*-cong E* Vσ Vτ eq)

F-⋯f*-fuse : (E : Frame* m) {p : ℕ} {ρ : m →ᵣ p} {τ : p →ₛ n} (Vτ : VSub τ) (Vρτ : VSub (ρ ·ₖ τ)) →
             frame*-⋯ (E ⋯ᶠ* ρ) τ Vτ ≡ frame*-⋯ E (ρ ·ₖ τ) Vρτ
F-⋯f*-fuse []       Vτ Vρτ = refl
F-⋯f*-fuse (F ∷ E*) {ρ} {τ} Vτ Vρτ =
  cong₂ _∷_ (frame-fusion-gen F (λ _ → V-`) Vτ Vρτ) (F-⋯f*-fuse E* Vτ Vρτ)

·ₖ-VSubᵣ : {m p n : ℕ} (ρ : m →ᵣ p) {τ : p →ₛ n} → VSub τ → VSub (ρ ·ₖ τ)
·ₖ-VSubᵣ ρ {τ} Vτ i = Vτ (ρ i)

-- The acq head-triple: canonₛ (suc b ∷ B) (` 0F , 1F , e2) 0F is a triple of two
-- variables (endpoint, junction) over a third term.  Endpoint var sits at flat
-- position syncs(suc b∷B)+0, junction at syncs(suc b∷B)+1.
canonₛ-acq-head : ∀ {N} (b : ℕ) (B : BindGroup) (e2 : Tm (2 + N)) →
  Σ[ ja ∈ 𝔽 (syncs (suc b ∷ B) + (2 + N)) ] Σ[ jj ∈ 𝔽 (syncs (suc b ∷ B) + (2 + N)) ]
  Σ[ tc ∈ Tm (syncs (suc b ∷ B) + (2 + N)) ]
    (canonₛ (suc b ∷ B) (` 0F , 1F , e2) 0F ≡ ((` ja) ⊗ (` jj)) ⊗ tc)
    × (Fin.toℕ ja ≡ syncs (suc b ∷ B) + 0)
    × (Fin.toℕ jj ≡ syncs (suc b ∷ B) + 1)
canonₛ-acq-head zero    []        e2 = 0F , 1F , e2 , refl , refl , refl
canonₛ-acq-head (suc b) []        e2 = 0F , 1F , * , refl , refl , refl
canonₛ-acq-head {N} zero    (c′ ∷ B) e2 =
  ( subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))
  , subst Tm (+-suc sB (2 + N)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , tripeq
  , jaeq
  , jjeq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc zero ∷ c′ ∷ B) (` 0F , 1F , e2) 0F
             ≡ ((` subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F)))
                 ⊗ (` subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))))
                 ⊗ subst Tm (+-suc sB (2 + N)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB (2 + N))
               (weaken* ⦃ Kᵣ ⦄ sB (suc 0F)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F)) ((` 0F) ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (ja jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq (((` ja) ⊗ (` jj)) ⊗ C)
                    ≡ ((` subst 𝔽 eq ja) ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl ja jj C = refl
    jaeq : Fin.toℕ (subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))) ≡ suc sB + 0
    jaeq = toℕ-subst𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
         ■ toℕ-weaken*ᵣ sB (suc 0F) ■ +-suc sB 0
    jjeq : Fin.toℕ (subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))) ≡ suc sB + 1
    jjeq = toℕ-subst𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))
         ■ toℕ-weaken*ᵣ sB (suc 1F) ■ +-suc sB 1
canonₛ-acq-head {N} (suc b) (c′ ∷ B) e2 =
  ( subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))
  , subst Tm (+-suc sB (2 + N)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
  , tripeq
  , jaeq
  , jjeq )
  where
    sB = syncs (c′ ∷ B)
    tripeq : canonₛ (suc (suc b) ∷ c′ ∷ B) (` 0F , 1F , e2) 0F
             ≡ ((` subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F)))
                 ⊗ (` subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))))
                 ⊗ subst Tm (+-suc sB (2 + N)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
    tripeq = substTrip (+-suc sB (2 + N))
               (weaken* ⦃ Kᵣ ⦄ sB (suc 0F)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F)) (* ⋯ weaken* ⦃ Kᵣ ⦄ sB)
      where
        substTrip : ∀ {p q} (eq : p ≡ q) (ja jj : 𝔽 p) (C : Tm p) →
                    subst Tm eq (((` ja) ⊗ (` jj)) ⊗ C)
                    ≡ ((` subst 𝔽 eq ja) ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
        substTrip refl ja jj C = refl
    jaeq : Fin.toℕ (subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))) ≡ suc sB + 0
    jaeq = toℕ-subst𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
         ■ toℕ-weaken*ᵣ sB (suc 0F) ■ +-suc sB 0
    jjeq : Fin.toℕ (subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))) ≡ suc sB + 1
    jjeq = toℕ-subst𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 1F))
         ■ toℕ-weaken*ᵣ sB (suc 1F) ■ +-suc sB 1

-- Variable-base sibling of canonₛ-↑transpose.  The C-region leaf canonₛ C
-- (` 0F , 1F , K `unit) j sits behind a foreign front block sB₂ (weaken* sB₂),
-- and the acq cleanup ⦅ K `unit ⦆ₛ collapses the head-channel variable ` 0F to *.
varC-transpose : ∀ {n} (C : BindGroup) (sB₂ : ℕ) (j : 𝔽 (sum C)) →
  subst Tm (cong (sB₂ +_) (sym (+-suc (syncs C) (suc (suc n)))))
    (subst Tm (+-suc (syncs C) (suc (suc n)))
       (canonₛ C (` 0F , 1F , K `unit) j) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    ⋯ (assocSwapᵣ (syncs C) 1 {2 + n} ↑* sB₂)
    ⋯ assocSwapᵣ sB₂ 1 {syncs C + (2 + n)}
    ⋯ ((assocSwapᵣ (syncs C) 2 {n} ↑* sB₂) ↑)
    ⋯ ((assocSwapᵣ sB₂ 2 {syncs C + n}) ↑)
    ⋯ ⦅ K `unit ⦆ₛ
  ≡ (canonₛ C (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    ⋯ (assocSwapᵣ (syncs C) 2 {n} ↑* sB₂) ⋯ assocSwapᵣ sB₂ 2 {syncs C + n}
varC-transpose []            sB₂ ()
-- Uniform proof for any nonempty leading group (empty tail included): recurse on
-- (Fin.splitAt b j).  inj₁ jh is a finite head-triple leaf computation; inj₂ k
-- recurses on C with the channel-triple flag shifted (1F→2F), threading the +-suc
-- codomain reassociation via canonₛ-substcod / canonₛ-nat-↑ / ΘrelEqᵍ exactly as
-- canonₛ-↑transpose's cons does.
varC-transpose {n} (b ∷ C)       sB₂ j =
    push
  ■ cong (λ z → z ⋯ ρc-base ⋯ ρd-base) core
  where
    Cg : BindGroup
    Cg = b ∷ C
    sC : ℕ
    sC = syncs Cg
    M0 : Tm (sB₂ + (sC + (3 + n)))
    M0 = subst Tm (cong (sB₂ +_) (sym (+-suc sC (suc (suc n)))))
           (subst Tm (+-suc sC (suc (suc n))) (canonₛ Cg (` 0F , 1F , K `unit) j) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    ρa = assocSwapᵣ sC 1 {2 + n} ↑* sB₂
    ρb = assocSwapᵣ sB₂ 1 {sC + (2 + n)}
    ρc = (assocSwapᵣ sC 2 {n} ↑* sB₂) ↑
    ρd = (assocSwapᵣ sB₂ 2 {sC + n}) ↑
    ρc-base = assocSwapᵣ sC 2 {n} ↑* sB₂
    ρd-base = assocSwapᵣ sB₂ 2 {sC + n}
    W : Tm (suc (sB₂ + (sC + (2 + n))))
    W = M0 ⋯ ρa ⋯ ρb
    push : W ⋯ ρc ⋯ ρd ⋯ ⦅ K `unit ⦆ₛ ≡ W ⋯ ⦅ K `unit ⦆ₛ ⋯ ρc-base ⋯ ρd-base
    push = sym (dist-↑-⦅⦆-⋯ (W ⋯ ρc) (K `unit) ρd-base)
         ■ cong (_⋯ ρd-base) (sym (dist-↑-⦅⦆-⋯ W (K `unit) ρc-base))
    core : W ⋯ ⦅ K `unit ⦆ₛ ≡ canonₛ Cg (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    core = {!core!}

open T using (_;_⊢ₚ_)

-- Output-substitution push for the singleton acq-cleanup substitution.
-- (General output substitutions are ill-typed against UChan's Fin flag; this
--  push is valid because ⦅*⦆ₛ, once lifted past the φ-nest binders, fixes every
--  flag index — the injected handle sits strictly above the nest.)
U-σ⋯ₛ : ∀ {m n n′} (P : T.Proc m) {σ : m →ₛ n} {τ : n →ₛ n′} →
        U[ P ] σ U.⋯ₚ τ ≡ U[ P ] (σ ·ₖ τ)
U-σ⋯ₛ T.⟪ e ⟫ {σ} {τ} = cong U.⟪_⟫ (fusion e σ τ)
U-σ⋯ₛ (P T.∥ Q)       = cong₂ U._∥_ (U-σ⋯ₛ P) (U-σ⋯ₛ Q)
U-σ⋯ₛ {n = n} {n′ = n′} (T.ν B₁ B₂ P) {σ} {τ} =
    cong (U._⋯ₚ τ) (Uν-flat σ B₁ B₂ P)
  ■ cong U.ν
      ( Bφ-⋯ₛ B₁ (Bφ B₂ (U[ P ] (leafσ σ B₁ B₂))) (τ ↑* 2)
      ■ cong (Bφ B₁)
          ( Bφ-⋯ₛ B₂ (U[ P ] (leafσ σ B₁ B₂)) ((τ ↑* 2) ↑* sB₁)
          ■ cong (Bφ B₂)
              ( U-σ⋯ₛ P {σ = leafσ σ B₁ B₂} {τ = Ψ}
              ■ U-cong P leaf-eq ) ) )
  ■ sym (Uν-flat (σ ·ₖ τ) B₁ B₂ P)
  where
    sB₁ = syncs B₁
    sB₂ = syncs B₂
    Ψ : (sB₂ + (sB₁ + (2 + n))) →ₛ (sB₂ + (sB₁ + (2 + n′)))
    Ψ = ((τ ↑* 2) ↑* sB₁) ↑* sB₂
    leaf-eq : (leafσ σ B₁ B₂ ·ₖ Ψ) ≗ leafσ (σ ·ₖ τ) B₁ B₂
    leaf-eq y with Fin.splitAt (sum B₁ + sum B₂) y
    ... | inj₁ z with Fin.splitAt (sum B₁) z
    ...   | inj₁ j =
            sym (⋯-↑*-wk (canonₛ B₁ (K `unit , 0F , K `unit) j) ((τ ↑* 2) ↑* sB₁) sB₂)
          ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
              (canonₛ-natₛ B₁ (K `unit) 0F (K `unit) (τ ↑* 2) 0F refl j)
    ...   | inj₂ k =
            canonₛ-natₛ B₂ (K `unit) (weaken* ⦃ Kᵣ ⦄ sB₁ 1F) (K `unit)
              ((τ ↑* 2) ↑* sB₁) (weaken* ⦃ Kᵣ ⦄ sB₁ 1F)
              (varΘ-fixₛ sB₁ (τ ↑* 2) 1F 1F (⋯-var 0F weakenᵣ)) k
    leaf-eq y | inj₂ i =
        sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sB₁) ((τ ↑* 2) ↑* sB₁) sB₂)
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
          (sym (⋯-↑*-wk (σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2) (τ ↑* 2) sB₁))
      ■ cong (λ z → z ⋯ weaken* ⦃ Kᵣ ⦄ sB₁ ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
          (sym (⋯-↑*-wk (σ i) τ 2))

U-acq : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
      → {g : Struct m} {b₁ : ℕ} {B₁ B₂ : BindGroup}
        {E : Frame* (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
        {P : T.Proc (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
      → Γ ; g ⊢ₚ T.ν (zero ∷ suc b₁ ∷ B₁) B₂ (T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P)
      → (U[ T.ν (zero ∷ suc b₁ ∷ B₁) B₂ (T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P) ] σ
           UR─→ₚ* U[ T.ν (suc b₁ ∷ B₁) B₂ (T.⟪ E [ ` zero ]* ⟫ T.∥ P) ] σ)
        ⊎ (U[ T.ν (zero ∷ suc b₁ ∷ B₁) B₂ (T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P) ] σ
           U.≋ U[ T.ν (suc b₁ ∷ B₁) B₂ (T.⟪ E [ ` zero ]* ⟫ T.∥ P) ] σ)
U-acq {m} {n} σ Vσ Γ-S {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P} ⊢P =
  ≋-wrap-⊎ front fire back
  where
    C : BindGroup
    C = suc b₁ ∷ B₁
    QL : T.Proc (sum (zero ∷ C) + sum B₂ + m)
    QL = T.⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ T.∥ P
    QR : T.Proc (sum C + sum B₂ + m)
    QR = T.⟪ E [ ` zero ]* ⟫ T.∥ P
    -- LHS flattened leaf
    LL : U.Proc (syncs B₂ + (syncs (zero ∷ C) + (2 + n)))
    LL = U[ QL ] (leafσ σ (zero ∷ C) B₂)
    flatL : U[ T.ν (zero ∷ C) B₂ QL ] σ ≡ U.ν (Bφ (zero ∷ C) (Bφ B₂ LL))
    flatL = Uν-flat σ (zero ∷ C) B₂ QL
    eqC : syncs B₂ + suc (syncs C + suc (suc n)) ≡ syncs B₂ + (syncs C + suc (suc (suc n)))
    eqC = cong (syncs B₂ +_) (sym (+-suc (syncs C) (suc (suc n))))
    LL₃ : U.Proc (3 + (syncs B₂ + (syncs C + n)))
    LL₃ = subst U.Proc eqC LL
            U.⋯ₚ (assocSwapᵣ (syncs C) 1 ↑* syncs B₂)
            U.⋯ₚ assocSwapᵣ (syncs B₂) 1
            U.⋯ₚ ((assocSwapᵣ (syncs C) 2 ↑* syncs B₂) ↑)
            U.⋯ₚ (assocSwapᵣ (syncs B₂) 2 ↑)
    mid : U.Proc n
    mid = Bφ C (Bφ B₂ (U.ν (U.φ U.acq LL₃)))
    sC = syncs C
    sB₂ = syncs B₂
    τ : sum (zero ∷ C) + sum B₂ + m →ₛ syncs B₂ + (syncs (zero ∷ C) + (2 + n))
    τ = leafσ σ (zero ∷ C) B₂
    Vτ : VSub τ
    Vτ = ++ₛ-VSub
           (++ₛ-VSub
             (λ i → value-⋯ (VSub-canonₛ (zero ∷ C) (K `unit , 0F , K `unit) (V-K , V-K) i)
                       (weaken* ⦃ Kᵣ ⦄ sB₂) (λ _ → V-`))
             (VSub-canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (suc sC) 1F , K `unit) (V-K , V-K)))
           (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                     (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ (suc sC)) (λ _ → V-`))
                     (weaken* ⦃ Kᵣ ⦄ sB₂) (λ _ → V-`))
    -- the four post-subst renamings of LL₃, as a single term/frame/proc push.
    ρa = assocSwapᵣ sC 1 {2 + n} ↑* sB₂
    ρb = assocSwapᵣ sB₂ 1 {sC + (2 + n)}
    ρc = (assocSwapᵣ sC 2 {n} ↑* sB₂) ↑
    ρd = (assocSwapᵣ sB₂ 2 {sC + n}) ↑
    rnT : Tm (sB₂ + (suc sC + (2 + n))) → Tm (3 + (sB₂ + (sC + n)))
    rnT t = (((subst Tm eqC t ⋯ ρa) ⋯ ρb) ⋯ ρc) ⋯ ρd
    rnP : U.Proc (sB₂ + (suc sC + (2 + n))) → U.Proc (3 + (sB₂ + (sC + n)))
    rnP P = (((subst U.Proc eqC P U.⋯ₚ ρa) U.⋯ₚ ρb) U.⋯ₚ ρc) U.⋯ₚ ρd
    subst-⟪⟫ : ∀ {a b} (eq : a ≡ b) (e : Tm a) →
               subst U.Proc eq (U.⟪ e ⟫) ≡ U.⟪ subst Tm eq e ⟫
    subst-⟪⟫ refl e = refl
    subst-∥ : ∀ {a b} (eq : a ≡ b) (A B : U.Proc a) →
              subst U.Proc eq (A U.∥ B) ≡ subst U.Proc eq A U.∥ subst U.Proc eq B
    subst-∥ refl A B = refl
    rnP-⟪⟫ : (e : Tm (sB₂ + (suc sC + (2 + n)))) → rnP (U.⟪ e ⟫) ≡ U.⟪ rnT e ⟫
    rnP-⟪⟫ e = cong (λ z → (((z U.⋯ₚ ρa) U.⋯ₚ ρb) U.⋯ₚ ρc) U.⋯ₚ ρd) (subst-⟪⟫ eqC e)
    rnP-∥ : (A B : U.Proc (sB₂ + (suc sC + (2 + n)))) → rnP (A U.∥ B) ≡ rnP A U.∥ rnP B
    rnP-∥ A B = cong (λ z → (((z U.⋯ₚ ρa) U.⋯ₚ ρb) U.⋯ₚ ρc) U.⋯ₚ ρd) (subst-∥ eqC A B)
    subst-frame-plug : ∀ {a b} (eq : a ≡ b) (F : Frame* a) (t : Tm a) →
                       subst Tm eq (F [ t ]*) ≡ (subst (λ z → Frame* z) eq F) [ subst Tm eq t ]*
    subst-frame-plug refl F t = refl
    F₁ : Frame* (sB₂ + (suc sC + (2 + n)))
    F₁ = frame*-⋯ E τ Vτ
    rnF : Frame* (sB₂ + (suc sC + (2 + n))) → Frame* (3 + (sB₂ + (sC + n)))
    rnF F = ((((subst (λ z → Frame* z) eqC F ⋯ᶠ* ρa) ⋯ᶠ* ρb) ⋯ᶠ* ρc) ⋯ᶠ* ρd)
    Fout : Frame* (3 + (sB₂ + (sC + n)))
    Fout = rnF F₁
    -- rnT distributes over a frame-plug.
    rnT-plug : (F : Frame* (sB₂ + (suc sC + (2 + n)))) (t : Tm (sB₂ + (suc sC + (2 + n)))) →
               rnT (F [ t ]*) ≡ (rnF F) [ rnT t ]*
    rnT-plug F t =
        cong (λ z → (((z ⋯ ρa) ⋯ ρb) ⋯ ρc) ⋯ ρd) (subst-frame-plug eqC F t)
      ■ cong (λ z → ((z ⋯ ρb) ⋯ ρc) ⋯ ρd) (frame-plug*ᵣ (subst (λ z → Frame* z) eqC F) ρa)
      ■ cong (λ z → (z ⋯ ρc) ⋯ ρd) (frame-plug*ᵣ (subst (λ z → Frame* z) eqC F ⋯ᶠ* ρa) ρb)
      ■ cong (_⋯ ρd) (frame-plug*ᵣ ((subst (λ z → Frame* z) eqC F ⋯ᶠ* ρa) ⋯ᶠ* ρb) ρc)
      ■ frame-plug*ᵣ (((subst (λ z → Frame* z) eqC F ⋯ᶠ* ρa) ⋯ᶠ* ρb) ⋯ᶠ* ρc) ρd
    -- the consumed acq channel triple after the push: first var → 0F, junction → 1F.
    τ0F : Tm (sB₂ + (suc sC + (2 + n)))
    τ0F = τ 0F
    e₀ : sC + suc (2 + n) ≡ suc (sC + (2 + n))
    e₀ = +-suc sC (2 + n)
    -- the whole post-triple chain applied to a single subterm.
    chain : Tm (sC + suc (2 + n)) → Tm (3 + (sB₂ + (sC + n)))
    chain t = rnT (subst Tm e₀ t ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    pushVar : 𝔽 (sC + suc (2 + n)) → 𝔽 (3 + (sB₂ + (sC + n)))
    pushVar v = ρd (ρc (ρb (ρa (subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ v))))))
    subst-var : ∀ {a b} (eq : a ≡ b) (v : 𝔽 a) → subst Tm eq (` v) ≡ ` subst 𝔽 eq v
    subst-var refl v = refl
    chain-var : (v : 𝔽 (sC + suc (2 + n))) → chain (` v) ≡ ` pushVar v
    chain-var v =
        cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd) (subst-var e₀ v)
      ■ cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
          (subst-var eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ v)))
    subst-⊗ : ∀ {a b} (eq : a ≡ b) (A B C : Tm a) →
              subst Tm eq ((A ⊗ B) ⊗ C) ≡ (subst Tm eq A ⊗ subst Tm eq B) ⊗ subst Tm eq C
    subst-⊗ refl A B C = refl
    chain-⊗ : (A B C : Tm (sC + suc (2 + n))) →
              chain ((A ⊗ B) ⊗ C) ≡ (chain A ⊗ chain B) ⊗ chain C
    chain-⊗ A B C =
        cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
          (subst-⊗ e₀ A B C)
      ■ cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
          (subst-⊗ eqC (subst Tm e₀ A ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                       (subst Tm e₀ B ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                       (subst Tm e₀ C ⋯ weaken* ⦃ Kᵣ ⦄ sB₂))
    trC = canonₛ-acq-head {suc n} b₁ B₁ (K `unit)
    va = proj₁ trC
    vj = proj₁ (proj₂ trC)
    tcc = proj₁ (proj₂ (proj₂ trC))
    canC≡ : canonₛ C (` 0F , 1F , K `unit) 0F ≡ ((` va) ⊗ (` vj)) ⊗ tcc
    canC≡ = proj₁ (proj₂ (proj₂ (proj₂ trC)))
    τ0F≡ : τ0F ≡ subst Tm e₀ (((` va) ⊗ (` vj)) ⊗ tcc) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    τ0F≡ = cong (λ z → subst Tm e₀ z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) canC≡
    rnTriple : rnT τ0F ≡ ((` pushVar va) ⊗ (` pushVar vj)) ⊗ chain tcc
    rnTriple = cong rnT τ0F≡ ■ chain-⊗ (` va) (` vj) tcc
             ■ cong₂ (λ p q → (p ⊗ q) ⊗ chain tcc) (chain-var va) (chain-var vj)
    junc-tr : Σ[ c ∈ Tm (3 + (sB₂ + (sC + n))) ]
              (rnT τ0F ≡ ((` 0F) ⊗ (` 1F)) ⊗ c)
    junc-tr = chain tcc ,
              (rnTriple ■ cong (λ p → (((` p)) ⊗ (` pushVar vj)) ⊗ chain tcc) pushVar-va
                       ■ cong (λ q → (((` 0F)) ⊗ (` q)) ⊗ chain tcc) pushVar-vj)
      where
        toℕva : Fin.toℕ va ≡ sC
        toℕva = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ trC)))) ■ +-identityʳ sC
        toℕvj : Fin.toℕ vj ≡ sC + 1
        toℕvj = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ trC))))
        -- shared prefix: subst e₀ ; weaken* sB₂ ; subst eqC ; raise toℕ to sB₂ + toℕ v.
        pre : (v : 𝔽 (sC + suc (2 + n))) →
              Fin.toℕ (subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ v))) ≡ sB₂ + Fin.toℕ v
        pre v = toℕ-subst𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ v))
              ■ toℕ-weaken*ᵣ sB₂ (subst 𝔽 e₀ v)
              ■ cong (sB₂ +_) (toℕ-subst𝔽 e₀ v)
        w2a = subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ va))
        toℕw2a : Fin.toℕ w2a ≡ sB₂ + sC
        toℕw2a = pre va ■ cong (sB₂ +_) toℕva
        -- ρa lands va's endpoint at sB₂.
        qa : sB₂ Nat.≤ Fin.toℕ w2a
        qa = subst (sB₂ Nat.≤_) (sym toℕw2a) (Nat.m≤m+n sB₂ sC)
        ρaw2a : Fin.toℕ (ρa w2a) ≡ sB₂
        ρaw2a = toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ w2a qa
              ■ cong (sB₂ +_)
                  ( toℕ-assoc-mid sC 1 (Fin.reduce≥ w2a qa)
                      (Nat.≤-reflexive (sym redc))
                      (subst (Nat._< sC + 1) (sym redc) (subst (sC Nat.<_) (Nat.+-comm 1 sC) (Nat.n<1+n sC)))
                  ■ cong (Nat._∸ sC) redc ■ Nat.n∸n≡0 sC )
              ■ Nat.+-identityʳ sB₂
          where redc : Fin.toℕ (Fin.reduce≥ w2a qa) ≡ sC
                redc = toℕ-reduce≥ w2a qa ■ cong (Nat._∸ sB₂) toℕw2a ■ Nat.m+n∸m≡n sB₂ sC
        wb-va : ρb (ρa w2a) ≡ 0F
        wb-va = Fin.toℕ-injective
          ( toℕ-assoc-mid sB₂ 1 (ρa w2a)
              (Nat.≤-reflexive (sym ρaw2a))
              (subst (Nat._< sB₂ + 1) (sym ρaw2a) (subst (sB₂ Nat.<_) (Nat.+-comm 1 sB₂) (Nat.n<1+n sB₂)))
          ■ cong (Nat._∸ sB₂) ρaw2a ■ Nat.n∸n≡0 sB₂ )
        pushVar-va : pushVar va ≡ 0F
        pushVar-va = cong (λ z → ρd (ρc z)) wb-va
        w2v = subst 𝔽 eqC (weaken* ⦃ Kᵣ ⦄ sB₂ (subst 𝔽 e₀ vj))
        toℕw2v : Fin.toℕ w2v ≡ sB₂ + (sC + 1)
        toℕw2v = pre vj ■ cong (sB₂ +_) toℕvj
        qav : sB₂ Nat.≤ Fin.toℕ w2v
        qav = subst (sB₂ Nat.≤_) (sym toℕw2v) (Nat.m≤m+n sB₂ (sC + 1))
        redcv : Fin.toℕ (Fin.reduce≥ w2v qav) ≡ sC + 1
        redcv = toℕ-reduce≥ w2v qav ■ cong (Nat._∸ sB₂) toℕw2v ■ Nat.m+n∸m≡n sB₂ (sC + 1)
        ρavj : Fin.toℕ (ρa w2v) ≡ sB₂ + (sC + 1)
        ρavj = toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ w2v qav
             ■ cong (sB₂ +_)
                 ( toℕ-assoc-ge sC 1 (Fin.reduce≥ w2v qav)
                     (subst (sC + 1 Nat.≤_) (sym redcv) Nat.≤-refl)
                 ■ redcv )
        ρbvj : Fin.toℕ (ρb (ρa w2v)) ≡ sB₂ + (sC + 1)
        ρbvj = toℕ-assoc-ge sB₂ 1 (ρa w2v)
                 (subst (sB₂ + 1 Nat.≤_) (sym ρavj)
                   (Nat.+-monoʳ-≤ sB₂ (subst (1 Nat.≤_) (Nat.+-comm 1 sC) (Nat.s≤s Nat.z≤n))))
             ■ ρavj
        qcv : 1 Nat.≤ Fin.toℕ (ρb (ρa w2v))
        qcv = subst (1 Nat.≤_) (sym ρbvj)
                (subst (1 Nat.≤_) (Nat.+-assoc sB₂ sC 1) (Nat.m≤n+m 1 (sB₂ + sC)))
        ρcvj : Fin.toℕ (ρc (ρb (ρa w2v))) ≡ 1 + sB₂
        ρcvj = toℕ-↑*-ge (assocSwapᵣ sC 2 ↑* sB₂) 1 (ρb (ρa w2v)) qcv
             ■ cong (1 +_) inner
          where
            redc1 : Fin.toℕ (Fin.reduce≥ (ρb (ρa w2v)) qcv) ≡ sB₂ + sC
            redc1 = toℕ-reduce≥ (ρb (ρa w2v)) qcv ■ cong (Nat._∸ 1) ρbvj ■ eqarith
              where eqarith : (sB₂ + (sC + 1)) Nat.∸ 1 ≡ sB₂ + sC
                    eqarith = cong (Nat._∸ 1) (sym (Nat.+-assoc sB₂ sC 1))
                            ■ Nat.m+n∸n≡m (sB₂ + sC) 1
            qin : sB₂ Nat.≤ Fin.toℕ (Fin.reduce≥ (ρb (ρa w2v)) qcv)
            qin = subst (sB₂ Nat.≤_) (sym redc1) (Nat.m≤m+n sB₂ sC)
            redin : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ (ρb (ρa w2v)) qcv) qin) ≡ sC
            redin = toℕ-reduce≥ (Fin.reduce≥ (ρb (ρa w2v)) qcv) qin
                  ■ cong (Nat._∸ sB₂) redc1 ■ Nat.m+n∸m≡n sB₂ sC
            inner : Fin.toℕ ((assocSwapᵣ sC 2 ↑* sB₂) (Fin.reduce≥ (ρb (ρa w2v)) qcv)) ≡ sB₂
            inner = toℕ-↑*-ge (assocSwapᵣ sC 2) sB₂ (Fin.reduce≥ (ρb (ρa w2v)) qcv) qin
                  ■ cong (sB₂ +_)
                      ( toℕ-assoc-mid sC 2 (Fin.reduce≥ (Fin.reduce≥ (ρb (ρa w2v)) qcv) qin)
                          (Nat.≤-reflexive (sym redin))
                          (subst (Nat._< sC + 2) (sym redin) (Nat.m<m+n sC (Nat.s≤s Nat.z≤n)))
                      ■ cong (Nat._∸ sC) redin ■ Nat.n∸n≡0 sC )
                  ■ Nat.+-identityʳ sB₂
        pushVar-vj : pushVar vj ≡ 1F
        pushVar-vj = Fin.toℕ-injective
          ( toℕ-↑*-ge (assocSwapᵣ sB₂ 2) 1 (ρc (ρb (ρa w2v))) qdv
          ■ cong (1 +_) innerd )
          where
            qdv : 1 Nat.≤ Fin.toℕ (ρc (ρb (ρa w2v)))
            qdv = subst (1 Nat.≤_) (sym ρcvj) (Nat.s≤s Nat.z≤n)
            redd : Fin.toℕ (Fin.reduce≥ (ρc (ρb (ρa w2v))) qdv) ≡ sB₂
            redd = toℕ-reduce≥ (ρc (ρb (ρa w2v))) qdv ■ cong (Nat._∸ 1) ρcvj ■ Nat.m+n∸m≡n 1 sB₂
            innerd : Fin.toℕ (assocSwapᵣ sB₂ 2 (Fin.reduce≥ (ρc (ρb (ρa w2v))) qdv)) ≡ 0
            innerd = toℕ-assoc-mid sB₂ 2 (Fin.reduce≥ (ρc (ρb (ρa w2v))) qdv)
                       (Nat.≤-reflexive (sym redd))
                       (subst (Nat._< sB₂ + 2) (sym redd) (Nat.m<m+n sB₂ (Nat.s≤s Nat.z≤n)))
                   ■ cong (Nat._∸ sB₂) redd ■ Nat.n∸n≡0 sB₂
    eout : Tm (3 + (sB₂ + (sC + n)))
    eout = proj₁ junc-tr
    Qout : U.Proc (3 + (sB₂ + (sC + n)))
    Qout = rnP (U[ P ] τ)
    threadEq : LL ≡ U.⟪ F₁ [ K `acq ·¹ τ0F ]* ⟫ U.∥ U[ P ] τ
    threadEq = cong (U._∥ U[ P ] τ) (cong U.⟪_⟫ (frame-plug* E τ Vτ))
    subst-app : ∀ {a b} (eq : a ≡ b) (d : Dir) (f t : Tm a) →
                subst Tm eq (f ·⟨ d ⟩ t) ≡ subst Tm eq f ·⟨ d ⟩ subst Tm eq t
    subst-app refl d f t = refl
    subst-K : ∀ {a b} (eq : a ≡ b) (c : _) → subst Tm eq (K c) ≡ K c
    subst-K refl c = refl
    rnT-Kacq· : (t : Tm (sB₂ + (suc sC + (2 + n)))) → rnT (K `acq ·¹ t) ≡ K `acq ·¹ rnT t
    rnT-Kacq· t =
        cong (λ z → (((z ⋯ ρa) ⋯ ρb) ⋯ ρc) ⋯ ρd) (subst-app eqC 𝟙 (K `acq) t)
      ■ cong (λ z → (((z ·¹ subst Tm eqC t ⋯ ρa) ⋯ ρb) ⋯ ρc) ⋯ ρd) (subst-K eqC `acq)
    rnT-acq : rnT (K `acq ·¹ τ0F) ≡ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ eout)
    rnT-acq = rnT-Kacq· τ0F ■ cong (λ z → K `acq ·¹ z) (proj₂ junc-tr)
    redexL : LL₃ ≡ U.⟪ Fout [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ eout) ]* ⟫ U.∥ Qout
    redexL =
        cong rnP threadEq
      ■ rnP-∥ (U.⟪ F₁ [ K `acq ·¹ τ0F ]* ⟫) (U[ P ] τ)
      ■ cong (U._∥ Qout)
          ( rnP-⟪⟫ (F₁ [ K `acq ·¹ τ0F ]*)
          ■ cong U.⟪_⟫ (rnT-plug F₁ (K `acq ·¹ τ0F) ■ cong (Fout [_]*) rnT-acq) )
    fired : U.Proc n
    fired = Bφ C (Bφ B₂ (U.ν ((U.⟪ Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ⟫ U.∥ Qout) U.⋯ₚ ⦅ * ⦆ₛ)))
    front : U[ T.ν (zero ∷ C) B₂ QL ] σ U.≋ mid
    front = ≡→≋ flatL
      ◅◅ U.ν-cong (φ-past-Bφ C U.acq (subst U.Proc (sym (+-suc (syncs C) (suc (suc n)))) (Bφ B₂ LL)))
      ◅◅ U.ν-cong (Bφ-cong C (U.φ-cong (≡→≋
           ( cong (U._⋯ₚ assocSwapᵣ (syncs C) 1)
               (subst-Bφ (sym (+-suc (syncs C) (suc (suc n)))) B₂ LL)
           ■ Bφ-⋯ B₂ (subst U.Proc eqC LL) (assocSwapᵣ (syncs C) 1) ))))
      ◅◅ U.ν-cong (Bφ-cong C (φ-past-Bφ B₂ U.acq
           (subst U.Proc eqC LL U.⋯ₚ (assocSwapᵣ (syncs C) 1 ↑* syncs B₂))))
      ◅◅ ν-past-Bφ C (Bφ B₂ (U.φ U.acq
           (subst U.Proc eqC LL U.⋯ₚ (assocSwapᵣ (syncs C) 1 ↑* syncs B₂) U.⋯ₚ assocSwapᵣ (syncs B₂) 1)))
      ◅◅ Bφ-cong C (U.ν-cong (≡→≋ (Bφ-⋯ B₂
           (U.φ U.acq (subst U.Proc eqC LL U.⋯ₚ (assocSwapᵣ (syncs C) 1 ↑* syncs B₂) U.⋯ₚ assocSwapᵣ (syncs B₂) 1))
           (assocSwapᵣ (syncs C) 2))))
      ◅◅ Bφ-cong C (ν-past-Bφ B₂
           (U.φ U.acq (subst U.Proc eqC LL U.⋯ₚ (assocSwapᵣ (syncs C) 1 ↑* syncs B₂) U.⋯ₚ assocSwapᵣ (syncs B₂) 1)
              U.⋯ₚ (assocSwapᵣ (syncs C) 2 ↑* syncs B₂)))
    fire : mid UR─→ₚ* fired
    fire = Bφ-fire C (Bφ-fire B₂
             (subst (λ z → U.ν (U.φ U.acq z) UR─→ₚ*
                       U.ν ((U.⟪ Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ⟫ U.∥ Qout) U.⋯ₚ ⦅ * ⦆ₛ))
                    (sym redexL)
                    (leaf-fire Fout {e = eout} Qout)))
    leaf′ : U.Proc (2 + (sB₂ + (sC + n)))
    leaf′ = (U.⟪ Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ⟫ U.∥ Qout) U.⋯ₚ ⦅ * ⦆ₛ
    -- acq-confine factors E and P so they avoid the consumed handle 0F.
    confine = acq-confine Γ-S ⊢P
    kk : ℕ
    kk = proj₁ confine
    ρ⁻ : kk →ᵣ (sum (zero ∷ C) + sum B₂ + m)
    ρ⁻ = proj₁ (proj₂ confine)
    ρ⁻≢0 : ∀ y → ρ⁻ y ≢ 0F
    ρ⁻≢0 = proj₁ (proj₂ (proj₂ confine))
    E₀ : Frame* kk
    E₀ = proj₁ (proj₂ (proj₂ (proj₂ confine)))
    E≡ : E ≡ E₀ ⋯ᶠ* ρ⁻
    E≡ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ confine))))
    P₀ : T.Proc kk
    P₀ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ confine)))))
    P≡ : P ≡ P₀ T.⋯ₚ ρ⁻
    P≡ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ confine)))))

    -- canonₛ with a zero head: splitAt 0 is always inj₂, so canonₛ (zero ∷ C)
    -- reduces to a subst of canonₛ C with bumped middle.
    canonₛ-zero-head : ∀ {N} (e1 e2 : Tm N) (x : 𝔽 N) (y : 𝔽 (sum C)) →
      canonₛ (zero ∷ C) (e1 , x , e2) y
      ≡ subst Tm (+-suc (syncs C) N) (canonₛ C (` 0F , suc x , e2 ⋯ weakenᵣ) y)
    canonₛ-zero-head e1 e2 x y = refl

    -- subst on U.Proc codomain pushes into the translation's substitution.
    subst-U-cod : ∀ {a c} (eq : a ≡ c) (s : (sum (zero ∷ C) + sum B₂ + m) →ₛ a) →
                  subst U.Proc eq (U[ P ] s)
                  ≡ U[ P ] (subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eq s)
    subst-U-cod refl s = refl
    subst-cod-ptR : ∀ {a c} (eq : a ≡ c) (s : (sum (zero ∷ C) + sum B₂ + m) →ₛ a) (i : _) →
                    subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eq s i ≡ subst Tm eq (s i)
    subst-cod-ptR refl s i = refl

    -- Qout collapses every renaming into the codomain substitution of U[ P ].
    sPre : (sum (zero ∷ C) + sum B₂ + m) →ₛ 3 + (sB₂ + (sC + n))
    sPre = ((((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ) ·ₖ ρa) ·ₖ ρb) ·ₖ ρc) ·ₖ ρd
    Qout≡ : Qout ≡ U[ P ] sPre
    Qout≡ =
        cong (λ z → (((z U.⋯ₚ ρa) U.⋯ₚ ρb) U.⋯ₚ ρc) U.⋯ₚ ρd) (subst-U-cod eqC τ)
      ■ cong (λ z → ((z U.⋯ₚ ρb) U.⋯ₚ ρc) U.⋯ₚ ρd)
          (U-σ⋯ P {σ = subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ} {ρ = ρa})
      ■ cong (λ z → (z U.⋯ₚ ρc) U.⋯ₚ ρd)
          (U-σ⋯ P {σ = subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ ·ₖ ρa} {ρ = ρb})
      ■ cong (λ z → z U.⋯ₚ ρd)
          (U-σ⋯ P {σ = (subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ ·ₖ ρa) ·ₖ ρb} {ρ = ρc})
      ■ U-σ⋯ P {σ = ((subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ ·ₖ ρa) ·ₖ ρb) ·ₖ ρc} {ρ = ρd}

    A₂ : (2 + (sB₂ + (sC + n))) →ᵣ (sB₂ + (2 + (sC + n)))
    A₂ = assocSwapᵣ 2 sB₂
    B₂ᵣ : (sB₂ + (2 + (sC + n))) →ᵣ (sB₂ + (sC + (2 + n)))
    B₂ᵣ = assocSwapᵣ 2 sC ↑* sB₂
    sPre⁻ : kk →ₛ 3 + (sB₂ + (sC + n))
    sPre⁻ = ρ⁻ ·ₖ sPre
    QoutP₀ : Qout ≡ U[ P₀ ] sPre⁻
    QoutP₀ = Qout≡ ■ cong (λ z → U[ z ] sPre) P≡ ■ U-⋯ₚ P₀ {ρ = ρ⁻} {σ = sPre}
    -- s₀ : sPre⁻ with the cleanup substitution applied to its image (the lowering).
    s₀ : kk →ₛ 2 + (sB₂ + (sC + n))
    s₀ y = sPre⁻ y ⋯ ⦅ * ⦆ₛ
    -- MASTER: for an index w avoiding the consumed handle 0F, sPre w is the
    -- weakening of a term t whose A₂;B₂ᵣ-image is leafσ σ C B₂ w.
    -- sPre w spelled out (collapse the ·ₖ composite pointwise).
    sPre-pt : (w : 𝔽 (sum C + sum B₂ + m)) →
              sPre w ≡ subst Tm eqC (τ w) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd
    sPre-pt w = cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
                  (subst-cod-ptR eqC τ w)
    TowerGoal : (w : 𝔽 (sum C + sum B₂ + m)) → Set
    TowerGoal w = sPre w ⋯ ⦅ * ⦆ₛ ⋯ A₂ ⋯ B₂ᵣ ≡ leafσ σ C B₂ w
    -- branches whose leaf does not mention the consumed handle 0F factor
    -- sPre w = t ⋯ weakenᵣ (a pure weakening), so ⦅*⦆ₛ cancels the weakening.
    fromWk : (w : 𝔽 (sum C + sum B₂ + m)) {L : Tm (sB₂ + (sC + (2 + n)))}
             (t : Tm (2 + (sB₂ + (sC + n)))) →
             sPre w ≡ t ⋯ weakenᵣ → t ⋯ A₂ ⋯ B₂ᵣ ≡ L →
             sPre w ⋯ ⦅ * ⦆ₛ ⋯ A₂ ⋯ B₂ᵣ ≡ L
    fromWk w t wkfact leaffact =
        cong (λ z → z ⋯ ⦅ * ⦆ₛ ⋯ A₂ ⋯ B₂ᵣ) wkfact
      ■ cong (λ z → z ⋯ A₂ ⋯ B₂ᵣ) (wk-cancels-⦅⦆-⋯ t *)
      ■ leaffact
    towerNF : (w : 𝔽 (sum C + sum B₂ + m)) → w ≢ 0F → TowerGoal w
    towerNF w w≢0 with Fin.splitAt (sum C + sum B₂) w in eqw
    ... | inj₂ i = fromWk w tailNF tailWk tailLeaf
      where
        tailNF : Tm (2 + (sB₂ + (sC + n)))
        tailNF = σ i ⋯ weaken* ⦃ Kᵣ ⦄ sC ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ weaken* ⦃ Kᵣ ⦄ 2
        -- τ w in the tail region.
        τtail : τ w ≡ σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (suc sC) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        τtail = leafσ-tail σ (zero ∷ C) B₂ w i eqw
        ρa⁻ = subst (λ z → z →ᵣ (sB₂ + suc (sC + (2 + n)))) (sym eqC) ρa
        -- push the subst eqC into ρa.
        substPush : subst Tm eqC (τ w) ⋯ ρa ≡ τ w ⋯ ρa⁻
        substPush = subst-⋯-dom-local eqC (τ w) ρa
        -- tailWk reconcile: σ i pushed through the post-substitution chain
        -- equals tailNF ⋯ weakenᵣ, as a pure renaming identity on σ i.
        wsC1 : n →ᵣ (suc sC + n)
        wsC1 = weaken* ⦃ Kᵣ ⦄ (suc sC)
        w2 : n →ᵣ (2 + n)
        w2 = weaken* ⦃ Kᵣ ⦄ 2
        wB : (2 + n) →ᵣ (sB₂ + (2 + n))
        wB = weaken* ⦃ Kᵣ ⦄ sB₂
        LHScomp : n →ᵣ (3 + (sB₂ + (sC + n)))
        LHScomp = ((((( w2 ·ₖ (weaken* ⦃ Kᵣ ⦄ (suc sC))) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ ρa⁻) ·ₖ ρb) ·ₖ ρc) ·ₖ ρd
        RHScomp : n →ᵣ (3 + (sB₂ + (sC + n)))
        RHScomp = (((weaken* ⦃ Kᵣ ⦄ sC ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) ·ₖ weakenᵣ)
        fuseTL : σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (suc sC) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρa⁻ ⋯ ρb ⋯ ρc ⋯ ρd
                 ≡ σ i ⋯ LHScomp
        fuseTL =
            cong (λ z → z ⋯ ρa⁻ ⋯ ρb ⋯ ρc ⋯ ρd)
              ( cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (fusion (σ i) w2 (weaken* ⦃ Kᵣ ⦄ (suc sC)))
              ■ fusion (σ i) (w2 ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sC)) (weaken* ⦃ Kᵣ ⦄ sB₂) )
          ■ cong (λ z → z ⋯ ρb ⋯ ρc ⋯ ρd) (fusion (σ i) ((w2 ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sC)) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ρa⁻)
          ■ cong (λ z → z ⋯ ρc ⋯ ρd) (fusion (σ i) (((w2 ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sC)) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ ρa⁻) ρb)
          ■ cong (_⋯ ρd) (fusion (σ i) ((((w2 ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sC)) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ ρa⁻) ·ₖ ρb) ρc)
          ■ fusion (σ i) (((((w2 ·ₖ weaken* ⦃ Kᵣ ⦄ (suc sC)) ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ ρa⁻) ·ₖ ρb) ·ₖ ρc) ρd
        fuseTR : tailNF ⋯ weakenᵣ ≡ σ i ⋯ RHScomp
        fuseTR =
            cong (_⋯ weakenᵣ)
              ( cong (_⋯ weaken* ⦃ Kᵣ ⦄ 2) (fusion (σ i) (weaken* ⦃ Kᵣ ⦄ sC) (weaken* ⦃ Kᵣ ⦄ sB₂))
              ■ fusion (σ i) (weaken* ⦃ Kᵣ ⦄ sC ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) (weaken* ⦃ Kᵣ ⦄ 2) )
          ■ fusion (σ i) ((weaken* ⦃ Kᵣ ⦄ sC ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) ·ₖ weaken* ⦃ Kᵣ ⦄ 2) weakenᵣ
        tailWkRen : LHScomp ≗ RHScomp
        tailWkRen v = Fin.toℕ-injective (lhsT ■ sym rhsT)
          where
            pv = Fin.toℕ v
            rhsT : Fin.toℕ (RHScomp v) ≡ 3 + (sB₂ + (sC + pv))
            rhsT = toℕ-weaken*ᵣ 1 (weaken* ⦃ Kᵣ ⦄ 2 (weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC v)))
                 ■ cong (1 +_) (toℕ-weaken*ᵣ 2 (weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ sC v))
                              ■ cong (2 +_) (toℕ-weaken*ᵣ sB₂ (weaken* ⦃ Kᵣ ⦄ sC v)
                                           ■ cong (sB₂ +_) (toℕ-weaken*ᵣ sC v)))
            -- the weakened tail value before the swaps
            wv : 𝔽 (sB₂ + (suc sC + (2 + n)))
            wv = weaken* ⦃ Kᵣ ⦄ sB₂ (weaken* ⦃ Kᵣ ⦄ (suc sC) (weaken* ⦃ Kᵣ ⦄ 2 v))
            wvℕ : Fin.toℕ wv ≡ sB₂ + (suc sC + (2 + pv))
            wvℕ = toℕ-weaken*ᵣ sB₂ (weaken* ⦃ Kᵣ ⦄ (suc sC) (weaken* ⦃ Kᵣ ⦄ 2 v))
                ■ cong (sB₂ +_) (toℕ-weaken*ᵣ (suc sC) (weaken* ⦃ Kᵣ ⦄ 2 v)
                               ■ cong (suc sC +_) (toℕ-weaken*ᵣ 2 v))
            -- ρa⁻ wv = ρa (subst 𝔽 eqC wv); toℕ preserved.
            wv′ : 𝔽 (sB₂ + (syncs C + suc (suc (suc n))))
            wv′ = subst 𝔽 eqC wv
            wv′ℕ : Fin.toℕ wv′ ≡ sB₂ + (suc sC + (2 + pv))
            wv′ℕ = toℕ-subst𝔽 eqC wv ■ wvℕ
            ρa⁻ℕ : Fin.toℕ (ρa⁻ wv) ≡ sB₂ + (suc sC + (2 + pv))
            ρa⁻ℕ = cong Fin.toℕ (apply-subst-ren eqC ρa wv)
                 ■ aℕ
              where
                geAa : sB₂ Nat.≤ Fin.toℕ wv′
                geAa = subst (sB₂ Nat.≤_) (sym wv′ℕ) (Nat.m≤m+n sB₂ (suc sC + (2 + pv)))
                redAa : Fin.toℕ (Fin.reduce≥ wv′ geAa) ≡ suc sC + (2 + pv)
                redAa = toℕ-reduce≥ wv′ geAa ■ cong (Nat._∸ sB₂) wv′ℕ ■ Nat.m+n∸m≡n sB₂ (suc sC + (2 + pv))
                geAa2 : sC + 1 Nat.≤ Fin.toℕ (Fin.reduce≥ wv′ geAa)
                geAa2 = subst (sC + 1 Nat.≤_) (sym redAa)
                          (subst (Nat._≤ suc sC + (2 + pv)) (Nat.+-comm 1 sC)
                            (Nat.s≤s (Nat.m≤m+n sC (2 + pv))))
                aℕ : Fin.toℕ (ρa wv′) ≡ sB₂ + (suc sC + (2 + pv))
                aℕ = toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ wv′ geAa
                   ■ cong (sB₂ +_) (toℕ-assoc-ge sC 1 (Fin.reduce≥ wv′ geAa) geAa2 ■ redAa)
            -- ρb preserves (sB₂-block ge); value ≥ sB₂.
            ρbℕ : Fin.toℕ (ρb (ρa⁻ wv)) ≡ sB₂ + (suc sC + (2 + pv))
            ρbℕ = toℕ-assoc-ge sB₂ 1 (ρa⁻ wv) geB ■ ρa⁻ℕ
              where geB : sB₂ + 1 Nat.≤ Fin.toℕ (ρa⁻ wv)
                    geB = subst (sB₂ + 1 Nat.≤_) (sym ρa⁻ℕ)
                            (Nat.+-monoʳ-≤ sB₂ (subst (Nat._≤ suc sC + (2 + pv)) refl
                              (Nat.s≤s Nat.z≤n)))
            -- ρc = (assocSwapᵣ sC 2 ↑* sB₂) ↑ ; value (suc) preserved.
            ρcℕ : Fin.toℕ (ρc (ρb (ρa⁻ wv))) ≡ sB₂ + (suc sC + (2 + pv))
            ρcℕ = toℕ-↑ (assocSwapᵣ sC 2 ↑* sB₂) (ρb (ρa⁻ wv))
                ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ ((assocSwapᵣ sC 2 ↑* sB₂) j))) ]′
                       (Fin.splitAt-≥ 1 (ρb (ρa⁻ wv)) geC1)
                ■ cong suc innerC
                ■ sym (Nat.+-suc sB₂ (sC + (2 + pv)))
              where
                geC1 : 1 Nat.≤ Fin.toℕ (ρb (ρa⁻ wv))
                geC1 = subst (1 Nat.≤_) (sym ρbℕ) (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.m≤n+m (suc sC + (2 + pv)) sB₂))
                redC1 : Fin.toℕ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) ≡ sB₂ + (sC + (2 + pv))
                redC1 = toℕ-reduce≥ (ρb (ρa⁻ wv)) geC1 ■ cong (Nat._∸ 1) (ρbℕ ■ Nat.+-suc sB₂ (sC + (2 + pv)))
                geC2 : sB₂ Nat.≤ Fin.toℕ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1)
                geC2 = subst (sB₂ Nat.≤_) (sym redC1) (Nat.m≤m+n sB₂ (sC + (2 + pv)))
                redC3 : Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) geC2) ≡ sC + (2 + pv)
                redC3 = toℕ-reduce≥ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) geC2 ■ cong (Nat._∸ sB₂) redC1 ■ Nat.m+n∸m≡n sB₂ (sC + (2 + pv))
                geC4 : sC + 2 Nat.≤ Fin.toℕ (Fin.reduce≥ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) geC2)
                geC4 = subst (sC + 2 Nat.≤_) (sym redC3)
                         (Nat.+-monoʳ-≤ sC (Nat.m≤m+n 2 pv))
                innerC : Fin.toℕ ((assocSwapᵣ sC 2 ↑* sB₂) (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1)) ≡ sB₂ + (sC + (2 + pv))
                innerC = toℕ-↑*-ge (assocSwapᵣ sC 2) sB₂ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) geC2
                       ■ cong (sB₂ +_) (toℕ-assoc-ge sC 2 (Fin.reduce≥ (Fin.reduce≥ (ρb (ρa⁻ wv)) geC1) geC2) geC4 ■ redC3)
            -- ρd = assocSwapᵣ sB₂ 2 ↑ ; value (suc) preserved.
            lhsT : Fin.toℕ (LHScomp v) ≡ 3 + (sB₂ + (sC + pv))
            lhsT = toℕ-↑ (assocSwapᵣ sB₂ 2) (ρc (ρb (ρa⁻ wv)))
                 ■ cong [ (λ _ → 0) , (λ j → suc (Fin.toℕ (assocSwapᵣ sB₂ 2 j))) ]′
                        (Fin.splitAt-≥ 1 (ρc (ρb (ρa⁻ wv))) geD1)
                 ■ cong suc (innerD ■ bridgeLD)
              where
                bridgeLD : sB₂ + (sC + (2 + pv)) ≡ 2 + (sB₂ + (sC + pv))
                bridgeLD = cong (sB₂ +_) (Nat.+-suc sC (suc pv) ■ cong suc (Nat.+-suc sC pv))
                         ■ Nat.+-suc sB₂ (suc (sC + pv)) ■ cong suc (Nat.+-suc sB₂ (sC + pv))
                geD1 : 1 Nat.≤ Fin.toℕ (ρc (ρb (ρa⁻ wv)))
                geD1 = subst (1 Nat.≤_) (sym ρcℕ) (Nat.≤-trans (Nat.s≤s Nat.z≤n) (Nat.m≤n+m (suc sC + (2 + pv)) sB₂))
                redD1 : Fin.toℕ (Fin.reduce≥ (ρc (ρb (ρa⁻ wv))) geD1) ≡ sB₂ + (sC + (2 + pv))
                redD1 = toℕ-reduce≥ (ρc (ρb (ρa⁻ wv))) geD1 ■ cong (Nat._∸ 1) (ρcℕ ■ Nat.+-suc sB₂ (sC + (2 + pv)))
                geD2 : sB₂ + 2 Nat.≤ Fin.toℕ (Fin.reduce≥ (ρc (ρb (ρa⁻ wv))) geD1)
                geD2 = subst (sB₂ + 2 Nat.≤_) (sym redD1)
                         (Nat.+-monoʳ-≤ sB₂ (Nat.≤-trans (Nat.m≤m+n 2 pv) (Nat.m≤n+m (2 + pv) sC)))
                innerD : Fin.toℕ (assocSwapᵣ sB₂ 2 (Fin.reduce≥ (ρc (ρb (ρa⁻ wv))) geD1)) ≡ sB₂ + (sC + (2 + pv))
                innerD = toℕ-assoc-ge sB₂ 2 (Fin.reduce≥ (ρc (ρb (ρa⁻ wv))) geD1) geD2 ■ redD1
        tailWk-fuse : σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (suc sC) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρa⁻ ⋯ ρb ⋯ ρc ⋯ ρd
                      ≡ tailNF ⋯ weakenᵣ
        tailWk-fuse = fuseTL ■ ⋯-cong (σ i) tailWkRen ■ sym fuseTR
        tailWk : sPre w ≡ tailNF ⋯ weakenᵣ
        tailWk =
            sPre-pt w
          ■ cong (λ z → z ⋯ ρb ⋯ ρc ⋯ ρd) substPush
          ■ cong (λ z → z ⋯ ρa⁻ ⋯ ρb ⋯ ρc ⋯ ρd) τtail
          ■ tailWk-fuse
        -- tail value passes through every map as a left-weakening; compare toℕ.
        -- LHS weakenings (grouping sC ; sB₂ ; 2)
        lC : n →ᵣ (sC + n)
        lC = weaken* ⦃ Kᵣ ⦄ sC
        lB : (sC + n) →ᵣ (sB₂ + (sC + n))
        lB = weaken* ⦃ Kᵣ ⦄ sB₂
        l2 : (sB₂ + (sC + n)) →ᵣ (2 + (sB₂ + (sC + n)))
        l2 = weaken* ⦃ Kᵣ ⦄ 2
        -- RHS weakenings (grouping 2 ; sC ; sB₂)
        r2 : n →ᵣ (2 + n)
        r2 = weaken* ⦃ Kᵣ ⦄ 2
        rC : (2 + n) →ᵣ (sC + (2 + n))
        rC = weaken* ⦃ Kᵣ ⦄ sC
        rB : (sC + (2 + n)) →ᵣ (sB₂ + (sC + (2 + n)))
        rB = weaken* ⦃ Kᵣ ⦄ sB₂
        tailRen : ((((lC ·ₖ lB) ·ₖ l2) ·ₖ A₂) ·ₖ B₂ᵣ) ≗ ((r2 ·ₖ rC) ·ₖ rB)
        tailRen v = Fin.toℕ-injective (lhs ■ sym rhs)
          where
            pv = Fin.toℕ v
            -- toℕ of the weakened value before the assocSwaps
            wA = l2 (lB (lC v))
            wAℕ : Fin.toℕ wA ≡ 2 + (sB₂ + (sC + pv))
            wAℕ = toℕ-weaken*ᵣ 2 (lB (lC v))
                ■ cong (2 +_) (toℕ-weaken*ᵣ sB₂ (lC v)
                              ■ cong (sB₂ +_) (toℕ-weaken*ᵣ sC v))
            -- A₂ preserves toℕ (input ≥ 2 + sB₂).
            geA : 2 + sB₂ Nat.≤ Fin.toℕ wA
            geA = subst (2 + sB₂ Nat.≤_) (sym wAℕ) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sB₂ (sC + pv)))
            A₂ℕ : Fin.toℕ (A₂ wA) ≡ 2 + (sB₂ + (sC + pv))
            A₂ℕ = toℕ-assoc-ge 2 sB₂ wA geA ■ wAℕ
            -- B₂ᵣ at A₂ wA.
            geB : sB₂ Nat.≤ Fin.toℕ (A₂ wA)
            geB = subst (sB₂ Nat.≤_) (sym A₂ℕ) (Nat.≤-trans (Nat.m≤m+n sB₂ (sC + pv))
                    (Nat.m≤n+m (sB₂ + (sC + pv)) 2))
            redB : Fin.toℕ (Fin.reduce≥ (A₂ wA) geB) ≡ 2 + (sC + pv)
            redB = toℕ-reduce≥ (A₂ wA) geB ■ cong (Nat._∸ sB₂) A₂ℕ
                 ■ cong (Nat._∸ sB₂)
                     (sym (Nat.+-assoc 2 sB₂ (sC + pv))
                      ■ cong (Nat._+ (sC + pv)) (Nat.+-comm 2 sB₂)
                      ■ Nat.+-assoc sB₂ 2 (sC + pv))
                 ■ Nat.m+n∸m≡n sB₂ (2 + (sC + pv))
            geAi : 2 + sC Nat.≤ Fin.toℕ (Fin.reduce≥ (A₂ wA) geB)
            geAi = subst (2 + sC Nat.≤_) (sym redB) (Nat.+-monoʳ-≤ 2 (Nat.m≤m+n sC pv))
            lhs : Fin.toℕ (B₂ᵣ (A₂ wA)) ≡ sB₂ + (sC + (2 + pv))
            lhs = toℕ-↑*-ge (assocSwapᵣ 2 sC) sB₂ (A₂ wA) geB
                ■ cong (sB₂ +_) (toℕ-assoc-ge 2 sC (Fin.reduce≥ (A₂ wA) geB) geAi ■ redB
                                ■ (sym (Nat.+-assoc 2 sC pv) ■ cong (Nat._+ pv) (Nat.+-comm 2 sC) ■ Nat.+-assoc sC 2 pv))
            rhs : Fin.toℕ (rB (rC (r2 v))) ≡ sB₂ + (sC + (2 + pv))
            rhs = toℕ-weaken*ᵣ sB₂ (rC (r2 v))
                ■ cong (sB₂ +_) (toℕ-weaken*ᵣ sC (r2 v)
                                ■ cong (sC +_) (toℕ-weaken*ᵣ 2 v))
        fuseL : tailNF ⋯ A₂ ⋯ B₂ᵣ
                ≡ σ i ⋯ ((((lC ·ₖ lB) ·ₖ l2) ·ₖ A₂) ·ₖ B₂ᵣ)
        fuseL =
            cong (λ z → z ⋯ A₂ ⋯ B₂ᵣ)
              ( cong (_⋯ l2) (fusion (σ i) lC lB)
              ■ fusion (σ i) (lC ·ₖ lB) l2 )
          ■ cong (_⋯ B₂ᵣ) (fusion (σ i) ((lC ·ₖ lB) ·ₖ l2) A₂)
          ■ fusion (σ i) (((lC ·ₖ lB) ·ₖ l2) ·ₖ A₂) B₂ᵣ
        fuseR : σ i ⋯ r2 ⋯ rC ⋯ rB
                ≡ σ i ⋯ ((r2 ·ₖ rC) ·ₖ rB)
        fuseR =
            cong (_⋯ rB) (fusion (σ i) r2 rC)
          ■ fusion (σ i) (r2 ·ₖ rC) rB
        tailLeaf : tailNF ⋯ A₂ ⋯ B₂ᵣ
                   ≡ σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ sC ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        tailLeaf = fuseL ■ ⋯-cong (σ i) tailRen ■ sym fuseR
    ... | inj₁ z with Fin.splitAt (sum C) z in eqz
    ...   | inj₁ j rewrite leafσ-A₁ σ C B₂ w z j eqw eqz =
            cong (λ z → z ⋯ A₂ ⋯ B₂ᵣ) coreC ■ leafC
      where
        Lc : Tm (sB₂ + (sC + (2 + n)))
        Lc = canonₛ C (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        tC : Tm (2 + (sB₂ + (sC + n)))
        tC = Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 2
        τC : τ w ≡ canonₛ (zero ∷ C) (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        τC = leafσ-A₁ σ (zero ∷ C) B₂ w z j eqw eqz
        -- C-region: the (zero ∷ C) head reduces to subst (+-suc sC) of canonₛ C with
        -- channel triple (` 0F , 1F , *).  The e1 slot is the head sync VARIABLE ` 0F,
        -- which the ACQ substitution ⦅ * ⦆ₛ collapses to *, matching tC's K `unit e1.
        -- So coreC is NOT a renaming identity; the variable collapse happens here.
        coreCmain :
          subst Tm eqC (canonₛ (zero ∷ C) (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
            ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ⋯ ⦅ * ⦆ₛ
          ≡ tC
        coreCmain =
          cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ⋯ ⦅ * ⦆ₛ)
            (canonₛ-zero-head (K `unit) (K `unit) 0F j)
          ■ varC-transpose C sB₂ j
        coreC : sPre w ⋯ ⦅ * ⦆ₛ ≡ tC
        coreC =
            cong (_⋯ ⦅ * ⦆ₛ)
              ( sPre-pt w
              ■ cong (λ z → subst Tm eqC z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd) τC )
          ■ coreCmain
        tCA : tC ⋯ A₂ ≡ Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂)
        tCA =
            fusion (Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwapᵣ sB₂ 2) A₂
          ■ ⋯-cong (Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwap-invol sB₂ 2)
          ■ ⋯-id (Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (λ _ → refl)
        cancelCₛ : ((assocSwapᵣ sC 2 ↑* sB₂) ·ₖ (assocSwapᵣ 2 sC ↑* sB₂)) ≗ idₖ
        cancelCₛ x = sym (dist-↑*-· sB₂ (assocSwapᵣ sC 2) (assocSwapᵣ 2 sC) x)
                   ■ id↑* sB₂ (assocSwap-invol sC 2) x
        leafC : tC ⋯ A₂ ⋯ B₂ᵣ ≡ canonₛ C (K `unit , 0F , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        leafC =
            cong (λ z → z ⋯ B₂ᵣ) tCA
          ■ fusion Lc (assocSwapᵣ sC 2 ↑* sB₂) B₂ᵣ
          ■ ⋯-id Lc cancelCₛ
    ...   | inj₂ k rewrite leafσ-B₁ σ C B₂ w z k eqw eqz = fromWk w tB2 wkB2 leafB2
      where
        cBk : Tm (sB₂ + (sC + (2 + n)))
        cBk = canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit) k
        tB2 : Tm (2 + (sB₂ + (sC + n)))
        tB2 = cBk ⋯ (assocSwapᵣ sC 2 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 2
        τB₂ : τ w ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ (suc sC) 1F , K `unit) k
        τB₂ = leafσ-B₁ σ (zero ∷ C) B₂ w z k eqw eqz
        rhsRed : tB2 ⋯ weakenᵣ
                 ≡ canonₛ B₂ (mapᶜ (assocSwapᵣ sC 2) (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit)) k
                     ⋯ assocSwapᵣ sB₂ 2 ⋯ weakenᵣ
        rhsRed = cong (λ z → z ⋯ assocSwapᵣ sB₂ 2 ⋯ weakenᵣ)
                   (canonₛ-nat B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit) (assocSwapᵣ sC 2) k)
        cc0 : UChan (sC + (2 + n))
        cc0 = (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit)
        cc1 : UChan (suc sC + (2 + n))
        cc1 = (K `unit , weaken* ⦃ Kᵣ ⦄ (suc sC) 1F , K `unit)
        c0 : Tm (sB₂ + (sC + (2 + n)))
        c0 = canonₛ B₂ cc0 k
        ρa♭ = subst (λ z → z →ᵣ (sB₂ + suc (sC + (2 + n)))) (sym eqC) ρa
        flagEq : weakenᵣ (weaken* ⦃ Kᵣ ⦄ sC 1F) ≡ weaken* ⦃ Kᵣ ⦄ (suc sC) 1F
        flagEq = Fin.toℕ-injective
          ( toℕ-weaken*ᵣ 1 (weaken* ⦃ Kᵣ ⦄ sC 1F)
          ■ cong (1 +_) (toℕ-weaken*ᵣ sC 1F)
          ■ sym (toℕ-weaken*ᵣ (suc sC) 1F) )
        headEq : c0 ⋯ (weakenᵣ ↑* sB₂) ≡ canonₛ B₂ cc1 k
        headEq = canonₛ-nat B₂ cc0 weakenᵣ k
               ■ cong (λ cc → canonₛ B₂ cc k) (cong₂ _,_ refl (cong₂ _,_ flagEq refl))
        flagEq2 : assocSwapᵣ sC 2 (weaken* ⦃ Kᵣ ⦄ sC 1F) ≡ 1F
        flagEq2 = Fin.toℕ-injective
          ( toℕ-assoc-mid sC 2 (weaken* ⦃ Kᵣ ⦄ sC 1F)
              (subst (sC Nat.≤_) (sym (toℕ-weaken*ᵣ sC 1F)) (Nat.m≤m+n sC 1))
              (subst (Nat._< sC + 2) (sym (toℕ-weaken*ᵣ sC 1F)) (Nat.+-monoʳ-< sC (Nat.s≤s (Nat.s≤s Nat.z≤n))))
          ■ cong (Nat._∸ sC) (toℕ-weaken*ᵣ sC 1F)
          ■ Nat.m+n∸m≡n sC 1 )
        mid1 : Tm (3 + (sB₂ + (sC + n)))
        mid1 = canonₛ B₂ (K `unit , 1F , K `unit) k ⋯ assocSwapᵣ sB₂ 2 ⋯ weakenᵣ
        midR : mid1 ≡ tB2 ⋯ weakenᵣ
        midR = cong (λ z → z ⋯ assocSwapᵣ sB₂ 2 ⋯ weakenᵣ)
                 ( cong (λ cc → canonₛ B₂ cc k) (cong₂ _,_ refl (cong₂ _,_ (sym flagEq2) refl))
                 ■ sym (canonₛ-nat B₂ cc0 (assocSwapᵣ sC 2) k) )
        core : subst Tm eqC (canonₛ B₂ cc1 k)
                 ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd
               ≡ tB2 ⋯ weakenᵣ
        core = coreL ■ midR
          where
            coreL : subst Tm eqC (canonₛ B₂ cc1 k) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ≡ mid1
            coreL = canonₛ-↑transpose {sC = sC} {n = n} B₂ k
        wkB2 : sPre w ≡ tB2 ⋯ weakenᵣ
        wkB2 =
            sPre-pt w
          ■ cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd) (cong (subst Tm eqC) τB₂)
          ■ core
        tB2A : tB2 ⋯ A₂ ≡ cBk ⋯ (assocSwapᵣ sC 2 ↑* sB₂)
        tB2A =
            fusion (cBk ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwapᵣ sB₂ 2) A₂
          ■ ⋯-cong (cBk ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwap-invol sB₂ 2)
          ■ ⋯-id (cBk ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (λ _ → refl)
        cancelBₛ : ((assocSwapᵣ sC 2 ↑* sB₂) ·ₖ (assocSwapᵣ 2 sC ↑* sB₂)) ≗ idₖ
        cancelBₛ x = sym (dist-↑*-· sB₂ (assocSwapᵣ sC 2) (assocSwapᵣ 2 sC) x)
                   ■ id↑* sB₂ (assocSwap-invol sC 2) x
        leafB2 : tB2 ⋯ A₂ ⋯ B₂ᵣ ≡ canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit) k
        leafB2 =
            cong (λ z → z ⋯ B₂ᵣ) tB2A
          ■ fusion cBk (assocSwapᵣ sC 2 ↑* sB₂) B₂ᵣ
          ■ ⋯-id cBk cancelBₛ
    -- after lowering (⦅*⦆ₛ collapses the consumed handle) + renaming, s₀ ·ₖ A₂ ·ₖ B₂ᵣ
    -- matches ρ⁻ ·ₖ leafσ σ C B₂.  This is exactly TowerGoal at the frame index ρ⁻ y.
    s₀-leaf : (λ y → s₀ y ⋯ A₂ ⋯ B₂ᵣ) ≗ (λ y → leafσ σ C B₂ (ρ⁻ y))
    s₀-leaf y = towerNF (ρ⁻ y) (ρ⁻≢0 y)
    subst-Tm-cod : ∀ {a c} (eq : a ≡ c) {aa} (u : Tm aa) (s : aa →ₛ a) →
                   subst Tm eq (u ⋯ s) ≡ u ⋯ subst (λ z → aa →ₛ z) eq s
    subst-Tm-cod refl u s = refl
    -- the combined leaf substitution that the whole post-redex renaming chain
    -- collapses to:  sPre ; ⦅*⦆ₛ ; A₂ ; B₂ᵣ.
    cs : (sum (zero ∷ C) + sum B₂ + m) →ₛ sB₂ + (sC + (2 + n))
    cs = (((sPre ·ₖ ⦅ * ⦆ₛ) ·ₖ A₂) ·ₖ B₂ᵣ)
    -- LHS thread collapses (rnT-plug ; frame-plug* ; junc-tr ; fusion) to (E[`0F]*) ⋯ cs.
    threadReduce :
      (((Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]*) ⋯ ⦅ * ⦆ₛ) ⋯ A₂) ⋯ B₂ᵣ
      ≡ (E [ ` 0F ]*) ⋯ cs
    threadReduce =
        cong (λ z → (z ⋯ ⦅ * ⦆ₛ ⋯ A₂) ⋯ B₂ᵣ) stepA
      ■ cong (λ z → (z ⋯ ⦅ * ⦆ₛ ⋯ A₂) ⋯ B₂ᵣ) stepB
      ■ ⋯-fuse4
      where
        stepA : Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ≡ rnT ((E [ ` 0F ]*) ⋯ τ)
        stepA =
            cong (Fout [_]*) (sym (proj₂ junc-tr))
          ■ sym (rnT-plug F₁ τ0F)
          ■ cong rnT (sym (frame-plug* E τ Vτ))
        τ̂ : (sum (zero ∷ C) + sum B₂ + m) →ₛ sB₂ + (sC + (3 + n))
        τ̂ = subst (λ z → (sum (zero ∷ C) + sum B₂ + m) →ₛ z) eqC τ
        s1 = τ̂ ·ₖ ρa
        s2 = s1 ·ₖ ρb
        s3 = s2 ·ₖ ρc
        stepB : rnT ((E [ ` 0F ]*) ⋯ τ) ≡ (E [ ` 0F ]*) ⋯ sPre
        stepB =
            cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
              (subst-Tm-cod eqC (E [ ` 0F ]*) τ)
          ■ cong (λ z → z ⋯ ρb ⋯ ρc ⋯ ρd) (fusion (E [ ` 0F ]*) τ̂ ρa)
          ■ cong (λ z → z ⋯ ρc ⋯ ρd) (fusion (E [ ` 0F ]*) s1 ρb)
          ■ cong (_⋯ ρd) (fusion (E [ ` 0F ]*) s2 ρc)
          ■ fusion (E [ ` 0F ]*) s3 ρd
        c1 : (sum (zero ∷ C) + sum B₂ + m) →ₛ 2 + (sB₂ + (sC + n))
        c1 = sPre ·ₖ ⦅ * ⦆ₛ
        c2 : (sum (zero ∷ C) + sum B₂ + m) →ₛ sB₂ + (2 + (sC + n))
        c2 = c1 ·ₖ A₂
        ⋯-fuse4 : ((E [ ` 0F ]*) ⋯ sPre ⋯ ⦅ * ⦆ₛ ⋯ A₂) ⋯ B₂ᵣ ≡ (E [ ` 0F ]*) ⋯ cs
        ⋯-fuse4 =
            cong (λ z → z ⋯ A₂ ⋯ B₂ᵣ) (fusion (E [ ` 0F ]*) sPre ⦅ * ⦆ₛ)
          ■ cong (_⋯ B₂ᵣ) (fusion (E [ ` 0F ]*) c1 A₂)
          ■ fusion (E [ ` 0F ]*) c2 B₂ᵣ
    -- VSub for the leaf substitution of the RHS (C-bind group).
    Vτ-C : VSub (leafσ σ C B₂)
    Vτ-C = ++ₛ-VSub
             (++ₛ-VSub
               (λ i → value-⋯ (VSub-canonₛ C (K `unit , 0F , K `unit) (V-K , V-K) i)
                         (weaken* ⦃ Kᵣ ⦄ sB₂) (λ _ → V-`))
               (VSub-canonₛ B₂ (K `unit , weaken* ⦃ Kᵣ ⦄ sC 1F , K `unit) (V-K , V-K)))
             (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                       (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                       (weaken* ⦃ Kᵣ ⦄ sC) (λ _ → V-`))
                       (weaken* ⦃ Kᵣ ⦄ sB₂) (λ _ → V-`))
    -- cs is a value-substitution: each component is a value (chanTriple / σ image
    -- pushed through value-preserving renamings).
    Vcs : VSub cs
    Vcs i = value-⋯ (value-⋯ (value-⋯ Vsprei ⦅ * ⦆ₛ ∈-cleanup) A₂ (λ _ → V-`)) B₂ᵣ (λ _ → V-`)
      where
        ∈-cleanup : VSub ⦅ * ⦆ₛ
        ∈-cleanup zero    = V-K
        ∈-cleanup (suc _) = V-`
        Vsprei : Value (sPre i)
        Vsprei = subst Value (sym (sPre-pt i))
          (value-⋯ (value-⋯ (value-⋯ (value-⋯ (Value-subst eqC (Vτ i))
            ρa (λ _ → V-`)) ρb (λ _ → V-`)) ρc (λ _ → V-`)) ρd (λ _ → V-`))
    -- the frame uses only ρ⁻-image indices, so cs and leafσ σ C B₂ agree there.
    csleaf : (ρ⁻ ·ₖ cs) ≗ (ρ⁻ ·ₖ leafσ σ C B₂)
    csleaf y = s₀-leaf y
    frameReconcile : (E [ ` 0F ]*) ⋯ cs ≡ (E [ ` 0F ]*) ⋯ leafσ σ C B₂
    frameReconcile =
        frame-plug* E cs Vcs
      ■ cong₂ _[_]*
          ( cong (λ EE → frame*-⋯ EE cs Vcs) E≡
          ■ F-⋯f*-fuse E₀ Vcs (·ₖ-VSubᵣ ρ⁻ Vcs)
          ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ Vcs) (·ₖ-VSubᵣ ρ⁻ Vτ-C) csleaf
          ■ sym (F-⋯f*-fuse E₀ Vτ-C (·ₖ-VSubᵣ ρ⁻ Vτ-C))
          ■ cong (λ EE → frame*-⋯ EE (leafσ σ C B₂) Vτ-C) (sym E≡) )
          plugReconcile
      ■ sym (frame-plug* E (leafσ σ C B₂) Vτ-C)
      where
        plugReconcile : (` 0F) ⋯ cs ≡ (` 0F) ⋯ leafσ σ C B₂
        plugReconcile =
            cong (λ z → z ⋯ A₂ ⋯ B₂ᵣ) coreC0 ■ leafC0
          where
            j0 : 𝔽 (sum C)
            j0 = 0F
            eqw0 : Fin.splitAt (sum C + sum B₂) {m} 0F ≡ inj₁ 0F
            eqw0 = refl
            eqz0 : Fin.splitAt (sum C) {sum B₂} 0F ≡ inj₁ 0F
            eqz0 = refl
            Lc0 : Tm (sB₂ + (sC + (2 + n)))
            Lc0 = canonₛ C (K `unit , 0F , K `unit) j0 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
            tC0 : Tm (2 + (sB₂ + (sC + n)))
            tC0 = Lc0 ⋯ (assocSwapᵣ sC 2 ↑* sB₂) ⋯ assocSwapᵣ sB₂ 2
            τC0 : sPre 0F ≡ subst Tm eqC
                    (canonₛ (zero ∷ C) (K `unit , 0F , K `unit) j0 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                    ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd
            τC0 = sPre-pt 0F
                ■ cong (λ z → subst Tm eqC z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
                    (leafσ-A₁ σ (zero ∷ C) B₂ 0F 0F j0 eqw0 eqz0)
            coreCmain0 :
              subst Tm eqC (canonₛ (zero ∷ C) (K `unit , 0F , K `unit) j0 ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
                ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ⋯ ⦅ * ⦆ₛ
              ≡ tC0
            coreCmain0 =
              cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ⋯ ⦅ * ⦆ₛ)
                (canonₛ-zero-head (K `unit) (K `unit) 0F j0)
              ■ varC-transpose C sB₂ j0
            coreC0 : sPre 0F ⋯ ⦅ * ⦆ₛ ≡ tC0
            coreC0 = cong (_⋯ ⦅ * ⦆ₛ) τC0 ■ coreCmain0
            tCA0 : tC0 ⋯ A₂ ≡ Lc0 ⋯ (assocSwapᵣ sC 2 ↑* sB₂)
            tCA0 =
                fusion (Lc0 ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwapᵣ sB₂ 2) A₂
              ■ ⋯-cong (Lc0 ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwap-invol sB₂ 2)
              ■ ⋯-id (Lc0 ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (λ _ → refl)
            cancelC0 : ((assocSwapᵣ sC 2 ↑* sB₂) ·ₖ (assocSwapᵣ 2 sC ↑* sB₂)) ≗ idₖ
            cancelC0 x = sym (dist-↑*-· sB₂ (assocSwapᵣ sC 2) (assocSwapᵣ 2 sC) x)
                       ■ id↑* sB₂ (assocSwap-invol sC 2) x
            leafC0 : tC0 ⋯ A₂ ⋯ B₂ᵣ ≡ leafσ σ C B₂ 0F
            leafC0 =
                cong (λ z → z ⋯ B₂ᵣ) tCA0
              ■ fusion Lc0 (assocSwapᵣ sC 2 ↑* sB₂) B₂ᵣ
              ■ ⋯-id Lc0 cancelC0
              ■ sym (leafσ-A₁ σ C B₂ 0F 0F j0 eqw0 eqz0)
    threadEqR :
      ((((U.⟪ Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ⟫) U.⋯ₚ ⦅ * ⦆ₛ)
            U.⋯ₚ assocSwapᵣ 2 sB₂) U.⋯ₚ (assocSwapᵣ 2 sC ↑* sB₂))
      ≡ U.⟪ (E [ ` 0F ]*) ⋯ leafσ σ C B₂ ⟫
    threadEqR = cong U.⟪_⟫ (threadReduce ■ frameReconcile)
    residEqR :
      (((Qout U.⋯ₚ ⦅ * ⦆ₛ) U.⋯ₚ assocSwapᵣ 2 sB₂) U.⋯ₚ (assocSwapᵣ 2 sC ↑* sB₂))
      ≡ U[ P ] (leafσ σ C B₂)
    residEqR =
        cong (λ z → ((z U.⋯ₚ ⦅ * ⦆ₛ) U.⋯ₚ A₂) U.⋯ₚ B₂ᵣ) QoutP₀
      ■ cong (λ z → (z U.⋯ₚ A₂) U.⋯ₚ B₂ᵣ) (U-σ⋯ₛ P₀ {σ = sPre⁻} {τ = ⦅ * ⦆ₛ})
      ■ cong (λ z → z U.⋯ₚ B₂ᵣ) (U-σ⋯ P₀ {σ = s₀} {ρ = A₂})
      ■ U-σ⋯ P₀ {σ = s₀ ·ₖ A₂} {ρ = B₂ᵣ}
      ■ U-cong P₀ s₀-leaf
      ■ sym (U-⋯ₚ P₀ {ρ = ρ⁻} {σ = leafσ σ C B₂})
      ■ cong (λ z → U[ z ] (leafσ σ C B₂)) (sym P≡)
    leafReconcile : (leaf′ U.⋯ₚ assocSwapᵣ 2 sB₂) U.⋯ₚ (assocSwapᵣ 2 sC ↑* sB₂)
                    ≡ U[ QR ] (leafσ σ C B₂)
    leafReconcile = cong₂ U._∥_ threadEqR residEqR
    back : fired U.≋ U[ T.ν C B₂ QR ] σ
    back =
         Bφ-cong C (Bφ-past-ν B₂ leaf′)
      ◅◅ Bφ-past-ν C (Bφ B₂ (leaf′ U.⋯ₚ assocSwapᵣ 2 sB₂))
      ◅◅ U.ν-cong (Bφ-cong C (≡→≋ (Bφ-⋯ B₂ (leaf′ U.⋯ₚ assocSwapᵣ 2 sB₂) (assocSwapᵣ 2 sC))))
      ◅◅ U.ν-cong (Bφ-cong C (Bφ-cong B₂ (≡→≋ leafReconcile)))
      ◅◅ ≡→≋ (sym (Uν-flat σ C B₂ QR))
