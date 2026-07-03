module BorrowedCF.Simulation.Theorems.AcqH1 where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation.TranslationProperties
  using (UB-nat; Ub-nat; Ub-V; mapᶜ; mapᶜ-fusion; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; weaken*ᵣ~↑ʳ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-assoc-lt; toℕ-↑
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol; R2' )
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation.TranslationProperties using (VChan; chanTriple-V; Value-subst)
open import BorrowedCF.Simulation.SplitConfine using (acq-confine)
open import BorrowedCF.Simulation.AcqSubstNat
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

