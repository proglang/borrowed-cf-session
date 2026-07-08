module BorrowedCF.Simulation.Theorems.Acq where

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
open import BorrowedCF.Simulation.FrameRename using (F-σ⋯)
open import BorrowedCF.Simulation.TranslationProperties using (VChan; chanTriple-V; Value-subst)
open import BorrowedCF.Simulation.SplitConfine using (acq-confine)
open import BorrowedCF.Simulation.AcqSubstNat
  using (subst₂→ₖ; subst-⋯ₚ-codₖ; subst-⋯ₚ-domₖ; liftCastₖ; subst-flipₖ
        ; subst-⋯ᵏ; subst-⋯-codᵏ; subst₂-cancelₖ; subst-subst-symᵏ; varΘ-fixₛ)
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import BorrowedCF.Simulation.Theorems.AcqH2 public

-- ————————————————————————————————————————————————————————————————
-- General avoidance machinery (reused across the three factorings).

0F-suc : ∀ {N} (x : 𝔽 (suc N)) → x ≢ 0F → Σ[ y ∈ 𝔽 N ] x ≡ suc y
0F-suc 0F      x≢0 = ⊥-elim (x≢0 refl)
0F-suc (suc y) _   = y , refl

-- ηfix : ⦅*⦆ₛ then weakenᵣ fixes every var except 0F (which it sends to *).
ηfix : ∀ {N} (x : 𝔽 (suc N)) → x ≢ 0F → (` x) ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ ≡ ` x
ηfix x x≢0 with 0F-suc x x≢0
... | y , refl = refl

-- A renaming image that never lands on 0F is fixed by ⦅*⦆ₛ then weakenᵣ.
avoid-ren : ∀ {N mm} (u : Tm N) (ρ : N →ᵣ suc mm) → (∀ x → ρ x ≢ 0F)
          → u ⋯ ρ ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ ≡ u ⋯ ρ
avoid-ren {N} {mm} u ρ ρ≢0 =
    fusion (u ⋯ ρ) ⦅ * ⦆ₛ weakenᵣ
  ■ fusion u ρ η
  ■ ⋯-cong u pt
  ■ conv-⋯ᵣₛ u {ρ = ρ}
  where
    η : suc mm →ₛ suc mm
    η = ⦅ * ⦆ₛ ·ₖ weakenᵣ
    pt : (ρ ·ₖ η) ≗ (`_ ∘ ρ)
    pt x = sym (⋯-var x (ρ ·ₖ η))
         ■ sym (fusion (` x) ρ η)
         ■ cong (_⋯ η) (⋯-var x ρ)
         ■ sym (fusion (` (ρ x)) ⦅ * ⦆ₛ weakenᵣ)
         ■ ηfix (ρ x) (ρ≢0 x)

-- weakenᵣ commutes past a lifted renaming.
wk-↑ : ∀ {a b} (t : Tm a) (ρ : a →ᵣ b) → (t ⋯ weakenᵣ) ⋯ (ρ ↑) ≡ (t ⋯ ρ) ⋯ weakenᵣ
wk-↑ t ρ = sym (⋯-↑-wk t ρ)

-- codomain-cast of a renaming.
castᵣ : ∀ {a c d} → c ≡ d → (a →ᵣ c) → (a →ᵣ d)
castᵣ {a} p θ = subst (λ z → a →ᵣ z) p θ

toℕ-castᵣ : ∀ {a c d} (p : c ≡ d) (θ : a →ᵣ c) (x : 𝔽 a) → Fin.toℕ (castᵣ p θ x) ≡ Fin.toℕ (θ x)
toℕ-castᵣ refl θ x = refl

-- canonₛ's head endpoint slot is irrelevant away from the head index j = 0F.
Ub-e1-irrel : ∀ {N} (b : ℕ) (e1 e1' : Tm N) (x : 𝔽 N) (e2 : Tm N) (j : 𝔽 b) → Fin.toℕ j ≢ 0 →
  Ub[ b ] (e1 , x , e2) j ≡ Ub[ b ] (e1' , x , e2) j
Ub-e1-irrel (suc b)       e1 e1' x e2 0F      j≢0 = ⊥-elim (j≢0 refl)
Ub-e1-irrel (suc (suc b)) e1 e1' x e2 (suc j) _   = refl

-- j ≢ 0F ⟹ the head-block index (splitAt b j = inj₁ jh) is also non-zero.
splitAt-inj₁-toℕ : ∀ {a c} (j : 𝔽 (a + c)) (jh : 𝔽 a) → Fin.splitAt a j ≡ inj₁ jh
                 → Fin.toℕ jh ≡ Fin.toℕ j
splitAt-inj₁-toℕ {a} {c} j jh eq =
    sym (Fin.toℕ-↑ˡ jh c)
  ■ cong Fin.toℕ (sym (join-eq eq))
  where
    join-eq : Fin.splitAt a j ≡ inj₁ jh → j ≡ jh Fin.↑ˡ c
    join-eq eqj = sym (Fin.join-splitAt a c j) ■ cong (Fin.join a c) eqj

canonₛ-e1-irrel : ∀ {N} (B : BindGroup) (e1 e1' : Tm N) (x : 𝔽 N) (e2 : Tm N)
                  (j : 𝔽 (sum B)) → Fin.toℕ j ≢ 0 →
  canonₛ B (e1 , x , e2) j ≡ canonₛ B (e1' , x , e2) j
canonₛ-e1-irrel []              e1 e1' x e2 ()      _
canonₛ-e1-irrel (b ∷ [])        e1 e1' x e2 j       j≢0 =
  Ub-e1-irrel (b + 0) e1 e1' x e2 j j≢0
canonₛ-e1-irrel {N} (b ∷ B@(_ ∷ _)) e1 e1' x e2 j j≢0
  with Fin.splitAt b j in eq
... | inj₂ k  = refl
... | inj₁ jh = cong (subst Tm (+-suc (syncs B) N))
                  (cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
                    (Ub-e1-irrel b (wk e1) (wk e1') (suc x) (` 0F) jh jh≢0))
  where
    jh≢0 : Fin.toℕ jh ≢ 0
    jh≢0 eqjh0 = j≢0 (sym (splitAt-inj₁-toℕ j jh eq) ■ eqjh0)

-- A lifted renaming never lands on 0F when its argument isn't 0F.
↑≢0 : ∀ {N M} (ρ : N →ᵣ M) (y : 𝔽 (suc N)) → y ≢ 0F → (ρ ↑) y ≢ 0F
↑≢0 ρ 0F      y≢0 = ⊥-elim (y≢0 refl)
↑≢0 ρ (suc k) _   = λ ()

subst-K′ : ∀ {a b} (eq : a ≡ b) → subst Tm eq (K `unit) ≡ K `unit
subst-K′ refl = refl

subst-var′ : ∀ {a b} (eq : a ≡ b) (v : 𝔽 a) → subst Tm eq (` v) ≡ ` (subst 𝔽 eq v)
subst-var′ refl v = refl

-- The acquired-channel continuation (third slot of canonₛ-acq-head's head triple)
-- avoids the handle position sC = syncs(suc b ∷ B): it is K `unit in three cases
-- and a var at position sB < sC in the fourth, so it factors through weakenᵣ ↑* sC.
tc-factors-gen : ∀ {N} (b : ℕ) (B : BindGroup) →
  Σ[ tc′ ∈ Tm (syncs (suc b ∷ B) + suc N) ]
    (proj₁ (proj₂ (proj₂ (canonₛ-acq-head b B (K `unit))))
       ≡ tc′ ⋯ (weakenᵣ ↑* syncs (suc b ∷ B)))
tc-factors-gen zero    []        = K `unit , refl
tc-factors-gen (suc b) []        = K `unit , refl
tc-factors-gen {N} (suc b) (c′ ∷ B) = K `unit , subst-K′ (+-suc (syncs (c′ ∷ B)) (2 + N))
tc-factors-gen {N} zero (c′ ∷ B) = (` v′) , pfac
  where
    sB : ℕ
    sB = syncs (c′ ∷ B)
    v′ : 𝔽 (syncs (suc zero ∷ c′ ∷ B) + suc N)
    v′ = subst 𝔽 (+-suc sB (1 + N)) (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {n = 1 + N}))
    pfac : proj₁ (proj₂ (proj₂ (canonₛ-acq-head zero (c′ ∷ B) (K `unit))))
            ≡ (` v′) ⋯ (weakenᵣ ↑* syncs (suc zero ∷ c′ ∷ B))
    pfac = cong (subst Tm (+-suc sB (2 + N))) (⋯-var (Fin.zero {n = 2 + N}) (weaken* ⦃ Kᵣ ⦄ sB))
         ■ subst-var′ (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {n = 2 + N}))
         ■ cong `_ vv′eq
         ■ sym (⋯-var v′ (weakenᵣ ↑* syncs (suc zero ∷ c′ ∷ B)))
      where
        v : 𝔽 (syncs (suc zero ∷ c′ ∷ B) + (2 + N))
        v = subst 𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {n = 2 + N}))
        toℕv : Fin.toℕ v ≡ sB
        toℕv = toℕ-subst𝔽 (+-suc sB (2 + N)) (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {n = 2 + N}))
             ■ toℕ-weaken*ᵣ sB (Fin.zero {n = 2 + N}) ■ Nat.+-identityʳ sB
        toℕv′ : Fin.toℕ v′ ≡ sB
        toℕv′ = toℕ-subst𝔽 (+-suc sB (1 + N)) (weaken* ⦃ Kᵣ ⦄ sB (Fin.zero {n = 1 + N}))
              ■ toℕ-weaken*ᵣ sB (Fin.zero {n = 1 + N}) ■ Nat.+-identityʳ sB
        v′<sC : Fin.toℕ v′ Nat.< syncs (suc zero ∷ c′ ∷ B)
        v′<sC = subst (Nat._< syncs (suc zero ∷ c′ ∷ B)) (sym toℕv′) Nat.≤-refl
        vv′eq : v ≡ (weakenᵣ ↑* syncs (suc zero ∷ c′ ∷ B)) v′
        vv′eq = Fin.toℕ-injective
                  (toℕv ■ sym (toℕ-↑*-lt weakenᵣ (syncs (suc zero ∷ c′ ∷ B)) v′ v′<sC ■ toℕv′))


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
    acq-out-eq :
      U.ν ((U.⟪ Fout [ (* ⊗ (` 1F)) ⊗ eout ]* ⟫ U.∥ Qout) U.⋯ₚ ⦅ * ⦆ₛ)
      ≡ U.ν ((U.⟪ Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]* ⟫ U.∥ Qout) U.⋯ₚ ⦅ * ⦆ₛ)
    acq-out-eq = cong U.ν (cong₂ U._∥_ (cong U.⟪_⟫ thread-eq) refl)
      where
        V* : VSub ⦅ * ⦆ₛ
        V* zero    = V-K
        V* (suc _) = V-`
        acq-term-eq : (( * ⊗ (` 1F)) ⊗ eout) ⋯ ⦅ * ⦆ₛ
                    ≡ (((` 0F) ⊗ (` 1F)) ⊗ eout) ⋯ ⦅ * ⦆ₛ
        acq-term-eq = refl
        thread-eq : (Fout [ (* ⊗ (` 1F)) ⊗ eout ]*) ⋯ ⦅ * ⦆ₛ
                  ≡ (Fout [ ((` 0F) ⊗ (` 1F)) ⊗ eout ]*) ⋯ ⦅ * ⦆ₛ
        thread-eq =
            frame-plug* Fout ⦅ * ⦆ₛ V*
          ■ cong ((frame*-⋯ Fout ⦅ * ⦆ₛ V*) [_]*) acq-term-eq
          ■ sym (frame-plug* Fout ⦅ * ⦆ₛ V*)
    -- fire (atomic-acquire leaf reconciliation) is defined below, after the
    -- sPre/avoid machinery it depends on (this where block resolves names in
    -- textual order).
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
    towerFac : (w : 𝔽 (sum C + sum B₂ + m)) → w ≢ 0F →
               Σ[ t ∈ Tm (2 + (sB₂ + (sC + n))) ]
                 (sPre w ≡ t ⋯ weakenᵣ) × (t ⋯ A₂ ⋯ B₂ᵣ ≡ leafσ σ C B₂ w)
    towerFac w w≢0 with Fin.splitAt (sum C + sum B₂) w in eqw
    ... | inj₂ i = tailNF , tailWk , tailLeaf
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
            tC , cWk , leafC
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
        cWk : sPre w ≡ tC ⋯ weakenᵣ
        cWk =
            sPre-pt w
          ■ cong (λ z → subst Tm eqC z ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd) τC
          ■ cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd)
              (canonₛ-zero-head (K `unit) (K `unit) 0F j)
          ■ Wρcρd
          where
            cc0 : UChan (2 + n)
            cc0 = (K `unit , 0F , K `unit)
            cc1 : UChan (3 + n)
            cc1 = (` 0F , 1F , K `unit)
            u : Tm (sC + (2 + n))
            u = canonₛ C cc0 j
            M0 : Tm (sB₂ + (sC + (3 + n)))
            M0 = subst Tm eqC (subst Tm (+-suc sC (2 + n)) (canonₛ C cc1 j) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
            jℕ≢0 : Fin.toℕ j ≢ 0
            jℕ≢0 eqj0 = w≢0 (Fin.toℕ-injective
                          (sym (splitAt-inj₁-toℕ z j eqz ■ splitAt-inj₁-toℕ w z eqw) ■ eqj0))
            cc-relate : canonₛ C cc1 j ≡ u ⋯ (weakenᵣ ↑* sC)
            cc-relate = canonₛ-e1-irrel C (` 0F) (K `unit) 1F (K `unit) j jℕ≢0
                      ■ sym (canonₛ-nat C cc0 weakenᵣ j)
            ρ0 : (sC + (2 + n)) →ᵣ suc (sC + (2 + n))
            ρ0 = castᵣ (+-suc sC (2 + n)) (weakenᵣ ↑* sC)
            ρ1 : (sC + (2 + n)) →ᵣ (sB₂ + (sC + (3 + n)))
            ρ1 = castᵣ eqC (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)
            ρ1a : (sC + (2 + n)) →ᵣ _
            ρ1a = ρ1 ·ₖ ρa
            ρW : (sC + (2 + n)) →ᵣ _
            ρW = ρ1a ·ₖ ρb
            Weq : M0 ⋯ ρa ⋯ ρb ≡ u ⋯ ρW
            Weq =
                cong (λ z → subst Tm eqC (subst Tm (+-suc sC (2 + n)) z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb) cc-relate
              ■ cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb)
                  (sym (subst-⋯-cod-local (+-suc sC (2 + n)) u (weakenᵣ ↑* sC)))
              ■ cong (λ z → subst Tm eqC z ⋯ ρa ⋯ ρb) (fusion u ρ0 (weaken* ⦃ Kᵣ ⦄ sB₂))
              ■ cong (λ z → z ⋯ ρa ⋯ ρb) (sym (subst-⋯-cod-local eqC u (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)))
              ■ cong (_⋯ ρb) (fusion u ρ1 ρa)
              ■ fusion u ρ1a ρb
            -- ρW never lands on 0F: it factors through weakenᵣ ↑* sC, which skips
            -- position sC; the two assocSwaps then keep the result ≥ 1.
            ρW≢0 : ∀ x → ρW x ≢ 0F
            ρW≢0 x eq0 = abs (subst (1 Nat.≤_) (cong Fin.toℕ eq0) posℕ)
              where
                abs : 1 Nat.≤ 0 → ⊥
                abs ()
                pv1 : ℕ
                pv1 = Fin.toℕ ((weakenᵣ ↑* sC) x)
                tρ1 : Fin.toℕ (ρ1 x) ≡ sB₂ + pv1
                tρ1 = toℕ-castᵣ eqC (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) x
                    ■ toℕ-weaken*ᵣ sB₂ (ρ0 x)
                    ■ cong (sB₂ +_) (toℕ-castᵣ (+-suc sC (2 + n)) (weakenᵣ ↑* sC) x)
                geB : sB₂ Nat.≤ Fin.toℕ (ρ1 x)
                geB = subst (sB₂ Nat.≤_) (sym tρ1) (Nat.m≤m+n sB₂ pv1)
                redB : Fin.toℕ (Fin.reduce≥ (ρ1 x) geB) ≡ pv1
                redB = toℕ-reduce≥ (ρ1 x) geB ■ cong (Nat._∸ sB₂) tρ1 ■ Nat.m+n∸m≡n sB₂ pv1
                -- toℕ (ρa (ρ1 x)) after the sC↔1 swap above sB₂.
                tρa : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB))
                tρa = toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (ρ1 x) geB
                1≤sB₂+1+ : ∀ k → 1 Nat.≤ sB₂ + (1 + k)
                1≤sB₂+1+ k = Nat.≤-trans (Nat.m≤n+m 1 sB₂) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n 1 k))
                -- toℕ x ≥ sC : weakenᵣ↑*sC lands above sC, so the sC↔1 swap fixes it.
                geCase : sC Nat.≤ Fin.toℕ x → 1 Nat.≤ Fin.toℕ (ρW x)
                geCase gex = subst (1 Nat.≤_) (sym tρW)
                               (Nat.≤-trans (Nat.≤-trans (Nat.m≤n+m 1 sC) sC+1≤pv1) (Nat.m≤n+m pv1 sB₂))
                  where
                    pv1eq : pv1 ≡ sC + (1 + Fin.toℕ (Fin.reduce≥ x gex))
                    pv1eq = toℕ-↑*-ge weakenᵣ sC x gex
                          ■ cong (sC +_) (toℕ-weaken*ᵣ 1 (Fin.reduce≥ x gex))
                    sC+1≤pv1 : sC + 1 Nat.≤ pv1
                    sC+1≤pv1 = subst (sC + 1 Nat.≤_) (sym pv1eq) (Nat.+-monoʳ-≤ sC (Nat.m≤m+n 1 _))
                    tassoc : Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB)) ≡ pv1
                    tassoc = toℕ-assoc-ge sC 1 (Fin.reduce≥ (ρ1 x) geB)
                               (subst (sC + 1 Nat.≤_) (sym redB) sC+1≤pv1)
                           ■ redB
                    tρaC : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + pv1
                    tρaC = tρa ■ cong (sB₂ +_) tassoc
                    geAB : sB₂ + 1 Nat.≤ Fin.toℕ (ρa (ρ1 x))
                    geAB = subst (sB₂ + 1 Nat.≤_) (sym tρaC)
                             (Nat.+-monoʳ-≤ sB₂ (Nat.≤-trans (Nat.m≤n+m 1 sC) sC+1≤pv1))
                    tρW : Fin.toℕ (ρW x) ≡ sB₂ + pv1
                    tρW = toℕ-assoc-ge sB₂ 1 (ρa (ρ1 x)) geAB ■ tρaC
                posℕ : 1 Nat.≤ Fin.toℕ (ρW x)
                posℕ with Nat.<-cmp (Fin.toℕ x) sC
                ... | tri< ltx _ _ = subst (1 Nat.≤_) (sym tρW) (1≤sB₂+1+ pv1)
                  where
                    pv1lt : pv1 Nat.< sC
                    pv1lt = subst (Nat._< sC) (sym (toℕ-↑*-lt weakenᵣ sC x ltx)) ltx
                    tassoc : Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB)) ≡ 1 + pv1
                    tassoc = toℕ-assoc-lt sC 1 (Fin.reduce≥ (ρ1 x) geB)
                               (subst (Nat._< sC) (sym redB) pv1lt)
                           ■ cong (1 +_) redB
                    tρaC : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + (1 + pv1)
                    tρaC = tρa ■ cong (sB₂ +_) tassoc
                    geAB : sB₂ + 1 Nat.≤ Fin.toℕ (ρa (ρ1 x))
                    geAB = subst (sB₂ + 1 Nat.≤_) (sym tρaC) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n 1 pv1))
                    tρW : Fin.toℕ (ρW x) ≡ sB₂ + (1 + pv1)
                    tρW = toℕ-assoc-ge sB₂ 1 (ρa (ρ1 x)) geAB ■ tρaC
                ... | tri≈ _ eqx _ = geCase (Nat.≤-reflexive (sym eqx))
                ... | tri> _ _ gtx = geCase (Nat.<⇒≤ gtx)
            W-avoid : (M0 ⋯ ρa ⋯ ρb) ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ ≡ M0 ⋯ ρa ⋯ ρb
            W-avoid = cong (λ z → z ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ) Weq
                    ■ avoid-ren u ρW ρW≢0
                    ■ sym Weq
            core-wk : M0 ⋯ ρa ⋯ ρb ≡ Lc ⋯ weakenᵣ
            core-wk = sym W-avoid ■ cong (_⋯ weakenᵣ) (core-gen C sB₂ 0F j)
            Wρcρd : M0 ⋯ ρa ⋯ ρb ⋯ ρc ⋯ ρd ≡ tC ⋯ weakenᵣ
            Wρcρd =
                cong (λ z → z ⋯ ρc ⋯ ρd) core-wk
              ■ cong (_⋯ ρd) (wk-↑ Lc (assocSwapᵣ sC 2 ↑* sB₂))
              ■ wk-↑ (Lc ⋯ (assocSwapᵣ sC 2 ↑* sB₂)) (assocSwapᵣ sB₂ 2)
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
    ...   | inj₂ k rewrite leafσ-B₁ σ C B₂ w z k eqw eqz = tB2 , wkB2 , leafB2
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
    towerNF : (w : 𝔽 (sum C + sum B₂ + m)) → w ≢ 0F → TowerGoal w
    towerNF w w≢0 = let t , wkf , lf = towerFac w w≢0 in fromWk w t wkf lf
    -- Pointwise avoidance: for a non-acquired index, sPre w factors through
    -- weakenᵣ (it never mentions the consumed acq-sync var 0F), so the ⦅*⦆ₛ
    -- lowering is inverted by re-weakening.
    avoid : (w : 𝔽 (sum C + sum B₂ + m)) → w ≢ 0F → sPre w ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ ≡ sPre w
    avoid w w≢0 = let t , wkf , _ = towerFac w w≢0 in
        cong (λ z → z ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ) wkf
      ■ cong (_⋯ weakenᵣ) (wk-cancels-⦅⦆-⋯ t *)
      ■ sym wkf
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
    -- ⦅*⦆ₛ-lowered leaf pieces:  Fbase/ebase/Qbase avoid the consumed acq-sync
    -- var 0F, so re-weakening (weakenᵣ) recovers Fout/eout/Qout (the avoidances
    -- Fout≡ / eout≡ / Qout≡w).  The atomic RU-Acquire (leaf-fire) fires on these
    -- bases; the input/output are reconciled to LL₃ / leaf′.
    V⦅*⦆ : VSub ⦅ * ⦆ₛ
    V⦅*⦆ zero    = V-K
    V⦅*⦆ (suc _) = V-`
    Fbase : Frame* (2 + (sB₂ + (sC + n)))
    Fbase = frame*-⋯ Fout ⦅ * ⦆ₛ V⦅*⦆
    ebase : Tm (2 + (sB₂ + (sC + n)))
    ebase = eout ⋯ ⦅ * ⦆ₛ
    Qbase : U.Proc (2 + (sB₂ + (sC + n)))
    Qbase = Qout U.⋯ₚ ⦅ * ⦆ₛ
    Fout≡ : Fout ≡ Fbase ⋯ᶠ* weakenᵣ
    Fout≡ = sym
      ( F-σ⋯ Fout V⦅*⦆ weakenᵣ Vη
      ■ cong (λ F → frame*-⋯ F η Vη) FoutE
      ■ F*-fuse-local E Vsp Vη Vsη
      ■ cong (λ EE → frame*-⋯ EE (sPre ·ₖ η) Vsη) E≡
      ■ F-⋯f*-fuse E₀ Vsη (·ₖ-VSubᵣ ρ⁻ Vsη)
      ■ frame*-cong E₀ (·ₖ-VSubᵣ ρ⁻ Vsη) (·ₖ-VSubᵣ ρ⁻ Vsp) avoidcong
      ■ sym (F-⋯f*-fuse E₀ Vsp (·ₖ-VSubᵣ ρ⁻ Vsp))
      ■ cong (λ EE → frame*-⋯ EE sPre Vsp) (sym E≡)
      ■ sym FoutE )
      where
        dom : ℕ
        dom = sum (zero ∷ C) + sum B₂ + m
        η : (3 + (sB₂ + (sC + n))) →ₛ (3 + (sB₂ + (sC + n)))
        η = ⦅ * ⦆ₛ ·ₖ weakenᵣ
        ·ₖ-VSubₛ : ∀ {a b c} {σ : a →ₛ b} → VSub σ → (ρ : b →ᵣ c) → VSub (σ ·ₖ ρ)
        ·ₖ-VSubₛ Vσ ρ i = value-⋯ (Vσ i) ρ (λ _ → V-`)
        F*-fuse-local : ∀ {a b c} (E' : Frame* a) {ϕ : a →ₛ b} (Vϕ : VSub ϕ)
                        {ξ : b →ₛ c} (Vξ : VSub ξ) (Vϕξ : VSub (ϕ ·ₖ ξ)) →
                        frame*-⋯ (frame*-⋯ E' ϕ Vϕ) ξ Vξ ≡ frame*-⋯ E' (ϕ ·ₖ ξ) Vϕξ
        F*-fuse-local []        Vϕ Vξ Vϕξ = refl
        F*-fuse-local (Fr ∷ E') Vϕ Vξ Vϕξ =
          cong₂ _∷_ (frame-fusion-gen Fr Vϕ Vξ Vϕξ) (F*-fuse-local E' Vϕ Vξ Vϕξ)
        subst-frame*-⋯ : ∀ {a c} (eq : a ≡ c) (E' : Frame* dom) {σ : dom →ₛ a}
                         (Vσ : VSub σ) (Vσ' : VSub (subst (λ z → dom →ₛ z) eq σ)) →
                         subst (λ z → Frame* z) eq (frame*-⋯ E' σ Vσ)
                         ≡ frame*-⋯ E' (subst (λ z → dom →ₛ z) eq σ) Vσ'
        subst-frame*-⋯ refl E' Vσ Vσ' = frame*-cong E' Vσ Vσ' (λ _ → refl)
        Vsp : VSub sPre
        Vsp i = subst Value (sym (sPre-pt i))
          (value-⋯ (value-⋯ (value-⋯ (value-⋯ (Value-subst eqC (Vτ i))
            ρa (λ _ → V-`)) ρb (λ _ → V-`)) ρc (λ _ → V-`)) ρd (λ _ → V-`))
        Vη : VSub η
        Vη i = value-⋯ (V⦅*⦆ i) weakenᵣ (λ _ → V-`)
        Vsη : VSub (sPre ·ₖ η)
        Vsη i = value-⋯ (Vsp i) η Vη
        Vτ̂ : VSub (subst (λ z → dom →ₛ z) eqC τ)
        Vτ̂ i = subst Value (sym (subst-cod-ptR eqC τ i)) (Value-subst eqC (Vτ i))
        Va : VSub ((subst (λ z → dom →ₛ z) eqC τ) ·ₖ ρa)
        Va = ·ₖ-VSubₛ Vτ̂ ρa
        Vab : VSub (((subst (λ z → dom →ₛ z) eqC τ) ·ₖ ρa) ·ₖ ρb)
        Vab = ·ₖ-VSubₛ Va ρb
        Vabc : VSub ((((subst (λ z → dom →ₛ z) eqC τ) ·ₖ ρa) ·ₖ ρb) ·ₖ ρc)
        Vabc = ·ₖ-VSubₛ Vab ρc
        FoutE : Fout ≡ frame*-⋯ E sPre Vsp
        FoutE =
            cong (λ F → F ⋯ᶠ* ρa ⋯ᶠ* ρb ⋯ᶠ* ρc ⋯ᶠ* ρd) (subst-frame*-⋯ eqC E Vτ Vτ̂)
          ■ cong (λ F → F ⋯ᶠ* ρb ⋯ᶠ* ρc ⋯ᶠ* ρd) (F-σ⋯ E Vτ̂ ρa Va)
          ■ cong (λ F → F ⋯ᶠ* ρc ⋯ᶠ* ρd) (F-σ⋯ E Va ρb Vab)
          ■ cong (λ F → F ⋯ᶠ* ρd) (F-σ⋯ E Vab ρc Vabc)
          ■ F-σ⋯ E Vabc ρd Vsp
        avoidcong : (ρ⁻ ·ₖ (sPre ·ₖ η)) ≗ (ρ⁻ ·ₖ sPre)
        avoidcong y = sym (fusion (sPre (ρ⁻ y)) ⦅ * ⦆ₛ weakenᵣ) ■ avoid (ρ⁻ y) (ρ⁻≢0 y)
    eout≡ : eout ≡ wk ebase
    eout≡ = sym ( cong (λ z → z ⋯ ⦅ * ⦆ₛ ⋯ weakenᵣ) eout-eq
                ■ avoid-ren tcc′ ρeout ρeout≢0
                ■ sym eout-eq )
      where
        ρ0 : (sC + (2 + n)) →ᵣ suc (sC + (2 + n))
        ρ0 = castᵣ (+-suc sC (2 + n)) (weakenᵣ ↑* sC)
        ρ1 : (sC + (2 + n)) →ᵣ (sB₂ + (sC + (3 + n)))
        ρ1 = castᵣ eqC (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)
        ρ1a : (sC + (2 + n)) →ᵣ _
        ρ1a = ρ1 ·ₖ ρa
        ρW : (sC + (2 + n)) →ᵣ _
        ρW = ρ1a ·ₖ ρb
        ρW≢0 : ∀ x → ρW x ≢ 0F
        ρW≢0 x eq0 = abs (subst (1 Nat.≤_) (cong Fin.toℕ eq0) posℕ)
          where
            abs : 1 Nat.≤ 0 → ⊥
            abs ()
            pv1 : ℕ
            pv1 = Fin.toℕ ((weakenᵣ ↑* sC) x)
            tρ1 : Fin.toℕ (ρ1 x) ≡ sB₂ + pv1
            tρ1 = toℕ-castᵣ eqC (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) x
                ■ toℕ-weaken*ᵣ sB₂ (ρ0 x)
                ■ cong (sB₂ +_) (toℕ-castᵣ (+-suc sC (2 + n)) (weakenᵣ ↑* sC) x)
            geB : sB₂ Nat.≤ Fin.toℕ (ρ1 x)
            geB = subst (sB₂ Nat.≤_) (sym tρ1) (Nat.m≤m+n sB₂ pv1)
            redB : Fin.toℕ (Fin.reduce≥ (ρ1 x) geB) ≡ pv1
            redB = toℕ-reduce≥ (ρ1 x) geB ■ cong (Nat._∸ sB₂) tρ1 ■ Nat.m+n∸m≡n sB₂ pv1
            tρa : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB))
            tρa = toℕ-↑*-ge (assocSwapᵣ sC 1) sB₂ (ρ1 x) geB
            1≤sB₂+1+ : ∀ k → 1 Nat.≤ sB₂ + (1 + k)
            1≤sB₂+1+ k = Nat.≤-trans (Nat.m≤n+m 1 sB₂) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n 1 k))
            geCase : sC Nat.≤ Fin.toℕ x → 1 Nat.≤ Fin.toℕ (ρW x)
            geCase gex = subst (1 Nat.≤_) (sym tρW)
                           (Nat.≤-trans (Nat.≤-trans (Nat.m≤n+m 1 sC) sC+1≤pv1) (Nat.m≤n+m pv1 sB₂))
              where
                pv1eq : pv1 ≡ sC + (1 + Fin.toℕ (Fin.reduce≥ x gex))
                pv1eq = toℕ-↑*-ge weakenᵣ sC x gex
                      ■ cong (sC +_) (toℕ-weaken*ᵣ 1 (Fin.reduce≥ x gex))
                sC+1≤pv1 : sC + 1 Nat.≤ pv1
                sC+1≤pv1 = subst (sC + 1 Nat.≤_) (sym pv1eq) (Nat.+-monoʳ-≤ sC (Nat.m≤m+n 1 _))
                tassoc : Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB)) ≡ pv1
                tassoc = toℕ-assoc-ge sC 1 (Fin.reduce≥ (ρ1 x) geB)
                           (subst (sC + 1 Nat.≤_) (sym redB) sC+1≤pv1)
                       ■ redB
                tρaC : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + pv1
                tρaC = tρa ■ cong (sB₂ +_) tassoc
                geAB : sB₂ + 1 Nat.≤ Fin.toℕ (ρa (ρ1 x))
                geAB = subst (sB₂ + 1 Nat.≤_) (sym tρaC)
                         (Nat.+-monoʳ-≤ sB₂ (Nat.≤-trans (Nat.m≤n+m 1 sC) sC+1≤pv1))
                tρW : Fin.toℕ (ρW x) ≡ sB₂ + pv1
                tρW = toℕ-assoc-ge sB₂ 1 (ρa (ρ1 x)) geAB ■ tρaC
            posℕ : 1 Nat.≤ Fin.toℕ (ρW x)
            posℕ with Nat.<-cmp (Fin.toℕ x) sC
            ... | tri< ltx _ _ = subst (1 Nat.≤_) (sym tρW) (1≤sB₂+1+ pv1)
              where
                pv1lt : pv1 Nat.< sC
                pv1lt = subst (Nat._< sC) (sym (toℕ-↑*-lt weakenᵣ sC x ltx)) ltx
                tassoc : Fin.toℕ (assocSwapᵣ sC 1 (Fin.reduce≥ (ρ1 x) geB)) ≡ 1 + pv1
                tassoc = toℕ-assoc-lt sC 1 (Fin.reduce≥ (ρ1 x) geB)
                           (subst (Nat._< sC) (sym redB) pv1lt)
                       ■ cong (1 +_) redB
                tρaC : Fin.toℕ (ρa (ρ1 x)) ≡ sB₂ + (1 + pv1)
                tρaC = tρa ■ cong (sB₂ +_) tassoc
                geAB : sB₂ + 1 Nat.≤ Fin.toℕ (ρa (ρ1 x))
                geAB = subst (sB₂ + 1 Nat.≤_) (sym tρaC) (Nat.+-monoʳ-≤ sB₂ (Nat.m≤m+n 1 pv1))
                tρW : Fin.toℕ (ρW x) ≡ sB₂ + (1 + pv1)
                tρW = toℕ-assoc-ge sB₂ 1 (ρa (ρ1 x)) geAB ■ tρaC
            ... | tri≈ _ eqx _ = geCase (Nat.≤-reflexive (sym eqx))
            ... | tri> _ _ gtx = geCase (Nat.<⇒≤ gtx)
        tcc′ : Tm (sC + (2 + n))
        tcc′ = proj₁ (tc-factors-gen {suc n} b₁ B₁)
        tc-eq : tcc ≡ tcc′ ⋯ (weakenᵣ ↑* sC)
        tc-eq = proj₂ (tc-factors-gen {suc n} b₁ B₁)
        ρWc : (sC + (2 + n)) →ᵣ _
        ρWc = ρW ·ₖ ρc
        ρeout : (sC + (2 + n)) →ᵣ _
        ρeout = ρWc ·ₖ ρd
        ρeout≢0 : ∀ x → ρeout x ≢ 0F
        ρeout≢0 x = ↑≢0 (assocSwapᵣ sB₂ 2) (ρWc x)
                      (↑≢0 (assocSwapᵣ sC 2 ↑* sB₂) (ρW x) (ρW≢0 x))
        Weq-analog : subst Tm eqC (subst Tm e₀ tcc ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb ≡ tcc′ ⋯ ρW
        Weq-analog =
            cong (λ z → subst Tm eqC (subst Tm e₀ z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb) tc-eq
          ■ cong (λ z → subst Tm eqC (z ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ⋯ ρa ⋯ ρb)
              (sym (subst-⋯-cod-local e₀ tcc′ (weakenᵣ ↑* sC)))
          ■ cong (λ z → subst Tm eqC z ⋯ ρa ⋯ ρb) (fusion tcc′ ρ0 (weaken* ⦃ Kᵣ ⦄ sB₂))
          ■ cong (λ z → z ⋯ ρa ⋯ ρb) (sym (subst-⋯-cod-local eqC tcc′ (ρ0 ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)))
          ■ cong (_⋯ ρb) (fusion tcc′ ρ1 ρa)
          ■ fusion tcc′ ρ1a ρb
        eout-eq : eout ≡ tcc′ ⋯ ρeout
        eout-eq =
            cong (λ z → z ⋯ ρc ⋯ ρd) Weq-analog
          ■ cong (_⋯ ρd) (fusion tcc′ ρW ρc)
          ■ fusion tcc′ ρWc ρd
    avoid⁻ : ((sPre⁻ ·ₖ ⦅ * ⦆ₛ) ·ₖ weakenᵣ) ≗ sPre⁻
    avoid⁻ y = avoid (ρ⁻ y) (ρ⁻≢0 y)
    Qout≡w : Qout ≡ Qbase U.⋯ₚ weakenᵣ
    Qout≡w = sym
      ( cong (λ z → (z U.⋯ₚ ⦅ * ⦆ₛ) U.⋯ₚ weakenᵣ) QoutP₀
      ■ cong (U._⋯ₚ weakenᵣ) (U-σ⋯ₛ P₀ {σ = sPre⁻} {τ = ⦅ * ⦆ₛ})
      ■ U-σ⋯ P₀ {σ = sPre⁻ ·ₖ ⦅ * ⦆ₛ} {ρ = weakenᵣ}
      ■ U-cong P₀ avoid⁻
      ■ sym QoutP₀ )
    in-eq : U.ν (U.φ U.acq (U.⟪ (Fbase ⋯ᶠ* weakenᵣ) [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ wk ebase) ]* ⟫ U.∥ (Qbase U.⋯ₚ weakenᵣ)))
            ≡ U.ν (U.φ U.acq LL₃)
    in-eq =
        cong (λ F → U.ν (U.φ U.acq (U.⟪ F [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ wk ebase) ]* ⟫ U.∥ (Qbase U.⋯ₚ weakenᵣ)))) (sym Fout≡)
      ■ cong (λ e → U.ν (U.φ U.acq (U.⟪ Fout [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ e) ]* ⟫ U.∥ (Qbase U.⋯ₚ weakenᵣ)))) (sym eout≡)
      ■ cong (λ Q → U.ν (U.φ U.acq (U.⟪ Fout [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ eout) ]* ⟫ U.∥ Q))) (sym Qout≡w)
      ■ cong (λ z → U.ν (U.φ U.acq z)) (sym redexL)
    out-eq : U.ν (U.⟪ Fbase [ (* ⊗ (` 0F)) ⊗ ebase ]* ⟫ U.∥ Qbase) ≡ U.ν leaf′
    out-eq = cong U.ν (cong₂ U._∥_ (cong U.⟪_⟫ (sym (frame-plug* Fout ⦅ * ⦆ₛ V⦅*⦆))) refl)
    leaf-part : U.ν (U.φ U.acq LL₃) UR─→ₚ* U.ν leaf′
    leaf-part = subst₂ _UR─→ₚ*_ in-eq out-eq (leaf-fire Fbase {ebase} Qbase)
    fire : mid UR─→ₚ* fired
    fire = Bφ-fire C (Bφ-fire B₂ leaf-part)
    back : fired U.≋ U[ T.ν C B₂ QR ] σ
    back =
         Bφ-cong C (Bφ-past-ν B₂ leaf′)
      ◅◅ Bφ-past-ν C (Bφ B₂ (leaf′ U.⋯ₚ assocSwapᵣ 2 sB₂))
      ◅◅ U.ν-cong (Bφ-cong C (≡→≋ (Bφ-⋯ B₂ (leaf′ U.⋯ₚ assocSwapᵣ 2 sB₂) (assocSwapᵣ 2 sC))))
      ◅◅ U.ν-cong (Bφ-cong C (Bφ-cong B₂ (≡→≋ leafReconcile)))
      ◅◅ ≡→≋ (sym (Uν-flat σ C B₂ QR))
