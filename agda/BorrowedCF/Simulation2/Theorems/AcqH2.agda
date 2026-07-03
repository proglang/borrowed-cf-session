module BorrowedCF.Simulation2.Theorems.AcqH2 where

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
        ; toℕ-weaken*ᵣ; weaken*ᵣ~↑ʳ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid; toℕ-assoc-ge; toℕ-assoc-lt; toℕ-↑
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

open import BorrowedCF.Simulation2.Theorems.AcqH1 public

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

-- ν (φ acq (⟪ F[acq · 𝓒[`0F × 1F × e]] ⟫ ∥ Q)) fires the merged RU-Acquire
-- (acq→gone) directly, yielding ν ((⟪ F[𝓒[`0F×1F×e]] ⟫ ∥ Q) ⋯ₚ ⦅*⦆ₛ).
leaf-fire : (F : Frame* (3 + n)) {e : Tm (3 + n)} (Q : U.Proc (3 + n)) →
  U.ν (U.φ U.acq (U.⟪ F [ K `acq ·¹ (((` 0F) ⊗ (` 1F)) ⊗ e) ]* ⟫ U.∥ Q))
    UR─→ₚ*
  U.ν ((U.⟪ F [ ((` 0F) ⊗ (` 1F)) ⊗ e ]* ⟫ U.∥ Q) U.⋯ₚ ⦅ * ⦆ₛ)
leaf-fire F {e} Q = UR.RU-Acquire F ◅ ε

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

-- Flag-parametric core of the variable-base transpose (after the ⦅*⦆ₛ
-- commutation decomposition).  The head endpoint ` 0F collapses to * and the
-- junction flag drops from (suc x) to x.  Proven by recursion on the group.
core-gen : ∀ {n} (D : BindGroup) (sB₂ : ℕ) (x : 𝔽 (2 + n)) (j : 𝔽 (sum D)) →
    subst Tm (cong (sB₂ +_) (sym (+-suc (syncs D) (suc (suc n)))))
      (subst Tm (+-suc (syncs D) (suc (suc n))) (canonₛ D (` 0F , suc x , K `unit) j) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
    ⋯ (assocSwapᵣ (syncs D) 1 {2 + n} ↑* sB₂)
    ⋯ assocSwapᵣ sB₂ 1 {syncs D + (2 + n)}
    ⋯ ⦅ K `unit ⦆ₛ
  ≡ canonₛ D (K `unit , x , K `unit) j ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
core-gen {n} D sB₂ x j =
    step1
  ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
      (canonₛ-natₛ D (` 0F) (suc x) (K `unit) ⦅ K `unit ⦆ₛ x refl j)
  where
    cD : Tm (syncs D + (3 + n))
    cD = canonₛ D (` 0F , suc x , K `unit) j
    sD : ℕ
    sD = syncs D
    ρa = assocSwapᵣ sD 1 {2 + n} ↑* sB₂
    ρb = assocSwapᵣ sB₂ 1 {sD + (2 + n)}
    ss : ∀ {A B} (p : A ≡ B) (t : Tm A) → subst Tm (sym p) (subst Tm p t) ≡ t
    ss refl t = refl
    sWk : ∀ {A B} (e : A ≡ B) (u : Tm A) →
          subst Tm (cong (sB₂ +_) e) (u ⋯ weaken* ⦃ Kᵣ ⦄ sB₂) ≡ subst Tm e u ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    sWk refl u = refl
    aS = assocSwapᵣ sD 1 {2 + n}
    varˢ : ∀ {mm pp} (σ : mm →ₛ pp) (x : 𝔽 mm) → σ x ≡ (` x) ⋯ σ
    varˢ σ x = sym (⋯-var x σ)
    varʳ : ∀ {mm pp} (ρ : mm →ᵣ pp) (x : 𝔽 mm) → (` x) ⋯ ρ ≡ ` (ρ x)
    varʳ ρ x = ⋯-var x ρ
    swap-collapse : (aS ·ₖ ⦅ K `unit ⦆ₛ) ≗ (⦅ K `unit ⦆ₛ ↑* sD)
    swap-collapse i = lhsS i ■ coreS i
      where
        wk-⋯-weaken : ∀ {aa} (t : Tm aa) (m : ℕ) →
                      wk ⦃ Kₛ ⦄ (t ⋯ weaken* ⦃ Kᵣ ⦄ m) ≡ t ⋯ weaken* ⦃ Kᵣ ⦄ (suc m)
        wk-⋯-weaken t m = fusion t (weaken* ⦃ Kᵣ ⦄ m) (weaken ⦃ Kᵣ ⦄) ■ ⋯-cong t (λ _ → refl)
        ↑*ˡ : ∀ {mm pp} (ϕ : mm →ₛ pp) (m : ℕ) (x : 𝔽 m) → (ϕ ↑* m) (x ↑ˡ mm) ≡ ` (x ↑ˡ pp)
        ↑*ˡ ϕ (suc m) zero    = refl
        ↑*ˡ ϕ (suc m) (suc x) = cong (wk ⦃ Kₛ ⦄) (↑*ˡ ϕ m x) ■ ⋯-var (x ↑ˡ _) (weaken ⦃ Kᵣ ⦄)
        ↑*ʳ : ∀ {mm pp} (ϕ : mm →ₛ pp) (m : ℕ) (y : 𝔽 mm) → (ϕ ↑* m) (m ↑ʳ y) ≡ (ϕ y) ⋯ weaken* ⦃ Kᵣ ⦄ m
        ↑*ʳ ϕ zero    y = sym (⋯-id (ϕ y) (λ _ → refl))
        ↑*ʳ ϕ (suc m) y = cong (wk ⦃ Kₛ ⦄) (↑*ʳ ϕ m y) ■ wk-⋯-weaken (ϕ y) m
        lhsS : (j : 𝔽 (sD + (3 + n))) → (aS ·ₖ ⦅ K `unit ⦆ₛ) j ≡ ⦅ K `unit ⦆ₛ (aS j)
        lhsS j =
            varˢ (aS ·ₖ ⦅ K `unit ⦆ₛ) j
          ■ sym (fusion (` j) aS ⦅ K `unit ⦆ₛ)
          ■ cong (_⋯ ⦅ K `unit ⦆ₛ) (varʳ aS j)
          ■ ⋯-var (aS j) ⦅ K `unit ⦆ₛ
        coreS : (j : 𝔽 (sD + (3 + n))) → ⦅ K `unit ⦆ₛ (aS j) ≡ (⦅ K `unit ⦆ₛ ↑* sD) j
        coreS j with Fin.splitAt sD j in eq
        ... | inj₁ x = sym (cong (⦅ K `unit ⦆ₛ ↑* sD) iform ■ ↑*ˡ ⦅ K `unit ⦆ₛ sD x)
          where iform : j ≡ x ↑ˡ (3 + n)
                iform = sym (Fin.join-splitAt sD (3 + n) j) ■ cong (Fin.join sD (3 + n)) eq
        ... | inj₂ zero = sym (cong (⦅ K `unit ⦆ₛ ↑* sD) iform ■ ↑*ʳ ⦅ K `unit ⦆ₛ sD (zero {2 + n}))
          where iform : j ≡ sD ↑ʳ (zero {2 + n})
                iform = sym (Fin.join-splitAt sD (3 + n) j) ■ cong (Fin.join sD (3 + n)) eq
        ... | inj₂ (suc z) =
            sym ( cong (⦅ K `unit ⦆ₛ ↑* sD) iform
                ■ ↑*ʳ ⦅ K `unit ⦆ₛ sD (suc z)
                ■ varʳ (weaken* ⦃ Kᵣ ⦄ sD) z
                ■ cong `_ (weaken*ᵣ~↑ʳ sD z) )
          where iform : j ≡ sD ↑ʳ (suc z)
                iform = sym (Fin.join-splitAt sD (3 + n) j) ■ cong (Fin.join sD (3 + n)) eq
    wk-swap-collapse : ((weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ρb) ·ₖ ⦅ K `unit ⦆ₛ)
                       ≗ (⦅ K `unit ⦆ₛ ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂)
    wk-swap-collapse v = lhsW v ■ coreW v ■ sym (rhsW v)
      where
        lhsW : (w : 𝔽 (suc (sD + (2 + n)))) →
               ((weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ρb) ·ₖ ⦅ K `unit ⦆ₛ) w
               ≡ ⦅ K `unit ⦆ₛ (ρb (weaken* ⦃ Kᵣ ⦄ sB₂ w))
        lhsW w =
            varˢ ((weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ρb) ·ₖ ⦅ K `unit ⦆ₛ) w
          ■ sym (fusion (` w) (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ρb) ⦅ K `unit ⦆ₛ)
          ■ cong (_⋯ ⦅ K `unit ⦆ₛ) (sym (fusion (` w) (weaken* ⦃ Kᵣ ⦄ sB₂) ρb))
          ■ cong (λ z → z ⋯ ρb ⋯ ⦅ K `unit ⦆ₛ) (varʳ (weaken* ⦃ Kᵣ ⦄ sB₂) w)
          ■ cong (_⋯ ⦅ K `unit ⦆ₛ) (varʳ ρb (weaken* ⦃ Kᵣ ⦄ sB₂ w))
          ■ ⋯-var (ρb (weaken* ⦃ Kᵣ ⦄ sB₂ w)) ⦅ K `unit ⦆ₛ
        rhsW : (w : 𝔽 (suc (sD + (2 + n)))) →
               (⦅ K `unit ⦆ₛ ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) w ≡ (⦅ K `unit ⦆ₛ w) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        rhsW w =
            varˢ (⦅ K `unit ⦆ₛ ·ₖ weaken* ⦃ Kᵣ ⦄ sB₂) w
          ■ sym (fusion (` w) ⦅ K `unit ⦆ₛ (weaken* ⦃ Kᵣ ⦄ sB₂))
          ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (⋯-var w ⦅ K `unit ⦆ₛ)
        coreW : (w : 𝔽 (suc (sD + (2 + n)))) →
                ⦅ K `unit ⦆ₛ (ρb (weaken* ⦃ Kᵣ ⦄ sB₂ w)) ≡ (⦅ K `unit ⦆ₛ w) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
        coreW zero = cong ⦅ K `unit ⦆ₛ pf0
          where
            toℕW0 : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (zero {sD + (2 + n)})) ≡ sB₂
            toℕW0 = toℕ-weaken*ᵣ sB₂ (zero {sD + (2 + n)}) ■ Nat.+-identityʳ sB₂
            pf0 : ρb (weaken* ⦃ Kᵣ ⦄ sB₂ (zero {sD + (2 + n)})) ≡ zero
            pf0 = Fin.toℕ-injective
              ( toℕ-assoc-mid sB₂ 1 (weaken* ⦃ Kᵣ ⦄ sB₂ zero)
                  (Nat.≤-reflexive (sym toℕW0))
                  (subst (Nat._< sB₂ + 1) (sym toℕW0) (Nat.≤-reflexive (sym (Nat.+-comm sB₂ 1))))
              ■ cong (Nat._∸ sB₂) toℕW0 ■ Nat.n∸n≡0 sB₂ )
        coreW (suc k) = cong ⦅ K `unit ⦆ₛ pfS
          where
            toℕWs : Fin.toℕ (weaken* ⦃ Kᵣ ⦄ sB₂ (suc k)) ≡ suc (sB₂ + Fin.toℕ k)
            toℕWs = toℕ-weaken*ᵣ sB₂ (suc k) ■ Nat.+-suc sB₂ (Fin.toℕ k)
            pfS : ρb (weaken* ⦃ Kᵣ ⦄ sB₂ (suc k)) ≡ suc (weaken* ⦃ Kᵣ ⦄ sB₂ k)
            pfS = Fin.toℕ-injective
              ( toℕ-assoc-ge sB₂ 1 (weaken* ⦃ Kᵣ ⦄ sB₂ (suc k))
                  (subst (sB₂ + 1 Nat.≤_) (sym toℕWs)
                    (Nat.≤-trans (Nat.≤-reflexive (Nat.+-comm sB₂ 1))
                                 (Nat.s≤s (Nat.m≤m+n sB₂ (Fin.toℕ k)))))
              ■ toℕWs ■ cong suc (sym (toℕ-weaken*ᵣ sB₂ k)) )
    pure : cD ⋯ weaken* ⦃ Kᵣ ⦄ sB₂ ⋯ ρa ⋯ ρb ⋯ ⦅ K `unit ⦆ₛ
           ≡ cD ⋯ (⦅ K `unit ⦆ₛ ↑* sD) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    pure =
        cong (λ z → z ⋯ ρb ⋯ ⦅ K `unit ⦆ₛ) (sym (⋯-↑*-wk cD aS sB₂))
      ■ cong (_⋯ ⦅ K `unit ⦆ₛ) (fusion (cD ⋯ aS) (weaken* ⦃ Kᵣ ⦄ sB₂) ρb)
      ■ fusion (cD ⋯ aS) (weaken* ⦃ Kᵣ ⦄ sB₂ ·ₖ ρb) ⦅ K `unit ⦆ₛ
      ■ ⋯-cong (cD ⋯ aS) wk-swap-collapse
      ■ sym (fusion (cD ⋯ aS) ⦅ K `unit ⦆ₛ (weaken* ⦃ Kᵣ ⦄ sB₂))
      ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
          (fusion cD aS ⦅ K `unit ⦆ₛ ■ ⋯-cong cD swap-collapse)
    step1 : subst Tm (cong (sB₂ +_) (sym (+-suc (syncs D) (suc (suc n)))))
              (subst Tm (+-suc (syncs D) (suc (suc n))) cD ⋯ weaken* ⦃ Kᵣ ⦄ sB₂)
            ⋯ (assocSwapᵣ (syncs D) 1 {2 + n} ↑* sB₂)
            ⋯ assocSwapᵣ sB₂ 1 {syncs D + (2 + n)}
            ⋯ ⦅ K `unit ⦆ₛ
          ≡ cD ⋯ (⦅ K `unit ⦆ₛ ↑* syncs D) ⋯ weaken* ⦃ Kᵣ ⦄ sB₂
    step1 = cong (λ z → z ⋯ ρa ⋯ ρb ⋯ ⦅ K `unit ⦆ₛ)
              ( sWk (sym (+-suc sD (suc (suc n)))) (subst Tm (+-suc sD (suc (suc n))) cD)
              ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ sB₂) (ss (+-suc sD (suc (suc n))) cD) )
          ■ pure

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
    core = core-gen Cg sB₂ 0F j

