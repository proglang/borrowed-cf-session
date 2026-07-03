module BorrowedCF.Simulation.RevComImage where

-- N2 for the reverse RU-Com case: a νσ-IMAGE INVERSION.
--
-- νσ b₁ b₂ σ maps block-1 indices → chanTriple(*,0F,*), block-2 indices →
-- chanTriple(*,1F,*), and the m-region → σ-values shifted by 2.  Hence a value
-- of the send channel that equals chanTriple(*,0F,*) MUST come from block-1.
-- `com-image-block1` reads that off, producing b₁ ≡ suc b₁', a block-1 position
-- z₀ : 𝔽 (suc b₁'), and the exact handle shape ((z₀ ↑ˡ 0) ↑ˡ (b₂+0)) ↑ˡ m that
-- count-handle-comᴸ / before-com-binderᴸ expect.

open import BorrowedCF.Simulation.Base
open import BorrowedCF.Simulation.ReverseInv using (νσ; ⊗-inj)

open import Data.Fin.Base using (join; _↑ʳ_)
open import Data.Fin.Properties using (join-splitAt; toℕ-↑ˡ; toℕ-cast; toℕ-injective; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)

-- The three-renaming shift the σ-region applies to each σ-value.
shift2 : Tm n → Tm (2 + n)
shift2 t = t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ 0 ⋯ weaken* ⦃ Kᵣ ⦄ 0

-- A shifted value cannot be the bare variable 0F (its vars are all ≥ 2F).
σreg-var : {t : Tm n} → Value t → shift2 t ≡ ` 0F → ⊥
σreg-var V-` ()
σreg-var V-K ()
σreg-var V-λ ()
σreg-var (V-⊗ _ _) ()
σreg-var (V-⊕ _) ()

-- A shifted value cannot be a pair whose right component is 0F.
σreg-pair : {t : Tm n} → Value t → ∀ {a : Tm (2 + n)} → shift2 t ≡ a ⊗ (` 0F) → ⊥
σreg-pair V-` ()
σreg-pair V-K ()
σreg-pair V-λ ()
σreg-pair (V-⊕ _) ()
σreg-pair (V-⊗ V₁ V₂) eq = σreg-var V₂ (proj₂ (⊗-inj eq))

-- A shifted value cannot be a chanTriple with middle channel 0F.
σreg-mid : {t : Tm n} → Value t → ∀ {a b : Tm (2 + n)}
         → shift2 t ≡ (a ⊗ (` 0F)) ⊗ b → ⊥
σreg-mid V-` ()
σreg-mid V-K ()
σreg-mid V-λ ()
σreg-mid (V-⊕ _) ()
σreg-mid (V-⊗ V₁ V₂) eq = σreg-pair V₁ (proj₁ (⊗-inj eq))

-- Every Ub-block entry is a chanTriple with the SAME middle channel c.
Ub-chanTriple : ∀ {N} b (e₁ : Tm N) (c : 𝔽 N) (e₂ : Tm N) (v : 𝔽 b)
              → Σ[ a ∈ Tm N ] Σ[ d ∈ Tm N ] Ub[ b ] (e₁ , c , e₂) v ≡ chanTriple (a , c , d)
Ub-chanTriple (suc zero)    e₁ c e₂ 0F      = e₁ , e₂ , refl
Ub-chanTriple (suc (suc b)) e₁ c e₂ 0F      = e₁ , _  , refl
Ub-chanTriple (suc (suc b)) e₁ c e₂ (suc v) = Ub-chanTriple (suc b) _ c e₂ v

-- A block-2 entry has middle channel 1F, so it is not chanTriple(*,0F,*).
block2-refute : ∀ b (v : 𝔽 (b + 0)) {a b′ : Tm (2 + n)}
              → chanTriple (a , 0F , b′) ≡ Ub[ b + 0 ] (* , weaken* ⦃ Kᵣ ⦄ 0 1F , *) v → ⊥
block2-refute b v ceq
  with a₀ , d₀ , ueq ← Ub-chanTriple (b + 0) * (weaken* ⦃ Kᵣ ⦄ 0 1F) * v
  with () ← proj₂ (⊗-inj (proj₁ (⊗-inj (ceq ■ ueq))))

-- A positive nat is a successor (to refine b₁ for the suc-indexed binder lemmas).
pos⇒suc : ∀ {b} → 1 Nat.≤ b → Σ[ b' ∈ ℕ ] b ≡ suc b'
pos⇒suc {suc b'} _ = b' , refl

-- The N2 lemma: block-1 image inversion, in the CLEAN count-handle form —
-- z : 𝔽 (b₁ + 0) with xS ≡ (z ↑ˡ (b₂+0)) ↑ˡ m (exactly count-handle-comᴸ's
-- handle), plus 1 ≤ b₁.  No subst / no b₁-refinement in the type.
com-image-block1 : ∀ {m n : ℕ} (b₁ b₂ : ℕ) (σ : m →ₛ n) (Vσ : VSub σ)
  (xS : 𝔽 (b₁ + 0 + (b₂ + 0) + m)) {e₁ e₁′ : Tm (2 + n)}
  → chanTriple (e₁ , 0F , e₁′) ≡ (` xS) ⋯ νσ b₁ b₂ σ
  → Σ[ z ∈ 𝔽 (b₁ + 0) ] (1 Nat.≤ b₁) × (xS ≡ (z ↑ˡ (b₂ + 0)) ↑ˡ m)
com-image-block1 {m} (suc b₁') b₂ σ Vσ xS {e₁} {e₁′} ceq
  with Fin.splitAt (suc b₁' + 0 + (b₂ + 0)) xS in seq
... | inj₂ i = ⊥-elim (σreg-mid (Vσ i) (sym ceq))
... | inj₁ w
  with Fin.splitAt (suc b₁' + 0) w in weq
...   | inj₂ v = ⊥-elim (block2-refute b₂ v ceq)
...   | inj₁ u = u , Nat.s≤s Nat.z≤n , xSeq
  where
    xS≡w↑ : xS ≡ w ↑ˡ m
    xS≡w↑ = sym (join-splitAt (suc b₁' + 0 + (b₂ + 0)) m xS) ■ cong (join _ m) seq
    w≡u↑ : w ≡ u ↑ˡ (b₂ + 0)
    w≡u↑ = sym (join-splitAt (suc b₁' + 0) (b₂ + 0) w) ■ cong (join _ (b₂ + 0)) weq
    xSeq : xS ≡ (u ↑ˡ (b₂ + 0)) ↑ˡ m
    xSeq = xS≡w↑ ■ cong (_↑ˡ m) w≡u↑
com-image-block1 zero b₂ σ Vσ xS ceq
  with Fin.splitAt (zero + 0 + (b₂ + 0)) xS in seq
... | inj₂ i = ⊥-elim (σreg-mid (Vσ i) (sym ceq))
... | inj₁ v = ⊥-elim (block2-refute b₂ v ceq)

-- ── recv-side (block-2, middle 1F) mirror of the send-side above ──────────────

-- 1F variants of the σ-region refuters (a shifted value's vars are all ≥ 2F).
σreg-var1 : {t : Tm n} → Value t → shift2 t ≡ ` 1F → ⊥
σreg-var1 V-` ()
σreg-var1 V-K ()
σreg-var1 V-λ ()
σreg-var1 (V-⊗ _ _) ()
σreg-var1 (V-⊕ _) ()

σreg-pair1 : {t : Tm n} → Value t → ∀ {a : Tm (2 + n)} → shift2 t ≡ a ⊗ (` 1F) → ⊥
σreg-pair1 V-` ()
σreg-pair1 V-K ()
σreg-pair1 V-λ ()
σreg-pair1 (V-⊕ _) ()
σreg-pair1 (V-⊗ V₁ V₂) eq = σreg-var1 V₂ (proj₂ (⊗-inj eq))

σreg-mid1 : {t : Tm n} → Value t → ∀ {a b : Tm (2 + n)}
          → shift2 t ≡ (a ⊗ (` 1F)) ⊗ b → ⊥
σreg-mid1 V-` ()
σreg-mid1 V-K ()
σreg-mid1 V-λ ()
σreg-mid1 (V-⊕ _) ()
σreg-mid1 (V-⊗ V₁ V₂) eq = σreg-pair1 V₁ (proj₁ (⊗-inj eq))

-- A block-1 entry has middle channel 0F, so it is not chanTriple(*,1F,*).
block1-refute : ∀ b (u : 𝔽 (b + 0)) {a b′ : Tm (2 + n)}
              → chanTriple (a , 1F , b′) ≡ Ub[ b + 0 ] (* , 0F , *) u ⋯ weaken* ⦃ Kᵣ ⦄ 0 → ⊥
block1-refute b u ceq
  with a₀ , d₀ , ueq ← Ub-chanTriple (b + 0) * 0F * u
  with () ← proj₂ (⊗-inj (proj₁ (⊗-inj (ceq ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ 0) ueq))))

-- recv-image-block2 : the block-2 mirror of com-image-block1 — pins the recv
-- channel xR to block-2 position w : 𝔽 (b₂+0), exposing 1 ≤ b₂, with the flat
-- index xR ≡ ((b₁+0) ↑ʳ w) ↑ˡ m (block-2 injection, R-Com's recv-handle shape).
recv-image-block2 : ∀ {m n : ℕ} (b₁ b₂ : ℕ) (σ : m →ₛ n) (Vσ : VSub σ)
  (xR : 𝔽 (b₁ + 0 + (b₂ + 0) + m)) {e₂ e₂′ : Tm (2 + n)}
  → chanTriple (e₂ , 1F , e₂′) ≡ (` xR) ⋯ νσ b₁ b₂ σ
  → Σ[ w ∈ 𝔽 (b₂ + 0) ] (1 Nat.≤ b₂) × (xR ≡ ((b₁ + 0) ↑ʳ w) ↑ˡ m)
recv-image-block2 {m} b₁ b₂ σ Vσ xR {e₂} {e₂′} ceq
  with Fin.splitAt (b₁ + 0 + (b₂ + 0)) xR in seq
... | inj₂ i = ⊥-elim (σreg-mid1 (Vσ i) (sym ceq))
... | inj₁ w′
  with Fin.splitAt (b₁ + 0) w′ in weq
...   | inj₁ u = ⊥-elim (block1-refute b₁ u ceq)
...   | inj₂ v = v , 1≤b₂ , xReq
  where
    1≤b₂ : 1 Nat.≤ b₂
    1≤b₂ = subst (1 Nat.≤_) (+-identityʳ b₂) (Nat.≤-trans (Nat.s≤s Nat.z≤n) (toℕ<n v))
    xR≡w′↑ : xR ≡ w′ ↑ˡ m
    xR≡w′↑ = sym (join-splitAt (b₁ + 0 + (b₂ + 0)) m xR) ■ cong (join _ m) seq
    w′≡inj : w′ ≡ (b₁ + 0) ↑ʳ v
    w′≡inj = sym (join-splitAt (b₁ + 0) (b₂ + 0) w′) ■ cong (join _ (b₂ + 0)) weq
    xReq : xR ≡ ((b₁ + 0) ↑ʳ v) ↑ˡ m
    xReq = xR≡w′↑ ■ cong (_↑ˡ m) w′≡inj
