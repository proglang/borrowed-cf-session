------------------------------------------------------------------------
-- Chain-level (BindCtx') reshuffling for the two split rules.
--
-- A `BindCtx' s G` is the composition chain of ONE binder group: the vector
-- of handles whose sessions compose to s.  Both split rules replace one entry
-- of such a chain by two adjacent entries.  `Ins T T1 T2 G G'` is the
-- cast-free witness that G' is G with one occurrence of T replaced by the
-- pair T1, T2; the lengths stay heterogeneous on purpose, so that every
-- arithmetic transport at the call site is a plain `subst Ctx eq`.
--
-- `InsR` is the same for R-Split, where the chain is additionally CUT
-- between the two new entries (they end up in different binder groups).
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Chain where

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types

open Nat.Variables
open Fin.Patterns

private variable
  t t₁ t₂ : 𝕊 0
  q : ℕ

------------------------------------------------------------------------
-- Skips bookkeeping

¬skips-seqˡ : ¬ Skips s₁ → ¬ Skips (s₁ ; s₂)
¬skips-seqˡ ¬S (S₁ ; S₂) = ¬S S₁

¬skips-seqʳ : ¬ Skips s₂ → ¬ Skips (s₁ ; s₂)
¬skips-seqʳ ¬S (S₁ ; S₂) = ¬S S₂

¬skips-ret : ¬ Skips (s ; ret)
¬skips-ret (_ ; ())

¬skips-acq : ¬ Skips (acq ; s)
¬skips-acq (() ; _)

------------------------------------------------------------------------
-- Positional agreement of two contexts around an inserted slot.
--
-- `Agree p Γ Γ′` says: Γ′ is Γ with ONE slot inserted so that every entry
-- of Γ at a position other than `p` is still found in Γ′, at the same
-- position when it is below `p` and one further right when it is above.
-- The entry at `p` itself is the one the split rules retype, so it is
-- excluded.  Everything is phrased through `Fin.toℕ`, which is what the
-- `dlwkq` / `drwkq` characterisations of `SplitRenamings.lwk` / `rwk`
-- deliver (see `Simulation.Support.Theorems.SplitsLQ` / `SplitsRQ`).

lookup-toℕ : ∀ {m} (Γ : Ctx m) (i j : 𝔽 m) → Fin.toℕ i ≡ Fin.toℕ j → Γ ﹫ i ≡ Γ ﹫ j
lookup-toℕ Γ i j eq = cong (Γ ﹫_) (Fin.toℕ-injective eq)

Agree : ∀ {m n} → ℕ → Ctx m → Ctx n → Set
Agree {m} {n} p Γ Γ′ = ∀ (j : 𝔽 m) (j′ : 𝔽 n) →
  Fin.toℕ j ≢ p →
  (Fin.toℕ j Nat.< p → Fin.toℕ j′ ≡ Fin.toℕ j) →
  (p Nat.< Fin.toℕ j → Fin.toℕ j′ ≡ suc (Fin.toℕ j)) →
  Γ′ ﹫ j′ ≡ Γ ﹫ j

-- The insertion sits directly after position 0.
agree-here : ∀ {k} {Γr : Ctx k} {T T₁ T₂ : 𝕋} → Agree 0 (T ⸴ Γr) (T₁ ⸴ T₂ ⸴ Γr)
agree-here 0F        j′         ne lo hi = ⊥-elim (ne refl)
agree-here (suc j)   0F         ne lo hi
  with () ← hi (Nat.s≤s Nat.z≤n)
agree-here (suc j)   (suc 0F)   ne lo hi
  with () ← hi (Nat.s≤s Nat.z≤n)
agree-here {Γr = Γr} (suc j) (suc (suc j′)) ne lo hi =
  lookup-toℕ Γr j′ j (suc⁻¹ (suc⁻¹ (hi (Nat.s≤s Nat.z≤n))))

-- One common entry in front shifts the insertion position by one.
agree-suc : ∀ {m n p} {Γ : Ctx m} {Γ′ : Ctx n} (U : 𝕋) →
  Agree p Γ Γ′ → Agree (suc p) (U ⸴ Γ) (U ⸴ Γ′)
agree-suc U A 0F      0F       ne lo hi = refl
agree-suc U A 0F      (suc j′) ne lo hi
  with () ← lo (Nat.s≤s Nat.z≤n)
agree-suc {p = p} U A (suc j) 0F ne lo hi with Nat.<-cmp (Fin.toℕ j) p
... | Bin.tri< lt _ _ with () ← lo (Nat.s≤s lt)
agree-suc {p = p} U A (suc j) 0F ne lo hi | Bin.tri≈ _ eq _ = ⊥-elim (ne (cong suc eq))
agree-suc {p = p} U A (suc j) 0F ne lo hi | Bin.tri> _ _ gt with () ← hi (Nat.s≤s gt)
agree-suc U A (suc j) (suc j′) ne lo hi =
  A j j′ (ne ∘ cong suc) (λ x → suc⁻¹ (lo (Nat.s≤s x))) (λ x → suc⁻¹ (hi (Nat.s≤s x)))

-- Iterated `agree-suc`.
agree-++ˡ : ∀ {m n p b} {Γ : Ctx m} {Γ′ : Ctx n} (Γ₀ : Ctx b) →
  Agree p Γ Γ′ → Agree (b + p) (Γ₀ ⸴* Γ) (Γ₀ ⸴* Γ′)
agree-++ˡ V.[]      A = A
agree-++ˡ (U ⸴ Γ₀) A = agree-suc U (agree-++ˡ Γ₀ A)

------------------------------------------------------------------------
-- One-entry replacement inside a context, cast free.

data Ins (T T₁ T₂ : 𝕋) : ∀ {m n} → Ctx m → Ctx n → Set where
  here  : ∀ {k} {Γr : Ctx k} → Ins T T₁ T₂ (T ⸴ Γr) (T₁ ⸴ T₂ ⸴ Γr)
  there : ∀ {m n} {Γ : Ctx m} {Γ′ : Ctx n} (U : 𝕋) →
          Ins T T₁ T₂ Γ Γ′ → Ins T T₁ T₂ (U ⸴ Γ) (U ⸴ Γ′)

-- Building one: cut the vector open at offset q.
mkIns : ∀ q {k} (Γ : Ctx (q + suc k)) (T₁ T₂ : 𝕋) →
  Σ[ T ∈ 𝕋 ] Σ[ Γ′ ∈ Ctx (q + suc (suc k)) ]
    (Γ ﹫ (q ↑ʳ 0F) ≡ T) × (Γ′ ﹫ (q ↑ʳ 0F) ≡ T₁) × (Γ′ ﹫ (q ↑ʳ 1F) ≡ T₂) × Ins T T₁ T₂ Γ Γ′
    × (∀ {j} (Γr : Ctx j) → Agree q (Γ ⸴* Γr) (Γ′ ⸴* Γr))
mkIns zero    (T ⸴ Γr) T₁ T₂ = T , (T₁ ⸴ T₂ ⸴ Γr) , refl , refl , refl , here , λ _ → agree-here
mkIns (suc q) (U ⸴ Γ)  T₁ T₂ =
  let T , Γ′ , eq , eq₁ , eq₂ , I , A = mkIns q Γ T₁ T₂ in
  T , (U ⸴ Γ′) , eq , eq₁ , eq₂ , there U I , λ Γr → agree-suc U (A Γr)

-- Append an untouched tail on the right.
ins-++ʳ : ∀ {m n k} {Γ : Ctx m} {Γ′ : Ctx n} (Γr : Ctx k) →
  Ins T T₁ T₂ Γ Γ′ → Ins T T₁ T₂ (Γ ⸴* Γr) (Γ′ ⸴* Γr)
ins-++ʳ Γr here        = here
ins-++ʳ Γr (there U I) = there U (ins-++ʳ Γr I)

-- Heads: either the replacement sits at the head, or the head is untouched.
ins-head : ∀ {m n} {Γ : Ctx (suc m)} {Γ′ : Ctx (suc n)} →
  Ins T T₁ T₂ Γ Γ′ → (Γ ﹫ 0F ≡ T × Γ′ ﹫ 0F ≡ T₁) ⊎ (Γ′ ﹫ 0F ≡ Γ ﹫ 0F)
ins-head here        = inj₁ (refl , refl)
ins-head (there U I) = inj₂ refl

------------------------------------------------------------------------
-- L-Split: one ⟨ t₁ ; t₂ ⟩ becomes ⟨ t₁ ⟩, ⟨ t₂ ⟩ in the SAME chain.

chain-lsplit : ∀ {m n} {Γ : Ctx m} {Γ′ : Ctx n} →
  t ≃ t₁ ; t₂ →
  ¬ Skips t₂ →
  Ins (⟨ t ⟩) (⟨ t₁ ⟩) (⟨ t₂ ⟩) Γ Γ′ →
  BindCtx′ s Γ →
  BindCtx′ s Γ′
chain-lsplit teq ¬S₂ here (cons _ w ¬skips eq C) =
  cons _ _ ¬skips
    (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; (≃-sym teq) ≃-refl) eq))
    (cons _ _ (¬skips-seqˡ ¬S₂) ≃-refl C)
chain-lsplit teq ¬S₂ (there _ I) (cons a s′ ¬skips eq C) =
  cons a s′ ¬skips eq (chain-lsplit teq ¬S₂ I C)

------------------------------------------------------------------------
-- R-Split: one ⟨ t₁ ; t₂ ⟩ becomes ⟨ t₁ ; ret ⟩, ⟨ acq ; t₂ ⟩ and the chain
-- is cut between them.

data InsR (T T₁ T₂ : 𝕋) : ∀ {m} → Ctx m → ∀ {n k} → Ctx n → Ctx k → Set where
  here  : ∀ {k} {Γr : Ctx k} → InsR T T₁ T₂ (T ⸴ Γr) (T₁ ⸴ V.[]) (T₂ ⸴ Γr)
  there : ∀ {m n k} {Γ : Ctx m} {Γ₁ : Ctx n} {Γ₂ : Ctx k} (U : 𝕋) →
          InsR T T₁ T₂ Γ Γ₁ Γ₂ → InsR T T₁ T₂ (U ⸴ Γ) (U ⸴ Γ₁) Γ₂

mkInsR : ∀ q {k} (Γ : Ctx (q + suc k)) (T₁ T₂ : 𝕋) →
  Σ[ T ∈ 𝕋 ] Σ[ Γ₁ ∈ Ctx (q + 1) ] Σ[ Γ₂ ∈ Ctx (suc k) ]
    (Γ ﹫ (q ↑ʳ 0F) ≡ T) × (Γ₁ ﹫ (q ↑ʳ 0F) ≡ T₁) × (Γ₂ ﹫ 0F ≡ T₂) × InsR T T₁ T₂ Γ Γ₁ Γ₂
    × (∀ {j} (Γr : Ctx j) → Agree q (Γ ⸴* Γr) (Γ₁ ⸴* (Γ₂ ⸴* Γr)))
mkInsR zero    (T ⸴ Γr) T₁ T₂ = T , (T₁ ⸴ V.[]) , (T₂ ⸴ Γr) , refl , refl , refl , here , λ _ → agree-here
mkInsR (suc q) (U ⸴ Γ)  T₁ T₂ =
  let T , Γ₁ , Γ₂ , eq , eq₁ , eq₂ , I , A = mkInsR q Γ T₁ T₂ in
  T , (U ⸴ Γ₁) , Γ₂ , eq , eq₁ , eq₂ , there U I , λ Γr → agree-suc U (A Γr)

-- Append an untouched tail on the right of the second (new) group.
insR-++ʳ : ∀ {m n k j} {Γ : Ctx m} {Γ₁ : Ctx n} {Γ₂ : Ctx k} (Γr : Ctx j) →
  InsR T T₁ T₂ Γ Γ₁ Γ₂ → InsR T T₁ T₂ (Γ ⸴* Γr) Γ₁ (Γ₂ ⸴* Γr)
insR-++ʳ Γr here        = here
insR-++ʳ Γr (there U I) = there U (insR-++ʳ Γr I)

insR-head : ∀ {m n k} {Γ : Ctx (suc m)} {Γ₁ : Ctx (suc n)} {Γ₂ : Ctx k} →
  InsR T T₁ T₂ Γ Γ₁ Γ₂ → (Γ ﹫ 0F ≡ T × Γ₁ ﹫ 0F ≡ T₁) ⊎ (Γ₁ ﹫ 0F ≡ Γ ﹫ 0F)
insR-head here        = inj₁ (refl , refl)
insR-head (there U I) = inj₂ refl

-- The new group always starts with the acq-headed handle.
insR-acqHead : ∀ {m n k} {Γ : Ctx m} {Γ₁ : Ctx n} {Γ₂ : Ctx k} →
  InsR T T₁ ⟨ acq ; t₂ ⟩ Γ Γ₁ Γ₂ → AcqHeadCtx Γ₂
insR-acqHead here        = _ , ≃-refl
insR-acqHead (there U I) = insR-acqHead I

-- The flattened image of an InsR is an Ins: same vector data, group boundary
-- forgotten.  (Used to relate the two vectors positionally.)
insR-flat : ∀ {m n k} {Γ : Ctx m} {Γ₁ : Ctx n} {Γ₂ : Ctx k} →
  InsR T T₁ T₂ Γ Γ₁ Γ₂ → Ins T T₁ T₂ Γ (Γ₁ ⸴* Γ₂)
insR-flat here        = here
insR-flat (there U I) = there U (insR-flat I)

chain-rsplit : ∀ {t t₁ t₂ : 𝕊 0} {s : 𝕊 0} {m n k} {Γ : Ctx m} {Γ₁ : Ctx n} {Γ₂ : Ctx k} →
  t ≃ t₁ ; t₂ →
  ¬ Skips t₂ →
  InsR (⟨ t ⟩) (⟨ t₁ ; ret ⟩) (⟨ acq ; t₂ ⟩) Γ Γ₁ Γ₂ →
  BindCtx′ s Γ →
  Σ[ u ∈ 𝕊 0 ] Σ[ v ∈ 𝕊 0 ]
      (u ; v ≃ s)
    × ¬ Skips v
    × BindCtx′ (u ; ret) Γ₁
    × BindCtx′ (acq ; v) Γ₂
chain-rsplit {t₁ = t₁} {t₂ = t₂} teq ¬S₂ here (cons _ w ¬skips eq C) =
  t₁ , (t₂ ; w)
    , ≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; (≃-sym teq) ≃-refl) eq)
    , ¬skips-seqˡ ¬S₂
    , cons (t₁ ; ret) skip ¬skips-ret ≃-skipʳ (nil skip)
    , cons (acq ; t₂) w ¬skips-acq ≃-assoc-; C
chain-rsplit teq ¬S₂ (there _ I) (cons a s′ ¬skips eq C) =
  let u , v , uv≃ , ¬Sv , CL , CR = chain-rsplit teq ¬S₂ I C in
  (a ; u) , v
    , ≃-trans ≃-assoc-; (≃-trans (≃-; ≃-refl uv≃) eq)
    , ¬Sv
    , cons a (u ; ret) ¬skips-ret (≃-sym ≃-assoc-;) CL
    , CR
