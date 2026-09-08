------------------------------------------------------------------------
-- Group-level reshuffling of a binder context: the two lemmas the paper's
-- appendix calls BindCtxLsplit and BindCtxRsplit.
--
-- `Same B1 Gc Gc' G G'` says that G and G' agree on the first |B1| binder
-- groups and continue with Gc resp. Gc'.  It is an inductive relation, so no
-- `sum-++` cast ever appears inside the proofs: `sum ((b :: B1) ++ C)`
-- reduces to `b + sum (B1 ++ C)` definitionally.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.Splits.Group where

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomCons using (acq-;-split)
open import BorrowedCF.Types.AtomUnsnoc using (atom-;-unsnoc)

open import BorrowedCF.Safety.Preservation.Splits.Chain

open Nat.Variables
open Fin.Patterns

private variable
  t t₁ t₂ : 𝕊 0
  b₀ q : ℕ
  C C′ : BindGroup

------------------------------------------------------------------------
-- Vector plumbing

++-inj : ∀ {m k} (Γ₁ Γ₂ : Ctx m) {Δ₁ Δ₂ : Ctx k} →
  Γ₁ ⸴* Δ₁ ≡ Γ₂ ⸴* Δ₂ → Γ₁ ≡ Γ₂ × Δ₁ ≡ Δ₂
++-inj V.[]       V.[]       eq = refl , eq
++-inj (T ⸴ Γ₁) (U ⸴ Γ₂) eq
  with refl ← V.∷-injectiveˡ eq
  with refl , refl ← ++-inj Γ₁ Γ₂ (V.∷-injectiveʳ eq) = refl , refl

0<len : ∀ (B₁ : BindGroup) {x B₂} → 0 Nat.< L.length (B₁ ++ x ∷ B₂)
0<len []       = Nat.z<s
0<len (_ ∷ _)  = Nat.z<s

------------------------------------------------------------------------
-- AcqHeadCtx only depends on the head entry.

acqHead-cong : ∀ {m k} {Γ : Ctx m} {Γ′ : Ctx k} (U : 𝕋) →
  AcqHeadCtx (U ⸴ Γ) → AcqHeadCtx (U ⸴ Γ′)
acqHead-cong ⟨ s ⟩         ah = ah
acqHead-cong `⊤            ()
acqHead-cong (_ ⟨ _ ⟩→ _)  ()
acqHead-cong (_ ⊗⟨ _ ⟩ _)  ()
acqHead-cong (_ ⊕ _)       ()

------------------------------------------------------------------------
-- Agreement on a prefix of binder groups.

data Same : (B₁ : BindGroup) {C C′ : BindGroup}
            {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} →
            Ctx (sum (B₁ ++ C)) → Ctx (sum (B₁ ++ C′)) → Set where
  nilS  : ∀ {C C′} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} → Same [] {C} {C′} {Γc} {Γc′} Γc Γc′
  consS : ∀ {b₀ B₁ C C′} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)}
            {Γ : Ctx (sum (B₁ ++ C))} {Γ′ : Ctx (sum (B₁ ++ C′))} (Γ₀ : Ctx b₀) →
          Same B₁ {C} {C′} {Γc} {Γc′} Γ Γ′ →
          Same (b₀ ∷ B₁) {C} {C′} {Γc} {Γc′} (Γ₀ ⸴* Γ) (Γ₀ ⸴* Γ′)

same-nil⁻¹ : ∀ {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} {Γ Γ′} →
  Same [] {C} {C′} {Γc} {Γc′} Γ Γ′ → Γ ≡ Γc × Γ′ ≡ Γc′
same-nil⁻¹ nilS = refl , refl

same-cons⁻¹ : ∀ {B₁} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} {Γ Γ′} →
  Same (b₀ ∷ B₁) {C} {C′} {Γc} {Γc′} Γ Γ′ →
  Σ[ Γ₀ ∈ Ctx b₀ ] Σ[ Γa ∈ Ctx (sum (B₁ ++ C)) ] Σ[ Γa′ ∈ Ctx (sum (B₁ ++ C′)) ]
    (Γ ≡ Γ₀ ⸴* Γa) × (Γ′ ≡ Γ₀ ⸴* Γa′) × Same B₁ {C} {C′} {Γc} {Γc′} Γa Γa′
same-cons⁻¹ (consS Γ₀ Sm) = Γ₀ , _ , _ , refl , refl , Sm

-- Building one: peel the prefix groups off the vector.
vsplit : ∀ m {k} (Γ : Ctx (m + k)) → Σ[ Γ₁ ∈ Ctx m ] Σ[ Γ₂ ∈ Ctx k ] Γ ≡ Γ₁ ⸴* Γ₂
vsplit zero    Γ         = V.[] , Γ , refl
vsplit (suc m) (T ⸴ Γ) =
  let Γ₁ , Γ₂ , eq = vsplit m Γ in (T ⸴ Γ₁) , Γ₂ , cong (T ⸴_) eq

mkSame : ∀ (B₁ : BindGroup) {C} (Γ : Ctx (sum (B₁ ++ C))) →
  Σ[ Γc ∈ Ctx (sum C) ]
    (∀ {C′} (Γc′ : Ctx (sum C′)) →
       Σ[ Γ′ ∈ Ctx (sum (B₁ ++ C′)) ] Same B₁ {C} {C′} {Γc} {Γc′} Γ Γ′)
mkSame []        Γ = Γ , λ Γc′ → Γc′ , nilS
mkSame (b₀ ∷ B₁) Γ
  with Γ₀ , Γa , refl ← vsplit b₀ Γ
  with Γc , f ← mkSame B₁ Γa
  = Γc , λ Γc′ → let Γa′ , Sm = f Γc′ in (Γ₀ ⸴* Γa′) , consS Γ₀ Sm

-- Fin plumbing for the lookup specification of `Same`.
cast-↑ʳ-+ : ∀ a b {k m} .(e : (a + b) + k ≡ a + m) .(e′ : b + k ≡ m) (y : 𝔽 k) →
  Fin.cast e ((a + b) ↑ʳ y) ≡ a ↑ʳ Fin.cast e′ (b ↑ʳ y)
cast-↑ʳ-+ zero    b e e′ y = refl
cast-↑ʳ-+ (suc a) b e e′ y = cong suc (cast-↑ʳ-+ a b _ e′ y)

-- What `Same` says about lookups: below the prefix the two contexts agree with
-- their suffixes.
same-lookupˡ : ∀ (B₁ : BindGroup) {C C′} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} {Γ Γ′} →
  Same B₁ {C} {C′} {Γc} {Γc′} Γ Γ′ →
  ∀ y → Γ ﹫ Fin.cast (sym (sum-++ B₁ C)) (sum B₁ ↑ʳ y) ≡ Γc ﹫ y
same-lookupˡ [] {Γc = Γc} nilS y = cong (Γc ﹫_) (Fin.cast-is-id refl y)
same-lookupˡ (b₀ ∷ B₁) {C} {Γc = Γc} (consS {Γ = Γa} Γ₀ Sm) y =
  cong ((Γ₀ ⸴* Γa) ﹫_) (cast-↑ʳ-+ b₀ (sum B₁) _ (sym (sum-++ B₁ C)) y)
    ■ V.lookup-++ʳ Γ₀ _ _
    ■ same-lookupˡ B₁ Sm y

same-lookupʳ : ∀ (B₁ : BindGroup) {C C′} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} {Γ Γ′} →
  Same B₁ {C} {C′} {Γc} {Γc′} Γ Γ′ →
  ∀ y → Γ′ ﹫ Fin.cast (sym (sum-++ B₁ C′)) (sum B₁ ↑ʳ y) ≡ Γc′ ﹫ y
same-lookupʳ [] {Γc′ = Γc′} nilS y = cong (Γc′ ﹫_) (Fin.cast-is-id refl y)
same-lookupʳ (b₀ ∷ B₁) {C′ = C′} (consS {Γ′ = Γa′} Γ₀ Sm) y =
  cong ((Γ₀ ⸴* Γa′) ﹫_) (cast-↑ʳ-+ b₀ (sum B₁) _ (sym (sum-++ B₁ C′)) y)
    ■ V.lookup-++ʳ Γ₀ _ _
    ■ same-lookupʳ B₁ Sm y


-- Positional agreement lifts through the untouched prefix groups.
same-agree : ∀ (B₁ : BindGroup) {C C′} {Γc : Ctx (sum C)} {Γc′ : Ctx (sum C′)} {Γ Γ′} {p} →
  Same B₁ {C} {C′} {Γc} {Γc′} Γ Γ′ → Agree p Γc Γc′ → Agree (sum B₁ + p) Γ Γ′
same-agree []        nilS         A = A
same-agree (b₀ ∷ B₁) {p = p} (consS {Γ = Γa} {Γ′ = Γa′} Γ₀ Sm) A =
  subst (λ z → Agree z (Γ₀ ⸴* Γa) (Γ₀ ⸴* Γa′)) (sym (Nat.+-assoc b₀ (sum B₁) p))
    (agree-++ˡ Γ₀ (same-agree B₁ Sm A))

------------------------------------------------------------------------
-- Transfer of the acq-head condition.

acqHead-lsplit : ∀ {B₁ B₂ w w′} {Γg : Ctx w} {Γg′ : Ctx w′} {Γr : Ctx (sum B₂)} {Γ Γ′} →
  ¬ Skips t₁ → t ≃ t₁ ; t₂ →
  Ins (⟨ t ⟩) (⟨ t₁ ⟩) (⟨ t₂ ⟩) Γg Γg′ →
  Same B₁ {w ∷ B₂} {w′ ∷ B₂} {Γg ⸴* Γr} {Γg′ ⸴* Γr} Γ Γ′ →
  AcqHeadCtx Γ → AcqHeadCtx Γ′
acqHead-lsplit ¬Sm₁ teq here nilS (h , eq)
  with acq-;-split (≃-trans (≃-sym teq) eq)
... | inj₁ (Sk , _)       = ⊥-elim (¬Sm₁ Sk)
... | inj₂ (h′ , eq′ , _) = h′ , eq′
acqHead-lsplit ¬Sm₁ teq (there U I) nilS ah = acqHead-cong U ah
acqHead-lsplit ¬Sm₁ teq I (consS V.[] Sm)     ah = acqHead-lsplit ¬Sm₁ teq I Sm ah
acqHead-lsplit ¬Sm₁ teq I (consS (U ⸴ Γ₀) Sm) ah = acqHead-cong U ah

acqHead-rsplit : ∀ {B₁ B₂ w w₁ w₂} {Γg : Ctx w} {Γg₁ : Ctx w₁} {Γg₂ : Ctx w₂}
  {Γr : Ctx (sum B₂)} {Γ Γ′} →
  ¬ Skips t₁ → t ≃ t₁ ; t₂ →
  InsR (⟨ t ⟩) (⟨ t₁ ; ret ⟩) (⟨ acq ; t₂ ⟩) Γg Γg₁ Γg₂ →
  Same B₁ {w ∷ B₂} {w₁ ∷ w₂ ∷ B₂} {Γg ⸴* Γr} {Γg₁ ⸴* (Γg₂ ⸴* Γr)} Γ Γ′ →
  AcqHeadCtx Γ → AcqHeadCtx Γ′
acqHead-rsplit ¬Sm₁ teq here nilS (h , eq)
  with acq-;-split (≃-trans (≃-sym teq) eq)
... | inj₁ (Sk , _)       = ⊥-elim (¬Sm₁ Sk)
... | inj₂ (h′ , eq′ , _) = (h′ ; ret) , ≃-trans (≃-; eq′ ≃-refl) ≃-assoc-;
acqHead-rsplit ¬Sm₁ teq (there U I) nilS ah = acqHead-cong U ah
acqHead-rsplit ¬Sm₁ teq I (consS V.[] Sm)     ah = acqHead-rsplit ¬Sm₁ teq I Sm ah
acqHead-rsplit ¬Sm₁ teq I (consS (U ⸴ Γ₀) Sm) ah = acqHead-cong U ah

------------------------------------------------------------------------
-- BindCtxLsplit

bindCtx-lsplit : ∀ (B₁ : BindGroup) {B₂ w w′ s} {Γg : Ctx w} {Γg′ : Ctx w′}
  {Γr : Ctx (sum B₂)} {Γ Γ′} →
  ¬ Skips t₁ → ¬ Skips t₂ → t ≃ t₁ ; t₂ →
  Ins (⟨ t ⟩) (⟨ t₁ ⟩) (⟨ t₂ ⟩) Γg Γg′ →
  BindCtx s (B₁ ++ w ∷ B₂) Γ →
  Same B₁ {w ∷ B₂} {w′ ∷ B₂} {Γg ⸴* Γr} {Γg′ ⸴* Γr} Γ Γ′ →
  BindCtx s (B₁ ++ w′ ∷ B₂) Γ′
bindCtx-lsplit [] {Γr = Γr} ¬Sm₁ ¬Sm₂ teq I (last C) Sm
  with refl , refl ← same-nil⁻¹ Sm
  = last (chain-lsplit teq ¬Sm₂ (ins-++ʳ Γr I) C)
bindCtx-lsplit [] {Γg = Γg} {Γg′} {Γr} ¬Sm₁ ¬Sm₂ teq I
               (cons-ret/acq s₁ {Γ₁ = Γ₁} s≃ ¬sk₂ C₁ C₂ ah) Sm
  with eq , refl ← same-nil⁻¹ Sm
  with refl , refl ← ++-inj Γ₁ Γg eq
  = cons-ret/acq s₁ s≃ ¬sk₂ (chain-lsplit teq ¬Sm₂ I C₁) C₂ ah
bindCtx-lsplit [] ¬Sm₁ ¬Sm₂ teq () (cons-acq C ah) Sm
bindCtx-lsplit (b₀ ∷ B₁) ¬Sm₁ ¬Sm₂ teq I C Sm
  with bindCtx-inv-cons (0<len B₁) C
... | inj₁ (s₁ , s₂ , Γ₁ , Γ₂ , s≃ , Γeq , C₁ , C₂ , ¬sk₂ , ah)
      with Γ₀ , Γa , Γa′ , refl , refl , Sm′ ← same-cons⁻¹ Sm
      with refl , refl ← ++-inj Γ₁ Γ₀ Γeq
      = cons-ret/acq s₁ s≃ ¬sk₂ C₁ (bindCtx-lsplit B₁ ¬Sm₁ ¬Sm₂ teq I C₂ Sm′)
          (acqHead-lsplit ¬Sm₁ teq I Sm′ ah)
... | inj₂ (refl , C₂ , ah)
      with V.[] , Γa , Γa′ , refl , refl , Sm′ ← same-cons⁻¹ Sm
      = cons-acq (bindCtx-lsplit B₁ ¬Sm₁ ¬Sm₂ teq I C₂ Sm′) (acqHead-lsplit ¬Sm₁ teq I Sm′ ah)

------------------------------------------------------------------------
-- BindCtxRsplit

bindCtx-rsplit : ∀ (B₁ : BindGroup) {B₂ w w₁ w₂ s} {Γg : Ctx w} {Γg₁ : Ctx w₁}
  {Γg₂ : Ctx w₂} {Γr : Ctx (sum B₂)} {Γ Γ′} →
  ¬ Skips t₁ → ¬ Skips t₂ → t ≃ t₁ ; t₂ →
  InsR (⟨ t ⟩) (⟨ t₁ ; ret ⟩) (⟨ acq ; t₂ ⟩) Γg Γg₁ Γg₂ →
  BindCtx s (B₁ ++ w ∷ B₂) Γ →
  Same B₁ {w ∷ B₂} {w₁ ∷ w₂ ∷ B₂} {Γg ⸴* Γr} {Γg₁ ⸴* (Γg₂ ⸴* Γr)} Γ Γ′ →
  BindCtx s (B₁ ++ w₁ ∷ w₂ ∷ B₂) Γ′
bindCtx-rsplit [] {Γr = Γr} ¬Sm₁ ¬Sm₂ teq I (last C) Sm
  with refl , refl ← same-nil⁻¹ Sm
  with u , v , uv≃ , ¬Sv , CL , CR ← chain-rsplit teq ¬Sm₂ (insR-++ʳ Γr I) C
  = cons-ret/acq u uv≃ ¬Sv CL (last CR) (insR-acqHead (insR-++ʳ Γr I))
bindCtx-rsplit [] {Γg = Γg} {Γg₁} {Γg₂} {Γr} ¬Sm₁ ¬Sm₂ teq I
               (cons-ret/acq s₁ {Γ₁ = Γ₁} s≃ ¬sk₂ C₁ C₂ ah) Sm
  with eq , refl ← same-nil⁻¹ Sm
  with refl , refl ← ++-inj Γ₁ Γg eq
  with u , v , uv≃ , ¬Sv , CL , CR ← chain-rsplit teq ¬Sm₂ I C₁
  with atom-;-unsnoc ret uv≃
... | inj₁ Sv = ⊥-elim (¬Sv Sv)
... | inj₂ (v₀ , uv₀≃ , v₀ret≃) =
  cons-ret/acq u
    (≃-trans (≃-sym ≃-assoc-;) (≃-trans (≃-; uv₀≃ ≃-refl) s≃))
    (¬skips-seqʳ ¬sk₂)
    CL
    (cons-ret/acq (acq ; v₀) ≃-assoc-; ¬sk₂
      (bindCtx′-≃ (≃-sym (≃-trans ≃-assoc-; (≃-; ≃-refl v₀ret≃))) CR)
      C₂ ah)
    (insR-acqHead (insR-++ʳ Γr I))
bindCtx-rsplit [] ¬Sm₁ ¬Sm₂ teq () (cons-acq C ah) Sm
bindCtx-rsplit (b₀ ∷ B₁) ¬Sm₁ ¬Sm₂ teq I C Sm
  with bindCtx-inv-cons (0<len B₁) C
... | inj₁ (s₁ , s₂ , Γ₁ , Γ₂ , s≃ , Γeq , C₁ , C₂ , ¬sk₂ , ah)
      with Γ₀ , Γa , Γa′ , refl , refl , Sm′ ← same-cons⁻¹ Sm
      with refl , refl ← ++-inj Γ₁ Γ₀ Γeq
      = cons-ret/acq s₁ s≃ ¬sk₂ C₁ (bindCtx-rsplit B₁ ¬Sm₁ ¬Sm₂ teq I C₂ Sm′)
          (acqHead-rsplit ¬Sm₁ teq I Sm′ ah)
... | inj₂ (refl , C₂ , ah)
      with V.[] , Γa , Γa′ , refl , refl , Sm′ ← same-cons⁻¹ Sm
      = cons-acq (bindCtx-rsplit B₁ ¬Sm₁ ¬Sm₂ teq I C₂ Sm′) (acqHead-rsplit ¬Sm₁ teq I Sm′ ah)
