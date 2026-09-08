-- | Process progress: the main induction (agent G3, wave 2).
--
--   The theorem is proved for a CLOSED process by structural recursion on the
--   process, carrying a `ProcessContext` from the root so that a reduction
--   found deep inside already IS a reduction of the whole process:
--
--     go : (ctx : ProcessContext k 0) (Q : Proc k) -> [] ; [] |-p plug ctx Q ->
--          Blocked+ Q  or  exists P'. plug ctx Q --> P'
--
--   The module is parametrised over the lemmas of `Safety/Progress/Redex.agda`
--   (agent G1) and `Safety/Progress/Sync.agda` (agent G2) so that it
--   type-checks before those files do; `Safety/Progress.agda` instantiates it.
--   The module parameters are the ONLY assumptions -- no postulate anywhere.
--
--   `go` returns the PRECISE blocked predicate `Blocked⁺`: the case analysis on
--   the two binder groups produces it for free, and `Blocked⁺⇒Blocked`
--   (Safety/Blocked.agda) recovers the paper's `Blocked`.
--
--   Owner: agent G3.
open import Data.Nat.ListAction using (sum)
open import Data.Fin.Patterns using (0F)

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Reduction.Base hiding (Blocked)
open import BorrowedCF.Reduction.Expressions using (_⋯→_; inv-`⊤)
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Processes.Typed using (_─→ₚ_)

open import BorrowedCF.Simulation.BackwardSoup.Locate
  using (ProcessContext; hole; par-left; par-right; bind; plug; compose; plug-compose)
open import BorrowedCF.Simulation.BackwardSoup.Position using (weakenThrough)

open import BorrowedCF.Safety.Blocked
open import BorrowedCF.Safety.Progress.Expr
open import BorrowedCF.Safety.Progress.Main.Shapes

module BorrowedCF.Safety.Progress.Main

  ----------------------------------------------------------------------------
  -- From `Safety/Progress/Sync.agda` (agent G2).

  -- Typing at the hole of a process context.
  (plug-typing :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (Q : Proc k) →
    [] ; [] ⊢ₚ plug ctx Q →
    Σ[ Δ ∈ Ctx k ] Σ[ σ ∈ Struct k ] ChanCx Δ × (Δ ; σ ⊢ₚ Q))

  -- Two dual heads in BC give a synchronisation redex (com / choice / close).
  (sync-redex :
    ∀ {k b₁ b₂ : ℕ} {B₁ B₂ : BindGroup}
      (ctx : ProcessContext k 0)
      (Q : Proc (sum (suc b₁ ∷ B₁) + sum (suc b₂ ∷ B₂) + k)) →
    [] ; [] ⊢ₚ plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) →
    0F ∈BC Q →
    head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC Q →
    Σ[ P′ ∈ Proc 0 ] (plug ctx (ν (suc b₁ ∷ B₁) (suc b₂ ∷ B₂) Q) ─→ₚ P′))

  ----------------------------------------------------------------------------
  -- From `Safety/Progress/Redex.agda` (agent G1).

  (step-in-ctx :
    ∀ {k n : ℕ} {e e′ : Tm k} (ctx : ProcessContext k n) →
    e ⋯→ e′ → plug ctx ⟪ e ⟫ ─→ₚ plug ctx ⟪ e′ ⟫)

  (∈AC⇒located-acq :
    ∀ {n : ℕ} {P : Proc n} {x : 𝔽 n} → x ∈AC P →
    Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ E ∈ Frame* k ] Σ[ d ∈ Dir ]
      P ≡ plug ctx ⟪ E [ K `acq ·⟨ d ⟩ (` weakenThrough ctx x) ]* ⟫)

  (redex-new :
    ∀ {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) (s : 𝕊 0) →
    Σ[ P′ ∈ Proc n ] (plug ctx ⟪ E [ K (`new s) ·¹ * ]* ⟫ ─→ₚ P′))

  (redex-fork :
    ∀ {k n : ℕ} (ctx : ProcessContext k n) (E : Frame* k) {e : Tm k} → Value e →
    Σ[ P′ ∈ Proc n ] (plug ctx ⟪ E [ K `fork ·¹ e ]* ⟫ ─→ₚ P′))

  (redex-lsplit :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K (`lsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′))

  (redex-rsplit :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (s₀ : 𝕊 0) (x : 𝔽 k) →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K (`rsplit s₀) ·¹ (` x) ]* ⟫ ─→ₚ P′))

  (redex-drop :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
    [] ; [] ⊢ₚ plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K `drop ·¹ (` x) ]* ⟫ ─→ₚ P′))

  (redex-discard :
    ∀ {k : ℕ} (ctx : ProcessContext k 0) (E : Frame* k) (x : 𝔽 k) →
    [] ; [] ⊢ₚ plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ →
    Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K `discard ·¹ (` x) ]* ⟫ ─→ₚ P′))

  (redex-acq-exposedˡ :
    ∀ {m k b : ℕ} {B₁ B₂ : BindGroup}
      (ctx₀ : ProcessContext m 0)
      (ctx₁ : ProcessContext k (sum (0 ∷ suc b ∷ B₁) + sum B₂ + m))
      (E : Frame* k) →
    Σ[ P′ ∈ Proc 0 ]
      (plug ctx₀ (ν (0 ∷ suc b ∷ B₁) B₂
         (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ 0F) ]* ⟫)) ─→ₚ P′))

  (redex-acq-exposedʳ :
    ∀ {m k b : ℕ} {B₁ B₂ : BindGroup}
      (ctx₀ : ProcessContext m 0)
      (ctx₁ : ProcessContext k (sum B₁ + sum (0 ∷ suc b ∷ B₂) + m))
      (E : Frame* k) →
    Σ[ P′ ∈ Proc 0 ]
      (plug ctx₀ (ν B₁ (0 ∷ suc b ∷ B₂)
         (plug ctx₁ ⟪ E [ K `acq ·¹ (` weakenThrough ctx₁ (head₂ B₁ b B₂)) ]* ⟫))
         ─→ₚ P′))

  where

open Nat.Variables

private
  variable
    j : ℕ

--------------------------------------------------------------------------------
-- Transporting the two conclusions along a process equation.  The only
-- equations used are instances of `plug-compose`: extending the root context by
-- one constructor is the same as descending into the corresponding subprocess.

private
  ⊢-≡ : {R S : Proc 0} → R ≡ S → [] ; [] ⊢ₚ R → [] ; [] ⊢ₚ S
  ⊢-≡ refl ⊢R = ⊢R

  red-≡ : {R S : Proc 0} → R ≡ S →
    Σ[ P′ ∈ Proc 0 ] (R ─→ₚ P′) → Σ[ P′ ∈ Proc 0 ] (S ─→ₚ P′)
  red-≡ refl x = x

--------------------------------------------------------------------------------
-- A constant application under an evaluation context inside a process context
-- has direction `𝟙`.  (`const-app-dir` of `Safety/Progress/Expr.agda` needs the
-- typing of the redex itself, which `plug-typing` and `⊢[]*⁻¹` extract.)

private
  app-dir-in :
    (ctx : ProcessContext k 0) (ctx₁ : ProcessContext j k) (E : Frame* j)
    {c : Const} {d : Dir} {w : Tm j} →
    [] ; [] ⊢ₚ plug ctx (plug ctx₁ ⟪ E [ K c ·⟨ d ⟩ w ]* ⟫) → d ≡ 𝟙
  app-dir-in ctx ctx₁ E ⊢P
    with _ , _ , _ , ⊢thr ←
      plug-typing (compose ctx ctx₁) _ (⊢-≡ (sym (plug-compose ctx ctx₁ _)) ⊢P)
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ (inv-⟪⟫ ⊢thr)
    = const-app-dir ⊢r

--------------------------------------------------------------------------------
-- The two `acq` redexes, phrased on the `ν` shapes that `Blocked⁺` decides.
-- `∈AC⇒located-acq` turns the membership witness into the located thread that
-- `redex-acq-exposed*` expects; the typing only supplies the direction.

private
  acq-redexˡ : ∀ {b : ℕ} {B₁ B₂ : BindGroup}
    (ctx : ProcessContext k 0) (Q : Proc (sum (0 ∷ suc b ∷ B₁) + sum B₂ + k)) →
    [] ; [] ⊢ₚ plug ctx (ν (0 ∷ suc b ∷ B₁) B₂ Q) →
    0F ∈AC Q →
    Σ[ P′ ∈ Proc 0 ] (plug ctx (ν (0 ∷ suc b ∷ B₁) B₂ Q) ─→ₚ P′)
  acq-redexˡ {b = b} {B₁} {B₂} ctx Q ⊢P mem
    with _ , ctx₁ , E , d , refl ← ∈AC⇒located-acq mem
    with refl ← app-dir-in ctx (bind (0 ∷ suc b ∷ B₁) B₂ ctx₁) E ⊢P
    = redex-acq-exposedˡ ctx ctx₁ E

  acq-redexʳ : ∀ {b : ℕ} {B₁ B₂ : BindGroup}
    (ctx : ProcessContext k 0) (Q : Proc (sum B₁ + sum (0 ∷ suc b ∷ B₂) + k)) →
    [] ; [] ⊢ₚ plug ctx (ν B₁ (0 ∷ suc b ∷ B₂) Q) →
    head₂ B₁ b B₂ ∈AC Q →
    Σ[ P′ ∈ Proc 0 ] (plug ctx (ν B₁ (0 ∷ suc b ∷ B₂) Q) ─→ₚ P′)
  acq-redexʳ {b = b} {B₁} {B₂} ctx Q ⊢P mem
    with _ , ctx₁ , E , d , refl ← ∈AC⇒located-acq mem
    with refl ← app-dir-in ctx (bind B₁ (0 ∷ suc b ∷ B₂) ctx₁) E ⊢P
    = redex-acq-exposedʳ ctx ctx₁ E

--------------------------------------------------------------------------------
-- The leaf case: a thread whose expression is a constant applied to a value.
-- Six constants reduce, six block (`BlockingConst` of `Safety/Blocked.agda`),
-- and `K `unit` is never applied (`no-unit-app`).

private
  leaf : {Δ : Ctx k} {σ : Struct k}
    (ctx : ProcessContext k 0) (E : Frame* k) (c : Const) {d : Dir} {v : Tm k} →
    ChanCx Δ → Value v →
    Δ ; σ ⊢ E [ K c ·⟨ d ⟩ v ]* ∶ `⊤ ∣ 𝕀 →
    [] ; [] ⊢ₚ plug ctx ⟪ E [ K c ·⟨ d ⟩ v ]* ⟫ →
    Blocked⁺ ⟪ E [ K c ·⟨ d ⟩ v ]* ⟫
      ⊎ Σ[ P′ ∈ Proc 0 ] (plug ctx ⟪ E [ K c ·⟨ d ⟩ v ]* ⟫ ─→ₚ P′)

  leaf ctx E `unit Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    = ⊥-elim (no-unit-app ⊢r)

  leaf ctx E `fork Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    = inj₂ (redex-fork ctx E V)

  leaf ctx E (`new s) Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with refl ← arg-new Δ-S V ⊢r
    = inj₂ (redex-new ctx E s)

  leaf ctx E (`lsplit s) Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with x , _ , _ , refl , _ , _ ← arg-lsplit Δ-S V ⊢r
    = inj₂ (redex-lsplit ctx E s x)

  leaf ctx E (`rsplit s) Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with x , _ , _ , refl , _ , _ ← arg-rsplit Δ-S V ⊢r
    = inj₂ (redex-rsplit ctx E s x)

  leaf ctx E `drop Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with x , _ , refl , _ , _ ← arg-drop Δ-S V ⊢r
    = inj₂ (redex-drop ctx E x ⊢P)

  leaf ctx E `discard Δ-S V ⊢e ⊢P
    with _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢r ← ⊢[]*⁻¹ E _ ⊢e
    with refl ← const-app-dir ⊢r
    with x , _ , refl , _ , _ ← arg-discard Δ-S V ⊢r
    = inj₂ (redex-discard ctx E x ⊢P)

  leaf ctx E `send       Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-send , refl))
  leaf ctx E `recv       Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-recv , refl))
  leaf ctx E `acq        Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-acq , refl))
  leaf ctx E (`end p)    Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-end p , refl))
  leaf ctx E (`select i) Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-select i , refl))
  leaf ctx E `branch     Δ-S V ⊢e ⊢P = inj₁ (B-Const⁺ (E , _ , _ , _ , V , B-branch , refl))

--------------------------------------------------------------------------------
-- The restriction case.  `groupShape` (Main/Shapes.agda) has already reduced
-- each binder group to one of the two typable shapes, so the four combinations
-- below are exhaustive and each matches one `Blocked⁺` rule.

private
  nu : {B₁ B₂ : BindGroup}
    (ctx : ProcessContext k 0) (Q : Proc (sum B₁ + sum B₂ + k)) →
    GroupShape B₁ → GroupShape B₂ →
    [] ; [] ⊢ₚ plug ctx (ν B₁ B₂ Q) →
    Blocked⁺ Q →
    Blocked⁺ (ν B₁ B₂ Q) ⊎ Σ[ P′ ∈ Proc 0 ] (plug ctx (ν B₁ B₂ Q) ─→ₚ P′)

  -- Both groups start with a full first group: R-Com / R-Choice / R-Close.
  nu ctx Q (head-full b₁ B₁) (head-full b₂ B₂) ⊢P bl
    with 0F ∈BC? Q | head₂ (suc b₁ ∷ B₁) b₂ B₂ ∈BC? Q
  ... | yes m₁ | yes m₂ = inj₂ (sync-redex ctx Q ⊢P m₁ m₂)
  ... | yes m₁ | no ¬m₂ = inj₁ (B-Nu⁺ (λ pr → ¬m₂ (pr .proj₂)) bl)
  ... | no ¬m₁ | _      = inj₁ (B-Nu⁺ (λ pr → ¬m₁ (pr .proj₁)) bl)

  -- Side 1 exposes a group: R-Acq on the head of side 1.
  nu ctx Q (head-sep b B₁) (head-full b₂ B₂) ⊢P bl
    with 0F ∈AC? Q
  ... | yes m = inj₂ (acq-redexˡ ctx Q ⊢P m)
  ... | no ¬m = inj₁ (B-NuAcqˡ⁺ ¬m bl)

  -- Side 2 exposes a group: R-Acq on the head of side 2.
  nu ctx Q (head-full b₁ B₁) (head-sep b B₂) ⊢P bl
    with head₂ (suc b₁ ∷ B₁) b B₂ ∈AC? Q
  ... | yes m = inj₂ (acq-redexʳ ctx Q ⊢P m)
  ... | no ¬m = inj₁ (B-NuAcqʳ⁺ ¬m bl)

  -- Both sides expose a group: either head may acquire.
  nu ctx Q (head-sep b B₁) (head-sep b′ B₂) ⊢P bl
    with 0F ∈AC? Q | head₂ (0 ∷ suc b ∷ B₁) b′ B₂ ∈AC? Q
  ... | yes m | _       = inj₂ (acq-redexˡ ctx Q ⊢P m)
  ... | no ¬m | yes m′  = inj₂ (acq-redexʳ ctx Q ⊢P m′)
  ... | no ¬m | no ¬m′  = inj₁ (B-NuAcqˡʳ⁺ ¬m ¬m′ bl)

--------------------------------------------------------------------------------
-- The induction.

go : (ctx : ProcessContext k 0) (Q : Proc k) →
  [] ; [] ⊢ₚ plug ctx Q →
  Blocked⁺ Q ⊎ Σ[ P′ ∈ Proc 0 ] (plug ctx Q ─→ₚ P′)

go ctx ⟪ e ⟫ ⊢P
  with _ , _ , Δ-S , ⊢thr ← plug-typing ctx ⟪ e ⟫ ⊢P
  with progress⁺ Δ-S (inv-⟪⟫ ⊢thr)
... | inj₂ (inj₂ (e′ , stp)) = inj₂ (_ , step-in-ctx ctx stp)
... | inj₁ V rewrite inv-`⊤ Δ-S V (inv-⟪⟫ ⊢thr) .proj₁ = inj₁ B-Unit⁺
... | inj₂ (inj₁ (E , c , d , v , V , refl)) =
      leaf ctx E c Δ-S V (inv-⟪⟫ ⊢thr) ⊢P

go ctx (Q₁ ∥ Q₂) ⊢P
  with go (compose ctx (par-left hole Q₂)) Q₁
          (⊢-≡ (sym (plug-compose ctx (par-left hole Q₂) Q₁)) ⊢P)
... | inj₂ red = inj₂ (red-≡ (plug-compose ctx (par-left hole Q₂) Q₁) red)
... | inj₁ bl₁
  with go (compose ctx (par-right Q₁ hole)) Q₂
          (⊢-≡ (sym (plug-compose ctx (par-right Q₁ hole) Q₂)) ⊢P)
... | inj₂ red = inj₂ (red-≡ (plug-compose ctx (par-right Q₁ hole) Q₂) red)
... | inj₁ bl₂ = inj₁ (B-Par⁺ bl₁ bl₂)

go ctx (ν B₁ B₂ Q) ⊢P
  with go (compose ctx (bind B₁ B₂ hole)) Q
          (⊢-≡ (sym (plug-compose ctx (bind B₁ B₂ hole) Q)) ⊢P)
... | inj₂ red = inj₂ (red-≡ (plug-compose ctx (bind B₁ B₂ hole) Q) red)
... | inj₁ bl
  with _ , _ , _ , ⊢ν ← plug-typing ctx (ν B₁ B₂ Q) ⊢P
  with _ , _ , _ , _ , _ , ⊢B₁ , ⊢B₂ , C₁ , C₂ , _ ← inv-ν ⊢ν
  = nu ctx Q (groupShape B₁ ⊢B₁ C₁) (groupShape B₂ ⊢B₂ C₂) ⊢P bl

--------------------------------------------------------------------------------
-- The theorem.

progress⁺ₚ : {γ : Struct 0} {P : Proc 0} →
  [] ; γ ⊢ₚ P → Blocked⁺ P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)
progress⁺ₚ {P = P} ⊢P = go hole P (close-γ ⊢P)

progressₚ : {γ : Struct 0} {P : Proc 0} →
  [] ; γ ⊢ₚ P → (P ≋ ⟪ * ⟫) ⊎ Blocked P ⊎ Σ[ P′ ∈ Proc 0 ] (P ─→ₚ P′)
progressₚ ⊢P with progress⁺ₚ ⊢P
... | inj₁ bl  = inj₂ (inj₁ (Blocked⁺⇒Blocked bl))
... | inj₂ red = inj₂ (inj₂ red)
