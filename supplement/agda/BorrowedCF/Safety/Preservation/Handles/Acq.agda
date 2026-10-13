-- | R-Acq preservation (agent P4b).  See `Preservation/Acq-STATUS.md`.
--
--   The step  ν (0 ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ acq x₀ ] ⟫ ∥ P)
--          ─→ ν (suc b₁ ∷ B₁) B₂ (⟪ E [ x₀ ] ⟫ ∥ P)
--   changes nothing but the TYPE of the bound handle `x₀ = 0F`: from
--   `⟨ u ⟩` with `u ≃ acq @ t` to `⟨ t ⟩`.  Everything of the derivation that
--   READS the context at `0F` must therefore be replayed at the new type.
--   Only three rules read the context: `∥′-dup` and `≼-∅` (they need `Unr`,
--   never true of a handle) and `∥′-tm-;` (it needs `Mobile`).  So the proof
--   splits on the width of the acquired group:
--
--   * width ≥ 2 (`b₁ = suc _`): the head is IMMOBILE (`AcqProbe.acq-head-
--     ¬mobile`), hence no `≼`/`≈` step of the derivation mentions `0F` in a
--     `MobCx`/`UnrCx` at all, and `≼-tr` replays the whole thing verbatim.
--   * width 1 (`b₁ = 0`): the head may well be mobile, but then it is ALONE
--     in its group, its frame contribution is `` ` 0F @ [] ``, and the
--     handle can be split off the frame by `∥`-laws only.  The structure
--     substitution `zap` (`0F ↦ []`, a legal `⇒` from the old context to the
--     new one, whatever the two head types are) erases `0F` from the
--     inherited `≼`, and `pat-hole-≼` puts it back in front.
module BorrowedCF.Safety.Preservation.Handles.Acq where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Nat.ListAction using (sum)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open import BorrowedCF.Prelude
open import BorrowedCF.Context as 𝐂
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Reduction.Base
open import BorrowedCF.Terms as Terms hiding (wk)
open import BorrowedCF.Types
open import BorrowedCF.Types.AtomSnoc using (ClosedAtom; acq)
open import BorrowedCF.Types.AtomUnsnoc using (closedatom-atom)
open import BorrowedCF.Types.AtomCons using (Cons; here; hd; ≃-cons; cons-suffix-unique)

open import BorrowedCF.Safety.Preservation.Handles.AcqProbe using (acq-head-¬mobile)
open import BorrowedCF.Safety.Preservation.Handles.Frames using (fuse2; fuse3; fuse4)
open import BorrowedCF.Safety.Preservation.Handles.Erase using (app-var-[]≼)
open import BorrowedCF.Simulation.Support.Confine using (count; count-self; count0⇒∉dom; ≼⇒count≤)
open import BorrowedCF.Simulation.Support.InvFrame using (strengthen-frame; inv-app; inv-var-count)
open import BorrowedCF.Simulation.Support.Strengthen using (strengthen-Proc-gen; Inverter; inv-weakenᵣ)
open import BorrowedCF.Simulation.Support.AcqInv using (acq-app-nonUnr)
open import BorrowedCF.Simulation.Support.AcqHandle using (count-handle-acq)
open import BorrowedCF.Types.AtomCons using (acq-;-split; acq-;-≄ret)

import BorrowedCF.Context.Substitution as 𝐂

open Variables
open Fin.Patterns

private variable b₁ : ℕ

------------------------------------------------------------------------
-- 1.  Transporting a structure relation across the head type of the
--     context.  Sound as soon as the OLD head type is immobile: `∥′-dup`,
--     `≼-∅` and `∥′-tm-;` are then the only rules that could look at `0F`,
--     and none of them can.
------------------------------------------------------------------------

module _ {n} {Δ₀ : Ctx n} {T T′ : 𝕋} (¬mob : ¬ Mobile T) where

  mobCx-tr : ∀ {α} → MobCx (T ⸴ Δ₀) α → MobCx (T′ ⸴ Δ₀) α
  mobCx-tr []                 = []
  mobCx-tr (x ∥ y)            = mobCx-tr x ∥ mobCx-tr y
  mobCx-tr (x ; y)            = mobCx-tr x ; mobCx-tr y
  mobCx-tr (`_ {x = 0F}    p) = ⊥-elim (¬mob p)
  mobCx-tr (`_ {x = suc y} p) = ` p

  unrCx-tr : ∀ {α} → UnrCx (T ⸴ Δ₀) α → UnrCx (T′ ⸴ Δ₀) α
  unrCx-tr []                 = []
  unrCx-tr (x ∥ y)            = unrCx-tr x ∥ unrCx-tr y
  unrCx-tr (x ; y)            = unrCx-tr x ; unrCx-tr y
  unrCx-tr (`_ {x = 0F}    p) = ⊥-elim (¬mob (unr⇒mobile p))
  unrCx-tr (`_ {x = suc y} p) = ` p

  ≈′-tr : ∀ {α β} → (T ⸴ Δ₀) ∶ α ≈′ β → (T′ ⸴ Δ₀) ∶ α ≈′ β
  ≈′-tr ;′-assoc      = ;′-assoc
  ≈′-tr (;′-cong₁ x)  = ;′-cong₁ (≈′-tr x)
  ≈′-tr (;′-cong₂ x)  = ;′-cong₂ (≈′-tr x)
  ≈′-tr ∥′-unit       = ∥′-unit
  ≈′-tr ∥′-assoc      = ∥′-assoc
  ≈′-tr ∥′-comm       = ∥′-comm
  ≈′-tr (∥′-cong₁ x)  = ∥′-cong₁ (≈′-tr x)
  ≈′-tr (∥′-dup U)    = ∥′-dup (unrCx-tr U)
  ≈′-tr (∥′-tm-; U)   = ∥′-tm-; (Sum.map mobCx-tr mobCx-tr U)

  ≈-tr : ∀ {α β} → (T ⸴ Δ₀) ∶ α ≈ β → (T′ ⸴ Δ₀) ∶ α ≈ β
  ≈-tr = Eq*.gmap id ≈′-tr

  ≼-tr : ∀ {α β} → (T ⸴ Δ₀) ∶ α ≼ β → (T′ ⸴ Δ₀) ∶ α ≼ β
  ≼-tr (≼-refl eq)     = ≼-refl (≈-tr eq)
  ≼-tr (≼-∅ U)         = ≼-∅ (unrCx-tr U)
  ≼-tr ≼-wk            = ≼-wk
  ≼-tr (≼-trans x y)   = ≼-trans (≼-tr x) (≼-tr y)
  ≼-tr (≼-cong-; x y)  = ≼-cong-; (≼-tr x) (≼-tr y)
  ≼-tr (≼-cong-∥ x y)  = ≼-cong-∥ (≼-tr x) (≼-tr y)

------------------------------------------------------------------------
-- 2.  `zap`: the structure substitution that erases `0F` in place.  It is a
--     legal `⇒` between ANY two contexts that differ only at `0F`, because
--     `[]` satisfies every context predicate.
------------------------------------------------------------------------

zap : ∀ {n} → suc n 𝐂.→ₛ suc n
zap 0F      = []
zap (suc y) = ` (suc y)

zap-⇒ : ∀ {n} {T T′ : 𝕋} {Δ₀ : Ctx n} → 𝐂._∶_⇒_ zap (T ⸴ Δ₀) (T′ ⸴ Δ₀)
zap-⇒ 0F      = (λ _ → []) , (λ _ → [])
zap-⇒ (suc y) = (λ u → ` u) , (λ m → ` m)

-- `zap` fixes everything that is weakened past `0F`.
zap-fix : ∀ {m k} (X : Struct m) {ϕ : m 𝐂.→ᵣ suc k} {ψ : m 𝐂.→ᵣ k} →
  (∀ x → ϕ x ≡ suc (ψ x)) →
  (X 𝐂.⋯ᵣ ϕ) 𝐂.⋯ zap ≡ X 𝐂.⋯ᵣ ϕ
zap-fix X {ϕ} eq =
  𝐂.fusion X ϕ zap ■ 𝐂.⋯-congᶜ X (λ x → cong zap (eq x) ■ cong `_ (sym (eq x)))

zap-fix𝓅 : ∀ {m k} (𝒫 : CxPat m) {ϕ : m 𝐂.→ᵣ suc k} {ψ : m 𝐂.→ᵣ k} →
  (∀ x → ϕ x ≡ suc (ψ x)) →
  (𝒫 ⋯𝓅 ϕ) ⋯𝓅 zap ≡ 𝒫 ⋯𝓅 ϕ
zap-fix𝓅 []            eq = refl
zap-fix𝓅 ((d , γ) ∷ 𝒫) eq = cong₂ _∷_ (cong (d ,_) (zap-fix γ eq)) (zap-fix𝓅 𝒫 eq)

------------------------------------------------------------------------
-- 3.  Two structure facts.
------------------------------------------------------------------------

-- Anything a `CxPat` builds around its hole is above the hole in parallel
-- with the pattern's own resources.  (`≼-wk` is what makes the two `;`
-- cases go through -- the hole may sit on either side of a `;`.)
pat-hole-≼ : ∀ {n} {Γ : Ctx n} (𝒫 : CxPat n) {γ : Struct n} →
  Γ ∶ 𝒫 [ γ ]𝓅 ≼ γ ∥ (𝒫 [ [] ]𝓅)
pat-hole-≼ [] = ≼-refl (≈-sym 𝐂.∥-unit₂)
pat-hole-≼ ((𝟙 , δ) ∷ 𝒫) {γ} =
  ≼-trans (≼-cong-∥ (≼-refl ≈-refl) (pat-hole-≼ 𝒫))
    (≼-refl (≈-trans (≈-sym 𝐂.∥-assoc)
      (≈-trans (𝐂.∥-cong 𝐂.∥-comm ≈-refl) 𝐂.∥-assoc)))
pat-hole-≼ ((L , δ) ∷ 𝒫) {γ} =
  ≼-trans (≼-cong-; (≼-refl ≈-refl) (pat-hole-≼ 𝒫))
    (≼-trans (≼-refl (𝐂.;-cong (≈-sym 𝐂.∥-unit₁) ≈-refl))
      (≼-trans ≼-wk (≼-refl (𝐂.∥-cong 𝐂.;-unit₁ ≈-refl))))
pat-hole-≼ ((R , δ) ∷ 𝒫) {γ} =
  ≼-trans (≼-cong-; (pat-hole-≼ 𝒫) (≼-refl ≈-refl))
    (≼-trans (≼-refl (𝐂.;-cong ≈-refl (≈-sym 𝐂.∥-unit₁)))
      (≼-trans ≼-wk (≼-refl (𝐂.∥-cong 𝐂.;-unit₂ ≈-refl))))

-- The handle a constant consumes is below the structure of the redex.
app-var-≼ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {c : Const} {x : 𝔽 n} {T ϵ} →
  Γ ; γ ⊢ K c ·¹ (` x) ∶ T ∣ ϵ → Γ ∶ ` x ≼ γ
app-var-≼ (T-AppUnr _ _ ⊢f ⊢a) =
  ≼-trans (≼-refl (≈-sym 𝐂.∥-unit₁))
    (≼-cong-∥ (inv-K ⊢f .proj₂ .proj₂ .proj₁) (inv-` ⊢a .proj₂))
app-var-≼ (T-AppLin _ _ ⊢f ⊢a) =
  ≼-trans (≼-refl (≈-sym 𝐂.∥-unit₁))
    (≼-cong-∥ (inv-K ⊢f .proj₂ .proj₂ .proj₁) (inv-` ⊢a .proj₂))
app-var-≼ (T-Conv _ _ ⊢e)  = app-var-≼ ⊢e
app-var-≼ (T-Weaken γ≤ ⊢e) = ≼-trans (app-var-≼ ⊢e) γ≤

------------------------------------------------------------------------
-- 4.  Peeling the `acq` off the head of the acquired group.
------------------------------------------------------------------------

private
  ⟨⟩≃ : ∀ {s₁ s₂ : 𝕊 0} → ⟨ s₁ ⟩ ≃ ⟨ s₂ ⟩ → s₁ ≃ s₂
  ⟨⟩≃ ⟨ eq ⟩ = eq

  acq-cancel : ∀ {n} {x y : 𝕊 n} → acq ; x ≃ acq ; y → x ≃ y
  acq-cancel eq
    with _ , c₂ , sx≃z₂ ← ≃-cons acq (λ ()) eq (hd here) =
    ≃-trans (≃-sym ≃-skipˡ)
      (≃-trans (≃-trans sx≃z₂ (cons-suffix-unique (closedatom-atom acq) c₂ (hd here)))
               ≃-skipˡ)

  ¬skips-end : ∀ {s : 𝕊 0} {p} → ¬ Skips (s ; end p)
  ¬skips-end (_ ; ())

  ¬skips-ret : ∀ {s : 𝕊 0} → ¬ Skips (s ; ret)
  ¬skips-ret (_ ; ())

------------------------------------------------------------------------
-- 5.  The `BindCtx` surgery: consume the `acq` at the head of the group
--     that the `cons-acq` node opens.
------------------------------------------------------------------------

-- A zero-width leading group can only be a `cons-acq` node: a
-- `cons-ret/acq` there would need `Skips (s₁ ; ret)`.
bindCtx-0-inv : ∀ {b B} {Γ : Ctx (sum (0 ∷ b ∷ B))} {c : 𝕊 0} →
  BindCtx c (0 ∷ b ∷ B) Γ → BindCtx (acq ; c) (b ∷ B) Γ × AcqHeadCtx Γ
bindCtx-0-inv (cons-ret/acq s₁ s≃ ¬sk (nil (_ ; ())) C ah)
bindCtx-0-inv (cons-acq C ah) = C , ah

bindCtx-acq : ∀ {b B} {Γ : Ctx (suc b + sum B)} {s t : 𝕊 0} {p} →
  (Γ ﹫ 0F) ≃ ⟨ acq ; t ⟩ →
  BindCtx (acq ; (s ; end p)) (suc b ∷ B) Γ →
  BindCtx (s ; end p) (suc b ∷ B) (⟨ t ⟩ ⸴ V.tail Γ)
bindCtx-acq head≃ (last (cons s₁ s₂ ¬sk s-split rest)) =
  last (cons _ s₂ ¬skips-end
    (acq-cancel (≃-trans (≃-sym ≃-assoc-;)
      (≃-trans (≃-; (≃-sym (⟨⟩≃ head≃)) ≃-refl) s-split)))
    rest)
bindCtx-acq {t = t} head≃
  (cons-ret/acq sh s≃ ¬skips₂ (cons s₁ s₂ʰ ¬skʰ hsplit rest) C ah)
  with acq-;-split s≃
... | inj₁ (Ssh , _) =
  ⊥-elim (acq-;-≄ret
    (≃-trans (≃-sym (≃-trans (≃-trans hsplit (≃-; (≃-sym (skips⇒skip≃ Ssh)) ≃-refl)) ≃-skipˡ))
      (≃-trans (≃-; (⟨⟩≃ head≃) ≃-refl) ≃-assoc-;)))
... | inj₂ (h , sh≃ , hs₂≃) =
  cons-ret/acq h hs₂≃ ¬skips₂
    (cons t s₂ʰ ¬skips-ret
      (acq-cancel (≃-trans (≃-sym ≃-assoc-;)
        (≃-trans (≃-; (≃-sym (⟨⟩≃ head≃)) ≃-refl)
          (≃-trans hsplit (≃-trans (≃-; sh≃ ≃-refl) ≃-assoc-;)))))
      rest)
    C ah

------------------------------------------------------------------------
-- 6.  The `TP-Res` frame of a binder list, and the two facts about it that
--     R-Acq needs.
------------------------------------------------------------------------

FrB : ∀ {n} (B B₂ : BindGroup) (γ : Struct n) → Struct (sum B + sum B₂ + n)
FrB {n} B B₂ γ = (structBinder B 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n)
               ∥ (structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum B) 𝐂.⋯ᵣ 𝐂.wkʳ n)
               ∥ (γ 𝐂.⋯ᵣ 𝐂.weaken* (sum B + sum B₂))

private
  rot : ∀ {n} {Γ : Ctx n} {a b c d : Struct n} →
    Γ ∶ a ∥ ((b ∥ c) ∥ d) ≈ ((a ∥ b) ∥ c) ∥ d
  rot = ≈-sym (≈-trans (𝐂.∥-cong 𝐂.∥-assoc ≈-refl) 𝐂.∥-assoc)

-- The leading zero-width group contributes nothing.
fr-0∷ : ∀ {n} (b : ℕ) (B B₂ : BindGroup) (γ : Struct n)
  {Γ : Ctx (sum (0 ∷ suc b ∷ B) + sum B₂ + n)} →
  Γ ∶ FrB (0 ∷ suc b ∷ B) B₂ γ ≈ FrB (suc b ∷ B) B₂ γ
fr-0∷ {n} b B B₂ γ =
  𝐂.∥-cong (𝐂.∥-cong
    (≈-trans (≈-reflexive (cong (λ X → [] ∥ (X 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n))
                                (𝐂.⋯-id (structBinder (suc b ∷ B)) (λ x → refl))))
             𝐂.∥-unit₁)
    ≈-refl) ≈-refl

-- A group of width one: its handle sits in parallel with everything else,
-- so `zap`ping it away and putting it back in front is the identity.
module _ {n} (B₁ B₂ : BindGroup) (γ : Struct n) where
  private
    Tt : Struct (sum (1 ∷ B₁) + sum B₂ + n)
    Tt = structBinder B₁ 𝐂.⋯ᵣ 𝐂.wkˡ 1 𝐂.⋯ᵣ 𝐂.wkʳ (sum B₂) 𝐂.⋯ᵣ 𝐂.wkʳ n

    Gg : Struct (sum (1 ∷ B₁) + sum B₂ + n)
    Gg = structBinder B₂ 𝐂.⋯ᵣ 𝐂.wkˡ (sum (1 ∷ B₁)) 𝐂.⋯ᵣ 𝐂.wkʳ n

    Aa : Struct (sum (1 ∷ B₁) + sum B₂ + n)
    Aa = γ 𝐂.⋯ᵣ 𝐂.weaken* (sum (1 ∷ B₁) + sum B₂)

    zapT : Tt 𝐂.⋯ zap ≡ Tt
    zapT = cong (𝐂._⋯ zap) (fuse3 (structBinder B₁) (𝐂.wkˡ 1) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))
         ■ zap-fix (structBinder B₁) (λ x → refl)
         ■ sym (fuse3 (structBinder B₁) (𝐂.wkˡ 1) (𝐂.wkʳ (sum B₂)) (𝐂.wkʳ n))

    zapG : Gg 𝐂.⋯ zap ≡ Gg
    zapG = cong (𝐂._⋯ zap) (fuse2 (structBinder B₂) (𝐂.wkˡ (sum (1 ∷ B₁))) (𝐂.wkʳ n))
         ■ zap-fix (structBinder B₂) (λ x → refl)
         ■ sym (fuse2 (structBinder B₂) (𝐂.wkˡ (sum (1 ∷ B₁))) (𝐂.wkʳ n))

    zapA : Aa 𝐂.⋯ zap ≡ Aa
    zapA = zap-fix γ (λ x → refl)

    frame-zap : FrB (1 ∷ B₁) B₂ γ 𝐂.⋯ zap ≡ ((([] ; []) ∥ Tt) ∥ Gg) ∥ Aa
    frame-zap = cong₂ _∥_ (cong₂ _∥_ (cong (([] ; []) ∥_) zapT) zapG) zapA

  fr-split : ∀ {Γ : Ctx (sum (1 ∷ B₁) + sum B₂ + n)} →
    Γ ∶ (` 0F) ∥ (FrB (1 ∷ B₁) B₂ γ 𝐂.⋯ zap) ≈ FrB (1 ∷ B₁) B₂ γ
  fr-split =
    ≈-trans (≈-reflexive (cong ((` 0F) ∥_) frame-zap))
      (≈-trans (𝐂.∥-cong ≈-refl (𝐂.∥-cong (𝐂.∥-cong
                  (≈-trans (𝐂.∥-cong 𝐂.;-unit₁ ≈-refl) 𝐂.∥-unit₁) ≈-refl) ≈-refl))
        (≈-trans rot
          (𝐂.∥-cong (𝐂.∥-cong (𝐂.∥-cong (≈-sym 𝐂.;-unit₂) ≈-refl) ≈-refl) ≈-refl)))

------------------------------------------------------------------------
-- 7.  Confinement of the R-Acq redex, with the thinning taken to be
--     `weakenᵣ` itself.  This is `Simulation.Support.SplitConfine.
--     acq-confine` with `mk-thin 0 …` replaced by `inv-weakenᵣ`: that
--     lemma's thinning is `Fin.cast (acqN-eq …) ∘ weakenᵣ` at an
--     existentially quantified scope, so no typed renaming witness can be
--     attached to it downstream.  The counting half is verbatim theirs.
------------------------------------------------------------------------

private
  acq-confine-wk : ∀ {m} {Γ : Ctx m} {γ : Struct m}
    {b₁ : ℕ} {B₁ B₂ : BindGroup}
    {E : Frame* (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)}
    {P : Proc (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)} →
    Γ ; γ ⊢ₚ ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P) →
    Σ (Frame* ((b₁ + sum B₁) + sum B₂ + m)) λ E₀ → (E ≡ E₀ ⋯ᶠ* weakenᵣ)
      × Σ (Proc ((b₁ + sum B₁) + sum B₂ + m)) λ P₀ → P ≡ P₀ ⋯ₚ weakenᵣ
  acq-confine-wk {m = m} {γ = γ} {b₁ = b₁} {B₁ = B₁} {B₂ = B₂} {E = E} {P = P} ⊢P =
    let handle : 𝔽 (sum (zero ∷ suc b₁ ∷ B₁) + sum B₂ + m)
        handle = 0F
        _ , _ , _ , _ , _ , _ , _ , _ , _ , ⊢body = inv-ν ⊢P
        α , β , αβ≼ , ⊢thread , ⊢Ppar = inv-∥ ⊢body
        βplug , (_ , _ , ⊢plug) , support , factor = strengthen-frame E (inv-⟪⟫ ⊢thread)
        ¬u = acq-app-nonUnr ⊢plug
        αfn , αarg , _ , (_ , _ , ⊢arg) , cle-plug = inv-app ⊢plug
        c-αβ≤1 = subst (count handle α + count handle β Nat.≤_)
                       (count-handle-acq b₁ B₁ B₂ γ)
                       (≼⇒count≤ {x = handle} ¬u αβ≼)
        1≤αarg = subst (Nat._≤ count handle αarg) (count-self handle)
                       (inv-var-count ⊢arg handle ¬u)
        1≤βplug = Nat.≤-trans 1≤αarg
                    (Nat.≤-trans (Nat.m≤n+m (count handle αarg) (count handle αfn))
                                 (cle-plug handle ¬u))
        1≤α = Nat.≤-trans 1≤βplug (support handle ¬u)
        α≤βplug = Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (count handle α) (count handle β))
                                           c-αβ≤1) 1≤βplug
        cβ0 = Nat.n≤0⇒n≡0 (Nat.s≤s⁻¹ (Nat.≤-trans (Nat.+-monoˡ-≤ (count handle β) 1≤α) c-αβ≤1))
        E₀ , Eeq = factor handle ¬u α≤βplug weakenᵣ inv-weakenᵣ
        P₀ , Peq = strengthen-Proc-gen ⊢Ppar weakenᵣ handle inv-weakenᵣ (count0⇒∉dom β cβ0)
    in E₀ , Eeq , P₀ , Peq

------------------------------------------------------------------------
-- 8.  The structure step of R-Acq: re-establish the frame bound over the
--     new head type.
------------------------------------------------------------------------

-- `zap` fixes everything that comes from below the binder.
wkₛ : ∀ {m} → m 𝐂.→ₛ suc m
wkₛ = 𝐂.weaken ⦃ 𝐂.Kₛ ⦄

zap-wk : ∀ {m} (X : Struct m) → (X 𝐂.⋯ wkₛ) 𝐂.⋯ zap ≡ X 𝐂.⋯ wkₛ
zap-wk (` x)   = refl
zap-wk []      = refl
zap-wk (α ∥ β) = cong₂ _∥_ (zap-wk α) (zap-wk β)
zap-wk (α ; β) = cong₂ _;_ (zap-wk α) (zap-wk β)

zap-wk𝓅 : ∀ {m} (𝒫 : CxPat m) → (𝒫 ⋯𝓅 wkₛ) ⋯𝓅 zap ≡ 𝒫 ⋯𝓅 wkₛ
zap-wk𝓅 []            = refl
zap-wk𝓅 ((d , γ) ∷ 𝒫) = cong₂ _∷_ (cong (d ,_) (zap-wk γ)) (zap-wk𝓅 𝒫)

-- Either the acquired handle is immobile, or its group has width one.
mob-or-thin : ∀ {b B} {Γ : Ctx (suc b + sum B)} {s : 𝕊 0} {p} →
  New s → BindCtx (acq ; (s ; end p)) (suc b ∷ B) Γ →
  (¬ Mobile (Γ ﹫ 0F)) ⊎ b ≡ 0
mob-or-thin {b = zero}  N C = inj₂ refl
mob-or-thin {b = suc _} N C = inj₁ (acq-head-¬mobile N C)

acq-final : ∀ {n b} {B₁ B₂ : BindGroup} {γ : Struct n} {T₁ : 𝕋} {t : 𝕊 0}
  {Δ₀ : Ctx ((b + sum B₁) + sum B₂ + n)}
  {𝒫₀ : CxPat ((b + sum B₁) + sum B₂ + n)}
  {β₀ : Struct ((b + sum B₁) + sum B₂ + n)}
  {γ′ : Struct (suc ((b + sum B₁) + sum B₂ + n))} {T ϵ} →
  (¬ Mobile T₁) ⊎ b ≡ 0 →
  (T₁ ⸴ Δ₀) ; γ′ ⊢ K `acq ·¹ (` 0F) ∶ T ∣ ϵ →
  (T₁ ⸴ Δ₀) ∶ (((𝒫₀ ⋯𝓅 wkₛ) [ γ′ ]𝓅) ∥ (β₀ 𝐂.⋯ wkₛ))
              ≼ FrB (suc b ∷ B₁) B₂ γ →
  (⟨ t ⟩ ⸴ Δ₀) ∶ (((𝒫₀ ⋯𝓅 wkₛ) [ ` 0F ]𝓅) ∥ (β₀ 𝐂.⋯ wkₛ))
              ≼ FrB (suc b ∷ B₁) B₂ γ
acq-final {𝒫₀ = 𝒫₀} (inj₁ ¬mob) ⊢app mid =
  ≼-tr ¬mob
    (≼-trans (≼-cong-∥ ([-]𝓅-≼ (𝒫₀ ⋯𝓅 wkₛ) (app-var-≼ ⊢app)) (≼-refl ≈-refl)) mid)
acq-final {B₁ = B₁} {B₂ = B₂} {γ = γ} {t = t} {Δ₀ = Δ₀} {𝒫₀ = 𝒫₀} {β₀ = β₀} {γ′ = γ′}
  (inj₂ refl) ⊢app mid =
  ≼-trans (≼-cong-∥ (pat-hole-≼ (𝒫₀ ⋯𝓅 wkₛ)) (≼-refl ≈-refl))
  (≼-trans (≼-refl 𝐂.∥-assoc)
  (≼-trans (≼-cong-∥ (≼-refl ≈-refl)
              (≼-trans (≼-cong-∥ ([-]𝓅-≼ (𝒫₀ ⋯𝓅 wkₛ)
                                    (app-var-[]≼ zap-⇒ refl ⊢app))
                                 (≼-refl ≈-refl))
                       (subst (λ Z → (⟨ t ⟩ ⸴ Δ₀) ∶ Z ≼ (FrB (1 ∷ B₁) B₂ γ 𝐂.⋯ zap)) zap-img
                              (𝐂.≼-⋯ zap-⇒ mid))))
    (≼-refl (fr-split B₁ B₂ γ))))
  where
  zap-img : ((((𝒫₀ ⋯𝓅 wkₛ) [ γ′ ]𝓅) ∥ (β₀ 𝐂.⋯ wkₛ)) 𝐂.⋯ zap)
          ≡ (((𝒫₀ ⋯𝓅 wkₛ) [ γ′ 𝐂.⋯ zap ]𝓅) ∥ (β₀ 𝐂.⋯ wkₛ))
  zap-img = cong₂ _∥_
              ([-]-dist-⋯ (𝒫₀ ⋯𝓅 wkₛ) γ′ zap
                ■ cong (_[ γ′ 𝐂.⋯ zap ]𝓅) (zap-wk𝓅 𝒫₀))
              (zap-wk β₀)

------------------------------------------------------------------------
-- 9.  R-Acq.
------------------------------------------------------------------------

private
  isUnr : ∀ {n} {c T U a ϵ} {Γ : Ctx n} {γ : Struct n} →
    Γ ; γ ⊢ K c ∶ T ⟨ a ⟩→ U ∣ ϵ → Arr.Unr a
  isUnr x = constFnUnr′ (inv-K x .proj₂ .proj₁) (inv-K x .proj₂ .proj₂ .proj₂)

  -- The frame and the parallel process have already been factored through
  -- the thinning that misses the acquired handle.
  pres-Acq′ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {b₁} → ChanCx Γ → ∀ {B₁ B₂}
    {E₀ : Frame* ((b₁ + sum B₁) + sum B₂ + n)}
    {P₀ : Proc ((b₁ + sum B₁) + sum B₂ + n)} →
    Γ ; γ ⊢ₚ ν (zero ∷ suc b₁ ∷ B₁) B₂
      (⟪ (E₀ ⋯ᶠ* weakenᵣ) [ K `acq ·¹ (` 0F) ]* ⟫ ∥ (P₀ ⋯ₚ weakenᵣ)) →
    Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂
      (⟪ (E₀ ⋯ᶠ* weakenᵣ) [ ` 0F ]* ⟫ ∥ (P₀ ⋯ₚ weakenᵣ))
  pres-Acq′ {n = n} {Γ = Γ} {γ = γ} {b₁ = b₁} Γ-S {B₁} {B₂} {E₀} {P₀} ⊢P
    with (T₁ ⸴ Γ₁) , Γ₂ , s , pl , N , ⊢B , ⊢B₂ , C , C′ , ⊢body ← inv-ν ⊢P
    with α , β , ≤αβ , ⊢th , ⊢Pd ← inv-∥ ⊢body
    with 𝒫 , γ′ , _ , _ , _ , _ , ≤α , eqT , ϵ≤ , ⊢E , ⊢app
      ← ⊢[]*⁻¹ (E₀ ⋯ᶠ* weakenᵣ) _ (inv-⟪⟫ ⊢th)
    with _ , _ , _ , _ , _ , _ , _ , ⊢fn , ⊢arg ← inv-·-unr ⊢app isUnr
    with _ , eqA `→ eqU , _ , `acq ← inv-K ⊢fn
    with C₁ , ah ← bindCtx-0-inv C
    = let Δ₀   = (Γ₁ ⸴* Γ₂) ⸴* Γ
          ⊢wkO = ⊢weakenᵣ {T = T₁} Δ₀
          ⊢wkN = ⊢weakenᵣ {T = ⟨ _ ⟩} Δ₀
          𝒫₀ , ≤𝒫 , ⊢E₀′ = ⊢E  ⊢⋯ᶠ*⁻¹ ⊢wkO / wk*-inj 1
          β₀ , ≤β , ⊢P₀′ = ⊢Pd ⊢⋯ₚ⁻¹  ⊢wkO / wk*-inj 1
          mid = ≼-trans (≼-cong-∥ (≼-trans (≤𝒫 (≼-refl ≈-refl)) ≤α) ≤β)
                  (≼-trans ≤αβ (≼-refl (fr-0∷ b₁ B₁ B₂ γ)))
      in TP-Res N pl (All.tail ⊢B) ⊢B₂
           (bindCtx-acq (≃-sym (≃-trans eqA (inv-` ⊢arg .proj₁))) C₁) C′
           (TP-Weaken (acq-final {b = b₁} {B₁ = B₁} {B₂ = B₂} {γ = γ} {𝒫₀ = 𝒫₀} {β₀ = β₀}
                        (mob-or-thin N C₁) ⊢app mid)
             (TP-Par
               (TP-Expr (T-Conv eqT ϵ≤
                 ⊢⟨ (⊢E₀′ ⊢⋯ᶠ* ⊢wkN) [ T-Conv eqU ℙ≤ϵ (T-Var 0F refl) ]*⟩))
               (⊢P₀′ ⊢⋯ₚ ⊢wkN)))

-- R-Acq
pres-Acq : ∀ {n} {Γ : Ctx n} {γ : Struct n} {b₁} → ChanCx Γ → ∀ {B₁ B₂}
  {E : Frame* (sum (suc b₁ ∷ B₁) + sum B₂ + n)}
  {P : Proc (sum (suc b₁ ∷ B₁) + sum B₂ + n)} →
  Γ ; γ ⊢ₚ ν (zero ∷ suc b₁ ∷ B₁) B₂ (⟪ E [ K `acq ·¹ (` 0F) ]* ⟫ ∥ P) →
  Γ ; γ ⊢ₚ ν (suc b₁ ∷ B₁) B₂ (⟪ E [ ` zero ]* ⟫ ∥ P)
pres-Acq Γ-S {B₁ = B₁} {B₂ = B₂} {E = E} {P = P} ⊢P
  with acq-confine-wk {B₁ = B₁} {B₂ = B₂} {E = E} {P = P} ⊢P
... | E₀ , refl , P₀ , refl = pres-Acq′ Γ-S {B₁ = B₁} {B₂ = B₂} {E₀ = E₀} {P₀ = P₀} ⊢P
