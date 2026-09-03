-- | Phase 4a, TERM LEVEL (`BackwardSoup/PLAN.md` §9, P3 / §8(c)).
--
--   THE THREAD LEMMA.  Inside ONE thread `E [ K c ·¹ (` x) ]*` whose hole is
--   an IMPURE handle-consuming redex, no other handle `x′` is `;`-BEFORE the
--   consumed handle `x`:
--
--     thread-¬before : ImpureHandleConst c →
--       Γ ; γ ⊢ E [ K c ·¹ (` x) ]* ∶ T ∣ ϵ →
--       ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ x′) → x′ ≢ x →
--       count x γ ≤ 1 → ¬ before x′ x γ
--
--   (and the `send` variant `thread-pair-¬before`, whose hole is
--   `K c ·¹ (w ⊗ (` x))`).
--
--   The proof is `Probes2` §7(e) in general form.  `⊢[]*⁻¹` decomposes the
--   thread's structure as `𝒫 [ γ′ ]𝓅 ≼ γ`, where `γ′` types the hole and the
--   context pattern `𝒫 : CxPat n` is the list of the frames' own structures,
--   each tagged with the DIRECTION in which the frame joins it to the hole.
--   Only three frames use direction `L`, i.e. put their resources `;`-BEFORE
--   the hole -- `app₁ v` with `Arr.IsL a`, `app₂ v` with `Arr.IsR a`, and
--   `v ⊗□` with `p/s ≡ seq` -- and each of them forces the hole to be PURE
--   (`§2`), contradicting the `𝕀` effect of the impure constant (`§1`).  What
--   remains is a pattern of `R`/`𝟙` entries, which can only place the frames
--   `;`-AFTER or in parallel with the hole (`§4`); LINEARITY (`count x γ ≤ 1`,
--   the handle occurs once) then says the frames do not mention `x` at all.
module BorrowedCF.Simulation.BackwardSoup.Position.ThreadOrder where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Types
open import BorrowedCF.Context
open import BorrowedCF.Context.Pattern
open import BorrowedCF.Reduction.Base

open import BorrowedCF.Simulation.Support.Confine
  using (count; count-self; count-join-Dir; count-join-PS; +≡0)
open import BorrowedCF.Simulation.BackwardSoup.Position

open Nat using (_≤_; _<_; z≤n; s≤s)
open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 0.  Arithmetic and effect scaffolding.

private
  ≤ϵ-reflexive : ϵ₁ ≡ ϵ₂ → ϵ₁ ≤ϵ ϵ₂
  ≤ϵ-reflexive refl = ≤ϵ-refl

  𝕀≤⇒≡𝕀 : 𝕀 ≤ϵ ϵ → ϵ ≡ 𝕀
  𝕀≤⇒≡𝕀 𝕀≤𝕀 = refl

  -- `a + b ≤ 1` with `b` non-zero forces `a ≡ 0`.
  split≤1 : ∀ {a b} → a + b ≤ 1 → 1 ≤ b → (a ≡ 0) × (b ≤ 1)
  split≤1 {zero}  le 1≤ = refl , le
  split≤1 {suc a} {b} (s≤s le) 1≤ =
    ⊥-elim (case subst (1 ≤_) (proj₂ (+≡0 (Nat.n≤0⇒n≡0 le))) 1≤ of λ ())

  count-other : ∀ {n} {x z : 𝔽 n} → z ≢ x → count z (` x) ≡ 0
  count-other {x = x} {z} z≢ with z Fin.≟ x
  ... | yes eq = ⊥-elim (z≢ eq)
  ... | no  _  = refl

  -- The three `Arr` directions, with the effect side conditions of `TF-app₁` /
  -- `TF-app₂`: the effect never drops outwards, and an IMPURE hole excludes
  -- the direction that would place the frame's resources `;`-before it.
  arrCases : ∀ (a : Arr) {ϵ ϵ₁ ϵ₂} →
    (Arr.Par a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ϵ) →
    (Arr.IsL a → ϵ₁ ≡ ℙ × ϵ₂ ≡ ϵ) →
    (Arr.IsR a → ϵ₁ ≡ ϵ × ϵ₂ ≡ ℙ) →
    (ϵ₁ ≤ϵ ϵ) × (ϵ₂ ≤ϵ ϵ)
      × (ϵ₁ ≡ 𝕀 → Arr.dir a ≢ L)
      × (ϵ₂ ≡ 𝕀 → flipDir (Arr.dir a) ≢ L)
  arrCases a {ϵ} {ϵ₁} {ϵ₂} appPar appLeft appRight = go (Arr.dir a) refl
    where
    go : (d : Dir) → Arr.dir a ≡ d →
         (ϵ₁ ≤ϵ ϵ) × (ϵ₂ ≤ϵ ϵ)
           × (ϵ₁ ≡ 𝕀 → Arr.dir a ≢ L)
           × (ϵ₂ ≡ 𝕀 → flipDir (Arr.dir a) ≢ L)
    go 𝟙 eq = ≤ϵ-reflexive (proj₁ (appPar eq))
            , ≤ϵ-reflexive (proj₂ (appPar eq))
            , (λ _ dL → case sym eq ■ dL of λ ())
            , (λ _ fdL → case cong flipDir (sym eq) ■ fdL of λ ())
    go L eq = subst (_≤ϵ ϵ) (sym (proj₁ (appLeft eq))) ℙ≤ϵ
            , ≤ϵ-reflexive (proj₂ (appLeft eq))
            , (λ is𝕀 _ → case sym (proj₁ (appLeft eq)) ■ is𝕀 of λ ())
            , (λ _ fdL → case cong flipDir (sym eq) ■ fdL of λ ())
    go R eq = ≤ϵ-reflexive (proj₁ (appRight eq))
            , subst (_≤ϵ ϵ) (sym (proj₂ (appRight eq))) ℙ≤ϵ
            , (λ _ dL → case sym eq ■ dL of λ ())
            , (λ is𝕀 _ → case sym (proj₂ (appRight eq)) ■ is𝕀 of λ ())

------------------------------------------------------------------------
-- 1.  An impure handle-consuming constant has effect `𝕀`.

impure-fn-eff :
  ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
  ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ → Arr.eff a ≡ 𝕀
impure-fn-eff `discard  (T-Const `discard)   = refl
impure-fn-eff `drop     (T-Const `drop)      = refl
impure-fn-eff `send     (T-Const (`send _))  = refl
impure-fn-eff `recv     (T-Const (`recv _))  = refl
impure-fn-eff `select   (T-Const `select)    = refl
impure-fn-eff `branch   (T-Const `branch)    = refl
impure-fn-eff `end      (T-Const `end)       = refl
impure-fn-eff ic (T-Conv (_ `→ _) _ d) = impure-fn-eff ic d
impure-fn-eff ic (T-Weaken _ d)        = impure-fn-eff ic d

impure-app-eff :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {e : Tm n} {dir} {T ϵ} →
  ImpureHandleConst c → Γ ; γ ⊢ K c ·⟨ dir ⟩ e ∶ T ∣ ϵ → ϵ ≡ 𝕀
impure-app-eff ic (T-AppUnr   _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (impure-fn-eff ic ⊢fn) ≤ₐ)
impure-app-eff ic (T-AppLin   _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (impure-fn-eff ic ⊢fn) ≤ₐ)
impure-app-eff ic (T-AppLeft  _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (impure-fn-eff ic ⊢fn) ≤ₐ)
impure-app-eff ic (T-AppRight _ ≤ₐ ⊢fn _) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (impure-fn-eff ic ⊢fn) ≤ₐ)
impure-app-eff ic (T-Conv _ ϵ≤ d) = 𝕀≤⇒≡𝕀 (subst (_≤ϵ _) (impure-app-eff ic d) ϵ≤)
impure-app-eff ic (T-Weaken _ d)  = impure-app-eff ic d

------------------------------------------------------------------------
-- 2.  Frames: the effect grows outwards, and an IMPURE hole admits no
--     `L`-directed frame.

-- `NoPre 𝒫`: no entry of the context pattern joins its structure to the LEFT
-- of the hole, i.e. no frame puts its own resources `;`-before the hole.
NoPre : ∀ {n} → CxPat n → Set
NoPre L.[] = ⊤
NoPre ((d , _) L.∷ 𝒫) = (d ≢ L) × NoPre 𝒫

NoPre-++ : ∀ {n} (𝒫₁ 𝒫₂ : CxPat n) → NoPre 𝒫₁ → NoPre 𝒫₂ → NoPre (𝒫₁ L.++ 𝒫₂)
NoPre-++ L.[] 𝒫₂ np₁ np₂ = np₂
NoPre-++ ((d , α) L.∷ 𝒫₁) 𝒫₂ (d≢L , np₁) np₂ = d≢L , NoPre-++ 𝒫₁ 𝒫₂ np₁ np₂

frame-eff-mono :
  ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame n} {T U ϵ₁ ϵ₂} →
  Γ ; 𝒫 ⊢ E ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → ϵ₁ ≤ϵ ϵ₂
frame-eff-mono (TF-app₁ {a = a} _ appPar appLeft appRight _) =
  proj₁ (arrCases a appPar appLeft appRight)
frame-eff-mono (TF-app₂ {a = a} _ appPar appLeft appRight _) =
  proj₁ (proj₂ (arrCases a appPar appLeft appRight))
frame-eff-mono (TF-□⊗ _ _ _)      = ≤ϵ-refl
frame-eff-mono (TF-⊗□ _ par _)    = ≤ϵ-refl
frame-eff-mono (TF-⊗□ _ seq _)    = ℙ≤ϵ
frame-eff-mono (TF-; _ _)         = ≤ϵ-refl
frame-eff-mono (TF-`let _ _ _)    = ≤ϵ-refl
frame-eff-mono (TF-`let⊗ _ _ _)   = ≤ϵ-refl
frame-eff-mono (TF-`inj□ _)       = ≤ϵ-refl
frame-eff-mono (TF-`case□ _ _ _ _) = ≤ϵ-refl

frames-eff-mono :
  ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame* n} {T U ϵ₁ ϵ₂} →
  Γ ; 𝒫 ⊢* E ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → ϵ₁ ≤ϵ ϵ₂
frames-eff-mono [] = ≤ϵ-refl
frames-eff-mono (⊢E ∷⟨ _ , ϵ≤ ⟩ ⊢E*) =
  ≤ϵ-trans (≤ϵ-trans (frames-eff-mono ⊢E*) ϵ≤) (frame-eff-mono ⊢E)

frame-noL :
  ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame n} {T U ϵ₁ ϵ₂} →
  Γ ; 𝒫 ⊢ E ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → ϵ₁ ≡ 𝕀 → NoPre 𝒫
frame-noL (TF-app₁ {a = a} _ appPar appLeft appRight _) is𝕀 =
  proj₁ (proj₂ (proj₂ (arrCases a appPar appLeft appRight))) is𝕀 , tt
frame-noL (TF-app₂ {a = a} _ appPar appLeft appRight _) is𝕀 =
  proj₂ (proj₂ (proj₂ (arrCases a appPar appLeft appRight))) is𝕀 , tt
frame-noL (TF-□⊗ par _ _) is𝕀 = (λ ()) , tt
frame-noL (TF-□⊗ seq _ _) is𝕀 = (λ ()) , tt
frame-noL (TF-⊗□ par _ _) is𝕀 = (λ ()) , tt
frame-noL (TF-⊗□ seq seq _) is𝕀 = ⊥-elim (case is𝕀 of λ ())
frame-noL (TF-; _ _)       is𝕀 = (λ ()) , tt
frame-noL (TF-`let _ par _) is𝕀 = (λ ()) , tt
frame-noL (TF-`let _ seq _) is𝕀 = (λ ()) , tt
frame-noL (TF-`let⊗ _ par _) is𝕀 = (λ ()) , tt
frame-noL (TF-`let⊗ _ seq _) is𝕀 = (λ ()) , tt
frame-noL (TF-`inj□ _)     is𝕀 = tt
frame-noL (TF-`case□ _ par _ _) is𝕀 = (λ ()) , tt
frame-noL (TF-`case□ _ seq _ _) is𝕀 = (λ ()) , tt

frames-noL :
  ∀ {n} {Γ : Ctx n} {𝒫 : CxPat n} {E : Frame* n} {T U ϵ₁ ϵ₂} →
  Γ ; 𝒫 ⊢* E ∶ T ∣ ϵ₁ ⟶ U ∣ ϵ₂ → ϵ₁ ≡ 𝕀 → NoPre 𝒫
frames-noL [] _ = tt
frames-noL {𝒫 = _} (_∷⟨_⟩_ {𝒫₁ = 𝒫₁} {𝒫₂ = 𝒫₂} ⊢E (_ , ϵ≤) ⊢E*) refl =
  NoPre-++ 𝒫₁ 𝒫₂
    (frame-noL ⊢E (𝕀≤⇒≡𝕀 (≤ϵ-trans (frames-eff-mono ⊢E*) ϵ≤)))
    (frames-noL ⊢E* refl)

------------------------------------------------------------------------
-- 3.  Counting the handle in the hole's structure.

const-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {T ϵ} (z : 𝔽 n) →
  ¬ Unr (Γ ﹫ z) → Γ ; γ ⊢ K c ∶ T ∣ ϵ → count z γ ≡ 0
const-count z ¬u ⊢c = sym (count-≼-eq ¬u (proj₁ (proj₂ (proj₂ (inv-K ⊢c)))))

var-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {T ϵ} (z : 𝔽 n) →
  ¬ Unr (Γ ﹫ z) → Γ ; γ ⊢ ` x ∶ T ∣ ϵ → count z γ ≡ count z (` x)
var-count z ¬u ⊢x = sym (count-≼-eq ¬u (proj₂ (inv-` ⊢x)))

-- The structure of `K c ·⟨ d ⟩ (` x)` counts exactly the handle `x`.
app-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {x : 𝔽 n} {dir} {T ϵ} (z : 𝔽 n) →
  ¬ Unr (Γ ﹫ z) → Γ ; γ ⊢ K c ·⟨ dir ⟩ (` x) ∶ T ∣ ϵ → count z γ ≡ count z (` x)
app-count z ¬u (T-AppUnr _ _ ⊢fn ⊢arg) =
  cong₂ _+_ (const-count z ¬u ⊢fn) (var-count z ¬u ⊢arg)
app-count z ¬u (T-AppLin _ _ ⊢fn ⊢arg) =
  cong₂ _+_ (const-count z ¬u ⊢fn) (var-count z ¬u ⊢arg)
app-count z ¬u (T-AppLeft _ _ ⊢fn ⊢arg) =
  cong₂ _+_ (var-count z ¬u ⊢arg) (const-count z ¬u ⊢fn) ■ +-identityʳ _
app-count z ¬u (T-AppRight _ _ ⊢fn ⊢arg) =
  cong₂ _+_ (const-count z ¬u ⊢fn) (var-count z ¬u ⊢arg)
app-count z ¬u (T-Conv _ _ d) = app-count z ¬u d
app-count z ¬u (T-Weaken γ≤ d) = sym (count-≼-eq ¬u γ≤) ■ app-count z ¬u d

------------------------------------------------------------------------
-- 4.  The context pattern: `NoPre` plus linearity kills every `;`-order.

pat-count-mono :
  ∀ {n} (𝒫 : CxPat n) (γ : Struct n) (z : 𝔽 n) → count z γ ≤ count z (𝒫 [ γ ]𝓅)
pat-count-mono L.[] γ z = Nat.≤-refl
pat-count-mono ((d , α) L.∷ 𝒫) γ z =
  Nat.≤-trans (pat-count-mono 𝒫 γ z)
    (subst (count z (𝒫 [ γ ]𝓅) ≤_)
      (sym (count-join-Dir d z α (𝒫 [ γ ]𝓅)))
      (Nat.m≤n+m (count z (𝒫 [ γ ]𝓅)) (count z α)))

pat-¬before :
  ∀ {n} {x y′ : 𝔽 n} (𝒫 : CxPat n) (γ′ : Struct n) →
  NoPre 𝒫 → 1 ≤ count x γ′ → count x (𝒫 [ γ′ ]𝓅) ≤ 1 →
  ¬ before y′ x γ′ → ¬ before y′ x (𝒫 [ γ′ ]𝓅)
pat-¬before L.[] γ′ np 1≤ ≤1 base b = base b
pat-¬before ((L , α) L.∷ 𝒫) γ′ (d≢L , np) 1≤ ≤1 base b = ⊥-elim (d≢L refl)
pat-¬before {x = x} {y′} ((𝟙 , α) L.∷ 𝒫) γ′ (_ , np) 1≤ ≤1 base b
  with split≤1 ≤1 (Nat.≤-trans 1≤ (pat-count-mono 𝒫 γ′ x))
... | cα0 , ≤1′ with b
... | inj₁ bα = ¬before-∉ʳ y′ x α cα0 bα
... | inj₂ br = pat-¬before 𝒫 γ′ np 1≤ ≤1′ base br
pat-¬before {x = x} {y′} ((R , α) L.∷ 𝒫) γ′ (_ , np) 1≤ ≤1 base b
  with split≤1
         (subst (_≤ 1) (Nat.+-comm (count x (𝒫 [ γ′ ]𝓅)) (count x α)) ≤1)
         (Nat.≤-trans 1≤ (pat-count-mono 𝒫 γ′ x))
... | cα0 , ≤1′ with b
... | inj₁ (_ , x∈α) = x∈α cα0
... | inj₂ (inj₁ br) = pat-¬before 𝒫 γ′ np 1≤ ≤1′ base br
... | inj₂ (inj₂ bα) = ¬before-∉ʳ y′ x α cα0 bα

------------------------------------------------------------------------
-- 5.  The thread lemma, abstracted over the hole.

plug-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {x : 𝔽 n} {T ϵ}
    (E : Frame* n) (h : Tm n) →
  Γ ; γ ⊢ E [ h ]* ∶ T ∣ ϵ →
  (∀ {γ′ U ϵ′} → Γ ; γ′ ⊢ h ∶ U ∣ ϵ′ → 1 ≤ count x γ′) →
  ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ
plug-count {x = x} E h ⊢plug holeCount ¬ux with ⊢[]*⁻¹ E h ⊢plug
... | 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , _ , _ , _ , ⊢hole =
  subst (1 ≤_) (count-≼-eq ¬ux ≤γ)
    (Nat.≤-trans (holeCount ⊢hole) (pat-count-mono 𝒫 γ′ x))

plug-¬before :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {x y′ : 𝔽 n} {T ϵ}
    (E : Frame* n) (h : Tm n) →
  Γ ; γ ⊢ E [ h ]* ∶ T ∣ ϵ →
  (∀ {γ′ U ϵ′} → Γ ; γ′ ⊢ h ∶ U ∣ ϵ′ → ϵ′ ≡ 𝕀) →
  (∀ {γ′ U ϵ′} → Γ ; γ′ ⊢ h ∶ U ∣ ϵ′ → 1 ≤ count x γ′) →
  (∀ {γ′ U ϵ′} → Γ ; γ′ ⊢ h ∶ U ∣ ϵ′ → count x γ′ ≤ 1 → ¬ before y′ x γ′) →
  ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) →
  count x γ ≤ 1 → ¬ before y′ x γ
plug-¬before {Γ = Γ} {x = x} {y′ = y′} E h ⊢plug holeEff holeCount holeBase ¬mx ¬my ≤1 b
  with ⊢[]*⁻¹ E h ⊢plug
... | 𝒫 , γ′ , _ , _ , _ , _ , ≤γ , _ , _ , ⊢E* , ⊢hole =
  pat-¬before 𝒫 γ′
    (frames-noL ⊢E* (holeEff ⊢hole))
    (holeCount ⊢hole)
    ≤1′
    (holeBase ⊢hole (Nat.≤-trans (pat-count-mono 𝒫 γ′ x) ≤1′))
    (before-mono-≼ ¬my ¬mx ≤γ b)
  where
    ¬ux : ¬ Unr (Γ ﹫ x)
    ¬ux = ¬mx ∘ unr⇒mobile
    ≤1′ : count x (𝒫 [ γ′ ]𝓅) ≤ 1
    ≤1′ = subst (_≤ 1) (sym (count-≼-eq ¬ux ≤γ)) ≤1

------------------------------------------------------------------------
-- 6.  The two instances.

thread-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {E : Frame* n} {c} {x : 𝔽 n} {T ϵ} →
  Γ ; γ ⊢ E [ K c ·¹ (` x) ]* ∶ T ∣ ϵ → ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ
thread-count {E = E} {c = c} {x = x} ⊢plug ¬ux =
  plug-count E (K c ·¹ (` x)) ⊢plug
    (λ ⊢h → subst (1 ≤_) (sym (app-count x ¬ux ⊢h ■ count-self x)) Nat.≤-refl)
    ¬ux

thread-¬before :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {E : Frame* n} {c} {x y′ : 𝔽 n} {T ϵ} →
  ImpureHandleConst c →
  Γ ; γ ⊢ E [ K c ·¹ (` x) ]* ∶ T ∣ ϵ →
  ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) → y′ ≢ x →
  count x γ ≤ 1 → ¬ before y′ x γ
thread-¬before {E = E} {c = c} {x = x} {y′ = y′} ic ⊢plug ¬mx ¬my y′≢x ≤1 =
  plug-¬before E (K c ·¹ (` x)) ⊢plug
    (impure-app-eff ic)
    (λ ⊢h → subst (1 ≤_) (sym (app-count x ¬ux ⊢h ■ count-self x)) Nat.≤-refl)
    (λ ⊢h _ → ¬before-∉ˡ y′ x _ (app-count y′ ¬uy ⊢h ■ count-other y′≢x))
    ¬mx ¬my ≤1
  where
    ¬ux = ¬mx ∘ unr⇒mobile
    ¬uy = ¬my ∘ unr⇒mobile

------------------------------------------------------------------------
-- 7.  The `send` variant: the handle is the SECOND COMPONENT of a pair.

-- Only `send` has a pair domain among the impure handle constants, and its
-- pair is `⊗¹`: the two components are joined in PARALLEL, never by `;`.
impure-dom-⊗ :
  ∀ {n} {Γ : Ctx n} {β : Struct n} {c} {Tᵈ U a ϵ} →
  ImpureHandleConst c → Γ ; β ⊢ K c ∶ Tᵈ ⟨ a ⟩→ U ∣ ϵ →
  ∀ {T₁ T₂ : 𝕋} {d} → T₁ ⊗⟨ d ⟩ T₂ ≃ Tᵈ → d ≡ 𝟙
impure-dom-⊗ `discard (T-Const `discard)  ()
impure-dom-⊗ `drop    (T-Const `drop)     ()
impure-dom-⊗ `send    (T-Const (`send _)) (_ ⊗ _) = refl
impure-dom-⊗ `recv    (T-Const (`recv _)) ()
impure-dom-⊗ `select  (T-Const `select)   ()
impure-dom-⊗ `branch  (T-Const `branch)   ()
impure-dom-⊗ `end     (T-Const `end)      ()
impure-dom-⊗ ic (T-Conv (dom≃ `→ _) _ dd) eq =
  impure-dom-⊗ ic dd (≃-trans eq (≃-sym dom≃))
impure-dom-⊗ ic (T-Weaken _ dd) eq = impure-dom-⊗ ic dd eq

private
  bumpˡ : ∀ {n} {x : 𝔽 n} (γ₁ γ₂ : Struct n) →
    count x γ₁ ≡ 0 → 1 ≤ count x γ₂ → 1 ≤ count x γ₁ + count x γ₂
  bumpˡ {x = x} γ₁ γ₂ c0 le = subst (λ k → 1 ≤ k + count x γ₂) (sym c0) le

  bumpʳ : ∀ {n} {x : 𝔽 n} (γ₂ γ₁ : Struct n) →
    count x γ₁ ≡ 0 → 1 ≤ count x γ₂ → 1 ≤ count x γ₂ + count x γ₁
  bumpʳ {x = x} γ₂ γ₁ c0 le =
    subst (λ k → 1 ≤ count x γ₂ + k) (sym c0)
      (subst (1 ≤_) (sym (+-identityʳ (count x γ₂))) le)

  shrinkˡ : ∀ {n} {x : 𝔽 n} (γ₁ γ₂ : Struct n) →
    count x γ₁ ≡ 0 → count x γ₁ + count x γ₂ ≤ 1 → count x γ₂ ≤ 1
  shrinkˡ {x = x} γ₁ γ₂ c0 le = subst (λ k → k + count x γ₂ ≤ 1) c0 le

  shrinkʳ : ∀ {n} {x : 𝔽 n} (γ₂ γ₁ : Struct n) →
    count x γ₁ ≡ 0 → count x γ₂ + count x γ₁ ≤ 1 → count x γ₂ ≤ 1
  shrinkʳ {x = x} γ₂ γ₁ c0 le =
    subst (_≤ 1) (+-identityʳ (count x γ₂)) (subst (λ k → count x γ₂ + k ≤ 1) c0 le)

  -- combining the constant's (empty) structure with the argument's
  nb-∥ : ∀ {n} {x y′ : 𝔽 n} (γ₁ γ₂ : Struct n) →
    count y′ γ₁ ≡ 0 → ¬ before y′ x γ₂ → ¬ before y′ x (γ₁ ∥ γ₂)
  nb-∥ {x = x} {y′} γ₁ γ₂ c0y nb = [ ¬before-∉ˡ y′ x γ₁ c0y , nb ]′

  -- `T-AppRight`: the constant's structure comes FIRST
  nb-;ˡ : ∀ {n} {x y′ : 𝔽 n} (γ₁ γ₂ : Struct n) →
    count y′ γ₁ ≡ 0 → ¬ before y′ x γ₂ → ¬ before y′ x (γ₁ ; γ₂)
  nb-;ˡ γ₁ γ₂ c0y nb (inj₁ (y′∈ , _)) = y′∈ c0y
  nb-;ˡ {x = x} {y′} γ₁ γ₂ c0y nb (inj₂ (inj₁ bb)) = ¬before-∉ˡ y′ x γ₁ c0y bb
  nb-;ˡ γ₁ γ₂ c0y nb (inj₂ (inj₂ bb)) = nb bb

  -- `T-AppLeft`: the constant's structure comes SECOND
  nb-;ʳ : ∀ {n} {x y′ : 𝔽 n} (γ₂ γ₁ : Struct n) →
    count x γ₁ ≡ 0 → ¬ before y′ x γ₂ → ¬ before y′ x (γ₂ ; γ₁)
  nb-;ʳ γ₂ γ₁ c0x nb (inj₁ (_ , x∈)) = x∈ c0x
  nb-;ʳ γ₂ γ₁ c0x nb (inj₂ (inj₁ bb)) = nb bb
  nb-;ʳ {x = x} {y′} γ₂ γ₁ c0x nb (inj₂ (inj₂ bb)) = ¬before-∉ʳ y′ x γ₁ c0x bb

pair-arg-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {w : Tm n} {x : 𝔽 n} {Tᵈ ϵ} →
  Γ ; γ ⊢ w ⊗ (` x) ∶ Tᵈ ∣ ϵ → ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ
pair-arg-count {x = x} ⊢pair ¬ux with inv-⊗ ⊢pair
... | p/s , α , β , _ , _ , _ , _ , ≤γ , _ , _ , _ , _ , ⊢x =
  subst (1 ≤_) (count-≼-eq ¬ux ≤γ)
    (subst (1 ≤_) (sym (count-join-PS p/s x α β))
      (subst (λ k → 1 ≤ count x α + k)
        (sym (var-count x ¬ux ⊢x ■ count-self x))
        (Nat.m≤n+m 1 (count x α))))

pair-arg-¬before :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {w : Tm n} {x y′ : 𝔽 n} {Tᵈ ϵ} →
  Γ ; γ ⊢ w ⊗ (` x) ∶ Tᵈ ∣ ϵ →
  (∀ {T₁ T₂ : 𝕋} {d} → T₁ ⊗⟨ d ⟩ T₂ ≃ Tᵈ → d ≡ 𝟙) →
  ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) → y′ ≢ x →
  count x γ ≤ 1 → ¬ before y′ x γ
pair-arg-¬before {x = x} {y′ = y′} ⊢pair d𝟙 ¬mx ¬my y′≢x ≤1 b with inv-⊗ ⊢pair
... | seq , _ , _ , _ , _ , _ , _ , _ , tyEq , _ , _ , _ , _ = case d𝟙 tyEq of λ ()
... | par , α , β , _ , _ , _ , _ , ≤γ , _ , _ , _ , _ , ⊢x =
  [ ¬before-∉ʳ y′ x α cxα0 , ¬before-∉ˡ y′ x β cyβ ]′ (before-mono-≼ ¬my ¬mx ≤γ b)
  where
    ¬ux = ¬mx ∘ unr⇒mobile
    ¬uy = ¬my ∘ unr⇒mobile
    cxβ : count x β ≡ 1
    cxβ = var-count x ¬ux ⊢x ■ count-self x
    cyβ : count y′ β ≡ 0
    cyβ = var-count y′ ¬uy ⊢x ■ count-other y′≢x
    cxα0 : count x α ≡ 0
    cxα0 = proj₁ (split≤1 (subst (_≤ 1) (sym (count-≼-eq ¬ux ≤γ)) ≤1)
                          (subst (1 ≤_) (sym cxβ) Nat.≤-refl))

pair-hole-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {w : Tm n} {x : 𝔽 n} {dir} {T ϵ} →
  Γ ; γ ⊢ K c ·⟨ dir ⟩ (w ⊗ (` x)) ∶ T ∣ ϵ → ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ
pair-hole-count {x = x} (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬ux =
  bumpˡ γ₁ γ₂ (const-count x ¬ux ⊢fn) (pair-arg-count ⊢arg ¬ux)
pair-hole-count {x = x} (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬ux =
  bumpˡ γ₁ γ₂ (const-count x ¬ux ⊢fn) (pair-arg-count ⊢arg ¬ux)
pair-hole-count {x = x} (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬ux =
  bumpʳ γ₂ γ₁ (const-count x ¬ux ⊢fn) (pair-arg-count ⊢arg ¬ux)
pair-hole-count {x = x} (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬ux =
  bumpˡ γ₁ γ₂ (const-count x ¬ux ⊢fn) (pair-arg-count ⊢arg ¬ux)
pair-hole-count (T-Conv _ _ dd) ¬ux = pair-hole-count dd ¬ux
pair-hole-count (T-Weaken γ≤ dd) ¬ux =
  subst (1 ≤_) (count-≼-eq ¬ux γ≤) (pair-hole-count dd ¬ux)

pair-hole-¬before :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {c} {w : Tm n} {x y′ : 𝔽 n} {dir} {T ϵ} →
  ImpureHandleConst c →
  Γ ; γ ⊢ K c ·⟨ dir ⟩ (w ⊗ (` x)) ∶ T ∣ ϵ →
  ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) → y′ ≢ x →
  count x γ ≤ 1 → ¬ before y′ x γ
pair-hole-¬before {x = x} {y′ = y′} ic (T-AppUnr {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬mx ¬my y′≢x ≤1 =
  nb-∥ γ₁ γ₂ (const-count y′ (¬my ∘ unr⇒mobile) ⊢fn)
    (pair-arg-¬before ⊢arg (impure-dom-⊗ ic ⊢fn) ¬mx ¬my y′≢x
      (shrinkˡ γ₁ γ₂ (const-count x (¬mx ∘ unr⇒mobile) ⊢fn) ≤1))
pair-hole-¬before {x = x} {y′ = y′} ic (T-AppLin {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬mx ¬my y′≢x ≤1 =
  nb-∥ γ₁ γ₂ (const-count y′ (¬my ∘ unr⇒mobile) ⊢fn)
    (pair-arg-¬before ⊢arg (impure-dom-⊗ ic ⊢fn) ¬mx ¬my y′≢x
      (shrinkˡ γ₁ γ₂ (const-count x (¬mx ∘ unr⇒mobile) ⊢fn) ≤1))
pair-hole-¬before {x = x} {y′ = y′} ic (T-AppLeft {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬mx ¬my y′≢x ≤1 =
  nb-;ʳ γ₂ γ₁ (const-count x (¬mx ∘ unr⇒mobile) ⊢fn)
    (pair-arg-¬before ⊢arg (impure-dom-⊗ ic ⊢fn) ¬mx ¬my y′≢x
      (shrinkʳ γ₂ γ₁ (const-count x (¬mx ∘ unr⇒mobile) ⊢fn) ≤1))
pair-hole-¬before {x = x} {y′ = y′} ic (T-AppRight {γ₁ = γ₁} {γ₂ = γ₂} _ _ ⊢fn ⊢arg) ¬mx ¬my y′≢x ≤1 =
  nb-;ˡ γ₁ γ₂ (const-count y′ (¬my ∘ unr⇒mobile) ⊢fn)
    (pair-arg-¬before ⊢arg (impure-dom-⊗ ic ⊢fn) ¬mx ¬my y′≢x
      (shrinkˡ γ₁ γ₂ (const-count x (¬mx ∘ unr⇒mobile) ⊢fn) ≤1))
pair-hole-¬before ic (T-Conv _ _ dd) ¬mx ¬my y′≢x ≤1 =
  pair-hole-¬before ic dd ¬mx ¬my y′≢x ≤1
pair-hole-¬before ic (T-Weaken γ≤ dd) ¬mx ¬my y′≢x ≤1 b =
  pair-hole-¬before ic dd ¬mx ¬my y′≢x
    (subst (_≤ 1) (sym (count-≼-eq (¬mx ∘ unr⇒mobile) γ≤)) ≤1)
    (before-mono-≼ ¬my ¬mx γ≤ b)

thread-pair-count :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {E : Frame* n} {c} {w : Tm n} {x : 𝔽 n} {T ϵ} →
  Γ ; γ ⊢ E [ K c ·¹ (w ⊗ (` x)) ]* ∶ T ∣ ϵ → ¬ Unr (Γ ﹫ x) → 1 ≤ count x γ
thread-pair-count {E = E} {c = c} {w = w} {x = x} ⊢plug ¬ux =
  plug-count E (K c ·¹ (w ⊗ (` x))) ⊢plug (λ ⊢h → pair-hole-count ⊢h ¬ux) ¬ux

thread-pair-¬before :
  ∀ {n} {Γ : Ctx n} {γ : Struct n} {E : Frame* n} {c} {w : Tm n} {x y′ : 𝔽 n} {T ϵ} →
  ImpureHandleConst c →
  Γ ; γ ⊢ E [ K c ·¹ (w ⊗ (` x)) ]* ∶ T ∣ ϵ →
  ¬ Mobile (Γ ﹫ x) → ¬ Mobile (Γ ﹫ y′) → y′ ≢ x →
  count x γ ≤ 1 → ¬ before y′ x γ
thread-pair-¬before {E = E} {c = c} {w = w} {x = x} {y′ = y′} ic ⊢plug ¬mx ¬my y′≢x ≤1 =
  plug-¬before E (K c ·¹ (w ⊗ (` x))) ⊢plug
    (impure-app-eff ic)
    (λ ⊢h → pair-hole-count ⊢h (¬mx ∘ unr⇒mobile))
    (λ ⊢h bnd → pair-hole-¬before ic ⊢h ¬mx ¬my y′≢x bnd)
    ¬mx ¬my ≤1
