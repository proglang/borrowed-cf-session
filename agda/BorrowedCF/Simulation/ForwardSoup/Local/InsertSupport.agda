-- | Phase 3 helper for the leaf rule `R-RSplit` (`ForwardSoup/PLAN.md`, §6.4,
--   option 1).
--
--   `RUS-RSplit` inserts a *new* sync boundary at flag position `k` of the
--   split endpoint `x`, so every φ-reference of `x` at slot `k` or above moves
--   up by one — in every thread of the configuration.  This module is the
--   mirror image of `Local/AcqSupport.agda`: it collects the facts about
--   `insertPhi` that the leaf needs.
--
--     * how `insertPhi` acts on a φ-reference of its own endpoint
--       (`insertPhi-hit`, `insertPhi-below`, `insertPhi-above`);
--     * how it re-indexes a binder environment (`Ub-insertPhi`,
--       `UBFrom-insertPhi`): inserting at a slot below the group turns
--       `UBFrom l` into `UBFrom (suc l)`, which is exactly the environment of
--       the reduct;
--     * that it commutes with the translation of an expression
--       (`insertPhi-T`), of a frame (`Tᶠ*-insertPhi-frames`,
--       `Tᶠ*-plug-insertPhi`) and of a whole process (`flatten-insertPhi`),
--       hence transports an image (`insertPhi-image`);
--     * that `Separated` — which is phrased with `consumePhi` — already
--       supplies the ambient obligations
--       (`consumePhi-fixed⇒insertPhi-fixed`, `phiFree-insertPhi`).
module BorrowedCF.Simulation.ForwardSoup.Local.InsertSupport where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Reduction.Base as SourceReduction
import BorrowedCF.Reduction.ExpressionsSoup as SoupExpression
import BorrowedCF.Reduction.Processes.UntypedSoup as SoupReduction
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.Expressions
  using (ValueEnv; Tᶠ[_]; Tᶠ*[_]; T[_]-Env-cong)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Separation
  using ( PhiFreeFor; UB-phiFree-init; endpoint-channel-injective
        ; liftRen-injective; lookup-take-cases; lookup-drop-cases
        )
open import BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport
  using (UBFrom-flags-cong; flatten-channels-env)

open Nat.Variables
open Fin.Patterns

private
  variable
    A : Set
    d p q : ℕ

------------------------------------------------------------------------
-- Reading off a `Data.Sum` dispatch.

private
  sum-map :
    {X Y : Set} (f : X → Y)
    (g₁ : 𝔽 p → X) (g₂ : 𝔽 q → X) (h₁ : 𝔽 p → Y) (h₂ : 𝔽 q → Y) →
    ((y : 𝔽 p) → f (g₁ y) ≡ h₁ y) →
    ((y : 𝔽 q) → f (g₂ y) ≡ h₂ y) →
    (s : 𝔽 p ⊎ 𝔽 q) → f ([ g₁ , g₂ ]′ s) ≡ [ h₁ , h₂ ]′ s
  sum-map f g₁ g₂ h₁ h₂ eq₁ eq₂ (inj₁ y) = eq₁ y
  sum-map f g₁ g₂ h₁ h₂ eq₁ eq₂ (inj₂ y) = eq₂ y

  lookup-++-cases₂ :
    (xs xs′ : Vec A p) (ys ys′ : Vec A q) (R : A → A → Set) →
    ((i : 𝔽 p) → R (lookup xs i) (lookup xs′ i)) →
    ((i : 𝔽 q) → R (lookup ys i) (lookup ys′ i)) →
    (j : 𝔽 (p + q)) → R (lookup (xs V.++ ys) j) (lookup (xs′ V.++ ys′) j)
  lookup-++-cases₂ [] [] ys ys′ R leftEq rightEq j = rightEq j
  lookup-++-cases₂ (x ∷ xs) (x′ ∷ xs′) ys ys′ R leftEq rightEq zero =
    leftEq zero
  lookup-++-cases₂ (x ∷ xs) (x′ ∷ xs′) ys ys′ R leftEq rightEq (suc j) =
    lookup-++-cases₂ xs xs′ ys ys′ R (λ i → leftEq (suc i)) rightEq j

------------------------------------------------------------------------
-- The slot arithmetic.

insertSlot-below :
  (k l : ℕ) → l Nat.< k → SoupReduction.insertSlot k l ≡ l
insertSlot-below zero l ()
insertSlot-below (suc k) zero below = refl
insertSlot-below (suc k) (suc l) (Nat.s≤s below) =
  cong suc (insertSlot-below k l below)

insertSlot-above :
  (k l : ℕ) → k Nat.≤ l → SoupReduction.insertSlot k l ≡ suc l
insertSlot-above zero l above = refl
insertSlot-above (suc k) zero ()
insertSlot-above (suc k) (suc l) (Nat.s≤s above) =
  cong suc (insertSlot-above k l above)

------------------------------------------------------------------------
-- `insertPhi` at its own endpoint.

insertPhi-hit :
  (x : 𝔽 d) (k l : ℕ) →
  SoupReduction.insertPhi x k (SoupTerm.`phi (x , l)) ≡
  SoupTerm.`phi (x , SoupReduction.insertSlot k l)
insertPhi-hit x k l with x FinP.≟ x
... | yes refl = refl
... | no apart = ⊥-elim (apart refl)

insertPhi-below :
  (x : 𝔽 d) (k l : ℕ) → l Nat.< k →
  SoupReduction.insertPhi x k (SoupTerm.`phi (x , l)) ≡
  SoupTerm.`phi (x , l)
insertPhi-below x k l below =
  insertPhi-hit x k l
  ■ cong (λ z → SoupTerm.`phi (x , z)) (insertSlot-below k l below)

insertPhi-above :
  (x : 𝔽 d) (k l : ℕ) → k Nat.≤ l →
  SoupReduction.insertPhi x k (SoupTerm.`phi (x , l)) ≡
  SoupTerm.`phi (x , suc l)
insertPhi-above x k l above =
  insertPhi-hit x k l
  ■ cong (λ z → SoupTerm.`phi (x , z)) (insertSlot-above k l above)

------------------------------------------------------------------------
-- `insertPhi` commutes with injective renamings and with the expression
-- translation.

insertPhi-ren :
  {ρ : 𝔽 p → 𝔽 q} →
  (∀ {x y} → ρ x ≡ ρ y → x ≡ y) →
  (x : 𝔽 p) (k : ℕ) (t : SoupTerm.Tm p) →
  SoupReduction.insertPhi (ρ x) k (t SoupTerm.⋯ᵣ ρ) ≡
  SoupReduction.insertPhi x k t SoupTerm.⋯ᵣ ρ
insertPhi-ren inj x k (SoupTerm.` y) = refl
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.`phi (y , l))
  with x FinP.≟ y | ρ x FinP.≟ ρ y
... | no apart | no apart′ = refl
... | no apart | yes same′ = ⊥-elim (apart (inj same′))
... | yes refl | no apart′ = ⊥-elim (apart′ refl)
... | yes refl | yes refl = refl
insertPhi-ren inj x k (SoupTerm.K c) = refl
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.ƛ t) =
  cong SoupTerm.ƛ
    (insertPhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj)
      (suc x) k t)
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.μ t) =
  cong SoupTerm.μ
    (insertPhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj)
      (suc x) k t)
insertPhi-ren inj x k (t₁ SoupTerm.·⟨ dir ⟩ t₂) =
  cong₂ (SoupTerm._·⟨ dir ⟩_)
    (insertPhi-ren inj x k t₁) (insertPhi-ren inj x k t₂)
insertPhi-ren inj x k (t₁ SoupTerm.; t₂) =
  cong₂ SoupTerm._;_
    (insertPhi-ren inj x k t₁) (insertPhi-ren inj x k t₂)
insertPhi-ren inj x k (t₁ SoupTerm.⊗ t₂) =
  cong₂ SoupTerm._⊗_
    (insertPhi-ren inj x k t₁) (insertPhi-ren inj x k t₂)
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.`let t₁ `in t₂) =
  cong₂ SoupTerm.`let_`in_
    (insertPhi-ren inj x k t₁)
    (insertPhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj)
      (suc x) k t₂)
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.`let⊗ t₁ `in t₂) =
  cong₂ SoupTerm.`let⊗_`in_
    (insertPhi-ren inj x k t₁)
    (insertPhi-ren {ρ = SoupTerm.liftRen (SoupTerm.liftRen ρ)}
      (liftRen-injective (liftRen-injective inj)) (suc (suc x)) k t₂)
insertPhi-ren inj x k (SoupTerm.`inj i t) =
  cong (SoupTerm.`inj i) (insertPhi-ren inj x k t)
insertPhi-ren {ρ = ρ} inj x k (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) =
  cong₂ (λ u us → SoupTerm.`case u `of⟨ proj₁ us ; proj₂ us ⟩)
    (insertPhi-ren inj x k t)
    (cong₂ _,_
      (insertPhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj)
        (suc x) k t₁)
      (insertPhi-ren {ρ = SoupTerm.liftRen ρ} (liftRen-injective inj)
        (suc x) k t₂))

insertPhi-wk :
  (x : 𝔽 p) (k : ℕ) (t : SoupTerm.Tm p) →
  SoupReduction.insertPhi (suc x) k (SoupTerm.wk t) ≡
  SoupTerm.wk (SoupReduction.insertPhi x k t)
insertPhi-wk = insertPhi-ren {ρ = Fin.suc} Fin.suc-injective

insertPhi-liftEnv :
  (x : 𝔽 q) (k : ℕ) (sigma : Translation.Env p q) →
  ∀ y →
  SoupReduction.insertPhi (suc x) k (Translation.liftEnv sigma y) ≡
  Translation.liftEnv (λ z → SoupReduction.insertPhi x k (sigma z)) y
insertPhi-liftEnv x k sigma zero = refl
insertPhi-liftEnv x k sigma (suc y) = insertPhi-wk x k (sigma y)

insertPhi-liftEnv₂ :
  (x : 𝔽 q) (k : ℕ) (sigma : Translation.Env p q) →
  ∀ y →
  SoupReduction.insertPhi (suc (suc x)) k
    (Translation.liftEnv (Translation.liftEnv sigma) y) ≡
  Translation.liftEnv
    (Translation.liftEnv (λ z → SoupReduction.insertPhi x k (sigma z))) y
insertPhi-liftEnv₂ x k sigma zero = refl
insertPhi-liftEnv₂ x k sigma (suc y) =
  insertPhi-wk (suc x) k (Translation.liftEnv sigma y)
  ■ cong SoupTerm.wk (insertPhi-liftEnv x k sigma y)

insertPhi-T :
  (x : 𝔽 q) (k : ℕ) (e : Source.Tm p) (sigma : Translation.Env p q) →
  SoupReduction.insertPhi x k (Translation.T[ e ] sigma) ≡
  Translation.T[ e ] (λ y → SoupReduction.insertPhi x k (sigma y))
insertPhi-T x k (Source.` y) sigma = refl
insertPhi-T x k (Source.K c) sigma = refl
insertPhi-T x k (Source.ƛ e) sigma =
  cong SoupTerm.ƛ
    ( insertPhi-T (suc x) k e (Translation.liftEnv sigma)
    ■ T[ e ]-Env-cong (insertPhi-liftEnv x k sigma)
    )
insertPhi-T x k (Source.μ e) sigma =
  cong SoupTerm.μ
    ( insertPhi-T (suc x) k e (Translation.liftEnv sigma)
    ■ T[ e ]-Env-cong (insertPhi-liftEnv x k sigma)
    )
insertPhi-T x k (e₁ Source.·⟨ dir ⟩ e₂) sigma =
  cong₂ (SoupTerm._·⟨ dir ⟩_)
    (insertPhi-T x k e₁ sigma) (insertPhi-T x k e₂ sigma)
insertPhi-T x k (e₁ Source.; e₂) sigma =
  cong₂ SoupTerm._;_
    (insertPhi-T x k e₁ sigma) (insertPhi-T x k e₂ sigma)
insertPhi-T x k (e₁ Source.⊗ e₂) sigma =
  cong₂ SoupTerm._⊗_
    (insertPhi-T x k e₁ sigma) (insertPhi-T x k e₂ sigma)
insertPhi-T x k (Source.`let e₁ `in e₂) sigma =
  cong₂ SoupTerm.`let_`in_
    (insertPhi-T x k e₁ sigma)
    ( insertPhi-T (suc x) k e₂ (Translation.liftEnv sigma)
    ■ T[ e₂ ]-Env-cong (insertPhi-liftEnv x k sigma)
    )
insertPhi-T x k (Source.`let⊗ e₁ `in e₂) sigma =
  cong₂ SoupTerm.`let⊗_`in_
    (insertPhi-T x k e₁ sigma)
    ( insertPhi-T (suc (suc x)) k e₂
        (Translation.liftEnv (Translation.liftEnv sigma))
    ■ T[ e₂ ]-Env-cong (insertPhi-liftEnv₂ x k sigma)
    )
insertPhi-T x k (Source.`inj i e) sigma =
  cong (SoupTerm.`inj i) (insertPhi-T x k e sigma)
insertPhi-T x k (Source.`case e `of⟨ e₁ ; e₂ ⟩) sigma =
  cong₂ (λ u us → SoupTerm.`case u `of⟨ proj₁ us ; proj₂ us ⟩)
    (insertPhi-T x k e sigma)
    (cong₂ _,_
      ( insertPhi-T (suc x) k e₁ (Translation.liftEnv sigma)
      ■ T[ e₁ ]-Env-cong (insertPhi-liftEnv x k sigma)
      )
      ( insertPhi-T (suc x) k e₂ (Translation.liftEnv sigma)
      ■ T[ e₂ ]-Env-cong (insertPhi-liftEnv x k sigma)
      ))

insertEnv :
  (x : 𝔽 d) (k : ℕ) → Translation.Env p d → Translation.Env p d
insertEnv x k sigma y = SoupReduction.insertPhi x k (sigma y)

insertEnv-Value :
  (x : 𝔽 d) (k : ℕ) {sigma : Translation.Env p d} →
  ValueEnv sigma → ValueEnv (insertEnv x k sigma)
insertEnv-Value x k Vsigma y = SoupReduction.insertPhi-Value x k (Vsigma y)

------------------------------------------------------------------------
-- `insertPhi` re-indexes a binder environment.

Ub-insertPhi :
  (b : ℕ) (x : 𝔽 d) (k : ℕ) (e₁ e₂ : SoupTerm.Tm d) (c : 𝔽 d)
  (y : 𝔽 b) →
  SoupReduction.insertPhi x k (Translation.Ub[ b ] (e₁ , c , e₂) y) ≡
  Translation.Ub[ b ]
    ( SoupReduction.insertPhi x k e₁
    , c
    , SoupReduction.insertPhi x k e₂
    ) y
Ub-insertPhi (suc zero) x k e₁ e₂ c zero = refl
Ub-insertPhi (suc (suc b)) x k e₁ e₂ c zero = refl
Ub-insertPhi (suc (suc b)) x k e₁ e₂ c (suc y) =
  Ub-insertPhi (suc b) x k SoupTerm.* e₂ c y

-- Inserting a boundary at a slot `k` that precedes the whole group shifts the
-- group's own boundaries up by one: the environment produced at offset `l`
-- becomes the one produced at offset `suc l`.
UBFrom-insertPhi :
  (k l : ℕ) → k Nat.≤ l →
  (B : Typed.BindGroup) (x c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
  (y : 𝔽 (sum B)) →
  SoupReduction.insertPhi x k
    (proj₁ (Translation.UBFrom l B x (e₁ , c , e₂)) y) ≡
  proj₁
    (Translation.UBFrom (suc l) B x
      ( SoupReduction.insertPhi x k e₁
      , c
      , SoupReduction.insertPhi x k e₂
      )) y
UBFrom-insertPhi k l above [] x c e₁ e₂ ()
UBFrom-insertPhi k l above (b ∷ []) x c e₁ e₂ y =
  Ub-insertPhi (b + 0) x k e₁ e₂ c y
UBFrom-insertPhi k l above (b ∷ b′ ∷ B) x c e₁ e₂ y =
  sum-map (SoupReduction.insertPhi x k)
    (Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (x , l)))
    (proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) x
             (SoupTerm.`phi (x , l) , c , e₂)))
    (Translation.Ub[ b ]
      ( SoupReduction.insertPhi x k e₁
      , c
      , SoupTerm.`phi (x , suc l)
      ))
    (proj₁ (Translation.UBFrom (suc (suc l)) (b′ ∷ B) x
             ( SoupTerm.`phi (x , suc l)
             , c
             , SoupReduction.insertPhi x k e₂
             )))
    -- head block: this group's own trailing boundary slips from `l` to `suc l`
    (λ z →
      Ub-insertPhi b x k e₁ (SoupTerm.`phi (x , l)) c z
      ■ cong
          (λ t →
            Translation.Ub[ b ]
              (SoupReduction.insertPhi x k e₁ , c , t) z)
          (insertPhi-above x k l above))
    -- tail block: the remaining groups, by induction
    (λ z →
      UBFrom-insertPhi k (suc l) (NatP.≤-trans above (NatP.n≤1+n l))
        (b′ ∷ B) x c (SoupTerm.`phi (x , l)) e₂ z
      ■ cong
          (λ t →
            proj₁ (Translation.UBFrom (suc (suc l)) (b′ ∷ B) x
                    (t , c , SoupReduction.insertPhi x k e₂)) z)
          (insertPhi-above x k l above))
    (Fin.splitAt b y)

-- The flag list of a binder group does not depend on the offset.
UBFrom-flags-insert :
  (k l : ℕ) (B : Typed.BindGroup) (x c : 𝔽 d)
  (e₁ e₂ : SoupTerm.Tm d) →
  proj₂ (Translation.UBFrom l B x (e₁ , c , e₂)) ≡
  proj₂
    (Translation.UBFrom (suc l) B x
      ( SoupReduction.insertPhi x k e₁
      , c
      , SoupReduction.insertPhi x k e₂
      ))
UBFrom-flags-insert k l B x c e₁ e₂ =
  UBFrom-flags-cong l (suc l) B x (e₁ , c , e₂) x
    ( SoupReduction.insertPhi x k e₁
    , c
    , SoupReduction.insertPhi x k e₂
    )

------------------------------------------------------------------------
-- `insertPhi` commutes with the translation of a frame.

++ₛ-insertPhi :
  (x : 𝔽 d) (k : ℕ)
  (sigma₁ sigma₁′ : Translation.Env p d)
  (sigma₂ sigma₂′ : Translation.Env q d) →
  ((y : 𝔽 p) → SoupReduction.insertPhi x k (sigma₁ y) ≡ sigma₁′ y) →
  ((y : 𝔽 q) → SoupReduction.insertPhi x k (sigma₂ y) ≡ sigma₂′ y) →
  (y : 𝔽 (p + q)) →
  SoupReduction.insertPhi x k ((sigma₁ Translation.++ₛ sigma₂) y) ≡
  (sigma₁′ Translation.++ₛ sigma₂′) y
++ₛ-insertPhi {p = p} x k sigma₁ sigma₁′ sigma₂ sigma₂′ leftEq rightEq y
  with Fin.splitAt p y
... | inj₁ z = leftEq z
... | inj₂ z = rightEq z

Tᶠ-insertPhi-frame :
  {a : ℕ} (F₀ : SourceReduction.Frame a)
  {sigma : Translation.Env a d} (Vsigma : ValueEnv sigma)
  (x : 𝔽 d) (k : ℕ)
  (Vinserted : ValueEnv (insertEnv x k sigma)) (t : SoupTerm.Tm d) →
  SoupExpression._[_]
    (SoupReduction.insertPhi-frame x k (Tᶠ[ F₀ ] {σ = sigma} Vsigma)) t ≡
  SoupExpression._[_]
    (Tᶠ[ F₀ ] {σ = insertEnv x k sigma} Vinserted) t
Tᶠ-insertPhi-frame (SourceReduction.app₁ e dir V?) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → t SoupTerm.·⟨ dir ⟩ z) (insertPhi-T x k e sigma)
Tᶠ-insertPhi-frame (SourceReduction.app₂ e dir V?) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → z SoupTerm.·⟨ dir ⟩ t) (insertPhi-T x k e sigma)
Tᶠ-insertPhi-frame (SourceReduction.□⊗ e) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → t SoupTerm.⊗ z) (insertPhi-T x k e sigma)
Tᶠ-insertPhi-frame (V SourceReduction.⊗□) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → z SoupTerm.⊗ t)
    (insertPhi-T x k (SourceReduction.vTm V) sigma)
Tᶠ-insertPhi-frame (SourceReduction.□; e) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → t SoupTerm.; z) (insertPhi-T x k e sigma)
Tᶠ-insertPhi-frame (SourceReduction.`let-`in e) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → SoupTerm.`let t `in z)
    ( insertPhi-T (suc x) k e (Translation.liftEnv sigma)
    ■ T[ e ]-Env-cong (insertPhi-liftEnv x k sigma)
    )
Tᶠ-insertPhi-frame (SourceReduction.`let⊗-`in e) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong (λ z → SoupTerm.`let⊗ t `in z)
    ( insertPhi-T (suc (suc x)) k e
        (Translation.liftEnv (Translation.liftEnv sigma))
    ■ T[ e ]-Env-cong (insertPhi-liftEnv₂ x k sigma)
    )
Tᶠ-insertPhi-frame (SourceReduction.`inj□ i) Vsigma x k Vinserted t = refl
Tᶠ-insertPhi-frame (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) {sigma = sigma}
  Vsigma x k Vinserted t =
  cong₂ (λ z₁ z₂ → SoupTerm.`case t `of⟨ z₁ ; z₂ ⟩)
    ( insertPhi-T (suc x) k e₁ (Translation.liftEnv sigma)
    ■ T[ e₁ ]-Env-cong (insertPhi-liftEnv x k sigma)
    )
    ( insertPhi-T (suc x) k e₂ (Translation.liftEnv sigma)
    ■ T[ e₂ ]-Env-cong (insertPhi-liftEnv x k sigma)
    )

-- Mapping `insertPhi` over the *frames* of a translated evaluation context is
-- the translation of the same context under the inserted environment.  This is
-- what relates the new `RUS-RSplit`'s `insertPhi-frames x k F [ … ]*` to the
-- translation of the reduct's frames.
Tᶠ*-insertPhi-frames :
  {a : ℕ} (E : SourceReduction.Frame* a)
  {sigma : Translation.Env a d} (Vsigma : ValueEnv sigma)
  (x : 𝔽 d) (k : ℕ)
  (Vinserted : ValueEnv (insertEnv x k sigma)) (t : SoupTerm.Tm d) →
  SoupExpression._[_]*
    (SoupReduction.insertPhi-frames x k (Tᶠ*[ E ] {σ = sigma} Vsigma)) t ≡
  SoupExpression._[_]*
    (Tᶠ*[ E ] {σ = insertEnv x k sigma} Vinserted) t
Tᶠ*-insertPhi-frames [] Vsigma x k Vinserted t = refl
Tᶠ*-insertPhi-frames (F₀ ∷ E) {sigma = sigma} Vsigma x k Vinserted t =
  cong
    (SoupExpression._[_]
      (SoupReduction.insertPhi-frame x k (Tᶠ[ F₀ ] {σ = sigma} Vsigma)))
    (Tᶠ*-insertPhi-frames E Vsigma x k Vinserted t)
  ■ Tᶠ-insertPhi-frame F₀ Vsigma x k Vinserted
      (SoupExpression._[_]*
        (Tᶠ*[ E ] {σ = insertEnv x k sigma} Vinserted) t)

Tᶠ*-plug-insertPhi :
  {a : ℕ} (E : SourceReduction.Frame* a)
  {sigma : Translation.Env a d} (Vsigma : ValueEnv sigma)
  (x : 𝔽 d) (k : ℕ)
  (Vinserted : ValueEnv (insertEnv x k sigma)) (t : SoupTerm.Tm d) →
  SoupReduction.insertPhi x k
    (SoupExpression._[_]* (Tᶠ*[ E ] {σ = sigma} Vsigma) t) ≡
  SoupExpression._[_]*
    (Tᶠ*[ E ] {σ = insertEnv x k sigma} Vinserted)
    (SoupReduction.insertPhi x k t)
Tᶠ*-plug-insertPhi E {sigma = sigma} Vsigma x k Vinserted t =
  SoupReduction.insertPhi-plug* x k (Tᶠ*[ E ] {σ = sigma} Vsigma) t
  ■ Tᶠ*-insertPhi-frames E Vsigma x k Vinserted
      (SoupReduction.insertPhi x k t)

------------------------------------------------------------------------
-- `Separated` is stated with `consumePhi`; it also rules out `insertPhi`.

private
  n≢suc : (l : ℕ) → l ≢ suc l
  n≢suc zero ()
  n≢suc (suc l) equal = n≢suc l (suc⁻¹ equal)

  ★≢phi : {r : SoupTerm.PhiRef d} → SoupTerm.* ≢ SoupTerm.`phi r
  ★≢phi ()

  phi-inj :
    {r r′ : SoupTerm.PhiRef d} →
    SoupTerm.`phi r ≡ SoupTerm.`phi r′ → r ≡ r′
  phi-inj refl = refl

  ƛ-inj :
    {t u : SoupTerm.Tm (suc d)} → SoupTerm.ƛ t ≡ SoupTerm.ƛ u → t ≡ u
  ƛ-inj refl = refl

  μ-inj :
    {t u : SoupTerm.Tm (suc d)} → SoupTerm.μ t ≡ SoupTerm.μ u → t ≡ u
  μ-inj refl = refl

  ·-inj :
    ∀ {dir} {t₁ u₁ t₂ u₂ : SoupTerm.Tm d} →
    (t₁ SoupTerm.·⟨ dir ⟩ t₂) ≡ (u₁ SoupTerm.·⟨ dir ⟩ u₂) →
    t₁ ≡ u₁ × t₂ ≡ u₂
  ·-inj refl = refl , refl

  seq-inj :
    {t₁ u₁ t₂ u₂ : SoupTerm.Tm d} →
    (t₁ SoupTerm.; t₂) ≡ (u₁ SoupTerm.; u₂) → t₁ ≡ u₁ × t₂ ≡ u₂
  seq-inj refl = refl , refl

  ⊗-inj :
    {t₁ u₁ t₂ u₂ : SoupTerm.Tm d} →
    (t₁ SoupTerm.⊗ t₂) ≡ (u₁ SoupTerm.⊗ u₂) → t₁ ≡ u₁ × t₂ ≡ u₂
  ⊗-inj refl = refl , refl

  let-inj :
    {t₁ u₁ : SoupTerm.Tm d} {t₂ u₂ : SoupTerm.Tm (suc d)} →
    (SoupTerm.`let t₁ `in t₂) ≡ (SoupTerm.`let u₁ `in u₂) →
    t₁ ≡ u₁ × t₂ ≡ u₂
  let-inj refl = refl , refl

  let⊗-inj :
    {t₁ u₁ : SoupTerm.Tm d} {t₂ u₂ : SoupTerm.Tm (suc (suc d))} →
    (SoupTerm.`let⊗ t₁ `in t₂) ≡ (SoupTerm.`let⊗ u₁ `in u₂) →
    t₁ ≡ u₁ × t₂ ≡ u₂
  let⊗-inj refl = refl , refl

  inj-inj :
    ∀ {i} {t u : SoupTerm.Tm d} →
    SoupTerm.`inj i t ≡ SoupTerm.`inj i u → t ≡ u
  inj-inj refl = refl

  case-inj :
    {t u : SoupTerm.Tm d} {t₁ u₁ t₂ u₂ : SoupTerm.Tm (suc d)} →
    (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) ≡
    (SoupTerm.`case u `of⟨ u₁ ; u₂ ⟩) →
    t ≡ u × t₁ ≡ u₁ × t₂ ≡ u₂
  case-inj refl = refl , refl , refl

-- A term that every `consumePhi` on `x` leaves alone carries no φ-cell of
-- `x`, hence `insertPhi` leaves it alone as well.
consumePhi-fixed⇒insertPhi-fixed :
  (x : 𝔽 d) (t : SoupTerm.Tm d) →
  ((l : ℕ) → SoupReduction.consumePhi x l t ≡ t) →
  (k : ℕ) → SoupReduction.insertPhi x k t ≡ t
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.` y) fixed k = refl
-- Consuming cell `0` of `x` either erases the reference (slot `0`) or
-- decrements it (slot `suc _`); either way it moves it, so the hypothesis at
-- `l = 0` is contradictory as soon as the reference sits on `x`.
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.`phi (y , zero)) fixed k
  with x FinP.≟ y
... | no apart = refl
... | yes refl = ⊥-elim (★≢phi (fixed 0))
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.`phi (y , suc slot)) fixed k
  with x FinP.≟ y
... | no apart = refl
... | yes refl = ⊥-elim (n≢suc slot (cong proj₂ (phi-inj (fixed 0))))
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.K c) fixed k = refl
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.ƛ t) fixed k =
  cong SoupTerm.ƛ
    (consumePhi-fixed⇒insertPhi-fixed (suc x) t (λ l → ƛ-inj (fixed l)) k)
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.μ t) fixed k =
  cong SoupTerm.μ
    (consumePhi-fixed⇒insertPhi-fixed (suc x) t (λ l → μ-inj (fixed l)) k)
consumePhi-fixed⇒insertPhi-fixed x (t₁ SoupTerm.·⟨ dir ⟩ t₂) fixed k =
  cong₂ (SoupTerm._·⟨ dir ⟩_)
    (consumePhi-fixed⇒insertPhi-fixed x t₁
      (λ l → proj₁ (·-inj (fixed l))) k)
    (consumePhi-fixed⇒insertPhi-fixed x t₂
      (λ l → proj₂ (·-inj (fixed l))) k)
consumePhi-fixed⇒insertPhi-fixed x (t₁ SoupTerm.; t₂) fixed k =
  cong₂ SoupTerm._;_
    (consumePhi-fixed⇒insertPhi-fixed x t₁
      (λ l → proj₁ (seq-inj (fixed l))) k)
    (consumePhi-fixed⇒insertPhi-fixed x t₂
      (λ l → proj₂ (seq-inj (fixed l))) k)
consumePhi-fixed⇒insertPhi-fixed x (t₁ SoupTerm.⊗ t₂) fixed k =
  cong₂ SoupTerm._⊗_
    (consumePhi-fixed⇒insertPhi-fixed x t₁
      (λ l → proj₁ (⊗-inj (fixed l))) k)
    (consumePhi-fixed⇒insertPhi-fixed x t₂
      (λ l → proj₂ (⊗-inj (fixed l))) k)
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.`let t₁ `in t₂) fixed k =
  cong₂ SoupTerm.`let_`in_
    (consumePhi-fixed⇒insertPhi-fixed x t₁
      (λ l → proj₁ (let-inj (fixed l))) k)
    (consumePhi-fixed⇒insertPhi-fixed (suc x) t₂
      (λ l → proj₂ (let-inj (fixed l))) k)
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.`let⊗ t₁ `in t₂) fixed k =
  cong₂ SoupTerm.`let⊗_`in_
    (consumePhi-fixed⇒insertPhi-fixed x t₁
      (λ l → proj₁ (let⊗-inj (fixed l))) k)
    (consumePhi-fixed⇒insertPhi-fixed (suc (suc x)) t₂
      (λ l → proj₂ (let⊗-inj (fixed l))) k)
consumePhi-fixed⇒insertPhi-fixed x (SoupTerm.`inj i t) fixed k =
  cong (SoupTerm.`inj i)
    (consumePhi-fixed⇒insertPhi-fixed x t (λ l → inj-inj (fixed l)) k)
consumePhi-fixed⇒insertPhi-fixed x
  (SoupTerm.`case t `of⟨ t₁ ; t₂ ⟩) fixed k =
  cong₂ (λ u us → SoupTerm.`case u `of⟨ proj₁ us ; proj₂ us ⟩)
    (consumePhi-fixed⇒insertPhi-fixed x t
      (λ l → proj₁ (case-inj (fixed l))) k)
    (cong₂ _,_
      (consumePhi-fixed⇒insertPhi-fixed (suc x) t₁
        (λ l → proj₁ (proj₂ (case-inj (fixed l)))) k)
      (consumePhi-fixed⇒insertPhi-fixed (suc x) t₂
        (λ l → proj₂ (proj₂ (case-inj (fixed l)))) k))

phiFree-insertPhi :
  {n : ℕ} {ambientChannel : 𝔽 n → Set} {t : SoupTerm.Tm (2 *ℕ n)} →
  PhiFreeFor ambientChannel t →
  (i : 𝔽 n) (side : 𝔽 2) (k : ℕ) → ¬ ambientChannel i →
  SoupReduction.insertPhi (Soup.endpoint i side) k t ≡ t
phiFree-insertPhi {t = t} free i side k notAmbient =
  consumePhi-fixed⇒insertPhi-fixed (Soup.endpoint i side) t
    (λ l → free i side l notAmbient) k

------------------------------------------------------------------------
-- `insertPhi` commutes with the translation of a whole process.

flatten-insertPhi :
  {k n : ℕ} (P : Typed.Proc k)
  (lc : Vec (OrientedChannel n) (Translation.channelCount P))
  (sigma sigma′ : Translation.Env k (2 *ℕ n))
  (c : 𝔽 n) (s : 𝔽 2) (l : ℕ) →
  ((i : 𝔽 (Translation.channelCount P)) →
    physicalChannel (lookup lc i) ≢ c) →
  ((y : 𝔽 k) →
    SoupReduction.insertPhi (Soup.endpoint c s) l (sigma y) ≡ sigma′ y) →
  (j : 𝔽 (Translation.processCount P)) →
  SoupReduction.insertPhi (Soup.endpoint c s) l
    (lookup (proj₂ (flattenOriented P lc sigma)) j) ≡
  lookup (proj₂ (flattenOriented P lc sigma′)) j
flatten-insertPhi (Typed.⟪ e ⟫) [] sigma sigma′ c s l chanApart envEq zero =
  insertPhi-T (Soup.endpoint c s) l e sigma ■ T[ e ]-Env-cong envEq
flatten-insertPhi (P Typed.∥ Q) lc sigma sigma′ c s l chanApart envEq =
  lookup-++-cases₂
    (proj₂ (flattenOriented P (V.take (Translation.channelCount P) lc) sigma))
    (proj₂ (flattenOriented P (V.take (Translation.channelCount P) lc) sigma′))
    (proj₂ (flattenOriented Q (V.drop (Translation.channelCount P) lc) sigma))
    (proj₂ (flattenOriented Q (V.drop (Translation.channelCount P) lc) sigma′))
    (λ t t′ → SoupReduction.insertPhi (Soup.endpoint c s) l t ≡ t′)
    (flatten-insertPhi P (V.take (Translation.channelCount P) lc)
      sigma sigma′ c s l
      (lookup-take-cases (Translation.channelCount P) lc
        (λ ch → physicalChannel ch ≢ c) chanApart)
      envEq)
    (flatten-insertPhi Q (V.drop (Translation.channelCount P) lc)
      sigma sigma′ c s l
      (lookup-drop-cases (Translation.channelCount P) lc
        (λ ch → physicalChannel ch ≢ c) chanApart)
      envEq)
flatten-insertPhi (Typed.ν B₁ B₂ P) (ch ∷ lc) sigma sigma′ c s l
  chanApart envEq =
  flatten-insertPhi P lc
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma′)
    c s l
    (λ i → chanApart (suc i))
    (++ₛ-insertPhi (Soup.endpoint c s) l
      (sigma₁ Translation.++ₛ sigma₂) (sigma₁ Translation.++ₛ sigma₂)
      sigma sigma′
      (++ₛ-insertPhi (Soup.endpoint c s) l sigma₁ sigma₁ sigma₂ sigma₂
        sigma₁-fixed sigma₂-fixed)
      envEq)
  where
  r₁ = physicalEndpoint ch 0F
  r₂ = physicalEndpoint ch 1F

  sigma₁ = proj₁ (Translation.UB[ B₁ ] r₁ (SoupTerm.* , r₁ , SoupTerm.*))
  sigma₂ = proj₁ (Translation.UB[ B₂ ] r₂ (SoupTerm.* , r₂ , SoupTerm.*))

  apart : (side : 𝔽 2) → Soup.endpoint c s ≢ physicalEndpoint ch side
  apart side equal =
    chanApart 0F (sym (endpoint-channel-injective equal))

  sigma₁-fixed :
    (y : 𝔽 (sum B₁)) →
    SoupReduction.insertPhi (Soup.endpoint c s) l (sigma₁ y) ≡ sigma₁ y
  sigma₁-fixed y =
    consumePhi-fixed⇒insertPhi-fixed (Soup.endpoint c s) (sigma₁ y)
      (λ l₀ → UB-phiFree-init B₁ (Soup.endpoint c s) r₁ l₀ (apart 0F) y) l

  sigma₂-fixed :
    (y : 𝔽 (sum B₂)) →
    SoupReduction.insertPhi (Soup.endpoint c s) l (sigma₂ y) ≡ sigma₂ y
  sigma₂-fixed y =
    consumePhi-fixed⇒insertPhi-fixed (Soup.endpoint c s) (sigma₂ y)
      (λ l₀ → UB-phiFree-init B₂ (Soup.endpoint c s) r₂ l₀ (apart 1F) y) l

------------------------------------------------------------------------
-- Transporting an image across `RUS-RSplit`'s global rewrite.

insertPhi-image :
  {k n m : ℕ} {P : Typed.Proc k}
  {lc : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma sigma′ : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {channels channels′ : Vec Soup.Channel n}
  {threads : Vec (Soup.Thread n) m}
  (c : 𝔽 n) (s : 𝔽 2) (l : ℕ) →
  ((y : 𝔽 k) →
    SoupReduction.insertPhi (Soup.endpoint c s) l (sigma y) ≡ sigma′ y) →
  ((i : 𝔽 (Translation.channelCount P)) →
    physicalChannel (lookup lc i) ≢ c) →
  ((i : 𝔽 n) → ¬ ambientChannel i → lookup channels′ i ≡ lookup channels i) →
  LocalImage P lc sigma ambientChannel ambientThread
    (Soup.config channels threads) →
  LocalImage P lc sigma′ ambientChannel ambientThread
    (Soup.config channels′
      (V.map (SoupReduction.insertPhi (Soup.endpoint c s) l) threads))
insertPhi-image {P = P} {lc = lc} {sigma = sigma} {sigma′ = sigma′}
  {channels = channels} {channels′ = channels′} {threads = threads}
  c s l envEq chanApart channelContent image = record
  { channelEmbedding-injective = channelEmbedding-injective image
  ; threadEmbedding = threadEmbedding image
  ; threadEmbedding-injective = threadEmbedding-injective image
  ; channel-not-ambient = channel-not-ambient image
  ; thread-not-ambient = thread-not-ambient image
  ; live-channel = λ i →
      channelContent (physicalChannel (lookup lc i))
        (channel-not-ambient image i)
      ■ live-channel image i
      ■ cong (λ cs → lookup cs i)
          (flatten-channels-env P lc sigma sigma′)
  ; live-thread = λ j → targetThread j (live-thread image j)
  ; garbage-channel = λ i outside notAmbient →
      channelContent i notAmbient
      ■ garbage-channel image i outside notAmbient
  ; garbage-thread = λ j outside notAmbient →
      V.lookup-map j
        (SoupReduction.insertPhi (Soup.endpoint c s) l) threads
      ■ cong (SoupReduction.insertPhi (Soup.endpoint c s) l)
          (garbage-thread image j outside notAmbient)
  }
  where
  threadEq :
    (j : 𝔽 (Translation.processCount P)) →
    SoupReduction.insertPhi (Soup.endpoint c s) l
      (lookup (proj₂ (flattenOriented P lc sigma)) j) ≡
    lookup (proj₂ (flattenOriented P lc sigma′)) j
  threadEq = flatten-insertPhi P lc sigma sigma′ c s l chanApart envEq

  targetThread :
    (j : 𝔽 (Translation.processCount P)) →
    OptionalThreadImage threads (threadEmbedding image j)
      (lookup (proj₂ (flattenOriented P lc sigma)) j) →
    OptionalThreadImage
      (V.map (SoupReduction.insertPhi (Soup.endpoint c s) l) threads)
      (threadEmbedding image j)
      (lookup (proj₂ (flattenOriented P lc sigma′)) j)
  targetThread j (present t slotEq lookupEq) =
    present t slotEq
      ( V.lookup-map t
          (SoupReduction.insertPhi (Soup.endpoint c s) l) threads
      ■ cong (SoupReduction.insertPhi (Soup.endpoint c s) l) lookupEq
      ■ threadEq j
      )
  targetThread j (omitted slotEq expectedEq) =
    omitted slotEq
      ( sym (threadEq j)
      ■ cong (SoupReduction.insertPhi (Soup.endpoint c s) l) expectedEq
      )
