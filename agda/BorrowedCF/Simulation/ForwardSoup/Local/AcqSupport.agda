-- | Phase 3 helper for the leaf rule `R-Acq` (`ForwardSoup/PLAN.md`, §4,
--   Phase 3, item 7 and §4.5).
--
--   `RUS-Acquire` is the only soup rule that rewrites *every* thread of the
--   configuration: it deletes the φ-cell `k` of the acquired endpoint `x` and
--   maps `consumePhi x k` over the whole soup.  This module collects the
--   facts about `consumePhi` that the leaf needs:
--
--     * how it acts on a φ-reference of its own endpoint (`consumePhi-hit`,
--       `consumePhi-succ`) — the two clauses of `shiftSlot` at slot `0`;
--     * how it re-indexes a binder environment (`Ub-consumePhi`,
--       `UBFrom-consumePhi`): consuming cell `0` turns `UBFrom (suc l)` into
--       `UBFrom l`, which is exactly the environment of the reduct;
--     * that it commutes with the translation of a frame
--       (`Tᶠ*-plug-consumePhi`) and of a whole process
--       (`flatten-consumePhi`), hence transports an image
--       (`consumePhi-image`);
--     * the two side conditions: flag lists do not depend on the `UBFrom`
--       offset (`UBFrom-flags-cong`) and the two endpoints of one channel are
--       distinct (`endpoint-side-injective`, `orientSide-distinct`).
module BorrowedCF.Simulation.ForwardSoup.Local.AcqSupport where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing)

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
  using ( consumePhi-T; consumePhi-liftEnv; consumePhi-liftEnv₂
        ; UB-phiFree-init; endpoint-channel-injective
        ; lookup-take-cases; lookup-drop-cases
        )
open import BorrowedCF.Simulation.ForwardSoup.Local.New using (remQuot-endpoint)

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

------------------------------------------------------------------------
-- `consumePhi` at its own endpoint.

consumePhi-hit :
  (x : 𝔽 d) →
  SoupReduction.consumePhi x 0 (SoupTerm.`phi (x , 0)) ≡ SoupTerm.*
consumePhi-hit x with x FinP.≟ x
... | yes refl = refl
... | no apart = ⊥-elim (apart refl)

consumePhi-succ :
  (x : 𝔽 d) (l : ℕ) →
  SoupReduction.consumePhi x 0 (SoupTerm.`phi (x , suc l)) ≡
  SoupTerm.`phi (x , l)
consumePhi-succ x l with x FinP.≟ x
... | yes refl = refl
... | no apart = ⊥-elim (apart refl)

consumePhi-Value :
  (x : 𝔽 d) (k : ℕ) {t : SoupTerm.Tm d} →
  SoupExpression.Value t →
  SoupExpression.Value (SoupReduction.consumePhi x k t)
consumePhi-Value x k SoupExpression.V-` = SoupExpression.V-`
consumePhi-Value x k (SoupExpression.V-phi {r = y , l})
  with x FinP.≟ y
... | no _ = SoupExpression.V-phi
... | yes refl with k NatP.≟ l
...   | no _ = SoupExpression.V-phi
...   | yes refl = SoupExpression.V-K
consumePhi-Value x k SoupExpression.V-K = SoupExpression.V-K
consumePhi-Value x k SoupExpression.V-λ = SoupExpression.V-λ
consumePhi-Value x k (SoupExpression.V-⊗ V₁ V₂) =
  SoupExpression.V-⊗ (consumePhi-Value x k V₁) (consumePhi-Value x k V₂)
consumePhi-Value x k (SoupExpression.V-⊕ V) =
  SoupExpression.V-⊕ (consumePhi-Value x k V)

consumeEnv :
  (x : 𝔽 d) (k : ℕ) → Translation.Env p d → Translation.Env p d
consumeEnv x k sigma y = SoupReduction.consumePhi x k (sigma y)

consumeEnv-Value :
  (x : 𝔽 d) (k : ℕ) {sigma : Translation.Env p d} →
  ValueEnv sigma → ValueEnv (consumeEnv x k sigma)
consumeEnv-Value x k Vsigma y = consumePhi-Value x k (Vsigma y)

------------------------------------------------------------------------
-- `consumePhi` re-indexes a binder environment.

Ub-consumePhi :
  (b : ℕ) (x : 𝔽 d) (k : ℕ) (e₁ e₂ : SoupTerm.Tm d) (c : 𝔽 d)
  (y : 𝔽 b) →
  SoupReduction.consumePhi x k (Translation.Ub[ b ] (e₁ , c , e₂) y) ≡
  Translation.Ub[ b ]
    ( SoupReduction.consumePhi x k e₁
    , c
    , SoupReduction.consumePhi x k e₂
    ) y
Ub-consumePhi (suc zero) x k e₁ e₂ c zero = refl
Ub-consumePhi (suc (suc b)) x k e₁ e₂ c zero = refl
Ub-consumePhi (suc (suc b)) x k e₁ e₂ c (suc y) =
  Ub-consumePhi (suc b) x k SoupTerm.* e₂ c y

-- Consuming the *first* φ-cell of a group turns the environment produced at
-- offset `suc l` into the one produced at offset `l`.
UBFrom-consumePhi :
  (l : ℕ) (B : Typed.BindGroup) (x c : 𝔽 d) (e₁ e₂ : SoupTerm.Tm d)
  (y : 𝔽 (sum B)) →
  SoupReduction.consumePhi x 0
    (proj₁ (Translation.UBFrom (suc l) B x (e₁ , c , e₂)) y) ≡
  proj₁
    (Translation.UBFrom l B x
      ( SoupReduction.consumePhi x 0 e₁
      , c
      , SoupReduction.consumePhi x 0 e₂
      )) y
UBFrom-consumePhi l [] x c e₁ e₂ ()
UBFrom-consumePhi l (b ∷ []) x c e₁ e₂ y =
  Ub-consumePhi (b + 0) x 0 e₁ e₂ c y
UBFrom-consumePhi l (b ∷ b′ ∷ B) x c e₁ e₂ y =
  sum-map (SoupReduction.consumePhi x 0)
    (Translation.Ub[ b ] (e₁ , c , SoupTerm.`phi (x , suc l)))
    (proj₁ (Translation.UBFrom (suc (suc l)) (b′ ∷ B) x
             (SoupTerm.`phi (x , suc l) , c , e₂)))
    (Translation.Ub[ b ]
      (SoupReduction.consumePhi x 0 e₁ , c , SoupTerm.`phi (x , l)))
    (proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) x
             ( SoupTerm.`phi (x , l)
             , c
             , SoupReduction.consumePhi x 0 e₂
             )))
    -- head block: the borrow entries of this group, whose trailing φ-cell
    -- slips from `suc l` to `l`
    (λ z →
      Ub-consumePhi b x 0 e₁ (SoupTerm.`phi (x , suc l)) c z
      ■ cong
          (λ t →
            Translation.Ub[ b ]
              (SoupReduction.consumePhi x 0 e₁ , c , t) z)
          (consumePhi-succ x l))
    -- tail block: the remaining groups, by induction
    (λ z →
      UBFrom-consumePhi (suc l) (b′ ∷ B) x c
        (SoupTerm.`phi (x , suc l)) e₂ z
      ■ cong
          (λ t →
            proj₁ (Translation.UBFrom (suc l) (b′ ∷ B) x
                    (t , c , SoupReduction.consumePhi x 0 e₂)) z)
          (consumePhi-succ x l))
    (Fin.splitAt b y)

------------------------------------------------------------------------
-- The head of a binder group at an arbitrary offset.  (`UB-head` of
-- `ForwardSoup/Translation.agda` is the instance at offset `0`.)

UBFrom-head :
  (l b : ℕ) (B : Typed.BindGroup) (r c : 𝔽 d)
  (e₁ e₂ : SoupTerm.Tm d) →
  Σ[ e₂′ ∈ SoupTerm.Tm d ]
    proj₁ (Translation.UBFrom l (suc b ∷ B) r (e₁ , c , e₂)) 0F ≡
    Translation.chanTriple (e₁ , c , e₂′)
UBFrom-head l zero [] r c e₁ e₂ = e₂ , refl
UBFrom-head l (suc b) [] r c e₁ e₂ = SoupTerm.* , refl
UBFrom-head l zero (b′ ∷ B) r c e₁ e₂
  with Translation.UBFrom (suc l) (b′ ∷ B) r
         (SoupTerm.`phi (r , l) , c , e₂)
... | sigma , flags = SoupTerm.`phi (r , l) , refl
UBFrom-head l (suc b) (b′ ∷ B) r c e₁ e₂
  with Translation.UBFrom (suc l) (b′ ∷ B) r
         (SoupTerm.`phi (r , l) , c , e₂)
... | sigma , flags = SoupTerm.* , refl

------------------------------------------------------------------------
-- The flag list of a binder group depends on the group only.

UBFrom-flags-cong :
  (k₁ k₂ : ℕ) (B : Typed.BindGroup) {d₁ d₂ : ℕ}
  (r₁ : 𝔽 d₁) (c₁ : Translation.UChan d₁)
  (r₂ : 𝔽 d₂) (c₂ : Translation.UChan d₂) →
  proj₂ (Translation.UBFrom k₁ B r₁ c₁) ≡
  proj₂ (Translation.UBFrom k₂ B r₂ c₂)
UBFrom-flags-cong k₁ k₂ [] r₁ c₁ r₂ c₂ = refl
UBFrom-flags-cong k₁ k₂ (b ∷ []) r₁ c₁ r₂ c₂ = refl
UBFrom-flags-cong k₁ k₂ (b ∷ B@(b′ ∷ B′))
  r₁ (e₁ , c₁ , e₂) r₂ (e₁′ , c₂ , e₂′)
  with Translation.UBFrom (suc k₁) B r₁
         (SoupTerm.`phi (r₁ , k₁) , c₁ , e₂)
     | Translation.UBFrom (suc k₂) B r₂
         (SoupTerm.`phi (r₂ , k₂) , c₂ , e₂′)
     | UBFrom-flags-cong (suc k₁) (suc k₂) B r₁
         (SoupTerm.`phi (r₁ , k₁) , c₁ , e₂)
         r₂
         (SoupTerm.`phi (r₂ , k₂) , c₂ , e₂′)
... | sigma₁ , flags₁ | sigma₂ , flags₂ | equal =
  cong (Translation.ϕ[ b ] ∷_) equal

------------------------------------------------------------------------
-- The two endpoints of one channel are distinct.

endpoint-side-injective :
  {n : ℕ} (i : 𝔽 n) (s s′ : 𝔽 2) →
  Soup.endpoint i s ≡ Soup.endpoint i s′ → s ≡ s′
endpoint-side-injective {n = n} i s s′ equal =
  cong proj₂
    ( sym (remQuot-endpoint i s)
    ■ cong
        (λ z → Fin.remQuot {n} 2 (Fin.cast (Nat.*-comm 2 n) z)) equal
    ■ remQuot-endpoint i s′
    )

orientSide-distinct :
  (orientation : Orientation) →
  orientSide orientation 0F ≢ orientSide orientation 1F
orientSide-distinct forward ()
orientSide-distinct reverse ()

physicalEndpoint-distinct :
  {n : ℕ} (channel : OrientedChannel n) →
  physicalEndpoint channel 0F ≢ physicalEndpoint channel 1F
physicalEndpoint-distinct (i , orientation) equal =
  orientSide-distinct orientation
    (endpoint-side-injective i
      (orientSide orientation 0F) (orientSide orientation 1F) equal)

------------------------------------------------------------------------
-- `consumePhi` commutes with the translation of a frame.

Tᶠ-plug-consumePhi :
  {a : ℕ} (F₀ : SourceReduction.Frame a)
  {sigma : Translation.Env a d} (Vsigma : ValueEnv sigma)
  (x : 𝔽 d) (k : ℕ)
  (Vconsumed : ValueEnv (consumeEnv x k sigma)) (t : SoupTerm.Tm d) →
  SoupReduction.consumePhi x k
    (SoupExpression._[_] (Tᶠ[ F₀ ] {σ = sigma} Vsigma) t) ≡
  SoupExpression._[_]
    (Tᶠ[ F₀ ] {σ = consumeEnv x k sigma} Vconsumed)
    (SoupReduction.consumePhi x k t)
Tᶠ-plug-consumePhi (SourceReduction.app₁ e dir V?) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → SoupReduction.consumePhi x k t SoupTerm.·⟨ dir ⟩ z)
    (consumePhi-T x k e sigma)
Tᶠ-plug-consumePhi (SourceReduction.app₂ e dir V?) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → z SoupTerm.·⟨ dir ⟩ SoupReduction.consumePhi x k t)
    (consumePhi-T x k e sigma)
Tᶠ-plug-consumePhi (SourceReduction.□⊗ e) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → SoupReduction.consumePhi x k t SoupTerm.⊗ z)
    (consumePhi-T x k e sigma)
Tᶠ-plug-consumePhi (V SourceReduction.⊗□) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → z SoupTerm.⊗ SoupReduction.consumePhi x k t)
    (consumePhi-T x k (SourceReduction.vTm V) sigma)
Tᶠ-plug-consumePhi (SourceReduction.□; e) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → SoupReduction.consumePhi x k t SoupTerm.; z)
    (consumePhi-T x k e sigma)
Tᶠ-plug-consumePhi (SourceReduction.`let-`in e) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → SoupTerm.`let SoupReduction.consumePhi x k t `in z)
    ( consumePhi-T (suc x) k e (Translation.liftEnv sigma)
    ■ T[ e ]-Env-cong (consumePhi-liftEnv x k sigma)
    )
Tᶠ-plug-consumePhi (SourceReduction.`let⊗-`in e) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong (λ z → SoupTerm.`let⊗ SoupReduction.consumePhi x k t `in z)
    ( consumePhi-T (suc (suc x)) k e
        (Translation.liftEnv (Translation.liftEnv sigma))
    ■ T[ e ]-Env-cong (consumePhi-liftEnv₂ x k sigma)
    )
Tᶠ-plug-consumePhi (SourceReduction.`inj□ i) Vsigma x k Vconsumed t = refl
Tᶠ-plug-consumePhi (SourceReduction.`case□`of⟨ e₁ ; e₂ ⟩) {sigma = sigma}
  Vsigma x k Vconsumed t =
  cong₂
    (λ z₁ z₂ →
      SoupTerm.`case SoupReduction.consumePhi x k t `of⟨ z₁ ; z₂ ⟩)
    ( consumePhi-T (suc x) k e₁ (Translation.liftEnv sigma)
    ■ T[ e₁ ]-Env-cong (consumePhi-liftEnv x k sigma)
    )
    ( consumePhi-T (suc x) k e₂ (Translation.liftEnv sigma)
    ■ T[ e₂ ]-Env-cong (consumePhi-liftEnv x k sigma)
    )

Tᶠ*-plug-consumePhi :
  {a : ℕ} (E : SourceReduction.Frame* a)
  {sigma : Translation.Env a d} (Vsigma : ValueEnv sigma)
  (x : 𝔽 d) (k : ℕ)
  (Vconsumed : ValueEnv (consumeEnv x k sigma)) (t : SoupTerm.Tm d) →
  SoupReduction.consumePhi x k
    (SoupExpression._[_]* (Tᶠ*[ E ] {σ = sigma} Vsigma) t) ≡
  SoupExpression._[_]*
    (Tᶠ*[ E ] {σ = consumeEnv x k sigma} Vconsumed)
    (SoupReduction.consumePhi x k t)
Tᶠ*-plug-consumePhi [] Vsigma x k Vconsumed t = refl
Tᶠ*-plug-consumePhi (F₀ ∷ E) {sigma = sigma} Vsigma x k Vconsumed t =
  Tᶠ-plug-consumePhi F₀ Vsigma x k Vconsumed
    (SoupExpression._[_]* (Tᶠ*[ E ] {σ = sigma} Vsigma) t)
  ■ cong
      (SoupExpression._[_]
        (Tᶠ[ F₀ ] {σ = consumeEnv x k sigma} Vconsumed))
      (Tᶠ*-plug-consumePhi E Vsigma x k Vconsumed t)

------------------------------------------------------------------------
-- `consumePhi` commutes with the translation of a whole process.

++ₛ-consumePhi :
  (x : 𝔽 d) (l : ℕ)
  (sigma₁ sigma₁′ : Translation.Env p d)
  (sigma₂ sigma₂′ : Translation.Env q d) →
  ((y : 𝔽 p) → SoupReduction.consumePhi x l (sigma₁ y) ≡ sigma₁′ y) →
  ((y : 𝔽 q) → SoupReduction.consumePhi x l (sigma₂ y) ≡ sigma₂′ y) →
  (y : 𝔽 (p + q)) →
  SoupReduction.consumePhi x l ((sigma₁ Translation.++ₛ sigma₂) y) ≡
  (sigma₁′ Translation.++ₛ sigma₂′) y
++ₛ-consumePhi {p = p} x l sigma₁ sigma₁′ sigma₂ sigma₂′
  leftEq rightEq y
  with Fin.splitAt p y
... | inj₁ z = leftEq z
... | inj₂ z = rightEq z

private
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

-- The channel content of a flattening does not depend on its environment.
flatten-channels-env :
  {k n : ℕ} (P : Typed.Proc k)
  (lc : Vec (OrientedChannel n) (Translation.channelCount P))
  (sigma sigma′ : Translation.Env k (2 *ℕ n)) →
  proj₁ (flattenOriented P lc sigma) ≡ proj₁ (flattenOriented P lc sigma′)
flatten-channels-env (Typed.⟪ e ⟫) [] sigma sigma′ = refl
flatten-channels-env (P Typed.∥ Q) lc sigma sigma′ =
  cong₂ V._++_
    (flatten-channels-env P (V.take (Translation.channelCount P) lc)
      sigma sigma′)
    (flatten-channels-env Q (V.drop (Translation.channelCount P) lc)
      sigma sigma′)
flatten-channels-env (Typed.ν B₁ B₂ P) (ch ∷ lc) sigma sigma′ =
  cong (orientChannel (proj₂ ch) (true , flags₁ , flags₂) ∷_)
    (flatten-channels-env P lc
      ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)
      ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma′))
  where
  r₁ = physicalEndpoint ch 0F
  r₂ = physicalEndpoint ch 1F

  sigma₁ = proj₁ (Translation.UB[ B₁ ] r₁ (SoupTerm.* , r₁ , SoupTerm.*))
  sigma₂ = proj₁ (Translation.UB[ B₂ ] r₂ (SoupTerm.* , r₂ , SoupTerm.*))
  flags₁ = proj₂ (Translation.UB[ B₁ ] r₁ (SoupTerm.* , r₁ , SoupTerm.*))
  flags₂ = proj₂ (Translation.UB[ B₂ ] r₂ (SoupTerm.* , r₂ , SoupTerm.*))

-- Every thread the translation produces is consumed by rewriting the
-- environment, provided the acquired endpoint belongs to a channel the
-- process does not own.
flatten-consumePhi :
  {k n : ℕ} (P : Typed.Proc k)
  (lc : Vec (OrientedChannel n) (Translation.channelCount P))
  (sigma sigma′ : Translation.Env k (2 *ℕ n))
  (c : 𝔽 n) (s : 𝔽 2) (l : ℕ) →
  ((i : 𝔽 (Translation.channelCount P)) →
    physicalChannel (lookup lc i) ≢ c) →
  ((y : 𝔽 k) →
    SoupReduction.consumePhi (Soup.endpoint c s) l (sigma y) ≡ sigma′ y) →
  (j : 𝔽 (Translation.processCount P)) →
  SoupReduction.consumePhi (Soup.endpoint c s) l
    (lookup (proj₂ (flattenOriented P lc sigma)) j) ≡
  lookup (proj₂ (flattenOriented P lc sigma′)) j
flatten-consumePhi (Typed.⟪ e ⟫) [] sigma sigma′ c s l chanApart envEq
  zero =
  consumePhi-T (Soup.endpoint c s) l e sigma ■ T[ e ]-Env-cong envEq
flatten-consumePhi (P Typed.∥ Q) lc sigma sigma′ c s l chanApart envEq =
  lookup-++-cases₂
    (proj₂ (flattenOriented P (V.take (Translation.channelCount P) lc) sigma))
    (proj₂ (flattenOriented P (V.take (Translation.channelCount P) lc) sigma′))
    (proj₂ (flattenOriented Q (V.drop (Translation.channelCount P) lc) sigma))
    (proj₂ (flattenOriented Q (V.drop (Translation.channelCount P) lc) sigma′))
    (λ t t′ → SoupReduction.consumePhi (Soup.endpoint c s) l t ≡ t′)
    (flatten-consumePhi P (V.take (Translation.channelCount P) lc)
      sigma sigma′ c s l
      (lookup-take-cases (Translation.channelCount P) lc
        (λ ch → physicalChannel ch ≢ c) chanApart)
      envEq)
    (flatten-consumePhi Q (V.drop (Translation.channelCount P) lc)
      sigma sigma′ c s l
      (lookup-drop-cases (Translation.channelCount P) lc
        (λ ch → physicalChannel ch ≢ c) chanApart)
      envEq)
flatten-consumePhi (Typed.ν B₁ B₂ P) (ch ∷ lc) sigma sigma′ c s l
  chanApart envEq =
  flatten-consumePhi P lc
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma)
    ((sigma₁ Translation.++ₛ sigma₂) Translation.++ₛ sigma′)
    c s l
    (λ i → chanApart (suc i))
    (++ₛ-consumePhi (Soup.endpoint c s) l
      (sigma₁ Translation.++ₛ sigma₂) (sigma₁ Translation.++ₛ sigma₂)
      sigma sigma′
      (++ₛ-consumePhi (Soup.endpoint c s) l sigma₁ sigma₁ sigma₂ sigma₂
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
    SoupReduction.consumePhi (Soup.endpoint c s) l (sigma₁ y) ≡ sigma₁ y
  sigma₁-fixed = UB-phiFree-init B₁ (Soup.endpoint c s) r₁ l (apart 0F)

  sigma₂-fixed :
    (y : 𝔽 (sum B₂)) →
    SoupReduction.consumePhi (Soup.endpoint c s) l (sigma₂ y) ≡ sigma₂ y
  sigma₂-fixed = UB-phiFree-init B₂ (Soup.endpoint c s) r₂ l (apart 1F)

------------------------------------------------------------------------
-- Transporting an image across `RUS-Acquire`'s global rewrite.

consumePhi-image :
  {k n m : ℕ} {P : Typed.Proc k}
  {lc : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma sigma′ : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {channels channels′ : Vec Soup.Channel n}
  {threads : Vec (Soup.Thread n) m}
  (c : 𝔽 n) (s : 𝔽 2) (l : ℕ) →
  ((y : 𝔽 k) →
    SoupReduction.consumePhi (Soup.endpoint c s) l (sigma y) ≡ sigma′ y) →
  ((i : 𝔽 (Translation.channelCount P)) →
    physicalChannel (lookup lc i) ≢ c) →
  ((i : 𝔽 n) → ¬ ambientChannel i → lookup channels′ i ≡ lookup channels i) →
  LocalImage P lc sigma ambientChannel ambientThread
    (Soup.config channels threads) →
  LocalImage P lc sigma′ ambientChannel ambientThread
    (Soup.config channels′
      (V.map (SoupReduction.consumePhi (Soup.endpoint c s) l) threads))
consumePhi-image {P = P} {lc = lc} {sigma = sigma} {sigma′ = sigma′}
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
      V.lookup-map j (SoupReduction.consumePhi (Soup.endpoint c s) l) threads
      ■ cong (SoupReduction.consumePhi (Soup.endpoint c s) l)
          (garbage-thread image j outside notAmbient)
  }
  where
  threadEq :
    (j : 𝔽 (Translation.processCount P)) →
    SoupReduction.consumePhi (Soup.endpoint c s) l
      (lookup (proj₂ (flattenOriented P lc sigma)) j) ≡
    lookup (proj₂ (flattenOriented P lc sigma′)) j
  threadEq = flatten-consumePhi P lc sigma sigma′ c s l chanApart envEq

  targetThread :
    (j : 𝔽 (Translation.processCount P)) →
    OptionalThreadImage threads (threadEmbedding image j)
      (lookup (proj₂ (flattenOriented P lc sigma)) j) →
    OptionalThreadImage
      (V.map (SoupReduction.consumePhi (Soup.endpoint c s) l) threads)
      (threadEmbedding image j)
      (lookup (proj₂ (flattenOriented P lc sigma′)) j)
  targetThread j (present t slotEq lookupEq) =
    present t slotEq
      ( V.lookup-map t (SoupReduction.consumePhi (Soup.endpoint c s) l)
          threads
      ■ cong (SoupReduction.consumePhi (Soup.endpoint c s) l) lookupEq
      ■ threadEq j
      )
  targetThread j (omitted slotEq expectedEq) =
    omitted slotEq
      ( sym (threadEq j)
      ■ cong (SoupReduction.consumePhi (Soup.endpoint c s) l) expectedEq
      )
