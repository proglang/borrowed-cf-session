-- | Phase 1 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §9, P1): THREAD PATHS.
--
--   A soup thread is a slot of the flattened configuration.  To reflect a
--   soup step we must first name the source of that slot: the subterm
--   `⟪ e ⟫` of the typed process that produced it, and the environment that
--   the enclosing `ν`-binders accumulated on the way down.  This module
--   supplies
--
--     * `ProcessContext`, a process context with a `hole`, a `par-left`, a
--       `par-right` and a `bind` former (the retired
--       `ForwardSoup/Context.agda` had the same data type without
--       `par-right`), together with `plug`, the index maps
--       `threadInContext`/`channelInContext` and their injectivity;
--     * `locate`, which decomposes a process at a given thread index --
--       stated as the inductive family `Located` so that no coercion of a
--       `𝔽 (processCount P)` along a process equation is ever needed;
--     * `focusChannels`/`focusEnv`, the channel vector and the environment
--       seen at the hole, with `focus-channel`, `focus-thread` and the
--       corollary `thread-content` relating them to the flattening of the
--       whole process;
--     * `focusValueEnv` and `focusTyping`, which carry a `ValueEnv` and a
--       typing derivation down to the hole;
--     * `image-thread`, which turns a NON-GARBAGE soup thread of a
--       `GlobalImage` into the process-level thread index that produced it.
--
--   No frame of the soup expression calculus is ever compared for equality
--   here: frames carry `Value` proofs as functions.
module BorrowedCF.Simulation.BackwardSoup.Locate where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)
open import Data.Maybe using (Maybe; just; nothing)

import Data.Vec.Relation.Unary.All.Properties as AllVP
import Relation.Binary.Construct.Closure.Equivalence as Eq*
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star

open import BorrowedCF.Prelude

import BorrowedCF.Context as Context
import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Types using (`⊤; 𝕀)
open import BorrowedCF.Reduction.Base using (ChanCx)

open import BorrowedCF.Simulation.ForwardSoup.Expressions using (ValueEnv)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv; flatten-bind-thread; flatten-bind-channel-suc)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using (flatten-par-threads; flatten-par-channels)
open import BorrowedCF.Simulation.ForwardSoup.Local.Frames using (bindEnv-Value)
open import BorrowedCF.Simulation.ForwardSoup.World
  using (GlobalImage; logicalChannels; localImage)
open import BorrowedCF.Simulation.BackwardSoup.Inversion
  using (PairEnv; UB-Pair; ++ₛ-Pair)

open Typed using (_;_⊢ₚ_; inv-⟪⟫; inv-∥; inv-ν; bindCtx⇒chanCtx)
open Source using (_;_⊢_∶_∣_)

open Nat.Variables
open Fin.Patterns

private
  variable
    a b : ℕ

------------------------------------------------------------------------
-- Small generic lemmas.

private
  ↑ʳ-inj :
    (p : ℕ) {q : ℕ} {i j : 𝔽 q} → p ↑ʳ i ≡ p ↑ʳ j → i ≡ j
  ↑ʳ-inj zero equal = equal
  ↑ʳ-inj (suc p) equal = ↑ʳ-inj p (Fin.suc-injective equal)

  splitAt-inj₁ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {l : 𝔽 p} →
    Fin.splitAt p i ≡ inj₁ l → l ↑ˡ q ≡ i
  splitAt-inj₁ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  splitAt-inj₂ :
    (p : ℕ) {q : ℕ} {i : 𝔽 (p + q)} {r : 𝔽 q} →
    Fin.splitAt p i ≡ inj₂ r → p ↑ʳ r ≡ i
  splitAt-inj₂ p {q} {i} equal =
    sym (cong (Fin.join p q) equal) ■ Fin.join-splitAt p q i

  just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  nothing≢just : {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()

  -- The channel context of a binder-extended scope (a copy of the private
  -- helper of `ForwardSoup/Local.agda`).
  chanCx-⸴* :
    {Γ₁ : Context.Ctx a} {Γ₂ : Context.Ctx b} →
    ChanCx Γ₁ → ChanCx Γ₂ → ChanCx (Γ₁ Context.⸴* Γ₂)
  chanCx-⸴* = AllVP.++⁺

------------------------------------------------------------------------
-- 1.  Process contexts.
--
-- `ProcessContext k n` is a process of arity `n` with a hole of arity `k`.

data ProcessContext : ℕ → ℕ → Set where
  hole : ProcessContext n n

  par-left :
    ProcessContext k n →
    Typed.Proc n →
    ProcessContext k n

  par-right :
    Typed.Proc n →
    ProcessContext k n →
    ProcessContext k n

  bind :
    (B₁ B₂ : Typed.BindGroup) →
    ProcessContext k (sum B₁ + sum B₂ + n) →
    ProcessContext k n

plug : ProcessContext k n → Typed.Proc k → Typed.Proc n
plug hole P = P
plug (par-left ctx Q) P = plug ctx P Typed.∥ Q
plug (par-right Q ctx) P = Q Typed.∥ plug ctx P
plug (bind B₁ B₂ ctx) P = Typed.ν B₁ B₂ (plug ctx P)

channelInContext :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.channelCount P) →
  𝔽 (Translation.channelCount (plug ctx P))
channelInContext hole P i = i
channelInContext (par-left ctx Q) P i =
  channelInContext ctx P i ↑ˡ Translation.channelCount Q
channelInContext (par-right Q ctx) P i =
  Translation.channelCount Q ↑ʳ channelInContext ctx P i
channelInContext (bind B₁ B₂ ctx) P i =
  suc (channelInContext ctx P i)

threadInContext :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  𝔽 (Translation.processCount P) →
  𝔽 (Translation.processCount (plug ctx P))
threadInContext hole P i = i
threadInContext (par-left ctx Q) P i =
  threadInContext ctx P i ↑ˡ Translation.processCount Q
threadInContext (par-right Q ctx) P i =
  Translation.processCount Q ↑ʳ threadInContext ctx P i
threadInContext (bind B₁ B₂ ctx) P i =
  threadInContext ctx P i

channelInContext-injective :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  ∀ {i j} →
  channelInContext ctx P i ≡ channelInContext ctx P j →
  i ≡ j
channelInContext-injective hole P equal = equal
channelInContext-injective (par-left ctx Q) P equal =
  channelInContext-injective ctx P
    (Fin.↑ˡ-injective (Translation.channelCount Q) _ _ equal)
channelInContext-injective (par-right Q ctx) P equal =
  channelInContext-injective ctx P
    (↑ʳ-inj (Translation.channelCount Q) equal)
channelInContext-injective (bind B₁ B₂ ctx) P equal =
  channelInContext-injective ctx P (Fin.suc-injective equal)

threadInContext-injective :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  ∀ {i j} →
  threadInContext ctx P i ≡ threadInContext ctx P j →
  i ≡ j
threadInContext-injective hole P equal = equal
threadInContext-injective (par-left ctx Q) P equal =
  threadInContext-injective ctx P
    (Fin.↑ˡ-injective (Translation.processCount Q) _ _ equal)
threadInContext-injective (par-right Q ctx) P equal =
  threadInContext-injective ctx P
    (↑ʳ-inj (Translation.processCount Q) equal)
threadInContext-injective (bind B₁ B₂ ctx) P equal =
  threadInContext-injective ctx P equal

compose :
  ProcessContext a n → ProcessContext k a → ProcessContext k n
compose hole inner = inner
compose (par-left outer Q) inner = par-left (compose outer inner) Q
compose (par-right Q outer) inner = par-right Q (compose outer inner)
compose (bind B₁ B₂ outer) inner = bind B₁ B₂ (compose outer inner)

plug-compose :
  (outer : ProcessContext a n) (inner : ProcessContext k a)
  (P : Typed.Proc k) →
  plug (compose outer inner) P ≡ plug outer (plug inner P)
plug-compose hole inner P = refl
plug-compose (par-left outer Q) inner P =
  cong (Typed._∥ Q) (plug-compose outer inner P)
plug-compose (par-right Q outer) inner P =
  cong (Q Typed.∥_) (plug-compose outer inner P)
plug-compose (bind B₁ B₂ outer) inner P =
  cong (Typed.ν B₁ B₂) (plug-compose outer inner P)

------------------------------------------------------------------------
-- 2.  Locating a thread.
--
-- `Located P i` says that `P` is `plug ctx ⟪ e ⟫` and that `i` is the index
-- of that expression's thread.  Phrasing it as an inductive family avoids
-- transporting `i : 𝔽 (processCount P)` along a process equation: a pattern
-- match on the single constructor makes both facts hold definitionally.

data Located : (P : Typed.Proc n) → 𝔽 (Translation.processCount P) → Set where
  located :
    {n k : ℕ} (ctx : ProcessContext k n) (e : Source.Tm k) →
    Located (plug ctx Typed.⟪ e ⟫)
      (threadInContext ctx Typed.⟪ e ⟫ zero)

private
  located-left :
    {n : ℕ} {P : Typed.Proc n} {i : 𝔽 (Translation.processCount P)}
    (Q : Typed.Proc n) →
    Located P i → Located (P Typed.∥ Q) (i ↑ˡ Translation.processCount Q)
  located-left Q (located ctx e) = located (par-left ctx Q) e

  located-right :
    {n : ℕ} {Q : Typed.Proc n} {i : 𝔽 (Translation.processCount Q)}
    (P : Typed.Proc n) →
    Located Q i → Located (P Typed.∥ Q) (Translation.processCount P ↑ʳ i)
  located-right P (located ctx e) = located (par-right P ctx) e

  located-bind :
    {n : ℕ} (B₁ B₂ : Typed.BindGroup)
    {P : Typed.Proc (sum B₁ + sum B₂ + n)}
    {i : 𝔽 (Translation.processCount P)} →
    Located P i → Located (Typed.ν B₁ B₂ P) i
  located-bind B₁ B₂ (located ctx e) = located (bind B₁ B₂ ctx) e

locate :
  (P : Typed.Proc n) (i : 𝔽 (Translation.processCount P)) → Located P i
locate Typed.⟪ e ⟫ zero = located hole e
locate (P Typed.∥ Q) i
  with Fin.splitAt (Translation.processCount P) i in splitEq
... | inj₁ l =
  subst (Located (P Typed.∥ Q))
    (splitAt-inj₁ (Translation.processCount P) splitEq)
    (located-left Q (locate P l))
... | inj₂ r =
  subst (Located (P Typed.∥ Q))
    (splitAt-inj₂ (Translation.processCount P) splitEq)
    (located-right P (locate Q r))
locate (Typed.ν B₁ B₂ P) i = located-bind B₁ B₂ (locate P i)

-- The Σ-shaped restatement asked for in `PLAN.md` §9.  The position
-- equation has to be transported along the process equation, which is why
-- `Located` is the primary form.
locate-Σ :
  (P : Typed.Proc n) (i : 𝔽 (Translation.processCount P)) →
  Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k n ] Σ[ e ∈ Source.Tm k ]
    Σ[ shape ∈ plug ctx Typed.⟪ e ⟫ ≡ P ]
      subst (λ R → 𝔽 (Translation.processCount R)) shape
        (threadInContext ctx Typed.⟪ e ⟫ zero) ≡ i
locate-Σ P i with locate P i
... | located ctx e = _ , ctx , e , refl , refl

------------------------------------------------------------------------
-- 3.  Focusing channels and environments at the hole.

focusChannels :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c) (Translation.channelCount (plug ctx P)) →
  Vec (OrientedChannel c) (Translation.channelCount P)
focusChannels hole P channels = channels
focusChannels (par-left ctx Q) P channels =
  focusChannels ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels)
focusChannels (par-right Q ctx) P channels =
  focusChannels ctx P (V.drop (Translation.channelCount Q) channels)
focusChannels (bind B₁ B₂ ctx) P (channel ∷ channels) =
  focusChannels ctx P channels

focusEnv :
  (ctx : ProcessContext k n) (P : Typed.Proc k) →
  Vec (OrientedChannel c) (Translation.channelCount (plug ctx P)) →
  Translation.Env n (2 *ℕ c) →
  Translation.Env k (2 *ℕ c)
focusEnv hole P channels sigma = sigma
focusEnv (par-left ctx Q) P channels sigma =
  focusEnv ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels) sigma
focusEnv (par-right Q ctx) P channels sigma =
  focusEnv ctx P (V.drop (Translation.channelCount Q) channels) sigma
focusEnv (bind B₁ B₂ ctx) P (channel ∷ channels) sigma =
  focusEnv ctx P channels (bindEnv B₁ B₂ channel sigma)

focusValueEnv :
  (ctx : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug ctx P)))
  {sigma : Translation.Env n (2 *ℕ c)} →
  ValueEnv sigma → ValueEnv (focusEnv ctx P channels sigma)
focusValueEnv hole P channels Vsigma = Vsigma
focusValueEnv (par-left ctx Q) P channels Vsigma =
  focusValueEnv ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels) Vsigma
focusValueEnv (par-right Q ctx) P channels Vsigma =
  focusValueEnv ctx P
    (V.drop (Translation.channelCount Q) channels) Vsigma
focusValueEnv (bind B₁ B₂ ctx) P (channel ∷ channels) Vsigma =
  focusValueEnv ctx P channels
    (bindEnv-Value {B₁ = B₁} {B₂ = B₂} {channel = channel} Vsigma)

-- The companion for `PairEnv` (`Inversion.agda`): every binder-group entry
-- is a `chanTriple`, hence a pair, so the property survives every `ν` on the
-- path.  This is what discharges the `PairEnv` hypothesis of
-- `plug-inversion-K` and `step-inversion` for the environments the backward
-- proof actually meets.
bindEnv-Pair :
  {k n : ℕ} {B₁ B₂ : Typed.BindGroup} {channel : OrientedChannel n}
  {sigma : Translation.Env k (2 *ℕ n)} →
  PairEnv sigma → PairEnv (bindEnv B₁ B₂ channel sigma)
bindEnv-Pair {B₁ = B₁} {B₂ = B₂} {channel = channel} Psigma =
  ++ₛ-Pair
    (++ₛ-Pair
      (UB-Pair B₁ (physicalEndpoint channel 0F))
      (UB-Pair B₂ (physicalEndpoint channel 1F)))
    Psigma

focusPairEnv :
  (ctx : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug ctx P)))
  {sigma : Translation.Env n (2 *ℕ c)} →
  PairEnv sigma → PairEnv (focusEnv ctx P channels sigma)
focusPairEnv hole P channels Psigma = Psigma
focusPairEnv (par-left ctx Q) P channels Psigma =
  focusPairEnv ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels) Psigma
focusPairEnv (par-right Q ctx) P channels Psigma =
  focusPairEnv ctx P
    (V.drop (Translation.channelCount Q) channels) Psigma
focusPairEnv (bind B₁ B₂ ctx) P (channel ∷ channels) Psigma =
  focusPairEnv ctx P channels
    (bindEnv-Pair {B₁ = B₁} {B₂ = B₂} {channel = channel} Psigma)

-- The empty environment of a closed process is trivially a pair environment.
closedPairEnv : {n : ℕ} → PairEnv {0} {n} (λ ())
closedPairEnv ()

------------------------------------------------------------------------
-- 4.  The flattening at the hole.

focus-channel :
  (ctx : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug ctx P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.channelCount P)) →
  lookup (proj₁ (flattenOriented (plug ctx P) channels sigma))
    (channelInContext ctx P i) ≡
  lookup (proj₁ (flattenOriented P
    (focusChannels ctx P channels)
    (focusEnv ctx P channels sigma))) i
focus-channel hole P channels sigma i = refl
focus-channel (par-left ctx Q) P channels sigma i =
  cong
    (λ cs → lookup cs
      (channelInContext ctx P i ↑ˡ Translation.channelCount Q))
    (flatten-par-channels (plug ctx P) Q channels sigma) ■
  V.lookup-++ˡ
    (proj₁ (flattenOriented (plug ctx P)
      (V.take (Translation.channelCount (plug ctx P)) channels) sigma))
    (proj₁ (flattenOriented Q
      (V.drop (Translation.channelCount (plug ctx P)) channels) sigma))
    (channelInContext ctx P i) ■
  focus-channel ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels) sigma i
focus-channel (par-right Q ctx) P channels sigma i =
  cong
    (λ cs → lookup cs
      (Translation.channelCount Q ↑ʳ channelInContext ctx P i))
    (flatten-par-channels Q (plug ctx P) channels sigma) ■
  V.lookup-++ʳ
    (proj₁ (flattenOriented Q
      (V.take (Translation.channelCount Q) channels) sigma))
    (proj₁ (flattenOriented (plug ctx P)
      (V.drop (Translation.channelCount Q) channels) sigma))
    (channelInContext ctx P i) ■
  focus-channel ctx P
    (V.drop (Translation.channelCount Q) channels) sigma i
focus-channel (bind B₁ B₂ ctx) P (channel ∷ channels) sigma i =
  flatten-bind-channel-suc {B₁ = B₁} {B₂ = B₂} {P = plug ctx P}
    {channel = channel} {logicalChannels = channels} {sigma = sigma}
    (channelInContext ctx P i) ■
  focus-channel ctx P channels (bindEnv B₁ B₂ channel sigma) i

focus-thread :
  (ctx : ProcessContext k n) (P : Typed.Proc k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug ctx P)))
  (sigma : Translation.Env n (2 *ℕ c))
  (i : 𝔽 (Translation.processCount P)) →
  lookup (proj₂ (flattenOriented (plug ctx P) channels sigma))
    (threadInContext ctx P i) ≡
  lookup (proj₂ (flattenOriented P
    (focusChannels ctx P channels)
    (focusEnv ctx P channels sigma))) i
focus-thread hole P channels sigma i = refl
focus-thread (par-left ctx Q) P channels sigma i =
  cong
    (λ ts → lookup ts
      (threadInContext ctx P i ↑ˡ Translation.processCount Q))
    (flatten-par-threads (plug ctx P) Q channels sigma) ■
  V.lookup-++ˡ
    (proj₂ (flattenOriented (plug ctx P)
      (V.take (Translation.channelCount (plug ctx P)) channels) sigma))
    (proj₂ (flattenOriented Q
      (V.drop (Translation.channelCount (plug ctx P)) channels) sigma))
    (threadInContext ctx P i) ■
  focus-thread ctx P
    (V.take (Translation.channelCount (plug ctx P)) channels) sigma i
focus-thread (par-right Q ctx) P channels sigma i =
  cong
    (λ ts → lookup ts
      (Translation.processCount Q ↑ʳ threadInContext ctx P i))
    (flatten-par-threads Q (plug ctx P) channels sigma) ■
  V.lookup-++ʳ
    (proj₂ (flattenOriented Q
      (V.take (Translation.channelCount Q) channels) sigma))
    (proj₂ (flattenOriented (plug ctx P)
      (V.drop (Translation.channelCount Q) channels) sigma))
    (threadInContext ctx P i) ■
  focus-thread ctx P
    (V.drop (Translation.channelCount Q) channels) sigma i
focus-thread (bind B₁ B₂ ctx) P (channel ∷ channels) sigma i =
  flatten-bind-thread {B₁ = B₁} {B₂ = B₂} {P = plug ctx P}
    {channel = channel} {logicalChannels = channels} {sigma = sigma}
    (threadInContext ctx P i) ■
  focus-thread ctx P channels (bindEnv B₁ B₂ channel sigma) i

private
  flatten-expr-thread :
    {k : ℕ} (e : Source.Tm k)
    (channels : Vec (OrientedChannel c) 0)
    (sigma : Translation.Env k (2 *ℕ c)) →
    lookup (proj₂ (flattenOriented Typed.⟪ e ⟫ channels sigma)) zero ≡
    Translation.T[ e ] sigma
  flatten-expr-thread e [] sigma = refl

-- The located thread's content: the translation of the located expression
-- under the focused environment.
thread-content :
  (ctx : ProcessContext k n) (e : Source.Tm k)
  (channels : Vec (OrientedChannel c)
    (Translation.channelCount (plug ctx Typed.⟪ e ⟫)))
  (sigma : Translation.Env n (2 *ℕ c)) →
  lookup (proj₂ (flattenOriented (plug ctx Typed.⟪ e ⟫) channels sigma))
    (threadInContext ctx Typed.⟪ e ⟫ zero) ≡
  Translation.T[ e ] (focusEnv ctx Typed.⟪ e ⟫ channels sigma)
thread-content ctx e channels sigma =
  focus-thread ctx Typed.⟪ e ⟫ channels sigma zero ■
  flatten-expr-thread e
    (focusChannels ctx Typed.⟪ e ⟫ channels)
    (focusEnv ctx Typed.⟪ e ⟫ channels sigma)

------------------------------------------------------------------------
-- 5.  Carrying a typing derivation to the hole.

focusTyping :
  (ctx : ProcessContext k n) (P : Typed.Proc k)
  {Γ : Context.Ctx n} {γ : Context.Struct n} →
  ChanCx Γ → Γ ; γ ⊢ₚ plug ctx P →
  Σ[ Γ′ ∈ Context.Ctx k ] Σ[ γ′ ∈ Context.Struct k ]
    ChanCx Γ′ × (Γ′ ; γ′ ⊢ₚ P)
focusTyping hole P Γ-S ⊢P = _ , _ , Γ-S , ⊢P
focusTyping (par-left ctx Q) P Γ-S ⊢P with inv-∥ ⊢P
... | _ , _ , _ , ⊢left , _ = focusTyping ctx P Γ-S ⊢left
focusTyping (par-right Q ctx) P Γ-S ⊢P with inv-∥ ⊢P
... | _ , _ , _ , _ , ⊢right = focusTyping ctx P Γ-S ⊢right
focusTyping (bind B₁ B₂ ctx) P Γ-S ⊢P with inv-ν ⊢P
... | _ , _ , _ , _ , _ , _ , _ , Cx , Cx′ , ⊢body =
  focusTyping ctx P
    (chanCx-⸴* (chanCx-⸴* (bindCtx⇒chanCtx Cx) (bindCtx⇒chanCtx Cx′)) Γ-S)
    ⊢body

focusExprTyping :
  (ctx : ProcessContext k n) (e : Source.Tm k)
  {Γ : Context.Ctx n} {γ : Context.Struct n} →
  ChanCx Γ → Γ ; γ ⊢ₚ plug ctx Typed.⟪ e ⟫ →
  Σ[ Γ′ ∈ Context.Ctx k ] Σ[ γ′ ∈ Context.Struct k ]
    ChanCx Γ′ × (Γ′ ; γ′ ⊢ e ∶ `⊤ ∣ 𝕀)
focusExprTyping ctx e Γ-S ⊢P
  with focusTyping ctx Typed.⟪ e ⟫ Γ-S ⊢P
... | Γ′ , γ′ , Γ′-S , ⊢body = Γ′ , γ′ , Γ′-S , inv-⟪⟫ ⊢body

------------------------------------------------------------------------
-- 6.  From a soup thread back to a process thread.

private
  shiftFound :
    {p q : ℕ} {f : 𝔽 (suc p) → Maybe (𝔽 q)} {j : 𝔽 q} →
    (f zero ≢ just j) →
    (Σ[ i ∈ 𝔽 p ] f (suc i) ≡ just j) ⊎
      ((i : 𝔽 p) → f (suc i) ≢ just j) →
    (Σ[ i ∈ 𝔽 (suc p) ] f i ≡ just j) ⊎
      ((i : 𝔽 (suc p)) → f i ≢ just j)
  shiftFound head≢ (inj₁ (i , equal)) = inj₁ (suc i , equal)
  shiftFound head≢ (inj₂ none) = inj₂ λ where
    zero → head≢
    (suc i) → none i

  findFin :
    (p : ℕ) {q : ℕ} (f : 𝔽 p → Maybe (𝔽 q)) (j : 𝔽 q) →
    (Σ[ i ∈ 𝔽 p ] f i ≡ just j) ⊎ ((i : 𝔽 p) → f i ≢ just j)
  findFin zero f j = inj₂ λ ()
  findFin (suc p) f j with f zero in headEq
  ... | nothing =
    shiftFound {f = f} (λ equal → nothing≢just (sym headEq ■ equal))
      (findFin p (λ i → f (suc i)) j)
  ... | just l with l Fin.≟ j
  ...   | yes refl = inj₁ (zero , headEq)
  ...   | no l≢j =
    shiftFound {f = f} (λ equal → l≢j (just-inj (sym headEq ■ equal)))
      (findFin p (λ i → f (suc i)) j)

-- A soup thread that is not the garbage term `K unit` is the image of a
-- (unique, by `threadEmbedding-injective`) process thread, and its content
-- is that thread's flattening.
image-thread :
  {n m : ℕ} {P : Typed.Proc 0} {C : Soup.Config n m}
  (image : GlobalImage P C) (j : 𝔽 m) →
  lookup (Soup.threads C) j ≢ SoupTerm.K Source.`unit →
  Σ[ i ∈ 𝔽 (Translation.processCount P) ]
    (threadEmbedding (localImage image) i ≡ just j) ×
    (lookup (Soup.threads C) j ≡
      lookup (proj₂ (flattenOriented P (logicalChannels image) (λ ()))) i)
image-thread {P = P} {C = C} image j notUnit
  with findFin (Translation.processCount P)
         (threadEmbedding (localImage image)) j
... | inj₂ none =
  ⊥-elim (notUnit (garbage-thread (localImage image) j none (λ ())))
... | inj₁ (i , embedded)
  with live-thread (localImage image) i
...   | present l slotEq live =
  i , embedded ,
  (cong (lookup (Soup.threads C)) (just-inj (sym embedded ■ slotEq)) ■ live)
...   | omitted slotEq unitEq =
  ⊥-elim (nothing≢just (sym slotEq ■ embedded))

-- `image-thread` followed by `locate` and `thread-content`: a live soup
-- thread is the translation of a located source expression under the
-- environment accumulated along its path.
image-thread-term :
  {n m : ℕ} {P : Typed.Proc 0} {C : Soup.Config n m}
  (image : GlobalImage P C) (j : 𝔽 m) →
  lookup (Soup.threads C) j ≢ SoupTerm.K Source.`unit →
  Σ[ k ∈ ℕ ] Σ[ ctx ∈ ProcessContext k 0 ] Σ[ e ∈ Source.Tm k ]
  Σ[ i ∈ 𝔽 (Translation.processCount P) ]
  Σ[ shape ∈ plug ctx Typed.⟪ e ⟫ ≡ P ]
    (subst (λ R → 𝔽 (Translation.processCount R)) shape
      (threadInContext ctx Typed.⟪ e ⟫ zero) ≡ i) ×
    (threadEmbedding (localImage image) i ≡ just j) ×
    (lookup (Soup.threads C) j ≡
      Translation.T[ e ]
        (focusEnv ctx Typed.⟪ e ⟫
          (subst
            (λ R → Vec (OrientedChannel n) (Translation.channelCount R))
            (sym shape) (logicalChannels image))
          (λ ())))
image-thread-term {P = P} image j notUnit
  with image-thread image j notUnit
... | i , embedded , content with locate P i
...   | located ctx e =
  _ , ctx , e , _ , refl , refl , embedded ,
  (content ■ thread-content ctx e (logicalChannels image) (λ ()))

------------------------------------------------------------------------
-- 7.  `≋` housekeeping.
--
-- (Moved here from `Canonical.agda` so that `Tracks.agda` -- which must not
-- depend on `Canonical.agda` -- can talk about the very same derivations.)

≋-sym : {P Q : Typed.Proc n} → P Typed.≋ Q → Q Typed.≋ P
≋-sym = Eq*.symmetric Typed._≋′_

≡→≋ : {P Q : Typed.Proc n} → P ≡ Q → P Typed.≋ Q
≡→≋ refl = Star.ε

-- A `≋` step is a congruence for every process context.
≋-plug :
  (c : ProcessContext k n) {P Q : Typed.Proc k} →
  P Typed.≋ Q → plug c P Typed.≋ plug c Q
≋-plug hole eq = eq
≋-plug (par-left c R₀) eq = Typed.∥-cong (≋-plug c eq) Star.ε
≋-plug (par-right R₀ c) eq = Typed.∥-cong Star.ε (≋-plug c eq)
≋-plug (bind B₁ B₂ c) eq = Typed.ν-cong (≋-plug c eq)
