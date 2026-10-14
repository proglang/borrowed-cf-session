-- | THE DECISIVE PROCESS-LEVEL FACT for multi-block backward-com (verdict A).
--
--   `ComProcessCex` established that a Mobile front pins the ν's send-side bind
--   group to R-Acq's shape `0 ∷ suc b ∷ B′`, with the front `0F` acq-headed and
--   the borrow's `acq` genuine (¬Mobile ⟨acq⟩).  What remained (com-fill's exact
--   verdict-B claim): "acq-headed session ≠ syntactic acq redex thread" — maybe a
--   well-typed com preimage SENDS the mobile borrow around the marker, firing the
--   send on a LATER msg channel with `0F` never `acq`-ed, so `R-Com` is blocked
--   (send behind marker) AND `R-Acq` is blocked (no `acq·0F` thread): a STUCK com.
--
--   THIS MODULE REFUTES THAT.  Between the Mobile front and the msg handle a
--   New-ν bind context always exposes a non-Mobile `acq`-channel (`mid`); the msg
--   handle (`h`) is non-Mobile too (msg is NoAcq).  The send-side body is typed
--   against `structBinder B₁`, which SEQUENCES the block's channels: `mid` is
--   `;`-before `h`.  The ordered algebra `_∶_≼_` is RIGID on non-Mobile leaves:
--   its ONLY ∥↔; converter `∥′-tm-;` needs a MobCx side, there is no `;`-comm,
--   and `≼-wk` only DROPS order.  Hence a body that presents `mid` and `h` in a
--   PARALLEL arrangement (as any bare `send`/`recv` thread composition does —
--   `send` builds `⟨msg⟩ ∥ ⟨handle⟩`, threads compose by `∥`) can NEVER be `≼`
--   `structBinder B₁`.  The only well-typed arrangement SEQUENCES `mid`'s `acq`
--   before the send (`acq` at head) — which is exactly an admin redex, in lockstep
--   with the untyped image.  So no STUCK separated com exists: verdict A.
--
--   Core theorem: `≺-antitone` — for non-Mobile x,y, `x`-`;`-before-`y` transports
--   BACKWARD along `_≼_`.  Corollary `bareSend-¬≼` — an all-parallel body cannot
--   `≼` any structure that `;`-orders two non-Mobile channels.  Concrete instance
--   `crux-A`/`crux-B` refute the two bare-send arrangements over the canonical
--   `⟨acq;ret⟩ , ⟨acq⟩ , ⟨msg⟩` bind context.  All exit 0, no holes/postulates.
module BorrowedCF.Simulation.Backward.ComOrderRigidity where

open import BorrowedCF.Prelude
open import BorrowedCF.Types.Syntax
open import BorrowedCF.Types.Equivalence
import BorrowedCF.Types.Predicates as P
open P using (Mobile; Unr; unr⇒mobile)
open import BorrowedCF.Context
open import BorrowedCF.Simulation.Support.CloseVacuityProbe using (NoAcq; ¬mobile-noAcq)
open import BorrowedCF.Simulation.Backward.ComProcessCex using (¬mobile-acq)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)

open Fin.Patterns

------------------------------------------------------------------------
-- Leaf occurrence and strict `;`-precedence in a Struct.
------------------------------------------------------------------------

data _∈ₗ_ {n} : 𝔽 n → Struct n → Set where
  here : ∀ {x} → x ∈ₗ (` x)
  pL : ∀ {x α β} → x ∈ₗ α → x ∈ₗ (α ∥ β)
  pR : ∀ {x α β} → x ∈ₗ β → x ∈ₗ (α ∥ β)
  sL : ∀ {x α β} → x ∈ₗ α → x ∈ₗ (α ; β)
  sR : ∀ {x α β} → x ∈ₗ β → x ∈ₗ (α ; β)

data _≺⟨_⟩_ {n} : 𝔽 n → Struct n → 𝔽 n → Set where
  mid : ∀ {x y α β} → x ∈ₗ α → y ∈ₗ β → x ≺⟨ α ; β ⟩ y
  qL  : ∀ {x y α β} → x ≺⟨ α ⟩ y → x ≺⟨ α ; β ⟩ y
  qR  : ∀ {x y α β} → x ≺⟨ β ⟩ y → x ≺⟨ α ; β ⟩ y
  rL  : ∀ {x y α β} → x ≺⟨ α ⟩ y → x ≺⟨ α ∥ β ⟩ y
  rR  : ∀ {x y α β} → x ≺⟨ β ⟩ y → x ≺⟨ α ∥ β ⟩ y

private
  NM : ∀ {n} → Ctx n → 𝔽 n → Set
  NM Γ x = ¬ Mobile (lookup Γ x)

------------------------------------------------------------------------
-- A leaf inside a MobCx (resp. UnrCx) is Mobile (resp. Unr).
------------------------------------------------------------------------

∈ₗ-mobile : ∀ {n} {Γ : Ctx n} {x α} → x ∈ₗ α → MobCx Γ α → Mobile (lookup Γ x)
∈ₗ-mobile here   mc = allCx-`⁻¹ mc
∈ₗ-mobile (pL i) mc = ∈ₗ-mobile i (proj₁ (allCx-∥⁻¹ mc))
∈ₗ-mobile (pR i) mc = ∈ₗ-mobile i (proj₂ (allCx-∥⁻¹ mc))
∈ₗ-mobile (sL i) mc = ∈ₗ-mobile i (proj₁ (allCx-;⁻¹ mc))
∈ₗ-mobile (sR i) mc = ∈ₗ-mobile i (proj₂ (allCx-;⁻¹ mc))

∈ₗ-unr : ∀ {n} {Γ : Ctx n} {x α} → x ∈ₗ α → UnrCx Γ α → Unr (lookup Γ x)
∈ₗ-unr here   U = allCx-`⁻¹ U
∈ₗ-unr (pL i) U = ∈ₗ-unr i (proj₁ (allCx-∥⁻¹ U))
∈ₗ-unr (pR i) U = ∈ₗ-unr i (proj₂ (allCx-∥⁻¹ U))
∈ₗ-unr (sL i) U = ∈ₗ-unr i (proj₁ (allCx-;⁻¹ U))
∈ₗ-unr (sR i) U = ∈ₗ-unr i (proj₂ (allCx-;⁻¹ U))

------------------------------------------------------------------------
-- ∈ₗ is preserved by ≈′ (both directions; no mobility needed).
------------------------------------------------------------------------

∈ₗ-≈′→ : ∀ {n} {Γ : Ctx n} {x α β} → Γ ∶ α ≈′ β → x ∈ₗ α → x ∈ₗ β
∈ₗ-≈′← : ∀ {n} {Γ : Ctx n} {x α β} → Γ ∶ α ≈′ β → x ∈ₗ β → x ∈ₗ α

∈ₗ-≈′→ ;′-assoc (sL (sL i)) = sL i
∈ₗ-≈′→ ;′-assoc (sL (sR i)) = sR (sL i)
∈ₗ-≈′→ ;′-assoc (sR i)      = sR (sR i)
∈ₗ-≈′→ (;′-cong₁ e) (sL i) = sL (∈ₗ-≈′→ e i)
∈ₗ-≈′→ (;′-cong₁ e) (sR i) = sR i
∈ₗ-≈′→ (;′-cong₂ e) (sL i) = sL i
∈ₗ-≈′→ (;′-cong₂ e) (sR i) = sR (∈ₗ-≈′→ e i)
∈ₗ-≈′→ ∥′-unit (pL i) = i
∈ₗ-≈′→ ∥′-assoc (pL (pL i)) = pL i
∈ₗ-≈′→ ∥′-assoc (pL (pR i)) = pR (pL i)
∈ₗ-≈′→ ∥′-assoc (pR i)      = pR (pR i)
∈ₗ-≈′→ ∥′-comm (pL i) = pR i
∈ₗ-≈′→ ∥′-comm (pR i) = pL i
∈ₗ-≈′→ (∥′-cong₁ e) (pL i) = pL (∈ₗ-≈′→ e i)
∈ₗ-≈′→ (∥′-cong₁ e) (pR i) = pR i
∈ₗ-≈′→ (∥′-dup U) i = pL i
∈ₗ-≈′→ (∥′-tm-; U) (pL i) = sL i
∈ₗ-≈′→ (∥′-tm-; U) (pR i) = sR i

∈ₗ-≈′← ;′-assoc (sL i)      = sL (sL i)
∈ₗ-≈′← ;′-assoc (sR (sL i)) = sL (sR i)
∈ₗ-≈′← ;′-assoc (sR (sR i)) = sR i
∈ₗ-≈′← (;′-cong₁ e) (sL i) = sL (∈ₗ-≈′← e i)
∈ₗ-≈′← (;′-cong₁ e) (sR i) = sR i
∈ₗ-≈′← (;′-cong₂ e) (sL i) = sL i
∈ₗ-≈′← (;′-cong₂ e) (sR i) = sR (∈ₗ-≈′← e i)
∈ₗ-≈′← ∥′-unit i = pL i
∈ₗ-≈′← ∥′-assoc (pL i)      = pL (pL i)
∈ₗ-≈′← ∥′-assoc (pR (pL i)) = pL (pR i)
∈ₗ-≈′← ∥′-assoc (pR (pR i)) = pR i
∈ₗ-≈′← ∥′-comm (pL i) = pR i
∈ₗ-≈′← ∥′-comm (pR i) = pL i
∈ₗ-≈′← (∥′-cong₁ e) (pL i) = pL (∈ₗ-≈′← e i)
∈ₗ-≈′← (∥′-cong₁ e) (pR i) = pR i
∈ₗ-≈′← (∥′-dup U) (pL i) = i
∈ₗ-≈′← (∥′-dup U) (pR i) = i
∈ₗ-≈′← (∥′-tm-; U) (sL i) = pL i
∈ₗ-≈′← (∥′-tm-; U) (sR i) = pR i

∈ₗ-≈→ : ∀ {n} {Γ : Ctx n} {x α β} → Γ ∶ α ≈ β → x ∈ₗ α → x ∈ₗ β
∈ₗ-≈→ ε         i = i
∈ₗ-≈→ (fwd e ◅ r) i = ∈ₗ-≈→ r (∈ₗ-≈′→ e i)
∈ₗ-≈→ (bwd e ◅ r) i = ∈ₗ-≈→ r (∈ₗ-≈′← e i)

------------------------------------------------------------------------
-- ∈ₗ transports BACKWARD along ≼ for NON-Mobile leaves (the extra
-- channels a `≼` may add are Unr, hence Mobile — so a non-Mobile leaf of
-- the bigger side is already a leaf of the smaller side).
------------------------------------------------------------------------

∈ₗ-≼ : ∀ {n} {Γ : Ctx n} {x α β} → Γ ∶ α ≼ β → NM Γ x → x ∈ₗ β → x ∈ₗ α
∈ₗ-≼ (≼-refl e)     nx i = ∈ₗ-≈→ (≈-sym e) i
∈ₗ-≼ (≼-∅ U)        nx i = ⊥-elim (nx (unr⇒mobile (∈ₗ-unr i U)))
∈ₗ-≼ ≼-wk           nx (pL (sL i)) = sL (pL i)
∈ₗ-≼ ≼-wk           nx (pL (sR i)) = sR (pL i)
∈ₗ-≼ ≼-wk           nx (pR (sL i)) = sL (pR i)
∈ₗ-≼ ≼-wk           nx (pR (sR i)) = sR (pR i)
∈ₗ-≼ (≼-trans p q)  nx i = ∈ₗ-≼ p nx (∈ₗ-≼ q nx i)
∈ₗ-≼ (≼-cong-; p q) nx (sL i) = sL (∈ₗ-≼ p nx i)
∈ₗ-≼ (≼-cong-; p q) nx (sR i) = sR (∈ₗ-≼ q nx i)
∈ₗ-≼ (≼-cong-∥ p q) nx (pL i) = pL (∈ₗ-≼ p nx i)
∈ₗ-≼ (≼-cong-∥ p q) nx (pR i) = pR (∈ₗ-≼ q nx i)

------------------------------------------------------------------------
-- ≺ is preserved by ≈′ for NON-Mobile x,y.  The ONLY delicate case is
-- `∥′-tm-;`: reading its `α∥β ≈ α;β` backward would turn a `∥`-pair into a
-- `;`-pair (a `mid`), but that needs x∈α with MobCx α (or y∈β, MobCx β) —
-- impossible for non-Mobile x,y.
------------------------------------------------------------------------

≺-≈′→ : ∀ {n} {Γ : Ctx n} {x y α β} → Γ ∶ α ≈′ β → NM Γ x → NM Γ y → x ≺⟨ α ⟩ y → x ≺⟨ β ⟩ y
≺-≈′← : ∀ {n} {Γ : Ctx n} {x y α β} → Γ ∶ α ≈′ β → NM Γ x → NM Γ y → x ≺⟨ β ⟩ y → x ≺⟨ α ⟩ y

≺-≈′→ ;′-assoc nx ny (mid (sL i) j) = mid i (sR j)
≺-≈′→ ;′-assoc nx ny (mid (sR i) j) = qR (mid i j)
≺-≈′→ ;′-assoc nx ny (qL (mid i j)) = mid i (sL j)
≺-≈′→ ;′-assoc nx ny (qL (qL p))    = qL p
≺-≈′→ ;′-assoc nx ny (qL (qR p))    = qR (qL p)
≺-≈′→ ;′-assoc nx ny (qR p)         = qR (qR p)
≺-≈′→ (;′-cong₁ e) nx ny (mid i j) = mid (∈ₗ-≈′→ e i) j
≺-≈′→ (;′-cong₁ e) nx ny (qL p)    = qL (≺-≈′→ e nx ny p)
≺-≈′→ (;′-cong₁ e) nx ny (qR p)    = qR p
≺-≈′→ (;′-cong₂ e) nx ny (mid i j) = mid i (∈ₗ-≈′→ e j)
≺-≈′→ (;′-cong₂ e) nx ny (qL p)    = qL p
≺-≈′→ (;′-cong₂ e) nx ny (qR p)    = qR (≺-≈′→ e nx ny p)
≺-≈′→ ∥′-unit nx ny (rL p) = p
≺-≈′→ ∥′-assoc nx ny (rL (rL p)) = rL p
≺-≈′→ ∥′-assoc nx ny (rL (rR p)) = rR (rL p)
≺-≈′→ ∥′-assoc nx ny (rR p)      = rR (rR p)
≺-≈′→ ∥′-comm nx ny (rL p) = rR p
≺-≈′→ ∥′-comm nx ny (rR p) = rL p
≺-≈′→ (∥′-cong₁ e) nx ny (rL p) = rL (≺-≈′→ e nx ny p)
≺-≈′→ (∥′-cong₁ e) nx ny (rR p) = rR p
≺-≈′→ (∥′-dup U) nx ny p = rL p
≺-≈′→ (∥′-tm-; U) nx ny (rL p) = qL p
≺-≈′→ (∥′-tm-; U) nx ny (rR p) = qR p

≺-≈′← ;′-assoc nx ny (mid i (sL j)) = qL (mid i j)
≺-≈′← ;′-assoc nx ny (mid i (sR j)) = mid (sL i) j
≺-≈′← ;′-assoc nx ny (qL p)         = qL (qL p)
≺-≈′← ;′-assoc nx ny (qR (mid i j)) = mid (sR i) j
≺-≈′← ;′-assoc nx ny (qR (qL p))    = qL (qR p)
≺-≈′← ;′-assoc nx ny (qR (qR p))    = qR p
≺-≈′← (;′-cong₁ e) nx ny (mid i j) = mid (∈ₗ-≈′← e i) j
≺-≈′← (;′-cong₁ e) nx ny (qL p)    = qL (≺-≈′← e nx ny p)
≺-≈′← (;′-cong₁ e) nx ny (qR p)    = qR p
≺-≈′← (;′-cong₂ e) nx ny (mid i j) = mid i (∈ₗ-≈′← e j)
≺-≈′← (;′-cong₂ e) nx ny (qL p)    = qL p
≺-≈′← (;′-cong₂ e) nx ny (qR p)    = qR (≺-≈′← e nx ny p)
≺-≈′← ∥′-unit nx ny p = rL p
≺-≈′← ∥′-assoc nx ny (rL p)        = rL (rL p)
≺-≈′← ∥′-assoc nx ny (rR (rL p))   = rL (rR p)
≺-≈′← ∥′-assoc nx ny (rR (rR p))   = rR p
≺-≈′← ∥′-comm nx ny (rL p) = rR p
≺-≈′← ∥′-comm nx ny (rR p) = rL p
≺-≈′← (∥′-cong₁ e) nx ny (rL p) = rL (≺-≈′← e nx ny p)
≺-≈′← (∥′-cong₁ e) nx ny (rR p) = rR p
≺-≈′← (∥′-dup U) nx ny (rL p) = p
≺-≈′← (∥′-dup U) nx ny (rR p) = p
≺-≈′← (∥′-tm-; (inj₁ mc)) nx ny (mid i j) = ⊥-elim (nx (∈ₗ-mobile i mc))
≺-≈′← (∥′-tm-; (inj₂ mc)) nx ny (mid i j) = ⊥-elim (ny (∈ₗ-mobile j mc))
≺-≈′← (∥′-tm-; U) nx ny (qL p) = rL p
≺-≈′← (∥′-tm-; U) nx ny (qR p) = rR p

≺-≈← : ∀ {n} {Γ : Ctx n} {x y α β} → Γ ∶ α ≈ β → NM Γ x → NM Γ y → x ≺⟨ β ⟩ y → x ≺⟨ α ⟩ y
≺-≈← ε           nx ny p = p
≺-≈← (fwd e ◅ r) nx ny p = ≺-≈′← e nx ny (≺-≈← r nx ny p)
≺-≈← (bwd e ◅ r) nx ny p = ≺-≈′→ e nx ny (≺-≈← r nx ny p)

------------------------------------------------------------------------
-- THE CORE: strict `;`-precedence of two NON-Mobile channels transports
-- BACKWARD along `_≼_`.  (`≼-wk` only drops order; `≼-∅` needs a leaf of
-- an all-Unr side; the `≈` step uses `≺-≈←`.)
------------------------------------------------------------------------

≺⇒∈ₗ : ∀ {n} {x y : 𝔽 n} {γ} → x ≺⟨ γ ⟩ y → x ∈ₗ γ
≺⇒∈ₗ (mid i _) = sL i
≺⇒∈ₗ (qL p) = sL (≺⇒∈ₗ p)
≺⇒∈ₗ (qR p) = sR (≺⇒∈ₗ p)
≺⇒∈ₗ (rL p) = pL (≺⇒∈ₗ p)
≺⇒∈ₗ (rR p) = pR (≺⇒∈ₗ p)

≺-antitone : ∀ {n} {Γ : Ctx n} {x y α β}
  → Γ ∶ α ≼ β → NM Γ x → NM Γ y → x ≺⟨ β ⟩ y → x ≺⟨ α ⟩ y
≺-antitone (≼-refl e)     nx ny p = ≺-≈← e nx ny p
≺-antitone (≼-∅ U)        nx ny p = ⊥-elim (nx (unr⇒mobile (∈ₗ-unr (≺⇒∈ₗ p) U)))
≺-antitone ≼-wk           nx ny (rL (mid i j)) = mid (pL i) (pL j)
≺-antitone ≼-wk           nx ny (rL (qL p))    = qL (rL p)
≺-antitone ≼-wk           nx ny (rL (qR p))    = qR (rL p)
≺-antitone ≼-wk           nx ny (rR (mid i j)) = mid (pR i) (pR j)
≺-antitone ≼-wk           nx ny (rR (qL p))    = qL (rR p)
≺-antitone ≼-wk           nx ny (rR (qR p))    = qR (rR p)
≺-antitone (≼-trans p q)  nx ny r = ≺-antitone p nx ny (≺-antitone q nx ny r)
≺-antitone (≼-cong-; p q) nx ny (mid i j) = mid (∈ₗ-≼ p nx i) (∈ₗ-≼ q ny j)
≺-antitone (≼-cong-; p q) nx ny (qL r)    = qL (≺-antitone p nx ny r)
≺-antitone (≼-cong-; p q) nx ny (qR r)    = qR (≺-antitone q nx ny r)
≺-antitone (≼-cong-∥ p q) nx ny (rL r)    = rL (≺-antitone p nx ny r)
≺-antitone (≼-cong-∥ p q) nx ny (rR r)    = rR (≺-antitone q nx ny r)

------------------------------------------------------------------------
-- COROLLARY.  An all-parallel body of single-channel leaves (any bare
-- `send`/`recv`/thread composition — `send·(msg⊗handle)` builds `msg ∥
-- handle`, threads compose by `∥`, no thread SEQUENCES two channels) has
-- NO strict precedence at all.  So it cannot `≼` any structure that
-- `;`-orders two NON-Mobile channels — in particular `structBinder B₁`,
-- which sequences the block's `mid` (the intervening ⟨acq⟩) before the
-- msg handle `h`.  Hence NO bare-send com preimage is well-typed.
------------------------------------------------------------------------

no-≺-∥leaves : ∀ {n} {x y : 𝔽 n} {a b c} → ¬ (x ≺⟨ (` a ∥ ` b) ∥ ` c ⟩ y)
no-≺-∥leaves (rL (rL ()))
no-≺-∥leaves (rL (rR ()))
no-≺-∥leaves (rR ())

bareSend-¬≼ : ∀ {n} {Γ : Ctx n} {x y a b c γ}
  → NM Γ x → NM Γ y → x ≺⟨ γ ⟩ y
  → ¬ ( Γ ∶ ((` a ∥ ` b) ∥ ` c) ≼ γ )
bareSend-¬≼ nx ny x≺γ le = no-≺-∥leaves (≺-antitone le nx ny x≺γ)

------------------------------------------------------------------------
-- CONCRETE.  Over the canonical separated-com bind context
-- `⟨acq;ret⟩ , ⟨acq⟩ , ⟨msg ‼ ⊤⟩` (mobile front 0F, intervening ⟨acq⟩ 1F,
-- msg handle 2F), NEITHER bare-send arrangement is `≼` the sequential
-- send-side binder `` ` 0F ; ` 1F ; ` 2F ``:
--   crux-A  — separate acq-thread: body `(` 0F ∥ ` 2F) ∥ ` 1F`;
--   crux-B  — send-then-acq in one thread: body `(` 0F ∥ ` 2F) ; ` 1F`.
-- Both need `1F ≺ 2F` (holds in the binder), refuted by `≺-antitone` since
-- 1F (⟨acq⟩, ¬mobile-acq) and 2F (⟨msg⟩, ¬mobile-noAcq) are non-Mobile.
------------------------------------------------------------------------

private
  Γc : Ctx 3
  Γc = ⟨ acq ; ret ⟩ ∷ ⟨ acq ⟩ ∷ ⟨ msg ‼ `⊤ ⟩ ∷ []

  nm1 : NM Γc 1F
  nm1 = ¬mobile-acq

  nm2 : NM Γc 2F
  nm2 = ¬mobile-noAcq NoAcq.msg

  binder : Struct 3
  binder = (` 0F) ; ((` 1F) ; (` 2F))

  1≺2 : 1F ≺⟨ binder ⟩ 2F
  1≺2 = qR (mid here here)

-- Arrangement A (bare send, separate acq-thread) is not well-typed.
crux-A : ¬ ( Γc ∶ (((` 0F) ∥ (` 2F)) ∥ (` 1F)) ≼ binder )
crux-A = bareSend-¬≼ nm1 nm2 1≺2

-- Arrangement B (send-then-acq in one thread) is not well-typed either.
crux-B : ¬ ( Γc ∶ (((` 0F) ∥ (` 2F)) ; (` 1F)) ≼ binder )
crux-B le with ≺-antitone le nm1 nm2 1≺2
... | mid _ ()
... | qL (rL ())
... | qL (rR ())
... | qR ()
