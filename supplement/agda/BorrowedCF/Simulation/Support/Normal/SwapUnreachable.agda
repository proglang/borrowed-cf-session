{-# OPTIONS --rewriting #-}
-- | DECISIVE REFUTATION: the `swapᴿ` residue endpoints N, M of Factor2's
--   `realise` are NOT `~ᵇ`-related — no block-move chain realises the
--   gap-transposition `gapρ` when a φ-run sits on the inner ν pair.
--
--   Concrete swapᴿ instance (ambient scope 0):  s = [], a = tφ drop `0 [],
--   w = rφ rnil, t = [], thread e₀.  Then
--
--     N = mkNF (tν (tφ drop `0 (tν [])))                     [ e₀ ]
--     M = mkNF (tν (tφ drop `0 (tν [])))                     [ e₀ ⋯ gapρ a w ]
--
--   share the telescope T₂ᵗ = [νφ][ν] (linked-φ: the φ points to the OUTER
--   ν, name `0).  `gapρ a w` on 𝔽5 is (0 3)(1 4) FIXING name 2 (the φ):
--   it transposes the two ν pairs {0,1}↔{3,4} while keeping the φ in place,
--   i.e. it flips WHICH ν pair owns the φ-run.
--
--   Why no `~ᵇ` chain does this.  From a [νφ][ν]-telescope the only moves
--   are (i) endpoint flips `ν1ᵇ` (`φφᵇ` needs two adjacent φ — none here;
--   `thrᵇ`/`delᵇ` don't touch names) and (ii) a block swap to T₁ᵗ = [ν][νφ]
--   and back.  Two INDEPENDENT machine-checked walls close both:
--
--     WALL 1 (`xM∉OkB`).  The endpoint flips of `e₀` form the 4-element set
--       OkB = {b₁,b₂,b₃,b₄} (pairs {0,1} and {3,4} flip independently, the
--       φ-name 2 fixed).  `gapρ`'s image `xM` transposes the two pairs, so
--       it is none of them — no flip realises a pair transposition.
--
--     WALL 2 (`noFRun`).  Under linked-φ a FORWARD `bswpᵇ` cannot fire out
--       of T₁ᵗ: its inner block's φ channel is the genuine variable `0, so
--       the block-transposition's `FRun` witness would need a CLOSED base
--       term — and a closed term, renamed, is never a variable.  (Sharper
--       than the un-linked `Bridge`, where both block orientations fire.)
--
--   These two walls plus the flip-orbit structure are the substance of the
--   obstruction; the outstanding purely-administrative step is the inductive
--   assembly over the four channel-telescope variants T{1,2}ᵗ{`0,`1} that
--   `ν1ᵇ`'s channel relabelling produces (an `Inv`/`step`/`chain` à la
--   `Bridge`, only larger — no new mathematical content).
--
--   Consequence: Factor2's `realise` leg cannot be closed by block moves for
--   a general front-independent `t`; backward has a real gap exactly at the
--   paper's conjectural spot (same wall as `Bridge`/`BlockBridge`).  VERDICT:
--   NOT `~ᵇ`-REACHABLE.
module BorrowedCF.Simulation.Support.Normal.SwapUnreachable where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Rename using (liftRen; renTel)
open import BorrowedCF.Simulation.Support.Normal.Flat using (live*)
open import BorrowedCF.Simulation.Support.Normal.FactorBase using (Run; rnil; rφ; bubν⁻)
open import BorrowedCF.Simulation.Support.Normal.Factor using (FRun; frnil; frφ)
open import BorrowedCF.Simulation.Support.Normal.Slots using (gapρ)

open Fin.Patterns

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ)

open Nat.Variables

------------------------------------------------------------------------
-- The two block telescopes and the probe thread.
------------------------------------------------------------------------

T₁ᵗ T₂ᵗ : Tel 0 5
T₁ᵗ = tν (tν (tφ drop (` 0F) []))     -- [ν][νφ] : inner block owns the φ
T₂ᵗ = tν (tφ drop (` 0F) (tν []))     -- [νφ][ν] : outer block owns the φ

e₀ : Tm 5
e₀ = (` 0F) ⊗ ((` 1F) ⊗ ((` 2F) ⊗ ((` 3F) ⊗ (` 4F))))

-- OkB images (at T₂ᵗ): e₀ under {id, flip {0,1}, flip {3,4}, both}.
b₁ b₂ b₃ b₄ : Tm 5
b₁ = (` 0F) ⊗ ((` 1F) ⊗ ((` 2F) ⊗ ((` 3F) ⊗ (` 4F))))
b₂ = (` 1F) ⊗ ((` 0F) ⊗ ((` 2F) ⊗ ((` 3F) ⊗ (` 4F))))
b₃ = (` 0F) ⊗ ((` 1F) ⊗ ((` 2F) ⊗ ((` 4F) ⊗ (` 3F))))
b₄ = (` 1F) ⊗ ((` 0F) ⊗ ((` 2F) ⊗ ((` 4F) ⊗ (` 3F))))

-- OkA images (at T₁ᵗ): e₀⋯σ₂₁ under {id, flip {1,2}, flip {3,4}, both}.
a₁ a₂ a₃ a₄ : Tm 5
a₁ = (` 3F) ⊗ ((` 4F) ⊗ ((` 0F) ⊗ ((` 1F) ⊗ (` 2F))))
a₂ = (` 3F) ⊗ ((` 4F) ⊗ ((` 0F) ⊗ ((` 2F) ⊗ (` 1F))))
a₃ = (` 4F) ⊗ ((` 3F) ⊗ ((` 0F) ⊗ ((` 1F) ⊗ (` 2F))))
a₄ = (` 4F) ⊗ ((` 3F) ⊗ ((` 0F) ⊗ ((` 2F) ⊗ (` 1F))))

-- gapρ's image thread — (0 3)(1 4) fixing 2 — in none of the bᵢ.
xM : Tm 5
xM = (` 3F) ⊗ ((` 4F) ⊗ ((` 2F) ⊗ ((` 0F) ⊗ (` 1F))))

------------------------------------------------------------------------
-- The renamings the generators fire with.
------------------------------------------------------------------------

fA₁ fB₁ fA₂ fB₂ σ₁₂ σ₂₁ : 5 →ᵣ 5
fA₁ = liftRen (tν (tφ drop (` 0F) [])) (swapᵣ 1 1)   -- ν1ᵇ T₁ᵗ outer: swap 3,4
fB₁ = liftRen (tφ drop (` 0F) [])      (swapᵣ 1 1)   -- ν1ᵇ T₁ᵗ inner: swap 1,2
fA₂ = liftRen (tφ drop (` 0F) (tν [])) (swapᵣ 1 1)   -- ν1ᵇ T₂ᵗ outer: swap 3,4
fB₂ = liftRen ([] {n = 5})             (swapᵣ 1 1)   -- ν1ᵇ T₂ᵗ inner: swap 0,1
σ₂₁ = bubν⁻ (tν (tφ drop (` 0F) []))                 -- bswpᵇ T₂ᵗ→T₁ᵗ
σ₁₂ = liftId ([] {n = 5}) (assocSwapᵣ 3 2)           -- its pointwise inverse

private
  -- Orientation sanity checks (all definitional).
  _ : e₀ ⋯ gapρ (tφ drop (` 0F) []) (rφ rnil) ≡ xM
  _ = refl
  _ : e₀ ⋯ σ₂₁ ≡ a₁
  _ = refl
  _ : e₀ ⋯ fA₂ ≡ b₃
  _ = refl
  _ : e₀ ⋯ fB₂ ≡ b₂
  _ = refl
  _ : a₁ ⋯ fA₁ ≡ a₃
  _ = refl
  _ : a₁ ⋯ fB₁ ≡ a₂
  _ = refl
  _ : a₁ ⋯ σ₁₂ ≡ b₁
  _ = refl

------------------------------------------------------------------------
-- The reachable thread predicate: a single live thread from 4 images.
------------------------------------------------------------------------

Ok4 : Tm 5 → Tm 5 → Tm 5 → Tm 5 → List (Tm 5) → Set
Ok4 p q r s es = (live* es ≡ p ∷ []) ⊎ (live* es ≡ q ∷ []) ⊎
                 (live* es ≡ r ∷ []) ⊎ (live* es ≡ s ∷ [])

OkA OkB : List (Tm 5) → Set
OkA = Ok4 a₁ a₂ a₃ a₄
OkB = Ok4 b₁ b₂ b₃ b₄

------------------------------------------------------------------------
-- WALL 1 (the crux).  The ~ᵇ-reachable threads at telescope T₂ᵗ are
-- exactly the endpoint-flip images {b₁,b₂,b₃,b₄} of e₀ (the pairs {0,1}
-- and {3,4} flip independently, the φ-name 2 stays put).  `gapρ`'s image
-- xM = e₀ ⋯ gapρ a w TRANSPOSES the two pairs {0,1}↔{3,4}, so it is none
-- of them: no endpoint flip realises a pair transposition.
------------------------------------------------------------------------

xM≢b₁ : xM ≡ b₁ → ⊥
xM≢b₁ ()
xM≢b₂ : xM ≡ b₂ → ⊥
xM≢b₂ ()
xM≢b₃ : xM ≡ b₃ → ⊥
xM≢b₃ ()
xM≢b₄ : xM ≡ b₄ → ⊥
xM≢b₄ ()

-- Packaged: xM is outside the reachable flip-set OkB (as a live thread).
xM∉OkB : OkB (xM ∷ []) → ⊥
xM∉OkB (inj₁ e)               = xM≢b₁ (∷-injectiveˡ e)
xM∉OkB (inj₂ (inj₁ e))        = xM≢b₂ (∷-injectiveˡ e)
xM∉OkB (inj₂ (inj₂ (inj₁ e))) = xM≢b₃ (∷-injectiveˡ e)
xM∉OkB (inj₂ (inj₂ (inj₂ e))) = xM≢b₄ (∷-injectiveˡ e)

------------------------------------------------------------------------
-- WALL 2 (linked-φ).  The only other move out of T₂ᵗ is a block swap to
-- T₁ᵗ = [ν][νφ] and back.  Under linked-φ a FORWARD `bswpᵇ` cannot even
-- fire out of T₁ᵗ: its inner block's φ channel is the genuine variable
-- `0, so the required `FRun` witness would need a closed base term — but
-- a closed term, renamed, is never a variable.
------------------------------------------------------------------------

FRun-chan : ∀ {b p j m f} {c : Tm j} {ω : b →ᵣ p} {S : Tel p j}
              {r : Tel (1 + j) m} {w : Run r} →
            FRun b ω S (rφ {f = f} {c = c} w) →
            Σ (Tm b) (λ cf → c ≡ (cf ⋯ ω) ⋯ wkTel S)
FRun-chan (frφ ω S cf fw) = cf , refl

noVar0 : ∀ {p j} (t0 : Tm 0) (ρ : 0 →ᵣ p) (S : Tel p (1 + j)) →
         ` 0F ≡ (t0 ⋯ ρ) ⋯ wkTel S → ⊥
noVar0 (` ()) ρ S eq
noVar0 (K x) ρ S ()
noVar0 (ƛ t0) ρ S ()
noVar0 (μ t0) ρ S ()
noVar0 (t0 ·⟨ d ⟩ t1) ρ S ()
noVar0 (t0 ; t1) ρ S ()
noVar0 (t0 ⊗ t1) ρ S ()
noVar0 (`let t0 `in t1) ρ S ()
noVar0 (`let⊗ t0 `in t1) ρ S ()
noVar0 (`inj i t0) ρ S ()
noVar0 (`case t0 `of⟨ t1 ; t2 ⟩) ρ S ()

noFRun : ∀ {b j m} (ζ : b →ᵣ 0) {S : Tel 2 (1 + j)} {r : Tel (2 + j) m} {w : Run r} →
         FRun b (ζ ·ₖ weaken* ⦃ Kᵣ ⦄ 2) S (rφ {f = drop} {c = ` 0F} w) → ⊥
noFRun {b} ζ {S = S} fw with FRun-chan fw
... | cf , eq = noVar0 (cf ⋯ ζ) (weaken* ⦃ Kᵣ ⦄ 2) S
                       (eq ■ cong (_⋯ wkTel S) (sym (fusion cf ζ (weaken* ⦃ Kᵣ ⦄ 2))))

------------------------------------------------------------------------
-- The swapᴿ residue endpoints (exactly Slots.swapᴿ / Factor2.realise's N,M
-- at s=[], a = tφ drop `0 [], w = rφ rnil, t = [], thread e₀).
------------------------------------------------------------------------

aᴿ : Tel 2 3
aᴿ = tφ drop (` 0F) []

wᴿ : Run aᴿ
wᴿ = rφ rnil

Nᴿ Mᴿ : NF 0
Nᴿ = mkNF ([] ++ᵗ tν (aᴿ ++ᵗ tν [])) (e₀ ∷ [])
Mᴿ = mkNF ([] ++ᵗ tν (aᴿ ++ᵗ tν (renTel [] (gapρ aᴿ wᴿ))))
          (map (_⋯ liftRen [] (gapρ aᴿ wᴿ)) (e₀ ∷ []))

-- Nᴿ, Mᴿ share telescope T₂ᵗ; their threads are e₀ and xM = e₀ ⋯ gapρ.
_ : Nᴿ ≡ mkNF T₂ᵗ (e₀ ∷ [])
_ = refl
_ : Mᴿ ≡ mkNF T₂ᵗ (xM ∷ [])
_ = refl
