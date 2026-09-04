-- | Phase 5.0 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §12.2, P5.0): SYNTACTIC THREAD TRACKING.
--
--   `Canonical.agda` rearranges a typed process with `_≋_` until the redex
--   thread sits where the typed reduction rules can fire.  The backward
--   proof must know WHICH soup slot the rearranged thread ends up in: a
--   well-typed process may contain several threads with identical soup
--   content, so no content-based or counting argument recovers the slot
--   from a black-box transport of the image (`PLAN.md` §12.1).
--
--   This module makes the correspondence syntactic.  `Tracks′ s a b` says
--   that the single congruence AXIOM `s : P ≋′ Q` carries the thread `a` of
--   `P` to the thread `b` of `Q`; `Tracks d a b` iterates this along a whole
--   `_≋_` derivation `d`.  Both are inductive families indexed by the
--   derivation, so they are preserved by every combinator `Canonical.agda`
--   uses: `_◅◅_` (`tracks-◅◅`), `≋-sym` (`tracks-sym`), `≡→≋`
--   (`tracks-≡→≋`), `subst` (`tracks-subst`, `tracks-substˡ`), `ν-cong`
--   (`tracks-gmap-ν`), `∥-cong` (`tracks-∥-cong-l`, `tracks-∥-cong-r`) and
--   `≋-plug` (`tracks-≋-plug`), plus the per-axiom instances
--   (`tracks-∥-comm-l/r`, `tracks-∥-assoc`, `tracks-∥-unitˡ/ʳ`,
--   `tracks-ν-swap′`, `tracks-ν-comm′`, `tracks-ν-ext′`).
--
--   The unit thread of `∥-unit′` is the only thread that is NOT tracked: it
--   disappears.  Every other axiom is a bijection on threads, realised by
--   `_↑ˡ_` / `_↑ʳ_` injections, `Fin.cast` along `+-assoc`, or `Fin.cast`
--   along `processCount-rename` (the renaming axioms `ν-swap′`, `ν-comm′`
--   and `ν-ext′` keep every thread where it is, but `processCount` of a
--   renamed process is not definitionally the original count).
--
--   Phase 5.1 (`TracksImage.agda`) proves that the forward image transport
--   `≋-image` respects `Tracks`; this module is deliberately free of any
--   image or soup machinery beyond what `Locate.agda` already pulls in.
module BorrowedCF.Simulation.BackwardSoup.Tracks where

open import Data.Nat.ListAction using (sum)

import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
  using (_◅_; _◅◅_) renaming (ε to ≋-refl)
open import Relation.Binary.Construct.Closure.Symmetric as Sym using (fwd; bwd)

open import BorrowedCF.Prelude

open import BorrowedCF.Terms using (Kᵣ; weaken*; swapᵣ; assocSwapᵣ)

import BorrowedCF.Processes.Typed as 𝐓
import BorrowedCF.Processes.TranslationSoup as Translation

open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (processCount-rename)
open import BorrowedCF.Simulation.BackwardSoup.Locate
  using ( ProcessContext; hole; par-left; par-right; bind
        ; plug; threadInContext; ≋-sym; ≡→≋; ≋-plug)

open 𝐓 using (BindGroup)

open Translation using () renaming (processCount to pc)

open Nat.Variables

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- 1.  Tracking through a single congruence AXIOM.
--
-- One constructor per axiom and, where the axiom permutes two blocks of
-- threads, one per block.  The indices are the source and the target thread.

data Tracks′ {n : ℕ} :
     {P Q : 𝐓.Proc n} (s : P 𝐓.≋′ Q) → 𝔽 (pc P) → 𝔽 (pc Q) → Set where

  -- `∥-comm′ : P ∥ Q ≋′ Q ∥ P`
  comm-l :
    {P Q : 𝐓.Proc n} (i : 𝔽 (pc P)) →
    Tracks′ (𝐓.∥-comm′ {P = P} {Q = Q}) (i ↑ˡ pc Q) (pc Q ↑ʳ i)
  comm-r :
    {P Q : 𝐓.Proc n} (j : 𝔽 (pc Q)) →
    Tracks′ (𝐓.∥-comm′ {P = P} {Q = Q}) (pc P ↑ʳ j) (j ↑ˡ pc P)

  -- `∥-assoc′ : P₁ ∥ (P₂ ∥ P₃) ≋′ (P₁ ∥ P₂) ∥ P₃`
  assoc :
    {P₁ P₂ P₃ : 𝐓.Proc n} (i : 𝔽 (pc P₁ + (pc P₂ + pc P₃))) →
    Tracks′ (𝐓.∥-assoc′ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃})
      i (Fin.cast (sym (+-assoc (pc P₁) (pc P₂) (pc P₃))) i)

  -- `∥-unit′ : ⟪ K `unit ⟫ ∥ P ≋′ P`.  The unit thread `0F` is UNTRACKED.
  unit :
    {P : 𝐓.Proc n} (i : 𝔽 (pc P)) →
    Tracks′ (𝐓.∥-unit′ {P = P}) (suc i) i

  -- `ν-swap′ : ν B₁ B₂ P ≋′ ν B₂ B₁ (P ⋯ₚ swapᵣ (sum B₁) (sum B₂))`
  swap-ν :
    {B₁ B₂ : BindGroup} {P : 𝐓.Proc (sum B₁ + sum B₂ + n)} (i : 𝔽 (pc P)) →
    Tracks′ (𝐓.ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P})
      i (Fin.cast (sym (processCount-rename P (swapᵣ (sum B₁) (sum B₂)))) i)

  -- `ν-comm′ : ν B₁ B₂ (ν A₁ A₂ P) ≋′
  --            ν A₁ A₂ (ν B₁ B₂ (P ⋯ₚ assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))`
  comm-ν :
    {B₁ B₂ A₁ A₂ : BindGroup}
    {P : 𝐓.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n))} (i : 𝔽 (pc P)) →
    Tracks′ (𝐓.ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P})
      i (Fin.cast
           (sym (processCount-rename P
                   (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))) i)

  -- `ν-ext′ : P ∥ ν B₁ B₂ Q ≋′
  --           ν B₁ B₂ ((P ⋯ₚ weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂)) ∥ Q)`
  ext-ν :
    {P : 𝐓.Proc n} {B₁ B₂ : BindGroup} {Q : 𝐓.Proc (sum B₁ + sum B₂ + n)}
    (i : 𝔽 (pc P + pc Q)) →
    Tracks′ (𝐓.ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂} {Q = Q})
      i (Fin.cast
           (cong (_+ pc Q)
             (sym (processCount-rename P
                     (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂))))) i)

  -- `∥-cong′ : P₁ ≋′ P₂ → P₁ ∥ Q ≋′ P₂ ∥ Q`
  cong-l :
    {P₁ P₂ Q : 𝐓.Proc n} {s : P₁ 𝐓.≋′ P₂}
    {a : 𝔽 (pc P₁)} {b : 𝔽 (pc P₂)} →
    Tracks′ s a b →
    Tracks′ (𝐓.∥-cong′ {Q = Q} s) (a ↑ˡ pc Q) (b ↑ˡ pc Q)
  cong-r :
    {P₁ P₂ Q : 𝐓.Proc n} {s : P₁ 𝐓.≋′ P₂} (j : 𝔽 (pc Q)) →
    Tracks′ (𝐓.∥-cong′ {Q = Q} s) (pc P₁ ↑ʳ j) (pc P₂ ↑ʳ j)

  -- `ν-cong′ : P ≋′ Q → ν B₁ B₂ P ≋′ ν B₁ B₂ Q`
  cong-ν :
    {B₁ B₂ : BindGroup} {P Q : 𝐓.Proc (sum B₁ + sum B₂ + n)}
    {s : P 𝐓.≋′ Q} {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
    Tracks′ s a b →
    Tracks′ (𝐓.ν-cong′ {B₁ = B₁} {B₂ = B₂} s) a b

------------------------------------------------------------------------
-- 2.  Tracking through the equivalence closure.
--
-- `_≋_` is `Star (SymClosure _≋′_)`, so a derivation is a list of steps that
-- are each used FORWARDS or BACKWARDS.  A backward step transports a thread
-- against the direction of its axiom, which is why `track-bwd` takes its
-- `Tracks′` with the two indices exchanged.

data Tracks {n : ℕ} :
     {P Q : 𝐓.Proc n} (d : P 𝐓.≋ Q) → 𝔽 (pc P) → 𝔽 (pc Q) → Set where

  track-ε :
    {P : 𝐓.Proc n} (a : 𝔽 (pc P)) → Tracks {P = P} ≋-refl a a

  track-fwd :
    {P M Q : 𝐓.Proc n} {s : P 𝐓.≋′ M} {d : M 𝐓.≋ Q}
    {a : 𝔽 (pc P)} {b : 𝔽 (pc M)} {c : 𝔽 (pc Q)} →
    Tracks′ s a b → Tracks d b c → Tracks (fwd s ◅ d) a c

  track-bwd :
    {P M Q : 𝐓.Proc n} {s : M 𝐓.≋′ P} {d : M 𝐓.≋ Q}
    {a : 𝔽 (pc P)} {b : 𝔽 (pc M)} {c : 𝔽 (pc Q)} →
    Tracks′ s b a → Tracks d b c → Tracks (bwd s ◅ d) a c

------------------------------------------------------------------------
-- 3.  The algebra of `Tracks`.

-- Concatenation.
tracks-◅◅ :
  {P M Q : 𝐓.Proc n} {d₁ : P 𝐓.≋ M} {d₂ : M 𝐓.≋ Q}
  {a : 𝔽 (pc P)} {b : 𝔽 (pc M)} {c : 𝔽 (pc Q)} →
  Tracks d₁ a b → Tracks d₂ b c → Tracks (d₁ ◅◅ d₂) a c
tracks-◅◅ (track-ε a) t₂ = t₂
tracks-◅◅ (track-fwd s t₁) t₂ = track-fwd s (tracks-◅◅ t₁ t₂)
tracks-◅◅ (track-bwd s t₁) t₂ = track-bwd s (tracks-◅◅ t₁ t₂)

-- Single steps.
tracks-fwd₁ :
  {P Q : 𝐓.Proc n} {s : P 𝐓.≋′ Q} {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks′ s a b → Tracks (fwd s ◅ ≋-refl) a b
tracks-fwd₁ s = track-fwd s (track-ε _)

tracks-bwd₁ :
  {P Q : 𝐓.Proc n} {s : Q 𝐓.≋′ P} {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks′ s b a → Tracks (bwd s ◅ ≋-refl) a b
tracks-bwd₁ s = track-bwd s (track-ε _)

-- `Eq*.return s` is `fwd s ◅ ε`.
tracks-return :
  {P Q : 𝐓.Proc n} {s : P 𝐓.≋′ Q} {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks′ s a b → Tracks (Eq*.return {R = 𝐓._≋′_} s) a b
tracks-return s = track-fwd s (track-ε _)

-- Symmetry.  `Eq*.symmetric` is `Star.reverse (Sym.symmetric _)`, i.e.
-- `Star.revApp (Sym.symmetric _) d ε`, so the general statement is the one
-- for `revApp`.
tracks-revApp :
  {P Q R : 𝐓.Proc n} {d : Q 𝐓.≋ P} {e : Q 𝐓.≋ R}
  {a : 𝔽 (pc Q)} {b : 𝔽 (pc P)} {c : 𝔽 (pc R)} →
  Tracks d a b → Tracks e a c →
  Tracks (Star.revApp (Sym.symmetric 𝐓._≋′_) d e) b c
tracks-revApp (track-ε a) te = te
tracks-revApp (track-fwd s td) te = tracks-revApp td (track-bwd s te)
tracks-revApp (track-bwd s td) te = tracks-revApp td (track-fwd s te)

tracks-sym :
  {P Q : 𝐓.Proc n} {d : P 𝐓.≋ Q} {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks d a b → Tracks (≋-sym d) b a
tracks-sym {a = a} t = tracks-revApp t (track-ε a)

-- Rewriting the two indices.
tracks-cast :
  {P Q : 𝐓.Proc n} {d : P 𝐓.≋ Q} {a a′ : 𝔽 (pc P)} {b b′ : 𝔽 (pc Q)} →
  Tracks d a b → a ≡ a′ → b ≡ b′ → Tracks d a′ b′
tracks-cast t refl refl = t

-- The reflexive derivation of a process EQUATION transports the thread
-- along that equation.
tracks-≡→≋ :
  {P Q : 𝐓.Proc n} (eq : P ≡ Q) (a : 𝔽 (pc P)) →
  Tracks (≡→≋ eq) a (subst (λ R → 𝔽 (pc R)) eq a)
tracks-≡→≋ refl a = track-ε a

-- `Canonical.agda` fixes up the RIGHT-hand side of a derivation with
-- `subst (λ z → L ≋ R z) eq`; the thread moves along the same equation.
tracks-subst :
  {X : Set ℓ} {x y : X} (eq : x ≡ y)
  {L : 𝐓.Proc n} {R : X → 𝐓.Proc n} {d : L 𝐓.≋ R x}
  {a : 𝔽 (pc L)} {b : 𝔽 (pc (R x))} →
  Tracks d a b →
  Tracks (subst (λ z → L 𝐓.≋ R z) eq d) a (subst (λ z → 𝔽 (pc (R z))) eq b)
tracks-subst refl t = t

tracks-substˡ :
  {X : Set ℓ} {x y : X} (eq : x ≡ y)
  {L : X → 𝐓.Proc n} {R : 𝐓.Proc n} {d : L x 𝐓.≋ R}
  {a : 𝔽 (pc (L x))} {b : 𝔽 (pc R)} →
  Tracks d a b →
  Tracks (subst (λ z → L z 𝐓.≋ R) eq d) (subst (λ z → 𝔽 (pc (L z))) eq a) b
tracks-substˡ refl t = t

------------------------------------------------------------------------
-- 4.  The congruences.

-- `𝐓.ν-cong = Eq*.gmap (ν _ _) ν-cong′`: the thread index is untouched.
tracks-gmap-ν :
  {B₁ B₂ : BindGroup} {P Q : 𝐓.Proc (sum B₁ + sum B₂ + n)} {d : P 𝐓.≋ Q}
  {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks d a b → Tracks (𝐓.ν-cong {B₁ = B₁} {B₂ = B₂} d) a b
tracks-gmap-ν (track-ε a) = track-ε a
tracks-gmap-ν (track-fwd s t) = track-fwd (cong-ν s) (tracks-gmap-ν t)
tracks-gmap-ν (track-bwd s t) = track-bwd (cong-ν s) (tracks-gmap-ν t)

-- The left half of `𝐓.∥-cong`: `Eq*.gmap (_∥ Q) ∥-cong′`.
∥-congᴳ :
  {P₁ P₂ Q : 𝐓.Proc n} → P₁ 𝐓.≋ P₂ → (P₁ 𝐓.∥ Q) 𝐓.≋ (P₂ 𝐓.∥ Q)
∥-congᴳ {Q = Q} = Eq*.gmap (𝐓._∥ Q) 𝐓.∥-cong′

tracks-gmap-∥ˡ :
  {P₁ P₂ Q : 𝐓.Proc n} {d : P₁ 𝐓.≋ P₂} {a : 𝔽 (pc P₁)} {b : 𝔽 (pc P₂)} →
  Tracks d a b →
  Tracks (∥-congᴳ {Q = Q} d) (a ↑ˡ pc Q) (b ↑ˡ pc Q)
tracks-gmap-∥ˡ (track-ε a) = track-ε _
tracks-gmap-∥ˡ (track-fwd s t) = track-fwd (cong-l s) (tracks-gmap-∥ˡ t)
tracks-gmap-∥ˡ (track-bwd s t) = track-bwd (cong-l s) (tracks-gmap-∥ˡ t)

tracks-gmap-∥ʳ :
  {P₁ P₂ Q : 𝐓.Proc n} (d : P₁ 𝐓.≋ P₂) (j : 𝔽 (pc Q)) →
  Tracks (∥-congᴳ {Q = Q} d) (pc P₁ ↑ʳ j) (pc P₂ ↑ʳ j)
tracks-gmap-∥ʳ ≋-refl j = track-ε _
tracks-gmap-∥ʳ (fwd s ◅ d) j = track-fwd (cong-r j) (tracks-gmap-∥ʳ d j)
tracks-gmap-∥ʳ (bwd s ◅ d) j = track-bwd (cong-r j) (tracks-gmap-∥ʳ d j)

------------------------------------------------------------------------
-- 5.  The derived combinators of `Processes/Typed.agda`.

tracks-∥-comm-l :
  {P Q : 𝐓.Proc n} (i : 𝔽 (pc P)) →
  Tracks (𝐓.∥-comm {P = P} {Q = Q}) (i ↑ˡ pc Q) (pc Q ↑ʳ i)
tracks-∥-comm-l i = track-fwd (comm-l i) (track-ε _)

tracks-∥-comm-r :
  {P Q : 𝐓.Proc n} (j : 𝔽 (pc Q)) →
  Tracks (𝐓.∥-comm {P = P} {Q = Q}) (pc P ↑ʳ j) (j ↑ˡ pc P)
tracks-∥-comm-r j = track-fwd (comm-r j) (track-ε _)

tracks-∥-assoc :
  {P₁ P₂ P₃ : 𝐓.Proc n} (i : 𝔽 (pc P₁ + (pc P₂ + pc P₃))) →
  Tracks (𝐓.∥-assoc {P₁ = P₁} {P₂ = P₂} {P₃ = P₃})
    i (Fin.cast (sym (+-assoc (pc P₁) (pc P₂) (pc P₃))) i)
tracks-∥-assoc i = track-fwd (assoc i) (track-ε _)

tracks-∥-unitˡ :
  {P : 𝐓.Proc n} (i : 𝔽 (pc P)) → Tracks (𝐓.∥-unitˡ {P = P}) (suc i) i
tracks-∥-unitˡ i = track-fwd (unit i) (track-ε _)

-- `pc (P ∥ ⟪ K `unit ⟫)` is `pc P + 1`.
tracks-∥-unitʳ :
  {P : 𝐓.Proc n} (i : 𝔽 (pc P)) → Tracks (𝐓.∥-unitʳ {P = P}) (i ↑ˡ 1) i
tracks-∥-unitʳ i = tracks-◅◅ (tracks-∥-comm-l i) (tracks-∥-unitˡ i)

-- The single `fwd` steps as `Canonical.agda` writes them.
tracks-ν-swap′ :
  {B₁ B₂ : BindGroup} {P : 𝐓.Proc (sum B₁ + sum B₂ + n)} (i : 𝔽 (pc P)) →
  Tracks (fwd (𝐓.ν-swap′ {B₁ = B₁} {B₂ = B₂} {P = P}) ◅ ≋-refl)
    i (Fin.cast (sym (processCount-rename P (swapᵣ (sum B₁) (sum B₂)))) i)
tracks-ν-swap′ i = track-fwd (swap-ν i) (track-ε _)

tracks-ν-comm′ :
  {B₁ B₂ A₁ A₂ : BindGroup}
  {P : 𝐓.Proc (sum A₁ + sum A₂ + (sum B₁ + sum B₂ + n))} (i : 𝔽 (pc P)) →
  Tracks
    (fwd (𝐓.ν-comm′ {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P}) ◅ ≋-refl)
    i (Fin.cast
         (sym (processCount-rename P
                 (assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂)))) i)
tracks-ν-comm′ i = track-fwd (comm-ν i) (track-ε _)

tracks-ν-ext′ :
  {P : 𝐓.Proc n} {B₁ B₂ : BindGroup} {Q : 𝐓.Proc (sum B₁ + sum B₂ + n)}
  (i : 𝔽 (pc P + pc Q)) →
  Tracks (fwd (𝐓.ν-ext′ {P = P} {B₁ = B₁} {B₂ = B₂} {Q = Q}) ◅ ≋-refl)
    i (Fin.cast
         (cong (_+ pc Q)
           (sym (processCount-rename P
                   (weaken* ⦃ Kᵣ ⦄ (sum B₁ + sum B₂))))) i)
tracks-ν-ext′ i = track-fwd (ext-ν i) (track-ε _)

-- `𝐓.∥-cong ps qs` is
-- `gmap ∥-cong′ ps ◅◅ ∥-comm ◅◅ gmap ∥-cong′ qs ◅◅ ∥-comm`.
tracks-∥-cong-l :
  {P₁ P₂ Q₁ Q₂ : 𝐓.Proc n} {d₁ : P₁ 𝐓.≋ P₂} {d₂ : Q₁ 𝐓.≋ Q₂}
  {a : 𝔽 (pc P₁)} {b : 𝔽 (pc P₂)} →
  Tracks d₁ a b → Tracks (𝐓.∥-cong d₁ d₂) (a ↑ˡ pc Q₁) (b ↑ˡ pc Q₂)
tracks-∥-cong-l {d₂ = d₂} {b = b} t =
  tracks-◅◅ (tracks-gmap-∥ˡ t)
    (tracks-◅◅ (tracks-∥-comm-l b)
      (tracks-◅◅ (tracks-gmap-∥ʳ d₂ b) (tracks-∥-comm-r b)))

tracks-∥-cong-r :
  {P₁ P₂ Q₁ Q₂ : 𝐓.Proc n} {d₁ : P₁ 𝐓.≋ P₂} {d₂ : Q₁ 𝐓.≋ Q₂}
  {a : 𝔽 (pc Q₁)} {b : 𝔽 (pc Q₂)} →
  Tracks d₂ a b → Tracks (𝐓.∥-cong d₁ d₂) (pc P₁ ↑ʳ a) (pc P₂ ↑ʳ b)
tracks-∥-cong-r {d₁ = d₁} {a = a} t =
  tracks-◅◅ (tracks-gmap-∥ʳ d₁ a)
    (tracks-◅◅ (tracks-∥-comm-r a)
      (tracks-◅◅ (tracks-gmap-∥ˡ t) (tracks-∥-comm-l _)))

------------------------------------------------------------------------
-- 6.  `≋-plug`: a derivation inside a process context.

tracks-≋-plug :
  (c : ProcessContext k n) {P Q : 𝐓.Proc k} {d : P 𝐓.≋ Q}
  {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks d a b →
  Tracks (≋-plug c d) (threadInContext c P a) (threadInContext c Q b)
tracks-≋-plug hole t = t
tracks-≋-plug (par-left c R₀) t =
  tracks-∥-cong-l {d₂ = ≋-refl} (tracks-≋-plug c t)
tracks-≋-plug (par-right R₀ c) t =
  tracks-∥-cong-r {d₁ = ≋-refl} (tracks-≋-plug c t)
tracks-≋-plug (bind B₁ B₂ c) t = tracks-gmap-ν (tracks-≋-plug c t)
