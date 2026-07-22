-- | The image of a TYPED prenex form is an explicit BLOCK normal form.
--
--   TypedPrenex turns every typed process into a ν-telescope over flat
--   threads; Normal.Image computes the normal form of ONE translated ν-node.
--   This module iterates the latter down the former: the image's telescope is
--   a sequence of `tν`-headed BLOCKS — one per typed ν-node, each carrying
--   exactly that node's φ-cells (`Image.φTel`) — and its thread list is the
--   typed threads under the accumulated per-layer substitution `Bσ`.
--
--   Nothing here needs a new idea: each layer of the induction is exactly one
--   application of `nf-U-ν`, and the indices go through untransported because
--   `BScope` computes the inner scope the way `νImage` scopes it (`s₂` per
--   layer) rather than as a sum.  Combined with `prenex-soundᵗ` and `U-≋`,
--   every image's normal form is `~`-equal to such a block form
--   (`image-block-~`) — the shape a backward block move is stated against.
module BorrowedCF.Simulation.Support.Normal.PrenexImage where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Translation
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Image
open import BorrowedCF.Simulation.Support.Normal.Equiv using (_~_; ~-trans)
open import BorrowedCF.Simulation.Support.Normal.Sound using (≡→~; ≋⇒~)
open import BorrowedCF.Simulation.Support.Normal.Idem using (map-idᵣ)
open import BorrowedCF.Simulation.Support.Congruence using (U-≋)

import BorrowedCF.Processes.Typed as 𝐓

open import Data.List using (List; []; _∷_; _++_; map)

open Nat.Variables

------------------------------------------------------------------------
-- The image block telescope.
------------------------------------------------------------------------

-- The inner scope of the image telescope.  Each typed ν-node contributes the
-- ν's two slots plus one φ-slot per sync — accumulated as `νImage` scopes it
-- (`s₂ = syncs B₂ + (syncs B₁ + (2 + n))` per layer), so that `BTel` below
-- needs no transport.
BScope : ∀ {a b} → TTel a b → ℕ → ℕ
BScope []ᵗ           n = n
BScope (tνᵗ B₁ B₂ t) n = BScope t (syncs B₂ + (syncs B₁ + (2 + n)))

-- One `tν`-headed block per typed ν-node, carrying that node's φ-cells, in
-- source order.  The head of each block is `νImage.tel′`.
BTel : ∀ {a b} (t : TTel a b) (n : ℕ) → Tel n (BScope t n)
BTel []ᵗ           n = []
BTel (tνᵗ B₁ B₂ t) n =
  tν (φTel B₁ (2 + n) ++ᵗ φTel B₂ (syncs B₁ + (2 + n)))
    ++ᵗ BTel t (syncs B₂ + (syncs B₁ + (2 + n)))

-- The substitution accumulated down the telescope: each layer feeds its body
-- exactly the `σ′` its `nf-U-ν` instance uses.
Bσ : ∀ {a b n} (t : TTel a b) → a →ₛ n → b →ₛ BScope t n
Bσ []ᵗ           σ = σ
Bσ (tνᵗ B₁ B₂ t) σ = Bσ t (νImage.σ′ B₁ B₂ σ)

------------------------------------------------------------------------
-- The base case: a flat thread list.
------------------------------------------------------------------------

-- The typed-image analogue of Idem's `nf-pars`: `combine` on binder-free
-- normal forms degenerates to consing, because every renaming it inserts is
-- the identity.
nf-U-pars : ∀ {m n} (es : List (Tm m)) (σ : m →ₛ n) →
            nf (U[ parsᵗ es ] σ) ≡ mkNF [] (map (_⋯ σ) es ++ (K `unit ∷ []))
nf-U-pars []       σ = refl
nf-U-pars (e ∷ es) σ =
  cong (combine (mkNF [] ((e ⋯ σ) ∷ []))) (nf-U-pars es σ)
    ■ cong₂ (λ a b → mkNF [] (a ∷ b)) (⋯-id (e ⋯ σ) (λ _ → refl))
        (map-idᵣ (map (_⋯ σ) es ++ (K `unit ∷ [])))

------------------------------------------------------------------------
-- The main theorem: the image of a plugged typed telescope, on the nose.
------------------------------------------------------------------------

-- Each `tνᵗ` layer is one `nf-U-ν`; the record `NF` hides its inner scope, so
-- the induction hypothesis rewrites under `mkNF (tel′ ++ᵗ tel _) (thr _)` by a
-- plain `cong` — no transport ever appears.
nf-prenex-image :
  ∀ {m k n} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ n) →
  nf (U[ plugᵗ t (parsᵗ es) ] σ)
    ≡ mkNF (BTel t n) (map (_⋯ Bσ t σ) es ++ (K `unit ∷ []))
nf-prenex-image []ᵗ           es σ = nf-U-pars es σ
nf-prenex-image (tνᵗ B₁ B₂ t) es σ =
  nf-U-ν B₁ B₂ (plugᵗ t (parsᵗ es)) σ
    ■ cong (λ N → mkNF (tel′ ++ᵗ tel N) (thr N)) (nf-prenex-image t es σ′)
  where open νImage B₁ B₂ σ

------------------------------------------------------------------------
-- Reading the block telescope off: the shape, one block per source ν-node.
------------------------------------------------------------------------

-- The shape of one node's block: its ν, then its bind groups' φ-cells.
blockShape : 𝐓.BindGroup → 𝐓.BindGroup → List Slot
blockShape B₁ B₂ = sν ∷ map sφ (syncFlags B₁) ++ map sφ (syncFlags B₂)

-- The whole telescope's shape spec: the blocks in source order.
BShape : ∀ {a b} → TTel a b → List Slot
BShape []ᵗ           = []
BShape (tνᵗ B₁ B₂ t) = blockShape B₁ B₂ ++ BShape t

shape-prenex-image : ∀ {a b} (t : TTel a b) (n : ℕ) → shape (BTel t n) ≡ BShape t
shape-prenex-image []ᵗ           n = refl
shape-prenex-image (tνᵗ B₁ B₂ t) n =
  shape-++ᵗ (tν (φTel B₁ (2 + n) ++ᵗ φTel B₂ (syncs B₁ + (2 + n))))
            (BTel t (syncs B₂ + (syncs B₁ + (2 + n))))
    ■ cong₂ _++_
        (cong (sν ∷_)
          ( shape-++ᵗ (φTel B₁ (2 + n)) (φTel B₂ (syncs B₁ + (2 + n)))
          ■ cong₂ _++_ (shape-φTel B₁ (2 + n))
                       (shape-φTel B₂ (syncs B₁ + (2 + n))) ))
        (shape-prenex-image t (syncs B₂ + (syncs B₁ + (2 + n))))

------------------------------------------------------------------------
-- Packaging: every image's normal form is a block form, up to ~.
------------------------------------------------------------------------

-- `prenex-soundᵗ` puts the source into prenex form, `U-≋` pushes that through
-- the translation, `≋⇒~` lands it on normal forms, and the main theorem names
-- the result: a block telescope indexed by the typed prenex telescope, over
-- the typed threads under the accumulated substitution.
image-block-~ :
  ∀ {m n} (P : 𝐓.Proc m) (σ : m →ₛ n) →
  nf (U[ P ] σ)
    ~ mkNF (BTel (tel (prenexᵗ P)) n)
           (map (_⋯ Bσ (tel (prenexᵗ P)) σ) (thr (prenexᵗ P)) ++ (K `unit ∷ []))
image-block-~ P σ =
  ~-trans (≋⇒~ (U-≋ σ (prenex-soundᵗ P)))
          (≡→~ (nf-prenex-image (tel (prenexᵗ P)) (thr (prenexᵗ P)) σ))
