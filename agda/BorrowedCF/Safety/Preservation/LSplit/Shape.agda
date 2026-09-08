------------------------------------------------------------------------
-- P3c, step 1: the SHAPE of a mobile split handle.
--
-- P3b left `pres-LSplit` with the premise "the consumed handle is not
-- mobile" and believed a mobile handle to be a genuine counterexample.  It
-- is not: a mobile handle is pinned to a very particular place in its
-- binder list, namely `q ≡ 0` (it is its group's HEAD) and `b₁ ≡ 0` (it is
-- its group's ONLY handle).  Contrapositively, this module proves
--
--   `handle-interior-¬mobile`  a handle at offset `q > 0` of its group is
--                              immobile, and
--   `handle-wide-¬mobile`      the head of a group of width `≥ 2` is
--                              immobile,
--
-- which is exactly what the two "immobile" clauses of the premise-free
-- `pres-LSplit` need.  The third clause (`q ≡ 0`, `b₁ ≡ 0`) needs no
-- mobility fact at all -- see `LSplit/Mobile.agda`.
--
-- Everything here is assembled from `Simulation/BackwardSoup/`, whose
-- interfaces are cached in `agda/_build`:
--   * `Position.first-group-¬mobile`         (no handle of the FIRST group
--                                             of a `New`-derived side is
--                                             mobile),
--   * `Crux.nonFirstGroup-interior-noAcq`    (an INTERIOR handle of a later
--                                             group carries no `acq`),
--   * `Crux.mobile-head-alone`               (a mobile handle at offset 0 is
--                                             its group's only handle),
--   * `GroupOrder.{NoAcq, ¬mobile-noAcq, …}`.
-- The only thing this module adds is the NAVIGATION: the reduction rule
-- addresses the handle by the flat position `sum B₁ + q` of the group list
-- `B₁ ++ (q + suc b₁) ∷ B₂`, and the lemmas above are stated over
-- `Position.GroupOf`.  `groupAt` builds that `GroupOf` and reads off its
-- index, offset and width.
------------------------------------------------------------------------
module BorrowedCF.Safety.Preservation.LSplit.Shape where

open import Data.List.Relation.Unary.All as Allᴸ using () renaming (All to Allᴸ)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Types

open import BorrowedCF.Safety.Preservation.Splits.Group using (cast-↑ʳ-+)

open import BorrowedCF.Simulation.BackwardSoup.GroupOrder
  using (NoAcq; ¬mobile-noAcq; new-end⇒noAcq; noAcq-;-snd; noAcq-≃)
open import BorrowedCF.Simulation.BackwardSoup.Position
  using ( GroupOf; head-group; next-group
        ; groupIndex; groupOffset; groupWidth; first-group-¬mobile )
open import BorrowedCF.Simulation.BackwardSoup.Position.Crux
  using (mobile-head-alone; nonFirstGroup-interior-noAcq)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- 1.  The flat position of the consumed handle.

dpos : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) →
  𝔽 (sum (B₁ ++ (q + suc b₁) ∷ B₂))
dpos B₁ q b₁ B₂ =
  Fin.cast (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
           (sum B₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum B₂))

------------------------------------------------------------------------
-- 2.  `GroupOf` at that position.

private
  go-index : ∀ {B} {i j : 𝔽 (sum B)} (e : i ≡ j) (g : GroupOf B i) →
    groupIndex (subst (GroupOf B) e g) ≡ groupIndex g
  go-index refl g = refl

  go-offset : ∀ {B} {i j : 𝔽 (sum B)} (e : i ≡ j) (g : GroupOf B i) →
    groupOffset (subst (GroupOf B) e g) ≡ groupOffset g
  go-offset refl g = refl

  go-width : ∀ {B} {i j : 𝔽 (sum B)} (e : i ≡ j) (g : GroupOf B i) →
    groupWidth (subst (GroupOf B) e g) ≡ groupWidth g
  go-width refl g = refl

groupAt : ∀ (B₁ : BindGroup) (q b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ g ∈ GroupOf (B₁ ++ (q + suc b₁) ∷ B₂) (dpos B₁ q b₁ B₂) ]
      (groupIndex  g ≡ L.length B₁)
    × (groupOffset g ≡ q)
    × (groupWidth  g ≡ q + suc b₁)
groupAt [] q b₁ B₂ =
    subst (GroupOf ((q + suc b₁) ∷ B₂)) (sym e) (head-group B₂ (q ↑ʳ 0F))
  , go-index  (sym e) (head-group B₂ (q ↑ʳ 0F))
  , (go-offset (sym e) (head-group B₂ (q ↑ʳ 0F))
      ■ (Fin.toℕ-↑ʳ q (Fin.zero {n = b₁}) ■ Nat.+-identityʳ q))
  , go-width  (sym e) (head-group B₂ (q ↑ʳ 0F))
  where
    e : dpos [] q b₁ B₂ ≡ (q ↑ʳ 0F) ↑ˡ sum B₂
    e = Fin.cast-is-id (sym (sum-++ [] ((q + suc b₁) ∷ B₂))) ((q ↑ʳ 0F) ↑ˡ sum B₂)
groupAt (b₀ ∷ B₁) q b₁ B₂ with groupAt B₁ q b₁ B₂
... | g , ei , eo , ew =
    subst (GroupOf ((b₀ ∷ B₁) ++ (q + suc b₁) ∷ B₂)) (sym e) (next-group b₀ g)
  , (go-index  (sym e) (next-group b₀ g) ■ cong suc ei)
  , (go-offset (sym e) (next-group b₀ g) ■ eo)
  , (go-width  (sym e) (next-group b₀ g) ■ ew)
  where
    e : dpos (b₀ ∷ B₁) q b₁ B₂ ≡ b₀ ↑ʳ dpos B₁ q b₁ B₂
    e = cast-↑ʳ-+ b₀ (sum B₁)
          (sym (sum-++ (b₀ ∷ B₁) ((q + suc b₁) ∷ B₂)))
          (sym (sum-++ B₁ ((q + suc b₁) ∷ B₂)))
          ((q ↑ʳ 0F) ↑ˡ sum B₂)

------------------------------------------------------------------------
-- 3.  An interior handle of a LATER group carries no `acq`.
--
-- This re-derives `Position/Crux.agda`'s PRIVATE `laterGroup-interior-noAcq`
-- from its public `nonFirstGroup-interior-noAcq`; the three lines are
-- verbatim theirs.

laterInterior-noAcq : ∀ {B} {Γ : Ctx (sum B)} {s : 𝕊 0} {p} →
  New s → BindCtx (s ; end p) B Γ → ⊢ᴮ B →
  ∀ {i} (grp : GroupOf B i) →
  0 Nat.< groupIndex grp → 0 Nat.< groupOffset grp →
  Σ[ s′ ∈ 𝕊 0 ] ((Γ ﹫ i) ≃ ⟨ s′ ⟩) × NoAcq s′
laterInterior-noAcq N (last C) ⊢B (head-group B′ j) () 0<off
laterInterior-noAcq N (last C) ⊢B (next-group _ ()) 0<gi 0<off
laterInterior-noAcq N (cons-ret/acq s₁ {Γ₁ = Γ₁} {Γ₂ = Γ₂} s≃ _ front rest ah)
  ⊢B (next-group n g′) 0<gi 0<off =
  let s′ , eq , na =
        nonFirstGroup-interior-noAcq
          (noAcq-;-snd (noAcq-≃ (≃-sym s≃) (new-end⇒noAcq N))) rest ah ⊢B g′ 0<off
  in s′ , subst (_≃ ⟨ s′ ⟩) (sym (V.lookup-++ʳ Γ₁ Γ₂ _)) eq , na
laterInterior-noAcq N (cons-ret/acq s₁ s≃ _ front rest ah) ⊢B
  (head-group B′ j) () 0<off
laterInterior-noAcq N (cons-acq C ah) ⊢B (next-group .0 g′) 0<gi 0<off =
  nonFirstGroup-interior-noAcq (new-end⇒noAcq N) C ah ⊢B g′ 0<off

------------------------------------------------------------------------
-- 4.  The two immobility facts the premise-free `pres-LSplit` needs.

-- A handle at a POSITIVE offset inside its group is immobile: in the first
-- group because the whole group sits over an `acq`-free session, in a later
-- group because only the group's HEAD carries the group's `acq`.
handle-interior-¬mobile : ∀ (B₁ : BindGroup) {B₂ : BindGroup} {q b₁ : ℕ}
  {Γ : Ctx (sum (B₁ ++ (q + suc b₁) ∷ B₂))} {s : 𝕊 0} {p} →
  0 Nat.< q → New s → ⊢ᴮ (B₁ ++ (q + suc b₁) ∷ B₂) →
  BindCtx (s ; end p) (B₁ ++ (q + suc b₁) ∷ B₂) Γ →
  ¬ Mobile (Γ ﹫ dpos B₁ q b₁ B₂)
handle-interior-¬mobile [] {B₂} {q} {b₁} 0<q N ⊢B C
  with g , ei , eo , ew ← groupAt [] q b₁ B₂ =
  first-group-¬mobile N C g ei
handle-interior-¬mobile (b₀ ∷ B₁) {B₂} {q} {b₁} 0<q N ⊢B C
  with g , ei , eo , ew ← groupAt (b₀ ∷ B₁) q b₁ B₂
  with s′ , eq , na ← laterInterior-noAcq N C ⊢B g
                        (subst (0 Nat.<_) (sym ei) Nat.z<s)
                        (subst (0 Nat.<_) (sym eo) 0<q) =
  λ mob → ¬mobile-noAcq na (mobile-≃ eq mob)

-- The HEAD of a group of width ≥ 2 is immobile: a mobile handle at offset 0
-- carries its group's terminator, and a terminator ends the group.
handle-wide-¬mobile : ∀ (B₁ : BindGroup) {B₂ : BindGroup} {b₁ : ℕ}
  {Γ : Ctx (sum (B₁ ++ suc (suc b₁) ∷ B₂))} {s : 𝕊 0} {p} →
  New s → BindCtx (s ; end p) (B₁ ++ suc (suc b₁) ∷ B₂) Γ →
  ¬ Mobile (Γ ﹫ dpos B₁ 0 (suc b₁) B₂)
handle-wide-¬mobile B₁ {B₂} {b₁} N C
  with g , ei , eo , ew ← groupAt B₁ 0 (suc b₁) B₂ =
  λ mob → case sym ew ■ mobile-head-alone N C g eo mob of λ ()
