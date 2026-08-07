-- | Phase 2: a STRUCTURAL normaliser `nf`, replacing the well-founded `prenex`.
--
--   `prenex` (Normal.Prenex) proves that normal forms EXIST, but it is defined
--   by well-founded recursion — its ∥ case recurses on `P ⋯ₚ wkTel t₂`, which is
--   not a subterm — so it does not compute symbolically.  Every proof that has
--   to case-split on a ≋′ generator and compare the two sides' normal forms
--   would therefore be stuck.  (This is the same reason Normal.Invariant proves
--   νcount/φcount/thrcount directly on `Proc` rather than through `prenex`.)
--
--   `nf` computes the same thing by ordinary structural recursion: the ∥ case
--   calls the NON-recursive `combine`, which does the rebasing inline using
--   Normal.Rename's `renTel` / `liftRen`.  `nf-sound` re-runs `prenex`'s ∥ chain
--   to show `nf` is still a normaliser.
--
--   With `nf` in hand, `nf-unique : ⌈ N₁ ⌉ ≋ ⌈ N₂ ⌉ → N₁ ~ N₂` becomes a
--   twelve-case induction in which each case is a concrete calculation on `nf`.
module BorrowedCF.Simulation.Support.Normal.Norm where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Rename
open import BorrowedCF.Simulation.Support.Normal.Prenex
  using (≡→≋; ≋-sym; plug-cong; tel-ext; tel-extˡ; pars-++)

open import Data.List using (List; []; _∷_; _++_; map)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)

open Nat.Variables

------------------------------------------------------------------------
-- Merging two normal forms over a common base scope.
------------------------------------------------------------------------

-- `combine N₁ N₂` puts N₂'s telescope outermost and rebases N₁'s underneath it
-- (`renTel`), renaming each side's threads into the shared inner scope.  It is
-- NOT recursive — that is what makes `nf` structural.
combine : ∀ {n} → NF n → NF n → NF n
combine {n} (mkNF {j₁} t₁ es₁) (mkNF {j₂} t₂ es₂) =
  mkNF (t₂ ++ᵗ renTel t₁ (wkTel t₂))
       ( map (_⋯ liftRen t₁ (wkTel t₂))         es₁
      ++ map (_⋯ wkTel (renTel t₁ (wkTel t₂)))  es₂ )

------------------------------------------------------------------------
-- The structural normaliser.
------------------------------------------------------------------------

nf : ∀ {n} → Proc n → NF n
nf ⟪ e ⟫   = mkNF [] (e ∷ [])
nf (P ∥ Q) = combine (nf P) (nf Q)
nf (ν P)   = mkNF (tν   (tel (nf P))) (thr (nf P))
nf (φ f c P) = mkNF (tφ f c (tel (nf P))) (thr (nf P))

------------------------------------------------------------------------
-- It is a normaliser: every process is ≋ to the plugging of its normal form.
------------------------------------------------------------------------

nf-sound : ∀ {n} (P : Proc n) → P ≋ ⌈ nf P ⌉
nf-sound ⟪ e ⟫   = ≋-sym ∥-unitʳ
nf-sound (ν P)   = ν-cong (nf-sound P)
nf-sound (φ f c P) = φ-cong (nf-sound P)
nf-sound (P ∥ Q) with nf P | nf Q | nf-sound P | nf-sound Q
... | mkNF {j₁} t₁ es₁ | mkNF {j₂} t₂ es₂ | cP | cQ =
  ∥-cong cP cQ
    ◅◅ tel-ext t₂ (pars es₂) (plug t₁ (pars es₁))
    ◅◅ plug-cong t₂
         ( ≡→≋ (cong (_∥ pars es₂) (plug-⋯ₚ t₁ (wkTel t₂) (pars es₁)))
        ◅◅ tel-extˡ (renTel t₁ (wkTel t₂)) (pars es₁ ⋯ₚ liftRen t₁ (wkTel t₂)) (pars es₂)
        ◅◅ plug-cong (renTel t₁ (wkTel t₂))
             ( ≡→≋ (cong₂ _∥_ (pars-⋯ₚ es₁ (liftRen t₁ (wkTel t₂)))
                              (pars-⋯ₚ es₂ (wkTel (renTel t₁ (wkTel t₂)))))
            ◅◅ pars-++ (map (_⋯ liftRen t₁ (wkTel t₂)) es₁)
                       (map (_⋯ wkTel (renTel t₁ (wkTel t₂)))  es₂) ) )
    ◅◅ ≡→≋ (sym (plug-++ᵗ t₂ (renTel t₁ (wkTel t₂)) _))
