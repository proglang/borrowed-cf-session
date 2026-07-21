-- | The normal form of a TRANSLATION IMAGE.
--
--   Downstream the reverse simulation has to invert `T ≋ U[ P ] σ`: from the
--   normal-form theory it gets `nf T ~ nf (U[ P ] σ)`, and to turn that into a
--   statement about P it must know what `nf (U[ P ] σ)` IS.  This module
--   computes it: the image's telescope is exactly one `tν` per source `ν`-node,
--   each followed by the two φ-nests the node's bind groups emit, and its
--   thread list is exactly the source's threads under the accumulated
--   substitution.
--
--   The obstacle is the `+-suc` bookkeeping in `Translation.UB[_]`: the φ-nest
--   for `b ∷ B` is built by recursing on `B` at scope `1 + n`, which produces a
--   body at `syncs B + suc n` where the caller wants `suc (syncs B) + n`, and
--   `UB[_]` bridges that with a `subst Proc`.  The fix is the same one
--   Normal.Form used for `Tel`: give the φ-nest a TRANSPORT-FREE structural
--   definition (`φTelᵣ`, inner scope `syncsScope B n`) and confine the index
--   equality to a single named lemma (`scope≡`).  `φTel` is then the transported
--   telescope, and — crucially — the transport sits on the TELESCOPE, not on the
--   body, so the two nests of a `ν`-node compose by plain `_++ᵗ_` with nothing
--   in between.
module BorrowedCF.Simulation.Support.Normal.Image where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Untyped
open import BorrowedCF.Processes.Translation
open import BorrowedCF.Simulation.Support.Normal.Form
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf; combine)
open import BorrowedCF.Simulation.Support.Normal.Rename using (renTel)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (νNF; φNF)
open import BorrowedCF.Simulation.Support.Base using (funext)

import BorrowedCF.Processes.Typed as 𝐓

open import Data.Nat.ListAction using (sum)
open import Data.List using (List; []; _∷_; _++_; map; length)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Telescope plumbing not already in Normal.Form.
------------------------------------------------------------------------

-- Moving a scope transport from the body of a plugging to its telescope.  This
-- is what lets `UB-plug` below be stated with a transport-free body.
plug-subst : ∀ {n k k′} (eq : k ≡ k′) (t : Tel n k) (X : Proc k′) →
             plug (subst (Tel n) eq t) X ≡ plug t (subst Proc (sym eq) X)
plug-subst refl t X = refl

subst-sym-■ : ∀ (A : ℕ → Set) {a b c} (p : a ≡ b) (q : b ≡ c) (x : A c) →
              subst A (sym (p ■ q)) x ≡ subst A (sym p) (subst A (sym q) x)
subst-sym-■ A refl refl x = refl

------------------------------------------------------------------------
-- Normalising a plugging.
------------------------------------------------------------------------

-- `nf` walks straight through a telescope: it neither reassociates nor renames
-- binders, so the normal form of a plugging is the telescope prefixed onto the
-- body's.  Every image statement below is an instance of this.
nf-plug : ∀ {n k} (t : Tel n k) (X : Proc k) →
          nf (plug t X) ≡ mkNF (t ++ᵗ tel (nf X)) (thr (nf X))
nf-plug []       X = refl
nf-plug (tν t)   X = cong νNF     (nf-plug t X)
nf-plug (tφ f t) X = cong (φNF f) (nf-plug t X)

------------------------------------------------------------------------
-- The φ-nest a bind group emits.
------------------------------------------------------------------------

-- `UB[ b ∷ B ]` emits one φ and recurses on B at scope `1 + n`; `syncsScope`
-- is that iteration, i.e. the inner scope of the nest, computed the way the
-- nest is BUILT rather than as `syncs B + n`.
syncsScope : 𝐓.BindGroup → ℕ → ℕ
syncsScope []              n = n
syncsScope (_ ∷ [])        n = n
syncsScope (_ ∷ B@(_ ∷ _)) n = syncsScope B (suc n)

-- The nest itself: one `tφ ϕ[ b ]` per NON-LAST element, outermost first.
φTelᵣ : (B : 𝐓.BindGroup) (n : ℕ) → Tel n (syncsScope B n)
φTelᵣ []              n = []
φTelᵣ (_ ∷ [])        n = []
φTelᵣ (b ∷ B@(_ ∷ _)) n = tφ ϕ[ b ] (φTelᵣ B (suc n))

-- The single index equality of the module.  Its cons case is literally the
-- `+-suc` that `UB[_]` transports along, which is why `UB-plug` can discharge
-- the whole transport with `subst-sym-■`.
scope≡ : ∀ (B : 𝐓.BindGroup) (n : ℕ) → syncsScope B n ≡ syncs B + n
scope≡ []              n = refl
scope≡ (_ ∷ [])        n = refl
scope≡ (_ ∷ B@(_ ∷ _)) n = scope≡ B (suc n) ■ +-suc (syncs B) n

φTel : (B : 𝐓.BindGroup) (n : ℕ) → Tel n (syncs B + n)
φTel B n = subst (Tel n) (scope≡ B n) (φTelᵣ B n)

------------------------------------------------------------------------
-- The substitution a bind group feeds to its continuation.
------------------------------------------------------------------------

-- A transcription of the argument `UB[_]` hands to `f`, so that `UB-plug` is a
-- structural induction with no inversion of the continuation.
σB : (B : 𝐓.BindGroup) → UChan n → sum B →ₛ syncs B + n
σB []              c             = λ()
σB (b ∷ [])        c             = Ub[ b + 0 ] c
σB {n} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) y =
  subst Tm (+-suc (syncs B) n) $
    [ Ub[ b ] (wk e₁ , suc x , ` 0F) ·ₖ weaken* (syncs B)
    , σB B (` 0F , suc x , wk e₂)
    ]′ (splitAt b y)

-- `UB[ B ] c f` is a φ-nest over `f` applied to `σB B c` — for ANY continuation
-- `f`.  Parametricity in `f` is what makes the two nests of a `ν`-node compose.
UB-plug : ∀ {n} (B : 𝐓.BindGroup) (c : UChan n)
          (f : (sum B →ₛ syncs B + n) → Proc (syncs B + n)) →
          UB[ B ] c f ≡ plug (φTel B n) (f (σB B c))
UB-plug []       c f = cong f (funext (λ ()))
UB-plug (b ∷ []) c f = refl
UB-plug {n} (b ∷ B@(_ ∷ _)) c@(e₁ , x , e₂) f =
  cong (φ ϕ[ b ])
    ( UB-plug B (` 0F , suc x , wk e₂) _
    ■ plug-subst (scope≡ B (suc n)) (φTelᵣ B (suc n)) _
    ■ cong (plug (φTelᵣ B (suc n)))
        (sym (subst-sym-■ Proc (scope≡ B (suc n)) (+-suc (syncs B) n)
                (f (σB (b ∷ B) c)))) )
  ■ sym (plug-subst (scope≡ B (suc n) ■ +-suc (syncs B) n)
           (tφ ϕ[ b ] (φTelᵣ B (suc n))) (f (σB (b ∷ B) c)))

------------------------------------------------------------------------
-- The image normal form: threads and parallel composition.
------------------------------------------------------------------------

nf-U-thr : ∀ {m n} (e : Tm m) (σ : m →ₛ n) →
           nf (U[ 𝐓.⟪ e ⟫ ] σ) ≡ mkNF [] ((e ⋯ σ) ∷ [])
nf-U-thr e σ = refl

nf-U-par : ∀ {m n} (P Q : 𝐓.Proc m) (σ : m →ₛ n) →
           nf (U[ P 𝐓.∥ Q ] σ) ≡ combine (nf (U[ P ] σ)) (nf (U[ Q ] σ))
nf-U-par P Q σ = refl

------------------------------------------------------------------------
-- The image normal form: the ν case.
------------------------------------------------------------------------

-- The scopes and substitutions the translation manufactures at a `ν`-node,
-- named once so the statement below reads as the shape it claims.
module νImage {m n : ℕ} (B₁ B₂ : 𝐓.BindGroup) (σ : m →ₛ n) where

  s₁ : ℕ
  s₁ = syncs B₁ + (2 + n)

  s₂ : ℕ
  s₂ = syncs B₂ + s₁

  σ₁ : sum B₁ →ₛ s₁
  σ₁ = σB B₁ (* , 0F , *)

  σ₂ : sum B₂ →ₛ s₂
  σ₂ = σB B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *)

  -- Source variables land three ways: B₁'s in the first nest (then weakened
  -- past the second), B₂'s in the second, and everything already in scope is
  -- weakened past the ν and both nests.
  σ′ : sum B₁ + sum B₂ + m →ₛ s₂
  σ′ = ((λ i → σ₁ i ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) ++ₛ σ₂)
     ++ₛ (λ i → σ i ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂))

  tel′ : Tel n s₂
  tel′ = tν (φTel B₁ (2 + n) ++ᵗ φTel B₂ s₁)

-- The characterisation.  Read off: slot 0 of the telescope is the `ν` of this
-- node, the next `syncs B₁ + syncs B₂` slots are its bind groups' φ cells (with
-- flags `ϕ[_]`, see `shape-φTel`), and everything after that — telescope AND
-- threads — belongs to the body, translated under `σ′`.
nf-U-ν : ∀ {m n} (B₁ B₂ : 𝐓.BindGroup) (P : 𝐓.Proc (sum B₁ + sum B₂ + m))
         (σ : m →ₛ n) →
         let open νImage B₁ B₂ σ in
         nf (U[ 𝐓.ν B₁ B₂ P ] σ)
           ≡ mkNF (tel′ ++ᵗ tel (nf (U[ P ] σ′))) (thr (nf (U[ P ] σ′)))
nf-U-ν {m} {n} B₁ B₂ P σ =
  cong νNF
    ( cong nf
        ( UB-plug B₁ (* , 0F , *) _
        ■ cong (plug (φTel B₁ (2 + n))) (UB-plug B₂ (* , weaken* ⦃ Kᵣ ⦄ (syncs B₁) 1F , *) _)
        ■ sym (plug-++ᵗ (φTel B₁ (2 + n)) (φTel B₂ s₁) (U[ P ] σ′)) )
    ■ nf-plug (φTel B₁ (2 + n) ++ᵗ φTel B₂ s₁) (U[ P ] σ′) )
  where open νImage B₁ B₂ σ

------------------------------------------------------------------------
-- Reading the telescope off: which slots are ν and which are φ.
------------------------------------------------------------------------

-- The SHAPE of a telescope — its binder sequence with the flags, but without
-- the scopes.  This is the form the inversion consumes: `~` may permute the
-- slots, but the multiset of shapes is fixed, so the image's shape is the
-- constraint an ≋-escaped process has to meet.
data Slot : Set where
  sν : Slot
  sφ : Flag → Slot

shape : ∀ {n k} → Tel n k → List Slot
shape []       = []
shape (tν t)   = sν   ∷ shape t
shape (tφ f t) = sφ f ∷ shape t

shape-subst : ∀ {n k k′} (eq : k ≡ k′) (t : Tel n k) →
              shape (subst (Tel n) eq t) ≡ shape t
shape-subst refl t = refl

shape-++ᵗ : ∀ {n k j} (t : Tel n k) (s : Tel k j) →
            shape (t ++ᵗ s) ≡ shape t ++ shape s
shape-++ᵗ []       s = refl
shape-++ᵗ (tν t)   s = cong (sν   ∷_) (shape-++ᵗ t s)
shape-++ᵗ (tφ f t) s = cong (sφ f ∷_) (shape-++ᵗ t s)

-- The flags a bind group contributes: one per non-last element, `ϕ[_]` of it.
syncFlags : 𝐓.BindGroup → List Flag
syncFlags []              = []
syncFlags (_ ∷ [])        = []
syncFlags (b ∷ B@(_ ∷ _)) = ϕ[ b ] ∷ syncFlags B

syncFlags-length : ∀ (B : 𝐓.BindGroup) → length (syncFlags B) ≡ syncs B
syncFlags-length []              = refl
syncFlags-length (_ ∷ [])        = refl
syncFlags-length (_ ∷ B@(_ ∷ _)) = cong suc (syncFlags-length B)

-- A bind group's nest is φ-only, with exactly those flags: no ν ever hides in
-- it, which is what lets the ν slots be counted against the source's ν-nodes.
shape-φTelᵣ : ∀ (B : 𝐓.BindGroup) (n : ℕ) →
              shape (φTelᵣ B n) ≡ map sφ (syncFlags B)
shape-φTelᵣ []              n = refl
shape-φTelᵣ (_ ∷ [])        n = refl
shape-φTelᵣ (b ∷ B@(_ ∷ _)) n = cong (sφ ϕ[ b ] ∷_) (shape-φTelᵣ B (suc n))

shape-φTel : ∀ (B : 𝐓.BindGroup) (n : ℕ) →
             shape (φTel B n) ≡ map sφ (syncFlags B)
shape-φTel B n = shape-subst (scope≡ B n) (φTelᵣ B n) ■ shape-φTelᵣ B n

-- Re-basing preserves the shape, so `combine`'s telescope is the two shapes
-- concatenated — with the RIGHT operand outermost, which is where `combine`
-- puts it.
shape-renTel : ∀ {n k} (t : Tel n k) (a : ℕ) → shape (renTel t a) ≡ shape t
shape-renTel []       a = refl
shape-renTel (tν t)   a = cong (sν   ∷_) (shape-renTel t (2 + a))
shape-renTel (tφ f t) a = cong (sφ f ∷_) (shape-renTel t (1 + a))

shape-U-thr : ∀ {m n} (e : Tm m) (σ : m →ₛ n) →
              shape (tel (nf (U[ 𝐓.⟪ e ⟫ ] σ))) ≡ []
shape-U-thr e σ = refl

shape-U-par : ∀ {m n} (P Q : 𝐓.Proc m) (σ : m →ₛ n) →
              shape (tel (nf (U[ P 𝐓.∥ Q ] σ)))
                ≡ shape (tel (nf (U[ Q ] σ))) ++ shape (tel (nf (U[ P ] σ)))
shape-U-par P Q σ =
  shape-++ᵗ (tel (nf (U[ Q ] σ)))
            (renTel (tel (nf (U[ P ] σ))) (inner (nf (U[ Q ] σ))))
    ■ cong (shape (tel (nf (U[ Q ] σ))) ++_)
        (shape-renTel (tel (nf (U[ P ] σ))) (inner (nf (U[ Q ] σ))))

-- The thread list is neither shortened nor extended by the translation: at a ∥
-- both sides' threads survive, only renamed into the shared inner scope.
thr-length-U-par : ∀ {m n} (P Q : 𝐓.Proc m) (σ : m →ₛ n) →
                   length (thr (nf (U[ P 𝐓.∥ Q ] σ)))
                     ≡ length (thr (nf (U[ P ] σ))) + length (thr (nf (U[ Q ] σ)))
thr-length-U-par P Q σ =
  L.length-++ (map (_⋯ _) (thr (nf (U[ P ] σ))))
    ■ cong₂ _+_ (L.length-map _ (thr (nf (U[ P ] σ))))
                (L.length-map _ (thr (nf (U[ Q ] σ))))

-- The shape of a whole ν-node image, spelled out.
shape-U-ν : ∀ {m n} (B₁ B₂ : 𝐓.BindGroup) (P : 𝐓.Proc (sum B₁ + sum B₂ + m))
            (σ : m →ₛ n) →
            let open νImage B₁ B₂ σ in
            shape (tel (nf (U[ 𝐓.ν B₁ B₂ P ] σ)))
              ≡ sν ∷ map sφ (syncFlags B₁) ++ map sφ (syncFlags B₂)
                   ++ shape (tel (nf (U[ P ] σ′)))
shape-U-ν {m} {n} B₁ B₂ P σ =
  cong (λ N → shape (tel N)) (nf-U-ν B₁ B₂ P σ)
    ■ cong (sν ∷_)
        ( shape-++ᵗ (φTel B₁ (2 + n) ++ᵗ φTel B₂ s₁) (tel (nf (U[ P ] σ′)))
        ■ cong (_++ shape (tel (nf (U[ P ] σ′))))
            ( shape-++ᵗ (φTel B₁ (2 + n)) (φTel B₂ s₁)
            ■ cong₂ _++_ (shape-φTel B₁ (2 + n)) (shape-φTel B₂ s₁) )
        ■ L.++-assoc (map sφ (syncFlags B₁)) (map sφ (syncFlags B₂))
                     (shape (tel (nf (U[ P ] σ′)))) )
  where open νImage B₁ B₂ σ
