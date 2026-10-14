-- | The accumulated prenex-image substitution is a VALUE substitution.
--
--   Every reverse-inversion tool (`frameApp-reflect`, `close-arg-var`,
--   `⋯→-⋯ₛ`, …) is already parametric in the substitution, demanding only a
--   `VSub` witness.  The per-op reflectors built on the block pipeline trace
--   the redex through `Bσ t σ` instead of the single-node `νσ`, so this witness
--   is the whole "composite-substitution generalisation": with it, the
--   existing reflectors apply verbatim.
--
--   The proof mirrors `Bσ`'s own layering: channel triples are values as soon
--   as their two term components are (`𝓒[ e₁ × x × e₂ ]` is a ⊗-pair over a
--   variable), renamings are trivially `VSub` (`V-\``), and `νImage.σ′` is a
--   `++ₛ`/weakening composite of `σB`s at unit/variable channels.
module BorrowedCF.Simulation.Support.Normal.PrenexImageVSub where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Reduction.Base using (Value; V-`; V-K; V-⊗; VSub; value-⋯)
import BorrowedCF.Processes.Typed as 𝐓
open import BorrowedCF.Processes.Translation
open import BorrowedCF.Simulation.Support.Frames using (++ₛ-VSub; weaken-VSub)
open import BorrowedCF.Simulation.Support.Normal.Image using (σB; module νImage)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (Bσ)
open import BorrowedCF.Simulation.Support.TypedPrenex using (TTel; []ᵗ; tνᵗ)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.ListAction using (sum)

open Nat.Variables
open Fin.Patterns

-- Renamings are value substitutions.
VSubᵣ : (ρ : m →ᵣ n) → VSub ⦃ Kᵣ ⦄ ρ
VSubᵣ ρ x = V-`

-- Transport along a scope equality preserves value-ness.
subst-Value : (eq : n ≡ m) {t : Tm n} → Value t → Value (subst Tm eq t)
subst-Value refl v = v

-- Value-ness of a `UChan`'s two term components.
UChanV : UChan n → Set
UChanV (e₁ , _ , e₂) = Value e₁ × Value e₂

Ub-VSub : ∀ b {c : UChan n} → UChanV c → VSub (Ub[ b ] c)
Ub-VSub 1 (v₁ , v₂) zero = V-⊗ (V-⊗ v₁ V-`) v₂
Ub-VSub (suc (suc b)) (v₁ , v₂) zero    = V-⊗ (V-⊗ v₁ V-`) V-K
Ub-VSub (suc (suc b)) (v₁ , v₂) (suc x) = Ub-VSub (suc b) (V-K , v₂) x

mutual
  σB-VSub : ∀ B {c : UChan n} → UChanV c → VSub (σB B c)
  σB-VSub []       uc ()
  σB-VSub (b ∷ []) uc = Ub-VSub (b + 0) uc
  σB-VSub {n} (b ∷ B@(_ ∷ _)) {c = e₁ , x , e₂} uc y =
    subst-Value (+-suc (syncs B) n) (σB-branch b B uc (splitAt b y) refl)

  σB-branch : ∀ b B {e₁ : Tm n} {x : 𝔽 n} {e₂ : Tm n} →
              UChanV {n = n} (e₁ , x , e₂) → {b' : ℕ} {B' : 𝐓.BindGroup} →
              (s : 𝔽 b ⊎ 𝔽 (sum (b' ∷ B'))) → B ≡ b' ∷ B' →
              Value ([ (λ j → Ub[ b ] (wk e₁ , suc x , ` 0F) j ⋯ weaken* (syncs (b' ∷ B')))
                     , σB (b' ∷ B') (` 0F , suc x , wk e₂) ]′ s)
  σB-branch b B (v₁ , v₂) (inj₁ j) refl =
    value-⋯ (Ub-VSub b (value-⋯ v₁ weakenᵣ (VSubᵣ _) , V-`) j)
            (weaken* _) (VSubᵣ _)
  σB-branch b (b' ∷ B') (v₁ , v₂) (inj₂ j) refl =
    σB-VSub (b' ∷ B') (V-` , value-⋯ v₂ weakenᵣ (VSubᵣ _)) j

σ′-VSub : ∀ (B₁ B₂ : 𝐓.BindGroup) {σ : m →ₛ n} → VSub σ → VSub (νImage.σ′ B₁ B₂ σ)
σ′-VSub B₁ B₂ Vσ =
  ++ₛ-VSub
    (++ₛ-VSub (weaken-VSub (syncs B₂) (σB-VSub B₁ (V-K , V-K)))
              (σB-VSub B₂ (V-K , V-K)))
    (weaken-VSub (syncs B₂) (weaken-VSub (syncs B₁) (weaken-VSub 2 Vσ)))

Bσ-VSub : ∀ {a b} (t : TTel a b) {σ : a →ₛ n} → VSub σ → VSub (Bσ t σ)
Bσ-VSub []ᵗ           Vσ = Vσ
Bσ-VSub (tνᵗ B₁ B₂ t) Vσ = Bσ-VSub t (σ′-VSub B₁ B₂ Vσ)
