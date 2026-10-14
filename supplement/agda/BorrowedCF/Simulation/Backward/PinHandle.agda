-- | Backward simulation, RU-LSplit — Stage D toolkit, part 2: the GROWN
--   handle slots at Bσ.
--
--   Setting (module BσHandle = module BσLwk's): the typed prenex telescope
--   factors as t₁ ++ᵗᵗ tνᵗ C₁ B t₂ with the split channel at block position
--   q of an entry (q + suc b₁) of the node's FIRST group C₁.  After the
--   split the entry grows to (q + suc (suc b₁)); the reduct thread holds the
--   two borrow handles at flat positions sum G₁ + q and sum G₁ + q + 1.
--
--   Main results: given the OLD handle's image triple decomposition
--       Bσ t σ x₀ᵥ ≡ (A ⊗ (` J)) ⊗ C
--   the two grown borrow handles' images are
--       handle-image₀ : Bσ t′ σ h₀ ≡ (subst A ⊗ (` subst J)) ⊗ K `unit
--       handle-image₁ : Bσ t′ σ h₁ ≡ (K `unit ⊗ (` subst J)) ⊗ subst C
--   — precisely the RU-LSplit reduct's borrow triples.  All content is the
--   forward SplitsH2 lemma family (canonₛ-handleq(-b1), handle-L-lwkq,
--   handle-R-lwkq, handle-R0-*q, handle-b1-L-*q), lifted through σB≗canonₛ,
--   νHandle, and Bσ-node.
--
--   STATUS: building.  Consumed by Backward.PinLSplit's Stage-D assembly.
module BorrowedCF.Simulation.Backward.PinHandle where

open import BorrowedCF.Simulation.Base
import BorrowedCF.Processes.Typed as TP

open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Image using (σB; module νImage)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage using (BScope; BTel; Bσ)
open import BorrowedCF.Simulation.Backward.PinConj
  using (BScope-++; Bσ-node; BσWk; νHandle)
open import BorrowedCF.Simulation.Backward.PinLwk
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (canonₛ)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH2
  using (canonₛ-handleq; canonₛ-handleq-b1; handle-L-lwkq; handle-R-lwkq;
         handle-R0-*q; handle-b1-L-*q)
open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ using (syncs-lwkq)
open import BorrowedCF.Terms using (module SplitRenamings)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.Fin.Properties using (splitAt-↑ˡ; toℕ-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Transport distribution helpers.
------------------------------------------------------------------------

subst-⊗ : ∀ {a b} (e : a ≡ b) (x y : Tm a) →
          subst Tm e (x ⊗ y) ≡ subst Tm e x ⊗ subst Tm e y
subst-⊗ refl x y = refl

subst-`` : ∀ {a b} (e : a ≡ b) (v : 𝔽 a) →
           subst Tm e (` v) ≡ ` subst 𝔽 e v
subst-`` refl v = refl

subst-Kᵤ : ∀ {a b} (e : a ≡ b) → subst Tm e (K `unit) ≡ K `unit
subst-Kᵤ refl = refl

subst-𝔽-irr : ∀ {x y : ℕ} (e e′ : x ≡ y) (v : 𝔽 x) → subst 𝔽 e v ≡ subst 𝔽 e′ v
subst-𝔽-irr e e′ v = cong (λ p → subst 𝔽 p v) (Nat.≡-irrelevant e e′)

subst-𝔽-■ : ∀ {x y z : ℕ} (e₁ : x ≡ y) (e₂ : y ≡ z) (v : 𝔽 x) →
            subst 𝔽 e₂ (subst 𝔽 e₁ v) ≡ subst 𝔽 (e₁ ■ e₂) v
subst-𝔽-■ refl refl v = refl

toℕ-subst : ∀ {x y : ℕ} (e : x ≡ y) (v : 𝔽 x) →
            Fin.toℕ (subst 𝔽 e v) ≡ Fin.toℕ v
toℕ-subst refl v = refl

wk*-subst : ∀ (s : ℕ) {a b} (e : a ≡ b) (t : Tm a) →
            subst Tm e t ⋯ weaken* ⦃ Kᵣ ⦄ s
              ≡ subst Tm (cong (s +_) e) (t ⋯ weaken* ⦃ Kᵣ ⦄ s)
wk*-subst s refl t = refl

⋯-BσWk-subst : ∀ {a b} (t : TTel a b) {N N′} (e : N ≡ N′) (x : Tm N) →
               subst Tm e x ⋯ BσWk t N′
                 ≡ subst Tm (cong (BScope t) e) (x ⋯ BσWk t N)
⋯-BσWk-subst t refl x = refl

⋯-subst-ren : ∀ {k N N′} (e : N ≡ N′) (ρ : k →ᵣ N) (x : Tm k) →
              x ⋯ (λ v → subst 𝔽 e (ρ v)) ≡ subst Tm e (x ⋯ ρ)
⋯-subst-ren refl ρ x = refl

-- BσWk is invariant under re-basing the telescope.
BσWk-⋯ᵗᵉˡ : ∀ {a b a′} (t : TTel a b) (ρ : a →ᵣ a′) (N : ℕ) (v : 𝔽 N) →
            BσWk (t ⋯ᵗᵉˡ ρ) N v ≡ subst 𝔽 (sym (BScope-⋯ᵗᵉˡ t ρ N)) (BσWk t N v)
BσWk-⋯ᵗᵉˡ []ᵗ            ρ N v = refl
BσWk-⋯ᵗᵉˡ (tνᵗ C₁ C₂ t) ρ N v =
  BσWk-⋯ᵗᵉˡ t (ρ ↑* (sum C₁ + sum C₂)) (syncs C₂ + (syncs C₁ + (2 + N)))
    (weaken* ⦃ Kᵣ ⦄ (syncs C₂) (weaken* ⦃ Kᵣ ⦄ (syncs C₁) (weaken* ⦃ Kᵣ ⦄ 2 v)))

⋯-BσWk-⋯ᵗᵉˡ : ∀ {a b a′} (t : TTel a b) (ρ : a →ᵣ a′) (N : ℕ) (x : Tm N) →
              x ⋯ BσWk (t ⋯ᵗᵉˡ ρ) N
                ≡ subst Tm (sym (BScope-⋯ᵗᵉˡ t ρ N)) (x ⋯ BσWk t N)
⋯-BσWk-⋯ᵗᵉˡ t ρ N x =
    ⋯-cong x (λ v → BσWk-⋯ᵗᵉˡ t ρ N v)
  ■ ⋯-subst-ren (sym (BScope-⋯ᵗᵉˡ t ρ N)) (BσWk t N) x

------------------------------------------------------------------------
-- The grown handle slots.
------------------------------------------------------------------------

module BσHandle {m n : ℕ} (σ : m →ₛ n)
                {aN : ℕ} (t₁ : TTel m aN)
                (G₁ G₂ : TP.BindGroup) (q b₁ : ℕ) (B : TP.BindGroup)
                {bN : ℕ}
                (t₂ : TTel (sum (G₁ ++ (q + suc b₁) ∷ G₂) + sum B + aN) bN)
  where

  open BσLwk σ t₁ G₁ G₂ q b₁ B t₂ public

  N₂ : ℕ
  N₂ = 2 + BScope t₁ n

  -- Handle positions, old and grown.
  p₀ᵒ : 𝔽 (sum C₁)
  p₀ᵒ = Fin.cast (sym (sum-++ G₁ ((q + suc b₁) ∷ G₂)))
          (sum G₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum G₂))

  p₀ p₁ : 𝔽 (sum C₁ᵍ)
  p₀ = Fin.cast (sym (sum-++ G₁ ((q + suc (suc b₁)) ∷ G₂)))
         (sum G₁ ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum G₂))
  p₁ = Fin.cast (sym (sum-++ G₁ ((q + suc (suc b₁)) ∷ G₂)))
         (sum G₁ ↑ʳ ((q ↑ʳ 1F) ↑ˡ sum G₂))

  x₀ᵥ : 𝔽 bN
  x₀ᵥ = wkTelᵗ t₂ ((p₀ᵒ ↑ˡ sum B) ↑ˡ aN)

  h₀ h₁ : 𝔽 (reScopeᵗ t₂ (sum C₁ᵍ + sum B + aN))
  h₀ = wkTelᵗ t₂ᵍ ((p₀ ↑ˡ sum B) ↑ˡ aN)
  h₁ = wkTelᵗ t₂ᵍ ((p₁ ↑ˡ sum B) ↑ˡ aN)

  -- The canonical handle triples.
  hcᵒ  = canonₛ-handleq    G₁ {N₂} (K `unit) 0F (K `unit) q b₁       G₂
  hcᵍ  = canonₛ-handleq    G₁ {N₂} (K `unit) 0F (K `unit) q (suc b₁) G₂
  hcᵍ₁ = canonₛ-handleq-b1 G₁ {N₂} (K `unit) 0F (K `unit) q b₁       G₂

  aᵒ cᵒ : Tm (syncs C₁ + N₂)
  aᵒ = proj₁ hcᵒ
  cᵒ = proj₁ (proj₂ hcᵒ)
  jᵒ : 𝔽 (syncs C₁ + N₂)
  jᵒ = proj₁ (proj₂ (proj₂ hcᵒ))

  aᵍ cᵍ : Tm (syncs C₁ᵍ + N₂)
  aᵍ = proj₁ hcᵍ
  cᵍ = proj₁ (proj₂ hcᵍ)
  jᵍ : 𝔽 (syncs C₁ᵍ + N₂)
  jᵍ = proj₁ (proj₂ (proj₂ hcᵍ))

  aᵇ cᵇ : Tm (syncs C₁ᵍ + N₂)
  aᵇ = proj₁ hcᵍ₁
  cᵇ = proj₁ (proj₂ hcᵍ₁)
  jᵇ : 𝔽 (syncs C₁ᵍ + N₂)
  jᵇ = proj₁ (proj₂ (proj₂ hcᵍ₁))

  ceq₂ : syncs C₁ + N₂ ≡ syncs C₁ᵍ + N₂
  ceq₂ = cong (_+ N₂) (syncs-lwkq G₁ {q} {b₁} {G₂})

  -- Scope bookkeeping.
  eO : BScope t₂ Nold ≡ BScope t n
  eO = sym (BScope-++ t₁ (tνᵗ C₁ B t₂) n)

  eG : BScope t₂ᵍ Nᵍ ≡ BScope t′ n
  eG = sym (BScope-++ t₁ (tνᵗ C₁ᵍ B t₂ᵍ) n)

  -- Image of one handle triple, spelled out at the node.
  private
    triple : ∀ {N} (a c : Tm N) (j : 𝔽 N) → Tm N
    triple a c j = (a ⊗ (` j)) ⊗ c

  -- The three canonical component images at the full image scope.
  A₀ C₀ : Tm (BScope t n)
  A₀ = subst Tm eO ((aᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold)
  C₀ = subst Tm eO ((cᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold)
  J₀ : 𝔽 (BScope t n)
  J₀ = subst 𝔽 eO (BσWk t₂ Nold (weaken* ⦃ Kᵣ ⦄ (syncs B) jᵒ))

  -- The OLD handle's image, decomposed.
  old-image : Bσ t σ x₀ᵥ ≡ (A₀ ⊗ (` J₀)) ⊗ C₀
  old-image =
      Bσ-node t₁ C₁ B t₂ σ (p₀ᵒ ↑ˡ sum B)
    ■ cong (λ u → subst Tm eO (u ⋯ BσWk t₂ Nold)) handle-red
    ■ cong (subst Tm eO) split-⋯
    ■ subst-⊗ eO _ _
    ■ cong₂ _⊗_ (subst-⊗ eO _ _ ■ cong (_ ⊗_) (subst-`` eO _)) refl
    where
      handle-red : νHandle C₁ B τ₀ (p₀ᵒ ↑ˡ sum B)
                     ≡ triple aᵒ cᵒ jᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
      handle-red =
          cong [ _ , _ ]′ (splitAt-↑ˡ (sum C₁) p₀ᵒ (sum B))
        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
            ( σB≗canonₛ C₁ (* , 0F , *) p₀ᵒ
            ■ proj₁ (proj₂ (proj₂ (proj₂ hcᵒ))) )
      split-⋯ : (triple aᵒ cᵒ jᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold
                  ≡ ((aᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold
                      ⊗ (` BσWk t₂ Nold (weaken* ⦃ Kᵣ ⦄ (syncs B) jᵒ)))
                    ⊗ ((cᵒ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold)
      split-⋯ = refl

  -- The GROWN borrow-0 handle's image.
  grown-image₀ :
    Bσ t′ σ h₀ ≡ (subst Tm eqB A₀ ⊗ (` subst 𝔽 eqB J₀)) ⊗ K `unit
  grown-image₀ =
      Bσ-node t₁ C₁ᵍ B t₂ᵍ σ (p₀ ↑ˡ sum B)
    ■ cong (λ u → subst Tm eG (u ⋯ BσWk t₂ᵍ Nᵍ)) handle-red
    ■ cong (subst Tm eG) split-⋯
    ■ subst-⊗ eG _ _
    ■ cong₂ _⊗_
        ( subst-⊗ eG _ _
        ■ cong₂ _⊗_ chase-A (subst-`` eG _ ■ cong `_ chase-J) )
        chase-C
    where
      handle-red : νHandle C₁ᵍ B τ₀ (p₀ ↑ˡ sum B)
                     ≡ ((aᵍ ⊗ (` jᵍ)) ⊗ cᵍ) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)
      handle-red =
          cong [ _ , _ ]′ (splitAt-↑ˡ (sum C₁ᵍ) p₀ (sum B))
        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B))
            ( σB≗canonₛ C₁ᵍ (* , 0F , *) p₀
            ■ proj₁ (proj₂ (proj₂ (proj₂ hcᵍ))) )
      split-⋯ : (((aᵍ ⊗ (` jᵍ)) ⊗ cᵍ) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ
                  ≡ ((aᵍ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ
                      ⊗ (` BσWk t₂ᵍ Nᵍ (weaken* ⦃ Kᵣ ⦄ (syncs B) jᵍ)))
                    ⊗ ((cᵍ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ)
      split-⋯ = refl
      -- component chases
      chase-gen : ∀ (x : Tm (syncs C₁ + N₂)) →
                  ((subst Tm ceq₂ x ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ)
                    ≡ subst Tm eqB
                        (subst Tm eO ((x ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold))
      chase-gen x =
          cong (_⋯ BσWk t₂ᵍ Nᵍ) (wk*-subst (syncs B) ceq₂ x)
        ■ ⋯-BσWk-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ
            (subst Tm (cong (syncs B +_) ceq₂) (x ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)))
        ■ cong (subst Tm (sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ)))
            (⋯-BσWk-subst t₂ (cong (syncs B +_) ceq₂) (x ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)))
        ■ subst-Tm-■ (cong (BScope t₂) (cong (syncs B +_) ceq₂))
                     (sym (BScope-⋯ᵗᵉˡ t₂ lwkᵃ Nᵍ)) _
        ■ subst-Tm-irr _ (eO ■ eqB) _
        ■ sym (subst-Tm-■ eO eqB ((x ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ Nold))
      chase-A : (aᵍ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ
                  ≡ subst Tm eqB A₀
      chase-A =
          cong (λ u → (u ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ)
            (sym (handle-L-lwkq G₁ (K `unit) 0F (K `unit) q b₁ G₂))
        ■ chase-gen aᵒ
      chase-C : (cᵍ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ ≡ K `unit
      chase-C = cong (λ u → (u ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B)) ⋯ BσWk t₂ᵍ Nᵍ)
                  (handle-R0-*q G₁ (K `unit) 0F (K `unit) q b₁ G₂)
      jeq : jᵍ ≡ subst 𝔽 ceq₂ jᵒ
      jeq = toℕ-injective
              ( proj₂ (proj₂ (proj₂ (proj₂ hcᵍ)))
              ■ cong (_+ 0) (sym (syncs-lwkq G₁ {q} {b₁} {G₂}))
              ■ sym (proj₂ (proj₂ (proj₂ (proj₂ hcᵒ))))
              ■ sym (toℕ-subst ceq₂ jᵒ) )
      chase-J : BσWk t₂ᵍ Nᵍ (weaken* ⦃ Kᵣ ⦄ (syncs B) jᵍ) ≡ subst 𝔽 eqB J₀
      chase-J = {!!}

  -- The GROWN borrow-1 handle's image.
  grown-image₁ :
    Bσ t′ σ h₁ ≡ (K `unit ⊗ (` subst 𝔽 eqB J₀)) ⊗ subst Tm eqB C₀
  grown-image₁ = {!!}
