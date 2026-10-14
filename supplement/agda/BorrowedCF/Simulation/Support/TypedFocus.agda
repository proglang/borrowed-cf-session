-- | The typed FOCUS construction.
--
--   A typed prenex form can be rearranged by ≋ so that a CHOSEN ν-node is the
--   outermost binder and a CHOSEN thread is the leftmost parallel component of
--   the flat thread list underneath the residual telescope:
--
--       plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) (parsᵗ es)
--         ≋ ν B₁ B₂ (plugᵗ u (⟪ e ⋯ ρf ⟫ ∥ parsᵗ es′))
--
--   The chosen node is bubbled past the prefix `t₁` by one adjacent `ν-comm′`
--   per prefix binder (the typed mirror of Normal.Bubble); its bind groups are
--   UNCHANGED, and the prefix nodes end up INSIDE the focused ν, rebased by the
--   accumulated block swaps.  The residual telescope `u = bubTelᵗ`, the thread
--   renaming `ρf = bubρᵗ`, and the leftover threads are all concrete recursive
--   functions of the inputs — nothing is existential, so a consumer can compute
--   the translation of the focused form directly.
--
--   NOTE the chosen thread stays INSIDE the residual telescope `u`: it lives at
--   the prenex inner scope and in general mentions binders of `t₂`, so it
--   cannot be strengthened past `u` — `⟪ e ⋯ ρf ⟫ ∥ parsᵗ es′` directly under
--   the focused ν, with `u` around it, is the strongest true shape.
module BorrowedCF.Simulation.Support.TypedFocus where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed
open import BorrowedCF.Simulation.Support.TypedPrenex

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅◅_)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables

------------------------------------------------------------------------
-- The residual telescope, inner scope, and thread renaming a bubble
-- produces.  One `assocSwapᵣ` per prefix binder, each pushed under the
-- already-processed tail by `⋯ᵗᵉˡ` / `↑ᵗᵉˡ` — all concrete, no Σ.
------------------------------------------------------------------------

bubScopeᵗ : ∀ {m q k} (b : ℕ) → TTel m q → TTel (b + q) k → ℕ
bubTelᵗ   : ∀ {m q k} (b : ℕ) (t₁ : TTel m q) (t₂ : TTel (b + q) k) →
            TTel (b + m) (bubScopeᵗ b t₁ t₂)

bubScopeᵗ {k = k} b []ᵗ            t₂ = k
bubScopeᵗ {m = m} b (tνᵗ C₁ C₂ t₁) t₂ =
  reScopeᵗ (bubTelᵗ b t₁ t₂) (sum C₁ + sum C₂ + (b + m))

bubTelᵗ b []ᵗ            t₂ = t₂
bubTelᵗ b (tνᵗ C₁ C₂ t₁) t₂ =
  tνᵗ C₁ C₂ (bubTelᵗ b t₁ t₂ ⋯ᵗᵉˡ assocSwapᵣ b (sum C₁ + sum C₂))

bubρᵗ : ∀ {m q k} (b : ℕ) (t₁ : TTel m q) (t₂ : TTel (b + q) k) →
        k →ᵣ bubScopeᵗ b t₁ t₂
bubρᵗ b []ᵗ            t₂ = idₖ
bubρᵗ b (tνᵗ C₁ C₂ t₁) t₂ =
  bubρᵗ b t₁ t₂ ·ₖ (bubTelᵗ b t₁ t₂ ↑ᵗᵉˡ assocSwapᵣ b (sum C₁ + sum C₂))

------------------------------------------------------------------------
-- Node to front: bubble the chosen ν past the prefix telescope.
------------------------------------------------------------------------

node-to-frontᵗ : ∀ {m q k} (B₁ B₂ : BindGroup) (t₁ : TTel m q)
                 (t₂ : TTel (sum B₁ + sum B₂ + q) k) (X : Proc k) →
                 plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) X
                   ≋ ν B₁ B₂ (plugᵗ (bubTelᵗ (sum B₁ + sum B₂) t₁ t₂)
                                    (X ⋯ₚ bubρᵗ (sum B₁ + sum B₂) t₁ t₂))
node-to-frontᵗ B₁ B₂ []ᵗ            t₂ X =
  ≡→≋ᵗ (cong (λ Y → ν B₁ B₂ (plugᵗ t₂ Y)) (sym (⋯ₚ-idᵣᵗ X (λ _ → refl))))
node-to-frontᵗ B₁ B₂ (tνᵗ C₁ C₂ t₁) t₂ X =
  ν-cong (node-to-frontᵗ B₁ B₂ t₁ t₂ X)
    ◅◅ Eq*.return ν-comm′
    ◅◅ ≡→≋ᵗ (cong (ν B₁ B₂ ∘ ν C₁ C₂)
               ( plug-⋯ₚᵗ (bubTelᵗ b t₁ t₂) (X ⋯ₚ bubρᵗ b t₁ t₂) (assocSwapᵣ b c)
               ■ cong (plugᵗ (bubTelᵗ b t₁ t₂ ⋯ᵗᵉˡ assocSwapᵣ b c))
                      (fusionₚ X (bubρᵗ b t₁ t₂) (bubTelᵗ b t₁ t₂ ↑ᵗᵉˡ assocSwapᵣ b c)) ))
  where
    b = sum B₁ + sum B₂
    c = sum C₁ + sum C₂

------------------------------------------------------------------------
-- Thread to front: pars-level surgery.
------------------------------------------------------------------------

deleteᵗ : ∀ {n} {e : Tm n} (es : List (Tm n)) → e ∈ es → List (Tm n)
deleteᵗ (x ∷ es) (here _)  = es
deleteᵗ (x ∷ es) (there i) = x ∷ deleteᵗ es i

pars-∈ᵗ : ∀ {n} {e : Tm n} (es : List (Tm n)) (i : e ∈ es) →
          parsᵗ es ≋ ⟪ e ⟫ ∥ parsᵗ (deleteᵗ es i)
pars-∈ᵗ (x ∷ es) (here refl) = ε
pars-∈ᵗ (x ∷ es) (there i)   =
  ∥-cong ε (pars-∈ᵗ es i) ◅◅ ∥-assoc ◅◅ ∥-cong ∥-comm ε ◅◅ ≋ᵗ-sym ∥-assoc

∈-mapᵗ : ∀ {n j} (ρ : n →ᵣ j) {e : Tm n} {es : List (Tm n)} →
         e ∈ es → (e ⋯ ρ) ∈ map (_⋯ ρ) es
∈-mapᵗ ρ (here refl) = here refl
∈-mapᵗ ρ (there i)   = there (∈-mapᵗ ρ i)

map-deleteᵗ : ∀ {n j} (ρ : n →ᵣ j) {e : Tm n} (es : List (Tm n)) (i : e ∈ es) →
              deleteᵗ (map (_⋯ ρ) es) (∈-mapᵗ ρ i) ≡ map (_⋯ ρ) (deleteᵗ es i)
map-deleteᵗ ρ (x ∷ es) (here refl) = refl
map-deleteᵗ ρ (x ∷ es) (there i)   = cong ((x ⋯ ρ) ∷_) (map-deleteᵗ ρ es i)

------------------------------------------------------------------------
-- The packaged result.
------------------------------------------------------------------------

record Focused (m k : ℕ) (B₁ B₂ : BindGroup) (e : Tm k) : Set where
  constructor mkFocused
  field
    {finner} : ℕ
    ftel : TTel (sum B₁ + sum B₂ + m) finner
    ρf   : k →ᵣ finner
    fthr : List (Tm finner)

  e′ : Tm finner
  e′ = e ⋯ ρf

  frest : Proc finner
  frest = parsᵗ fthr

  focused : Proc m
  focused = ν B₁ B₂ (plugᵗ ftel (⟪ e′ ⟫ ∥ frest))

focus-≋ :
  ∀ {m q k} (t₁ : TTel m q) (B₁ B₂ : BindGroup)
    (t₂ : TTel (sum B₁ + sum B₂ + q) k)
    (es : List (Tm k)) {e : Tm k} (i : e ∈ es) →
  plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) (parsᵗ es)
    ≋ ν B₁ B₂ (plugᵗ (bubTelᵗ (sum B₁ + sum B₂) t₁ t₂)
                     (⟪ e ⋯ bubρᵗ (sum B₁ + sum B₂) t₁ t₂ ⟫
                        ∥ parsᵗ (map (_⋯ bubρᵗ (sum B₁ + sum B₂) t₁ t₂) (deleteᵗ es i))))
focus-≋ t₁ B₁ B₂ t₂ es {e} i =
  node-to-frontᵗ B₁ B₂ t₁ t₂ (parsᵗ es)
    ◅◅ ≡→≋ᵗ (cong (λ Y → ν B₁ B₂ (plugᵗ u Y)) (pars-⋯ₚᵗ es ρ))
    ◅◅ ν-cong (plug-congᵗ u (pars-∈ᵗ (map (_⋯ ρ) es) (∈-mapᵗ ρ i)))
    ◅◅ ≡→≋ᵗ (cong (λ zs → ν B₁ B₂ (plugᵗ u (⟪ e ⋯ ρ ⟫ ∥ parsᵗ zs))) (map-deleteᵗ ρ es i))
  where
    b = sum B₁ + sum B₂
    u = bubTelᵗ b t₁ t₂
    ρ = bubρᵗ b t₁ t₂

focus :
  ∀ {m q k} (t₁ : TTel m q) (B₁ B₂ : BindGroup)
    (t₂ : TTel (sum B₁ + sum B₂ + q) k)
    (es : List (Tm k)) {e : Tm k} (i : e ∈ es) →
  Σ[ F ∈ Focused m k B₁ B₂ e ]
    plugᵗ (t₁ ++ᵗᵗ tνᵗ B₁ B₂ t₂) (parsᵗ es) ≋ Focused.focused F
focus t₁ B₁ B₂ t₂ es i =
  mkFocused (bubTelᵗ b t₁ t₂) (bubρᵗ b t₁ t₂) (map (_⋯ bubρᵗ b t₁ t₂) (deleteᵗ es i))
  , focus-≋ t₁ B₁ B₂ t₂ es i
  where b = sum B₁ + sum B₂

------------------------------------------------------------------------
-- Choosing a node of a telescope, and the prenex corollary.
------------------------------------------------------------------------

data TelAt : ∀ {m k} → TTel m k → Set where
  here  : ∀ {m k} {B₁ B₂ : BindGroup} {t : TTel (sum B₁ + sum B₂ + m) k} →
          TelAt (tνᵗ B₁ B₂ t)
  there : ∀ {m k} {B₁ B₂ : BindGroup} {t : TTel (sum B₁ + sum B₂ + m) k} →
          TelAt t → TelAt (tνᵗ B₁ B₂ t)

record Split {m k : ℕ} (t : TTel m k) : Set where
  constructor mkSplit
  field
    {mid}   : ℕ
    pre     : TTel m mid
    G₁ G₂   : BindGroup
    post    : TTel (sum G₁ + sum G₂ + mid) k
    split-≡ : t ≡ pre ++ᵗᵗ tνᵗ G₁ G₂ post

splitAtᵗ : ∀ {m k} (t : TTel m k) → TelAt t → Split t
splitAtᵗ (tνᵗ B₁ B₂ t) here      = mkSplit []ᵗ B₁ B₂ t refl
splitAtᵗ (tνᵗ B₁ B₂ t) (there p) with splitAtᵗ t p
... | mkSplit pre G₁ G₂ post eq = mkSplit (tνᵗ B₁ B₂ pre) G₁ G₂ post (cong (tνᵗ B₁ B₂) eq)

focus-prenexᵗ :
  ∀ {m} (P : Proc m) (p : TelAt (tel (prenexᵗ P)))
    {e : Tm (inner (prenexᵗ P))} (i : e ∈ thr (prenexᵗ P)) →
  let s = splitAtᵗ (tel (prenexᵗ P)) p in
  Σ[ F ∈ Focused m (inner (prenexᵗ P)) (Split.G₁ s) (Split.G₂ s) e ]
    P ≋ Focused.focused F
focus-prenexᵗ P p {e} i =
  proj₁ FC
  , (prenex-soundᵗ P
      ◅◅ ≡→≋ᵗ (cong (λ t → plugᵗ t (parsᵗ (thr (prenexᵗ P)))) (Split.split-≡ s))
      ◅◅ proj₂ FC)
  where
    s  = splitAtᵗ (tel (prenexᵗ P)) p
    FC = focus (Split.pre s) (Split.G₁ s) (Split.G₂ s) (Split.post s)
               (thr (prenexᵗ P)) i
