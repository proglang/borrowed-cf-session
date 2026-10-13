-- | Phase 3 helper shared by the ν-leaves that *shrink* a binder group
--   (`ForwardSoup/PLAN.md`, §4, Phase 3, items 3, 5 and 6).
--
--   `R-Com`, `R-Drop` and `R-Discard` all reduce a restriction whose head
--   bind group loses its first borrow,
--
--     ν (suc b₁ ∷ B₁) B₂ (… (` 0F) … ∥ (P ⋯ₚ ρ))  ─→ₚ  ν (b₁ ∷ B₁) B₂ (… ∥ P)
--
--   so all three need the same two facts about the binder environment of
--   `LocalImage/Frame.agda`: dropping the head borrow shifts the environment
--   by one (`Ub-drop`, `UB-env-drop`, and the `weakenᵣ-bindEnv-coh*` family
--   built from them), and — except for the `R-Drop` case, where the head flag
--   flips from `drop` to `acq` — leaves the flag list of the bound channel
--   alone (`UB-flags-drop`, `bindChannel-drop`, `bindChannel-last`).
--
--   The `Fin.splitAt` readers `split-left`/`split-right`/`split-ambient` and
--   the two `_↑*_` laws `lift*-↑ˡ`/`lift*-↑ʳ` used to build the `R-Com`
--   weakening arithmetic live here too; they were private to `Local/Com.agda`.
module BorrowedCF.Simulation.ForwardSoup.Local.BindDrop where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source
import BorrowedCF.Terms.BaseSoup as SoupTerm

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
  using (OrientedChannel; physicalEndpoint; orientChannel)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Frame
  using (bindEnv; bindChannel)

open Fin.Patterns

private
  variable
    a b d k n : ℕ

------------------------------------------------------------------------
-- Lifting a renaming past a block of variables.

lift*-↑ˡ :
  ∀ {a b : ℕ} (rho : 𝔽 a → 𝔽 b) j (y : 𝔽 j) →
  Source._↑*_ rho j (y ↑ˡ a) ≡ y ↑ˡ b
lift*-↑ˡ rho (suc j) zero = refl
lift*-↑ˡ rho (suc j) (suc y) = cong suc (lift*-↑ˡ rho j y)

lift*-↑ʳ :
  ∀ {a b : ℕ} (rho : 𝔽 a → 𝔽 b) j (w : 𝔽 a) →
  Source._↑*_ rho j (j ↑ʳ w) ≡ j ↑ʳ rho w
lift*-↑ʳ rho zero w = refl
lift*-↑ʳ rho (suc j) w = cong suc (lift*-↑ʳ rho j w)

------------------------------------------------------------------------
-- Reading off a two-step `Fin.splitAt`.

split-left :
  ∀ a c {k} {x : 𝔽 (a + c + k)} {z : 𝔽 (a + c)} {v : 𝔽 a} →
  Fin.splitAt (a + c) x ≡ inj₁ z →
  Fin.splitAt a z ≡ inj₁ v →
  (v ↑ˡ c) ↑ˡ k ≡ x
split-left a c {k} {x} {z} {v} outer inner =
  cong (λ s → Fin.join a c s ↑ˡ k) (sym inner)
  ■ cong (λ t → t ↑ˡ k) (Fin.join-splitAt a c z)
  ■ cong (Fin.join (a + c) k) (sym outer)
  ■ Fin.join-splitAt (a + c) k x

split-right :
  ∀ a c {k} {x : 𝔽 (a + c + k)} {z : 𝔽 (a + c)} {w : 𝔽 c} →
  Fin.splitAt (a + c) x ≡ inj₁ z →
  Fin.splitAt a z ≡ inj₂ w →
  (a ↑ʳ w) ↑ˡ k ≡ x
split-right a c {k} {x} {z} {w} outer inner =
  cong (λ s → Fin.join a c s ↑ˡ k) (sym inner)
  ■ cong (λ t → t ↑ˡ k) (Fin.join-splitAt a c z)
  ■ cong (Fin.join (a + c) k) (sym outer)
  ■ Fin.join-splitAt (a + c) k x

split-ambient :
  ∀ p {k} {x : 𝔽 (p + k)} {y : 𝔽 k} →
  Fin.splitAt p x ≡ inj₂ y →
  p ↑ʳ y ≡ x
split-ambient p {k} {x} outer =
  cong (Fin.join p k) (sym outer) ■ Fin.join-splitAt p k x

------------------------------------------------------------------------
-- Dropping the head borrow of a group.

Ub-drop :
  ∀ b {d : ℕ} (c : 𝔽 d) (e₂ : SoupTerm.Tm d) (x : 𝔽 (suc b)) →
  Translation.Ub[ suc (suc b) ] (SoupTerm.* , c , e₂) (Fin.suc x) ≡
  Translation.Ub[ suc b ] (SoupTerm.* , c , e₂) x
Ub-drop zero c e₂ zero = refl
Ub-drop (suc b) c e₂ zero = refl
Ub-drop (suc b) c e₂ (suc x) = Ub-drop b c e₂ x

UB-env-drop :
  ∀ b (B : Typed.BindGroup) {d : ℕ} (r c : 𝔽 d) (e₂ : SoupTerm.Tm d)
    (x : 𝔽 (sum (suc b ∷ B))) →
  proj₁ (Translation.UB[ suc (suc b) ∷ B ] r (SoupTerm.* , c , e₂))
    (Fin.suc x) ≡
  proj₁ (Translation.UB[ suc b ∷ B ] r (SoupTerm.* , c , e₂)) x
UB-env-drop zero [] r c e₂ 0F = refl
UB-env-drop (suc b) [] r c e₂ 0F = refl
UB-env-drop (suc b) [] r c e₂ (suc x) = UB-env-drop b [] r c e₂ x
UB-env-drop b (b′ ∷ B) r c e₂ x
  with Translation.UBFrom 1 (b′ ∷ B) r
         (SoupTerm.`phi (r , 0) , c , e₂)
     | Fin.splitAt (suc b) x
... | sigma , flags | inj₁ y = Ub-drop b c (SoupTerm.`phi (r , 0)) y
... | sigma , flags | inj₂ y = refl

UB-flags-drop :
  ∀ b (B : Typed.BindGroup) {d : ℕ} (r c : 𝔽 d)
    (e₁ e₂ : SoupTerm.Tm d) →
  proj₂ (Translation.UB[ suc (suc b) ∷ B ] r (e₁ , c , e₂)) ≡
  proj₂ (Translation.UB[ suc b ∷ B ] r (e₁ , c , e₂))
UB-flags-drop b [] r c e₁ e₂ = refl
UB-flags-drop b (b′ ∷ B) r c e₁ e₂
  with Translation.UBFrom 1 (b′ ∷ B) r
         (SoupTerm.`phi (r , 0) , c , e₂)
... | sigma , flags = refl

-- The `b₁ = 0` analogue, for a group with a non-empty tail: the two
-- environments share the very same `UBFrom 1 B …` tail block — only the head
-- block shrinks from `Ub[ 1 ]` to `Ub[ 0 ]`, and `Fin.splitAt 1 (suc y)` and
-- `Fin.splitAt 0 y` are both `inj₂ y`.
UB-env-drop-last :
  ∀ (b′ : ℕ) (B : Typed.BindGroup) {d : ℕ} (r c : 𝔽 d)
    (e₂ : SoupTerm.Tm d) (y : 𝔽 (sum (0 ∷ b′ ∷ B))) →
  proj₁ (Translation.UB[ 1 ∷ b′ ∷ B ] r (SoupTerm.* , c , e₂))
    (Fin.suc y) ≡
  proj₁ (Translation.UB[ 0 ∷ b′ ∷ B ] r (SoupTerm.* , c , e₂)) y
UB-env-drop-last b′ B r c e₂ y
  with Translation.UBFrom 1 (b′ ∷ B) r
         (SoupTerm.`phi (r , 0) , c , e₂)
... | sigma , flags = refl

------------------------------------------------------------------------
-- Shifting a concatenated environment by one.

block-shift :
  ∀ {p q d : ℕ} (bL : Translation.Env (suc p) d)
    (bR : Translation.Env p d) (rest : Translation.Env q d) →
  ((y : 𝔽 p) → bL (Fin.suc y) ≡ bR y) →
  (i : 𝔽 (p + q)) →
  (bL Translation.++ₛ rest) (Fin.suc i) ≡ (bR Translation.++ₛ rest) i
block-shift {p = p} bL bR rest coherent i with Fin.splitAt p i
... | inj₁ y = coherent y
... | inj₂ z = refl

------------------------------------------------------------------------
-- The three binder-environment coherences of `R-Drop`/`R-Discard`.
--
--   The source process is renamed by `Source.weakenᵣ`, which is `suc` on
--   variables; the head borrow of the first group is exactly the variable it
--   inserts.

private
  binderEnv :
    (B : Typed.BindGroup) {d : ℕ} (endpoint : 𝔽 d) →
    Translation.Env (sum B) d
  binderEnv B endpoint =
    proj₁ (Translation.UB[ B ] endpoint (SoupTerm.* , endpoint , SoupTerm.*))

-- Head group `suc (suc b′) ∷ B₁` ↦ `suc b′ ∷ B₁` (any tail).
weakenᵣ-bindEnv-coh :
  ∀ {b′ : ℕ} {B₁ B₂ : Typed.BindGroup} {channel : OrientedChannel n}
    {sigma : Translation.Env k (2 *ℕ n)}
    (x : 𝔽 (sum (suc b′ ∷ B₁) + sum B₂ + k)) →
  bindEnv (suc (suc b′) ∷ B₁) B₂ channel sigma (Source.weakenᵣ x) ≡
  bindEnv (suc b′ ∷ B₁) B₂ channel sigma x
weakenᵣ-bindEnv-coh {b′ = b′} {B₁ = B₁} {B₂ = B₂} {channel = channel}
  {sigma = sigma} x =
  block-shift
    (binderEnv (suc (suc b′) ∷ B₁) end₁ Translation.++ₛ binderEnv B₂ end₂)
    (binderEnv (suc b′ ∷ B₁) end₁ Translation.++ₛ binderEnv B₂ end₂)
    sigma
    (block-shift (binderEnv (suc (suc b′) ∷ B₁) end₁)
      (binderEnv (suc b′ ∷ B₁) end₁) (binderEnv B₂ end₂)
      (UB-env-drop b′ B₁ end₁ end₁ SoupTerm.*))
    x
  where
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

-- Head group `1 ∷ []` ↦ `0 ∷ []`: the head block disappears entirely.
weakenᵣ-bindEnv-coh-last :
  ∀ {B₂ : Typed.BindGroup} {channel : OrientedChannel n}
    {sigma : Translation.Env k (2 *ℕ n)}
    (x : 𝔽 (sum (0 ∷ []) + sum B₂ + k)) →
  bindEnv (1 ∷ []) B₂ channel sigma (Source.weakenᵣ x) ≡
  bindEnv (0 ∷ []) B₂ channel sigma x
weakenᵣ-bindEnv-coh-last {B₂ = B₂} {channel = channel} {sigma = sigma} x =
  block-shift
    (binderEnv (1 ∷ []) end₁ Translation.++ₛ binderEnv B₂ end₂)
    (binderEnv (0 ∷ []) end₁ Translation.++ₛ binderEnv B₂ end₂)
    sigma
    (block-shift (binderEnv (1 ∷ []) end₁) (binderEnv (0 ∷ []) end₁)
      (binderEnv B₂ end₂) (λ ()))
    x
  where
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

-- Head group `1 ∷ c′ ∷ B′` ↦ `0 ∷ c′ ∷ B′`: the `R-Drop` case.
weakenᵣ-bindEnv-coh-drop :
  ∀ {c′ : ℕ} {B′ B₂ : Typed.BindGroup} {channel : OrientedChannel n}
    {sigma : Translation.Env k (2 *ℕ n)}
    (x : 𝔽 (sum (0 ∷ c′ ∷ B′) + sum B₂ + k)) →
  bindEnv (1 ∷ c′ ∷ B′) B₂ channel sigma (Source.weakenᵣ x) ≡
  bindEnv (0 ∷ c′ ∷ B′) B₂ channel sigma x
weakenᵣ-bindEnv-coh-drop {c′ = c′} {B′ = B′} {B₂ = B₂} {channel = channel}
  {sigma = sigma} x =
  block-shift
    (binderEnv (1 ∷ c′ ∷ B′) end₁ Translation.++ₛ binderEnv B₂ end₂)
    (binderEnv (0 ∷ c′ ∷ B′) end₁ Translation.++ₛ binderEnv B₂ end₂)
    sigma
    (block-shift (binderEnv (1 ∷ c′ ∷ B′) end₁)
      (binderEnv (0 ∷ c′ ∷ B′) end₁) (binderEnv B₂ end₂)
      (UB-env-drop-last c′ B′ end₁ end₁ SoupTerm.*))
    x
  where
  end₁ = physicalEndpoint channel 0F
  end₂ = physicalEndpoint channel 1F

------------------------------------------------------------------------
-- The bound channel keeps its content in the two flag-preserving cases.

bindChannel-drop :
  ∀ {b′ : ℕ} {B₁ B₂ : Typed.BindGroup} {channel : OrientedChannel n} →
  bindChannel (suc (suc b′) ∷ B₁) B₂ channel ≡
  bindChannel (suc b′ ∷ B₁) B₂ channel
bindChannel-drop {b′ = b′} {B₁ = B₁} {B₂ = B₂} {channel = channel} =
  cong
    (λ flags →
      orientChannel (proj₂ channel)
        ( true
        , flags
        , proj₂ (Translation.UB[ B₂ ] (physicalEndpoint channel 1F)
                  ( SoupTerm.*
                  , physicalEndpoint channel 1F
                  , SoupTerm.*))
        ))
    (UB-flags-drop b′ B₁ (physicalEndpoint channel 0F)
      (physicalEndpoint channel 0F) SoupTerm.* SoupTerm.*)

bindChannel-last :
  ∀ {B₂ : Typed.BindGroup} {channel : OrientedChannel n} →
  bindChannel (1 ∷ []) B₂ channel ≡ bindChannel (0 ∷ []) B₂ channel
bindChannel-last = refl
