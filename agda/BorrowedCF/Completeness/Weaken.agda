-- | ALGORITHMIC WEAKENING.
--
--   A derivation under γ₁ can be replayed under any larger structure γ₂ (γ₁ ≼ γ₂),
--   as long as γ₂ is linear.  Term, mode, type, effect and both counters are
--   unchanged; the CONSTRAINT SET moves, in the subcontext premises `_∶_≼_↑ Δ₀` of
--   the nine structural rules and in the mobility constraints of A-Abs.
--
--   Since C10 the ≼ premises generate constraints, so weakening can only be stated
--   relative to a solution: the derivation lives over a context Γ̂ that still holds
--   unification variables, while the weakening and the linearity fact are known on
--   the SOLVED context Γ, with `Approx Γ̂ Γ σ` connecting them.  Each rule's premise
--   is brought down to Γ by `≼↑-sound` + `≼-ctx-≃`, weakened there by the canonical
--   split, and lifted back to Γ̂ by `≼↑-complete`.
--
--   The module is parametrised over the canonical-split lemmas (agent C1); see
--   `Weaken/Instance.agda` for the instantiation.
module BorrowedCF.Completeness.Weaken where

open import Data.Fin.Subset as S renaming (⊥ to ⁅⁆)
open import Data.Fin.Subset.Properties renaming (∉⊥ to ∉⁅⁆; ⊥⊆ to ⁅⁆⊆)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All

open import BorrowedCF.Prelude
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Context
open import BorrowedCF.Context.Domain
open import BorrowedCF.Terms hiding (_↑)
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved
open import BorrowedCF.Completeness.Base
open import BorrowedCF.Completeness.Sub.Base using (Approx; approx-⸴; unrCx-approx)
open import BorrowedCF.Completeness.Weaken.Support

import BorrowedCF.Completeness.Sub as Sub
import BorrowedCF.Context.Substitution as 𝐂

open Nat.Variables

private variable
  Γ̂ : Ctx n
  Δ₀ : CSet

-- | `LinStruct Γ γ` is a Π-type, so neither Γ nor γ can be recovered from it by
--   unification; every use of a `lin-*` lemma would leave them as unsolved metas.
--   Wrapping it in a record makes the type former injective, which is all the
--   elaborator needs.
record LinBox {n} (Γ : Ctx n) (γ : Struct n) : Set where
  constructor box
  field unbox : LinStruct Γ γ

open LinBox public

-- | The constraint set a derivation emits, and the one a subcontext premise emits.
--   Reading them off makes every `All.++⁻` below independent of the constructor's
--   implicit-argument order.
csetOf : ∀ {n} {Γ : Ctx n} {γ : Struct n} {m k : ℕ} {ξ : Mode}
           {e : Tm n} {T : 𝕋} {ϵ : Eff} {Δ : CSet} →
  Γ ; γ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k → CSet
csetOf {Δ = Δ} _ = Δ

csetOf≼ : ∀ {n} {Γ : Ctx n} {α β : Struct n} {Δ₀ : CSet} → Γ ∶ α ≼ β ↑ Δ₀ → CSet
csetOf≼ {Δ₀ = Δ₀} _ = Δ₀

module Weakening
  -- | The canonical split (agent C1): if SOME split of γ separates the variables of
  --   X from those of Y, then the canonical one `(γ ↓ X) , (γ ↓ Y)` does too.
  (canon-split :
     ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (d : Dir) →
     LinStruct Γ γ →
     Γ ∶ join d α β ≼ γ →
     dom α ⊆ X → dom β ⊆ Y →
     (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
     (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
     Γ ∶ join d (γ ↓ X) (γ ↓ Y) ≼ γ)
  (canon-split-ps :
     ∀ {n} {Γ : Ctx n} {γ α β : Struct n} {X Y : Subset n} (p/s : ParSeq) →
     LinStruct Γ γ →
     Γ ∶ join p/s α β ≼ γ →
     dom α ⊆ X → dom β ⊆ Y →
     (∀ x → x ∈ X → x ∉ dom α → Unr (Γ ﹫ x)) →
     (∀ x → x ∈ Y → x ∉ dom β → Unr (Γ ﹫ x)) →
     Γ ∶ join p/s (γ ↓ X) (γ ↓ Y) ≼ γ)
  (lin-↓ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {X : Subset n} →
     LinBox Γ γ → LinBox Γ (γ ↓ X))
  (lin-bind : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T : 𝕋} (d : Dir) →
     LinBox Γ γ → LinBox (T ⸴ Γ) (join d (` zero) (𝐂.wk γ)))
  (lin-bind-ps : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T : 𝕋} (p/s : ParSeq) →
     LinBox Γ γ → LinBox (T ⸴ Γ) (join p/s (` zero) (𝐂.wk γ)))
  (lin-bind₂ : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T₁ T₂ : 𝕋} (p/s : ParSeq) (d : Dir) →
     LinBox Γ γ →
     LinBox (T₁ ⸴ T₂ ⸴ Γ) (join p/s (join d (` zero) (` suc zero)) (𝐂.wk (𝐂.wk γ))))
  (lin-bind-rec : ∀ {n} {Γ : Ctx n} {γ : Struct n} {T₁ T₂ : 𝕋} →
     LinBox Γ γ →
     LinBox (T₁ ⸴ T₂ ⸴ Γ) ((` zero) ∥ (` suc zero) ∥ 𝐂.wk (𝐂.wk γ)))
  where

  ----------------------------------------------------------------------
  -- Transporting a split along ≼, on the SOLVED context
  ----------------------------------------------------------------------

  -- The canonical split of γ₂ exists whenever the canonical split of γ₁ does.
  -- We hand `canon-split` the subsets X ∩ dom γ₂ and Y ∩ dom γ₂ (which restrict γ₂
  -- to the same thing, by `↓-∩`); that way its Unr side conditions only speak about
  -- variables of γ₂, and those are exactly the ones `≼⇒extra-Unr` covers.
  split-weaken : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} (d : Dir) →
    LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ →
    Γ ∶ join d (γ₁ ↓ X) (γ₁ ↓ Y) ≼ γ₁ →
    Γ ∶ join d (γ₂ ↓ X) (γ₂ ↓ Y) ≼ γ₂
  split-weaken {Γ = Γ} {γ₁} {γ₂} {X} {Y} d lin w h =
    subst₂ (λ a b → Γ ∶ join d a b ≼ γ₂) (↓-∩ γ₂ ⊆-refl) (↓-∩ γ₂ ⊆-refl)
      (canon-split d (unbox lin) (≼-trans h w) (dm X) (dm Y) (un X) (un Y))
    where
      dm : ∀ (Z : Subset _) → dom (γ₁ ↓ Z) ⊆ (Z ∩ dom γ₂)
      dm Z z∈ = x∈p∩q⁺ (↓-dom γ₁ Z z∈ , ≼⇒dom⊆ w (↓-dom⊆dom γ₁ z∈))

      un : ∀ (Z : Subset _) → ∀ x → x ∈ (Z ∩ dom γ₂) → x ∉ dom (γ₁ ↓ Z) → Unr (Γ ﹫ x)
      un Z x x∈ x∉ =
        extra-unr w (proj₂ (x∈p∩q⁻ Z (dom γ₂) x∈))
                    (∉-dom-↓ γ₁ (proj₁ (x∈p∩q⁻ Z (dom γ₂) x∈)) x∉)

  split-weaken-ps : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} (p/s : ParSeq) →
    LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ →
    Γ ∶ join p/s (γ₁ ↓ X) (γ₁ ↓ Y) ≼ γ₁ →
    Γ ∶ join p/s (γ₂ ↓ X) (γ₂ ↓ Y) ≼ γ₂
  split-weaken-ps {Γ = Γ} {γ₁} {γ₂} {X} {Y} p/s lin w h =
    subst₂ (λ a b → Γ ∶ join p/s a b ≼ γ₂) (↓-∩ γ₂ ⊆-refl) (↓-∩ γ₂ ⊆-refl)
      (canon-split-ps p/s (unbox lin) (≼-trans h w) (dm X) (dm Y) (un X) (un Y))
    where
      dm : ∀ (Z : Subset _) → dom (γ₁ ↓ Z) ⊆ (Z ∩ dom γ₂)
      dm Z z∈ = x∈p∩q⁺ (↓-dom γ₁ Z z∈ , ≼⇒dom⊆ w (↓-dom⊆dom γ₁ z∈))

      un : ∀ (Z : Subset _) → ∀ x → x ∈ (Z ∩ dom γ₂) → x ∉ dom (γ₁ ↓ Z) → Unr (Γ ﹫ x)
      un Z x x∈ x∉ =
        extra-unr w (proj₂ (x∈p∩q⁻ Z (dom γ₂) x∈))
                    (∉-dom-↓ γ₁ (proj₁ (x∈p∩q⁻ Z (dom γ₂) x∈)) x∉)

  -- `join L` is `_;_`, so A-Seq is the d = L instance.
  split-weaken-seq : ∀ {n} {Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} →
    LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ →
    Γ ∶ (γ₁ ↓ X) ; (γ₁ ↓ Y) ≼ γ₁ →
    Γ ∶ (γ₂ ↓ X) ; (γ₂ ↓ Y) ≼ γ₂
  split-weaken-seq = split-weaken L

  ----------------------------------------------------------------------
  -- Algorithmic weakening, relative to a fixed solution σ
  ----------------------------------------------------------------------

  module _ {σ : UV.Sub} (Sσ : Solving σ) where

    -- A solved subcontext premise over Γ̂ is a plain subcontext fact over Γ.
    ≼↑⇒≼ : ∀ {n} {Γ̂ Γ : Ctx n} {α β : Struct n} {Δ₀ : CSet} →
      Approx Γ̂ Γ σ → SolvedΔ Δ₀ σ → Γ̂ ∶ α ≼ β ↑ Δ₀ → Γ ∶ α ≼ β
    ≼↑⇒≼ {Γ̂ = Γ̂} {Γ = Γ} ap SΔ₀ d =
      ≼-ctx-≃ (approx⇒ctxEq σ Γ̂ Γ ap) (≼↑-sound Sσ SΔ₀ d)

    -- A-Var / A-Const / A-LSplit / A-RSplit: just post-compose with the weakening.
    lift-≼ : ∀ {n} {Γ̂ Γ : Ctx n} {α γ₁ γ₂ : Struct n} {Δ₀ : CSet} →
      Approx Γ̂ Γ σ → Γ ∶ γ₁ ≼ γ₂ → SolvedΔ Δ₀ σ → Γ̂ ∶ α ≼ γ₁ ↑ Δ₀ →
      Σ[ Δ₀′ ∈ CSet ] (Γ̂ ∶ α ≼ γ₂ ↑ Δ₀′) × SolvedΔ Δ₀′ σ
    lift-≼ ap w SΔ₀ ≤γ = Sub.≼↑-complete Sσ ap (≼-trans (≼↑⇒≼ ap SΔ₀ ≤γ) w)

    -- The two-subterm rules: down to Γ, canonical split, back up to Γ̂.
    lift-split : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} {Δ₀ : CSet}
      (d : Dir) →
      Approx Γ̂ Γ σ → LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → SolvedΔ Δ₀ σ →
      Γ̂ ∶ join d (γ₁ ↓ X) (γ₁ ↓ Y) ≼ γ₁ ↑ Δ₀ →
      Σ[ Δ₀′ ∈ CSet ] (Γ̂ ∶ join d (γ₂ ↓ X) (γ₂ ↓ Y) ≼ γ₂ ↑ Δ₀′) × SolvedΔ Δ₀′ σ
    lift-split d ap lin w SΔ₀ ≤γ =
      Sub.≼↑-complete Sσ ap (split-weaken d lin w (≼↑⇒≼ ap SΔ₀ ≤γ))

    lift-split-ps : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} {Δ₀ : CSet}
      (p/s : ParSeq) →
      Approx Γ̂ Γ σ → LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → SolvedΔ Δ₀ σ →
      Γ̂ ∶ join p/s (γ₁ ↓ X) (γ₁ ↓ Y) ≼ γ₁ ↑ Δ₀ →
      Σ[ Δ₀′ ∈ CSet ] (Γ̂ ∶ join p/s (γ₂ ↓ X) (γ₂ ↓ Y) ≼ γ₂ ↑ Δ₀′) × SolvedΔ Δ₀′ σ
    lift-split-ps p/s ap lin w SΔ₀ ≤γ =
      Sub.≼↑-complete Sσ ap (split-weaken-ps p/s lin w (≼↑⇒≼ ap SΔ₀ ≤γ))

    lift-split-seq : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {X Y : Subset n} {Δ₀ : CSet} →
      Approx Γ̂ Γ σ → LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ → SolvedΔ Δ₀ σ →
      Γ̂ ∶ (γ₁ ↓ X) ; (γ₁ ↓ Y) ≼ γ₁ ↑ Δ₀ →
      Σ[ Δ₀′ ∈ CSet ] (Γ̂ ∶ (γ₂ ↓ X) ; (γ₂ ↓ Y) ≼ γ₂ ↑ Δ₀′) × SolvedΔ Δ₀′ σ
    lift-split-seq = lift-split L

    -- The UnrCx premises of A-Abs / A-AbsRec: Unr is reflected, so they travel to
    -- Γ, get weakened there, and come back.
    unr-weaken : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} →
      Approx Γ̂ Γ σ → Γ ∶ γ₁ ≼ γ₂ → UnrCx Γ̂ γ₁ → UnrCx Γ̂ γ₂
    unr-weaken {Γ̂ = Γ̂} {Γ = Γ} ap w U =
      unrCx-approx {σ = σ} ap (unrCx-weaken w (unrCx-fwd σ Γ̂ Γ ap U))

    ----------------------------------------------------------------------

    alg-weaken-box : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {m k : ℕ} {ξ : Mode}
                       {e : Tm n} {T : 𝕋} {ϵ : Eff} {Δ : CSet} →
      Approx Γ̂ Γ σ → LinBox Γ γ₂ → Γ ∶ γ₁ ≼ γ₂ →
      Γ̂ ; γ₁ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k →
      SolvedΔ Δ σ →
      Σ[ Δ′ ∈ CSet ] (Γ̂ ; γ₂ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ′ / k) × SolvedΔ Δ′ σ

    alg-weaken-box ap lin w (A-Var ≤γ) SΔ
      using Δ₀′ , ≤γ′ , S₀ ← lift-≼ ap w SΔ ≤γ
      = Δ₀′ , A-Var ≤γ′ , S₀
    alg-weaken-box ap lin w (A-Const ≤γ Ac ⊢c) SΔ
      using Δ₀′ , ≤γ′ , S₀ ← lift-≼ ap w SΔ ≤γ
      = Δ₀′ , A-Const ≤γ′ Ac ⊢c , S₀
    alg-weaken-box ap lin w (A-LSplit ≤γ ¬skips) SΔ
      using Δ₀′ , ≤γ′ , S₀ ← lift-≼ ap w SΔ ≤γ
      = Δ₀′ , A-LSplit ≤γ′ ¬skips , S₀
    alg-weaken-box ap lin w (A-RSplit ≤γ ¬skips) SΔ
      using Δ₀′ , ≤γ′ , S₀ ← lift-≼ ap w SΔ ≤γ
      = Δ₀′ , A-RSplit ≤γ′ ¬skips , S₀

    alg-weaken-box ap lin w (A-App {a = a} ec ≤γ x y) SΔ
      using S₀ , S₁₂ ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using S₁ , S₂ ← All.++⁻ (csetOf x) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split (Arr.dir a) ap lin w S₀ ≤γ
      using Δ₁′ , x′ , tr₁ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x S₁
      using Δ₂′ , y′ , tr₂ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) y S₂
      = Δ₀′ ++ Δ₁′ ++ Δ₂′
      , A-App ec ≤γ′ x′ y′
      , All.++⁺ tr₀ (All.++⁺ tr₁ tr₂)

    alg-weaken-box ap lin w (A-Seq unr-T ≤γ x y) SΔ
      using S₀ , S₁₂ ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using S₁ , S₂ ← All.++⁻ (csetOf x) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split-seq ap lin w S₀ ≤γ
      using Δ₁′ , x′ , tr₁ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x S₁
      using Δ₂′ , y′ , tr₂ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) y S₂
      = Δ₀′ ++ Δ₁′ ++ Δ₂′
      , A-Seq unr-T ≤γ′ x′ y′
      , All.++⁺ tr₀ (All.++⁺ tr₁ tr₂)

    alg-weaken-box ap lin w (A-LetPair {d = d} p/s ≤γ x y) SΔ
      using S₀ , S₁₂ ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using S₁ , S₂ ← All.++⁻ (csetOf x) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split-ps p/s ap lin w S₀ ≤γ
      using Δ₁′ , x′ , tr₁ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x S₁
      using Δ₂′ , y′ , tr₂ ← alg-weaken-box (approx-⸴ ≃-refl (approx-⸴ ≃-refl ap))
                              (lin-bind₂ p/s d (lin-↓ lin))
                              (≼-join p/s (≼-refl ≈-refl) (wk-≼ (wk-≼ (↓-mono-≼ w)))) y S₂
      = Δ₀′ ++ Δ₁′ ++ Δ₂′
      , A-LetPair p/s ≤γ′ x′ y′
      , All.++⁺ tr₀ (All.++⁺ tr₁ tr₂)

    alg-weaken-box ap lin w (A-Let p/s ≤γ x y) SΔ
      using S₀ , S₁₂ ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using S₁ , S₂ ← All.++⁻ (csetOf x) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split-ps p/s ap lin w S₀ ≤γ
      using Δ₁′ , x′ , tr₁ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x S₁
      using Δ₂′ , y′ , tr₂ ← alg-weaken-box (approx-⸴ ≃-refl ap)
                              (lin-bind-ps p/s (lin-↓ lin))
                              (≼-join p/s (≼-refl ≈-refl) (wk-≼ (↓-mono-≼ w))) y S₂
      = Δ₀′ ++ Δ₁′ ++ Δ₂′
      , A-Let p/s ≤γ′ x′ y′
      , All.++⁺ tr₀ (All.++⁺ tr₁ tr₂)

    alg-weaken-box ap lin w (A-Case p/s ≤γ x y₁ y₂) (eq ∷ SΔ)
      using S₀ , Srest ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using Sc , S₁₂ ← All.++⁻ (csetOf x) Srest
      using S₁ , S₂ ← All.++⁻ (csetOf y₁) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split-ps p/s ap lin w S₀ ≤γ
      using Δ′ , x′ , tr ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x Sc
      using Δ₁′ , y₁′ , tr₁ ← alg-weaken-box (approx-⸴ ≃-refl ap)
                               (lin-bind-ps p/s (lin-↓ lin))
                               (≼-join p/s (≼-refl ≈-refl) (wk-≼ (↓-mono-≼ w))) y₁ S₁
      using Δ₂′ , y₂′ , tr₂ ← alg-weaken-box (approx-⸴ ≃-refl ap)
                               (lin-bind-ps p/s (lin-↓ lin))
                               (≼-join p/s (≼-refl ≈-refl) (wk-≼ (↓-mono-≼ w))) y₂ S₂
      = _ ∷ Δ₀′ ++ Δ′ ++ Δ₁′ ++ Δ₂′
      , A-Case p/s ≤γ′ x′ y₁′ y₂′
      , eq ∷ All.++⁺ tr₀ (All.++⁺ tr (All.++⁺ tr₁ tr₂))

    alg-weaken-box {Γ̂ = Γ̂} {γ₁ = γ₁} {γ₂ = γ₂} ap lin w (A-Abs {a = a} unr-Γ ϵ≤ x refl) SΔ
      using Sm , Sb ← All.++⁻ (mobConstraints (Arr.mob a) Γ̂ γ₁) SΔ
      using Δ″ , x′ , tr ← alg-weaken-box (approx-⸴ ≃-refl ap)
                            (lin-bind (Arr.dir a) lin)
                            (≼-join (Arr.dir a) (≼-refl ≈-refl) (wk-≼ w)) x Sb
      = mobConstraints (Arr.mob a) Γ̂ γ₂ ++ Δ″
      , A-Abs (unr-weaken ap w ∘ unr-Γ) ϵ≤ x′ refl
      , All.++⁺ (mobConstraints-weaken (Arr.mob a) σ Γ̂ ap w Sm) tr

    alg-weaken-box ap lin w (A-AbsRec unr-Γ unr-a ϵ≤ x) SΔ
      using Δ″ , x′ , tr ← alg-weaken-box (approx-⸴ ≃-refl (approx-⸴ ≃-refl ap))
                            (lin-bind-rec lin)
                            (≼-cong-∥ (≼-refl ≈-refl) (wk-≼ (wk-≼ w))) x SΔ
      = Δ″ , A-AbsRec (unr-weaken ap w unr-Γ) unr-a ϵ≤ x′ , tr

    alg-weaken-box ap lin w (A-Pair p/s ≤γ seq⇒pure x y) SΔ
      using S₀ , S₁₂ ← All.++⁻ (csetOf≼ ≤γ) SΔ
      using S₁ , S₂ ← All.++⁻ (csetOf x) S₁₂
      using Δ₀′ , ≤γ′ , tr₀ ← lift-split-ps p/s ap lin w S₀ ≤γ
      using Δ₁′ , x′ , tr₁ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) x S₁
      using Δ₂′ , y′ , tr₂ ← alg-weaken-box ap (lin-↓ lin) (↓-mono-≼ w) y S₂
      = Δ₀′ ++ Δ₁′ ++ Δ₂′
      , A-Pair p/s ≤γ′ seq⇒pure x′ y′
      , All.++⁺ tr₀ (All.++⁺ tr₁ tr₂)

    alg-weaken-box ap lin w (A-Inj x) SΔ
      using Δ′ , x′ , tr ← alg-weaken-box ap lin w x SΔ
      = Δ′ , A-Inj x′ , tr

    alg-weaken-box ap lin w (A-Check x) (eq ∷ SΔ)
      using Δ′ , x′ , tr ← alg-weaken-box ap lin w x SΔ
      = _ ∷ Δ′ , A-Check x′ , eq ∷ tr

    alg-weaken-box ap lin w (A-Ann cf x) SΔ
      using Δ′ , x′ , tr ← alg-weaken-box ap lin w x SΔ
      = Δ′ , A-Ann cf x′ , tr

    -- | ALGORITHMIC WEAKENING (the deliverable).
    alg-weaken : ∀ {n} {Γ̂ Γ : Ctx n} {γ₁ γ₂ : Struct n} {m k : ℕ} {ξ : Mode}
                   {e : Tm n} {T : 𝕋} {ϵ : Eff} {Δ : CSet} →
      Approx Γ̂ Γ σ →
      LinStruct Γ γ₂ →
      Γ ∶ γ₁ ≼ γ₂ →
      Γ̂ ; γ₁ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ / k →
      SolvedΔ Δ σ →
      Σ[ Δ′ ∈ CSet ] (Γ̂ ; γ₂ / m ⊢[ ξ ] e ∶ T ∣ ϵ ↑ Δ′ / k) × SolvedΔ Δ′ σ
    alg-weaken ap lin = alg-weaken-box ap (box lin)
