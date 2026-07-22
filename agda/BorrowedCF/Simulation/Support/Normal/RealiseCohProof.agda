-- | Proofs of the three ALIGNED realisation coherences stated by
--   `Normal.Realise`: `BswpThreadCoh`, `BswpThreadCohᵇ` and `FlipResidue`.
--
--   Architecture.  The alignment premises pin the positional decomposition
--   to the image decomposition by `shape-det`, after which everything is a
--   computation on the CONCRETE image data:
--
--   * the two `Bσ` laws are extracted for free from record equalities
--     between normal forms computed two ways — `law` from
--     `nf-endo` + `U-σ⋯` + `nf-prenex-image` (a base endo-renaming pushes
--     into the accumulated substitution), `law2` from
--     `U-⋯ₚ` + `plug-⋯ₚᵗ` + `nf-prenex-image` (a typed base renaming
--     re-telescopes the image);
--   * Factor's `bswapRen`/`dragRen` composites factor through `liftId`
--     over the tail block telescope, and their base parts match the
--     Congruence engine's composites by the toℕ specs of
--     `RealiseCohNat` (`Bridge.bridge-fwd`, `BridgeFlip.bridge-flip`);
--   * the leaf reconciles are exactly `subEqComm-gen` (block swap) and
--     `subEq-gen` (endpoint flip), transported along `canonₛ ≗ σB`;
--   * the backward swap inverts the forward one through the cast-conjugate
--     of the forward renaming (`asF-invol`);
--   * the flip's `~ᵩ` residue is produced by a `~ᵩ`-only drag of the
--     second sync nest (`drag-soundᵩ`, mirroring Factor's `drag-sound`
--     with `φφᵩ` only).
module BorrowedCF.Simulation.Support.Normal.RealiseCohProof where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
open import BorrowedCF.Processes.Typed using (BindGroup)
open import BorrowedCF.Processes.Untyped using (Flag)
open import BorrowedCF.Processes.Translation using (U[_]; UChan; syncs; ϕ[_])
open import BorrowedCF.Simulation.Support.TypedPrenex
open import BorrowedCF.Simulation.Support.Normal.Form
  using (Tel; []; tν; tφ; _++ᵗ_; NF; mkNF; tel; thr; inner)
open import BorrowedCF.Simulation.Support.Normal.Norm using (nf)
open import BorrowedCF.Simulation.Support.Normal.Image
  using (φTel; φTelᵣ; scope≡; σB; module νImage; Slot; sν; sφ; shape;
         shape-subst; shape-++ᵗ; shape-φTel; syncFlags)
open import BorrowedCF.Simulation.Support.Normal.Equiv using (liftId)
open import BorrowedCF.Simulation.Support.Normal.Shift
  using (shift1; shift2; liftId-cong; liftId-·; liftId-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.Endo
  using (liftId-id; ++ᵗ-idʳ; ++ᵗ-assoc; nf-endo)
open import BorrowedCF.Simulation.Support.Normal.Nat
  using (map-fuse; subst-++; subst-■; NF-≡; map-++ᴸ)
open import BorrowedCF.Simulation.Support.Normal.Bubble
  using (map-⋯-cong; map-⋯-id; bubφ)
open import BorrowedCF.Simulation.Support.Normal.FactorBase
  using (Run; rnil; rφ; Block; bnil; bν; bubν⁻; bubφ⁻; bubφ-inv;
         _~ᵩ_; _~ᵩ₁_; φφᵩ; νφᵩ; thrᵩ; delᵩ;
         ~ᵩ-refl; ~ᵩ-sym; ~ᵩ-trans; ≡→~ᵩ; ~ᵩ-νNF; ~ᵩ-φNF)
open import BorrowedCF.Simulation.Support.Normal.Factor
  using (dragTel; dragRen; bswapTel; bswapRen; prefixNF; prefixNF-++ᵗ)
open import BorrowedCF.Simulation.Support.Normal.PrenexImage
  using (BTel; BScope; Bσ; BShape; blockShape; shape-prenex-image;
         nf-prenex-image)
open import BorrowedCF.Simulation.Support.Normal.RealiseBase
open import BorrowedCF.Simulation.Support.Normal.Realise
  using (BswpThreadCoh; BswpThreadCohᵇ; FlipResidue; ImageOf)
open import BorrowedCF.Simulation.Support.Normal.RealiseCohNat
  using (toℕ-subst𝔽; asF; lift↑; asF-invol; lift↑-∘; lift↑-id;
         cntᵗ; cntᵗ-++ᵗ; cntᵗ-nest; cntᵗ-φTel; cntᵗ-BTel; Bcnt; Bcnt-⋯ᵗᵉˡ;
         spec-bswapRen; module Bridge; module BridgeFlip)
open import BorrowedCF.Simulation.Support.TranslationProperties
  using (U-σ⋯; U-⋯ₚ)
open import BorrowedCF.Simulation.Support.CongruenceH1
  using (leafσ; canonₛ; subEq-gen)
open import BorrowedCF.Simulation.Support.CongruenceH2 using (Φᵗ)
open import BorrowedCF.Simulation.Support.Congruence using (subEqComm-gen)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Relation.Binary.Construct.Closure.Equivalence as Eq*

open Nat.Variables
open Fin.Patterns

------------------------------------------------------------------------
-- Transport and map plumbing.
------------------------------------------------------------------------

private
  subst-List-refl : ∀ {k} (p : k ≡ k) (xs : List (Tm k)) →
                    subst (List ∘ Tm) p xs ≡ xs
  subst-List-refl p xs = cong (λ q → subst (List ∘ Tm) q xs) (≡-irrelevant p refl)

  subst-Tm-irrel : ∀ {c d} (p q : c ≡ d) (x : Tm c) →
                   subst Tm p x ≡ subst Tm q x
  subst-Tm-irrel p q x = cong (λ e → subst Tm e x) (≡-irrelevant p q)

  subst-List-irrel : ∀ {c d} (p q : c ≡ d) (xs : List (Tm c)) →
                     subst (List ∘ Tm) p xs ≡ subst (List ∘ Tm) q xs
  subst-List-irrel p q xs = cong (λ e → subst (List ∘ Tm) e xs) (≡-irrelevant p q)

  subst-move : ∀ {A : Set} {F : A → Set} {a b} (e : a ≡ b) {x : F a} {y : F b} →
               subst F e x ≡ y → x ≡ subst F (sym e) y
  subst-move refl h = h

  subst-List-∷ : ∀ {c d} (e : c ≡ d) (x : Tm c) (xs : List (Tm c)) →
                 subst (List ∘ Tm) e (x ∷ xs) ≡ subst Tm e x ∷ subst (List ∘ Tm) e xs
  subst-List-∷ refl x xs = refl

  subst-Tm-K : ∀ {c d} (e : c ≡ d) (cst : Const) → subst Tm e (K cst) ≡ K cst
  subst-Tm-K refl cst = refl

  subst-List-[] : ∀ {c d} (e : c ≡ d) → subst (List ∘ Tm) e [] ≡ []
  subst-List-[] refl = refl

  map-⋯-congₛ : ∀ {a b} {σ σ′ : a →ₛ b} → (∀ x → σ x ≡ σ′ x) →
                (es : List (Tm a)) → map (_⋯ σ) es ≡ map (_⋯ σ′) es
  map-⋯-congₛ h []       = refl
  map-⋯-congₛ h (e ∷ es) = cong₂ _∷_ (⋯-cong e h) (map-⋯-congₛ h es)

  map-fuseₛᵣ : ∀ {a b c} (σ : a →ₛ b) (ρ : b →ᵣ c) (es : List (Tm a)) →
               map (_⋯ ρ) (map (_⋯ σ) es) ≡ map (_⋯ (σ ·ₖ ρ)) es
  map-fuseₛᵣ σ ρ []       = refl
  map-fuseₛᵣ σ ρ (e ∷ es) = cong₂ _∷_ (fusion e σ ρ) (map-fuseₛᵣ σ ρ es)

  map-fuseᵣₛ : ∀ {a b c} (ρ : a →ᵣ b) (σ : b →ₛ c) (es : List (Tm a)) →
               map (_⋯ σ) (map (_⋯ ρ) es) ≡ map (_⋯ (ρ ·ₖ σ)) es
  map-fuseᵣₛ ρ σ []       = refl
  map-fuseᵣₛ ρ σ (e ∷ es) = cong₂ _∷_ (fusion e ρ σ) (map-fuseᵣₛ ρ σ es)

  subst-List-map : ∀ {a c d} (e : c ≡ d) (τ : a →ₛ c) (es : List (Tm a)) →
                   subst (List ∘ Tm) e (map (_⋯ τ) es)
                     ≡ map (_⋯ (λ y → subst Tm e (τ y))) es
  subst-List-map refl τ es = refl

  -- Expand a subst over an image thread list.
  subst-img : ∀ {a c d} (e : c ≡ d) (τ : a →ₛ c) (es : List (Tm a)) →
              subst (List ∘ Tm) e (map (_⋯ τ) es ++ (K `unit ∷ []))
                ≡ map (_⋯ (λ y → subst Tm e (τ y))) es ++ (K `unit ∷ [])
  subst-img e τ es =
      subst-++ e (map (_⋯ τ) es) (K `unit ∷ [])
    ■ cong₂ _++_ (subst-List-map e τ es)
        (subst-List-∷ e (K `unit) [] ■ cong₂ _∷_ (subst-Tm-K e `unit) (subst-List-[] e))

  mkNF-thr-≡ : ∀ {n k} {t : Tel n k} {es₁ es₂ : List (Tm k)} →
               mkNF t es₁ ≡ mkNF t es₂ → es₁ ≡ es₂
  mkNF-thr-≡ {es₁ = es₁} eq =
    sym (subst-List-refl (NF-inner eq) es₁) ■ NF-thr eq

  -- Push a Fin-cast in the renaming out onto the term.
  ⋯-cast𝔽 : ∀ {a c d} (e : c ≡ d) (ρ : a →ᵣ c) (t : Tm a) →
            t ⋯ (λ v → subst 𝔽 e (ρ v)) ≡ subst Tm e (t ⋯ ρ)
  ⋯-cast𝔽 refl ρ t = refl

  -- Push a Tm-cast in the substitution out onto the term.
  ⋯-castₛ : ∀ {a c d} (e : c ≡ d) (τ : a →ₛ c) (t : Tm a) →
            t ⋯ (λ v → subst Tm e (τ v)) ≡ subst Tm e (t ⋯ τ)
  ⋯-castₛ refl τ t = refl

  -- Conjugating a renaming by scope casts.
  conj-⋯ : ∀ {c d a} (E : d ≡ c) (ρ : c →ᵣ c) (e : a ≡ d) (x : Tm a) →
           (subst Tm e x) ⋯ (λ v → subst 𝔽 (sym E) (ρ (subst 𝔽 E v)))
             ≡ subst Tm (sym E) ((subst Tm (e ■ E) x) ⋯ ρ)
  conj-⋯ refl ρ refl x = refl

------------------------------------------------------------------------
-- Image substitution algebra.
------------------------------------------------------------------------

private
  [,]′-congʳ : ∀ {A B C : Set} (f : A → C) {g g′ : B → C} →
               (∀ z → g z ≡ g′ z) → (s : A ⊎ B) → [ f , g ]′ s ≡ [ f , g′ ]′ s
  [,]′-congʳ f h (inj₁ a′) = refl
  [,]′-congʳ f h (inj₂ b′) = h b′

  canonₛ-σB : ∀ {n} (B : BindGroup) (cc : UChan n) (y : 𝔽 (sum B)) →
              σB B cc y ≡ canonₛ B cc y
  canonₛ-σB []              cc ()
  canonₛ-σB (b ∷ [])        cc y = refl
  canonₛ-σB {n} (b ∷ B@(_ ∷ _)) (e₁ , x , e₂) y =
    cong (subst Tm (+-suc (syncs B) n))
      ([,]′-congʳ _ (λ k′ → canonₛ-σB B (` 0F , suc x , wk e₂) k′)
        (Fin.splitAt b y))

  σ′-leafσ : ∀ {m n} (B₁ B₂ : BindGroup) (σ : m →ₛ n) (x : 𝔽 (sum B₁ + sum B₂ + m)) →
             νImage.σ′ B₁ B₂ σ x ≡ leafσ σ B₁ B₂ x
  σ′-leafσ B₁ B₂ σ x with Fin.splitAt (sum B₁ + sum B₂) x
  ... | inj₂ i = refl
  ... | inj₁ z with Fin.splitAt (sum B₁) z
  ...   | inj₁ j  = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (canonₛ-σB B₁ _ j)
  ...   | inj₂ k′ = canonₛ-σB B₂ _ k′

  leafσ-cong : ∀ {m n} (B₁ B₂ : BindGroup) {σ σ′ : m →ₛ n} → (∀ i → σ i ≡ σ′ i) →
               ∀ x → leafσ σ B₁ B₂ x ≡ leafσ σ′ B₁ B₂ x
  leafσ-cong B₁ B₂ h x with Fin.splitAt (sum B₁ + sum B₂) x
  ... | inj₁ z = refl
  ... | inj₂ i =
    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)
                  ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (h i)

  σ′-cong : ∀ {m n} (B₁ B₂ : BindGroup) {σ σ′ : m →ₛ n} → (∀ i → σ i ≡ σ′ i) →
            ∀ x → νImage.σ′ B₁ B₂ σ x ≡ νImage.σ′ B₁ B₂ σ′ x
  σ′-cong B₁ B₂ h x with Fin.splitAt (sum B₁ + sum B₂) x
  ... | inj₁ z = refl
  ... | inj₂ i =
    cong (λ t → t ⋯ weaken* ⦃ Kᵣ ⦄ 2 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₁)
                  ⋯ weaken* ⦃ Kᵣ ⦄ (syncs B₂)) (h i)

  Bσ-cong : ∀ {a k n} (t : TTel a k) {σ σ′ : a →ₛ n} → (∀ i → σ i ≡ σ′ i) →
            ∀ y → Bσ t σ y ≡ Bσ t σ′ y
  Bσ-cong []ᵗ           h y = h y
  Bσ-cong (tνᵗ B₁ B₂ t) h y = Bσ-cong t (σ′-cong B₁ B₂ h) y

  Bσ-base-subst : ∀ {a k ñ n} (t : TTel a k) (e : ñ ≡ n) (σ : a →ₛ ñ) (y : 𝔽 k) →
                  Bσ t (λ x → subst Tm e (σ x)) y
                    ≡ subst Tm (cong (BScope t) e) (Bσ t σ y)
  Bσ-base-subst t refl σ y = refl

BScope-++ᵗᵗ : ∀ {a b c} (u : TTel a b) (v : TTel b c) (n : ℕ) →
              BScope (u ++ᵗᵗ v) n ≡ BScope v (BScope u n)
BScope-++ᵗᵗ []ᵗ           v n = refl
BScope-++ᵗᵗ (tνᵗ B₁ B₂ u) v n =
  BScope-++ᵗᵗ u v (syncs B₂ + (syncs B₁ + (2 + n)))

private
  Bσ-++ᵗᵗ : ∀ {a b c n} (u : TTel a b) (v : TTel b c) (σ : a →ₛ n) (y : 𝔽 c) →
            subst Tm (BScope-++ᵗᵗ u v n) (Bσ (u ++ᵗᵗ v) σ y) ≡ Bσ v (Bσ u σ) y
  Bσ-++ᵗᵗ []ᵗ           v σ y = refl
  Bσ-++ᵗᵗ (tνᵗ B₁ B₂ u) v σ y = Bσ-++ᵗᵗ u v (νImage.σ′ B₁ B₂ σ) y

BScope-⋯ᵗᵉˡ : ∀ {a k m} (t : TTel a k) (χ : a →ᵣ m) (n : ℕ) →
              BScope (t ⋯ᵗᵉˡ χ) n ≡ BScope t n
BScope-⋯ᵗᵉˡ []ᵗ           χ n = refl
BScope-⋯ᵗᵉˡ (tνᵗ B₁ B₂ t) χ n =
  BScope-⋯ᵗᵉˡ t (χ ↑* (sum B₁ + sum B₂)) (syncs B₂ + (syncs B₁ + (2 + n)))

------------------------------------------------------------------------
-- The two Bσ laws, extracted from normal forms computed two ways.
------------------------------------------------------------------------

private
  law : ∀ {m k n} (t : TTel m k) (es : List (Tm k)) (σ : m →ₛ n) (ξ : n →ᵣ n) →
        map (_⋯ liftId (BTel t n) ξ) (map (_⋯ Bσ t σ) es ++ (K `unit ∷ []))
          ≡ map (_⋯ Bσ t (σ ·ₖ ξ)) es ++ (K `unit ∷ [])
  law t es σ ξ = mkNF-thr-≡
    ( sym (cong (λ N → mkNF (tel N) (map (_⋯ liftId (tel N) ξ) (thr N)))
             (nf-prenex-image t es σ))
    ■ sym (nf-endo (U[ plugᵗ t (parsᵗ es) ] σ) ξ)
    ■ cong nf (U-σ⋯ (plugᵗ t (parsᵗ es)) {σ = σ} {ρ = ξ})
    ■ nf-prenex-image t es (σ ·ₖ ξ) )

  law2 : ∀ {m m̃ k n} (t : TTel m k) (χ : m →ᵣ m̃) (es : List (Tm k)) (σ̃ : m̃ →ₛ n) →
         subst (List ∘ Tm) (sym (BScope-⋯ᵗᵉˡ t χ n))
               (map (_⋯ Bσ t (χ ·ₖ σ̃)) es ++ (K `unit ∷ []))
           ≡ map (_⋯ Bσ (t ⋯ᵗᵉˡ χ) σ̃) (map (_⋯ (t ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ [])
  law2 {n = n} t χ es σ̃ =
      subst-List-irrel (sym (BScope-⋯ᵗᵉˡ t χ n)) (NF-inner eqNF) _
    ■ NF-thr eqNF
    where
      eqNF : mkNF (BTel t n) (map (_⋯ Bσ t (χ ·ₖ σ̃)) es ++ (K `unit ∷ []))
               ≡ mkNF (BTel (t ⋯ᵗᵉˡ χ) n)
                      (map (_⋯ Bσ (t ⋯ᵗᵉˡ χ) σ̃) (map (_⋯ (t ↑ᵗᵉˡ χ)) es)
                        ++ (K `unit ∷ []))
      eqNF =
          sym (nf-prenex-image t es (χ ·ₖ σ̃))
        ■ cong nf (sym (U-⋯ₚ (plugᵗ t (parsᵗ es)) {ρ = χ} {σ = σ̃}))
        ■ cong (λ Q → nf (U[ Q ] σ̃))
            ( plug-⋯ₚᵗ t (parsᵗ es) χ
            ■ cong (plugᵗ (t ⋯ᵗᵉˡ χ)) (pars-⋯ₚᵗ es (t ↑ᵗᵉˡ χ)) )
        ■ nf-prenex-image (t ⋯ᵗᵉˡ χ) (map (_⋯ (t ↑ᵗᵉˡ χ)) es) σ̃

  law2Pt : ∀ {m m̃ k n} (t : TTel m k) (χ : m →ᵣ m̃) (σ̃ : m̃ →ₛ n) (y : 𝔽 k) →
           subst Tm (sym (BScope-⋯ᵗᵉˡ t χ n)) (Bσ t (χ ·ₖ σ̃) y)
             ≡ Bσ (t ⋯ᵗᵉˡ χ) σ̃ ((t ↑ᵗᵉˡ χ) y)
  law2Pt {n = n} t χ σ̃ y =
    L.∷-injectiveˡ
      ( sym (subst-List-∷ (sym (BScope-⋯ᵗᵉˡ t χ n)) (Bσ t (χ ·ₖ σ̃) y) _)
      ■ law2 t χ (` y ∷ []) σ̃ )

  lawPt : ∀ {m k n} (t : TTel m k) (σ : m →ₛ n) (ξ : n →ᵣ n) (y : 𝔽 k) →
          (Bσ t σ y) ⋯ liftId (BTel t n) ξ ≡ Bσ t (σ ·ₖ ξ) y
  lawPt t σ ξ y = L.∷-injectiveˡ (law t (` y ∷ []) σ ξ)

------------------------------------------------------------------------
-- The Factor composites factor through the tail telescope.
------------------------------------------------------------------------

private
  dragRen-factor : ∀ {p j m k} (S : Tel p j) {r : Tel j m} (w : Run r)
                   (t : Tel m k) (x : 𝔽 k) →
                   dragRen S w t x ≡ liftId t (dragRen S w []) x
  dragRen-factor S rnil t x = sym (liftId-id t (λ _ → refl) x)
  dragRen-factor S (rφ {f = f} {r = r} w) t x =
      cong (dragRen (shift1 S) w t) (liftId-++ᵗ r t (bubφ⁻ S) x)
    ■ dragRen-factor (shift1 S) w t (liftId t (liftId r (bubφ⁻ S)) x)
    ■ liftId-· t (liftId r (bubφ⁻ S)) (dragRen (shift1 S) w []) x
    ■ liftId-cong t
        (λ v → cong (dragRen (shift1 S) w [])
                 (cong (λ z → liftId z (bubφ⁻ S) v) (sym (++ᵗ-idʳ r)))) x

  bswapRen-factor : ∀ {n i m k} (a : Tel (2 + n) i) {rb : Tel (2 + i) m}
                    (w : Run rb) (t : Tel m k) (x : 𝔽 k) →
                    bswapRen a w t x ≡ liftId t (bswapRen a w []) x
  bswapRen-factor a {rb} w t x =
      cong (dragRen (tν (shift2 a)) w t) (liftId-++ᵗ rb t (bubν⁻ (tν a)) x)
    ■ dragRen-factor (tν (shift2 a)) w t (liftId t (liftId rb (bubν⁻ (tν a))) x)
    ■ liftId-· t (liftId rb (bubν⁻ (tν a))) (dragRen (tν (shift2 a)) w []) x
    ■ liftId-cong t
        (λ v → cong (dragRen (tν (shift2 a)) w [])
                 (cong (λ z → liftId z (bubν⁻ (tν a)) v) (sym (++ᵗ-idʳ rb)))) x

------------------------------------------------------------------------
-- The block-swap core: forward thread coherence over the two located
-- nodes, at the concrete image data.
------------------------------------------------------------------------

private
  collapse3 : ∀ {c₁ c₂ c₃} (p : c₁ ≡ c₂) (q : c₂ ≡ c₃) (r : c₃ ≡ c₁)
              (xs : List (Tm c₁)) →
              subst (List ∘ Tm) r (subst (List ∘ Tm) q (subst (List ∘ Tm) p xs))
                ≡ xs
  collapse3 p q r xs =
      cong (subst (List ∘ Tm) r) (sym (subst-■ (List ∘ Tm) p q xs))
    ■ sym (subst-■ (List ∘ Tm) (p ■ q) r xs)
    ■ subst-List-refl ((p ■ q) ■ r) xs

module SwapCore {q₀ n₀ : ℕ} (σ₀ : q₀ →ₛ n₀) (A₁ A₂ G₁ G₂ : BindGroup)
                {k₀ : ℕ}
                (t₂ : TTel (sum A₁ + sum A₂ + (sum G₁ + sum G₂ + q₀)) k₀)
                where

  private
    sA1 = syncs A₁ ; sA2 = syncs A₂ ; sG1 = syncs G₁ ; sG2 = syncs G₂

  open Bridge A₁ A₂ G₁ G₂ {n₀} public

  χ : (sum A₁ + sum A₂ + (sum G₁ + sum G₂ + q₀))
        →ᵣ (sum G₁ + sum G₂ + (sum A₁ + sum A₂ + q₀))
  χ = assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)

  σᴳ = νImage.σ′ G₁ G₂ σ₀
  σᴬ = νImage.σ′ A₁ A₂ σᴳ
  σᴬ⁰ = νImage.σ′ A₁ A₂ σ₀
  σᴳ″ = νImage.σ′ G₁ G₂ σᴬ⁰

  V  = tνᵗ G₁ G₂ (tνᵗ A₁ A₂ t₂)
  V′ = tνᵗ A₁ A₂ (tνᵗ G₁ G₂ (t₂ ⋯ᵗᵉˡ χ))

  private
    ñ : ℕ
    ñ = sG2 + (sG1 + (2 + (sA2 + (sA1 + (2 + n₀)))))

    Φc : 𝔽 n₂ᵇ → 𝔽 ñ
    Φc = Φᵗ sA1 sA2 sG1 sG2 {n₀}

    c₂ c₃ c₄ : ℕ
    c₂ = sA2 + (sA1 + (sG2 + (sG1 + (2 + (2 + n₀)))))
    c₃ = sA2 + (sG2 + (sA1 + (sG1 + (2 + (2 + n₀)))))
    c₄ = sG2 + (sA2 + (sA1 + (sG1 + (2 + (2 + n₀)))))

    f₁ : n₂ᵇ →ᵣ c₂
    f₁ = (assocSwapᵣ 2 sG2
           ·ₖ ((assocSwapᵣ 2 sG1 ·ₖ (assocSwapᵣ 2 2 {n₀} ↑* sG1)) ↑* sG2))
             ↑* sA1 ↑* sA2
    f₂ : c₂ →ᵣ c₃
    f₂ = assocSwapᵣ sA1 sG2 ↑* sA2
    f₃ : c₃ →ᵣ c₄
    f₃ = assocSwapᵣ sA2 sG2
    f₄ : c₄ →ᵣ ñ
    f₄ = ((assocSwapᵣ sA1 sG1 ↑* sA2)
           ·ₖ (assocSwapᵣ sA2 sG1
                ·ₖ (((assocSwapᵣ sA1 2 ↑* sA2) ·ₖ assocSwapᵣ sA2 2) ↑* sG1)))
             ↑* sG2

    toLeaf : ∀ x → σᴬ x ≡ leafσ (leafσ σ₀ G₁ G₂) A₁ A₂ x
    toLeaf x = σ′-leafσ A₁ A₂ σᴳ x
             ■ leafσ-cong A₁ A₂ (σ′-leafσ G₁ G₂ σ₀) x

    fromLeaf : ∀ z → leafσ (leafσ σ₀ A₁ A₂) G₁ G₂ z ≡ σᴳ″ z
    fromLeaf z = sym ( σ′-leafσ G₁ G₂ σᴬ⁰ z
                     ■ leafσ-cong G₁ G₂ (σ′-leafσ A₁ A₂ σ₀) z )

  intertwine : (w : Run rᴬ) → ∀ x → σᴬ x ⋯ bswapRen aᴮ w [] ≡ subst Tm eqΦ (σᴳ″ (χ x))
  intertwine w x =
      ⋯-cong (σᴬ x) (bridge-fwd w)
    ■ ⋯-cast𝔽 eqΦ Φc (σᴬ x)
    ■ cong (subst Tm eqΦ) innerEq
    where
      innerEq : σᴬ x ⋯ Φc ≡ σᴳ″ (χ x)
      innerEq =
          sym (fusion (σᴬ x) ((f₁ ·ₖ f₂) ·ₖ f₃) f₄)
        ■ cong (_⋯ f₄) (sym (fusion (σᴬ x) (f₁ ·ₖ f₂) f₃))
        ■ cong (λ z → (z ⋯ f₃) ⋯ f₄) (sym (fusion (σᴬ x) f₁ f₂))
        ■ cong (λ t → (((t ⋯ f₁) ⋯ f₂) ⋯ f₃) ⋯ f₄) (toLeaf x)
        ■ subEqComm-gen σ₀ A₁ A₂ G₁ G₂ x
        ■ fromLeaf (χ x)

  EC : BScope (t₂ ⋯ᵗᵉˡ χ) ñ ≡ BScope t₂ n₂ᵇ
  EC = BScope-⋯ᵗᵉˡ t₂ χ ñ ■ cong (BScope t₂) eqΦ

  fwdPt : (w : Run rᴬ) → ∀ y →
          (Bσ t₂ σᴬ y) ⋯ bswapRen aᴮ w (BTel t₂ n₂ᵇ)
            ≡ subst Tm EC (Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″ ((t₂ ↑ᵗᵉˡ χ) y))
  fwdPt w y =
      ⋯-cong (Bσ t₂ σᴬ y) (bswapRen-factor aᴮ w (BTel t₂ n₂ᵇ))
    ■ lawPt t₂ σᴬ (bswapRen aᴮ w []) y
    ■ Bσ-cong t₂ (intertwine w) y
    ■ Bσ-base-subst t₂ eqΦ (χ ·ₖ σᴳ″) y
    ■ cong (subst Tm (cong (BScope t₂) eqΦ)) mid
    ■ sym (subst-■ Tm (BScope-⋯ᵗᵉˡ t₂ χ ñ) (cong (BScope t₂) eqΦ) _)
    where
      mid : Bσ t₂ (χ ·ₖ σᴳ″) y
              ≡ subst Tm (BScope-⋯ᵗᵉˡ t₂ χ ñ) (Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″ ((t₂ ↑ᵗᵉˡ χ) y))
      mid = subst-move (sym (BScope-⋯ᵗᵉˡ t₂ χ ñ)) (law2Pt t₂ χ σᴳ″ y)
          ■ subst-Tm-irrel (sym (sym (BScope-⋯ᵗᵉˡ t₂ χ ñ))) (BScope-⋯ᵗᵉˡ t₂ χ ñ) _

  fwdList : (w : Run rᴬ) (es : List (Tm k₀)) →
            map (_⋯ bswapRen aᴮ w (BTel t₂ n₂ᵇ))
                (map (_⋯ Bσ t₂ σᴬ) es ++ (K `unit ∷ []))
              ≡ subst (List ∘ Tm) EC
                  (map (_⋯ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es)
                    ++ (K `unit ∷ []))
  fwdList w es =
      map-++ᴸ ρ̄ (map (_⋯ Bσ t₂ σᴬ) es) (K `unit ∷ [])
    ■ cong (_++ (K `unit ∷ []))
        ( map-fuseₛᵣ (Bσ t₂ σᴬ) ρ̄ es
        ■ map-⋯-congₛ (fwdPt w) es )
    ■ sym ( cong (subst (List ∘ Tm) EC)
              (cong (_++ (K `unit ∷ []))
                (map-fuseᵣₛ (t₂ ↑ᵗᵉˡ χ) (Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) es))
          ■ subst-img EC ((t₂ ↑ᵗᵉˡ χ) ·ₖ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) es )
    where
      ρ̄ = bswapRen aᴮ w (BTel t₂ n₂ᵇ)

------------------------------------------------------------------------
-- The forward block-swap thread coherence.
------------------------------------------------------------------------

bswpThreadCoh : BswpThreadCoh
bswpThreadCoh {m} {q₀} {k₀} {p} u G₁ G₂ A₁ A₂ t₂ es σ s a ra w t′ bt es₁
              pre≡ fl₁ fl₂ X≡₂ eq eqk
  with shape-det s (BTel u p) (sym pre≡ ■ sym (shape-prenex-image u p))
... | refl , refl
  with shape-det a
        (φTel G₁ (2 + BScope u p) ++ᵗ φTel G₂ (syncs G₁ + (2 + BScope u p)))
        ( shape-run ra
        ■ cong (map sφ) (sym fl₁)
        ■ map-sφ-++ (syncFlags G₁) (syncFlags G₂)
        ■ sym (cong₂ _++_ (shape-φTel G₁ (2 + BScope u p))
                          (shape-φTel G₂ (syncs G₁ + (2 + BScope u p))))
        ■ sym (shape-++ᵗ (φTel G₁ (2 + BScope u p))
                         (φTel G₂ (syncs G₁ + (2 + BScope u p)))) )
... | refl , refl
  with shape-det _
        (φTel A₁ (2 + (syncs G₂ + (syncs G₁ + (2 + BScope u p))))
          ++ᵗ φTel A₂ (syncs A₁ + (2 + (syncs G₂ + (syncs G₁ + (2 + BScope u p))))))
        ( shape-run w
        ■ cong (map sφ) (sym fl₂)
        ■ map-sφ-++ (syncFlags A₁) (syncFlags A₂)
        ■ sym (cong₂ _++_ (shape-φTel A₁ _) (shape-φTel A₂ _))
        ■ sym (shape-++ᵗ (φTel A₁ _) (φTel A₂ _)) )
... | refl , refl
  with shape-det t′
        (BTel t₂ (syncs A₂ + (syncs A₁ + (2 + (syncs G₂ + (syncs G₁ + (2 + BScope u p)))))))
        (sym X≡₂ ■ sym (shape-prenex-image t₂ _))
... | refl , refl =
    cong (subst (List ∘ Tm) eqk) (cong (map (_⋯ _)) step0 ■ fwdList w es
      ■ cong (subst (List ∘ Tm) EC) step3)
  ■ collapse3 (BScope-++ᵗᵗ u V′ p) EC eqk _
  where
    open SwapCore (Bσ u σ) A₁ A₂ G₁ G₂ t₂

    T  = u ++ᵗᵗ V
    T′ = u ++ᵗᵗ V′

    pwT : ∀ y → subst Tm (sym (NF-inner eq)) (Bσ T σ y) ≡ Bσ t₂ σᴬ y
    pwT y = subst-Tm-irrel (sym (NF-inner eq)) (BScope-++ᵗᵗ u V p) _
          ■ Bσ-++ᵗᵗ u V σ y

    step0 : es₁ ≡ map (_⋯ Bσ t₂ σᴬ) es ++ (K `unit ∷ [])
    step0 = subst-move (NF-inner eq) (NF-thr eq)
          ■ subst-img (sym (NF-inner eq)) (Bσ T σ) es
          ■ cong (_++ (K `unit ∷ [])) (map-⋯-congₛ pwT es)

    pwT′ : ∀ y → subst Tm (BScope-++ᵗᵗ u V′ p) (Bσ T′ σ y)
                   ≡ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″ y
    pwT′ y = Bσ-++ᵗᵗ u V′ σ y

    step3 : map (_⋯ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ [])
              ≡ subst (List ∘ Tm) (BScope-++ᵗᵗ u V′ p)
                  (map (_⋯ Bσ T′ σ) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ []))
    step3 = sym ( subst-img (BScope-++ᵗᵗ u V′ p) (Bσ T′ σ) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es)
                ■ cong (_++ (K `unit ∷ []))
                    (map-⋯-congₛ pwT′ (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es)) )

------------------------------------------------------------------------
-- The backward block-swap thread coherence: invert the forward one
-- through the cast-conjugate of the forward renaming.
------------------------------------------------------------------------

private
  subst-Tm-refl : ∀ {c} (p : c ≡ c) (x : Tm c) → subst Tm p x ≡ x
  subst-Tm-refl p x = cong (λ e → subst Tm e x) (≡-irrelevant p refl)

bswpThreadCohᵇ : BswpThreadCohᵇ
bswpThreadCohᵇ {m} {q₀} {k₀} {p} u G₁ G₂ A₁ A₂ t₂ es σ s a ra w t′ bt es₁
               pre≡ fl₁ fl₂ X≡₂ eq eqk
  with shape-det s (BTel u p) (sym pre≡ ■ sym (shape-prenex-image u p))
... | refl , refl
  with shape-det a
        (φTel A₁ (2 + BScope u p) ++ᵗ φTel A₂ (syncs A₁ + (2 + BScope u p)))
        ( shape-run ra
        ■ cong (map sφ) (sym fl₂)
        ■ map-sφ-++ (syncFlags A₁) (syncFlags A₂)
        ■ sym (cong₂ _++_ (shape-φTel A₁ (2 + BScope u p))
                          (shape-φTel A₂ (syncs A₁ + (2 + BScope u p))))
        ■ sym (shape-++ᵗ (φTel A₁ (2 + BScope u p))
                         (φTel A₂ (syncs A₁ + (2 + BScope u p)))) )
... | refl , refl
  with shape-det _
        (φTel G₁ (2 + (syncs A₂ + (syncs A₁ + (2 + BScope u p))))
          ++ᵗ φTel G₂ (syncs G₁ + (2 + (syncs A₂ + (syncs A₁ + (2 + BScope u p))))))
        ( shape-run w
        ■ cong (map sφ) (sym fl₁)
        ■ map-sφ-++ (syncFlags G₁) (syncFlags G₂)
        ■ sym (cong₂ _++_ (shape-φTel G₁ _) (shape-φTel G₂ _))
        ■ sym (shape-++ᵗ (φTel G₁ _) (φTel G₂ _)) )
... | refl , refl
  with shape-det t′
        (BTel (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂))
              (syncs G₂ + (syncs G₁ + (2 + (syncs A₂ + (syncs A₁ + (2 + BScope u p)))))))
        ( sym X≡₂
        ■ sym (BShape-⋯ᵗᵉˡ t₂ (assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)))
        ■ sym (shape-prenex-image (t₂ ⋯ᵗᵉˡ assocSwapᵣ (sum A₁ + sum A₂) (sum G₁ + sum G₂)) _) )
... | refl , refl =
    cong (subst (List ∘ Tm) eqk) es₁≡
  ■ collapse3 refl (BScope-++ᵗᵗ u V′ p) eqk _
  where
    open SwapCore (Bσ u σ) A₁ A₂ G₁ G₂ t₂

    T  = u ++ᵗᵗ V
    T′ = u ++ᵗᵗ V′

    ñ₂ : ℕ
    ñ₂ = syncs G₂ + (syncs G₁ + (2 + (syncs A₂ + (syncs A₁ + (2 + BScope u p)))))

    aᵇ : Tel (2 + BScope u p) (syncs A₂ + (syncs A₁ + (2 + BScope u p)))
    aᵇ = φTel A₁ (2 + BScope u p) ++ᵗ φTel A₂ (syncs A₁ + (2 + BScope u p))

    tᵇ : Tel ñ₂ (BScope (t₂ ⋯ᵗᵉˡ χ) ñ₂)
    tᵇ = BTel (t₂ ⋯ᵗᵉˡ χ) ñ₂

    ρ̄ᵇ : BScope (t₂ ⋯ᵗᵉˡ χ) ñ₂ →ᵣ BScope (t₂ ⋯ᵗᵉˡ χ) ñ₂
    ρ̄ᵇ = bswapRen aᵇ w tᵇ

    wf : Run rᴬ
    wf = Run-++ᵗ (Run-φTel A₁ (2 + n₁ᵇ)) (Run-φTel A₂ (syncs A₁ + (2 + n₁ᵇ)))

    ρ̄f : BScope t₂ n₂ᵇ →ᵣ BScope t₂ n₂ᵇ
    ρ̄f = bswapRen aᴮ wf (BTel t₂ n₂ᵇ)

    ρ̄ᵇ⁻ : BScope (t₂ ⋯ᵗᵉˡ χ) ñ₂ →ᵣ BScope (t₂ ⋯ᵗᵉˡ χ) ñ₂
    ρ̄ᵇ⁻ v = subst 𝔽 (sym EC) (ρ̄f (subst 𝔽 EC v))

    Deq : cntᵗ tᵇ ≡ cntᵗ (BTel t₂ n₂ᵇ)
    Deq = cntᵗ-BTel (t₂ ⋯ᵗᵉˡ χ) ñ₂ ■ Bcnt-⋯ᵗᵉˡ t₂ χ ■ sym (cntᵗ-BTel t₂ n₂ᵇ)

    cancel : ∀ v → ρ̄ᵇ⁻ (ρ̄ᵇ v) ≡ v
    cancel v = Fin.toℕ-injective
      ( toℕ-subst𝔽 (sym EC) _
      ■ spec-bswapRen aᴮ wf (BTel t₂ n₂ᵇ) (subst 𝔽 EC (ρ̄ᵇ v))
      ■ cong (lift↑ (cntᵗ (BTel t₂ n₂ᵇ)) (asF (cntᵗ rᴬ + 2) (cntᵗ aᴮ + 2)))
          (toℕ-subst𝔽 EC (ρ̄ᵇ v))
      ■ cong (lift↑ (cntᵗ (BTel t₂ n₂ᵇ)) (asF (cntᵗ rᴬ + 2) (cntᵗ aᴮ + 2)))
          (spec-bswapRen aᵇ w tᵇ v)
      ■ cong₂ (λ z₁ z₂ →
            lift↑ (cntᵗ (BTel t₂ n₂ᵇ)) (asF (cntᵗ rᴬ + 2) (cntᵗ aᴮ + 2))
              (lift↑ z₁ (asF (z₂ + 2) (cntᵗ aᵇ + 2)) (Fin.toℕ v)))
          Deq (cntᵗ-nest G₁ G₂ (2 + (syncs A₂ + (syncs A₁ + (2 + BScope u p)))))
      ■ cong₂ (λ z₁ z₂ →
            lift↑ (cntᵗ (BTel t₂ n₂ᵇ)) (asF (z₁ + 2) (z₂ + 2))
              (lift↑ (cntᵗ (BTel t₂ n₂ᵇ))
                (asF ((syncs G₁ + syncs G₂) + 2) (cntᵗ aᵇ + 2)) (Fin.toℕ v)))
          (cnt-rᴬ′) (cnt-aᴮ′)
      ■ cong (λ z →
            lift↑ (cntᵗ (BTel t₂ n₂ᵇ)) (asF ((syncs A₁ + syncs A₂) + 2) ((syncs G₁ + syncs G₂) + 2))
              (lift↑ (cntᵗ (BTel t₂ n₂ᵇ))
                (asF ((syncs G₁ + syncs G₂) + 2) (z + 2)) (Fin.toℕ v)))
          (cntᵗ-nest A₁ A₂ (2 + BScope u p))
      ■ lift↑-∘ (cntᵗ (BTel t₂ n₂ᵇ))
          (asF ((syncs A₁ + syncs A₂) + 2) ((syncs G₁ + syncs G₂) + 2))
          (asF ((syncs G₁ + syncs G₂) + 2) ((syncs A₁ + syncs A₂) + 2))
          (Fin.toℕ v)
      ■ lift↑-id (cntᵗ (BTel t₂ n₂ᵇ))
          (λ z → asF-invol ((syncs G₁ + syncs G₂) + 2) ((syncs A₁ + syncs A₂) + 2) z)
          (Fin.toℕ v) )
      where
        cnt-rᴬ′ : cntᵗ rᴬ ≡ syncs A₁ + syncs A₂
        cnt-rᴬ′ = cntᵗ-nest A₁ A₂ (2 + n₁ᵇ)
        cnt-aᴮ′ : cntᵗ aᴮ ≡ syncs G₁ + syncs G₂
        cnt-aᴮ′ = cntᵗ-nest G₁ G₂ (2 + n₀′)
          where n₀′ = BScope u p

    bwdPt : ∀ y → (subst Tm (sym (NF-inner eq)) (Bσ T σ y)) ⋯ ρ̄ᵇ⁻
                    ≡ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″ ((t₂ ↑ᵗᵉˡ χ) y)
    bwdPt y =
        conj-⋯ EC ρ̄f (sym (NF-inner eq)) (Bσ T σ y)
      ■ cong (subst Tm (sym EC))
          ( cong (_⋯ ρ̄f)
              ( subst-Tm-irrel (sym (NF-inner eq) ■ EC) (BScope-++ᵗᵗ u V p) _
              ■ Bσ-++ᵗᵗ u V σ y )
          ■ fwdPt wf y )
      ■ sym (subst-■ Tm EC (sym EC) _)
      ■ subst-Tm-refl (EC ■ sym EC) _

    es₁≡ : es₁ ≡ subst (List ∘ Tm) (BScope-++ᵗᵗ u V′ p)
                   (map (_⋯ Bσ T′ σ) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ []))
    es₁≡ =
        sym (map-fuse ρ̄ᵇ ρ̄ᵇ⁻ es₁ ■ map-⋯-id cancel es₁)
      ■ cong (map (_⋯ ρ̄ᵇ⁻))
          ( subst-move (NF-inner eq) (NF-thr eq)
          ■ subst-img (sym (NF-inner eq)) (Bσ T σ) es )
      ■ map-++ᴸ ρ̄ᵇ⁻ (map (_⋯ (λ y → subst Tm (sym (NF-inner eq)) (Bσ T σ y))) es)
                (K `unit ∷ [])
      ■ cong (_++ (K `unit ∷ []))
          ( map-fuseₛᵣ (λ y → subst Tm (sym (NF-inner eq)) (Bσ T σ y)) ρ̄ᵇ⁻ es
          ■ map-⋯-congₛ bwdPt es
          ■ sym (map-fuseᵣₛ (t₂ ↑ᵗᵉˡ χ) (Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) es) )
      ■ step3ᵇ
      where
        step3ᵇ : map (_⋯ Bσ (t₂ ⋯ᵗᵉˡ χ) σᴳ″) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ [])
                   ≡ subst (List ∘ Tm) (BScope-++ᵗᵗ u V′ p)
                       (map (_⋯ Bσ T′ σ) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es) ++ (K `unit ∷ []))
        step3ᵇ = sym ( subst-img (BScope-++ᵗᵗ u V′ p) (Bσ T′ σ) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es)
                     ■ cong (_++ (K `unit ∷ []))
                         (map-⋯-congₛ (λ y → Bσ-++ᵗᵗ u V′ σ y) (map (_⋯ (t₂ ↑ᵗᵉˡ χ)) es)) )

------------------------------------------------------------------------
-- A `~ᵩ`-only drag: the moving run crosses a stationary RUN, so only
-- `φφᵩ` fires (mirrors Factor's `drag-sound`, which uses full `~`).
------------------------------------------------------------------------

private
  Run-shift1 : ∀ {n j} {s : Tel n j} → Run s → Run (shift1 s)
  Run-shift1 rnil   = rnil
  Run-shift1 (rφ w) = rφ (Run-shift1 w)

  ~ᵩ-prefix : ∀ {n j} (S : Tel n j) {N₁ N₂ : NF j} → N₁ ~ᵩ N₂ →
              prefixNF S N₁ ~ᵩ prefixNF S N₂
  ~ᵩ-prefix []       c = c
  ~ᵩ-prefix (tν S)   c = ~ᵩ-νNF (~ᵩ-prefix S c)
  ~ᵩ-prefix (tφ f S) c = ~ᵩ-φNF (~ᵩ-prefix S c)

  bubbleφᵩ : ∀ {n j k} {s : Tel n j} (rs : Run s) (f : Flag)
             (u : Tel (1 + j) k) (es : List (Tm k)) →
             mkNF (tφ f (shift1 s ++ᵗ u)) es
               ~ᵩ mkNF (s ++ᵗ tφ f u) (map (_⋯ liftId u (bubφ s)) es)
  bubbleφᵩ rnil f u es =
    ≡→~ᵩ (cong (mkNF (tφ f u)) (sym (map-⋯-id (liftId-id u (λ _ → refl)) es)))
  bubbleφᵩ (rφ {f = g} {r = s} rs) f u es =
    ~ᵩ-trans (Eq*.return (φφᵩ [] f g (shift1 s ++ᵗ u) es))
      (~ᵩ-trans
        (~ᵩ-φNF (bubbleφᵩ rs f u
                  (map (_⋯ liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1)) es)))
        (≡→~ᵩ (cong (mkNF (tφ g (s ++ᵗ tφ f u)))
                    ( map-fuse (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1))
                               (liftId u (bubφ s)) es
                    ■ map-⋯-cong fuse es ))))
    where
      fuse : ∀ x → liftId u (bubφ s) (liftId (shift1 s ++ᵗ u) (assocSwapᵣ 1 1) x)
                     ≡ liftId u (bubφ (tφ g s)) x
      fuse x = cong (liftId u (bubφ s)) (liftId-++ᵗ (shift1 s) u (assocSwapᵣ 1 1) x)
                 ■ liftId-· u (liftId (shift1 s) (assocSwapᵣ 1 1)) (bubφ s) x

  bubbleφᵩ⁻ : ∀ {n j k} {s : Tel n j} (rs : Run s) (f : Flag)
              (u : Tel (1 + j) k) (es : List (Tm k)) →
              mkNF (s ++ᵗ tφ f u) es
                ~ᵩ mkNF (tφ f (shift1 s ++ᵗ u)) (map (_⋯ liftId u (bubφ⁻ s)) es)
  bubbleφᵩ⁻ {s = s} rs f u es =
    ~ᵩ-trans (≡→~ᵩ (cong (mkNF (s ++ᵗ tφ f u)) (sym undo)))
             (~ᵩ-sym (bubbleφᵩ rs f u (map (_⋯ liftId u (bubφ⁻ s)) es)))
    where
      undo : map (_⋯ liftId u (bubφ s)) (map (_⋯ liftId u (bubφ⁻ s)) es) ≡ es
      undo = map-fuse (liftId u (bubφ⁻ s)) (liftId u (bubφ s)) es
               ■ map-⋯-id (λ x → liftId-· u (bubφ⁻ s) (bubφ s) x
                                   ■ liftId-id u (bubφ-inv s) x) es

  drag-soundᵩ : ∀ {p′ j m k} {S : Tel p′ j} (rS : Run S) {r : Tel j m}
                (w : Run r) (t : Tel m k) (es : List (Tm k)) →
                mkNF (S ++ᵗ (r ++ᵗ t)) es
                  ~ᵩ mkNF (dragTel S w t) (map (_⋯ dragRen S w t) es)
  drag-soundᵩ {S = S} rS rnil t es =
    ≡→~ᵩ (cong (mkNF (S ++ᵗ t)) (sym (map-⋯-id (λ _ → refl) es)))
  drag-soundᵩ {S = S} rS (rφ {f = f} {r = r} w) t es =
    ~ᵩ-trans (bubbleφᵩ⁻ rS f (r ++ᵗ t) es)
      (~ᵩ-trans
        (~ᵩ-φNF (drag-soundᵩ (Run-shift1 rS) w t
                  (map (_⋯ liftId (r ++ᵗ t) (bubφ⁻ S)) es)))
        (≡→~ᵩ (cong (mkNF (tφ f (dragTel (shift1 S) w t)))
                    (map-fuse (liftId (r ++ᵗ t) (bubφ⁻ S))
                              (dragRen (shift1 S) w t) es))))

------------------------------------------------------------------------
-- The run flags of a canonical φ-nest run are its sync flags.
------------------------------------------------------------------------

private
  runFlags-run-subst : ∀ {n k k′} (e : k ≡ k′) {t : Tel n k} (w : Run t) →
                       runFlags (run-subst e w) ≡ runFlags w
  runFlags-run-subst refl w = refl

  runFlags-φTelᵣ : ∀ (B : BindGroup) (c : ℕ) →
                   runFlags (Run-φTelᵣ B c) ≡ syncFlags B
  runFlags-φTelᵣ []              c = refl
  runFlags-φTelᵣ (_ ∷ [])        c = refl
  runFlags-φTelᵣ (b ∷ B@(_ ∷ _)) c = cong (ϕ[ b ] ∷_) (runFlags-φTelᵣ B (suc c))

  runFlags-φTel : ∀ (B : BindGroup) (c : ℕ) →
                  runFlags (Run-φTel B c) ≡ syncFlags B
  runFlags-φTel B c =
    runFlags-run-subst (scope≡ B c) (Run-φTelᵣ B c) ■ runFlags-φTelᵣ B c

  subst-Tel-irrel : ∀ {nn c d} (p q : c ≡ d) (t : Tel nn c) →
                    subst (Tel nn) p t ≡ subst (Tel nn) q t
  subst-Tel-irrel {nn} p q t = cong (λ e → subst (Tel nn) e t) (≡-irrelevant p q)

------------------------------------------------------------------------
-- The endpoint-flip residue.
------------------------------------------------------------------------

flipResidue : FlipResidue
flipResidue {m} {q₀} {k₀} {p} u G₁ G₂ t₀ es σ s v es₁ pre≡ Y≡ eq
  with shape-det s (BTel u p) (sym pre≡ ■ sym (shape-prenex-image u p))
... | refl , refl
  with shape-det v
        ((φTel G₁ (2 + BScope u p) ++ᵗ φTel G₂ (syncs G₁ + (2 + BScope u p)))
          ++ᵗ BTel t₀ (syncs G₂ + (syncs G₁ + (2 + BScope u p))))
        ( sym Y≡
        ■ sym ( shape-++ᵗ (φTel G₁ (2 + BScope u p) ++ᵗ φTel G₂ (syncs G₁ + (2 + BScope u p)))
                          (BTel t₀ (syncs G₂ + (syncs G₁ + (2 + BScope u p))))
              ■ cong₂ _++_
                  ( shape-++ᵗ (φTel G₁ (2 + BScope u p))
                              (φTel G₂ (syncs G₁ + (2 + BScope u p)))
                  ■ cong₂ _++_ (shape-φTel G₁ (2 + BScope u p))
                               (shape-φTel G₂ (syncs G₁ + (2 + BScope u p))) )
                  (shape-prenex-image t₀ (syncs G₂ + (syncs G₁ + (2 + BScope u p)))) ) )
... | refl , refl =
  ~ᵩ-trans (≡→~ᵩ startEq)
    (~ᵩ-trans (≡→~ᵩ (sym (prefixNF-++ᵗ (BTel u p) (mkNF (tν (nest₁ ++ᵗ (nest₂ ++ᵗ BTel t₀ nB₁))) ES0))))
      (~ᵩ-trans (~ᵩ-prefix (BTel u p) (~ᵩ-νNF (drag-soundᵩ (Run-φTel G₁ (2 + nB)) w₂ (BTel t₀ nB₁) ES0)))
        (~ᵩ-trans (≡→~ᵩ (prefixNF-++ᵗ (BTel u p) (mkNF (tν (dragTel nest₁ w₂ (BTel t₀ nB₁))) (map (_⋯ dragRen nest₁ w₂ (BTel t₀ nB₁)) ES0))))
          (≡→~ᵩ (mkNF-cong eqk′ telPart thrPart)))))
  where
    nB = BScope u p
    nB₁ = syncs G₂ + (syncs G₁ + (2 + nB))
    sG1 = syncs G₁ ; sG2 = syncs G₂

    σ₀ = Bσ u σ
    σᴳ  = νImage.σ′ G₁ G₂ σ₀
    σᴳᵇ = νImage.σ′ G₂ G₁ σ₀

    swp : (sum G₁ + sum G₂ + q₀) →ᵣ (sum G₂ + sum G₁ + q₀)
    swp = swapᵣ (sum G₁) (sum G₂)

    V  = tνᵗ G₁ G₂ t₀
    V′ = tνᵗ G₂ G₁ (t₀ ⋯ᵗᵉˡ swp)
    T  = u ++ᵗᵗ V
    T′ = u ++ᵗᵗ V′

    nest₁ = φTel G₁ (2 + nB)
    nest₂ = φTel G₂ (sG1 + (2 + nB))
    vC = (nest₁ ++ᵗ nest₂) ++ᵗ BTel t₀ nB₁

    open BridgeFlip G₁ G₂ {nB}

    w₂ : Run nest₂
    w₂ = Run-φTel G₂ (sG1 + (2 + nB))

    ρ̂fl : nB₁ →ᵣ nB₁
    ρ̂fl = liftId nestᴮ (swapᵣ 1 1) ·ₖ dragRen nest₁ w₂ []

    -- the identified thread list
    pwT : ∀ y → subst Tm (sym (NF-inner eq)) (Bσ T σ y) ≡ Bσ t₀ σᴳ y
    pwT y = subst-Tm-irrel (sym (NF-inner eq)) (BScope-++ᵗᵗ u V p) _
          ■ Bσ-++ᵗᵗ u V σ y

    step0 : es₁ ≡ map (_⋯ Bσ t₀ σᴳ) es ++ (K `unit ∷ [])
    step0 = subst-move (NF-inner eq) (NF-thr eq)
          ■ subst-img (sym (NF-inner eq)) (Bσ T σ) es
          ■ cong (_++ (K `unit ∷ [])) (map-⋯-congₛ pwT es)

    ES0 = map (_⋯ liftId vC (swapᵣ 1 1))
              (map (_⋯ Bσ t₀ σᴳ) es ++ (K `unit ∷ []))

    startEq : mkNF (BTel u p ++ᵗ tν vC) (map (_⋯ liftId vC (swapᵣ 1 1)) es₁)
                ≡ mkNF (BTel u p ++ᵗ tν (nest₁ ++ᵗ (nest₂ ++ᵗ BTel t₀ nB₁))) ES0
    startEq = cong₂ (λ z zs → mkNF (BTel u p ++ᵗ tν z) zs)
                (++ᵗ-assoc nest₁ nest₂ (BTel t₀ nB₁))
                (cong (map (_⋯ liftId vC (swapᵣ 1 1))) step0)

    -- the flip intertwiner via subEq-gen
    ñ₁ : ℕ
    ñ₁ = sG1 + (sG2 + (2 + nB))

    g₁ : nB₁ →ᵣ ñ₁
    g₁ = assocSwapᵣ sG2 sG1

    g₂ : ñ₁ →ᵣ ñ₁
    g₂ = (swapᵣ 1 1 ↑* sG2) ↑* sG1

    Ψc : 𝔽 nB₁ → 𝔽 ñ₁
    Ψc = g₁ ·ₖ g₂

    intertwine-fl : ∀ x → σᴳ x ⋯ ρ̂fl ≡ subst Tm eqΨ (σᴳᵇ (swp x))
    intertwine-fl x =
        ⋯-cong (σᴳ x) (bridge-flip w₂)
      ■ ⋯-cast𝔽 eqΨ Ψc (σᴳ x)
      ■ cong (subst Tm eqΨ) innerEq
      where
        innerEq : σᴳ x ⋯ Ψc ≡ σᴳᵇ (swp x)
        innerEq =
            sym (fusion (σᴳ x) g₁ g₂)
          ■ cong (λ t → (t ⋯ g₁) ⋯ g₂) (σ′-leafσ G₁ G₂ σ₀ x)
          ■ subEq-gen σ₀ G₁ G₂ x
          ■ sym (σ′-leafσ G₂ G₁ σ₀ (swp x))

    ECfl : BScope (t₀ ⋯ᵗᵉˡ swp) ñ₁ ≡ BScope t₀ nB₁
    ECfl = BScope-⋯ᵗᵉˡ t₀ swp ñ₁ ■ cong (BScope t₀) eqΨ

    flPt : ∀ y → Bσ t₀ (σᴳ ·ₖ ρ̂fl) y
                   ≡ subst Tm ECfl (Bσ (t₀ ⋯ᵗᵉˡ swp) σᴳᵇ ((t₀ ↑ᵗᵉˡ swp) y))
    flPt y =
        Bσ-cong t₀ intertwine-fl y
      ■ Bσ-base-subst t₀ eqΨ (swp ·ₖ σᴳᵇ) y
      ■ cong (subst Tm (cong (BScope t₀) eqΨ)) mid
      ■ sym (subst-■ Tm (BScope-⋯ᵗᵉˡ t₀ swp ñ₁) (cong (BScope t₀) eqΨ) _)
      where
        mid : Bσ t₀ (swp ·ₖ σᴳᵇ) y
                ≡ subst Tm (BScope-⋯ᵗᵉˡ t₀ swp ñ₁) (Bσ (t₀ ⋯ᵗᵉˡ swp) σᴳᵇ ((t₀ ↑ᵗᵉˡ swp) y))
        mid = subst-move (sym (BScope-⋯ᵗᵉˡ t₀ swp ñ₁)) (law2Pt t₀ swp σᴳᵇ y)
            ■ subst-Tm-irrel (sym (sym (BScope-⋯ᵗᵉˡ t₀ swp ñ₁))) (BScope-⋯ᵗᵉˡ t₀ swp ñ₁) _

    factor : ∀ x → (liftId vC (swapᵣ 1 1) ·ₖ dragRen nest₁ w₂ (BTel t₀ nB₁)) x
                     ≡ liftId (BTel t₀ nB₁) ρ̂fl x
    factor x =
        cong (dragRen nest₁ w₂ (BTel t₀ nB₁))
          (liftId-++ᵗ (nest₁ ++ᵗ nest₂) (BTel t₀ nB₁) (swapᵣ 1 1) x)
      ■ dragRen-factor nest₁ w₂ (BTel t₀ nB₁)
          (liftId (BTel t₀ nB₁) (liftId (nest₁ ++ᵗ nest₂) (swapᵣ 1 1)) x)
      ■ liftId-· (BTel t₀ nB₁) (liftId (nest₁ ++ᵗ nest₂) (swapᵣ 1 1))
                 (dragRen nest₁ w₂ []) x

    eqk′ : BScope t₀ nB₁ ≡ BScope T′ p
    eqk′ = sym (BScope-++ᵗᵗ u V′ p ■ BScope-⋯ᵗᵉˡ t₀ swp ñ₁ ■ cong (BScope t₀) eqΨ)

    shapeEq : shape (BTel u p ++ᵗ tν (dragTel nest₁ w₂ (BTel t₀ nB₁)))
                ≡ shape (BTel T′ p)
    shapeEq =
        shape-++ᵗ (BTel u p) (tν (dragTel nest₁ w₂ (BTel t₀ nB₁)))
      ■ cong₂ (λ z₁ z₂ → z₁ ++ (sν ∷ z₂))
          (shape-prenex-image u p)
          ( shape-dragTel nest₁ w₂ (BTel t₀ nB₁)
          ■ cong₂ (λ z₁ z₂ → map sφ z₁ ++ z₂)
              (runFlags-φTel G₂ (sG1 + (2 + nB)))
              (cong₂ _++_ (shape-φTel G₁ (2 + nB)) (shape-prenex-image t₀ nB₁)) )
      ■ cong (BShape u ++_)
          (cong (sν ∷_)
            (sym (L.++-assoc (map sφ (syncFlags G₂)) (map sφ (syncFlags G₁)) (BShape t₀))))
      ■ sym
        ( shape-prenex-image T′ p
        ■ BShape-++ᵗᵗ u V′
        ■ cong (BShape u ++_)
            (cong (λ z → sν ∷ (map sφ (syncFlags G₂) ++ map sφ (syncFlags G₁)) ++ z)
              (BShape-⋯ᵗᵉˡ t₀ swp)) )

    telPart : subst (Tel p) eqk′ (BTel u p ++ᵗ tν (dragTel nest₁ w₂ (BTel t₀ nB₁)))
                ≡ BTel T′ p
    telPart with shape-det (BTel u p ++ᵗ tν (dragTel nest₁ w₂ (BTel t₀ nB₁)))
                           (BTel T′ p) shapeEq
    ... | e′ , tp = subst-Tel-irrel eqk′ e′ _ ■ tp

    thrPart : subst (List ∘ Tm) eqk′ (map (_⋯ dragRen nest₁ w₂ (BTel t₀ nB₁)) ES0)
                ≡ map (_⋯ Bσ T′ σ) (map (_⋯ (t₀ ↑ᵗᵉˡ swp)) es) ++ (K `unit ∷ [])
    thrPart =
        cong (subst (List ∘ Tm) eqk′)
          ( map-fuse (liftId vC (swapᵣ 1 1)) (dragRen nest₁ w₂ (BTel t₀ nB₁))
              (map (_⋯ Bσ t₀ σᴳ) es ++ (K `unit ∷ []))
          ■ map-⋯-cong factor (map (_⋯ Bσ t₀ σᴳ) es ++ (K `unit ∷ []))
          ■ law t₀ es σᴳ ρ̂fl
          ■ cong (_++ (K `unit ∷ [])) (map-⋯-congₛ flPt es)
          ■ sym ( cong (subst (List ∘ Tm) ECfl)
                    (cong (_++ (K `unit ∷ []))
                      (map-fuseᵣₛ (t₀ ↑ᵗᵉˡ swp) (Bσ (t₀ ⋯ᵗᵉˡ swp) σᴳᵇ) es))
                ■ subst-img ECfl ((t₀ ↑ᵗᵉˡ swp) ·ₖ Bσ (t₀ ⋯ᵗᵉˡ swp) σᴳᵇ) es )
          ■ cong (subst (List ∘ Tm) ECfl) step3fl )
      ■ collapse3 (BScope-++ᵗᵗ u V′ p) ECfl eqk′ _
      where
        step3fl : map (_⋯ Bσ (t₀ ⋯ᵗᵉˡ swp) σᴳᵇ) (map (_⋯ (t₀ ↑ᵗᵉˡ swp)) es) ++ (K `unit ∷ [])
                    ≡ subst (List ∘ Tm) (BScope-++ᵗᵗ u V′ p)
                        (map (_⋯ Bσ T′ σ) (map (_⋯ (t₀ ↑ᵗᵉˡ swp)) es) ++ (K `unit ∷ []))
        step3fl = sym ( subst-img (BScope-++ᵗᵗ u V′ p) (Bσ T′ σ) (map (_⋯ (t₀ ↑ᵗᵉˡ swp)) es)
                      ■ cong (_++ (K `unit ∷ []))
                          (map-⋯-congₛ (λ y → Bσ-++ᵗᵗ u V′ σ y) (map (_⋯ (t₀ ↑ᵗᵉˡ swp)) es)) )
