-- | Phase 5.1 of the backward simulation `UntypedSoup → Typed`
--   (`BackwardSoup/PLAN.md` §12.2, P5.1): the forward image transport along
--   the structural congruence RESPECTS the syntactic thread tracking of
--   `BackwardSoup/Tracks.agda`.
--
--   `≋-image` (`ForwardSoup/LocalImage/Struct.agda`) moves a `LocalImage`
--   along a derivation `d : P ≋ Q`, but its type hides the thread map: the
--   result is only `Σ lc′. LocalImage Q lc′ …`.  The backward proof needs to
--   know WHERE the redex thread of `P` ends up in `Q` (`PLAN.md` §12.1), and
--   `Tracks d a b` is exactly the syntactic record of that.  This module
--   closes the loop:
--
--     `Tracks d a b  ⟹  threadEmbedding (≋-image d I) b ≡ threadEmbedding I a`
--
--   i.e. the transported image sends the tracked target thread `b` to the very
--   soup slot that the original image assigns to the source thread `a`.
--
--   Exports: the two per-axiom lemmas `≋′-image-tracks` / `≋′-image⁻-tracks`
--   and the induction `≋-image-tracks` over the equivalence closure, plus the
--   three transport lemmas for the ways `Struct.agda` rewrites an image
--   (`proc-image-embedding`, `subst-channels-embedding`,
--   `restriction-swap-embedding`).
--
--   The supporting `Fin` arithmetic is private: `Fin.cast` against `_↑ˡ_`,
--   `_↑ʳ_` and `_+_`-associativity (all by `Fin.toℕ`-injectivity), the two
--   directions of the `splitAt`/`cast` interaction that `ν-ext′` needs, and
--   `assoc-composite` — the composite of the FIVE reindexings that
--   `≋′-image⁻ ∥-assoc′` performs is a single `Fin.cast`.
module BorrowedCF.Simulation.BackwardSoup.TracksImage where

open import Data.Nat.ListAction using (sum)
open import Data.Nat using () renaming (_*_ to _*ℕ_)

open import BorrowedCF.Prelude

import BorrowedCF.Processes.Typed as Typed
import BorrowedCF.Processes.TranslationSoup as Translation
import BorrowedCF.Processes.UntypedSoup as Soup
import BorrowedCF.Terms.Base as Source

open import BorrowedCF.Processes.Congruence using (swapₚ-inv)

open import BorrowedCF.Simulation.ForwardSoup.Translation
  using (processCount-rename)

open import BorrowedCF.Simulation.ForwardSoup.LocalImage
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Congruence
  using (swap-↑ˡ; swap-↑ʳ)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Restriction
  using (restriction-swap-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Extrusion
  using (extrusionRenaming)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Parallel
  using (split-elim; par-split-left; par-split-right)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Bind
  using (res-split-image)
open import BorrowedCF.Simulation.ForwardSoup.LocalImage.Struct
  using (proc-image; ≋′-image; ≋′-image⁻; ≋-image)

open import BorrowedCF.Simulation.BackwardSoup.Tracks
  using ( Tracks′; comm-l; comm-r; assoc; unit; swap-ν; comm-ν; ext-ν
        ; cong-l; cong-r; cong-ν
        ; Tracks; track-ε; track-fwd; track-bwd)

-- Not re-exported: a plain `open` only brings the name into scope.
open Translation using () renaming (processCount to pc)

------------------------------------------------------------------------
-- 1.  `Fin` arithmetic.
--
-- Every equation below relates injections built from `_↑ˡ_`, `_↑ʳ_` and
-- `Fin.cast`; all of them are settled by `Fin.toℕ`.

private
  tn : {a : ℕ} → 𝔽 a → ℕ
  tn = Fin.toℕ

  tn-cast : {a b : ℕ} (equal : a ≡ b) (i : 𝔽 a) → tn (Fin.cast equal i) ≡ tn i
  tn-cast equal i = Fin.toℕ-cast equal i

  tn-l : {a : ℕ} (i : 𝔽 a) (b : ℕ) → tn (i ↑ˡ b) ≡ tn i
  tn-l = Fin.toℕ-↑ˡ

  tn-r : (a : ℕ) {b : ℕ} (i : 𝔽 b) → tn (a ↑ʳ i) ≡ a + tn i
  tn-r a i = Fin.toℕ-↑ʳ a i

  -- A cast is determined by its effect on `Fin.toℕ`.
  castℕ :
    {a b : ℕ} (equal : a ≡ b) {i : 𝔽 a} {j : 𝔽 b} →
    tn i ≡ tn j → Fin.cast equal i ≡ j
  castℕ equal {i = i} same = Fin.toℕ-injective (tn-cast equal i ■ same)

  -- Two casts with a common target agree as soon as their sources do.
  castℕ′ :
    {a b c : ℕ} (equal₁ : a ≡ c) (equal₂ : b ≡ c) {i : 𝔽 a} {j : 𝔽 b} →
    tn i ≡ tn j → Fin.cast equal₁ i ≡ Fin.cast equal₂ j
  castℕ′ equal₁ equal₂ {i = i} {j = j} same =
    Fin.toℕ-injective (tn-cast equal₁ i ■ same ■ sym (tn-cast equal₂ j))

  ----------------------------------------------------------------------
  -- Casting a sum on its left summand.

  cast-+-↑ˡ :
    {p p′ : ℕ} (q : ℕ) (equal : p ≡ p′) (wide : p + q ≡ p′ + q) (x : 𝔽 p) →
    Fin.cast wide (x ↑ˡ q) ≡ Fin.cast equal x ↑ˡ q
  cast-+-↑ˡ q equal wide x =
    castℕ wide
      (tn-l x q ■ sym (tn-l (Fin.cast equal x) q ■ tn-cast equal x))

  cast-+-↑ʳ :
    {p p′ q : ℕ} (equal : p ≡ p′) (wide : p + q ≡ p′ + q) (y : 𝔽 q) →
    Fin.cast wide (p ↑ʳ y) ≡ p′ ↑ʳ y
  cast-+-↑ʳ {p = p} {p′ = p′} equal wide y =
    castℕ wide (tn-r p y ■ cong (_+ tn y) equal ■ sym (tn-r p′ y))

  ----------------------------------------------------------------------
  -- Casting along `+-assoc`, in both directions, on each of the three blocks.

  cast-assoc-ll :
    {a : ℕ} (b c : ℕ) (x : 𝔽 a) →
    Fin.cast (+-assoc a b c) ((x ↑ˡ b) ↑ˡ c) ≡ x ↑ˡ (b + c)
  cast-assoc-ll {a = a} b c x =
    castℕ (+-assoc a b c)
      (tn-l (x ↑ˡ b) c ■ tn-l x b ■ sym (tn-l x (b + c)))

  cast-assoc-rl :
    (a : ℕ) {b : ℕ} (c : ℕ) (y : 𝔽 b) →
    Fin.cast (+-assoc a b c) ((a ↑ʳ y) ↑ˡ c) ≡ a ↑ʳ (y ↑ˡ c)
  cast-assoc-rl a {b = b} c y =
    castℕ (+-assoc a b c)
      (tn-l (a ↑ʳ y) c ■ tn-r a y ■
       sym (tn-r a (y ↑ˡ c) ■ cong (a +_) (tn-l y c)))

  cast-assoc-rr :
    (a b : ℕ) {c : ℕ} (z : 𝔽 c) →
    Fin.cast (+-assoc a b c) ((a + b) ↑ʳ z) ≡ a ↑ʳ (b ↑ʳ z)
  cast-assoc-rr a b {c = c} z =
    castℕ (+-assoc a b c)
      (tn-r (a + b) z ■ +-assoc a b (tn z) ■
       sym (tn-r a (b ↑ʳ z) ■ cong (a +_) (tn-r b z)))

  cast-assoc-ll⁻ :
    {a : ℕ} (b c : ℕ) (x : 𝔽 a) →
    Fin.cast (sym (+-assoc a b c)) (x ↑ˡ (b + c)) ≡ (x ↑ˡ b) ↑ˡ c
  cast-assoc-ll⁻ {a = a} b c x =
    castℕ (sym (+-assoc a b c))
      (tn-l x (b + c) ■ sym (tn-l (x ↑ˡ b) c ■ tn-l x b))

  cast-assoc-rl⁻ :
    (a : ℕ) {b : ℕ} (c : ℕ) (y : 𝔽 b) →
    Fin.cast (sym (+-assoc a b c)) (a ↑ʳ (y ↑ˡ c)) ≡ (a ↑ʳ y) ↑ˡ c
  cast-assoc-rl⁻ a {b = b} c y =
    castℕ (sym (+-assoc a b c))
      (tn-r a (y ↑ˡ c) ■ cong (a +_) (tn-l y c) ■
       sym (tn-l (a ↑ʳ y) c ■ tn-r a y))

  cast-assoc-rr⁻ :
    (a b : ℕ) {c : ℕ} (z : 𝔽 c) →
    Fin.cast (sym (+-assoc a b c)) (a ↑ʳ (b ↑ʳ z)) ≡ (a + b) ↑ʳ z
  cast-assoc-rr⁻ a b {c = c} z =
    castℕ (sym (+-assoc a b c))
      (tn-r a (b ↑ʳ z) ■ cong (a +_) (tn-r b z) ■
       sym (+-assoc a b (tn z)) ■ sym (tn-r (a + b) z))

  ----------------------------------------------------------------------
  -- The composite of the five reindexings performed by `≋′-image⁻ ∥-assoc′`
  -- (swap, assoc, swap, assoc, swap) is the cast along `sym (+-assoc p q r)`.

  assoc-composite :
    (p q r : ℕ) (i : 𝔽 (p + (q + r))) →
    Fin.swap r
      (Fin.cast (+-assoc r p q)
        (Fin.swap q (Fin.cast (+-assoc q r p) (Fin.swap p i))))
    ≡ Fin.cast (sym (+-assoc p q r)) i
  assoc-composite p q r =
    split-elim p Motive leftBlock
      (split-elim q (λ j → Motive (p ↑ʳ j)) middleBlock rightBlock)
    where
    Motive : 𝔽 (p + (q + r)) → Set
    Motive i =
      Fin.swap r
        (Fin.cast (+-assoc r p q)
          (Fin.swap q (Fin.cast (+-assoc q r p) (Fin.swap p i))))
      ≡ Fin.cast (sym (+-assoc p q r)) i

    outer : 𝔽 (r + (p + q)) → 𝔽 ((p + q) + r)
    outer = Fin.swap r

    step₄ : 𝔽 ((r + p) + q) → 𝔽 ((p + q) + r)
    step₄ z = outer (Fin.cast (+-assoc r p q) z)

    step₃ : 𝔽 (q + (r + p)) → 𝔽 ((p + q) + r)
    step₃ z = step₄ (Fin.swap q z)

    step₂ : 𝔽 ((q + r) + p) → 𝔽 ((p + q) + r)
    step₂ z = step₃ (Fin.cast (+-assoc q r p) z)

    leftBlock : (x : 𝔽 p) → Motive (x ↑ˡ (q + r))
    leftBlock x =
      cong step₂ (swap-↑ˡ (q + r) x) ■
      cong step₃ (cast-assoc-rr q r x) ■
      cong step₄ (swap-↑ʳ q (r ↑ʳ x)) ■
      cong outer (cast-assoc-rl r q x) ■
      swap-↑ʳ r (x ↑ˡ q) ■
      sym (cast-assoc-ll⁻ q r x)

    middleBlock : (y : 𝔽 q) → Motive (p ↑ʳ (y ↑ˡ r))
    middleBlock y =
      cong step₂ (swap-↑ʳ p (y ↑ˡ r)) ■
      cong step₃ (cast-assoc-ll r p y) ■
      cong step₄ (swap-↑ˡ (r + p) y) ■
      cong outer (cast-assoc-rr r p y) ■
      swap-↑ʳ r (p ↑ʳ y) ■
      sym (cast-assoc-rl⁻ p r y)

    rightBlock : (z : 𝔽 r) → Motive (p ↑ʳ (q ↑ʳ z))
    rightBlock z =
      cong step₂ (swap-↑ʳ p (q ↑ʳ z)) ■
      cong step₃ (cast-assoc-rl q p z) ■
      cong step₄ (swap-↑ʳ q (z ↑ˡ p)) ■
      cong outer (cast-assoc-ll p q z) ■
      swap-↑ˡ (p + q) z ■
      sym (cast-assoc-rr⁻ p q z)

  ----------------------------------------------------------------------
  -- The two directions of the thread map of `extrusion-reindex`.

  -- Forward: `threadBackward` undoes the cast that `Tracks′.ext-ν` records.
  extrusion-back :
    {p p′ : ℕ} (q : ℕ) (equal : p′ ≡ p) (wide : p + q ≡ p′ + q)
    (back : 𝔽 p′ → 𝔽 p) →
    ((x : 𝔽 p′) → back x ≡ Fin.cast equal x) →
    (i : 𝔽 (p + q)) →
    [ (λ x → back x ↑ˡ q) , (λ y → p ↑ʳ y) ]′
      (Fin.splitAt p′ (Fin.cast wide i))
    ≡ i
  extrusion-back {p = p} {p′ = p′} q equal wide back backEq =
    split-elim p Motive leftBlock rightBlock
    where
    parts : 𝔽 p′ ⊎ 𝔽 q → 𝔽 (p + q)
    parts = [ (λ x → back x ↑ˡ q) , (λ y → p ↑ʳ y) ]′

    Motive : 𝔽 (p + q) → Set
    Motive i = parts (Fin.splitAt p′ (Fin.cast wide i)) ≡ i

    narrow : p ≡ p′
    narrow = sym equal

    leftBlock : (x : 𝔽 p) → Motive (x ↑ˡ q)
    leftBlock x =
      cong (λ z → parts (Fin.splitAt p′ z)) (cast-+-↑ˡ q narrow wide x) ■
      cong parts (Fin.splitAt-↑ˡ p′ (Fin.cast narrow x) q) ■
      cong (_↑ˡ q)
        (backEq (Fin.cast narrow x) ■ Fin.cast-involutive equal narrow x)

    rightBlock : (y : 𝔽 q) → Motive (p ↑ʳ y)
    rightBlock y =
      cong (λ z → parts (Fin.splitAt p′ z)) (cast-+-↑ʳ narrow wide y) ■
      cong parts (Fin.splitAt-↑ʳ p′ q y)

  -- Backward: `threadForward` IS the cast that `Tracks′.ext-ν` records.
  extrusion-fwd :
    {p p′ : ℕ} (q : ℕ) (equal : p ≡ p′) (wide : p + q ≡ p′ + q)
    (ahead : 𝔽 p → 𝔽 p′) →
    ((x : 𝔽 p) → ahead x ≡ Fin.cast equal x) →
    (i : 𝔽 (p + q)) →
    [ (λ x → ahead x ↑ˡ q) , (λ y → p′ ↑ʳ y) ]′ (Fin.splitAt p i)
    ≡ Fin.cast wide i
  extrusion-fwd {p = p} {p′ = p′} q equal wide ahead aheadEq =
    split-elim p Motive leftBlock rightBlock
    where
    parts : 𝔽 p ⊎ 𝔽 q → 𝔽 (p′ + q)
    parts = [ (λ x → ahead x ↑ˡ q) , (λ y → p′ ↑ʳ y) ]′

    Motive : 𝔽 (p + q) → Set
    Motive i = parts (Fin.splitAt p i) ≡ Fin.cast wide i

    leftBlock : (x : 𝔽 p) → Motive (x ↑ˡ q)
    leftBlock x =
      cong parts (Fin.splitAt-↑ˡ p x q) ■
      cong (_↑ˡ q) (aheadEq x) ■
      sym (cast-+-↑ˡ q equal wide x)

    rightBlock : (y : 𝔽 q) → Motive (p ↑ʳ y)
    rightBlock y =
      cong parts (Fin.splitAt-↑ʳ p q y) ■ sym (cast-+-↑ʳ equal wide y)

------------------------------------------------------------------------
-- 2.  The three ways `Struct.agda` rewrites an image.

-- (a) Transport along an equality of PROCESSES (`≋′-image⁻ ν-swap′`).
proc-image-embedding :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (equal : P ≡ Q)
  (image : LocalImage P logicalChannels sigma ambientChannel ambientThread C)
  (a : 𝔽 (pc P)) (b : 𝔽 (pc Q)) →
  Fin.toℕ a ≡ Fin.toℕ b →
  threadEmbedding (proj₂ (proc-image equal image)) b ≡ threadEmbedding image a
proc-image-embedding refl image a b same =
  cong (threadEmbedding image) (Fin.toℕ-injective (sym same))

-- (b) Transport along an equality of LOGICAL CHANNEL VECTORS
--     (`≋′-image⁻ ν-comm′` and `≋′-image⁻ ν-ext′`).
subst-channels-embedding :
  {k n m : ℕ} {Q : Typed.Proc k}
  {logicalChannels logicalChannels′ :
    Vec (OrientedChannel n) (Translation.channelCount Q)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (equal : logicalChannels ≡ logicalChannels′)
  (image : LocalImage Q logicalChannels sigma ambientChannel ambientThread C)
  (b : 𝔽 (pc Q)) →
  threadEmbedding
    (subst
      (λ channels →
        LocalImage Q channels sigma ambientChannel ambientThread C)
      equal image)
    b
  ≡ threadEmbedding image b
subst-channels-embedding refl image b = refl

-- (c) `restriction-swap-image` inspects the ORIENTATION of the bound channel;
--     its thread map is the same cast in both clauses.
restriction-swap-embedding :
  {k n m : ℕ} {B₁ B₂ : Typed.BindGroup}
  {P : Typed.Proc (sum B₁ + sum B₂ + k)}
  {logicalChannels :
    Vec (OrientedChannel n) (Translation.channelCount (Typed.ν B₁ B₂ P))}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m}
  (image :
    LocalImage (Typed.ν B₁ B₂ P) logicalChannels sigma
      ambientChannel ambientThread C)
  (b : 𝔽 (pc (P Typed.⋯ₚ Source.swapᵣ (sum B₁) (sum B₂)))) →
  threadEmbedding (restriction-swap-image image) b ≡
  threadEmbedding image
    (Fin.cast (processCount-rename P (Source.swapᵣ (sum B₁) (sum B₂))) b)
restriction-swap-embedding
  {logicalChannels = (channel , forward) ∷ bodyChannels} image b = refl
restriction-swap-embedding
  {logicalChannels = (channel , reverse) ∷ bodyChannels} image b = refl

------------------------------------------------------------------------
-- 3.  A single congruence axiom, forwards.

≋′-image-tracks :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} {step : P Typed.≋′ Q}
  (image : LocalImage P logicalChannels sigma ambientChannel ambientThread C)
  {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks′ step a b →
  threadEmbedding (proj₂ (≋′-image step image)) b ≡ threadEmbedding image a

≋′-image-tracks image (comm-l {Q = Q} i) =
  cong (threadEmbedding image) (swap-↑ʳ (pc Q) i)

≋′-image-tracks image (comm-r {P = P} j) =
  cong (threadEmbedding image) (swap-↑ˡ (pc P) j)

≋′-image-tracks image (assoc {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} i) =
  cong (threadEmbedding image)
    (Fin.cast-involutive
      (+-assoc (pc P₁) (pc P₂) (pc P₃))
      (sym (+-assoc (pc P₁) (pc P₂) (pc P₃))) i)

≋′-image-tracks image (unit i) = refl

≋′-image-tracks image (swap-ν {B₁ = B₁} {B₂ = B₂} {P = P} i) =
  restriction-swap-embedding image (Fin.cast (sym renameEq) i) ■
  cong (threadEmbedding image)
    (Fin.cast-involutive renameEq (sym renameEq) i)
  where
  renameEq = processCount-rename P (Source.swapᵣ (sum B₁) (sum B₂))

≋′-image-tracks {logicalChannels = outerChannel ∷ innerChannel ∷ bodyChannels}
  image (comm-ν {B₁ = B₁} {B₂ = B₂} {A₁ = A₁} {A₂ = A₂} {P = P} i) =
  cong (threadEmbedding image)
    (Fin.cast-involutive renameEq (sym renameEq) i)
  where
  renameEq =
    processCount-rename P
      (Source.assocSwapᵣ (sum A₁ + sum A₂) (sum B₁ + sum B₂))

≋′-image-tracks image (ext-ν {P = P} {B₁ = B₁} {B₂ = B₂} {Q = Q} i) =
  cong (threadEmbedding image)
    (extrusion-back (pc Q) renameEq (cong (_+ pc Q) (sym renameEq))
      (Fin.cast renameEq) (λ _ → refl) i)
  where
  renameEq = processCount-rename P (extrusionRenaming B₁ B₂)

≋′-image-tracks image (cong-l {P₂ = P₂} {Q = Q} {s = inner} {b = b} t) =
  cong [ threadEmbedding (proj₂ (≋′-image inner (par-split-left image)))
       , threadEmbedding (par-split-right image)
       ]′
    (Fin.splitAt-↑ˡ (pc P₂) b (pc Q)) ■
  ≋′-image-tracks (par-split-left image) t

≋′-image-tracks image (cong-r {P₂ = P₂} {Q = Q} {s = inner} j) =
  cong [ threadEmbedding (proj₂ (≋′-image inner (par-split-left image)))
       , threadEmbedding (par-split-right image)
       ]′
    (Fin.splitAt-↑ʳ (pc P₂) (pc Q) j)

≋′-image-tracks {logicalChannels = boundChannel ∷ bodyChannels} image
  (cong-ν t) =
  ≋′-image-tracks (res-split-image image) t

------------------------------------------------------------------------
-- 4.  A single congruence axiom, backwards.

≋′-image⁻-tracks :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount Q)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} {step : P Typed.≋′ Q}
  (image : LocalImage Q logicalChannels sigma ambientChannel ambientThread C)
  {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks′ step a b →
  threadEmbedding (proj₂ (≋′-image⁻ step image)) a ≡ threadEmbedding image b

≋′-image⁻-tracks image (comm-l {Q = Q} i) =
  cong (threadEmbedding image) (swap-↑ˡ (pc Q) i)

≋′-image⁻-tracks image (comm-r {P = P} j) =
  cong (threadEmbedding image) (swap-↑ʳ (pc P) j)

≋′-image⁻-tracks image (assoc {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} i) =
  cong (threadEmbedding image) (assoc-composite (pc P₁) (pc P₂) (pc P₃) i)

≋′-image⁻-tracks image (unit i) = refl

≋′-image⁻-tracks image (swap-ν {B₁ = B₁} {B₂ = B₂} {P = P} i) =
  proc-image-embedding
    (cong (Typed.ν B₁ B₂) (swapₚ-inv {a = sum B₁} {b = sum B₂} P))
    (restriction-swap-image image)
    (Fin.cast (sym roundEq) i) i (tn-cast (sym roundEq) i) ■
  restriction-swap-embedding image (Fin.cast (sym roundEq) i) ■
  cong (threadEmbedding image)
    (castℕ′ innerEq (sym outerEq) (tn-cast (sym roundEq) i))
  where
  outerEq = processCount-rename P (Source.swapᵣ (sum B₁) (sum B₂))
  innerEq =
    processCount-rename (P Typed.⋯ₚ Source.swapᵣ (sum B₁) (sum B₂))
      (Source.swapᵣ (sum B₂) (sum B₁))
  roundEq = innerEq ■ outerEq

≋′-image⁻-tracks
  {logicalChannels = innerChannel ∷ outerChannel ∷ bodyChannels} image
  (comm-ν i) =
  subst-channels-embedding _ image _

≋′-image⁻-tracks {logicalChannels = boundChannel ∷ restChannels} image
  (ext-ν {P = P} {B₁ = B₁} {B₂ = B₂} {Q = Q} i) =
  subst-channels-embedding _ image _ ■
  cong (threadEmbedding image)
    (extrusion-fwd (pc Q) (sym renameEq) (cong (_+ pc Q) (sym renameEq))
      (Fin.cast (sym renameEq)) (λ _ → refl) i)
  where
  renameEq = processCount-rename P (extrusionRenaming B₁ B₂)

≋′-image⁻-tracks image (cong-l {P₁ = P₁} {Q = Q} {s = inner} {a = a} t) =
  cong [ threadEmbedding (proj₂ (≋′-image⁻ inner (par-split-left image)))
       , threadEmbedding (par-split-right image)
       ]′
    (Fin.splitAt-↑ˡ (pc P₁) a (pc Q)) ■
  ≋′-image⁻-tracks (par-split-left image) t

≋′-image⁻-tracks image (cong-r {P₁ = P₁} {Q = Q} {s = inner} j) =
  cong [ threadEmbedding (proj₂ (≋′-image⁻ inner (par-split-left image)))
       , threadEmbedding (par-split-right image)
       ]′
    (Fin.splitAt-↑ʳ (pc P₁) (pc Q) j)

≋′-image⁻-tracks {logicalChannels = boundChannel ∷ bodyChannels} image
  (cong-ν t) =
  ≋′-image⁻-tracks (res-split-image image) t

------------------------------------------------------------------------
-- 5.  A whole derivation.

≋-image-tracks :
  {k n m : ℕ} {P Q : Typed.Proc k}
  {logicalChannels : Vec (OrientedChannel n) (Translation.channelCount P)}
  {sigma : Translation.Env k (2 *ℕ n)}
  {ambientChannel : 𝔽 n → Set} {ambientThread : 𝔽 m → Set}
  {C : Soup.Config n m} {derivation : P Typed.≋ Q}
  (image : LocalImage P logicalChannels sigma ambientChannel ambientThread C)
  {a : 𝔽 (pc P)} {b : 𝔽 (pc Q)} →
  Tracks derivation a b →
  threadEmbedding (proj₂ (≋-image derivation image)) b ≡
  threadEmbedding image a
≋-image-tracks image (track-ε a) = refl
≋-image-tracks image (track-fwd {s = step} t rest) =
  ≋-image-tracks (proj₂ (≋′-image step image)) rest ■
  ≋′-image-tracks image t
≋-image-tracks image (track-bwd {s = step} t rest) =
  ≋-image-tracks (proj₂ (≋′-image⁻ step image)) rest ■
  ≋′-image⁻-tracks image t
