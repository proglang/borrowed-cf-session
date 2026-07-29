-- | General handle-position identification — the linchpin of the telescoped
--   backward channel-op reflections (REUSABLE across LSplit/RSplit/Com/Choice/
--   Close/Acq).
--
--   A channel-op redex borrows a ν-endpoint handle presented, in the flattened
--   image `leafσ σ BL BR`, as a chanTriple whose middle junction points at the
--   FIRST endpoint (`wkΦ Φfull 0F`, toℕ = syncs BL + syncs BR).  `handleId-block1`
--   recovers, from such an image equation, the bind-group decomposition
--   `BL = B₁ ++ (q + suc b₁) ∷ B₂` and the exact `atk (q ↑ʳ 0F)` handle variable
--   the typed R-<Op> rule fires on.
--
--   The core combinator `block-decomp` walks the blocks of a `Fin (sum B)`,
--   exposing which block it lands in and its offset — every position IS a
--   handle for its own decomposition.
module BorrowedCF.Simulation.Backward.HandleId where

open import BorrowedCF.Prelude
open import BorrowedCF.Terms
import BorrowedCF.Processes.Typed as TP
open TP using (BindGroup)
open import BorrowedCF.Reduction.Base using (Value; V-`; V-K; V-λ; V-⊗; V-⊕; value-⋯; VSub)
open import BorrowedCF.Simulation.Support.ReverseInv using (⊗-inj)
open import BorrowedCF.Processes.Translation using (Ub[_]; syncs; UChan)
open import BorrowedCF.Simulation.Support.Theorems.SplitsH1 using (canonₛ; leafσ; VSub-canonₛ)
open import BorrowedCF.Simulation.Support.TranslationProperties using (VChan)
open import BorrowedCF.Simulation.Support.Theorems.SplitsLQ using (Ub-triple; canonₛ-handleq)
open import BorrowedCF.Simulation.Support.BlockPerm using (toℕ-weaken*ᵣ)

open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List using ([]; _∷_; _++_)
open import Data.Fin.Base using (join; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; join-splitAt; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-suc; +-comm; m+[n∸m]≡n)

open Fin.Patterns

------------------------------------------------------------------------
-- Triple / subst micro-helpers.
------------------------------------------------------------------------

private
  `-inj : ∀ {p} {x y : 𝔽 p} → (` x) ≡ (` y) → x ≡ y
  `-inj refl = refl

  tripleℕ : ∀ {p} {a c a′ c′ : Tm p} {j j′ : 𝔽 p}
          → (a ⊗ (` j)) ⊗ c ≡ (a′ ⊗ (` j′)) ⊗ c′ → Fin.toℕ j ≡ Fin.toℕ j′
  tripleℕ eq = cong Fin.toℕ (`-inj (proj₂ (⊗-inj (proj₁ (⊗-inj eq)))))

  substTrip : ∀ {p qq} (eq : p ≡ qq) (A : Tm p) (jj : 𝔽 p) (C : Tm p) →
              subst Tm eq ((A ⊗ (` jj)) ⊗ C)
              ≡ (subst Tm eq A ⊗ (` subst 𝔽 eq jj)) ⊗ subst Tm eq C
  substTrip refl A jj C = refl

  toℕ-subst𝔽 : ∀ {p qq} (e : p ≡ qq) (y : 𝔽 p) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
  toℕ-subst𝔽 refl y = refl

  subst-sym : ∀ {p qq} (eq : p ≡ qq) {X : Tm p} {Y : Tm qq}
            → subst Tm eq X ≡ Y → X ≡ subst Tm (sym eq) Y
  subst-sym refl e = e

------------------------------------------------------------------------
-- splitAt positional inversions + block walk: locate a `Fin (sum B)` in
-- its bind-group block.
------------------------------------------------------------------------

private
  splitAt-inj₁ : ∀ p q (i : 𝔽 (p + q)) {o : 𝔽 p}
               → Fin.splitAt p i ≡ inj₁ o → i ≡ o ↑ˡ q
  splitAt-inj₁ p q i {o} eq = sym (join-splitAt p q i) ■ cong (join p q) eq

  splitAt-inj₂ : ∀ p q (i : 𝔽 (p + q)) {o : 𝔽 q}
               → Fin.splitAt p i ≡ inj₂ o → i ≡ p ↑ʳ o
  splitAt-inj₂ p q i {o} eq = sym (join-splitAt p q i) ■ cong (join p q) eq

block-decomp : (B : BindGroup) (i : 𝔽 (sum B)) →
  Σ[ B₁ ∈ BindGroup ] Σ[ w ∈ ℕ ] Σ[ B₂ ∈ BindGroup ] Σ[ o ∈ 𝔽 w ]
    (B ≡ B₁ ++ w ∷ B₂) × (Fin.toℕ i ≡ sum B₁ + Fin.toℕ o)
block-decomp [] ()
block-decomp (b ∷ B′) i with Fin.splitAt b i in eq
... | inj₁ o = [] , b , B′ , o , refl , (cong Fin.toℕ (splitAt-inj₁ b (sum B′) i eq) ■ toℕ-↑ˡ o (sum B′))
... | inj₂ i′ with block-decomp B′ i′
...   | B₁ , w , B₂ , o , B′≡ , i′≡ =
        (b ∷ B₁) , w , B₂ , o , cong (b ∷_) B′≡ ,
        ( cong Fin.toℕ (splitAt-inj₂ b (sum B′) i eq) ■ toℕ-↑ʳ b i′ ■ cong (b +_) i′≡
        ■ sym (+-assoc b (sum B₁) (Fin.toℕ o)) )

------------------------------------------------------------------------
-- Arbitrary-position junction toℕ of `canonₛ`: EVERY position's middle
-- junction points at the threaded channel `chan`, at flat toℕ syncs + toℕ chan.
------------------------------------------------------------------------

private
  -- express a block width as toℕ-offset + suc rest (offset < width).
  blk-as-handle : ∀ (w : ℕ) (o : 𝔽 w) → Σ[ b₁ ∈ ℕ ] w ≡ Fin.toℕ o + suc b₁
  blk-as-handle w o = w Nat.∸ suc (Fin.toℕ o)
    , sym (+-suc (Fin.toℕ o) (w Nat.∸ suc (Fin.toℕ o)) ■ m+[n∸m]≡n (toℕ<n o))

  -- bind-group-indexed transport of a Fin / Tm / junction, and its naturality.
  substF : ∀ {B B′} (eq : B ≡ B′) → 𝔽 (sum B′) → 𝔽 (sum B)
  substF eq = subst (λ BB → 𝔽 (sum BB)) (sym eq)
  substT : ∀ {B B′ N} (eq : B ≡ B′) → Tm (syncs B′ + N) → Tm (syncs B + N)
  substT {N = N} eq = subst (λ BB → Tm (syncs BB + N)) (sym eq)
  substJ : ∀ {B B′ N} (eq : B ≡ B′) → 𝔽 (syncs B′ + N) → 𝔽 (syncs B + N)
  substJ {N = N} eq = subst (λ BB → 𝔽 (syncs BB + N)) (sym eq)

  toℕ-substF : ∀ {B B′} (eq : B ≡ B′) (x : 𝔽 (sum B′)) → Fin.toℕ (substF eq x) ≡ Fin.toℕ x
  toℕ-substF refl x = refl
  toℕ-substJ : ∀ {B B′ N} (eq : B ≡ B′) (x : 𝔽 (syncs B′ + N)) → Fin.toℕ (substJ {N = N} eq x) ≡ Fin.toℕ x
  toℕ-substJ refl x = refl
  canonₛ-substF : ∀ {B B′} (eq : B ≡ B′) {N} (cc : UChan N) (kk : 𝔽 (sum B′)) →
    canonₛ B cc (substF eq kk) ≡ substT eq (canonₛ B′ cc kk)
  canonₛ-substF refl cc kk = refl
  substT-trip : ∀ {B B′ N} (eq : B ≡ B′) (A : Tm (syncs B′ + N)) (jj : 𝔽 (syncs B′ + N)) (C : Tm (syncs B′ + N)) →
    substT {N = N} eq ((A ⊗ (` jj)) ⊗ C) ≡ (substT eq A ⊗ (` substJ eq jj)) ⊗ substT eq C
  substT-trip refl A jj C = refl

-- The arbitrary-position junction toℕ, proved non-recursively: `block-decomp`
-- locates k in its handle block, and `canonₛ-handleq` reads off the junction.
canonₛ-mid-toℕ : ∀ (B : BindGroup) {N} (e₁ : Tm N) (chan : 𝔽 N) (e₂ : Tm N) (k : 𝔽 (sum B))
  {a c : Tm (syncs B + N)} {j : 𝔽 (syncs B + N)}
  → canonₛ B (e₁ , chan , e₂) k ≡ (a ⊗ (` j)) ⊗ c
  → Fin.toℕ j ≡ syncs B + Fin.toℕ chan
canonₛ-mid-toℕ B {N} e₁ chan e₂ k {a} {c} {j} ceq
  with B₁ , w , B₂ , o , Beq , ktoℕ ← block-decomp B k
  with b₁ , weq ← blk-as-handle w o
  with ah , ch , jh , heq , htoℕ ← canonₛ-handleq B₁ e₁ chan e₂ (Fin.toℕ o) b₁ B₂ =
    tripleℕ (sym ceq ■ big) ■ toℕ-substJ Beq2 jh ■ htoℕ ■ cong (_+ Fin.toℕ chan) (cong syncs (sym Beq2))
  where
    Beq2 : B ≡ B₁ ++ (Fin.toℕ o + suc b₁) ∷ B₂
    Beq2 = Beq ■ cong (λ ww → B₁ ++ ww ∷ B₂) weq
    HP : 𝔽 (sum (B₁ ++ (Fin.toℕ o + suc b₁) ∷ B₂))
    HP = Fin.cast (sym (sum-++ B₁ ((Fin.toℕ o + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((Fin.toℕ o ↑ʳ 0F) ↑ˡ sum B₂))
    toℕ-HP : Fin.toℕ HP ≡ sum B₁ + Fin.toℕ o
    toℕ-HP = toℕ-cast (sym (sum-++ B₁ ((Fin.toℕ o + suc b₁) ∷ B₂))) (sum B₁ ↑ʳ ((Fin.toℕ o ↑ʳ 0F) ↑ˡ sum B₂))
           ■ toℕ-↑ʳ (sum B₁) ((Fin.toℕ o ↑ʳ 0F) ↑ˡ sum B₂)
           ■ cong (sum B₁ +_) (toℕ-↑ˡ (Fin.toℕ o ↑ʳ 0F) (sum B₂) ■ toℕ-↑ʳ (Fin.toℕ o) 0F ■ +-identityʳ (Fin.toℕ o))
    k≡ : k ≡ substF Beq2 HP
    k≡ = toℕ-injective (ktoℕ ■ sym (toℕ-substF Beq2 HP ■ toℕ-HP))
    big : canonₛ B (e₁ , chan , e₂) k
        ≡ (substT Beq2 ah ⊗ (` substJ Beq2 jh)) ⊗ substT Beq2 ch
    big = cong (canonₛ B (e₁ , chan , e₂)) k≡
        ■ canonₛ-substF Beq2 (e₁ , chan , e₂) HP
        ■ cong (substT Beq2) heq
        ■ substT-trip Beq2 ah jh ch

------------------------------------------------------------------------
-- σ-region refutation: a shifted VALUE cannot present a chanTriple whose
-- middle junction sits below the shift.  `val-mid1` peels ONE weaken*.
------------------------------------------------------------------------

private
  val-var1 : ∀ {j} (t : Tm j) → Value t → (r : ℕ) {w : 𝔽 (r + j)}
           → t ⋯ weaken* ⦃ Kᵣ ⦄ r ≡ (` w)
           → Σ[ w₀ ∈ 𝔽 j ] (t ≡ (` w₀)) × (w ≡ weaken* ⦃ Kᵣ ⦄ r w₀)
  val-var1 (` x) V-` r refl = x , refl , refl

  val-pair1 : ∀ {j} (t : Tm j) → Value t → (r : ℕ) {a : Tm (r + j)} {w : 𝔽 (r + j)}
            → t ⋯ weaken* ⦃ Kᵣ ⦄ r ≡ (a ⊗ (` w))
            → Σ[ w₀ ∈ 𝔽 j ] Σ[ a₀ ∈ Tm j ] (t ≡ (a₀ ⊗ (` w₀))) × (w ≡ weaken* ⦃ Kᵣ ⦄ r w₀)
  val-pair1 (t₁ ⊗ t₂) (V-⊗ V₁ V₂) r eq
    with w₀ , t₂≡ , weq ← val-var1 t₂ V₂ r (proj₂ (⊗-inj eq)) =
    w₀ , t₁ , cong (t₁ ⊗_) t₂≡ , weq

  val-mid1 : ∀ {j} (t : Tm j) → Value t → (r : ℕ) {a b : Tm (r + j)} {w : 𝔽 (r + j)}
           → t ⋯ weaken* ⦃ Kᵣ ⦄ r ≡ (a ⊗ (` w)) ⊗ b
           → Σ[ w₀ ∈ 𝔽 j ] Σ[ a₀ ∈ Tm j ] Σ[ b₀ ∈ Tm j ]
               (t ≡ (a₀ ⊗ (` w₀)) ⊗ b₀) × (w ≡ weaken* ⦃ Kᵣ ⦄ r w₀)
  val-mid1 (t₁ ⊗ t₂) (V-⊗ V₁ V₂) r eq
    with w₀ , a₀ , t₁≡ , weq ← val-pair1 t₁ V₁ r (proj₁ (⊗-inj eq)) =
    w₀ , a₀ , t₂ , cong (_⊗ t₂) t₁≡ , weq

  n≢n+suc : ∀ n k → n ≡ n + suc k → ⊥
  n≢n+suc zero    k ()
  n≢n+suc (suc n) k eq = n≢n+suc n k (Nat.suc-injective eq)


------------------------------------------------------------------------
-- The linchpin: recover the bind-group decomposition + handle position of a
-- block-1 (channel-0) redex from its flattened image `leafσ σ BL BR`.
------------------------------------------------------------------------

handleId-block1 : ∀ {m n} (BL BR : BindGroup) (σ : m →ₛ n) (Vσ : VSub σ)
  (x : 𝔽 (sum BL + sum BR + m))
  {e₁ e₂ : Tm (syncs BR + (syncs BL + (2 + n)))} {w : 𝔽 (syncs BR + (syncs BL + (2 + n)))}
  → Fin.toℕ w ≡ syncs BL + syncs BR
  → ((e₁ ⊗ (` w)) ⊗ e₂) ≡ leafσ σ BL BR x
  → Σ[ B₁ ∈ BindGroup ] Σ[ B₂ ∈ BindGroup ] Σ[ q ∈ ℕ ] Σ[ b₁ ∈ ℕ ]
      (BL ≡ B₁ ++ (q + suc b₁) ∷ B₂)
      × (Fin.toℕ x ≡ sum B₁ + q)
handleId-block1 {m} {n} BL BR σ Vσ x {e₁} {e₂} {w} wtoℕ argeq
  with Fin.splitAt (sum BL + sum BR) x in seqo
... | inj₂ u = ⊥-elim (n≢n+suc (syncs BR + syncs BL) (suc (Fin.toℕ w₂)) contraeq)
  where
    T₁ = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2
    T₀ = T₁ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs BL)
    V₁ : Value T₁
    V₁ = value-⋯ (Vσ u) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)
    V₀ : Value T₀
    V₀ = value-⋯ V₁ (weaken* ⦃ Kᵣ ⦄ (syncs BL)) (λ _ → V-`)
    tailimg : T₀ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs BR) ≡ (e₁ ⊗ (` w)) ⊗ e₂
    tailimg = sym argeq
    peel0 = val-mid1 T₀ V₀ (syncs BR) tailimg
    w₀  = proj₁ peel0
    T₀≡ = proj₁ (proj₂ (proj₂ (proj₂ peel0)))
    weq0 : w ≡ weaken* ⦃ Kᵣ ⦄ (syncs BR) w₀
    weq0 = proj₂ (proj₂ (proj₂ (proj₂ peel0)))
    peel1 = val-mid1 T₁ V₁ (syncs BL) T₀≡
    w₁  = proj₁ peel1
    T₁≡ = proj₁ (proj₂ (proj₂ (proj₂ peel1)))
    weq1 : w₀ ≡ weaken* ⦃ Kᵣ ⦄ (syncs BL) w₁
    weq1 = proj₂ (proj₂ (proj₂ (proj₂ peel1)))
    peel2 = val-mid1 (σ u) (Vσ u) 2 T₁≡
    w₂  = proj₁ peel2
    weq2 : w₁ ≡ weaken* ⦃ Kᵣ ⦄ 2 w₂
    weq2 = proj₂ (proj₂ (proj₂ (proj₂ peel2)))
    wval : Fin.toℕ w ≡ syncs BR + (syncs BL + suc (suc (Fin.toℕ w₂)))
    wval = cong Fin.toℕ weq0 ■ toℕ-weaken*ᵣ (syncs BR) w₀
         ■ cong (syncs BR +_)
             ( cong Fin.toℕ weq1 ■ toℕ-weaken*ᵣ (syncs BL) w₁
             ■ cong (syncs BL +_) (cong Fin.toℕ weq2 ■ toℕ-weaken*ᵣ 2 w₂) )
    contraeq : syncs BR + syncs BL ≡ (syncs BR + syncs BL) + suc (suc (Fin.toℕ w₂))
    contraeq = sym (+-comm (syncs BL) (syncs BR)) ■ sym wtoℕ ■ wval
             ■ sym (+-assoc (syncs BR) (syncs BL) (suc (suc (Fin.toℕ w₂))))
... | inj₁ z
  with Fin.splitAt (sum BL) z in seqi
...   | inj₂ kk = ⊥-elim (n≢n+suc (syncs BR + syncs BL) 0 contraeq)
  where
    bimg : (e₁ ⊗ (` w)) ⊗ e₂ ≡ canonₛ BR (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs BL) 1F , K `unit) kk
    bimg = argeq
    wtoℕ2 : Fin.toℕ w ≡ syncs BR + Fin.toℕ (weaken* ⦃ Kᵣ ⦄ (syncs BL) 1F)
    wtoℕ2 = canonₛ-mid-toℕ BR (K `unit) (weaken* ⦃ Kᵣ ⦄ (syncs BL) 1F) (K `unit) kk (sym bimg)
    contraeq : syncs BR + syncs BL ≡ (syncs BR + syncs BL) + suc 0
    contraeq = sym (+-comm (syncs BL) (syncs BR)) ■ sym wtoℕ ■ wtoℕ2
             ■ cong (syncs BR +_) (toℕ-weaken*ᵣ (syncs BL) 1F)
             ■ sym (+-assoc (syncs BR) (syncs BL) 1)
...   | inj₁ j
  with B₁ , w′ , B₂ , o , BL≡ , jtoℕ ← block-decomp BL j
  with b₁ , weq ← blk-as-handle w′ o =
  B₁ , B₂ , Fin.toℕ o , b₁ , (BL≡ ■ cong (λ ww → B₁ ++ ww ∷ B₂) weq) , xtoℕ
  where
    xtoℕ : Fin.toℕ x ≡ sum B₁ + Fin.toℕ o
    xtoℕ = cong Fin.toℕ (splitAt-inj₁ (sum BL + sum BR) m x seqo)
         ■ toℕ-↑ˡ z m
         ■ cong Fin.toℕ (splitAt-inj₁ (sum BL) (sum BR) z seqi)
         ■ toℕ-↑ˡ j (sum BR)
         ■ jtoℕ

------------------------------------------------------------------------
-- Block-2 (channel-1) dual: recv / branch / close-⁇.  The redex borrows the
-- SECOND endpoint, presented with middle junction toℕ = suc (sBL + sBR); the
-- handle lives in BR, so we decompose BR instead.
------------------------------------------------------------------------

handleId-block2 : ∀ {m n} (BL BR : BindGroup) (σ : m →ₛ n) (Vσ : VSub σ)
  (x : 𝔽 (sum BL + sum BR + m))
  {e₁ e₂ : Tm (syncs BR + (syncs BL + (2 + n)))} {w : 𝔽 (syncs BR + (syncs BL + (2 + n)))}
  → Fin.toℕ w ≡ suc (syncs BL + syncs BR)
  → ((e₁ ⊗ (` w)) ⊗ e₂) ≡ leafσ σ BL BR x
  → Σ[ B₁ ∈ BindGroup ] Σ[ B₂ ∈ BindGroup ] Σ[ q ∈ ℕ ] Σ[ b₁ ∈ ℕ ]
      (BR ≡ B₁ ++ (q + suc b₁) ∷ B₂)
      × (Fin.toℕ x ≡ sum BL + (sum B₁ + q))
handleId-block2 {m} {n} BL BR σ Vσ x {e₁} {e₂} {w} wtoℕ argeq
  with Fin.splitAt (sum BL + sum BR) x in seqo
... | inj₂ u = ⊥-elim (n≢n+suc (syncs BR + syncs BL) (Fin.toℕ w₂) contraeq)
  where
    T₁ = σ u ⋯ weaken* ⦃ Kᵣ ⦄ 2
    T₀ = T₁ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs BL)
    V₁ : Value T₁
    V₁ = value-⋯ (Vσ u) (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`)
    V₀ : Value T₀
    V₀ = value-⋯ V₁ (weaken* ⦃ Kᵣ ⦄ (syncs BL)) (λ _ → V-`)
    tailimg : T₀ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs BR) ≡ (e₁ ⊗ (` w)) ⊗ e₂
    tailimg = sym argeq
    peel0 = val-mid1 T₀ V₀ (syncs BR) tailimg
    w₀  = proj₁ peel0
    T₀≡ = proj₁ (proj₂ (proj₂ (proj₂ peel0)))
    weq0 : w ≡ weaken* ⦃ Kᵣ ⦄ (syncs BR) w₀
    weq0 = proj₂ (proj₂ (proj₂ (proj₂ peel0)))
    peel1 = val-mid1 T₁ V₁ (syncs BL) T₀≡
    w₁  = proj₁ peel1
    T₁≡ = proj₁ (proj₂ (proj₂ (proj₂ peel1)))
    weq1 : w₀ ≡ weaken* ⦃ Kᵣ ⦄ (syncs BL) w₁
    weq1 = proj₂ (proj₂ (proj₂ (proj₂ peel1)))
    peel2 = val-mid1 (σ u) (Vσ u) 2 T₁≡
    w₂  = proj₁ peel2
    weq2 : w₁ ≡ weaken* ⦃ Kᵣ ⦄ 2 w₂
    weq2 = proj₂ (proj₂ (proj₂ (proj₂ peel2)))
    wval : Fin.toℕ w ≡ syncs BR + (syncs BL + suc (suc (Fin.toℕ w₂)))
    wval = cong Fin.toℕ weq0 ■ toℕ-weaken*ᵣ (syncs BR) w₀
         ■ cong (syncs BR +_)
             ( cong Fin.toℕ weq1 ■ toℕ-weaken*ᵣ (syncs BL) w₁
             ■ cong (syncs BL +_) (cong Fin.toℕ weq2 ■ toℕ-weaken*ᵣ 2 w₂) )
    -- suc (sBL+sBR) ≡ sBR+(sBL+suc(suc w₂)); strip a suc to get n ≡ n + suc w₂.
    contraeq : syncs BR + syncs BL ≡ (syncs BR + syncs BL) + suc (Fin.toℕ w₂)
    contraeq = Nat.suc-injective
      ( cong suc (sym (+-comm (syncs BL) (syncs BR))) ■ sym wtoℕ ■ wval
      ■ sym (+-assoc (syncs BR) (syncs BL) (suc (suc (Fin.toℕ w₂))))
      ■ +-suc (syncs BR + syncs BL) (suc (Fin.toℕ w₂)) )
... | inj₁ z
  with Fin.splitAt (sum BL) z in seqi
...   | inj₁ j = ⊥-elim (n≢n+suc (syncs BR + syncs BL) 0 contraeq)
  where
    Vcbl : Value (canonₛ BL (K `unit , 0F , K `unit) j)
    Vcbl = VSub-canonₛ BL (K `unit , 0F , K `unit) (V-K , V-K) j
    peel = val-mid1 (canonₛ BL (K `unit , 0F , K `unit) j) Vcbl (syncs BR) (sym argeq)
    w₀   = proj₁ peel
    cbl≡ = proj₁ (proj₂ (proj₂ (proj₂ peel)))
    weq0 : w ≡ weaken* ⦃ Kᵣ ⦄ (syncs BR) w₀
    weq0 = proj₂ (proj₂ (proj₂ (proj₂ peel)))
    midtoℕ : Fin.toℕ w₀ ≡ syncs BL + 0
    midtoℕ = canonₛ-mid-toℕ BL (K `unit) 0F (K `unit) j cbl≡
    -- toℕ w = sBR + sBL, but hyp = suc (sBL+sBR): the false n ≡ n + suc 0.
    derived : Fin.toℕ w ≡ syncs BR + syncs BL
    derived = cong Fin.toℕ weq0 ■ toℕ-weaken*ᵣ (syncs BR) w₀
            ■ cong (syncs BR +_) (midtoℕ ■ +-identityʳ (syncs BL))
    contraeq : syncs BR + syncs BL ≡ (syncs BR + syncs BL) + suc 0
    contraeq = sym derived ■ wtoℕ ■ cong suc (+-comm (syncs BL) (syncs BR))
             ■ sym (+-suc (syncs BR + syncs BL) 0 ■ cong suc (+-identityʳ (syncs BR + syncs BL)))
...   | inj₂ kk
  with B₁ , w′ , B₂ , o , BR≡ , kktoℕ ← block-decomp BR kk
  with b₁ , weq ← blk-as-handle w′ o =
  B₁ , B₂ , Fin.toℕ o , b₁ , (BR≡ ■ cong (λ ww → B₁ ++ ww ∷ B₂) weq) , xtoℕ
  where
    xtoℕ : Fin.toℕ x ≡ sum BL + (sum B₁ + Fin.toℕ o)
    xtoℕ = cong Fin.toℕ (splitAt-inj₁ (sum BL + sum BR) m x seqo)
         ■ toℕ-↑ˡ z m
         ■ cong Fin.toℕ (splitAt-inj₂ (sum BL) (sum BR) z seqi)
         ■ toℕ-↑ʳ (sum BL) kk
         ■ cong (sum BL +_) kktoℕ
