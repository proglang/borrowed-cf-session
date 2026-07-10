module BorrowedCF.Simulation3.Support.Theorems.SplitsH3 where

open import BorrowedCF.Simulation3.Support.Base
import BorrowedCF.Processes.Typed             as T
import BorrowedCF.Processes.Untyped           as U
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Data.Sum using (_⊎_)
open import BorrowedCF.Context using (Ctx; Struct)
open import BorrowedCF.Simulation3.Support.SplitConfine using (lsplit-confine; rsplit-confine)
open import BorrowedCF.Simulation3.Support.Frames using (frame-plug*; frame*-⋯; frame-plug₁; ++ₛ-VSub)
open import BorrowedCF.Simulation3.Support.TranslationProperties
  using (UB-nat; mapᶜ; varΘ; U-cong; U-⋯ₚ; U-σ⋯; ++ₛ-⋯; liftCast; subst₂→; chanTriple-mapᶜ
        ; VChan; chanTriple-V; Value-subst; Ub-nat; Ub-V)
  renaming ( subst-⋯ₚ-dom to TP-subst-⋯ₚ-dom
           ; subst₂-cancel to subst₂-cancel-local
           ; subst-⋯-cod to subst-⋯-cod-local
           ; subst-subst-sym′ to subst-subst-sym-local
           ; subst-⋯ to subst-⋯-dom-local )
open import BorrowedCF.Simulation3.Support.BlockPerm
  using ( assocSwap-01; R-base-b0; assocSwap-0a; toℕ-R3; toℕ-R3₂; toℕ-R4
        ; toℕ-weaken*ᵣ; toℕ-swapᵣ-mid; toℕ-reduce≥; toℕ-assoc-mid
        ; toℕ-assoc-lt; toℕ-assoc-ge
        ; toℕ-↑*-ge; toℕ-↑*-lt; commuteS; wkSwap-cancel; assocSwap-invol )
open T using (BindGroup)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Data.List.Properties using (++-assoc)
open import BorrowedCF.Simulation3.Support.RsplitTransport
  using (⋯-subst₂; ⋯ₚ-subst₂; subst-Tm-uip; toℕ-subst-cod; toℕ-subst₂ᵣ)
open import BorrowedCF.Simulation3.Support.FrameRename
  using (⋯ᶠ*-cong; ⋯ᶠ*-fuse; F-σ⋯)

open import BorrowedCF.Simulation3.Support.Theorems.SplitsH2 public

drwk-lo : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          Fin.toℕ j Nat.< sum B₁ → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ Fin.toℕ j
drwk-lo []        b₁ B₂ j ()
drwk-lo (a ∷ B₁') b₁ B₂ j lt with drwk-lo B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = Fin.toℕ-↑ˡ p _ ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr) ■ sym jℕ
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : Fin.toℕ r Nat.< sum B₁'
        boundr = Nat.+-cancelˡ-< a (Fin.toℕ r) (sum B₁') (subst (Nat._< a + sum B₁') jℕ lt)

drwk-hi : ∀ (B₁ : T.BindGroup) (b₁ : ℕ) (B₂ : T.BindGroup) (j : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
          sum B₁ Nat.≤ Fin.toℕ j → Fin.toℕ (drwk B₁ b₁ B₂ j) ≡ suc (Fin.toℕ j)
drwk-hi []        b₁ B₂ j h = Fin.toℕ-↑ʳ 1 j
drwk-hi (a ∷ B₁') b₁ B₂ j h with drwk-hi B₁' b₁ B₂
... | recf with splitAt a j in seq
... | inj₁ p = ⊥-elim (Nat.<-irrefl refl (Nat.<-≤-trans (Nat.<-≤-trans (subst (Nat._< a) (sym jℕ) (Fin.toℕ<n p)) (Nat.m≤m+n a (sum B₁'))) h))
  where jℕ : Fin.toℕ j ≡ Fin.toℕ p
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ˡ p (sum (B₁' ++ suc b₁ ∷ B₂))
... | inj₂ r = Fin.toℕ-↑ʳ a (drwk B₁' b₁ B₂ r) ■ cong (a +_) (recf r boundr)
             ■ Nat.+-suc a (Fin.toℕ r) ■ cong suc (sym jℕ)
  where jℕ : Fin.toℕ j ≡ a + Fin.toℕ r
        jℕ = cong Fin.toℕ (sym (Fin.join-splitAt a (sum (B₁' ++ suc b₁ ∷ B₂)) j)
                          ■ cong (Fin.join a (sum (B₁' ++ suc b₁ ∷ B₂))) seq)
           ■ Fin.toℕ-↑ʳ a r
        boundr : sum B₁' Nat.≤ Fin.toℕ r
        boundr = Nat.+-cancelˡ-≤ a (sum B₁') (Fin.toℕ r) (subst (a + sum B₁' Nat.≤_) jℕ h)

-- chainRwk: telescope a slot-equality (at scope suc N, shift sT) through the +-suc
-- scope-shuffle canonₛ applies when peeling a B₁ chain (scope N).  Identical shape
-- to chainLwk (reused verbatim); kept separate only for readability of the rwk side.
chainRwk : ∀ {N} {sT sT′ : ℕ} (sl : sT ≡ sT′)
           {DA DB : Set} (g : DA → Tm (sT + suc N)) (g′ : DB → Tm (sT′ + suc N))
           (i : DA) (di : DB) →
           subst Tm (cong (_+ suc N) sl) (g i) ≡ g′ di →
           subst Tm (cong (_+ N) (cong suc sl)) (subst Tm (+-suc sT N) (g i))
           ≡ subst Tm (+-suc sT′ N) (g′ di)
chainRwk = chainLwk

-- ===== canonₛ-rwk =====
-- canonₛ on the rwk-grown bind group (with a FRESH width-1 block inserted before the
-- handle chain), off the consumed handle, equals the transported ungrown canonₛ.
-- The base case (B₁ = []) is the substantive re-threading obligation the roadmap flags:
-- the inserted `1`-block becomes the new head, re-threading (` 0F, suc x, wk e₂) through
-- the whole tail — but away from slot 0F that threading is INVISIBLE (e₁ only read at 0F).
-- Ub[ b ] reads its first slot only at position 0F.  Off 0F it is e₁-independent.
Ub-e₁ : ∀ (b : ℕ) {N} (a a′ : Tm N) (c : 𝔽 N) (e₂ : Tm N) (j : 𝔽 (suc b)) → j ≢ 0F →
        Ub[ suc b ] (a , c , e₂) j ≡ Ub[ suc b ] (a′ , c , e₂) j
Ub-e₁ zero    a a′ c e₂ zero    j≢ = ⊥-elim (j≢ refl)
Ub-e₁ (suc b) a a′ c e₂ zero    j≢ = ⊥-elim (j≢ refl)
Ub-e₁ (suc b) a a′ c e₂ (suc j) j≢ = refl

-- e₁ (the head data-block's first slot) is only read at position 0F; off 0F the
-- canonical substitution is independent of it.  Induction mirrors canonₛ.
canonₛ-e₁ : ∀ (b₁ : ℕ) (B₂ : BindGroup) {N} (a a′ : Tm N) (x : 𝔽 N) (e₂ : Tm N)
            (i : 𝔽 (sum (suc b₁ ∷ B₂))) → i ≢ 0F →
            canonₛ (suc b₁ ∷ B₂) (a , x , e₂) i ≡ canonₛ (suc b₁ ∷ B₂) (a′ , x , e₂) i
canonₛ-e₁ b₁ [] {N} a a′ x e₂ i i≢ =
  Ub-e₁ (b₁ + 0) a a′ x e₂ i i≢
canonₛ-e₁ b₁ (c ∷ B₂′) {N} a a′ x e₂ i i≢
  with Fin.splitAt (suc b₁) i in seq
... | inj₁ p rewrite seq =
      cong (subst Tm (+-suc (syncs (c ∷ B₂′)) N))
        (cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c ∷ B₂′)))
          (Ub-e₁ b₁ (wk a) (wk a′) (suc x) (` 0F) p p≢))
  where
    p≢ : p ≢ 0F
    p≢ p≡ = i≢ ( sym (Fin.join-splitAt (suc b₁) (sum (c ∷ B₂′)) i)
               ■ cong (Fin.join (suc b₁) (sum (c ∷ B₂′))) seq
               ■ cong (_↑ˡ sum (c ∷ B₂′)) p≡ )
... | inj₂ r rewrite seq = refl

-- canonₛ-rwk, base case (B₁ = []): the fresh `1`-block sync (front of the tail's
-- syncs) is exactly the slot canonₛ-nat's (weakenᵣ ↑* syncs) inserts; off 0F, e₁
-- is invisible (canonₛ-e₁).  This is the substantive re-threading obligation.
canonₛ-rwk0 : ∀ {N} (cc : UChan N) (b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (suc b₁ ∷ B₂))) →
             i ≢ 0F →
             canonₛ (1 ∷ suc b₁ ∷ B₂) cc (weakenᵣ i)
             ≡ subst Tm (+-suc (syncs (suc b₁ ∷ B₂)) N)
                 (canonₛ (suc b₁ ∷ B₂) cc i ⋯ (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)))
canonₛ-rwk0 {N} (e₁ , x , e₂) b₁ B₂ i i≢ =
  cong (subst Tm (+-suc sD N))
    ( canonₛ-e₁ b₁ B₂ (` 0F) (wk e₁) (suc x) (wk e₂) i i≢
    ■ sym (canonₛ-nat (suc b₁ ∷ B₂) (e₁ , x , e₂) weakenᵣ i) )
  where sD = syncs (suc b₁ ∷ B₂)

-- syncs of a cons with a nonempty tail bumps by one (definitionally).
syncs-cons : ∀ (a : ℕ) (B₁' : BindGroup) (c : ℕ) (D : BindGroup) →
             syncs (a ∷ (B₁' ++ c ∷ D)) ≡ suc (syncs (B₁' ++ c ∷ D))
syncs-cons a []          c D = refl
syncs-cons a (b ∷ B₁'') c D = refl

-- sins: the sync-level insertion renaming, sending the ungrown group's syncs to
-- the rwk-grown group's syncs (which has ONE more φ, from the inserted 1-block).
-- Recursion on B₁ mirrors drwk: base inserts (weakenᵣ ↑* sD) retyped by +-suc;
-- the head block conjugates by the two +-suc scope shuffles.
sins : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N} →
       syncs (B₁ ++ suc b₁ ∷ B₂) + N →ᵣ syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N
sins [] b₁ B₂ {N} =
  subst (λ z → syncs (suc b₁ ∷ B₂) + N →ᵣ z) (+-suc (syncs (suc b₁ ∷ B₂)) N)
    (weakenᵣ ↑* syncs (suc b₁ ∷ B₂))
sins (a ∷ B₁') b₁ B₂ {N} =
  subst₂ _→ᵣ_
    (+-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂)))
    (+-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂))))
    (sins B₁' b₁ B₂ {suc N})

-- sins inserts a fresh sync slot at flat position syncs (suc b₁ ∷ B₂) (the
-- handle-chain's sync count, i.e. the leaf end of the handle block), regardless
-- of the B₁ prefix: at/above that position toℕ bumps by one.  Induction on B₁.
sins-toℕ-hi : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
              syncs (suc b₁ ∷ B₂) Nat.≤ Fin.toℕ j →
              Fin.toℕ (sins B₁ b₁ B₂ {N} j) ≡ suc (Fin.toℕ j)
sins-toℕ-hi [] b₁ B₂ {N} j h =
    toℕ-subst-cod (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) j
  ■ toℕ-↑*-ge weakenᵣ (syncs (suc b₁ ∷ B₂)) j h
  ■ cong (syncs (suc b₁ ∷ B₂) +_) (cong suc (toℕ-reduce≥ j h))
  ■ Nat.+-suc (syncs (suc b₁ ∷ B₂)) (Fin.toℕ j Nat.∸ syncs (suc b₁ ∷ B₂))
  ■ cong suc (Nat.m+[n∸m]≡n h)
sins-toℕ-hi (a ∷ B₁') b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sins B₁' b₁ B₂ {suc N}) j
  ■ sins-toℕ-hi B₁' b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-subst𝔽 (sym pL) j)) h)
  ■ cong suc (toℕ-subst𝔽 (sym pL) j)
  where
    pL = +-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂)))
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl

-- below the insertion threshold syncs (suc b₁ ∷ B₂), sins preserves toℕ.
sins-toℕ-lo : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N}
              (j : 𝔽 (syncs (B₁ ++ suc b₁ ∷ B₂) + N)) →
              Fin.toℕ j Nat.< syncs (suc b₁ ∷ B₂) →
              Fin.toℕ (sins B₁ b₁ B₂ {N} j) ≡ Fin.toℕ j
sins-toℕ-lo [] b₁ B₂ {N} j h =
    toℕ-subst-cod (+-suc (syncs (suc b₁ ∷ B₂)) N) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)) j
  ■ toℕ-↑*-lt weakenᵣ (syncs (suc b₁ ∷ B₂)) j h
sins-toℕ-lo (a ∷ B₁') b₁ B₂ {N} j h =
    toℕ-subst₂ᵣ pL pR (sins B₁' b₁ B₂ {suc N}) j
  ■ sins-toℕ-lo B₁' b₁ B₂ {suc N} (subst 𝔽 (sym pL) j)
      (subst (Nat._< syncs (suc b₁ ∷ B₂)) (sym (toℕ-subst𝔽 (sym pL) j)) h)
  ■ toℕ-subst𝔽 (sym pL) j
  where
    pL = +-suc (syncs (B₁' ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' (suc b₁) B₂))
    pR = +-suc (syncs (B₁' ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a B₁' 1 (suc b₁ ∷ B₂)))
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl

-- the handle-chain sync count bounds the whole grown group's sync count.
sD≤ : ∀ (B₁ : BindGroup) {b₁ B₂} → syncs (suc b₁ ∷ B₂) Nat.≤ syncs (B₁ ++ suc b₁ ∷ B₂)
sD≤ []                {b₁} {B₂} = Nat.≤-refl
sD≤ (a ∷ B₁') {b₁} {B₂} =
  subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (syncs-cons a B₁' (suc b₁) B₂))
    (Nat.≤-trans (sD≤ B₁') (Nat.n≤1+n _))

-- sins turns a weaken by the ungrown handle-group sync count into a weaken by
-- the grown one (both above the insertion threshold, so shifted by one).
sins-wk : ∀ (B₁ : BindGroup) (b₁ : ℕ) (B₂ : BindGroup) {N} (v : 𝔽 N) →
          sins B₁ b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
          ≡ weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v
sins-wk B₁ b₁ B₂ {N} v = Fin.toℕ-injective
  ( sins-toℕ-hi B₁ b₁ B₂ {N} (weaken* ⦃ Kᵣ ⦄ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
      (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ (syncs (B₁ ++ suc b₁ ∷ B₂)) v))
        (Nat.≤-trans (sD≤ B₁) (Nat.m≤m+n (syncs (B₁ ++ suc b₁ ∷ B₂)) (Fin.toℕ v))))
  ■ cong suc (toℕ-weaken*ᵣ (syncs (B₁ ++ suc b₁ ∷ B₂)) v)
  ■ sym (toℕ-weaken*ᵣ (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂)) v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwk B₁)) )

-- canonₛ-rwk (general): canonₛ on the rwk-grown group, off the consumed handle,
-- equals the ungrown canonₛ post-composed with the sync-insertion renaming sins.
canonₛ-rwk : ∀ (B₁ : BindGroup) {N} (cc : UChan N) (b₁ : ℕ) (B₂ : BindGroup)
             (i : 𝔽 (sum (B₁ ++ suc b₁ ∷ B₂))) →
             i ≢ Fin.cast (sym (sum-++ B₁ (suc b₁ ∷ B₂))) (sum B₁ ↑ʳ 0F) →
             canonₛ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) cc (drwk B₁ b₁ B₂ i)
             ≡ canonₛ (B₁ ++ suc b₁ ∷ B₂) cc i ⋯ sins B₁ b₁ B₂ {N}
canonₛ-rwk [] {N} cc b₁ B₂ i i≢ =
    canonₛ-rwk0 cc b₁ B₂ i (λ i≡ → i≢ (i≡ ■ sym cast≡))
  ■ sym (subst-⋯-cod-local (+-suc (syncs (suc b₁ ∷ B₂)) N)
           (canonₛ (suc b₁ ∷ B₂) cc i) (weakenᵣ ↑* syncs (suc b₁ ∷ B₂)))
  where
    cast≡ : Fin.cast (sym (sum-++ [] (suc b₁ ∷ B₂))) (sum [] ↑ʳ 0F) ≡ 0F
    cast≡ = refl
canonₛ-rwk (a ∷ []) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk [] {suc N} (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ([] ++ 1 ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    SS  = cong suc (+-suc sD N)
    ρ0 = sins [] b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc (syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ (suc sD) v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hi [] b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (sD Nat.≤_) (sym (toℕ-weaken*ᵣ sD v)) (Nat.m≤m+n sD (Fin.toℕ v)))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ (suc sD) v) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ (suc sD)
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ([] ++ 1 ∷ suc b₁ ∷ B₂)) (weakenᵣ r) =
      cong (subst Tm SS) (rec r r≢0)
    ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    SS  = cong suc (+-suc sD N)
    ρ0 = sins [] b₁ B₂ {suc N}
    pL = +-suc (syncs ([] ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc (syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    leafM = canonₛ (suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢0 : r ≢ 0F
    r≢0 r≡ = i≢ ( sym (Fin.join-splitAt a (sum ([] ++ suc b₁ ∷ B₂)) i)
                ■ cong (Fin.join a (sum ([] ++ suc b₁ ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split a [] b₁ B₂) )
canonₛ-rwk (a ∷ d ∷ B₁″) {N} (e₁ , x , e₂) b₁ B₂ i i≢
  with canonₛ-rwk (d ∷ B₁″) {suc N} (` 0F , suc x , wk e₂) b₁ B₂
... | rec with Fin.splitAt a i in seq
... | inj₁ p rewrite Fin.splitAt-↑ˡ a p (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) =
      cong (subst Tm SS) (sym headCore)
    ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL headM)
          ■ ⋯-subst₂ pL pR headM ρ0
          ■ subst-Tm-uip pR SS (headM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sins (d ∷ B₁″) b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    hp = Ub[ a ] (wk e₁ , suc x , ` 0F) p
    headM = hp ⋯ weaken* ⦃ Kᵣ ⦄ sD
    ptwise : ∀ v → (weaken* ⦃ Kᵣ ⦄ sD ·ₖ ρ0) v ≡ weaken* ⦃ Kᵣ ⦄ sDʳ v
    ptwise v = Fin.toℕ-injective
      ( sins-toℕ-hi (d ∷ B₁″) b₁ B₂ {suc N} (weaken* ⦃ Kᵣ ⦄ sD v)
          (subst (syncs (suc b₁ ∷ B₂) Nat.≤_) (sym (toℕ-weaken*ᵣ sD v))
            (Nat.≤-trans (sD≤ (d ∷ B₁″)) (Nat.m≤m+n sD (Fin.toℕ v))))
      ■ cong suc (toℕ-weaken*ᵣ sD v)
      ■ sym (toℕ-weaken*ᵣ sDʳ v ■ cong (Nat._+ Fin.toℕ v) (syncs-rwk (d ∷ B₁″))) )
    headCore : headM ⋯ ρ0 ≡ hp ⋯ weaken* ⦃ Kᵣ ⦄ sDʳ
    headCore = fusion hp (weaken* ⦃ Kᵣ ⦄ sD) ρ0 ■ ⋯-cong hp ptwise
... | inj₂ r rewrite Fin.splitAt-↑ʳ a (sum ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) (drwk (d ∷ B₁″) b₁ B₂ r) =
      cong (subst Tm SS) (rec r r≢h)
    ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sD N) pL leafM)
          ■ ⋯-subst₂ pL pR leafM ρ0
          ■ subst-Tm-uip pR SS (leafM ⋯ ρ0) )
  where
    sD  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sDʳ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    SS  = +-suc sDʳ N
    ρ0  = sins (d ∷ B₁″) b₁ B₂ {suc N}
    pL = +-suc (syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc (syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)) N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    leafM = canonₛ ((d ∷ B₁″) ++ suc b₁ ∷ B₂) (` 0F , suc x , wk e₂) r
    r≢h : r ≢ Fin.cast (sym (sum-++ (d ∷ B₁″) (suc b₁ ∷ B₂))) (sum (d ∷ B₁″) ↑ʳ 0F)
    r≢h r≡ = i≢ ( sym (Fin.join-splitAt a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂)) i)
                ■ cong (Fin.join a (sum ((d ∷ B₁″) ++ suc b₁ ∷ B₂))) seq
                ■ cong (a ↑ʳ_) r≡
                ■ sym (pos-split a (d ∷ B₁″) b₁ B₂) )

-- The rsplit-grown bind group's Bφ-prefix carries one extra φ-drop binder (the
-- inserted `1`-block).  That binder slides down past the remaining blocks to the
-- front of the leaf body.  syncs C₁ᴿ = suc (syncs C₁); subst on a re-types Z.
ss-Uf : ∀ {h : ℕ → ℕ} {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) {t : U.Proc (h x)} →
        subst (λ j → U.Proc (h j)) q (subst (λ j → U.Proc (h j)) p t)
        ≡ subst (λ j → U.Proc (h j)) (p ■ q) t
ss-Uf refl refl = refl

-- syncs of an append with a nonempty tail splits additively (one junction per
-- B₁-block).  Fact (A) for the sw-cast index reshaping.
syncs-split : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} →
              syncs (B₁ ++ suc b₁ ∷ B₂) ≡ L.length B₁ + syncs (suc b₁ ∷ B₂)
syncs-split []            {b₁} {B₂} = refl
syncs-split (a ∷ [])      {b₁} {B₂} = cong suc (syncs-split [] {b₁} {B₂})
syncs-split (a ∷ d ∷ B₁″) {b₁} {B₂} = cong suc (syncs-split (d ∷ B₁″) {b₁} {B₂})

toℕ-subst-domM : ∀ {A A′ Bb} (e : A ≡ A′) (ρ : A →ᵣ Bb) (y : 𝔽 A′) →
                 Fin.toℕ (subst (λ z → z →ᵣ Bb) e ρ y) ≡ Fin.toℕ (ρ (subst 𝔽 (sym e) y))
toℕ-subst-domM refl ρ y = refl

-- a weakened term (image of ⋯ weakenᵣ, so avoiding 0F) commutes weaken*(suc k)
-- with the split weaken* k then weakenᵣ↑*(suc k) (across the +-suc scope bridge).
weaken-suc-shift : ∀ {N} (u : Tm N) (k : ℕ) →
  u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (suc k)
  ≡ subst Tm (+-suc k N) (u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ k) ⋯ (weakenᵣ ↑* (suc k))
weaken-suc-shift {N} u k =
    fusion u weakenᵣ (weaken* ⦃ Kᵣ ⦄ (suc k))
  ■ ⋯-cong u ptwise
  ■ sym (fusion u weakenᵣ (weaken* ⦃ Kᵣ ⦄ k ·ₖ ρ*))
  ■ sym (fusion (u ⋯ weakenᵣ) (weaken* ⦃ Kᵣ ⦄ k) ρ*)
  ■ sym (subst-⋯-dom-local (+-suc k N) (u ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ k) (weakenᵣ ↑* (suc k)))
  where
    ρ* : (k + suc N) →ᵣ (suc k + suc N)
    ρ* = subst (λ z → z →ᵣ (suc k + suc N)) (sym (+-suc k N)) (weakenᵣ ↑* (suc k))
    ptwise : (weakenᵣ ·ₖ weaken* ⦃ Kᵣ ⦄ (suc k)) ≗ (weakenᵣ ·ₖ (weaken* ⦃ Kᵣ ⦄ k ·ₖ ρ*))
    ptwise v = Fin.toℕ-injective
      ( toℕ-weaken*ᵣ (suc k) (weakenᵣ v)
      ■ sym ( toℕ-subst-domM (sym (+-suc k N)) (weakenᵣ ↑* (suc k)) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
            ■ toℕ-↑*-ge weakenᵣ (suc k) w′ q
            ■ cong (suc k +_) (cong suc redw) ) )
      where
        toℕ-subst𝔽M : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
        toℕ-subst𝔽M refl y = refl
        w′ : 𝔽 (suc k + N)
        w′ = subst 𝔽 (sym (sym (+-suc k N))) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
        w′N : Fin.toℕ w′ ≡ suc (k + Fin.toℕ v)
        w′N = toℕ-subst𝔽M (sym (sym (+-suc k N))) (weaken* ⦃ Kᵣ ⦄ k (weakenᵣ v))
            ■ toℕ-weaken*ᵣ k (weakenᵣ v) ■ Nat.+-suc k (Fin.toℕ v)
        q : suc k Nat.≤ Fin.toℕ w′
        q = subst (suc k Nat.≤_) (sym w′N) (Nat.s≤s (Nat.m≤m+n k (Fin.toℕ v)))
        redw : Fin.toℕ (Fin.reduce≥ w′ q) ≡ Fin.toℕ v
        redw = toℕ-reduce≥ w′ q ■ cong (Nat._∸ suc k) w′N ■ Nat.m+n∸m≡n k (Fin.toℕ v)

-- rsplit grown-handle L-slot: the fresh 1-channel's L-slot = ungrown handle's
-- L-slot post-composed with sins.  B₁-induction mirroring canonₛ-rwk (the
-- sins subst₂-conjugation via ⋯-subst₂ / subst-Tm-uip).
handle-L-rwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  proj₁ (canonₛ-handle B₁ e₁ x e₂ 0 (suc b₁ ∷ B₂))
  ≡ proj₁ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂) ⋯ sins B₁ b₁ B₂ {N}
handle-L-rwk [] {N} e₁ x e₂ zero     []       = ⋯-id (wk e₁) (λ _ → refl)
handle-L-rwk [] {N} e₁ x e₂ (suc b₁) []       = ⋯-id (wk e₁) (λ _ → refl)
handle-L-rwk [] {N} e₁ x e₂ zero     (c′ ∷ B) =
    cong (subst Tm (+-suc (suc (syncs (c′ ∷ B))) N)) (weaken-suc-shift e₁ (syncs (c′ ∷ B)))
  ■ sym (subst-⋯-cod-local (+-suc (suc (syncs (c′ ∷ B))) N)
           (subst Tm (+-suc (syncs (c′ ∷ B)) N) (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
           (weakenᵣ ↑* (suc (syncs (c′ ∷ B)))))
handle-L-rwk [] {N} e₁ x e₂ (suc b₁) (c′ ∷ B) =
    cong (subst Tm (+-suc (suc (syncs (c′ ∷ B))) N)) (weaken-suc-shift e₁ (syncs (c′ ∷ B)))
  ■ sym (subst-⋯-cod-local (+-suc (suc (syncs (c′ ∷ B))) N)
           (subst Tm (+-suc (syncs (c′ ∷ B)) N) (e₁ ⋯ weakenᵣ ⋯ weaken* ⦃ Kᵣ ⦄ (syncs (c′ ∷ B))))
           (weakenᵣ ↑* (suc (syncs (c′ ∷ B)))))
handle-L-rwk (a ∷ []) {N} e₁ x e₂ b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ([] ++ suc b₁ ∷ B₂)
    sBᴿ = syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)
    ρ   = sins [] b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handle [] (` 0F) (suc x) (wk e₂) b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
handle-L-rwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
    cong (subst Tm (+-suc sBᴿ N)) (handle-L-rwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB  = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sBᴿ = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    ρ   = sins (d ∷ B₁″) b₁ B₂ {suc N}
    t   = proj₁ (canonₛ-handle (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))

ss-Tm : ∀ {x y z : ℕ} (p : x ≡ y) (q : y ≡ z) (t : Tm x) → subst Tm q (subst Tm p t) ≡ subst Tm (p ■ q) t
ss-Tm refl refl t = refl

subst-`v : ∀ {p q} (e : p ≡ q) (v : 𝔽 p) → subst Tm e (` v) ≡ ` (subst 𝔽 e v)
subst-`v refl v = refl

-- rsplit grown-handle R-slot: the residual suc b₁-channel's R-slot (prefix B₁++[1],
-- carried to the C₁ᴿ scope by ++-assoc) = ungrown handle's R-slot ⋯ sins.
handle-R-rwk : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  subst Tm (cong (λ z → syncs z + N) (++-assoc B₁ (1 ∷ []) (suc b₁ ∷ B₂)))
    (proj₁ (proj₂ (canonₛ-handle (B₁ ++ 1 ∷ []) e₁ x e₂ b₁ B₂)))
  ≡ proj₁ (proj₂ (canonₛ-handle B₁ e₁ x e₂ b₁ B₂)) ⋯ sins B₁ b₁ B₂ {N}
handle-R-rwk [] {N} e₁ x e₂ zero     []       = refl
handle-R-rwk [] {N} e₁ x e₂ (suc b₁) []       = refl
handle-R-rwk [] {N} e₁ x e₂ zero     (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc sB' N))) (subst-`v (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))
  ■ subst-`v (cong suc (+-suc sB' N)) (subst 𝔽 (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))
  ■ cong `_ (Fin.toℕ-injective (toℕVL ■ sym toℕVR))
  ■ sym (cong (_⋯ sins [] zero (c′ ∷ B) {N}) (subst-`v (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F)))
  where
    toℕ-subst𝔽 : ∀ {a c} (e : a ≡ c) (y : 𝔽 a) → Fin.toℕ (subst 𝔽 e y) ≡ Fin.toℕ y
    toℕ-subst𝔽 refl y = refl
    sB' = syncs (c′ ∷ B)
    toℕVL : Fin.toℕ (subst 𝔽 (cong suc (+-suc sB' N)) (subst 𝔽 (+-suc sB' (suc N)) (weaken* ⦃ Kᵣ ⦄ sB' 0F))) ≡ sB'
    toℕVL = toℕ-subst𝔽 (cong suc (+-suc sB' N)) _ ■ toℕ-subst𝔽 (+-suc sB' (suc N)) _
          ■ toℕ-weaken*ᵣ sB' 0F ■ Nat.+-identityʳ sB'
    w : 𝔽 (suc sB' + N)
    w = subst 𝔽 (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F)
    wN : Fin.toℕ w ≡ sB'
    wN = toℕ-subst𝔽 (+-suc sB' N) (weaken* ⦃ Kᵣ ⦄ sB' 0F) ■ toℕ-weaken*ᵣ sB' 0F ■ Nat.+-identityʳ sB'
    toℕVR : Fin.toℕ (sins [] zero (c′ ∷ B) {N} w) ≡ sB'
    toℕVR = toℕ-subst-cod (+-suc (suc sB') N) (weakenᵣ ↑* suc sB') w
          ■ toℕ-↑*-lt weakenᵣ (suc sB') w (subst (Nat._< suc sB') (sym wN) (Nat.n<1+n sB'))
          ■ wN
handle-R-rwk [] {N} e₁ x e₂ (suc b₁) (c′ ∷ B) =
    cong (subst Tm (cong suc (+-suc (syncs (c′ ∷ B)) N))) (subst-Kunit (+-suc (syncs (c′ ∷ B)) (suc N)))
  ■ subst-Kunit (cong suc (+-suc (syncs (c′ ∷ B)) N))
  ■ sym (cong (_⋯ sins [] (suc b₁) (c′ ∷ B)) (subst-Kunit (+-suc (syncs (c′ ∷ B)) N)))
handle-R-rwk (a ∷ []) {N} e₁ x e₂ b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwk [] (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ []) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ([] ++ suc b₁ ∷ B₂)
    sBᴿ' = syncs (([] ++ 1 ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ([] ++ 1 ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ([] ++ 1 ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handle [] (` 0F) (suc x) (wk e₂) b₁ B₂))
    ρ    = sins [] b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc [] (1 ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ []) (1 ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a [] (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a [] 1 (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')
handle-R-rwk (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ =
    massage
  ■ cong (subst Tm (+-suc sBᴿ N)) (handle-R-rwk (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂)
  ■ sym ( cong (_⋯ sins (a ∷ d ∷ B₁″) b₁ B₂ {N}) (subst-Tm-uip (+-suc sB N) pL t)
        ■ ⋯-subst₂ pL pR t ρ
        ■ subst-Tm-uip pR (+-suc sBᴿ N) (t ⋯ ρ) )
  where
    sB   = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)
    sBᴿ' = syncs (((d ∷ B₁″) ++ 1 ∷ []) ++ suc b₁ ∷ B₂)
    sBᴿ  = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)
    T'   = proj₁ (proj₂ (canonₛ-handle ((d ∷ B₁″) ++ 1 ∷ []) (` 0F) (suc x) (wk e₂) b₁ B₂))
    t    = proj₁ (proj₂ (canonₛ-handle (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂))
    ρ    = sins (d ∷ B₁″) b₁ B₂ {suc N}
    castB' = cong (λ z → syncs z + suc N) (++-assoc (d ∷ B₁″) (1 ∷ []) (suc b₁ ∷ B₂))
    castA  = cong (λ z → syncs z + N) (++-assoc (a ∷ d ∷ B₁″) (1 ∷ []) (suc b₁ ∷ B₂))
    pL = +-suc sB N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) (suc b₁) B₂))
    pR = +-suc sBᴿ N ■ cong (_+ N) (sym (syncs-cons a (d ∷ B₁″) 1 (suc b₁ ∷ B₂)))
    massage : subst Tm castA (subst Tm (+-suc sBᴿ' N) T') ≡ subst Tm (+-suc sBᴿ N) (subst Tm castB' T')
    massage = ss-Tm (+-suc sBᴿ' N) castA T'
            ■ subst-Tm-uip (+-suc sBᴿ' N ■ castA) (castB' ■ +-suc sBᴿ N) T'
            ■ sym (ss-Tm castB' (+-suc sBᴿ N) T')

-- canonₛ over two ++-associated lists (same value) transports by subst.
canonₛ-cast : ∀ {L1 L2 : BindGroup} (p : L1 ≡ L2) {N} (cc : UChan N) (i : 𝔽 (sum L1)) →
  canonₛ L2 cc (subst (λ L → 𝔽 (sum L)) p i)
  ≡ subst (λ L → Tm (syncs L + N)) p (canonₛ L1 cc i)
canonₛ-cast refl cc i = refl

subst-syncs : ∀ {L1 L2 : BindGroup} (p : L1 ≡ L2) {N} (t : Tm (syncs L1 + N)) →
  subst (λ L → Tm (syncs L + N)) p t ≡ subst Tm (cong (λ z → syncs z + N) p) t
subst-syncs refl t = refl

-- L-slot of a head-triple whose head channel is (` 0F) is a variable at flat
-- position syncs (suc b₁ ∷ B₂).
head-L0-var : ∀ {N} (e2 : Tm (suc N)) (x : 𝔽 (suc N)) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs (suc b₁ ∷ B₂) + suc N) ]
    (proj₁ (canonₛ-head-triple b₁ B₂ (` 0F) e2 x) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
head-L0-var e2 x zero    []       = 0F , refl , refl
head-L0-var e2 x (suc b) []       = 0F , refl , refl
head-L0-var {N} e2 x zero (c′ ∷ B) =
    subst 𝔽 (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , subst-`v (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , (toℕ-substᶠ (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
      ■ toℕ-weaken*ᵣ sB (suc 0F) ■ Nat.+-comm sB 1)
  where sB = syncs (c′ ∷ B)
head-L0-var {N} e2 x (suc b) (c′ ∷ B) =
    subst 𝔽 (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , subst-`v (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
  , (toℕ-substᶠ (+-suc sB (suc N)) (weaken* ⦃ Kᵣ ⦄ sB (suc 0F))
      ■ toℕ-weaken*ᵣ sB (suc 0F) ■ Nat.+-comm sB 1)
  where sB = syncs (c′ ∷ B)

-- L-slot of canonₛ-handle on any nonempty prefix is a variable at position
-- syncs (suc b₁ ∷ B₂) (the handle recurses down to a (` 0F) leaf).
handle-L-var : ∀ (a : ℕ) (L' : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs ((a ∷ L') ++ suc b₁ ∷ B₂) + N) ]
    (proj₁ (canonₛ-handle (a ∷ L') e₁ x e₂ b₁ B₂) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
handle-L-var a [] {N} e₁ x e₂ b₁ B₂ with head-L0-var (wk e₂) (suc x) b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs ([] ++ suc b₁ ∷ B₂)
handle-L-var a (d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ with handle-L-var d B₁″ (` 0F) (suc x) (wk e₂) b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs ((d ∷ B₁″) ++ suc b₁ ∷ B₂)

handle-L1-var : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs ((B₁ ++ 1 ∷ []) ++ suc b₁ ∷ B₂) + N) ]
    (proj₁ (canonₛ-handle (B₁ ++ 1 ∷ []) e₁ x e₂ b₁ B₂) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
handle-L1-var []         {N} e₁ x e₂ b₁ B₂ = handle-L-var 1 [] e₁ x e₂ b₁ B₂
handle-L1-var (c ∷ B₁')  {N} e₁ x e₂ b₁ B₂ = handle-L-var c (B₁' ++ 1 ∷ []) e₁ x e₂ b₁ B₂

-- R-slot of the fresh 1-channel handle is a variable at position
-- syncs (suc b₁ ∷ B₂).
handle-R0-var : ∀ (B₁ : BindGroup) {N} (e₁ : Tm N) (x : 𝔽 N) (e₂ : Tm N) (b₁ : ℕ) (B₂ : BindGroup) →
  Σ[ v ∈ 𝔽 (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + N) ]
    (proj₁ (proj₂ (canonₛ-handle B₁ e₁ x e₂ 0 (suc b₁ ∷ B₂))) ≡ ` v)
    × (Fin.toℕ v ≡ syncs (suc b₁ ∷ B₂))
handle-R0-var [] {N} e₁ x e₂ b₁ B₂ =
    subst 𝔽 (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F)
  , subst-`v (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F)
  , (toℕ-substᶠ (+-suc sD N) (weaken* ⦃ Kᵣ ⦄ sD 0F)
      ■ toℕ-weaken*ᵣ sD 0F ■ Nat.+-identityʳ sD)
  where sD = syncs (suc b₁ ∷ B₂)
handle-R0-var (a ∷ []) {N} e₁ x e₂ b₁ B₂ with handle-R0-var [] (` 0F) (suc x) (wk e₂) b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs (1 ∷ suc b₁ ∷ B₂)
handle-R0-var (a ∷ d ∷ B₁″) {N} e₁ x e₂ b₁ B₂ with handle-R0-var (d ∷ B₁″) (` 0F) (suc x) (wk e₂) b₁ B₂
... | vh , eqh , tnh =
    subst 𝔽 (+-suc sB N) vh
  , (cong (subst Tm (+-suc sB N)) eqh ■ subst-`v (+-suc sB N) vh)
  , (toℕ-substᶠ (+-suc sB N) vh ■ tnh)
  where sB = syncs ((d ∷ B₁″) ++ 1 ∷ suc b₁ ∷ B₂)

comm3 : ∀ x y z → x + (y + z) ≡ y + (x + z)
comm3 x y z = sym (+-assoc x y z) ■ cong (_+ z) (Nat.+-comm x y) ■ +-assoc y x z

-- the leaf swap assocSwapᵣ sD 1 at leaf scope (L.length B₁ + a) — the φ-drop
-- binder, which sits ABOVE the B₁-prefix binders (de Bruijn-checked), slides past
-- the sD suffix-binders to the leaf.  Retyped to the (syncs C₁)-relative scope.
sw-dom : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
         syncs (B₁ ++ suc b₁ ∷ B₂) + suc a ≡ syncs (suc b₁ ∷ B₂) + (1 + (L.length B₁ + a))
sw-dom B₁ {b₁} {B₂} {a} =
    cong (_+ suc a) (syncs-split B₁)
  ■ +-suc (L.length B₁ + syncs (suc b₁ ∷ B₂)) a
  ■ cong suc (+-assoc (L.length B₁) (syncs (suc b₁ ∷ B₂)) a ■ comm3 (L.length B₁) (syncs (suc b₁ ∷ B₂)) a)
  ■ sym (+-suc (syncs (suc b₁ ∷ B₂)) (L.length B₁ + a))

sw-cod : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
         1 + (syncs (suc b₁ ∷ B₂) + (L.length B₁ + a)) ≡ suc (syncs (B₁ ++ suc b₁ ∷ B₂) + a)
sw-cod B₁ {b₁} {B₂} {a} =
  cong suc (comm3 (syncs (suc b₁ ∷ B₂)) (L.length B₁) a
           ■ sym (+-assoc (L.length B₁) (syncs (suc b₁ ∷ B₂)) a)
           ■ cong (_+ a) (sym (syncs-split B₁)))

sw-cast : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ} →
          (syncs (B₁ ++ suc b₁ ∷ B₂) + suc a) →ᵣ suc (syncs (B₁ ++ suc b₁ ∷ B₂) + a)
sw-cast B₁ {b₁} {B₂} {a} =
  subst₂ _→ᵣ_ (sym (sw-dom B₁ {b₁} {B₂} {a})) (sw-cod B₁ {b₁} {B₂} {a})
    (assocSwapᵣ (syncs (suc b₁ ∷ B₂)) 1 {L.length B₁ + a})

-- Prefix fold: applies one φ-binder per B₁-block, with the leaf at the bottom.
-- (Distinct from Bφ, which drops the last block; here EVERY block is a binder.)
Pfx : ∀ {n} (B₁ : BindGroup) → U.Proc (L.length B₁ + n) → U.Proc n
Pfx []        X = X
Pfx {n} (b ∷ B₁') X =
  U.φ ϕ[ b ] (Pfx B₁' (subst U.Proc (sym (+-suc (L.length B₁') n)) X))

Pfx-cong : ∀ {n} (B₁ : BindGroup) {X Y : U.Proc (L.length B₁ + n)} →
           X U.≋ Y → Pfx {n} B₁ X U.≋ Pfx B₁ Y
Pfx-cong []        xy = xy
Pfx-cong {n} (b ∷ B₁') xy =
  U.φ-cong (Pfx-cong B₁' (subst-≋ (sym (+-suc (L.length B₁') n)) xy))

subst-Pfx : ∀ {n n′} (e : n ≡ n′) (B₁ : BindGroup) (X : U.Proc (L.length B₁ + n)) →
            subst U.Proc e (Pfx {n} B₁ X)
            ≡ Pfx {n′} B₁ (subst U.Proc (cong (L.length B₁ +_) e) X)
subst-Pfx refl B₁ X = refl

-- ⋯ₚ lifts through Pfx by ↑* (L.length B₁) over the prefix binders.
Pfx-⋯ : ∀ {n n′} (B₁ : BindGroup) (X : U.Proc (L.length B₁ + n)) (ρ : n →ᵣ n′) →
        Pfx {n} B₁ X U.⋯ₚ ρ ≡ Pfx {n′} B₁ (X U.⋯ₚ (ρ ↑* L.length B₁))
Pfx-⋯ []        X ρ = refl
Pfx-⋯ {n} {n′} (b ∷ B₁') X ρ =
  cong (U.φ ϕ[ b ])
    ( Pfx-⋯ B₁' (subst U.Proc (sym (+-suc (L.length B₁') n)) X) (ρ ↑)
    ■ cong (Pfx B₁') bodyeq )
  where
    sB = L.length B₁'
    Θ : (sB + suc n) →ᵣ (sB + suc n′)
    Θ = (ρ ↑) ↑* sB
    Θ⁺eq : subst (λ z → z →ᵣ (sB + suc n′)) (+-suc sB n) Θ
           ≡ subst (λ z → suc (sB + n) →ᵣ z) (sym (+-suc sB n′)) (ρ ↑* suc sB)
    Θ⁺eq = subst-flip (+-suc sB n′) (sym (subst₂→ (+-suc sB n) (+-suc sB n′) Θ) ■ liftCast sB ρ)
    bodyeq : (subst U.Proc (sym (+-suc sB n)) X) U.⋯ₚ ((ρ ↑) ↑* sB)
             ≡ subst U.Proc (sym (+-suc sB n′)) (X U.⋯ₚ (ρ ↑* suc sB))
    bodyeq =
        TP-subst-⋯ₚ-dom (+-suc sB n) X Θ
      ■ cong (X U.⋯ₚ_) Θ⁺eq
      ■ subst-⋯ₚ-cod (sym (+-suc sB n′)) X (ρ ↑* suc sB)

-- Peel: Bφ over an append (with nonempty tail c∷D′) = Pfx of B₁ over Bφ of the tail.
syncs-split-gen : ∀ (Bp : BindGroup) (cc : ℕ) (Dp : BindGroup) →
                  syncs (Bp ++ cc ∷ Dp) ≡ L.length Bp + syncs (cc ∷ Dp)
syncs-split-gen []            cc Dp = refl
syncs-split-gen (x ∷ [])      cc Dp = cong suc (syncs-split-gen [] cc Dp)
syncs-split-gen (x ∷ y ∷ Bp″) cc Dp = cong suc (syncs-split-gen (y ∷ Bp″) cc Dp)

peel-eq : ∀ (B₁ : BindGroup) (c : ℕ) (D′ : BindGroup) {a : ℕ} →
          syncs (B₁ ++ c ∷ D′) + a ≡ syncs (c ∷ D′) + (L.length B₁ + a)
peel-eq B₁ c D′ {a} =
    cong (_+ a) (syncs-split-gen B₁ c D′)
  ■ +-assoc (L.length B₁) (syncs (c ∷ D′)) a
  ■ comm3 (L.length B₁) (syncs (c ∷ D′)) a

Bφ-peel : ∀ (B₁ : BindGroup) (c : ℕ) (D′ : BindGroup) {a : ℕ}
          (Z : U.Proc (syncs (B₁ ++ c ∷ D′) + a)) →
          Bφ (B₁ ++ c ∷ D′) Z
          ≡ Pfx B₁ (Bφ (c ∷ D′) (subst U.Proc (peel-eq B₁ c D′ {a}) Z))
Bφ-peel []        c D′ {a} Z =
  cong (Bφ (c ∷ D′)) (sym (cong (λ e → subst U.Proc e Z) (uipℕ (peel-eq [] c D′ {a}) refl)))
Bφ-peel (b ∷ [])       c D′ {a} Z =
  cong (U.φ ϕ[ b ])
    ( Bφ-peel [] c D′ {suc a} (subst U.Proc (sym (+-suc sT a)) Z)
    ■ cong (Pfx [])
        ( cong (Bφ (c ∷ D′)) bodyeq
        ■ sym (subst-Bφ (sym (+-suc (L.length ([] {A = ℕ})) a)) (c ∷ D′)
                 (subst U.Proc (peel-eq (b ∷ []) c D′ {a}) Z)) ) )
  where
    sT = syncs ([] ++ c ∷ D′)
    bodyeq : subst U.Proc (peel-eq [] c D′ {suc a})
               (subst U.Proc (sym (+-suc sT a)) Z)
             ≡ subst U.Proc (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length ([] {A = ℕ})) a)))
                 (subst U.Proc (peel-eq (b ∷ []) c D′ {a}) Z)
    bodyeq = ss-U (sym (+-suc sT a)) (peel-eq [] c D′ {suc a}) {t = Z}
           ■ cong (λ e → subst U.Proc e Z) (uipℕ _ _)
           ■ sym (ss-U (peel-eq (b ∷ []) c D′ {a})
                       (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length ([] {A = ℕ})) a))) {t = Z})
Bφ-peel (b ∷ x ∷ B₁'') c D′ {a} Z =
  cong (U.φ ϕ[ b ])
    ( Bφ-peel (x ∷ B₁'') c D′ {suc a} (subst U.Proc (sym (+-suc sT a)) Z)
    ■ cong (Pfx (x ∷ B₁''))
        ( cong (Bφ (c ∷ D′)) bodyeq
        ■ sym (subst-Bφ (sym (+-suc (L.length (x ∷ B₁'')) a)) (c ∷ D′)
                 (subst U.Proc (peel-eq (b ∷ x ∷ B₁'') c D′ {a}) Z)) ) )
  where
    sT = syncs ((x ∷ B₁'') ++ c ∷ D′)
    bodyeq : subst U.Proc (peel-eq (x ∷ B₁'') c D′ {suc a})
               (subst U.Proc (sym (+-suc sT a)) Z)
             ≡ subst U.Proc (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length (x ∷ B₁'')) a)))
                 (subst U.Proc (peel-eq (b ∷ x ∷ B₁'') c D′ {a}) Z)
    bodyeq = ss-U (sym (+-suc sT a)) (peel-eq (x ∷ B₁'') c D′ {suc a}) {t = Z}
           ■ cong (λ e → subst U.Proc e Z) (uipℕ _ _)
           ■ sym (ss-U (peel-eq (b ∷ x ∷ B₁'') c D′ {a})
                       (cong (syncs (c ∷ D′) +_) (sym (+-suc (L.length (x ∷ B₁'')) a))) {t = Z})

-- Pull a single φ binder OUT of a Bφ B block (reverse of φ-past-Bφ).
Bφ-φ-comm : (B : BindGroup) (z : U.Flag) {n : ℕ} (Y : U.Proc (1 + (syncs B + n))) →
            Bφ B (U.φ z Y) U.≋
            U.φ z (Bφ B (Y U.⋯ₚ assocSwapᵣ 1 (syncs B)))
Bφ-φ-comm B z {n} Y =
     Eq*.symmetric _
       ( φ-past-Bφ B z (Y U.⋯ₚ assocSwapᵣ 1 (syncs B))
       ◅◅ Bφ-cong B (U.φ-cong (≡→≋ bodyid)) )
  where
    bodyid : (Y U.⋯ₚ assocSwapᵣ 1 (syncs B)) U.⋯ₚ assocSwapᵣ (syncs B) 1 ≡ Y
    bodyid = U.fusionₚ Y (assocSwapᵣ 1 (syncs B)) (assocSwapᵣ (syncs B) 1)
           ■ local-⋯ₚ-id Y (assocSwap-invol 1 (syncs B))

-- The inserted φ-drop binder descends to the leaf.  Non-recursive: peel B₁ as a
-- Pfx prefix, push the (1-block) φ-drop down past Bφ (suc b₁ ∷ B₂) to the leaf
-- via φ-past-Bφ, then re-peel.  The ↑* L.length B₁ on the swap comes from Pfx-⋯.
Brwk-slide : ∀ (B₁ : BindGroup) {b₁ : ℕ} {B₂ : BindGroup} {a : ℕ}
             (Z : U.Proc (syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + a)) →
             Bφ (B₁ ++ 1 ∷ suc b₁ ∷ B₂) Z
             U.≋ Bφ (B₁ ++ suc b₁ ∷ B₂)
                   (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                                 U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
Brwk-slide B₁ {b₁} {B₂} {a} Z =
     ≡→≋ (Bφ-peel B₁ 1 (suc b₁ ∷ B₂) {a} Z)
  ◅◅ Pfx-cong B₁ (φ-past-Bφ (suc b₁ ∷ B₂) U.drop {L.length B₁ + a} bodyW)
  ◅◅ ≡→≋
       ( cong (Pfx B₁) (cong (Bφ (suc b₁ ∷ B₂)) reconcile)
       ■ sym (Bφ-peel B₁ (suc b₁) B₂ {a}
                (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                              U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))) )
  where
    sD = syncs (suc b₁ ∷ B₂)
    W0 : U.Proc (syncs (1 ∷ suc b₁ ∷ B₂) + (L.length B₁ + a))
    W0 = subst U.Proc (peel-eq B₁ 1 (suc b₁ ∷ B₂) {a}) Z
    bodyW : U.Proc (sD + suc (L.length B₁ + a))
    bodyW = subst U.Proc (sym (+-suc sD (L.length B₁ + a))) W0
    reconcile : U.φ U.drop (bodyW U.⋯ₚ assocSwapᵣ sD 1 {L.length B₁ + a})
                ≡ subst U.Proc (peel-eq B₁ (suc b₁) B₂ {a})
                    (U.φ U.drop (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                                  U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
    reconcile =
        cong (U.φ U.drop) reconcileBody
      ■ sym (subst-φ (peel-eq B₁ (suc b₁) B₂ {a})
               (subst U.Proc (cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)) Z
                 U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}))
      where
        raw : (sD + (1 + (L.length B₁ + a))) →ᵣ (1 + (sD + (L.length B₁ + a)))
        raw = assocSwapᵣ sD 1 {L.length B₁ + a}
        EQ : syncs (B₁ ++ 1 ∷ suc b₁ ∷ B₂) + a ≡ syncs (B₁ ++ suc b₁ ∷ B₂) + suc a
        EQ = cong (_+ a) (syncs-rwk B₁) ■ sym (+-suc (syncs (B₁ ++ suc b₁ ∷ B₂)) a)
        -- RHS body: subst EQ Z ⋯ sw-cast = subst (sw-cod) ((subst (EQ ■ sw-dom) Z) ⋯ raw).
        rhs≡ : subst U.Proc EQ Z U.⋯ₚ sw-cast B₁ {b₁} {B₂} {a}
               ≡ subst U.Proc (sw-cod B₁ {b₁} {B₂} {a})
                   (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)
        rhs≡ = cast-⋯2 (sw-dom B₁ {b₁} {B₂} {a}) (sw-cod B₁ {b₁} {B₂} {a}) (subst U.Proc EQ Z) raw
             ■ cong (λ w → subst U.Proc (sw-cod B₁ {b₁} {B₂} {a}) (w U.⋯ₚ raw))
                 (ss-U EQ (sw-dom B₁ {b₁} {B₂} {a}) {t = Z})
        -- LHS body: bodyW = subst (EQ ■ sw-dom) Z (same coercion, by UIP).
        bodyW≡ : bodyW ≡ subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z
        bodyW≡ = ss-U (peel-eq B₁ 1 (suc b₁ ∷ B₂) {a}) (sym (+-suc sD (L.length B₁ + a))) {t = Z}
               ■ cong (λ e → subst U.Proc e Z) (uipℕ _ (EQ ■ sw-dom B₁ {b₁} {B₂} {a}))
        reconcileBody =
            cong (U._⋯ₚ raw) bodyW≡
          ■ sym ( cong (subst U.Proc (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))) rhs≡
                ■ ss-U (sw-cod B₁ {b₁} {B₂} {a}) (cong suc (peel-eq B₁ (suc b₁) B₂ {a}))
                       {t = subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw}
                ■ cong (λ e → subst U.Proc e (subst U.Proc (EQ ■ sw-dom B₁ {b₁} {B₂} {a}) Z U.⋯ₚ raw)) (uipℕ _ refl) )

