-- | Backward simulation, RU-RSplit.  Reflects one untyped remote-split step
--   back to a typed R-RSplit step in the CLEAN single-step codomain.  Ported from
--   BorrowedCF.Simulation.RevRSplit (SplitRenamings moved to Terms and now takes a
--   `sum B`-shaped ℕ; the ⊎ cleanup slot of the codomain collapsed).
module BorrowedCF.Simulation2.Backward.RSplit where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Typed   as TR
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Terms using (module SplitRenamings)
open import BorrowedCF.Simulation.ReverseInv
  using (νσ; ⊗-inj; νσ-VSub; U-ν-singleton;
         frameApp-reflect; inv-U-ν-∥-shape; inv-ν-chanCx; ν-inj; close-arg-var)
open import BorrowedCF.Simulation2.Backward.LSplit using (fin-split)
open import BorrowedCF.Simulation2.Backward.Inversions using (inv-U-⟪⟫; inv-U-∥; inv-U-ν)
open import BorrowedCF.Simulation.RevComImage using (com-image-block1)
open import BorrowedCF.Simulation.RevAdmin using (_≈_; ≋⇒≈)
open import BorrowedCF.Simulation.TranslationProperties using (≡→≋; U-σ⋯; U-⋯ₚ; U-cong)
open import BorrowedCF.Simulation.InvFrame using (fn-rsplit-dom; strengthen-frame)
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯; ++ₛ-VSub)
open import BorrowedCF.Simulation.RsplitTransport using (toℕ-subst-cod)
open import BorrowedCF.Simulation.FrameRename using (F-σ⋯; ⋯ᶠ*-fuse)
open import BorrowedCF.Simulation.SplitConfine using (rsplit-confine)
open import BorrowedCF.Simulation.Theorems.SplitsH1 using (leafσ; canonₛ; canonₛ-handle; VSub-canonₛ)
open import BorrowedCF.Simulation.Theorems.Splits
  using (leafσ-rwk-idq; sinsq; sins-toℕ-hiq; canonₛ-handleq; handle-L-rwkq; handle-R-rwkq;
         handle-R0-varq; handle-L1-varq; F-⋯f*-fuse; frame*-cong; ·ₖ-VSubᵣ)
open import BorrowedCF.Simulation.BlockPerm using (toℕ-weaken*ᵣ)
open import Data.Nat.ListAction.Properties using (sum-++)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Data.Fin.Properties using (toℕ-cast; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; toℕ<n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; m+[n∸m]≡n)
import Data.Sum as Sum
open TP using (BindGroup)

rsplit-arg-chan : ∀ {N} {Γ : Ctx N} {α : Struct N} {s : 𝕊 0} {arg : Tm N} {T ϵ}
  → Γ ; α ⊢ K (`rsplit s) ·¹ arg ∶ T ∣ ϵ
  → Σ[ s′ ∈ 𝕊 0 ] Σ[ β ∈ Struct N ] Σ[ R ∈ 𝕋 ] Σ[ ϵ₂ ∈ Eff ]
      (Γ ; β ⊢ arg ∶ R ∣ ϵ₂) × (⟨ s ; s′ ⟩ ≃ R)
rsplit-arg-chan (T-AppUnr _ _ ⊢fn ⊢arg) = let s′ , eq = fn-rsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
rsplit-arg-chan (T-AppLin _ _ ⊢fn ⊢arg) = let s′ , eq = fn-rsplit-dom ⊢fn in s′ , _ , _ , _ , ⊢arg , eq
rsplit-arg-chan (T-Conv _ _ d) = rsplit-arg-chan d
rsplit-arg-chan (T-Weaken _ d) = rsplit-arg-chan d

module _ {m n : ℕ} (σ : m →ₛ n) (Vσ : VSub σ) (q b₁' b₂ : ℕ) where

  private
    module 𝐒 = SplitRenamings [] [] (sum (b₂ ∷ []))
    swk = 𝐒.rwk {q = q} {b = b₁'} {n = m}
    C₁ : BindGroup
    C₁  = (q + suc b₁') ∷ []
    C₁ᴿ : BindGroup
    C₁ᴿ = (q + 1) ∷ suc b₁' ∷ []
    Bg : BindGroup
    Bg  = b₂ ∷ []

    νσ0 : sum C₁ + sum Bg + m →ₛ 2 + n
    νσ0 = νσ (q + suc b₁') b₂ σ

    atkU : 𝔽 (sum C₁ + sum Bg + m)
    atkU = 𝐒.atk {q + suc b₁'} {m} (q ↑ʳ 0F)

    injG0 injG1 : 𝔽 (sum C₁ᴿ + sum Bg + m)
    injG0 = 𝐒.inj {B = (q + 1) ∷ suc b₁' ∷ []} ((q ↑ʳ 0F) ↑ˡ (suc b₁' + sum ([] {A = ℕ})))
    injG1 = 𝐒.inj {B = (q + 1) ∷ suc b₁' ∷ []} ((q + 1) ↑ʳ 0F)

    Vνσ0 : VSub νσ0
    Vνσ0 = νσ-VSub (q + suc b₁') b₂ σ Vσ

  rsplit-recon :
    ∀ {Γ : Ctx m} (Γ-S : ChanCx Γ) {γ : Struct m} {s : 𝕊 0}
      {F₀ : Frame* (sum C₁ + sum Bg + m)} {P₁t : TP.Proc (sum C₁ + sum Bg + m)}
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
    → Γ ; γ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)
    → F ≡ frame*-⋯ F₀ νσ0 Vνσ0
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
    → P₁ ≡ U[ P₁t ] νσ0
    → UP.ν (UP.φ UP.drop
            (UP.⟪ (F ⋯ᶠ* weakenᵣ)
                   [ ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ]* ⟫
             UP.∥ (P₁ UP.⋯ₚ weakenᵣ)))
      ≡ U[ TP.ν C₁ᴿ Bg (TP.⟪ F₀ ⋯ᶠ* swk [ (` injG0) ⊗ (` injG1) ]* ⟫ TP.∥ (P₁t TP.⋯ₚ swk)) ] σ
  -- rsplit-recon : the reverse-RSplit codomain equality  Q ≡ U[ P′ ] σ.
  --   Q = the RU-RSplit contractum (ν (φ drop (⟪…⟫ ∥ …))), P′ = the R-RSplit
  --   result.  Because the reverse works in the DIRECT U-ν layout (no leafσ
  --   flattening), this is a PURE equality (unlike the forward's ≋ back-bridge).
  --   Split by cong into three pieces:
  --     * φ-eq   : UP.drop ≡ ϕ[ q + 1 ]                             — DONE.
  --     * thread-eq (goal 0): the frame+leaf-triple identity; the U-ν-layout
  --         port of the forward's frame-eq ■ ccTripleᴿ0/ccTripleᴿ1 (inj0/inj1
  --         grown triples), WITHOUT the ρ₁ᴿ/ρ₂ᴿ/assocSwap reordering.
  --     * rest-eq  (goal 1): the residual rwk-naturality; the U-ν-layout port
  --         of the forward's Prwkeq.
  --   Both goal 0 and goal 1 reduce to a single missing pointwise lemma
  --     νσ-Σ-rwk-id : ∀ v → v ≢ atkU → νσ0 v ⋯ weakenᵣ ≡ Σ (swk v)
  --   (Σ = the U-ν innermost substitution for C₁ᴿ,Bg), the U-ν analogue of
  --   SplitsRQ2.leafσ-rwk-idq.  Its TAIL (σ-)component is clean (νσ0 tail ⋯
  --   weakenᵣ = σ⋯weaken*3 = Σ tail); its C₁-BLOCK component is the handle-growth
  --   content carried by SplitsRQ2.handle-L-rwkq / handle-R-rwkq (+ the at-handle
  --   injG0/injG1 canonₛ decompositions for thread-eq), threaded through
  --   rsplit-confine (ρ⁻/skip) exactly as lsplit-recon threads lsplit-confine.
  rsplit-recon Γ-S {s = s} {F₀ = F₀} {P₁t = P₁t} {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq
    with rsplit-confine Γ-S {B₁ = []} {B₂ = []} {B = Bg} {q = q} {b₁ = b₁'} {s = s} {E = F₀} {P = P₁t} ⊢P
  ... | _ , ρ⁻ , skipH , E₀ , Eeq , P₀ , Peq =
    cong UP.ν (cong₂ UP.φ φ-eq (cong₂ UP._∥_ threadEq restEq))
    where
      φ-eq : UP.drop ≡ ϕ[ q + 1 ]
      φ-eq = sym (cong ϕ[_] (Nat.+-comm q 1))

      Σᴿ : sum C₁ᴿ + sum Bg + m →ₛ suc (2 + n)
      Σᴿ = leafσ σ C₁ᴿ Bg

      VΣ : VSub Σᴿ
      VΣ = ++ₛ-VSub
             (++ₛ-VSub
               (λ i → value-⋯ (VSub-canonₛ C₁ᴿ (K `unit , 0F , K `unit) (V-K , V-K) i)
                         (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`))
               (VSub-canonₛ Bg (K `unit , weaken* ⦃ Kᵣ ⦄ (syncs C₁ᴿ) 1F , K `unit) (V-K , V-K)))
             (λ i → value-⋯ (value-⋯ (value-⋯ (Vσ i)
                       (weaken* ⦃ Kᵣ ⦄ 2) (λ _ → V-`))
                       (weaken* ⦃ Kᵣ ⦄ (syncs C₁ᴿ)) (λ _ → V-`))
                       (weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (λ _ → V-`))

      sins-wk : ∀ (w : 𝔽 (0 + (2 + n))) →
                (sinsq [] q b₁' [] {2 + n} ↑* syncs Bg) w ≡ weakenᵣ w
      sins-wk w = Fin.toℕ-injective (sins-toℕ-hiq [] q b₁' [] {2 + n} w Nat.z≤n)

      νσ-Σ-rwk-id : ∀ v → v ≢ atkU → νσ0 v ⋯ weakenᵣ ≡ Σᴿ (swk v)
      νσ-Σ-rwk-id v v≢ =
          ⋯-cong (νσ0 v) (λ w → sym (sins-wk w))
        ■ leafσ-rwk-idq σ [] [] Bg q b₁' v v≢

      restEq : P₁ UP.⋯ₚ weakenᵣ ≡ U[ P₁t TP.⋯ₚ swk ] Σᴿ
      restEq =
          cong (UP._⋯ₚ weakenᵣ) Resteq
        ■ U-σ⋯ P₁t
        ■ cong (λ p → U[ p ] (νσ0 ·ₖ weakenᵣ)) Peq
        ■ U-⋯ₚ P₀
        ■ U-cong P₀ (λ y → νσ-Σ-rwk-id (ρ⁻ y) (skipH y))
        ■ sym (U-⋯ₚ P₀)
        ■ cong (λ p → U[ p ] (swk ·ₖ Σᴿ)) (sym Peq)
        ■ sym (U-⋯ₚ P₁t)

      frameNat : frame*-⋯ F₀ νσ0 Vνσ0 ⋯ᶠ* weakenᵣ ≡ frame*-⋯ (F₀ ⋯ᶠ* swk) Σᴿ VΣ
      frameNat = sym
        ( cong (λ EE → frame*-⋯ (EE ⋯ᶠ* swk) Σᴿ VΣ) Eeq
        ■ cong (λ EE → frame*-⋯ EE Σᴿ VΣ) (⋯ᶠ*-fuse E₀ ρ⁻ swk)
        ■ F-⋯f*-fuse E₀ VΣ (·ₖ-VSubᵣ (ρ⁻ ·ₖ swk) VΣ)
        ■ frame*-cong E₀ (·ₖ-VSubᵣ (ρ⁻ ·ₖ swk) VΣ)
            (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vνσ0 y) weakenᵣ (λ x → V-`))
            (λ y → sym (νσ-Σ-rwk-id (ρ⁻ y) (skipH y)))
        ■ sym (F-σ⋯ E₀ (·ₖ-VSubᵣ ρ⁻ Vνσ0) weakenᵣ
                 (λ y → value-⋯ (·ₖ-VSubᵣ ρ⁻ Vνσ0 y) weakenᵣ (λ x → V-`)))
        ■ cong (_⋯ᶠ* weakenᵣ) (sym (F-⋯f*-fuse E₀ Vνσ0 (·ₖ-VSubᵣ ρ⁻ Vνσ0)))
        ■ cong (λ EE → frame*-⋯ EE νσ0 Vνσ0 ⋯ᶠ* weakenᵣ) (sym Eeq) )

      hc = canonₛ-handleq [] {2 + n} (K `unit) 0F (K `unit) q b₁' []
      wk0 : (2 + n) →ᵣ (0 + (2 + n))
      wk0 = weaken* ⦃ Kᵣ ⦄ 0

      castposU : 𝔽 (sum C₁)
      castposU = Fin.cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
      atkeqU : νσ0 atkU ≡ canonₛ C₁ (K `unit , 0F , K `unit) castposU ⋯ wk0
      atkeqU = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ + sum Bg) (castposU ↑ˡ sum Bg) m)
             ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁) castposU (sum Bg))
      junc0 : (j : 𝔽 (syncs C₁ + (2 + n))) → Fin.toℕ j ≡ 0 → wk0 j ≡ 0F
      junc0 j tj = Fin.toℕ-injective (toℕ-weaken*ᵣ 0 j ■ tj)

      νσ0-tri : νσ0 atkU ≡ ((proj₁ hc ⋯ wk0) ⊗ (` 0F)) ⊗ (proj₁ (proj₂ hc) ⋯ wk0)
      νσ0-tri = atkeqU
              ■ cong (_⋯ wk0) (proj₁ (proj₂ (proj₂ (proj₂ hc))))
              ■ cong (λ z → ((proj₁ hc ⋯ wk0) ⊗ (` z)) ⊗ (proj₁ (proj₂ hc) ⋯ wk0))
                  (junc0 (proj₁ (proj₂ (proj₂ hc))) (proj₂ (proj₂ (proj₂ (proj₂ hc)))))

      e₁≡ : e₁ ≡ proj₁ hc ⋯ wk0
      e₁≡ = proj₁ (⊗-inj (proj₁ (⊗-inj (argeq ■ νσ0-tri))))
      e₂≡ : e₂ ≡ proj₁ (proj₂ hc) ⋯ wk0
      e₂≡ = proj₂ (⊗-inj (argeq ■ νσ0-tri))

      hcᴿ0 = canonₛ-handleq [] {2 + n} (K `unit) 0F (K `unit) q 0 (suc b₁' ∷ [])
      castposᴿ0 : 𝔽 (sum C₁ᴿ)
      castposᴿ0 = Fin.cast (sym (sum-++ [] C₁ᴿ)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ (suc b₁' + sum ([] {A = ℕ}))))
      τᴿinj0 : Σᴿ injG0 ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
      τᴿinj0 = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum Bg) (castposᴿ0 ↑ˡ sum Bg) m)
             ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ0 (sum Bg))
      junc1 : weaken* ⦃ Kᵣ ⦄ (syncs Bg) (proj₁ (proj₂ (proj₂ hcᴿ0))) ≡ 1F
      junc1 = Fin.toℕ-injective
                (toℕ-weaken*ᵣ (syncs Bg) (proj₁ (proj₂ (proj₂ hcᴿ0)))
                 ■ proj₂ (proj₂ (proj₂ (proj₂ hcᴿ0))))
      slotL0 : proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ≡ proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ⋯ (sinsq [] q b₁' [] {2 + n} ↑* syncs Bg)
      slotL0 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (handle-L-rwkq [] (K `unit) 0F (K `unit) q b₁' [])
             ■ ⋯-↑*-wk (proj₁ hc) (sinsq [] q b₁' [] {2 + n}) (syncs Bg)
      LslotEq : proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ≡ wk e₁
      LslotEq = slotL0
              ■ ⋯-cong (proj₁ hc ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) sins-wk
              ■ cong (_⋯ weakenᵣ) (sym e₁≡)
      hR0 = handle-R0-varq [] {2 + n} (K `unit) 0F (K `unit) q b₁' []
      Rv0≡0F : weaken* ⦃ Kᵣ ⦄ (syncs Bg) (proj₁ hR0) ≡ 0F
      Rv0≡0F = Fin.toℕ-injective (toℕ-weaken*ᵣ (syncs Bg) (proj₁ hR0) ■ proj₂ (proj₂ hR0))
      RslotEq : proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ≡ (` 0F)
      RslotEq = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (proj₁ (proj₂ hR0))
              ■ cong `_ Rv0≡0F

      tripleL : ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ≡ Σᴿ injG0
      tripleL = sym
        ( τᴿinj0
        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (proj₁ (proj₂ (proj₂ (proj₂ hcᴿ0))))
        ■ cong (λ z → ((proj₁ hcᴿ0 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) ⊗ (` z)) ⊗ (proj₁ (proj₂ hcᴿ0) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))) junc1
        ■ cong₂ (λ L R → (L ⊗ (` 1F)) ⊗ R) LslotEq RslotEq )
      hcᴿ1 = canonₛ-handle ((q + 1) ∷ []) {2 + n} (K `unit) 0F (K `unit) b₁' []
      j0ᴿ = proj₁ (proj₂ (proj₂ hcᴿ1))
      castposᴿ1 : 𝔽 (sum C₁ᴿ)
      castposᴿ1 = Fin.cast (sym (sum-++ [] C₁ᴿ)) (sum [] ↑ʳ ((q + 1) ↑ʳ 0F))
      hcᴿ1castpos : 𝔽 (sum C₁ᴿ)
      hcᴿ1castpos = Fin.cast (sym (sum-++ ((q + 1) ∷ []) (suc b₁' ∷ []))) (sum ((q + 1) ∷ []) ↑ʳ 0F)
      tc1 : Fin.toℕ castposᴿ1 ≡ q + 1
      tc1 = toℕ-cast (sym (sum-++ [] C₁ᴿ)) (sum [] ↑ʳ ((q + 1) ↑ʳ 0F))
          ■ toℕ-↑ʳ (sum ([] {A = ℕ})) ((q + 1) ↑ʳ 0F)
          ■ toℕ-↑ʳ (q + 1) 0F
          ■ +-identityʳ (q + 1)
      tc2 : Fin.toℕ hcᴿ1castpos ≡ q + 1
      tc2 = toℕ-cast (sym (sum-++ ((q + 1) ∷ []) (suc b₁' ∷ []))) (sum ((q + 1) ∷ []) ↑ʳ 0F)
          ■ toℕ-↑ʳ (sum ((q + 1) ∷ [])) 0F
          ■ +-identityʳ (sum ((q + 1) ∷ []))
          ■ +-identityʳ (q + 1)
      cast-eq : castposᴿ1 ≡ hcᴿ1castpos
      cast-eq = Fin.toℕ-injective (tc1 ■ sym tc2)
      τᴿinj1 : Σᴿ injG1 ≡ canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
      τᴿinj1 = cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ + sum Bg) (castposᴿ1 ↑ˡ sum Bg) m)
             ■ cong [ _ , _ ]′ (Fin.splitAt-↑ˡ (sum C₁ᴿ) castposᴿ1 (sum Bg))
      canonᴿ1-decomp' : canonₛ C₁ᴿ (K `unit , 0F , K `unit) castposᴿ1 ≡ (proj₁ hcᴿ1 ⊗ (` j0ᴿ)) ⊗ proj₁ (proj₂ hcᴿ1)
      canonᴿ1-decomp' = cong (canonₛ C₁ᴿ (K `unit , 0F , K `unit)) cast-eq
                      ■ proj₁ (proj₂ (proj₂ (proj₂ hcᴿ1)))
      juncR1 : weaken* ⦃ Kᵣ ⦄ (syncs Bg) j0ᴿ ≡ 1F
      juncR1 = Fin.toℕ-injective (toℕ-weaken*ᵣ (syncs Bg) j0ᴿ ■ proj₂ (proj₂ (proj₂ (proj₂ hcᴿ1))))
      hL1 = handle-L1-varq [] {2 + n} (K `unit) 0F (K `unit) q b₁' []
      Lv0≡0F : weaken* ⦃ Kᵣ ⦄ (syncs Bg) (proj₁ hL1) ≡ 0F
      Lv0≡0F = Fin.toℕ-injective (toℕ-weaken*ᵣ (syncs Bg) (proj₁ hL1) ■ proj₂ (proj₂ hL1))
      LslotEqR : proj₁ hcᴿ1 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ≡ (` 0F)
      LslotEqR = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (proj₁ (proj₂ hL1)) ■ cong `_ Lv0≡0F
      slotR1 : proj₁ (proj₂ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)
             ≡ proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ⋯ (sinsq [] q b₁' [] {2 + n} ↑* syncs Bg)
      slotR1 = cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) (handle-R-rwkq [] (K `unit) 0F (K `unit) q b₁' [])
             ■ ⋯-↑*-wk (proj₁ (proj₂ hc)) (sinsq [] q b₁' [] {2 + n}) (syncs Bg)
      RslotEqR : proj₁ (proj₂ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg) ≡ wk e₂
      RslotEqR = slotR1
               ■ ⋯-cong (proj₁ (proj₂ hc) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) sins-wk
               ■ cong (_⋯ weakenᵣ) (sym e₂≡)

      tripleR : (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ≡ Σᴿ injG1
      tripleR = sym
        ( τᴿinj1
        ■ cong (_⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) canonᴿ1-decomp'
        ■ cong (λ z → ((proj₁ hcᴿ1 ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg)) ⊗ (` z)) ⊗ (proj₁ (proj₂ hcᴿ1) ⋯ weaken* ⦃ Kᵣ ⦄ (syncs Bg))) juncR1
        ■ cong₂ (λ L R → (L ⊗ (` 1F)) ⊗ R) LslotEqR RslotEqR )

      body-eq : (((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂))
              ≡ ((` injG0) ⊗ (` injG1)) ⋯ Σᴿ
      body-eq = cong₂ _⊗_ tripleL tripleR

      threadEq : UP.⟪ (F ⋯ᶠ* weakenᵣ)
                        [ ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ]* ⟫
               ≡ U[ TP.⟪ F₀ ⋯ᶠ* swk [ (` injG0) ⊗ (` injG1) ]* ⟫ ] Σᴿ
      threadEq = cong UP.⟪_⟫
        ( cong₂ _[_]* (cong (_⋯ᶠ* weakenᵣ) Feq ■ frameNat) body-eq
        ■ sym (frame-plug* (F₀ ⋯ᶠ* swk) Σᴿ VΣ) )

  rsplit-go :
    ∀ {Γ : Ctx m} (Γ-S : ChanCx Γ) {γ : Struct m} {s : 𝕊 0}
      (b₁ : ℕ) (b₁≡ : b₁ ≡ q + suc b₁')
      (z : 𝔽 (b₁ + 0)) (toℕz≡q : Fin.toℕ z ≡ q)
      {F₀ : Frame* (sum (b₁ ∷ []) + sum Bg + m)}
      {P₁t : TP.Proc (sum (b₁ ∷ []) + sum Bg + m)}
      {argᴸ : Tm (sum (b₁ ∷ []) + sum Bg + m)}
      (argᴸ≡ : argᴸ ≡ (` ((z ↑ˡ sum Bg) ↑ˡ m)))
      {F : Frame* (2 + n)} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
    → Γ ; γ ⊢ₚ TP.ν (b₁ ∷ []) Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)
    → F ≡ frame*-⋯ F₀ (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ)
    → ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ argᴸ ⋯ νσ b₁ b₂ σ
    → P₁ ≡ U[ P₁t ] (νσ b₁ b₂ σ)
    → Σ[ P′ ∈ TP.Proc m ]
        (Star TR._─→ₚ_
           (TP.ν (b₁ ∷ []) Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)) P′)
      × ((UP.ν (UP.φ UP.drop
                 (UP.⟪ (F ⋯ᶠ* weakenᵣ)
                        [ ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ]* ⟫
                  UP.∥ (P₁ UP.⋯ₚ weakenᵣ))))
          ≈ U[ P′ ] σ)
  rsplit-go Γ-S {s = s} b₁ refl z toℕz≡q {F₀ = F₀} {P₁t = P₁t} {argᴸ = argᴸ} argᴸ≡
            {F = F} {e₁ = e₁} {e₂ = e₂} {P₁ = P₁} ⊢P Feq argeq Resteq =
    P′ , step , ≋⇒≈ (≡→≋ recon)
    where
      P′ : TP.Proc m
      P′ = TP.ν C₁ᴿ Bg (TP.⟪ F₀ ⋯ᶠ* swk [ (` injG0) ⊗ (` injG1) ]* ⟫ TP.∥ (P₁t TP.⋯ₚ swk))

      castposU-toℕ : Fin.toℕ (Fin.cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))) ≡ q
      castposU-toℕ =
          toℕ-cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
        ■ toℕ-↑ˡ (q ↑ʳ 0F) (sum [])
        ■ toℕ-↑ʳ q 0F
        ■ +-identityʳ q

      z≡ : z ≡ Fin.cast (sym (sum-++ [] C₁)) (sum [] ↑ʳ ((q ↑ʳ 0F) ↑ˡ sum []))
      z≡ = toℕ-injective (toℕz≡q ■ sym castposU-toℕ)

      argᴸ≡atkU : argᴸ ≡ (` atkU)
      argᴸ≡atkU = argᴸ≡ ■ cong (λ w → (` ((w ↑ˡ sum Bg) ↑ˡ m))) z≡

      ⊢P' : _ ; _ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)
      ⊢P' = subst (λ v → _ ; _ ⊢ₚ TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ v ]* ⟫ TP.∥ P₁t))
              argᴸ≡atkU ⊢P

      argeq' : ((e₁ ⊗ (` 0F)) ⊗ e₂) ≡ (` atkU) ⋯ νσ0
      argeq' = argeq ■ cong (λ v → v ⋯ νσ0) argᴸ≡atkU

      recon : UP.ν (UP.φ UP.drop
                    (UP.⟪ (F ⋯ᶠ* weakenᵣ)
                           [ ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ]* ⟫
                     UP.∥ (P₁ UP.⋯ₚ weakenᵣ)))
              ≡ U[ P′ ] σ
      recon = rsplit-recon Γ-S ⊢P' Feq argeq' Resteq

      stepAtk : Star TR._─→ₚ_
                  (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ (` atkU) ]* ⟫ TP.∥ P₁t)) P′
      stepAtk = TR.R-RSplit {B₁ = []} {B₂ = []} {B = Bg} {q = q} {b₁ = b₁'} {s = s} {P = P₁t} {E = F₀} ◅ ε

      step : Star TR._─→ₚ_
               (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ argᴸ ]* ⟫ TP.∥ P₁t)) P′
      step = subst (λ v → Star TR._─→ₚ_
                     (TP.ν C₁ Bg (TP.⟪ F₀ [ K (`rsplit s) ·¹ v ]* ⟫ TP.∥ P₁t)) P′)
               (sym argᴸ≡atkU) stepAtk

-- RU-RSplit reflection (interface as in Backward.Leaf.bwd-fork / lsplit-reflect):
-- the untyped redex is its frame F + the equation U[ P ] σ ≡ (RU-RSplit LHS);
-- result = (RU-RSplit RHS) ≈-bridged to U[ P′ ] σ.  Wired at Backward.agda:119
-- by  rsplit-reflect σ Vσ Γ-S ⊢P (sym eq).
rsplit-reflect : ∀ {m n} (σ : m →ₛ n) → VSub σ → {Γ : Ctx m} → ChanCx Γ
               → {g : Struct m} {P : TP.Proc m} → Γ ; g ⊢ₚ P
               → {s : 𝕊 0} {e₁ e₂ : Tm (2 + n)} {P₁ : UP.Proc (2 + n)}
                 {F : Frame* (2 + n)}
               → U[ P ] σ ≡ UP.ν (UP.⟪ F [ K (`rsplit s) ·¹ ((e₁ ⊗ (` 0F)) ⊗ e₂) ]* ⟫ UP.∥ P₁)
               → Σ[ P′ ∈ TP.Proc m ]
                   (Star TR._─→ₚ_ P P′
                    × UP.ν (UP.φ UP.drop
                        (UP.⟪ (F ⋯ᶠ* weakenᵣ)
                               [ ((wk e₁ ⊗ (` 1F)) ⊗ (` 0F)) ⊗ (((` 0F) ⊗ (` 1F)) ⊗ wk e₂) ]* ⟫
                         UP.∥ (P₁ UP.⋯ₚ weakenᵣ)))
                        ≈ U[ P′ ] σ)
rsplit-reflect σ Vσ Γ-S {P = P} ⊢P {s = s} {F = F} eq
  with B₁ , B₂ , P₀ , refl , bodyeq ← inv-U-ν P σ eq
  with inv-U-ν-∥-shape B₁ B₂ P₀ σ bodyeq
... | Sum.inj₂ (Sum.inj₁ refl)
  with _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₂ (Sum.inj₂ refl)
  with _ , _ , _ , _ , _ , _ , _ , _ , () , _ ← inv-ν ⊢P
... | Sum.inj₁ (b₁ , b₂ , refl , refl)
  with _ , _ , Γ′-S , ⊢body ← inv-ν-chanCx Γ-S ⊢P
  with bodyeq′ ← ν-inj (bodyeq ■ U-ν-singleton b₁ b₂ P₀ σ)
  with PL , P₁t , refl , Leq , Resteq ← inv-U-∥ P₀ (νσ b₁ b₂ σ) (sym bodyeq′)
  with eL , refl , Leq′ ← inv-U-⟪⟫ PL (νσ b₁ b₂ σ) (sym Leq)
  with _ , _ , _ , ⊢PL , ⊢P₁t ← inv-∥ ⊢body
  with F₀ , argᴸ , refl , Feq , argeq
       ← frameApp-reflect Γ′-S eL (inv-⟪⟫ ⊢PL) (νσ b₁ b₂ σ) (νσ-VSub b₁ b₂ σ Vσ) (`rsplit s)
           F (sym Leq′)
  with _ , (_ , _ , ⊢plug) , _ , _ ← strengthen-frame F₀ (inv-⟪⟫ ⊢PL)
  with _ , _ , _ , _ , ⊢argᴸ , ch ← rsplit-arg-chan ⊢plug
  with x , argᴸ≡ ← close-arg-var argᴸ ⊢argᴸ ch (νσ b₁ b₂ σ) (sym argeq)
  with z , _ , xeq ← com-image-block1 b₁ b₂ σ Vσ x (argeq ■ cong (_⋯ νσ b₁ b₂ σ) argᴸ≡)
  with b₁' , b₁≡ ← fin-split b₁ z =
  rsplit-go σ Vσ (Fin.toℕ z) b₁' b₂ Γ-S b₁ b₁≡ z refl
    (argᴸ≡ ■ cong `_ xeq) ⊢P Feq argeq Resteq
