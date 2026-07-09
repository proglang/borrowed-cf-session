module BorrowedCF.Simulation2.Backward.NonEpsRoadblock where

-- | MACHINE-CHECKED roadblock for the φ-DECOMPOSITION route (route b) of the
--   reverse-simulation non-ε engine  (Backward.agda ?0).
--
--   Route b keeps the untyped step `red` and its reduct `R` FIXED and varies the
--   TYPED source, peeling the ≋-link ADJACENT TO THE IMAGE and recognising it as
--   an image→image move so that the untyped ≋-chain gets STRICTLY SHORTER
--   (termination is on chain length).  It classifies the ≋′ generators as
--     • image→image  : ∥-comm/assoc/unit, ν-swap′, ν-comm′   (recognise, recurse)
--     • image-escape : νφ-comm′                              (push φ in, separate)
--   and BETS that the image→image class admits a STRICT single-step recognition
--       recog : U[ P ]σ ≋′ S  →  Σ P̃. (S ≡ U[ P̃ ]σ) × (P ≋ P̃)
--   (S is again a strict image, exactly ONE link closer), so chain length falls.
--
--   THIS MODULE REFUTES THAT BET for the ν-renaming generator `ν-swap′`, at the
--   RevCongStrongLE bar: the only structurally-available recogniser violates the
--   descent metric the engine's termination requires.
--
--   For an image  U[ ν B₁ B₂ P₀ ]σ = ν body  the untyped  ν-swap′  fires on the
--   TWO ν-bound data endpoints (var 0 ↔ var 1) via  swapᵣ 1 1, landing on
--       Simg = ν (body ⋯ₚ swapᵣ 1 1).
--   To recurse with a chain-length DESCENT the engine needs  Simg  to be a STRICT
--   image  U[ P̃ ]σ  reachable in ZERO ≋-links (so the recursive chain  Simg ≋ R
--   is exactly the peeled tail).  The only P̃ whose typed relation  P ≋ P̃  is
--   provable is the typed ν-swap target  ν B₂ B₁ (P₀ ⋯ₚ swapᵣ (sum B₁)(sum B₂)),
--   and the only bridge  Simg ≋ U[ P̃ ]σ  is (the reverse of) the endpoint swap
--   composed with  U-ν-swap  (CongruenceH1) — whose  ν-swap′ core is wrapped in
--   the φ-telescope reconciliation Uν-flat / Bφ-transpose / Bφ-⋯ / leaf-U-cong.
--   That bridge is a MULTI-LINK  U.≋  chain, NOT the length-0 strict image the
--   descent demands.  `descent-fails` proves its length is  suc _  (≥ 1), so it
--   can never be ≤ 0.  Hence recognising the swapped image LENGTHENS the chain,
--   the engine has NO descent metric at ν-swap′, and route b is non-terminating
--   here — the identical failure mode as the machine-refuted reduction-TRANSPORT
--   route (RevCongStrongLE), now for the LIVE source-varying route, at the
--   image→image ν-renaming links route b specifically claimed to dodge.
--
--   (The escape generator νφ-comm′ is a DIFFERENT, already-known obstruction:
--    RevUCong.reverse-U-≋-⊥ machine-refutes the strict full reflection through it.
--    This module adds the ν-swap′/ν-comm′ image→image obstruction on top.)

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed   as TP
import BorrowedCF.Processes.Untyped as UP
open import BorrowedCF.Simulation.CongruenceH1 using (U-ν-swap)
import Relation.Binary.Construct.Closure.Equivalence as Eq*
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open Fin.Patterns

------------------------------------------------------------------------
-- Chain length of an untyped structural-congruence proof.
--   UP._≋_ = EqClosure _≋′_ = Star (SymClosure _≋′_): count its ◅ nodes.
------------------------------------------------------------------------

len : ∀ {n} {P Q : UP.Proc n} → P UP.≋ Q → ℕ
len ε        = 0
len (_ ◅ xs) = suc (len xs)

len-◅◅ : ∀ {n} {P Q R : UP.Proc n} (xs : P UP.≋ Q) (ys : Q UP.≋ R)
       → len (xs ◅◅ ys) ≡ len xs + len ys
len-◅◅ ε        ys = refl
len-◅◅ (x ◅ xs) ys = cong suc (len-◅◅ xs ys)

------------------------------------------------------------------------
-- A concrete φ-bearing image and its untyped ν-swap′ neighbour.
--   B₁ = 1 ∷ 1 ∷ []  (syncs 1  ⇒  one φ-cell inside the ν),  B₂ = [].
------------------------------------------------------------------------

B₁ B₂ : TP.BindGroup
B₁ = 1 ∷ 1 ∷ []
B₂ = []

P₀ : TP.Proc 2                        -- sum B₁ + sum B₂ + 0 = 2
P₀ = TP.⟪ ` 0F ⟫

σ₀ : 0 →ₛ 0
σ₀ ()

image : UP.Proc 0
image = U[ TP.ν B₁ B₂ P₀ ] σ₀         -- ≡ ν body  (definitional)

-- The single untyped ν-swap′ link at the image end.  `image` is ν-headed
-- definitionally, so ν-swap′ applies; the Σ names its (φ-telescoped) reduct.
swapNbr : Σ[ S ∈ UP.Proc 0 ] (image UP.≋ S)
swapNbr = _ , Eq*.return UP.ν-swap′

Simg : UP.Proc 0
Simg = proj₁ swapNbr

peeled : image UP.≋ Simg               -- the image-adjacent link the engine peels
peeled = proj₂ swapNbr

------------------------------------------------------------------------
-- The only typed recogniser: typed ν-swap.  Its untyped image-bridge is U-ν-swap.
------------------------------------------------------------------------

P̃ : TP.Proc 0
P̃ = TP.ν B₂ B₁ (P₀ TP.⋯ₚ swapᵣ (sum B₁) (sum B₂))

bridge : image UP.≋ U[ P̃ ] σ₀
bridge = U-ν-swap σ₀ {B₁} {B₂} {P₀}

-- The recogniser must certify  Simg ≋ U[ P̃ ]σ.  Its ONLY witness routes back
-- across the peeled link and forward along U-ν-swap:
recog : Simg UP.≋ U[ P̃ ] σ₀
recog = Eq*.symmetric UP._≋′_ peeled ◅◅ bridge

------------------------------------------------------------------------
-- Descent obligation vs. reality.
--   Chain-length descent at this link needs  Simg  to be a STRICT image:
--   len recog ≡ 0.  It is  suc _  instead (≥ 1), because the recogniser is a
--   non-trivial ≋-chain.  So no descent — the machine-checked roadblock.
------------------------------------------------------------------------

-- symmetric of a single-step chain is again a single ◅ (length 1).
sym-peeled-len : len (Eq*.symmetric UP._≋′_ peeled) ≡ 1
sym-peeled-len = refl

recog-len : len recog ≡ suc (len bridge)
recog-len = len-◅◅ (Eq*.symmetric UP._≋′_ peeled) bridge

descent-fails : ¬ (len recog ≤ 0)
descent-fails le rewrite recog-len = contra le
  where
    contra : ¬ (suc (len bridge) ≤ 0)
    contra ()
