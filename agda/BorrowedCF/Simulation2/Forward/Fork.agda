-- | Forward simulation, R-Fork.  Single untyped step RU-Fork, aligned through
--   the frame with frame-plug*.  Needs only the (drift-free) Frames machinery.
module BorrowedCF.Simulation2.Forward.Fork where

open import BorrowedCF.Simulation2.Base
import BorrowedCF.Processes.Typed             as TP
import BorrowedCF.Processes.Untyped           as UP
import BorrowedCF.Reduction.Processes.Untyped as UR
open import BorrowedCF.Simulation.Frames using (frame-plug*; frame*-⋯)

U-fork : ∀ {m n} (σ : m →ₛ n) → VSub σ
       → {E : Frame* m} {e : Tm m} (V : Value e)
       → U[ TP.⟪ E [ K `fork ·¹ e ]* ⟫ ] σ
           UR.─→ₚ U[ TP.⟪ E [ * ]* ⟫ TP.∥ TP.⟪ e ·¹ * ⟫ ] σ
U-fork σ Vσ {E} {e} V =
  subst₂ UR._─→ₚ_
    (sym (cong UP.⟪_⟫ (frame-plug* E σ Vσ)))
    (cong₂ UP._∥_ (sym (cong UP.⟪_⟫ (frame-plug* E σ Vσ))) refl)
    (UR.RU-Fork (frame*-⋯ E σ Vσ) (value-⋯ V σ Vσ))
