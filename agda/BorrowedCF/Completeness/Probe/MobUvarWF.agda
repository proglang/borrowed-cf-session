-- | The WELL-FORMED mobility instance (supervisor's objection to
--   Probe/MobUvar.agda: "nothing may come after Drop (ret), and nothing before
--   Acq").  Section 1 formalises that well-formedness as `WF`/`WFTy`; §2-§4
--   give the instance and its declarative derivation, using only WF types
--   produced by the system's own `rsplit`/`lsplit`; §5 the mobility facts;
--   §6 the ANSWER: the algorithmic system as mechanised does NOT reject the
--   term, because A-Ann re-infers the rsplit result at the SOLVED type.
module BorrowedCF.Completeness.Probe.MobUvarWF where

open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import BorrowedCF.Prelude
open import BorrowedCF.Context
open import BorrowedCF.Terms
open import BorrowedCF.Types renaming (Solved to SolvedTy)
open import BorrowedCF.Types.Unification
open import BorrowedCF.Algorithmic
open import BorrowedCF.Algorithmic.Solved

open Fin.Patterns
open Nat.Variables

------------------------------------------------------------------------
-- 1.  Well-formedness of session types.
--
--   `Core s`  : s mentions neither `acq` nor `ret`, anywhere (payloads of
--               `msg` and the branches of `brn` included).
--   `WF s`    : a Core, optionally preceded by `acq` and/or followed by `ret`
--               on the TOP-LEVEL ;-spine, plus the bare handle `ret`.
--   This is exactly "acq only as the first atom, ret only as the last, never
--   inside a payload".  The paper's session-type-formation.tex has no rule for
--   Acq/Drop at all; they arise only through rsplit, whose result shapes
--   ⟨ s ; ret ⟩ and ⟨ acq ; s′ ⟩ are the two non-Core constructors below.

mutual
  data Core {n} : 𝕊 n → Set where
    `_   : ∀ {x} → Core (` x)
    end  : Core (end {n} p)
    msg  : CoreTy T → Core (msg {n} p T)
    brn  : Core s₁ → Core s₂ → Core (brn {n} p s₁ s₂)
    mu   : Core s → Core (mu s)
    _;_  : Core s₁ → Core s₂ → Core (s₁ ; s₂)
    skip : Core (skip {n})
    ``_  : ∀ α → Core (``_ {n} α)

  data CoreTy : 𝕋 → Set where
    ⟨_⟩    : Core s → CoreTy ⟨ s ⟩
    `⊤     : CoreTy `⊤
    _⟨_⟩→_ : CoreTy T → (a : Arr) → CoreTy U → CoreTy (T ⟨ a ⟩→ U)
    _⊗⟨_⟩_ : CoreTy T → (d : Dir) → CoreTy U → CoreTy (T ⊗⟨ d ⟩ U)
    _⊕_    : CoreTy T → CoreTy U → CoreTy (T ⊕ U)

data WF {n} : 𝕊 n → Set where
  core     : Core s → WF s
  ret      : WF (ret {n})
  acq-head : Core s → WF (acq ; s)
  ret-tail : Core s → WF (s ; ret)
  acq-ret  : Core s → WF (acq ; (s ; ret))

data WFTy : 𝕋 → Set where
  ⟨_⟩    : WF s → WFTy ⟨ s ⟩
  `⊤     : WFTy `⊤
  _⟨_⟩→_ : WFTy T → (a : Arr) → WFTy U → WFTy (T ⟨ a ⟩→ U)
  _⊗⟨_⟩_ : WFTy T → (d : Dir) → WFTy U → WFTy (T ⊗⟨ d ⟩ U)
  _⊕_    : WFTy T → WFTy U → WFTy (T ⊕ U)

------------------------------------------------------------------------
-- 2.  The types of the instance, and their WF proofs.

sM sQ : 𝕊 0
sM = msg ‼ `⊤              -- !Unit
sQ = sM ; end ‼            -- !Unit ; Term

Tq  : 𝕋                    -- the λ annotation
Tq  = ⟨ sQ ⟩ ⊗⟨ L ⟩ ⟨ end ⁇ ⟩
Tx₁ : 𝕋                    -- rsplit's first  component
Tx₁ = ⟨ sM ; ret ⟩
Tx₂ : 𝕋                    -- rsplit's second component
Tx₂ = ⟨ acq ; end ‼ ⟩
Ty₁ : 𝕋                    -- lsplit's first  component
Ty₁ = ⟨ sM ⟩
Ty₂ : 𝕋                    -- lsplit's second component
Ty₂ = ⟨ ret ⟩

wf-Tq  : WFTy Tq
wf-Tq  = ⟨ core (msg `⊤ ; end) ⟩ ⊗⟨ L ⟩ ⟨ core end ⟩
wf-Tx₁ : WFTy Tx₁
wf-Tx₁ = ⟨ ret-tail (msg `⊤) ⟩
wf-Tx₂ : WFTy Tx₂
wf-Tx₂ = ⟨ acq-head end ⟩
wf-Ty₁ : WFTy Ty₁
wf-Ty₁ = ⟨ core (msg `⊤) ⟩
wf-Ty₂ : WFTy Ty₂
wf-Ty₂ = ⟨ ret ⟩

--  the algorithmic type of x₂ is WF too (α is a session placeholder)
wf-Tx₂-alg : ∀ {α} → WFTy ⟨ acq ; `` α ⟩
wf-Tx₂-alg {α} = ⟨ acq-head (`` α) ⟩

------------------------------------------------------------------------
-- 3.  The term.
--
--   λ(q : ⟨ !Unit ; Term ⟩ ⊗ᴸ ⟨ Wait ⟩).
--     let⊗ (x , z)   = q               in
--     let⊗ (x₁ , x₂) = rsplit_{!Unit} x in
--     let⊗ (y₁ , y₂) = lsplit_{!Unit} x₁ in
--       (send (unit , y₁) ; drop y₂) ; (end⁇ z ; end‼ (acq x₂))
--                                          ↑ z is used BEFORE x₂

a₀ : Arr
a₀ = record { lin = 𝟙 ; dir = 𝟙 ; mob = S ; eff = 𝕀 ; ω⇒M = λ() ; ω⇒𝟙 = λ() }

bodyE : Tm 7
bodyE = ((K `send ·¹ (* ⊗ (` 0F))) ; (K `drop ·¹ (` 1F)))
      ; ((K (`end ⁇) ·¹ (` 5F)) ; (K (`end ‼) ·¹ (K `acq ·¹ (` 3F))))

eLsplit : Tm 5
eLsplit = K (`lsplit sM) ·¹ (` 0F)

eRsplit : Tm 3
eRsplit = K (`rsplit sM) ·¹ (` 0F)

fWF : Tm 0
fWF = ƛ (`let⊗ (` 0F) `in (`let⊗ eRsplit `in (`let⊗ eLsplit `in bodyE)))

------------------------------------------------------------------------
-- 4.  Mobility facts.

mobile-x₂ : Mobile Tx₂
mobile-x₂ = ⟨ end ‼ , end , ≃-refl ⟩

--  Mobile ⟨ s ⟩ forces s to be Bounded (Bounded respects ≃ and acq ; s′ is
--  Bounded whenever s′ is).
mobile⇒bounded : Mobile ⟨ s ⟩ → Bounded s
mobile⇒bounded ⟨ s′ , B , eq ⟩ = ≃-bounded (≃-sym eq) (-;₂ B)

¬bounded-acq-uvar : ∀ {α} → ¬ Bounded (acq {0} ; `` α)
¬bounded-acq-uvar (() ;₁ _)
¬bounded-acq-uvar (-;₂ ())

--  ... so the type A-RSplit gives x₂ is NOT mobile as it stands.
¬mobile-acq-uvar : ∀ {α} → ¬ Mobile ⟨ acq {0} ; `` α ⟩
¬mobile-acq-uvar = ¬bounded-acq-uvar ∘ mobile⇒bounded

------------------------------------------------------------------------
-- 5.  The declarative derivation.  Every type it mentions is WF (§2).

Cx1 : Ctx 1
Cx1 = Tq ⸴ []

Cx3 : Ctx 3
Cx3 = ⟨ sQ ⟩ ⸴ ⟨ end ⁇ ⟩ ⸴ Cx1

Cx5 : Ctx 5
Cx5 = Tx₁ ⸴ Tx₂ ⸴ Cx3

Cx7 : Ctx 7
Cx7 = Ty₁ ⸴ Ty₂ ⸴ Cx5

app-const : ∀ {n} {Γ : Ctx n} {γ : Struct n} {c T U a ϵ} {e : Tm n} →
            (⊢c : ⊢ c ∶ T ⟨ a ⟩→ U) → Arr.eff a ≤ϵ ϵ →
            Γ ; γ ⊢ e ∶ T ∣ ϵ →
            Γ ; ([] ∥ γ) ⊢ (K c) ·¹ e ∶ U ∣ ϵ
app-const ⊢c ≤a d = T-AppUnr (constFnUnr ⊢c) ≤a (T-Conv ≃-refl ℙ≤ϵ (T-Const ⊢c)) d

¬skips-sM : ¬ Skips sM
¬skips-sM ()

¬skips-ret : ¬ Skips (ret {0})
¬skips-ret ()

¬skips-end : ¬ Skips (end {0} ‼)
¬skips-end ()

body-decl : Cx7 ; (((` 0F) ; (` 1F)) ; ((` 3F) ; (` 5F))) ⊢ bodyE ∶ `⊤ ∣ 𝕀
body-decl = T-Weaken
  (≼-refl (≈-trans (;-cong (;-cong (≈-trans ∥-unit₁ ∥-unit₁) ∥-unit₁)
                           (;-cong ∥-unit₁ (≈-trans ∥-unit₁ ∥-unit₁)))
                   (;-cong ≈-refl (;-commMob (inj₂ (` mobile-x₂))))))
  (T-Seq `⊤
    (T-Seq `⊤ (app-const (`send `⊤) 𝕀≤𝕀
                 (T-Conv ≃-refl ℙ≤ϵ (T-Pair par par (T-Const `unit) (T-Var 0F refl))))
              (app-const `drop 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Var 1F refl))))
    (T-Seq `⊤ (app-const `end 𝕀≤𝕀 (T-Conv ≃-refl ℙ≤ϵ (T-Var 5F refl)))
              (app-const `end 𝕀≤𝕀
                 (app-const `acq ℙ≤ϵ (T-Conv ≃-refl ℙ≤ϵ (T-Var 3F refl))))))

eLsplit-decl : Cx5 ; (` 0F) ⊢ eLsplit ∶ Ty₁ ⊗⟨ L ⟩ Ty₂ ∣ 𝕀
eLsplit-decl = T-Weaken (≼-refl ∥-unit₁)
  (app-const (`lsplit sM ret ¬skips-sM ¬skips-ret) ℙ≤ϵ
             (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)))

lsplit-decl : Cx5 ; (((` 0F) ∥ (` 1F)) ; (` 3F)) ⊢ (`let⊗ eLsplit `in bodyE) ∶ `⊤ ∣ 𝕀
lsplit-decl = T-Weaken
  (≼-trans (≼-refl (≈-sym ;-assoc)) (≼-cong-; ;-≼-∥ (≼-refl ≈-refl)))
  (T-LetPair seq {γ₁ = ` 0F} {γ₂ = (` 1F) ; (` 3F)} eLsplit-decl body-decl)

eRsplit-decl : Cx3 ; (` 0F) ⊢ eRsplit ∶ Tx₁ ⊗⟨ 𝟙 ⟩ Tx₂ ∣ 𝕀
eRsplit-decl = T-Weaken (≼-refl ∥-unit₁)
  (app-const (`rsplit sM (end ‼) ¬skips-sM ¬skips-end) ℙ≤ϵ
             (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)))

rsplit-decl : Cx3 ; (((` 0F) ; (` 1F)) ; []) ⊢ (`let⊗ eRsplit `in (`let⊗ eLsplit `in bodyE)) ∶ `⊤ ∣ 𝕀
rsplit-decl = T-Weaken (≼-refl (≈-sym ;-unit₂))
  (T-LetPair seq {γ₁ = ` 0F} {γ₂ = ` 1F} eRsplit-decl lsplit-decl)

decl : [] ; [] ⊢ fWF ∶ Tq ⟨ a₀ ⟩→ `⊤ ∣ ℙ
decl = T-Abs (λ()) (λ())
  (T-Weaken (≼-refl (≈-trans ;-unit₂ (≈-sym ∥-unit₂)))
    (T-LetPair seq {γ₁ = ` 0F} {γ₂ = []}
      (T-Conv ≃-refl ℙ≤ϵ (T-Var 0F refl)) rsplit-decl))

------------------------------------------------------------------------
-- 6.  The ANSWER: the mechanised algorithm does NOT reject this term.
--
--   A-RSplit invents α and infers ⟨ sM ; ret ⟩ ⊗¹ ⟨ acq ; `` α ⟩, whose second
--   component is not Mobile (¬mobile-acq-uvar).  But A-Ann/A-Check let the
--   algorithm hand that application ANY type whose C-Eq is solvable — in
--   particular the SOLVED type Tx₁ ⊗¹ Tx₂, closed by σ = UV.someSub (α ↦ end ‼).
--   A-LetPair then binds x₂ at Tx₂, which IS Mobile (mobile-x₂), and the rest of
--   the algorithmic derivation mirrors the declarative one.  So the instance is
--   a counterexample to the PAPER's algorithm (whose A-Annot needs a source
--   annotation) but NOT to the Agda `Complete⇐`.

αᵣ : UVar
αᵣ = UV.fresh 0                       -- the variable A-RSplit invents at m = 0

Uᵣ : 𝕋                                -- the type A-App actually infers
Uᵣ = ⟨ sM ; ret ⟩ ⊗⟨ 𝟙 ⟩ ⟨ acq ; `` αᵣ ⟩

¬mobile-Uᵣ-snd : ¬ Mobile ⟨ acq ; `` αᵣ ⟩
¬mobile-Uᵣ-snd = ¬mobile-acq-uvar

Δᵣ : CSet
Δᵣ = C-Eq (Tx₁ ⊗⟨ 𝟙 ⟩ Tx₂) Uᵣ ∷ C-Eq ⟨ sM ; `` αᵣ ⟩ ⟨ sQ ⟩ ∷ []

alg-rsplit : Cx3 ; (` 0F) / 0 ⊢ eRsplit ⇒ (Tx₁ ⊗⟨ 𝟙 ⟩ Tx₂) ∣ ℙ ↑ Δᵣ / 1
alg-rsplit =
  A-Ann (A-Check (A-App _ (≼-refl ∥-unit₂)
                         (A-RSplit (≼-refl ≈-refl) ¬skips-sM)
                         (A-Check (A-Var (≼-refl ≈-refl)))))

solvedΔᵣ : SolvedΔ Δᵣ UV.someSub
solvedΔᵣ = ≃-refl ∷ ≃-refl ∷ []

--  The escape is not special to this term.  A-Ann/A-Check let the algorithm
--  replace ANY inferred type by ANY σ-equivalent one, at the cost of one C-Eq:
retype : ∀ {n} {Γ : Ctx n} {γ : Struct n} {e : Tm n} {m U G ϵ Δ k} →
         Γ ; γ / m ⊢ e ⇒ U ∣ ϵ ↑ Δ / k →
         Γ ; γ / m ⊢ e ⇒ G ∣ ϵ ↑ C-Eq G U ∷ Δ / k
retype d = A-Ann (A-Check d)

retype-solved : ∀ {σ Δ U G} → subTy G σ ≃ subTy U σ → SolvedΔ Δ σ →
                SolvedΔ (C-Eq G U ∷ Δ) σ
retype-solved eq SΔ = eq ∷ SΔ

--  So no binder of the algorithmic system is ever STUCK at an unsolved type:
--  every inferred type can be traded for a solved one that σ identifies with it.
--  `alg-rsplit` above is `retype` at work on the rsplit application.
