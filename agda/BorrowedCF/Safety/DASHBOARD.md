# Type safety dashboard

Generated from `dashboard/state.json` (2026-09-08 (all agents finished; final clean check running)). Open `dashboard/dashboard.html` for the live view (`dashboard/serve.sh`).

## Theorems

| name | module | status | note |
|---|---|---|---|
| preservationₚ | Safety/Preservation.agda | DONE: all 14 cases proved, no postulates; final clean check running | ChanCx Γ → Γ ; γ ⊢ₚ P → P ─→ₚ Q → Γ ; γ ⊢ₚ Q; assembled by P4 from per-rule lemmas |
| progressₚ | Safety/Progress.agda | DONE (verified): progressₚ and progress⁺ₚ, zero goals, no postulates | [] ; γ ⊢ₚ P → (P ≋ ⟪*⟫) ⊎ Blocked P ⊎ ∃ P′. P ─→ₚ P′ (closed processes, confirmed by user); wave 2 |

## Lemmas

| name | module | status | agent |
|---|---|---|---|
| Blocked / Blocked⁺ / ∈BC / ∈AC (+ decidability) | Safety/Blocked.agda | done | F |
| progress⁺ (expression progress with constant head) | Safety/Progress/Expr.agda | done | F |
| const-app-dir, stuck-arg-shape | Safety/Progress/Expr.agda | done | F |
| Plug (evaluation-position predicate), plug?, plug-⋯ᵣ(⁻¹) | Safety/Progress/Expr/Plug.agda | done | F |
| ∈BC/∈AC/Blocked transport along renamings | Safety/Blocked.agda | done | F |
| pres-Com | Safety/Preservation/Com.agda | done | P2 |
| pres-Choice (+ BindCtxInvChoice) | Safety/Preservation/Choice.agda | done | P2 |
| ≃-dual, dual-unfold, msg-cancel, com-split (dual heads of R-Com are dual msg types) | Safety/Preservation/Support/{Dual,ConsMsg,MsgSplit}.agda | done | P2 |
| pres-LSplit (+ BindCtxLsplit) | Safety/Preservation/LSplit.agda | done | P3c |
| pres-RSplit (+ BindCtxRsplit) | Safety/Preservation/RSplit.agda | done | P3b |
| pres-Acq | Safety/Preservation/Handles/Acq.agda | done | P4b |
| bindCtx-lsplit, bindCtx-rsplit (paper's BindCtxLsplit/Rsplit) + Ins/InsR/Same plumbing | Safety/Preservation/Splits/{Chain,Group}.agda | done | P3 |
| lsplit-binder / rsplit-binder (new binder context + lookups of the two new handles at the rule's positions) | Safety/Preservation/{LSplit,RSplit}.agda, Splits/Redex.agda | done | P3 |
| pres-Exp, pres-New, pres-Fork | Safety/Preservation/Basic.agda | done | P4 |
| pres-Drop, pres-Discard, pres-Close (+ bindCtx-drop, bindCtx-discard, erasure lemmas) | Safety/Preservation/Handles.agda | done | P4 |
| R-Par / R-Bind / R-Struct cases + assembly | Safety/Preservation.agda | done | P4 |
| ∈BC/∈AC ⇒ located thread; reduction under ProcessContext; single-thread redex lemmas | Safety/Progress/Redex.agda | done | G1 |
| dual heads lemma; sync redexes com/choice/close ⇒ reduction; plug-typing inversion | Safety/Progress/Sync.agda | done | G2 |
| progressₚ induction | Safety/Progress/Main.agda, Safety/Progress.agda | done | G3 |

## Agents

| id | model | task | files | state |
|---|---|---|---|---|
| F | opus | Blocked predicate (tex-exact + precise), decidability, strengthened expression progress | Safety/Blocked.agda, Safety/Progress/Expr.agda | finished |
| P2 | opus | preservation cases R-Com, R-Choice | Safety/Preservation/Com.agda, Choice.agda | finished |
| P3 | opus | preservation cases R-LSplit, R-RSplit | Safety/Preservation/LSplit.agda, RSplit.agda | finished (binder lemmas done, case assembly handed to P3b) |
| P4 | opus | preservation cases Exp/New/Fork/Drop/Acq/Discard/Close/Par/Bind/Struct + assembly | Safety/Preservation.agda, Preservation/Basic.agda, Handles.agda | finished (all cases but R-Acq; assembly done with temporary postulates for Choice/LSplit/RSplit) |
| G1 | opus | progress: single-thread process redexes ⇒ reduction exists (new/fork/lsplit/rsplit/drop/discard/acq), located-thread bridge from ∈BC/∈AC, reduction under process contexts | Safety/Progress/Redex.agda, Progress/Redex/ | finished |
| G2 | opus | progress: synchronisation redexes (com/choice/close) from two blocked heads ⇒ reduction exists; dual-head lemma; typing inversion through process contexts | Safety/Progress/Sync.agda, Progress/Sync/ | finished |
| G3 | opus | progress: main induction over the closed process with a ProcessContext (parametrised over G1/G2 lemma signatures), final theorem progressₚ | Safety/Progress.agda, Safety/Progress/Main.agda | finished |
| P3b | opus | preservation: assemble pres-LSplit / pres-RSplit from P3's binder lemmas (strengthening round trip via SplitConfine, context lemma for lwk/rwk, structure inequality, TP-Res assembly) | Safety/Preservation/LSplit.agda, RSplit.agda, Splits/ | finished (pres-RSplit done; pres-LSplit only for immobile handles) |
| P4b | opus | preservation: R-Acq — probe for a counterexample (transmute rule ∥′-tm-; loses mobility after acquire), else prove pres-Acq | Safety/Preservation/Handles/Acq.agda, AcqProbe.agda | finished (pres-Acq proved; counterexample refuted; rules audit: no fix needed) |
| P3c | opus | preservation: pres-LSplit mobile-handle case (handle alone in its group by head-¬mobile; zap + pat-hole route) and premise-free pres-LSplit; final wiring | Safety/Preservation/LSplit/, LSplit.agda (final lemma), Preservation.agda (last postulate) | finished |

## Issues found

- Toolchain: HEAD uses `_×?_` (stdlib 2.4); ~/.agda/libraries still names stdlib 2.3. Private AGDA_DIR with stdlib 2.4 used for all checks.
- Paper CT-LSplit/CT-RSplit require only ¬(S₂ ≃ Skip); Agda requires ¬ Skips of both components. Paper B-Seq/B-Drop lack the ¬skips₂ and acqHead premises of Agda's BindCtx. The looser paper rules admit the F4 deadlock probes (Simulation/BackwardSoup/Examples/Probes.agda).
- Process progress as stated (arbitrary Γ) fails for open processes: x : ret ⊢ ⟪drop x⟫ neither reduces nor is Blocked. Mechanised for closed processes.
- B-NuBlockedAcq is imprecise when both binder lists start with a separator: it declares the process blocked if ONE separator head is not acquired, even if the other one is (R-Acquire fires after C-ResSwap). Precise variant Blocked⁺ mechanised alongside; Blocked⁺ ⊆ Blocked.
- The first disjunct P ≡ ⟪*⟫ of process progress is subsumed by Blocked (B-ExpValueBlocked + B-ParBlocked).
- Existing Agda expression progress classifies (ƛ e) · v as blocked (Blocked allows any head term); paper says constant. Strengthened version progress⁺ in Safety/Progress/Expr.agda.
- Cosmetic: CT-New lists Term first in tex, Agda's `new lists end ⁇ first.
- Decisions (user, 2026-09-08): progress for closed processes is accepted; Blocked⁺ recorded as a commented block below B-NuBlockedAcq in tex/rules/blocked.tex; ~/.agda/libraries stays at stdlib 2.3 for now (private AGDA_DIR only); reviewer feedback will be added to the repo later.
- TP-Res in tex writes Γ ∥ Γ₁ ∥ Γ₂ ⊢ P; Agda orders the concrete context (Γ₁ ⸴* Γ₂) ⸴* Γ (reversed). Cosmetic (P2).
- P3: the extra ¬ Skips s₁ premise of the Agda split constants is NEEDED to re-establish AcqHeadCtx after a split (acqHead-lsplit/rsplit use it); the paper CT-LSplit/CT-RSplit must be tightened accordingly.
- F: tex B-ExpConstBlocked does not exclude the constant `unit` (Agda's Const has it); B-NuBlocked's set condition {x,y} ∩ BC(P) ≠ {x,y} mechanised as ¬(x ∈ BC × y ∈ BC); Frame carries value side conditions on directed application that the tex F[·] leaves implicit.
- P3: no typed renaming exists for the split renamings lwk/rwk (the consumed handle's slot changes type), so R-LSplit/R-RSplit need strengthening (SplitConfine) rather than renaming; Processes/Renamings.⊢wkRSplit is unusable for R-RSplit as written (keeps the old type at the shifted position). The paper's context-pattern formulation 𝒢[·] of BindCtxLsplit/Rsplit is replaced by cast-free inductive relations Same/Ins/InsR.
- Mobile on sessions: tex has Te-Acq and Te-Skips (Skip is mobile); Agda's Mobile (Types/Predicates.agda:183) has only the acq case.
- P4: tex R-Discard/R-Drop/R-Close differ in generality from Agda (Agda R-Drop drops the head of a group of any width, typing forces width 1 via bindCtx-drop; Agda R-Discard genuinely more general; R-Close realised by weaken* 2).
- G3: progress needs no first disjunct and holds for [] ; γ (every closed structure is ≈ []); a binder group [0] is untypable only because of the BindCtx/end interaction, which neither ⊢ᴮ nor the tex rules state; the acq case of progress needs typing (direction 𝟙) and is not purely structural.
- R-Acq resolved (P4b probe): Mobile ⟨acq ; t⟩ requires Bounded t, i.e. t already carries the group's terminator, and nothing may follow a terminator inside a group, so a mobile head is always ALONE in its group (head-¬mobile). The transmute rule can therefore never split a group across threads, and the feared preservation counterexample is untypable. Same fact as Crux's mobile-head-alone/group-head-¬mobile.
- G1: Agda diverges (>20 GB) on a `with` that abstracts a Canonical.agda record together with a constructor pattern (the with generalises the threadInContext index); consuming the record in a separate top-level function avoids it. R-Drop/R-Discard/R-Acq must be applied with explicit indices; E is never inferable through _[_]*. R-Par exists only for the left component (right needs R-Struct with ∥-comm).
- P2: paper R-Choice brackets ∥ as E₁ ∥ (E₂ ∥ P) while R-Com uses (E₁ ∥ E₂) ∥ P; Agda uses the left-nested form for both. Paper choice is label-indexed, Agda binary (branch returns ⟨s₁⟩ ⊕ ⟨s₂⟩). ⊢ᴮ and AcqHeadCtx have no counterpart in the paper. New session-type theory needed for Com/Choice: ≃-dual, msg-cancel, brn-cancel (absent from Types/*).
- P4b audit: no proof in the development consumes handle mobility through ∥′-tm-; (its only witnesses are UnrCx⇒MobCx); Te-Acq matters only for T-Abs's mobile-closure premise (fork/send). Making the transmute unconditional would break R-Acq preservation for real. Adding the paper's Te-Skips to Agda would let a ⟨skip⟩ head sit in a wide group and require restating mobile-head-alone.
- P3b claimed R-LSplit preservation fails for a mobile handle sharing its group with another thread's handle; REFUTED by P4b's head-¬mobile (a mobile head is alone in its group). The mobile case needs the zap/pat-hole route instead of transporting the derivation through a struct substitution (which would need Mobile of the two new handles).
- G2: the head-duality argument needed new type theory (ConsK front kinds, ≃-invariant, dual-flipped), because Types/Atoms abandoned ≃-transport of a leading brn. Paper R-Com leaves 'x,y not free in F₁,F₂,v,P' to the binder convention, Agda needs it from linearity (com-confine); R-Close has no residual so it fires only after scope extrusion (ν-ext backwards, sound by close-pair-confine). B-NuBlocked's side condition is exactly the converse of sync-redex.
- P3c: Te-Skips (Skip mobile) in the paper would also break handle-interior-¬mobile (a ⟨skip⟩ handle could sit inside a group), so the paper should drop Te-Skips or restate the group lemmas. Mobile is not decidable (quantifies over sessions modulo ≃), so case splits must be syntactic on the rule indices.
