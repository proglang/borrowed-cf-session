# TODO

## Open

- [ ] **State metatheory status accurately.** Importance: Medium. Urgency: High.
  Distinguish intended type soundness, algorithmic soundness/completeness, and
  translation simulation/bisimulation from results that are already proved or
  mechanized. Check both the introduction and related-work claims.

- [ ] **Add paper organization.** Importance: Medium. Urgency: Medium.
  Add a short organization paragraph once the final section structure is stable.

## Done

- [x] **Replace the initial placeholders.** Importance: High. Urgency: High.
  The introduction now explains protocol fidelity, binary session types, regular
  recursion, and CFSTs.

- [x] **Complete the problem statement.** Importance: High. Urgency: High.
  The introduction explains that plain CFSTs make non-tail-recursive protocols
  expressible, but still force resource-passing style and polymorphic recursion.

- [x] **Define borrowing early and concretely.** Importance: High. Urgency:
  High. The introduction explains that a borrow consumes a prefix of a session
  and leaves a residual suffix while the type discipline internalizes the linear
  channel update.

- [x] **Explain why borrowing for CFSTs differs from borrowing for regular
  session types.** Importance: High. Urgency: High. The introduction now says
  that splitting must work modulo CFST equality, including associativity,
  `Skip`, choice, and recursive unfolding.

- [x] **Preview local and remote borrowing.** Importance: High. Urgency: High.
  The introduction now explains that local borrowing follows evaluation order
  and remote borrowing needs synchronization.

- [x] **Position against BGV.** Importance: High. Urgency: Medium. The
  introduction contrasts regular vs. context-free session types, translational
  vs. direct semantics, and uniform remote-style vs. local/remote-aware borrows.

- [x] **Align the contribution list with the body.** Importance: High. Urgency:
  High. The introduction now separates core conceptual contributions from
  supporting technical contributions and includes the algorithmic and translation
  material developed in the body.

- [x] **Introduce the running examples.** Importance: Medium. Urgency: Medium.
  The introduction now previews tree serialization for local borrowing and
  streaming HTML rendering for remote borrowing.

- [x] **Normalize terminology.** Importance: Low. Urgency: Medium. The
  introduction now introduces CFSTs, `\thecalculus`, context-free session types
  with borrowing, resource-passing style, local borrowing, and remote borrowing
  before the contribution bullets.

- [x] **Decide where the tree example belongs.** Importance: Medium. Urgency:
  Medium. The introduction now gives only a short preview, while the motivation
  section carries the detailed `sendTree`/`sendTreeB` walkthrough.
