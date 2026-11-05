# Node standards — what every node must show

A reader who clicks a node on [`GRAPH.md`](../GRAPH.md) should see, before
opening any Lean, what the node is, what it adds to the nodes it builds on,
and where the mathematics comes from. These rules apply to every node, new or
existing. Node pages under [`docs/nodes/`](nodes/README.md) are generated from
each node's `formalization.yaml` by `python scripts/graph.py`, so every rule
below is met by filling in the metadata, never by editing a generated page.

## 1. Arrows: when one node leads to another, the graph shows it

- If a claim uses another node's result, the proof must take that result as a
  named hypothesis (a `…_step` theorem), the claim's `imports:` must list it,
  and `RNSSolutions/Assemble.lean` must join the two. That is what draws the
  arrow; nothing else does.
- Do not re-prove another node's result inside a proof file to avoid the
  arrow. If a node re-derives something another node already proves, either
  switch to importing it or say in the node's notes why it stands alone.
- A node that is conceptually a sequel to another (same objects, a sharper or
  more special statement) but does not use its result should still say so in
  its description, naming the earlier node, so the relation is visible even
  without an arrow.
- For planned nodes, `planned: rests_on:` lists the nodes it will rest on, so
  the dashed arrows are right before any Lean exists.

## 2. A note on what the node is and what it does

- `node: description:` — two to five plain sentences: what the node proves,
  in the network's words (wheels, survivors, cycle, ceiling), and the standard
  name of the result where there is one. This is the first thing on the node
  page.
- Each claim's `summary:` — one sentence saying what that claim states, so the
  reader knows what the Lean `def` beside it means before reading it.
- **What is new over the node it builds on.** When a node rests on, sharpens
  or specializes an earlier node, its description (or a separate
  `improves:` line once `graph.py` supports it) says what it adds: a stronger
  bound, a general case of a special one, a new direction (backward runs, the
  other column), a certificate where there was only a statement. Skip this
  only when the description already makes it obvious.
- If a claim is a disproof or settles only part of a conjecture, the summary
  says exactly which part (for example `GapCertificate` refutes Erdős's guess
  for the wheels up to 13, not his "large enough cycles" form).

## 3. Links to the source when the work is not original

- Every result that is not new to this project lists its published source
  under `sources:` with a `url:` and a `relationship:` saying how the node
  relates to it (proves it, restates it, follows its proof, records its
  data, states the conjecture it refutes).
- This includes standard textbook facts (the Chinese Remainder Theorem,
  periodicity of residues): cite a standard reference rather than leaving the
  list empty.
- Results taken from another Lean project are outside-source nodes and link
  to that project's proof.
- Original work says so in its description, so a missing source list reads as
  "new here", not as "forgot to cite".

## 4. The reader's path to the Lean

Each generated node page already gives, in order: status, description,
published sources, each claim with its summary and Lean statement, what each
claim rests on (with links), where its proof lives, which nodes use it, and
the node's files. Keep the metadata complete enough that this page answers
"what will I find in the Lean code?" without opening it.

## 5. Checklist before marking a node built

- [ ] `description:` says what the node is, in plain words, and names the
      classical result if there is one.
- [ ] Every claim has a one-sentence `summary:`.
- [ ] What it adds over the node it builds on is stated, if not obvious.
- [ ] Every input from another node is an `imports:` entry and a line in
      `Assemble.lean` (so the arrow is drawn).
- [ ] Sources with links for anything not original; original work says so.
- [ ] `python scripts/graph.py` rerun; the node page reads correctly.
- [ ] Built clean on GitHub with only the standard three axioms.

## Where the network stands (audit of 2026-11-05)

Checked across all 54 nodes. No proof file uses another node's claims without
an arrow, so no drawn arrow is missing outright. Still to fix:

- **No arrows in or out (19 nodes).** Some genuinely stand alone; each should
  either gain the arrow it deserves or say why it stands alone:
  `BrunTwinSum`, `ColumnAction`, `DirichletColumns`, `DudekJohnston`,
  `GallagherAverage`, `GapCertificate`, `GapConjectures` (rests only on open
  conjectures), `GapMoments`, `HensleyRichards`, `InadmissibleOccurrences`
  (the node list says it builds on `Admissibility`), `Infinitude`,
  `KanoldBound`, `LinearForms`, `LongGaps` (should rest on `BlockingRuns`),
  `MenonIdentity`, `PillaiBrauer`, `PrimeGapsBridge` (relates to
  `Admissibility`), `RamanujanSums`, `RoughInPrimeGaps`.
- **No published source (15 nodes).** Standard facts need a textbook or
  reference link; outside-source nodes need their project link in
  `sources:`: `CRT`, `CeilingOvershoot`, `ColumnAction`, `ColumnStructure`,
  `GapConjectures`, `GapTracks`, `JacobsthalQuadratic`, `MertensThird`,
  `PrimeNumberTheorem`, `ShareBounds`, `SophieGermainWheel`,
  `SquareRootShield`, `SurvivorCount`, `Wheel6`, `WheelOrder`.
- **No description (1 node):** `DirichletColumns`.
- **No "what is new" field yet.** Add an optional `improves:` line to
  `formalization.yaml` and have `graph.py` print it under the description.
