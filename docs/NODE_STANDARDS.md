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
- A node that is related to another in content (same objects, a sharper or
  more special statement, the other side of the same definition) but does not
  take its result as a hypothesis lists it under `related:` in its
  `formalization.yaml`, each entry with a `node:` and a `note:` saying how.
  These show on the node page as "Related nodes", never as arrows: an arrow
  always means a hypothesis Lean checked. A node with no arrows in or out must
  have at least one `related:` entry or say in its description why it stands
  alone.
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
  or specializes an earlier node, an `improves:` line under `node:` in its
  `formalization.yaml` says what it adds (shown on the page as "What it
  adds"): a stronger
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
      `Assemble.lean` (so the arrow is drawn); content links without a
      hypothesis are `related:` entries.
- [ ] Sources with links for anything not original; original work says so.
- [ ] `python scripts/graph.py` rerun; the node page reads correctly.
- [ ] Built clean on GitHub with only the standard three axioms.

## Where the network stands

**Audit of 2026-11-05, after fixes:** all 54 nodes have a description, at
least one published source, and either an arrow or a `related:` entry. No
proof uses another node's claims without an arrow.

What was fixed that day:

- **19 nodes had no arrows in or out.** None of them takes another node's
  result as a hypothesis, so no arrow was added; each now lists its related
  nodes with a note on how (for example `KanoldBound` → `BlockingRuns`,
  `LongGaps` → `BlockingRuns`, `InadmissibleOccurrences` → `Admissibility`).
  `ColumnAction` and `ColumnStructure` state the same column fact in two
  forms, each proved in three lines; they are cross-referenced rather than
  joined. `LongGaps` should gain a real arrow from `BlockingRuns` once the
  outside result is cited.
- **15 nodes had no published source.** Standard facts now cite a reference
  (Wikipedia or the classical paper); the three outside-source nodes now list
  their Lean project. `SophieGermainWheel`'s source states the facts modulo 3
  and modulo 20, and its entry says so.
- **`DirichletColumns` had no description;** it has one.
- **`graph.py`** now prints `improves:` as "What it adds" and `related:` as a
  "Related nodes" section on each node page.

Re-run the audit after adding a node: every node needs a description, a
source unless original, and an arrow or a related entry.
