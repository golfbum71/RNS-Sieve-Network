# RNS-Sieve-Network

A readable dependency map of a Lean 4 / Mathlib formalization of a
residue-number-system (RNS) wheel sieve for primes: what is proved, what rests
on open conjectures, and how each result builds on the others.

The formalization itself runs to thousands of lines. This repository
restructures it so that nobody has to read them. Each result is a short,
plainly stated claim; the proofs sit in a separate folder, and every
connection between results is checked by Lean.

**Start here: [`GRAPH.md`](GRAPH.md)** — the network as a diagram, what each
result rests on, and what (if anything) is taken on trust. Each node also has
its own page under [`docs/nodes/`](docs/nodes/README.md).

## How it is organized

The structure follows Terence Tao's
[IEANTN](https://github.com/teorth/IEANTN) network for explicit analytic
number theory.

```
RNSNetwork/Vocabulary.lean        shared definitions only — no theorems
RNSNetwork/Nodes/<Node>/
    Conclusions.lean              the node's claims, as `def … : Prop` — no proofs
    formalization.yaml            what each claim rests on, and its evidence
RNSSolutions/<Node>.lean          the proofs
RNSSolutions/Assemble.lean        joins the proofs along the arrows
scripts/graph.py                  regenerates GRAPH.md and docs/nodes/
docs/NODE_LIST.md                 the plain-language list of all planned nodes
```

**Every arrow is its own theorem.** A proof file imports other nodes' claims,
never their proofs. When a claim rests on another node, it is proved as a
`…_step` theorem that takes the upstream claim as a named hypothesis: "if that
holds, this holds." `RNSSolutions/Assemble.lean` then plugs the finished
upstream proofs into those hypotheses, one line per arrow. So each arrow in
the graph is exactly a hypothesis Lean checked, and nothing is hidden inside
a proof.

**Open conjectures are hypotheses, never claims.** Where a result depends on
an open problem (the Hardy–Littlewood conjecture, Dickson's conjecture,
Oppermann's conjecture, …), the problem is stated precisely as a `Prop` and
taken as a named hypothesis. The graph draws it as such.

## Building

Needs [Lean 4](https://lean-lang.org) (via `elan`); the toolchain and Mathlib
version are pinned in `lean-toolchain` and `lake-manifest.json`.

```
lake exe cache get        # download prebuilt Mathlib (first time only)
lake build                # the claims and Vocabulary — fast, no proofs
lake build RNSSolutions   # the proofs; prints `#print axioms` for each
```

Every proof should report only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Regenerating the graph

```
pip install pyyaml
python scripts/graph.py
```

`GRAPH.md` and `docs/nodes/` are generated from the `formalization.yaml` files
and the claims in each `Conclusions.lean`. Edit those and re-run; never edit
the generated pages by hand.

## Related

[`HardyLittlewood`](https://github.com/golfbum71/HardyLittlewood) packages the
singular-series results of this network as a single Comparator-ready
challenge and solution.

## License

Apache 2.0 — see [`LICENSE`](LICENSE).
