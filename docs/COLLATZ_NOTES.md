# The Collatz map from the 6n−2 hub — session notes

On 2026-11-24 the Collatz (3x+1) problem was worked through in the network's
6n±1 terms, starting from Geoffrey Fischer's own diagram of the map on the
residues 6n, 6n±1, 6n±2 and 6n+3. This page records everything that session
found: the parts now proved in Lean (node
[`CollatzHub`](nodes/CollatzHub.md)), the parts measured by computer (with the
script that reproduces each number, in
[`scripts/collatz/`](../scripts/collatz/README.md)), and the parts that are
heuristic. Each item is marked:

- **Proved**: a Lean claim of `CollatzHub`, built on GitHub with the standard
  axioms only.
- **Measured**: a computer count over the stated range; true there, not proved
  beyond it.
- **Heuristic**: an argument from averages; it explains the measurements but
  is not a proof.

Nothing on this page proves the Collatz conjecture. It is stated in hub form
in `CollatzHub` as `collatz_hub_form` and never claimed. Section 13 says
exactly where the open part sits.

## 1. The diagram

Geo's diagram follows a number through its residue on division by 6, with the
parity of n deciding each arrow. Green boxes are even (the map halves them),
red boxes are odd (the map sends x to 3x + 1). Checked arrow by arrow, every
arrow is right except one pair: **the two labels leaving 6n+2 are swapped.**
6n+2 halves to 3n+1, which is 6n+1 when n is even (example: 14 → 7) and goes
back to 6n−2 when n is odd (example: 8 → 4). With the labels corrected, the
4-2-1 cycle runs through the diagram as it should (4 is 6n−2 with n = 1,
2 is 6n+2 with n = 0, 1 is 6n+1 with n = 0).

What the diagram shows (all **Proved** as stated in section 2, or immediate):

- Multiples of 3 can only appear at the start of a path: 3x + 1 is never
  divisible by 3, and halving never creates a factor of 3.
- Every odd step lands on 6n−2. This is the **hub**.
- After the first few steps every odd number is 6n−1 or 6n+1, the two columns
  of the network's wheel.

## 2. The hub map and its three loops

Follow the map from the hub value 6n−2 until it returns to the hub. There are
three loops, chosen by the index n:

| Index n | Loop | Next index | Size change |
|---|---|---|---|
| even | through the 6n−1 column (the **bad loop**) | 3n/2 | times 1.5 |
| remainder 1 on division by 4 | through 6n+2 and 6n+1 | (3n + 1)/4 | about times 0.75 |
| remainder 3 on division by 4 | through 6n+2 straight back | (n + 1)/4 | about times 0.25 |

The odd Collatz number feeding hub index n is 2n − 1 (index 14 is 27,
index 16 is 31). The 4-2-1 cycle is the fixed point n = 1. In hub form the
conjecture says every index reaches 1.

**Proved** (`hub_step_tracks_collatz`): the three loops are exactly the
Collatz map, two or three Collatz steps per loop.

## 3. Runs and exits

- **Run formula — Proved** (`run_formula`). A run of bad loops starting from
  an index with k factors of 2 (2^k times an odd number m) lasts exactly k
  loops and ends at 3^k·m. So a single run multiplies the index by (3/2)^k,
  and since k is at most the number of bits of the index, one run can raise
  an index to at most about its 1.585 power.
- **Only the bad loop climbs — Proved** (`up_only_on_bad_loop`). Every peak is
  the end of a run, an odd multiple of 3.
- **The exit — Measured, exact rule checked** (`exit_table.py`). The run's end
  3^k·m is odd, so a drop always follows. It is the times-0.75 drop when 3^k·m
  leaves remainder 1 on division by 4 (k even and m remainder 1, or k odd and
  m remainder 3), and the times-0.25 drop otherwise. The exit's remainder on
  division by 16 decides what follows the drop:

  | Exit mod 16 | Drop | Then |
  |---|---|---|
  | 1 | times 0.75 | another times-0.75 drop |
  | 5 | times 0.75 | a run of 2 or more |
  | 9 | times 0.75 | a times-0.25 drop |
  | 13 | times 0.75 | a run of exactly 1 |
  | 3 | times 0.25 | a times-0.75 drop |
  | 7 | times 0.25 | a run of exactly 1 |
  | 11 | times 0.25 | a times-0.25 drop |
  | 15 | times 0.25 | a run of 2 or more |

  Exits of every length land in every row, so a long run does not push its
  exit toward a better or worse row.
- **Exit pairing — Proved** (`exit_pairing`). An even index and its double
  exit their runs one factor of 3 apart, so one exit takes each drop. When the
  smaller one takes the times-0.75 drop, both land on the same index one loop
  after their runs end. Along a doubling chain the pairs alternate, so every
  even index merges with its half or its double. Example: indices 16 (from 31)
  and 32 (from 63) both land on 61 (Collatz value 364).
- **The pair is built into the ladder — Proved** (`pairing_is_ladder`). If a
  ladder rung leaving remainder 1 on division by 3 opens a branch entry x, the
  next rung up is divisible by 3 and opens the run entry 2x. The pair (x, 2x)
  is forced by the ladder's cycle through the remainders on division by 3.

## 4. The linking sieve (forward from each residue class)

`collatz_link_sieve.py` follows whole residue classes of the index forward
until every member provably drops below its start, or the known bits run out
(an **open** class, a problem area). Linking rules close more classes. At
depth 20 (classes modulo 3 times 2^20), **Measured**:

| Rules on | Open classes | Open share |
|---|---|---|
| residues only, modulo 2^20 | 42,318 | 4.04% |
| plus the mod-3 rule (a multiple of 3 is entered from two thirds of itself; **Proved** as `run_entry`) | 84,636 of 3·2^20 | 2.69% |
| plus coalescence with a smaller number's path | 84,256 | 2.68% |
| plus exit pairing at the start | 71,178 | 2.26% |
| plus exit pairing at every run exit along the path | 59,334 | 1.89% |

The open share keeps shrinking and never reaches zero. The open classes are
mostly short runs followed by the times-0.75 drop, chained. Coalescence closes
little because two of the three backward links lead to larger numbers
(**Proved**: `predecessors_complete`), so merging usually joins a larger path.

**Measured** (`glide_bits.py`): climbs last far longer than the starting bits
can dictate. The climb of 27 (index 14) uses 58 bits of loop decisions against
under 4 bits in its start, so later loops are decided by bits that the
multiplications by 3 create.

## 5. Chunks built backward, and meeting in the middle

- **The ladder — Proved** (`ladder_entry`, `ladder_cycle`, `rung_hub_value`).
  Every index v is entered from 4v − 1, whose hub value is 4 times that of v;
  rung i has hub value 4^i times. Rungs step down by one remainder on division
  by 3 each time, so within any three rungs there is a run entry and a branch
  entry.
- **Ladder chunks — Measured** (`ladder_chunks.py`). Growing chunks backward
  from 1, generation by generation, covers half of all indices up to 4,096 by
  generation 25, up to 16,384 by 30, up to 65,536 by 35, and up to 262,144 by
  40: about five generations for each fourfold range. 90% takes 54, 59, 66
  and 71 generations.
- **Meeting in the middle — Measured** (`meet_middle.py`). For the 2,761
  problem-area indices up to 65,536, chunks grown to generation 60 cover 85% of
  the range, the average problem index meets a chunk within 6 loops, and the
  worst total cost (generations plus loops) is lowest there: 140, against 155
  forward only and 257 backward only. Checking exit pairing and run walk-backs
  at the climbers' peaks added nothing; chunk membership already contains the
  whole path below the cap, so the climbers are limited only by their peaks.
- **Doubling chains do not close up — Measured** (`doubling_chain.py`). The
  pair merge points of one chain (m, 2m, 4m, ...) follow w → 9w − 2, but
  neighboring pairs meet only after 8 to 95 loops with no bound, so pairing
  stays local.

## 6. Climbers, peaks and mountains

- **Who climbs — Measured** (`climber_profile.py`, the 2,000 highest climbers
  among indices 1,024 to 2^20): 58% have an index divisible by 4 (25%
  overall), 34% divisible by 16 (6% overall), only 5% leave remainder 3 on
  division by 4 (25% overall), with no bias on division by 3. In ordinary
  Collatz terms: odd numbers ending in many 1 bits. 91% of their peaks are
  divisible by 9 (52% overall) and 33% are reached by runs of 6 or more (6%
  overall). They peak about a third of the way along their path (8% overall).
- **Shared peaks — Measured.** Those 2,000 climbers have only 373 distinct
  peaks; the most shared peak (index 413,685,225, Collatz value 2,482,111,348)
  is reached by 91 of them. Climbers merge on the way up.
- **The funnel trunk — Proved** (`funnel_trunk`). Every number climbing to a
  peak divisible by 3 without passing it goes through two thirds of the peak.
- **A peak's family is its backward tree below the peak — Measured exactly**
  (`shared_peaks.py`): for the eight largest families below 2^20 the forward
  count and the backward tree count agree exactly. The count itself is
  **Proved** in section 11.
- **Depth against width — Measured** (`funnels.py`,
  `funnel_width_depth.py`). Depth is measured in bits below the peak. Every
  funnel deeper than the square root of its peak is one of 27's small peaks
  (1539, 1215, 297, 117); above peak 40,000 no funnel tested goes below the
  0.518 power of its peak. For large funnels the depth is almost exactly the
  number of bits in the funnel's size (ratio 0.86 to 1.01).
- **The mountain's slope — Measured** (`mountain_slope.py`). Below every giant
  peak the number of climbers halves with each bit of depth (for peak
  4,108,012,983: 38,615, 33,606, 20,691, 11,297, 5,840, 3,033, 1,543, 739, ...).
  Mountains differ only in the size of their summit band.
- **The summit is ladder territory — Measured** (`summit_composition.py`,
  identical for five mountains from 1,373 to 116,128 members). In the band
  within a factor 2 of the peak: 54% ladder members, 33% branch members, 13%
  run members, and only 8% in exit pairs (a pair's partners are one bit
  apart, so a summit member's partner would sit above the peak). Further down
  the slope the mix settles at about half, a quarter, a quarter, matching the
  three loops' odds, with about 38% in exit pairs. A quarter of every mountain
  is in pairs.

## 7. Critical branching, and why base 3 governs the backward tree

- **The exponent — exact equation, Measured constant**
  (`critical_branching.py`). Average a value's backward tree over residues
  with the exact ladder cycle: if its size grows like the room above the value
  to the power s, then (3/2)^s = 3·(1 − 2^(−s)), solved exactly by s = 1. Tree
  size is proportional to room, with constant C between about 2.3 and 3.1 for
  roots near 2^40 and rooms from 2^4 to 2^16.
- **Why depth equals width — Measured.** A funnel's smallest member brings its
  own tree, of size about C times the room above it (ratio 0.9 to 2.3 in the
  deepest funnels), so a funnel's width is about 1.5 to 4 times the room above
  its deepest member.
- **Base 3, not base 2 — Measured** (`ternary_residues.py`, 12,000 roots).
  The root's residue modulo 2, 4 or 16 explains none of the variation in C;
  modulo 3, 9, 27, 81, 243 it explains 1.6%, 3.0%, 4.3%, 6.4%, 8.4%. Average C
  rises with the factors of 3 in the root: 1.9, 3.7, 4.9, 8.9, 10.6, 16.6 for
  0 to 5 factors. Large C always comes with a deep dip below the root, through
  repeated run entries.

So forward paths are decided by base-2 digits and backward trees by base-3
digits. The meeting of the two is where the problem is hard.

## 8. Exact links against random models

`exact_links.py` and `tail_hierarchy.py` compare real backward trees (room
2^10, roots near 2^40) with random models.

- **Measured:** a model with random residues on every rung (no exact links)
  starves 6–7% of trees; with the exact ladder cycle (which makes exit pairing
  exact) none die, and each exact ternary digit moves the median toward the
  real one (1.00, then 1.24, then 1.34 against a real 1.41 to 1.48).
- **Correction recorded.** With 4,000 trees per model it first looked as if
  real trees had fewer giants than every model. With 10,000 trees per model
  that difference disappeared: the exact ladder cycle alone reproduces the
  real tail (share with C above 10: real 4.01%, model 4.01%), and deeper
  digits change only the median.

## 9. The dip law and the n² edge

- **Measured** (`dip_law.py`). The share of backward trees that dip at least
  d bits below their root is about 17%, 3–4%, 1%, 0.3–0.5% for d = 1 to 4,
  roughly 4 times rarer per bit, and does not depend on the room.
- **Heuristic.** If each bit of dip is 4 times rarer, a funnel reaching down to
  the e-th power of its peak occurs with chance about P^(−2(1−e)) for a peak
  P, among about P peaks of that size, so about P^(2e−1) such funnels. That
  grows for e above one half and vanishes below it. The edge at e = 1/2 is a
  peak at the square of the starting number, matching the worst measured peaks
  (section 10) and the deepest funnels (section 6).

## 10. The fair game and how high numbers climb

- **Proved** (`fair_block`): any four consecutive indices starting at a
  multiple of 4 step to four indices adding up to exactly one less. On
  average over residues the loop multipliers (1.5 half the time, 0.75 and 0.25
  a quarter each) average exactly 1.
- **Heuristic with a rigorous form on residue classes.** A fair game obeys
  Doob's inequality: at most a 2^(−d) share of starts can ever climb to 2^d
  times their start. **Measured** (`climb_bound.py`, indices 2^16 to 2^20):
  the real share is about 0.4 times 2^(−d) at every d from 1 to 11.
- **Measured.** The worst peak as a power of the starting index: 1.825 for
  indices 1,024 to 4,095, 1.834 for 4,096 to 65,535, 1.929 for 65,536 to 2^20
  (index 14, the 27 orbit, reaches the 2.78 power).

A bound for every number cannot come from averages: a 2^(−d) share is never
zero, and one runaway number could sit inside every sliver. This is the same
barrier as Tao's "almost all" result.

## 11. The counting formula — Proved

`CollatzHub` proves the exact count of a mountain:

- `counting_step`: for a value below a ceiling and not on a cycle, the number
  of indices reaching it without reaching the ceiling is 1, plus that count
  for its ladder rung, plus for its run entry (two thirds of it, when it is
  divisible by 3), plus for its branch entry (when it leaves remainder 1 on
  division by 3).
- `count_zero_at_ceiling`: at or above the ceiling the count is 0.
- `ladder_sum`: unrolled up the ladder, the count is a sum over the rungs below
  the ceiling of each rung plus its run entry's or branch entry's count.
- A peak's mountain is the count for two thirds of the peak, with the peak as
  ceiling (`counting_formula_check.py`: 116,128 for peak 4,108,012,983, 52,361
  for 2,867,062,959, 7,019 for 20,168,811).

The "not on a cycle" condition cannot be dropped: 1 is its own branch entry.
Every level of the recursion asks a question about one more base-3 digit, so
the formula does not close up into a simple expression.

## 12. Where this meets the literature

| Found here | Known as |
|---|---|
| Hub map, three loops | an accelerated Collatz map; this packaging around the 6n−2 hub is original |
| Residue classes that provably drop (section 4) | Terras's stopping-time sieve; computer verifications (Barina, to 2^71) |
| Neighbors merging (section 4) | coalescence: Garner (1985), Elia and Tucker (2015), LaDue (2018) |
| Ladder chunks (section 5) | the inverse tree; Krasikov and Lagarias's lower bound on its size |
| Forward by base 2, backward by base 3 (section 7) | Lagarias and Weiss (1992), branching models modulo powers of 3 |
| C depending on the root mod 3^j; real trees narrower than models (section 8) | Applegate and Lagarias (1995) |
| Critical branching, peaks near n² (sections 7, 9) | standard predictions of those models |
| Fair game, almost all numbers behave (section 10) | Terras, Everett; Tao (2019) |
| Exit pairing as an exact rule built into the ladder, depth as the bits of width, the summit as ladder territory | not found stated this way; offered as new framings |

Sources: [Lagarias, The 3x+1 problem: an overview](https://arxiv.org/abs/2111.02635);
[Lagarias and Weiss (1992)](https://doi.org/10.1214/aoap/1177005779);
[Applegate and Lagarias, The distribution of 3x+1 trees (1995)](https://projecteuclid.org/euclid.em/1062621078);
[Garner (1985), annotated in Lagarias's bibliography](https://arxiv.org/abs/math/0309224);
[LaDue, Clusters of integers with equal total stopping times](https://arxiv.org/abs/1709.02979);
[Elia and Tucker, Consecutive integers and the Collatz conjecture](https://arxiv.org/abs/1511.09141);
[Barina, Improved verification limit (2025)](https://doi.org/10.1007/s11227-025-07337-0).

## 13. The open part, exactly

Everything structural above holds for every number. The single step that is
missing is a bound for every individual number, not for most of them. In this
page's terms, any one of these would be enough to rule out a runaway number:

- no peak's mountain has more than about the square root of the peak in
  members (equivalently, no funnel reaches below about the square root of its
  peak);
- the ladder sum of section 11 stays below about the square root of the peak
  for every peak;
- some quantity carried along every path that the base-2 and base-3 digits
  cannot keep pushing upward.

All three are open. The averages (sections 7 to 10) say the answer is yes with
room to spare; turning that into a statement about every number is the
Collatz problem itself.
