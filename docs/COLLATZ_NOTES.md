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

## 14. The rising tide (added later the same day)

Geo's picture: go up the numbers in order and treat everything already settled
as under water. `rising_tide.py` makes the flood exact: it is every value on
the path of any smaller index, so it reaches far above the tide line. When the
tide reaches an index, follow it only until its path touches the flood.

**Measured** for every hub index up to 2^20:

| When the tide arrives, the index is… | Share |
|---|---|
| already wet (a smaller index's path ran through it) | 48.3% |
| dry, but drops straight into the flood without climbing | 25.8% |
| dry, climbs, and meets the flood below its own peak | 0.8% |
| dry, and must climb all the way to its peak first | 25.05% |

On average an index reaches the flood in 1.6 loops (3.5 loops to drop below
its own start). The flood holds 1.7 million values.

What formulas fill with no climbing at all (**Proved**): every odd index
above 1 drops below itself in one loop (`up_only_on_bad_loop`), and every
multiple of 3 is entered from two thirds of itself, a smaller number
(`run_entry`). Together that is two thirds of the number line.

**The pioneers.** The hardest dry indices are the smallest members of giant
mountains: 79,744 must climb 35,953 times its size, 135,136 must climb 30,399
times (the bottoms of the mountains of peaks 2,867,062,959 and 4,108,012,983).
This is forced: if any smaller number had touched the smallest member's climb,
that smaller number would follow the same climb to the same peak and be the
smallest member instead. So a mountain's smallest member, its **pioneer**, can
never meet the flood before the peak, and every other member then joins the
pioneer's trunk below the peak. The rising tide therefore comes down to one
question per mountain: how far below its peak its pioneer sits, which is the
funnel-depth question of sections 6 and 9.

In optimization terms the rising tide is a sublevel-set filtration, the
picture of basins joining as the level rises is a merge tree (a
disconnectivity graph for energy landscapes), and the pioneers are where new
branches of the merge tree start.

## 15. Searching for a Lyapunov score (added later the same day)

Convergence proofs in optimization use a Lyapunov (potential) score that goes
down every step even when the raw value goes up. `lyapunov_search.py` tried
the family: size in bits, plus a credit for each factor of 2 (pre-paying a
run), plus a credit for each factor of 3 (crediting run entries), over every
hub index up to 2^18, block by block (one run plus the drop that ends it).

**Measured:** the credits raise the share of indices whose score drops in one
block from 71.9% to 81.2%, but the worst case never moves: every one of the 35
scores tried still needs 44 or 45 blocks for the hardest indices (135,136 and
180,181, mountain pioneers).

**Why this family cannot work (measured fact, simple reason):** after any drop
the next run's length is fresh, with share exactly one half, a quarter, an
eighth, ... for runs of 0, 1, 2, ..., whatever came before. A score built from
size plus finitely many counts or low digits can be beaten by the next block;
during a run longer than the digits it reads, the size grows by half each loop
while the score's correction cannot keep up. A working score would have to
read an unlimited amount of a number's digits in a way that anticipates the
whole climb, which is the open problem again, stated as a requirement on any
proof.

## 16. Smaller peaks inside a mountain (added later the same day)

A smaller peak inside a mountain is a member where a run ends. Its run entry
(two thirds of it) is smaller and steps straight onto it, so it is always a
member too, and each smaller peak's own sub-mountain lies inside the big one:
mountains nest.

- **Proved** (`sub_peak_rule`): a member ends a run inside the mountain exactly
  when it leaves remainder 3 on division by 6.
- **Measured** (`sub_peaks.py`): in every giant mountain, members split by
  remainder on division by 6 as 1/9 for each even remainder and 2/9 for each
  odd one. So smaller peaks are 2/9 of a mountain, one per 4.5 members:

  | Peak | Size | Smaller peaks | Members per smaller peak |
  |---|---|---|---|
  | 4,108,012,983 | 116,128 | 25,845 | 4.49 |
  | 2,867,062,959 | 52,361 | 11,598 | 4.51 |
  | 413,685,225 | 34,497 | 7,677 | 4.49 |
  | 261,804,123 | 15,513 | 3,435 | 4.52 |
  | 20,168,811 | 7,019 | 1,535 | 4.57 |
  | 1,358,937 | 1,373 | 299 | 4.59 |

  300 random small mountains near 2^30 give 4.7 to 5.0, closing in on 4.5 as
  they grow.
- **Measured: how they nest.** Most smaller peaks have only 1 to 3 members
  below them. For sub-mountains of 4 to 64 members, each sixteen times larger
  size is about 80 to 100 times rarer. At the top, nearly every giant mountain
  has one or two foothills holding about a third of it (45,573 of 116,128;
  12,054 of 34,497; 5,089 of 15,513; 2,694 of 7,019), each with its own
  foothills inside; the mountain of peak 2,867,062,959 is the exception (its
  largest foothill is 8%).

The 2/9 rule fixes how many peaks a mountain has; how their sizes nest is what
decides how deep its pioneer can sit, and that part is not proved.

## 17. Pioneers and their staircase (added later the same day)

- **Where the numbers between a run start and its peak belong — Measured**
  (`interval_owners.py`). Every number has exactly one highest point, so the
  number line splits into mountains with no overlaps; a number with no home
  would be a runaway. Between a trunk run's start and its peak, only 0.08% to
  0.3% of the numbers climb to that peak (942 of 1,090,506 for peak 1,358,937);
  about half go on to higher peaks, about half top out lower, and 28.7% are
  their own peak (they never rise above themselves). A mountain also reaches
  below its run start: 431 of that mountain's 1,373 climbers start below it.
- **The pioneer keeps its title up its staircase — Measured, with a simple
  reason** (`pioneer_staircase.py`). The pioneer of a giant mountain is the
  pioneer of exactly those smaller peaks on its climb that set a new high (13
  of the 22 peaks on the climb of 135,136; 8 of 11 for 56,692; all 8 for
  15,956): it is in each such sub-mountain and nothing in it is lower. Peaks on
  its climb that are not new highs, and every foothill off the staircase, have
  their own pioneers, and those only climb to where they join the trunk.
- **No interception below the peak.** Every value on a pioneer's climb reaches
  1 only through the rest of the pioneer's own path, over its peak, and nothing
  smaller touches the climb before the peak (otherwise that smaller number
  would be the pioneer). So a pioneer's cost is exactly its peak; hand-offs
  happen only sideways and after the peak.
- **Exact:** every ladder rung above the start is odd and the rungs cycle
  through the remainders on division by 3 (`ladder_cycle`), so every third rung
  is a smaller peak; which rung starts the pattern is set by the start's
  remainder on division by 3.
- **Measured** (`pioneer_staircase.py`): about 2% of the smaller peaks in each
  one-bit band below a giant peak have 16 or more members, at every depth; the
  largest foothills sit 1 to 2 bits below the summit.
- **Favors — Measured** (`mountain_favors.py`): crediting each number to the
  earlier path it first links into, owners whose own climb went over a
  thousandfold link about 9 later numbers each, owners with climbs under
  twofold about 1; small climbs still do 83% of all linking up to 2^20.

## 18. How pioneers thin out (added later the same day)

**Measured** (`pioneer_density.py`, hub indices up to 2^22): pioneers are
exactly a quarter of every doubling block (0.250 to 0.253), mostly trivial.
Pioneers whose peak reaches the c-th power of their start grow per doubling
block by about 2^(2−c): 1.65 times per block for c = 1.25 (predicted 1.68),
1.40 for c = 1.5 (predicted 1.41), barely at all for c = 1.75. So pioneers
reaching the square come at a steady rate, and those reaching beyond it thin
out so fast that their total is finite on average (**Heuristic**). Like the
density of primes, this says nothing about a single exceptional number.

## 19. Assuming a runaway (added later the same day)

- **Proved by contradiction (simple):** either there are infinitely many
  pioneers or some pioneer runs away. (The peaks 3, 9, 27, ... each have a
  mountain with a pioneer; finitely many pioneers would force one to pass
  through infinitely many ever-higher powers of 3.)
- **A smallest runaway R** would be even, not a multiple of 3, in an open sieve
  class at every depth, dry forever; bad loops at least 41.5% of its loops (and,
  if they keep their usual half share, the double-divide drop under about 5.4%
  instead of 25%); the pioneer of an endless staircase of record peaks. So
  **if every mountain's pioneer is at least a fixed power of its peak (any
  power, even 0.01), no runaway exists.**
- **Why "all numbers become runaways past some point" is impossible:** a
  number has one path, so 1's tree and a runaway's tree never share a number,
  and 1's own ladder (1, 3, 11, 43, 171, ...) and the ladders of all numbers
  verified below 2^71 reach above every point.
- **Correction recorded.** During the session it was claimed that the density
  results (Terras, Tao) make the runaway set a vanishing share. That is wrong:
  a number can dip below its start and still run away later, so those results
  do not reach the numbers with unbounded paths (see
  [arXiv 2208.11801](https://arxiv.org/abs/2208.11801), section 4).
- **What a runaway's mountains would look like — Heuristic, from measured
  sizes.** Real mountains hold about 1.5 to 4 times peak ÷ pioneer members, so
  a runaway's mountains would keep a fixed share, about 2.5 ÷ R, of all numbers
  below each new peak (about 2/9 of them foothill peaks), while every ordinary
  pioneer's share fades. Two statements together would exclude it: every
  backward tree keeps a fixed share of the numbers below its ceiling, and 1's
  tree holds a share going to 100%. Neither is proved.

## 20. Covering the escape routes (added later the same day)

- **Measured** (`escape_cover.py`): following only the loops each problem-area
  member's digits force (sieve depth 8 to 20, members up to 2^20), the forced
  stretch lands on 1's tree grown to 16 times the range for 76.5% to 87.4% of
  members, and grown to 64 times for 92.3% to 97.0%; every miss is a member
  whose connecting branch rises above the cap.
- **Measured** (`cover_height.py`, members up to 2^24): the height 1's tree must
  reach, as a power of the member, has median 1.12 to 1.15 and 99th percentile
  1.39 to 1.46 (creeping up slowly with depth); the hardest member of each size
  from 1,024 up needs 1.76 to 1.99 (3,315,838 needs 1.994). 1's tree is
  infinite; the power is how high the branch connecting a member to 1 climbs.

## 21. A floor for every backward tree (added later the same day)

`tree_floor.py`: on every ladder, whatever its digits, a branch entry rung is
followed by a run entry rung once every three rungs (**Proved** facts:
`ladder_cycle`, `pairing_is_ladder`). Letting an adversary choose the worst
remainders everywhere gives a tree no real tree can fall below; it grows like
the room to the power **0.437** (**Computed**, a proof in principle; the
adversary calculation is not formalized). This lands on the first classic
bound, Krasikov's x^(3/7) of 1989; Wirsching reached x^0.48, Applegate and
Lagarias x^0.81, Krasikov and Lagarias x^0.84 by making more remainder digits
exact. One more exact digit (division by 9) raises the floor slightly here
(0.44 to 0.46 over a short range). Even x^(1−ε) is a vanishing share, so this
route does not by itself give the fixed share section 19 needs.

## 22. What digits make a climber (added later the same day)

- **Engineered climbs — Proved in essence:** a bad loop uses one binary digit
  and multiplies by exactly 1.5; a drop uses two and never raises the index. So
  from its own digits an index climbs at most by 1.5 per digit: the best is a
  single pure run from 2^b to 3^b, about the 1.585 power.
- **Record climbs go beyond their own digits — Measured**
  (`engineered_vs_records.py`): 79,744 climbs n^0.38 while reading its own
  digits and n^0.55 after they ran out; 3,315,838 climbs n^0.23 then n^0.76.
- **The binary code — Measured** (`climber_digits.py`, top 0.1% of climbers
  among Collatz numbers 2.1 to 4.2 million): at least 80% binary ones ×8.9,
  six or more trailing ones ×8.4, a block of eight or more ones anywhere ×5.0;
  remainders on division by 3, 9, 27, 5, 7 and base-3 digits show nothing.
- **Reproducible — Measured** (`dense_ones.py`, 48-bit numbers ending in binary
  01): with 95% ones, 27.7% reach the 1.3 power of their start (0.02% for
  random digits) and 11.8% the 1.5 power. Blocks of ones are stored runs: each
  launches a run when it reaches the bottom of the number. That climb is
  entirely paid for by the number's own digits (9.2 bits while reading them,
  0.16 after).

## 23. How record climbs use the loops (added later the same day)

**Measured** (`climb_loops.py`, top 200 climbers among hub indices 2^20 to
2^21): bad loops 74% to 77% (52% on ordinary paths), the double-divide drop 5%
to 8% (24% ordinary), runs of 6 or more 13% to 17% of runs (1% ordinary), and
after a run the gentle drop 72% to 77% (50% ordinary). The part after a
climber's own digits run out has the same signature as the part read from
them. Two of the three loops multiply by 3 and so write new digits; only the
double-divide drop writes nothing, and record climbs avoid it.

## 24. The steps of the staircase (added later the same day)

**Measured** (`staircase_steps.py`, every hub index from 2^18 to 2^19, 137,175
records later beaten and 186,690 final peaks): whether a record peak is beaten
again is decided by its remainder on division by 16, not by the run that
reached it or its extra factors of 3:

| Peak mod 16 | Share of beaten records | Share of final peaks |
|---|---|---|
| 5 | 29.6% | 0.0% |
| 13 | 29.3% | 0.0% |
| 1 | 13.2% | 11.9% |
| 15 | 12.9% | 12.5% |
| 3, 7, 9 | 4.4% to 4.7% each | about 18% each |
| 11 | 1.6% | 20.6% |

- **Proved** (`free_step`): a peak leaving remainder 5 on division by 16 reaches
  27/16 of itself three loops later (a three-quarter drop, then two bad loops),
  and one leaving remainder 13 reaches 18/16 of itself two loops later. So
  these are never final peaks: the free steps of the staircase.
- 70% of final peaks are followed directly by the double-divide drop. Valleys
  that recover are mostly shallow (68% within 1 bit) and usually restart with
  a run of 1 (61%).
- **Link to the climb before:** a peak is 3^k·m, so its remainder on division
  by 16 is fixed by the run length k (through 3^k, which repeats every 4) and
  the four binary digits of m just above the run in the run's starting number.
  What lets a climb reach the next level is coded in those four digits, read
  through 3^k; about a quarter of run exits land on a free step.

## 25. Blocks of ones in the row number (Nov 26)

Label: **proved** (Lean: `block_handoff`, `block_chain`, `block_of_ones_drops`), checked against real paths.

Look at a 6n+1 number in a row where n ends in a 0 followed by a block of binary ones, so n + 1 is a power of 2 times an odd number. When the block has at least three ones, five steps (up, halve, up, halve, halve) land on the 6n+1 number of another row. That row's n + 1 is exactly nine eighths of the old one, so its block is three ones shorter. Repeating this, a block is handed down three ones at a time, growing by 9/8 per hand-off. It is a second, slower climbing mode: about 1.125 per three digits, against 1.5 per digit for the 6n−1 bad loop.

Once fewer than three ones are left there is a fixed finish. With two ones left it drops to (27M − 5)/2, where M is 9 to the number of hand-offs times the odd part. With none left it drops to (9M − 7)/2. That finish is below the starting number for every row whose block has 2, 3, 5, 6, 8, 11 or 14 ones, whatever the higher digits are. From 17 ones on (and 9, 12, … in the no-ones-left case) the 9/8 growth outlasts the finish, so the block alone does not settle the row.

Correction: before this was checked, I said that every block of 3t + 2 ones drops right after its runs of 2. That holds only up to 14 ones.

Checked: every number below 3 million that the rule settles (106,583 of them) reaches the predicted value and is below its start. The ledger page marks these rows with the Block of ones rule and shows the hand-off chain in the run readout.

## 26. Pioneer, peak and tide (Nov 27)

For each pioneer (odd, the smallest number whose path tops out at a given highest odd value, with that value above it) three markers: the pioneer, the peak, and the tide, the first value below the pioneer. From there on the path is among numbers already settled. Table: the "Collatz Pioneers" Sheet (all 10,880 below 100,000) and `scripts/collatz/pioneer_markers.py` (all 108,880 below 1,000,000).

**Peak signature (proved).** Write the pioneer as 2^j · m − 1 (j trailing binary ones, m odd). The top of its first climb is 2 · 3^(j−1) · m − 1, so in ternary it ends in at least j − 1 twos. It ends in exactly j − 1 when m is not a multiple of 3, and m always isn't for a pioneer: otherwise the pioneer leaves remainder 2 on division by 3, and such a number is entered from the smaller number two thirds of its double, less a third. Checked: all 78,440 pioneers whose peak is the first climb's top. The binary ones at the start become ternary twos at the top.

**Second climbs (5 and 13 proved; the rest measured).** The exit index 3^(j−1) · m on division by 16 sorts the pioneers. 5 or 13: always climbs above the first peak (the free-step rule, Lean `free_step`), 27,941 pioneers. 3, 7, 11 or 15: never climbs above it in the data (54,642 pioneers), but this is not proved. 1 or 9: either; with more digits, more are settled (on division by 1024 about two thirds are decided). 151 of the 158 pioneers whose peak is above the pioneer to the power 1.5 climb again after the first climb.

**The tide.** Count u odd steps and k halvings from the pioneer. The value is above 3^u / 2^k times the pioneer, so:
- (proved) the tide never comes while 3^u is at least 2^k;
- (proved) the tide comes right after a halving, since an odd step only makes the number larger;
- (measured, every pioneer below 1,000,000) it comes with the balance k − 1.585 u between 0 and 1 bit, and tide ÷ pioneer is within 0.002 of 2 to the minus balance. That the tide always comes at the first moment 3^u falls below 2^k is Terras's coefficient stopping time conjecture (1976), open.

**Debt from the top.** At the peak the path owes a debt in bits: 1.585 × (odd steps up) − (halvings up), about log2(peak ÷ pioneer). On the way down each odd step adds 1.585 to the debt and each halving pays off 1, and the tide comes when the debt is first paid. So steps down and odd steps down are tied to the debt at the peak, not separate facts. Examples from a first-climb peak: with two trailing ones the debt is about 0.585 bits. A steep exit (three halvings after the odd step, paying 1.415) reaches the tide at once: every pioneer leaving remainder 3 on division by 16 meets the tide at (9x + 5)/16 four steps after its peak. A gentle exit (two halvings, paying 0.415) needs a second drop: remainder 11 on division by 32 meets it at (27x + 23)/32. Every halving count on the way down is read from the binary digits of the number reached, so the whole trip to the tide is fixed by the pioneer's last digits (the row-pattern rule, seen from the top).

**Not a digit rule: being a pioneer.** No ending of up to 14 binary digits makes a number always a pioneer, and a growing number of endings never are. Being a pioneer depends on every smaller number. A pioneer's last ternary digit is never 2.

## 27. One-drop mountains (Nov 27)

Label: **proved** (Lean: `climb_formula`, `halving_formula`, `one_drop_tide`), checked both ways by `scripts/collatz/one_drop.py`.

Take an odd number with j trailing binary ones, written 2^j · m − 1. Its climb is forced: j climbs (up, halve) in 2j steps reach 3^j · m − 1, with no choices along the way. What happens next is one drop of some number of halvings. Let h be the fewest halvings that outweigh the climb (the smallest h with 3^j below 2^(j+h)): 1, 2, 2, 3, 3, 4, 5, 5, 6, 6, 7, 8, … for j = 1, 2, 3, …

- If the last h binary digits of m are the last h digits of the 2-adic number 1/3^j, the top 3^j · m − 1 is divisible by 2^h, so the drop has at least h halvings, and after exactly 2j + h steps the number is (3^j · m − 1)/2^h, below its start. The mountain meets the tide in a single drop.
- If they are not, the drop has fewer than h halvings and lands above the start (the climb outweighs it), so it does not meet the tide in one drop.

(For a handful of the smallest m the halvings do not quite outweigh the "−1"s; the Lean statement carries the exact condition 3^j · m + 2^h ≤ 2^(j+h) · m.)

The endings form a repeating pattern, not a list to be searched: the 2-adic digits of 1/3^j repeat, after the first, every 2 · 3^(j−1) digits. For j = 1 they are …10101011: the same alternating 1, 0 that sets the first run in the row patterns of the 6n+1 column. The digits m must end in for j = 1 to 8: 1, 01, 11, 001, 011, 1001, 00011, 00001.

Examples. j = 1 is the rule for remainder 1 on division by 4. j = 2 (m ending in 01) is the family x ≡ 3 mod 16 with tide (9x + 5)/16 from section 26. j = 3 (m ending in 11) gives x ≡ 23 mod 32 with tide (27x + 19)/32 after 8 steps.

What this gives the tide program: every climb length has its own exact one-drop class, a fixed share 2^(−h) of the numbers with that many trailing ones, read from the number with no looking ahead, for climbs of any length. Two-drop mountains are the same construction one level up: after the first drop the number reached has its own trailing ones and its own class.

## 28. Mountain types and the bases that fit them (Nov 27)

Script: `scripts/collatz/mountain_types.py` (every odd number below 2^22).

**Which base.** Powers of 2 decide what a number does next (each halving reads one binary digit). Powers of 3 record what it has done (each odd step multiplies by 3). Base 6 fixes only the last digit: every peak ends in 5 in base 6, because every peak is a 6n−1 number. Base 16 decides the first two moves after a top (the exit table). No fixed base is enough: a trip with u odd steps reads about 2.6 u binary digits. The language in which the patterns repeat is binary digits of fractions whose denominators are powers of 3.

**Mountain types.** Write a trip to the tide as blocks "climb j, drop d" (j odd steps with single halvings between, then d halvings). Each type of trip is exactly one ending of binary digits, and that ending is the 2-adic digits of a fraction whose denominator is 3 to the number of odd steps, so it repeats (Terras 1976; the one-drop types are section 27). With 3 to 5 odd steps:

- 3: climb 3 drop 3 (ending 10111); climb 2 drop 2, climb 1 drop 2 (01011)
- 4: climb 4 drop 4 (0001111); climb 3 drop 2, climb 1 drop 3 (0000111); climb 2 drop 2, climb 2 drop 3 (0111011)
- 5: climb 5 drop 4 (01011111); climb 4 drop 3, climb 1 drop 2 (01001111); climb 4 drop 2, climb 1 drop 3 (10101111); climb 3 drop 2, climb 2 drop 3 (00100111); climb 3 drop 2, climb 1 drop 2, climb 1 drop 2 (11000111); climb 2 drop 2, climb 3 drop 3 (11011011); climb 2 drop 2, climb 2 drop 2, climb 1 drop 2 (01111011)

The number of types for 1, 2, 3, … odd steps is 1, 1, 2, 3, 7, 12, 30, 85, 173, 476: OEIS A100982. Mike Winkler (arXiv 1504.00212, 1709.03385) gives a recursive tree that generates them. So this level is known; our block language and the one-drop family (section 27, in Lean) are a slice of it in Geo's terms.

**Time to the tide is quantized.** Every odd number below 2^22 meets the tide after exactly u + ⌊u · log2 3⌋ + 1 steps, where u is its number of odd steps: 3, 6, 8, 11, 13, 16, 19, 21, 24, 26, … (OEIS A020914). The tide cannot come sooner (proved, section 26); that it never comes later is Terras's coefficient stopping time conjecture, open.

## 29. Building a mountain block by block (Nov 27)

Label: **proved** (Lean: `block_step`, `block_landing`, `block_ending_lift`, `two_blocks`).

A mountain is a chain of blocks, each "climb j, drop d". Four facts make the chain exact:

1. **One block.** From 2^j · m − 1 the climb is forced to 3^j · m − 1; if that top is 2^d times a number c, the drop of d halvings lands on c. Steps: 2j + d.
2. **Where it lands.** The landing point is the start of the next block, a number 2^(j₂) · m₂ − 1 with j₂ trailing ones, exactly when 3^j · m + 2^d = 2^(d + j₂) · m₂ + 1.
3. **The ending is built from the previous one.** Two starts satisfying the same block equation agree in their last D + t binary digits (D = d + j₂) exactly when their landing points agree in their last t. So the binary ending of a whole mountain type is: the first block's D digits (fixed by the block), then the next block's ending carried back through the block, digit for digit. Nothing is lost and nothing is left free, because multiplying by 3 can be undone on binary digits (3 is odd).
4. **Blocks compose.** The steps add, and the second block starts where the first lands.

Together: every mountain type, however many blocks, has exactly one binary ending, of length the total halvings, assembled block by block. Section 28's table is what this produces for 3 to 5 odd steps; the counts are OEIS A100982 (Winkler's tree builds the same classes). The question left open is whether a chain of blocks that never reaches the tide can exist: by fact 3 it would be a whole number whose binary digits match an endless chain of block endings, and ruling that out for every whole number is the conjecture itself.

## 30. The cycle equation (Nov 27)

Label: **proved** (Lean: `shape_landing`, `cycle_equation`, `cycle_shape_tests`).

Write the shape of any run of steps as its order of odd steps and halvings. Then:

- **Where a shape lands.** If the shape has U odd steps and K halvings, 2^K times the number reached is 3^U times the start, plus a constant c that depends only on the order of the steps, not on the start. (The block-landing rule of section 29 is the one-block case.)
- **The cycle equation.** If the run comes back to its start, then (2^K − 3^U) × start = c. So a cycle of a given shape exists only if c ÷ (2^K − 3^U) is a whole number, and then that whole number is its start.
- **Tests.** Up, halve, halve, up, halve, halve: c = 7, 2^4 − 3^2 = 7, start 1 (the loop 1, 4, 2 gone round twice). Climb 2, drop 3 (up, halve, up, halve, halve, halve): c = 5, and 5 ÷ 7 is not whole, so no number has that shape as a cycle.

This puts the "no cycle" half of the problem in block language as one exact equation per shape. Ruling out every shape is still open; Hercher (2023) shows a cycle would need at least 92 climb-and-drop passages.

## 31. Shadows of the negative cycles (Nov 27)

Label: **proved** (Lean: `climb_formula`, `block_handoff`, `neg17_handoff`, `neg17_chain`); script `scripts/collatz/shadows.py`.

The map x → x/2, 3x + 1 on all whole numbers, negative included, has four cycles besides 0: the positive 1 → 4 → 2 → 1, and on the negatives −1 → −2 → −1, −5 → −14 → −7 → −20 → −10 → −5, and the 18-step cycle of −17 (−17, −50, −25, −74, −37, −110, −55, −164, −82, −41, −122, −61, −182, −91, −272, −136, −68, −34). Each cycle has u odd steps and k halvings.

**The shadow rule.** A positive number that agrees with a cycle member a in its last k (or more) binary digits, x = a + 2^k · y, follows the cycle's steps once and lands on a + 3^u · y: it is scaled by 3^u/2^k about the cycle and agrees with a in k fewer digits. Repeating, it follows the cycle as long as the agreement lasts.

- Shadow of −1 (u = 1, k = 1, ×3/2 per digit): the climb. Trailing binary ones are agreement with −1 = …1111. This is the run formula.
- Shadow of −5 (u = 2, k = 3, ×9/8 per three digits): the block of ones (section 25). Its hand-off is `block_handoff`.
- Shadow of −17 (u = 7, k = 11, ×2187/2048 per 11 digits): new, `neg17_handoff` and `neg17_chain`.
- Shadow of 0 (halving) and of the positive cycle 1 → 4 → 2 → 1 (×3/4): these shrink, and they are the rules for even numbers and for remainder 1 on division by 4.

**What it explains.**
1. Every slow way to stay high is a shadow of a negative cycle, because those are the cycles whose factor 3^u/2^k is above 1.
2. The sliver's endings are these shadows. On division by 32 the sliver uses exactly the endings …00111, …01111, …11011, …11111, which are the endings of −25, −17, −5 and −1 (members of the −17, −5 and −1 cycles). Every sliver number below 3 million agrees with some negative-cycle member in at least its last 5 binary digits.
3. Why no rule that reads only a finite ending can close the sliver: −5 and −17 never drop, and at every depth their endings are shared by positive numbers, which therefore cannot be settled by their ending alone. A rule that closes the sliver has to use what makes a positive number different from −5 or −17: its binary digits eventually turn into all 0s on the left, where theirs are all 1s. So every shadow a positive number follows must break off within its own digits.

## 32. The digit carry law, and where a shadow breaks off (Nov 28)

Label: **proved** (Lean: `digit_carry`), the rest as marked.

**The digit carry law (proved).** Run some steps from r, with U odd steps and K halvings. Any number that agrees with r in its last K + 1 binary digits, r + 2^(K+1) · q, makes the same steps and lands on the same place plus 2 · 3^U · q. The unread digits q ride along: multiplied by 3 at each odd step, moved down one place at each halving. (This is the classical fact, Terras 1976 and Everett 1977, that a number's last digits fix its first steps, written for the plain 3x + 1 map with the carried part made exact.)

**Where a shadow breaks off (proved, from the carry law and section 31).** A positive x that agrees with a negative-cycle member a in exactly K binary digits follows the cycle while the agreement lasts, then lands on a point of the cycle plus 3^U times its unread digits. The digit where the agreement ends is where its path first leaves the cycle's pattern: the cycle wanted an odd step and it gets a halving, or the other way round.

**How long a shadow can last (proved, simple).** A positive x agreeing with a negative a in its last K digits has x − a = 2^K · y with y at least 1, so 2^K ≤ x + |a|: a shadow lasts at most about as many digits as x has. So one shadow lifts a number at most to about x^1.585 (shadow of −1, the climb; this is the climb bound found earlier), x^1.057 (−5) or x^1.009 (−17).

**Why that does not finish the argument.** The hope was that a positive number, having only so many digits, runs out of shadows. It does not run out, because climbing makes new digits: each odd step multiplies by 3 and adds about 1.585 digits, while each halving removes one. After a shadow breaks, the number's next ending comes from 3^U times its unread digits, digits the climb has just manufactured. So "positive numbers have finitely many digits" by itself only returns the balance between 1.585 digits made per odd step and 1 used per halving, the same balance as the debt of section 26. A closing rule has to say something about the digits that multiplying by 3 produces, not just count them.
