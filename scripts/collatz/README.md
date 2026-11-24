# Collatz scripts (CollatzHub notes)

Python 3, standard library only. Run each from this folder, for example
`python3 exit_table.py`. They reproduce the measured results recorded in
[`docs/COLLATZ_NOTES.md`](../../docs/COLLATZ_NOTES.md); the proved results are
in the Lean node [`CollatzHub`](../../docs/nodes/CollatzHub.md).

Every script works on the **hub map** on the index n of the hub value 6n − 2:
n → 3n/2 when n is even (the bad loop), (3n + 1)/4 when n leaves remainder 1
on division by 4, (n + 1)/4 when it leaves remainder 3.

| Script | What it reproduces | Notes section | Time |
|---|---|---|---|
| `collatz_link_sieve.py` | The linking sieve: open residue classes by depth, with the mod-3 rule (`--mod3`), coalescence (`--coalesce`) and exit pairing at every run exit (`--pair`) | 4 | 8–60 s at depth 20 |
| `exit_table.py` | The exit table mod 16, and the drop decided by run length and the odd part mod 4 | 3 | seconds |
| `glide_bits.py` | Climbs last far longer than the starting bits could dictate | 4 | about 1 min |
| `doubling_chain.py` | Pair merge points along one doubling chain do not meet quickly | 5 | seconds |
| `ladder_chunks.py` | Ladder chunks grown backward from 1: coverage by generation | 5 | 4 s (60 s with cap factor 4096) |
| `meet_middle.py` | Chunks backward plus the sieve's problem classes forward, and the null result of peak linking | 5 | 4 s |
| `climber_profile.py` | What the highest climbers have in common | 6 | about 25 s |
| `shared_peaks.py` | Family size against run length into the peak; families are backward trees below the peak | 6 | about 20 s |
| `funnels.py` | Funnel depth exponent for every peak below 2^18 and random peaks to 2^36 | 6 | under 1 s |
| `funnel_width_depth.py` | Depth against width over about 255,000 funnels | 6 | about 1 s |
| `mountain_slope.py` | Climbers per one-bit band below a peak (the halving slope) | 6 | under 1 s |
| `summit_composition.py` | Which loop each member takes, by band, and the share in exit pairs | 6 | under 1 s |
| `critical_branching.py` | Tree size proportional to room (exponent exactly 1); deepest member's tree | 7 | about 1 min |
| `ternary_residues.py` | The branching constant C is driven by base-3 digits, not base-2 | 7 | about 15 s |
| `exact_links.py` | Real trees against random models with and without the exact ladder cycle | 8 | about 20 s |
| `tail_hierarchy.py` | Real trees against models with 1 to 8 exact ternary digits (10,000 trees each) | 8 | about 70 s |
| `dip_law.py` | How far trees dip below their root: about 4 times rarer per bit | 9 | about 20 s |
| `climb_bound.py` | The fair game: climb shares against the 2^−d bound, worst peak exponents | 10 | a few minutes |
| `counting_formula_check.py` | The ladder-sum counting formula against brute force | 11 | seconds |
| `rising_tide.py` | The rising tide: already wet, dry, and mountain pioneers | 14 | about 1 min |
| `lyapunov_search.py` | Lyapunov scores with credits for factors of 2 and 3 | 15 | a few minutes |
| `sub_peaks.py` | Smaller peaks inside mountains: one per 4.5 members, and how they nest | 16 | about 1 min |
| `interval_owners.py` | Where the numbers between a run start and its peak belong | 17 | a few minutes |
| `pioneer_staircase.py` | The pioneer's staircase of new highs, and foothill sizes by depth | 17 | about 1 min |
| `mountain_favors.py` | How many later numbers link into each path, by the owner's climb | 17 | about 1 min |
| `pioneer_density.py` | Pioneers per doubling block, and how big pioneers thin out | 18 | a few minutes |
| `escape_cover.py` | Forced escape routes landing on 1's tree, by sieve depth | 20 | 20–60 s (`python3 escape_cover.py 26 20`) |
| `cover_height.py` | How high 1's tree must reach to cover every forced route | 20 | about 1 min |
| `tree_floor.py` | The worst-case floor on backward trees from the exact links | 21 | a few minutes |
| `engineered_vs_records.py` | Climb from a number's own digits against climb after they run out | 22 | seconds |
| `climber_digits.py` | Digit features of the top climbers against everyone | 22 | about 1 min |
| `dense_ones.py` | Engineered numbers with dense binary ones | 22 | about 1 min |
| `climb_loops.py` | How record climbs use the three loops | 23 | about 1 min |
| `staircase_steps.py` | Record peaks that are beaten again against final peaks, by ending | 24 | about 1 min |

Times are on a single core; random samples use fixed seeds, so reruns print
the same numbers.
