# Node list

The plain-language list the network was built from. The built network's
own record is each node's `formalization.yaml`, rendered in `GRAPH.md`.

Each node is one group of related claims. For each: what it says in plain
words, the Lean names in `rns_sieve_6.lean` (or the companion file named),
what it rests on, and its verification status.

**Status key**
- **Clean** — `#print axioms` confirmed to show only `propext`,
  `Classical.choice`, `Quot.sound`.
- **Cited** — a published theorem, stated precisely in Lean, whose proof is
  taken from the literature and has not been reproduced in Lean.
- **Conditional** — the step is proved, but its input is an open conjecture,
  held as a named hypothesis.

Every Clean status below was confirmed by `#print axioms` runs reported by
Geoffrey Fischer on 2026-11-03.

---

## Foundations

### 1. `Wheel6` — the 6n±1 wheel
Every prime above 3 leaves remainder 1 or 5 on division by 6.
- Lean: `prime_gt_three_is_candidate` (Part A, Step 1)
- Rests on: Mathlib only
- Status: Clean

### 2. `CRT` — one big cycle is the same as many small wheels
A position in the combined cycle of all the wheels carries exactly the same
information as one position on each individual wheel.
- Lean: `crt_map_bijective` (Part A, Step 3)
- Rests on: Mathlib's Chinese Remainder Theorem
- Status: Clean

### 3. `SquareRootShield` — trial division only needs small wheels
A number is prime exactly when no prime at or below the square root of the
ceiling divides it.
- Lean: `square_root_shield` (Part A, Step 5)
- Rests on: Mathlib only
- Status: Clean

### 4. `Admissibility` — which offset patterns can repeat forever
An offset pattern only has to be checked at the wheels no larger than the
number of offsets; the pattern {0, 2, 4} fails at the wheel of size 3; an
evenly spaced run passes exactly when every wheel up to its length divides
the spacing (the Lagrange–Waring condition).
- Lean: `admissible_of_large_primes`, `admissible_zero_two_four_false`
  (Part B, Step 1); `ap_offsets_admissible_iff` (Part D)
- Rests on: Vocabulary only
- Status: Clean

---

## Counting survivors

### 5. `SurvivorCount` — the exact number of open positions
The number of positions in the combined cycle that survive every wheel is
the product, over the wheels, of the open positions on each one: one at the
wheel of size 2 and two fewer than the wheel size elsewhere for twin primes,
and the wheel size minus `w` for a general pattern.
- Lean: `wheel_survivors_card_formula` (Part A, Step 4);
  `local_survivors_gen_card`, `wheel_survivors_gen_card_formula`
  (Part B, Step 4)
- Rests on: `CRT` (the source's admissibility hypothesis is unused and
  was dropped)
- Status: Clean

### 6. `SingularSeries` — the correction constant exists and is positive
Each wheel's correction factor differs from 1 by an amount that shrinks
like one over the wheel size squared, so the product over all wheels
converges, and for an admissible pattern the result is strictly positive.
The exact surviving fraction equals the correction product times the naive
independent-blocking guess.
- Lean: `delta_bound_of_large_prime`, `singular_series_delta_summable`,
  `singular_series_multipliable`, `hardy_littlewood_constant_pos`
  (Part B, Step 3); `rns_local_density_eq_singular_series_mul_naive`
  (Part B, Step 4)
- Rests on: `SurvivorCount` (local density only; the other claims rest on
  nothing)
- Status: Clean; the same results are also packaged, Comparator-ready, in
  the separate `HardyLittlewood` repository

### 7. `TwinConstant` — the classical twin-prime constant is recovered
For the twin pattern, the constant built from the wheels equals the
textbook value: 2 times the product, over odd primes, of one minus one over
(the prime minus one) squared.
- Lean: `twin_prime_constant_eq_classical` (Bonus section)
- Rests on: `SingularSeries`
- Status: Clean

### 8. `Pruning` — which starting positions are worth testing
Once the Lagrange–Waring condition is met, the number of starting positions
left to test for an evenly spaced prime run is an exact product over the
wheels: one fewer than the wheel size where the wheel divides the spacing,
and the run length fewer elsewhere.
- Lean: `valid_starting_residues_card_formula` (Part E)
- Rests on: `SurvivorCount` (with no admissibility hypothesis on the survivor
  count, `Admissibility` is not needed)
- Status: Clean

### 9. `WheelOrder` — what each wheel adds when wheels arrive in order
Bringing wheels in one at a time, the positions a wheel blocks for the
first time equal the open positions left by every earlier wheel times the
full size of every later wheel. Separately, from any 6n±1 position, the next
number with a chosen last digit is reached in the raw digit distance or at
most one further step of 10.
- Lean: `wheel_marginal_new_formula` (Part F); `wheel_gap_floor` (Part G)
- Rests on: no other node (Part G uses the `is_candidate` definition, not
  the `Wheel6` claim)
- Status: Clean

---

## Certificates and runs

### 10. `ShieldCertificates` — certifying primes, and why prime runs stop
If a set of wheels covers every prime up to the square root of the ceiling,
surviving them proves primality, for single numbers, evenly spaced runs in
either direction, and offset patterns. Conversely, a wheel that does not
divide the spacing must block one of any run as long as the wheel itself,
which caps the run length and forces the Lagrange–Waring condition on real
prime runs. Between a cutoff and its square, prime means exactly "no wheel
divides it."
- Lean: `prime_of_shield_cover`, `family_prime_of_shield_cover`,
  `forward_ap_prime_of_active_shield`, `backward_ap_prime_of_active_shield`,
  `tuple_prime_of_active_shield`, `ap_hits_wheel`,
  `ap_prime_run_length_lt_of_lt_start`, `ap_prime_run_forces_divisibility`,
  `window_prime_iff`, `window_twin_iff`, and the backward versions
- Rests on: `SquareRootShield` (no proof here uses `Admissibility`)
- Status: Clean

---

## Infinitude

### 11. `Infinitude` — two independent proofs that primes never run out
Euclid's argument using the combined cycle plus one; and a counting
argument showing a fixed finite set of wheels cannot build enough
square-free parts for every number.
- Lean: `rns_primes_unbounded`, `rns_wheel_supply_cannot_be_finite`,
  `rns_infinitude_via_squarefree_counting`
- Rests on: Vocabulary only
- Status: Clean

### 12. `ColumnStructure` — how the two columns multiply
A product of two numbers from the 6n-1 column lands in the 6n+1 column,
and so on for all four combinations; each prime above 3 hits the 6n-1
column at exactly one position per cycle; every number in the 6n-1 column
has a prime factor from that same column.
- Lean: `col_minus_mul_col_minus` and the three companions,
  `col_minus_periodicity`, `col_minus_has_minus_prime_factor`,
  `col_minus_composite_has_proper_minus_factor` (Part C)
- Rests on: `Wheel6`
- Status: Clean

### 13. `DirichletColumns` — both columns hold infinitely many primes
- Lean: `col_minus_primes_infinite`, `col_plus_primes_infinite`,
  `col_minus_primes_unbounded`, `col_plus_primes_unbounded` (Part I)
- Rests on: no other node; only Mathlib's Dirichlet theorem and the column
  definitions
- Status: Clean

---

## Conditional results (rest on open conjectures)

### 14. `HardyLittlewood` — the conjecture, and what it would give
The prime-pattern count is stated to grow like the constant times the
number divided by its logarithm raised to the number of offsets. Proved: if
that holds for the twin pattern, there are infinitely many twin primes.
- Lean: `hardy_littlewood_conjecture` (stated, open);
  `twin_prime_conjecture_implies_infinite_twin_primes`
- Rests on: `SingularSeries` and `Admissibility` (positivity of the constant,
  and admissibility of {0, 2}); open input `hardy_littlewood_conjecture`
- Status: Conditional, Clean

### 15. `HensleyRichards` — Hardy and Littlewood's two conjectures clash
If an admissible pattern packs more offsets into a window than there are
primes in a window of that length, Conjecture A (every admissible pattern
repeats forever) and Conjecture B (prime counts are subadditive) cannot both
hold.
- Lean: `HL_A_and_B_incompatible` (Part J)
- Rests on: no other node; open inputs `HL_conjecture_A`, `HL_conjecture_B`
- Status: Conditional, Clean

### 16. `LinearForms` — Dickson's conjecture gives Sophie Germain primes
The pair "a number and twice it plus one" passes the linear-forms version
of admissibility; so Dickson's conjecture would give infinitely many Sophie
Germain primes.
- Lean: `sophieGermainSystem_admissible`,
  `sophie_germain_conjecture_of_LinearForms_conjecture` (Part K)
- Rests on: Vocabulary; open input `LinearForms_conjecture`
- Status: Conditional, Clean

### 17. `GapConjectures` — Legendre, Brocard, Oppermann, Andrica
Each named survivor bound implies its conjecture; Oppermann's conjecture
implies both Andrica's and Legendre's, giving Legendre two independent
routes.
- Lean (`rns_open_conjectures.lean`):
  `legendre_conjecture_of_jacobsthal_bound`,
  `brocard_conjecture_of_four_survivors_bound`,
  `oppermann_conjecture_of_oppermann_bound`,
  `andrica_conjecture_of_oppermann_conjecture`,
  `legendre_conjecture_of_oppermann_conjecture`
- Rests on: no other node; open inputs
  `jacobsthal_bound_holds`, `four_survivors_bound_holds`,
  `oppermann_bound_holds`, `oppermann_conjecture`
- Status: Conditional, Clean

---

## Companion files

### 18. `SophieGermainWheel` — where Sophie Germain primes can sit
Every Sophie Germain prime above 3 lies in the 6n-1 column; none ends in the
digit 7; so above 5 its last digit is 1, 3 or 9.
- Lean (`sophie_germain_wheel.lean`): `sophie_germain_mod_six`,
  `sophie_germain_not_ends_in_seven`, `sophie_germain_last_digit`
- Rests on: `Wheel6`, `WheelOrder` (the last-digit wheel from Part G)
- Status: Clean

### 19. `GapTracks` — which gaps each column allows
The smaller of two twin primes above 3 always lies in the 6n-1 column, and
the smaller of two cousin primes in the 6n+1 column. In general, a gap
starting from the 6n-1 column never leaves remainder 4 on division by 6, and
a gap starting from the 6n+1 column never leaves remainder 2; a gap that is a
multiple of 6 keeps both primes in the same column. One claim is refuted
rather than proved: the number between two primes six apart is not always
composite (5, 7, 11 is a counterexample).
- Lean (`twin_cousin_sexy_tracks.lean`, `prime_gap_track_constraint.lean`):
  `twin_prime_mod_six`, `cousin_prime_mod_six`, `sexy_prime_same_track`,
  `sexy_middle_not_always_blocked`,
  `prime_gap_forbidden_four_from_six_minus_one`,
  `prime_gap_forbidden_two_from_six_plus_one`,
  `prime_gap_same_track_of_six_dvd`
- Rests on: `Wheel6`
- Status: Clean

### 20. `DudekJohnston` — a near-prime between every pair of squares
Between every two consecutive squares there is a number with at most four
prime factors, counted with repetition. This is a proven, published
weakening of Legendre's conjecture, which asks for a prime there.
- Source: Dudek and Johnston, *Almost primes between all squares*,
  arXiv:2501.18048 (2025), Theorem 1.2
- Lean (`dudek_johnston_rns.lean`): `dudek_johnston_statement` (stated),
  `dudek_johnston_almost_primes_between_squares` (proof is `sorry`)
- Rests on: the paper
- Status: Cited. The small cases check out by computation, but they use
  `native_decide`, which relies on the extra axiom `Lean.ofReduceBool`.

---

## New work in this repository

### 21. `UniformSubdivision` — equal shares of survivors in equal intervals
With one wheel rotating and the rest frozen, the full cycle splits into as
many equal intervals as the rotating wheel's size minus one, each holding one
frozen cycle's worth of survivors. By column, a rotating wheel on the 6n+1
side keeps every column's share exact; one on the 6n-1 side swaps columns,
so each interval is off by the two columns' difference in the overhang.
- Prior work: Lehmer, Canad. J. Math. 7 (1955), Theorem 4 (the whole-count
  form is a special case); restated by Grob and Schmitt, arXiv:1905.03117
  (2019), Theorems 6-9. The 6n+1-side column form uses Lehmer's mechanism;
  the 6n-1-side correction was not found in the literature searched.
- Lean: `frozen_wheels_repeat`, `one_wheel_removed`, `uniform_subdivision`,
  `uniform_subdivision_plus_side`, `uniform_subdivision_minus_side`
  (stated in this repository; no source file)
- Rests on: Vocabulary only
- Status: Planned. Claims stated; not yet built or proved. Checked
  numerically on 3,647 cases with no failures.

---

## Candidate formalizations (not yet started)

Results from the literature on how survivors spread out, each stated in
wheel terms. All are finite counting statements about the combined cycle,
so they fit the RNS vocabulary directly. Statements marked "checked" held
in a numerical test (4,761 cases: wheel sets drawn from the primes up to 19,
up to 24 equal intervals).

**Tier 1: elementary, and they strengthen existing nodes**
- **Lehmer's even split, general form** (Lehmer 1955, Thm 4). If one wheel
  leaves remainder 1 on division by a chosen number of intervals, the
  survivors of the cycle split evenly across that many equal intervals
  (endpoints rounded down). `uniform_subdivision` becomes the special case
  of the rotating prime minus one intervals. Checked.
- **Column form of Lehmer's split.** With wheels 2 and 3 frozen, if some
  wheel leaves remainder 1 on division by the least common multiple of 6
  and the number of intervals, each column splits evenly too. Checked.
- **Mirror symmetry** (Lehmer 1955, Thm 1; Grob and Schmitt 2019, Thm 2).
  A position survives exactly when its reflection in the cycle survives.
  (The interval-by-interval form needs exact endpoints; with rounded-down
  endpoints it fails, as the test showed.)
- **Spread bound** (Lehmer 1955, Thms 9-10). Any two equal intervals'
  survivor counts differ by at most two to the number of wheels. Checked.
- **Column-imbalance bound.** With wheels 2 and 3 frozen, the two columns'
  survivor counts up to any point differ by at most two to the number of
  remaining wheels. Proof by inclusion-exclusion with the column sign.
  Checked.
- **Column action of a wheel.** Multiplying by a prime keeps the 6n-1 and
  6n+1 columns in place if it leaves remainder 1 on division by 6, and
  swaps them if it leaves remainder 5. (The lemma behind both column forms;
  check overlap with `ColumnStructure` first.)

**Tier 2: elementary but longer**
- **Divisibility case of the even split** (Lehmer 1955, Thm 2): if the
  square of the number of intervals divides the modulus, the split is even.
  Only applies to moduli with repeated factors, so outside pure wheel
  cycles; low priority.
- **Lehmer's closed form for 6n-1-type wheels** (Lehmer 1955, Thm 8): when
  every wheel leaves remainder one less than the number of intervals, the
  excess in the first intervals has an exact formula. The 6n-1 side of
  Lehmer's picture, and the natural partner to `uniform_subdivision_minus_side`.
- **Adding one wheel at most doubles the largest gap** (Codecà and Nair
  1998, Thm 1(i)): the largest gap between the survivor count and its
  proportional share, after adding a wheel, is at most twice the old one
  minus one over the new prime. Needs rational numbers.
- **Mean-square identity** (Codecà and Nair 1998, Thm 3(i)): an exact
  formula for the average squared gap over the survivor positions.

**Tier 3: needs heavier Mathlib**
- **Germain's exact criterion** (Germain 2005, Thm 1.1): the survivors
  split evenly across a given number of equal intervals exactly when every
  odd Dirichlet character for that number takes the value 1 at some wheel.
  The proof uses the nonvanishing of Dirichlet L-functions at 1; check
  what Mathlib provides before scoping.

**From Birdsey and Schay (arXiv:1906.09220, 2019)**
- **Twin share of the cycle** (Tier 1). Among all survivors of a cycle, the
  twin survivors make up exactly the product, over the wheels from 3 up, of
  the wheel size minus 2 over the wheel size minus 1. Follows from the two
  existing counts in `SurvivorCount`. A companion finite identity splits
  that product into the partial twin-prime constant times the share of
  numbers coprime to the wheels.
- **Their heuristic as a named hypothesis** (Tier 3). Stated as a `Prop`:
  below the next prime's square, the twin primes number the wheel share
  of twins times the count of primes there, times one Mertens correction
  (half of e to the Euler constant), asymptotically. The step from it to
  the twin-prime asymptotic needs the prime number theorem and Mertens'
  product theorem as further inputs; check what Mathlib provides, or take
  them as cited hypotheses. This puts the paper's unproven assumption on
  the graph as an open input, separate from the exact wheel share.

**Open question (not a formalization target yet)**
- How large the column imbalance can get as wheels are added. Computed up
  to the wheel at 23 (maxima 2, 3, 5, 8, 12, 18); the untwisted analogue is
  studied by Codecà and Nair 1998 and grows at a similar rate. No paper on
  the column version found so far.
