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
  (proved in `RNSSolutions/UniformSubdivision.lean`; no source file)
- Rests on: Vocabulary only
- Status: Clean. All five claims proved; `#print axioms` shows only the
  standard three (Geoffrey Fischer, 2026-11-04). Checked numerically
  beforehand on 3,647 cases.

### 36. `Sawtooth` — the survivor count minus its proportional share
The survivors up to any point are a signed count over the ways of choosing
some of the wheels: the bound divided by the product of the chosen wheels,
plus for an even number chosen and minus for an odd number (Legendre). At a
fraction of the cycle, the survivors minus their proportional share, times
the fraction's denominator, are minus a signed sum of remainders, one for
each choice of wheels. So the split at that fraction is even exactly when
the remainders cancel.
- Prior work: the classical identity (Legendre's count with the Möbius
  function); the starting point of Germain, Canad. Math. Bull. 48 (2005),
  Theorem 1.1, which writes it over divisors with fractional parts.
- Lean: `legendre_count`, `sawtooth_identity`,
  `even_split_iff_remainders_cancel`, `column_legendre_count` (proved in `RNSSolutions/Sawtooth.lean`;
  no source file)
- Rests on: Vocabulary only
- Status: Clean. All four claims proved; `#print axioms` shows only the
  standard three (Geoffrey Fischer, 2026-11-04). Checked numerically beforehand on
  16,065 cases (wheels from 2 to 13, up to 14 intervals, fractions past the
  end of the cycle included).

### 44. `BonseCeiling` — from four wheels on, the ceiling sits inside one cycle
For every prime from 11 on, its square (the ceiling of the wheels below it)
is smaller than the product of the wheels below it (their combined cycle).
With 2, 3, 5 the ceiling 49 lies outside the cycle 30; once 7 is in, the
ceiling 121 lies inside the cycle 210, and it stays inside.
- Prior work: Bonse's inequality (1907).
- Lean: `ceiling_inside_cycle` (proved in `RNSSolutions/BonseCeiling.lean`;
  no source file). Strong induction over the primes, using Bertrand's postulate
  from Mathlib.
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three
  (Geoffrey Fischer, 2026-11-05).

### 45. `PillaiBrauer` — runs where no member is coprime to all the others
Among any 16 or fewer consecutive positive integers one is coprime to all the
others (Pillai; now proved here). From 17 on this fails through the wheels up to 13:
every member of the run 2184 to 2200 shares one of 2, 3, 5, 7, 11, 13 with
another member, and shifting by any multiple of the cycle 30030 keeps that.
- Prior work: Pillai (1940), Brauer (1941).
- Lean: `pillai_sixteen`, `pillai_witness_17`, `pillai_witness_17_repeats`
  (all proved in `RNSSolutions/PillaiBrauer.lean`)
- Rests on: Vocabulary only
- Status: Clean. All three claims proved; `#print axioms` shows only the
  standard three (witness claims: Geoffrey Fischer, 2026-11-05; `pillai_sixteen`:
  GitHub Actions build, 2026-11-05).
- How `pillai_sixteen` is proved: two members of a run of at most 16 differ by
  at most 15, so a prime dividing both is a wheel up to 13. A member is
  coprime to all the others as soon as every wheel up to 13 dividing it has no
  other multiple in the run, which depends only on the run's start in the
  cycle 30030. The kernel checks every start of the cycle and every length
  from 1 to 16 (`decide +kernel`, 30 separate block checks; about 3.5 minutes
  of build time).

### 46. `KanoldBound` — every stretch of 2^k numbers holds a survivor of k wheels
For any k prime wheels, every stretch of two to the k consecutive numbers
contains a survivor, so the largest survivor gap is at most two to the number
of wheels. Kanold's explicit bound on Jacobsthal's function.
- Prior work: Kanold, Math. Ann. 170 (1967).
- Lean: `stretch_holds_survivor` (cited, not proved)
- Rests on: Vocabulary only
- Status: Cited (2026-11-05). Checked numerically for every set of up to six
  wheels from the primes up to 23. A Lean proof is future work.

### 47. `MenonIdentity` — a gcd sum over the survivors of one cycle
For prime wheels, the gcds of (survivor minus one) with the cycle length, added
over the survivors of one cycle, total the survivor count times two to the
number of wheels.
- Prior work: Menon, J. Indian Math. Soc. 29 (1965).
- Lean: `menon_wheel_sum` (proved in `RNSSolutions/MenonIdentity.lean`)
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05). Checked numerically first for every set of wheels
  from the primes up to 13.
- How it is proved: the gcd is the sum of the totients of its divisors; swapping
  the sums, each divisor d of the cycle counts the survivors leaving remainder 1
  on division by d. Those are 1 + d·t for t below the cofactor e, and since d is
  invertible modulo e their remainders run once through every remainder, so φ(e)
  of them survive. Each divisor then gives φ(d)·φ(e) = φ(cycle), and the cycle
  of k wheels has 2^k divisors. Elementary; no Chinese Remainder Theorem
  machinery needed.

### 48. `GallagherAverage` — the wheel correction is 1 on average
Averaged over all patterns of k distinct offsets from 1 to h, the
Hardy-Littlewood constant tends to 1 as h grows.
- Prior work: Gallagher, Mathematika 23 (1976); Kowalski (2008); Pintz (2010).
- Lean: `singular_series_average_one` (cited, not proved). A proof would rest on
  `SingularSeries`.
- Rests on: Vocabulary only
- Status: Cited (2026-11-05).

### 49. `LongGaps` — blocked runs become long prime gaps (outside source)
OpenAI's Lean proof of an improved Rankin-type lower bound for the largest
prime gap. Planned as an outside-source node cited from `BlockingRuns`.

### 50. `PrimeGapsBridge` — the network's admissibility is PrimeGapsLib's
The network's admissibility (fewer occupied positions than the wheel size)
equals Axiom Math's PrimeGapsLib definition (some residue class missed at
every prime), copied word for word. So PrimeGapsLib's results on admissible
sets, including gaps of at most 246 infinitely often under Bombieri-Vinogradov,
apply to the network's patterns unchanged.
- Lean: `admissible_iff_primegaps` (proved in `RNSSolutions/PrimeGapsBridge.lean`)
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 51. `RamanujanSums` — the survivor pattern's frequencies, wheel by wheel
Ramanujan's sum for the combined cycle (the survivors of one cycle, turned by
a frequency and added up) is a product over the wheels: wheel size minus 1 if
the wheel divides the frequency, minus 1 if not.
- Prior work: the squarefree case of Kluyver's evaluation (1906).
- Lean: `cycle_root`, `ramanujan_sum` (defined here; Mathlib has no Ramanujan
  sums), `ramanujan_wheel_product` (proved in `RNSSolutions/RamanujanSums.lean`)
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 52. `BrunTwinSum` — the twin primes' reciprocals add up to a finite total
- Prior work: Brun (1919). Its sieve heart is the twin share of `ShareBounds`.
- Lean: `twin_reciprocal`, `brun_sum_finite` (cited, not proved; a proof would
  use Mathlib's Selberg sieve and a Mertens-type estimate)
- Status: Cited (2026-11-05).

### 53. `GapMoments` — the survivor gaps are spread as evenly as their average allows
The gaps between consecutive survivors of one cycle, raised to any fixed power
and added up, are at most a constant times their total if every gap were the
average gap.
- Prior work: Erdős's conjecture; Hooley (powers below 2); Montgomery and
  Vaughan, Ann. of Math. 123 (1986), all powers.
- Lean: `gap_moment_bound` (cited, not proved)
- Status: Cited (2026-11-05). Checked numerically for every set of wheels from
  the primes up to 13 at powers 1/2, 1, 2, 3 (constant at most 2.1).

Not stated: Erdős's 1962 result that Jacobsthal's function is typically close
to its average-gap prediction. Its exact normalization could not be confirmed
from a primary source, so it is left out rather than stated wrongly.

### 54. `SophieGermainPowers` — on the wheel of size 2p+1, p-th powers have three positions
For a Sophie Germain prime p, every p-th power sits at position 0, 1 or -1 on
the wheel of size 2p+1 (Fermat's little theorem); so if that wheel blocks a
sum of three p-th powers, it blocks one of the three numbers.
- Lean: `pth_power_positions`, `three_powers_blocked`
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 55. `SophieGermainTheorem` — Fermat's first case for Sophie Germain primes
For a prime p with 2p+1 prime, x^p + y^p + z^p = 0 forces p to divide x y z;
for odd p, x^p + y^p = z^p has no solution with p dividing none of x, y, z.
The proof uses the wheel of size 2p+1 twice: on x, y, z, and on the p-th roots
of the pairwise sums y+z, z+x, x+y.
- Prior work: Sophie Germain (about 1823); formalized in Isabelle by
  Ballenghien (2025). No Lean formalization found.
- Lean: `sophie_germain_theorem`, `fermat_first_case`
- Rests on: `SophieGermainPowers` (both claims)
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 56. `GermainAuxiliary` — Sophie Germain's theorem with any suitable wheel
A prime wheel q is auxiliary for an odd prime p when no two p-th power
positions sit next to each other and p is not at a p-th power position. If one
exists, x^p + y^p + z^p = 0 forces p to divide x y z. The wheel 2p+1 is
auxiliary for Sophie Germain primes; the wheels 29 and 53, checked position by
position by Lean's kernel, are auxiliary for 7 and 13, which are not Sophie
Germain primes, giving the first case of Fermat's Last Theorem for 7 and 13.
- Prior work: Sophie Germain (Legendre, 1823); formalized in Isabelle by
  Ballenghien (2025).
- Lean: `auxiliary_prime_theorem`, `sophie_germain_wheel_auxiliary`,
  `auxiliary_seven`, `auxiliary_thirteen`, `fermat_first_case_seven`,
  `fermat_first_case_thirteen`
- Rests on: `SophieGermainPowers` (for the Sophie Germain link)
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 57. `Schatunowsky` — 30 is the largest number whose survivors are all prime
Treat a number as a cycle: its survivors are the numbers below it sharing no
factor with it. For 30 every survivor other than 1 is prime. If a prime's
square lies below a number and the prime does not divide it, that square is a
composite survivor; so every prime below the ceiling's root must be a wheel of
the number. Bonse's inequality then puts the product of those wheels above
the next ceiling once the wheels reach 7, and below that only 30 fits.
- Prior work: Schatunowsky (1893); Pambuccian (2015) derives it from Bonse's
  inequality.
- Lean: `ceiling_forces_wheels`, `thirty_survivors_all_prime`,
  `schatunowsky_bound`
- Rests on: `BonseCeiling` (for the bound)
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 58. `HurwitzZetaZero` — the Hurwitz zeta function at 0
For 0 < x ≤ 1 the Hurwitz zeta function at 0 equals 1/2 − x. This turns
L-function values into finite sums over a cycle's residues, the analytic input
`GermainCriterion` needs beyond Mathlib. Mathlib's even part at 0 and its
functional equation reduce it to Mathlib's `sinZeta x` at 1. Abel summation
and dominated convergence show that this is the sum of the sawtooth's Fourier
series, and Abel's limit theorem sums that series to π(1/2 − x). This fills
the case s = 0 that Mathlib's `hurwitzZeta_neg_nat` leaves as a TODO, and
could be offered to Mathlib.
- Prior work: Apostol, Introduction to Analytic Number Theory (1976),
  Thm 12.13.
- Lean: `hurwitz_zeta_at_zero`, `sin_zeta_at_one`, `sawtooth_partial_sums`,
  `sin_zeta_at_one_eq_series`
- Rests on: Mathlib only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).
- Later, to look at (an alternative proof): the residue theorem route. Riemann's Hankel-loop formula
  for the Hurwitz zeta function becomes, at s = 0, a loop integral of
  e^(−az)/(z(1 − e^(−z))) whose only enclosed pole, at z = 0, has residue
  1/2 − a. The residue step fits Mathlib's Cauchy integral formula on circles,
  but Mathlib has no Hankel loops and no general residue theorem, and the loop
  formula would still have to be tied to Mathlib's `hurwitzZeta` at s = 0 by
  analytic continuation.

### 59. `FortunateCeiling` — what lands on a prime just above the cycle
Add a number above 1 to the combined cycle of the wheels. If the sum is prime,
a wheel dividing the number would divide the sum too, and the sum is larger
than the wheel; so no wheel divides the number. The ceiling argument then
applies: below the next prime's square the number is prime, a composite one is
at least that square, and below the next prime's cube a composite one is a
product of exactly two primes. This settles the RNS half of two open
statements in DeepMind's `formal-conjectures`:
- Fortune's conjecture (every Fortunate number is prime): every Fortunate
  number is at least the next prime, and is prime whenever it lies below the
  next prime's square, so the conjecture follows from that ceiling bound
  (`fortune_of_ceiling`). The bound itself is open.
- OEIS A038771 (smallest composite that lands on a prime): never below the next
  prime's square, for every wheel count, which is the "ratio at least 1" half
  of the Greathouse–Ordowski conjecture; and Kamenetsky's conjecture (always
  two prime factors) holds whenever the value is below the next prime's cube
  (`semiprime_conjecture_of_cube`). The cube bound is open.
The definitions follow `formal-conjectures` (`Wikipedia/FortuneConjecture.lean`,
`OEIS/38771.lean`) with the same wheels and indexing; two bridge claims tie
Mathlib's `primorial` and the product of the first primes to the network's
`primorial_modulus`.
- Prior work: OEIS A005235, A038771; the existence of a composite that lands
  on a prime uses Dirichlet's theorem, as in `formal-conjectures`' `a_n_exists`.
- Lean: `shift_avoids_wheels`, `shift_prime_below_ceiling`,
  `composite_shift_at_least_ceiling`, `composite_shift_semiprime_below_cube`,
  `first_primes_eq_cycle`, `primorial_eq_cycle`, `fortunate_spec`,
  `fortunate_at_least_next_prime`, `fortunate_prime_below_ceiling`,
  `fortune_of_ceiling`, `smallest_composite_shift_spec`,
  `smallest_composite_shift_floor`,
  `smallest_composite_shift_semiprime_below_cube`, `semiprime_conjecture_of_cube`
- Rests on: `ShieldCertificates` (`window_prime_iff`, for the three
  prime-below-the-ceiling claims); everything else on Mathlib only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-05).

### 60. `AlmostPrimeWindow` — survivors between the cutoff and its cube
Take the wheels below a cutoff. From the cutoff up to its cube, a number no
wheel divides is a prime or a product of exactly two primes: every prime
factor is at least the cutoff, so three would already reach the cube. The
composite survivors are exactly the products of two primes each at least the
cutoff. This is the almost-prime mechanism behind Chen's theorem. It also
places the parity problem exactly: in this window a survivor is prime
precisely when its number of prime factors is odd, and the wheels by
themselves cannot tell one factor from two.
- Prior work: the standard step behind sifting at the cube root (Chen's
  theorem); the parity problem (Selberg; Tao's 2007 exposition).
- Lean: `window_almost_prime`, `window_composite_iff`,
  `window_prime_iff_odd_factors`
- Rests on: Vocabulary only. Generalises `FortunateCeiling`'s cube claim.
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### 61. `TuranCycle` — Turán's sieve, exactly, on the positions 1 to N
At each position, count the wheels dividing it (its hits). Over the positions
1 to N the hits total the multiples of each wheel, and the squared hits total
the multiples of the least common multiple of each ordered pair of wheels,
both exactly. Turán's second-moment inequality, proved for any counting
function on any finite set, then bounds the survivors, which have no hits.
Weak (about 15,100 allowed against the true 5760 for the wheels up to 13 on
one cycle), but the first step from exact counts to sieve bounds, with every
ingredient exact.
- Prior work: Turán (1934), the second-moment proof of Hardy–Ramanujan.
- Lean: `hits_sum`, `hits_sq_sum`, `turan_inequality`, `turan_wheels`
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### 62. `BrunPureSieve` — truncated inclusion–exclusion for the wheels
Count the survivors of prime wheels among the positions 1 to N by
inclusion–exclusion over sets of wheels. Stopping after the sets of at most an
even number of wheels gives at least the true count; stopping after an odd
number gives at most it (the Bonferroni inequalities); going all the way is
exact (Legendre's identity). The proof groups the subsets of each position's
hit set by size, and Mathlib's partial alternating binomial sum
(`Int.alternating_sum_range_choose_eq_choose`) does the rest. Brun's pure
sieve, the starting point of his sieve and of the fundamental lemma.
- Prior work: Brun (1915, 1919); Bonferroni inequalities; Legendre.
- Lean: `bonferroni_even`, `bonferroni_odd`, `legendre_exact`, `bonferroni_even_fn`,
  `bonferroni_odd_fn`, `twin_bonferroni_upper`
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).
- Brun stage 1 (added 2026-11-06): the same truncation works for any function
  of the position, not only the position itself. A position survives when no
  wheel divides the function's value there. Applied to the product of a
  position and the position two further on, this gives Brun's upper bound for
  twin survivors: the count is at most inclusion–exclusion stopped at an even
  number of wheels. Clean; standard three axioms only.

### 63. `MertensThird`, `PrimeNumberTheorem`, `CeilingOvershoot` — stated and connected
`MertensThird` and `PrimeNumberTheorem` were metadata only; both now have Lean
statements. For Mertens' third theorem the one result taken from PNT+ is the
remainder bound `Mertens.E₃.abs_le` (blueprint 7.1.8), copied word for word
with the definition `E₃` (blueprint 7.1.6); PNT+'s `Mertens.lean` and its one
non-Mathlib import contain no `sorry` (checked at commit 127b50e, 2026-10-19).
The identity (blueprint 7.1.7: the survivor share is e^(-γ) e^(E₃(x)) / log x)
is proved here, adapted from PNT+, and the limit form (share times log x tends
to e^(-γ)) follows. `CeilingOvershoot` is then a step: with the wheels up to
the square root of x, x times the survivor share over the number of primes up
to x tends to 2e^(-γ), about 1.1229. Below the ceiling the survivors are
exactly the primes, so the wheel product overshoots them by about 12%.
Numerically 0.91 at a thousand, 1.05 at ten million.
- Lean: `mertens_third_remainder` (outside, PNT+ word for word),
  `product_identity`, `mertens_third`, `pnt_equivalent` (outside, PNT+ `pi_alt'`
  word for word), `prime_number_theorem`, `ceiling_overshoot`
- Rests on: PNT+ (two outside claims)
- Status: the identity and the three steps are Clean (GitHub Actions build,
  2026-11-06); the two outside claims are cited. By text search the PNT+
  chain behind `pi_alt'` has two `sorry` lemmas (`prelim_decay_2`,
  `prelim_decay_3` in `Wiener.lean`) that nothing in that chain uses; a
  `#print axioms` run inside PNT+ would confirm.

### 64. `ShareAsymptotics` — how fast the survivor and twin shares shrink
With the wheels up to n, the share of the cycle that survives, times log n,
tends to e^(-γ) (about 0.5615); so `ShareBounds`' bound (at most 1/log) is
sharp up to that factor. The twin share times log² n tends to the twin-prime
constant times e^(-2γ) (about 0.4162). Twice the odd twin product (over the
odd primes of 1 − 1/(p−1)²) is proved equal to `TwinConstant`'s classical
twin-prime constant, which `TwinConstant` proves equal to the Hardy–Littlewood
constant of the twin pattern. In general, for any nonempty admissible offset
pattern with k offsets, its share of the cycle times (log n)^k tends to its
Hardy–Littlewood constant times e^(-kγ): the wheel-side form of the
Hardy–Littlewood prediction, exact in everything but Mertens. Numerically
0.56144, 0.41618, and 0.50583 for the pattern 0, 2, 6 (limit 0.50589), at n a
million.
- Lean: `survivor_share_asymptotic`, `twin_share_asymptotic`,
  `odd_twin_product_eq_classical`, `twin_share_asymptotic_classical`,
  `pattern_share_asymptotic`
- Rests on: `SurvivorCount`, `TwinShare`, `SingularSeries`, `MertensThird`
  (hence on the PNT+ remainder bound)
- Status: Clean. Steps proved; `#print axioms` shows only the standard three
  (GitHub Actions build, 2026-11-06).

Not given new nodes, because the network already has them: Legendre's
identities for the survivor count (periodicity and the one-wheel recurrence
are `UniformSubdivision.frozen_wheels_repeat` and `one_wheel_removed`; the
mirror is `SurvivorSymmetry`; the signed count is `Sawtooth.legendre_count`),
and Dirichlet's theorem for the columns (`DirichletColumns`).

---

## Candidate formalizations (not yet started)

The scoped items below now appear on [`GRAPH.md`](../GRAPH.md) as planned
nodes (grey dashed boxes), with the outside Lean results they cite drawn as
purple outside-source nodes. Each node's page under `docs/nodes/` records
its planned claims, scope and evidence.

Results from the literature on how survivors spread out, each stated in
wheel terms. All are finite counting statements about the combined cycle,
so they fit the RNS vocabulary directly. Statements marked "checked" held
in a numerical test (4,761 cases: wheel sets drawn from the primes up to 19,
up to 24 equal intervals).

### 65. `BrunTwinCount` — counting the twin multiples of a set of wheels (Brun stage 2)
Take distinct prime wheels and their product. Among the positions 1 to N,
count those where the product divides the position times the position two
further on. In one full cycle of the product there are one such position for
the wheel at 2 and two for every other wheel, multiplied together. So up to
N the count is N times that number divided by the product, off by at most
that number. The proof goes one cycle at a time: full cycles each add the
same amount and the leftover piece adds between nothing and one cycle's worth.
Inside a cycle the positions are the residues of the product; the Chinese
Remainder Theorem splits them into residues of each wheel, and for one wheel
the residue times the residue two further on is zero only at zero and at
minus two (the same residue for the wheel at 2).
- Prior work: Brun (1919); standard in every sieve text.
- Lean: `twin_multiples_count` (with `twin_rho`)
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### 66. `BrunTruncation` — stopping early for a product of shares (Brun stage 3)
Give each wheel a share between zero and one. The share escaping every wheel
is the product of one minus each share. Expand it by inclusion–exclusion and
stop after the sets of at most some number of wheels: stopping at an even
number overestimates, at an odd number underestimates, and the error is at
most the sum, over the sets of one more wheel, of the product of their
shares. That sum is at most the total share raised to that number, divided
by its factorial. Proved by adding one wheel at a time.
- Prior work: Brun (1919); the Bonferroni inequalities for independent events.
- Lean: `truncation_error`, `esymm_power_bound`
- Rests on: Vocabulary only
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### 67. `BrunTwinBound` — Brun's twin bound with every error term (Brun stage 4)
Joins stages 1 to 3. The twin survivors of a set of prime wheels up to N
are at most N times the product of one minus each wheel's twin share, plus
N times the truncation error from stage 3, plus the total number of twin
roots over the sets of wheels used. A wheel's twin share is one half for the
wheel at 2 and two over the wheel otherwise. Also: a twin prime pair whose
smaller member is at least L survives every wheel below L, so the twin prime
pairs up to N are at most L plus the twin survivors of the wheels below L.
- Prior work: Brun (1919).
- Lean: `twin_sifted_bound` (step), `twin_count_le_sifted`
- Rests on: `BrunPureSieve.twin_bonferroni_upper`, `BrunTwinCount.twin_multiples_count`,
  `BrunTruncation.truncation_error` (arrows in `RNSSolutions/Assemble.lean`)
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### 68. `MertensSecond` — the sum of the reciprocals of the primes
The sum of one over each prime up to x is the logarithm of the logarithm of
x, plus a constant, plus a remainder at most a constant over the logarithm of
x. This is an outside claim: PNT+ proves it with explicit constants
(`Mertens.sum_prime_div_eq` with `Mertens.E₂p.abs_le`), and the claim here
asks only for some constants. From it, as a step: the sum is at most the
logarithm of the logarithm plus a constant.
- Prior work: Mertens (1874); PrimeNumberTheoremAnd.
- Lean: `mertens_second_remainder` (outside), `prime_reciprocal_upper` (step)
- Status: the step is clean (standard three axioms); the outside claim is cited, not rebuilt.

### 69. `BrunAnalytic` — how few twin primes there are (Brun stage 5)
For the wheels below L, the product of one minus each twin share is the twin
share of the cycle, so `ShareBounds` bounds it by twice one over the
logarithm of L, squared. Then the choice: with u the eighth root of the
logarithm of N, take the wheels below about e to the u to the sixth and stop
inclusion–exclusion after the sets of about 46 u wheels. Each part of
`BrunTwinBound`'s bound is then at most a small multiple of N over the
logarithm of N to the three halves; in all, from some point on, the twin
prime pairs up to N are at most 5 N over the logarithm of N to the three
halves. The power is more than one, which is what makes the sum of the
reciprocals of the twin primes converge.
- Prior work: Brun (1919), who obtains the sharper power two with a log log
  factor; three halves is what the summation needs.
- Lean: `twin_product_bound`, `twin_prime_count_bound` (steps)
- Rests on: `SurvivorCount`, `ShareBounds`, `BrunTwinBound`, `BrunTruncation`,
  `MertensSecond`. In `RNSSolutions/Assemble.lean` every arrow inside the
  network is joined; the one remaining hypothesis is the outside claim
  `MertensSecond.mertens_second_remainder`.
- Status: Clean. Proved; `#print axioms` shows only the standard three (GitHub
  Actions build, 2026-11-06).

### Where to look first

Places already found to hold results, statements or tools these items need.
Check here before searching again. Links pinned to a commit were current on
2026-11-04.

**Lean projects with proofs to cite (as purple outside-source nodes)**
- [PrimeNumberTheoremAnd (PNT+)](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  — Mertens' three theorems (`PrimeNumberTheoremAnd/IEANTN/Mertens.lean`;
  third theorem `E₃.bound''`), the prime number theorem (`pi_alt'`,
  `chebyshev_asymptotic` in `Consequences.lean`), Dirichlet's theorem in
  prime-number-theorem form (`WeakPNT_AP` in `Wiener.lean`), the Selberg
  sieve (`Mathlib/NumberTheory/Sieve/`) and Brun-Titchmarsh
  (`BrunTitchmarsh.lean`). Builds on Lean v4.35.0. For: CeilingOvershoot,
  BirdseySchay, any future Brun's-theorem work.
- [openai/math](https://github.com/openai/math) — the quadratic bound on
  Jacobsthal's function, with Lean proof and preprint (September 2026). For:
  BlockingRuns; replaces Jacobsthal as a target of our own.
- [plby/lean-proofs](https://github.com/plby/lean-proofs) — Lean proofs of
  Hooley's exponential distribution of survivor gaps (Erdős 235) and the
  Montgomery-Vaughan gap moments (Erdős 220), both about survivors of
  primorial cycles. Possible outside sources for future gap nodes.
- plby/lean-proofs also proves Gafni and Tao's theorem (Erdős 682): almost
  every prime gap contains a survivor of every wheel smaller than the gap
  (`src/latest/ErdosProblems/Erdos682.lean`; paper arXiv:2508.06463).
  Drawn on the graph as the outside source `RoughInPrimeGaps`.
- [30k30/scholia](https://github.com/30k30/scholia) — Lean glue from
  Jacobsthal's function to Erdős 687 (blocking runs). For: BlockingRuns.
- [epoch-research/LeanOpenProblems-results](https://github.com/epoch-research/LeanOpenProblems-results)
  — the outside proof of the 2, 4, 2, 4, 2 gap-block statement. For:
  InadmissibleOccurrences (our proof should come from Admissibility).
- [Selberg sieve package](https://reservoir.lean-lang.org/@amellendijk/selbergSieve)
  (Arend Mellendijk) — now folded into PNT+; the natural base for Brun's
  theorem.

**Statement collections (to align statements and avoid duplicate work)**
- [DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  — statements with `sorry`, tagged open or solved, often linking outside
  proofs. Relevant files: `OEIS/1223.lean`, `ErdosProblems/854.lean`,
  `682.lean`, `687.lean`, `970.lean`, `235.lean`, `220.lean`,
  `GreensOpenProblems/46.lean`, and `Wikipedia/` (Dickson, TwinPrimes,
  Schinzel, Legendre, Oppermann, Andrica, Brocard).
- [IEANTN](https://github.com/teorth/IEANTN) — the network model this
  repository follows; its nodes are explicit analytic bounds (Dusart's
  prime gaps, Rosser-Schoenfeld, Chebyshev constants). Dusart2018 and
  PrimeInterval are possible cited inputs for gap-conjecture nodes.
- [Lean evaluation leaderboard](https://lean-lang.org/eval/problems/brun_constant_converges/)
  — poses Brun's theorem as a problem; status not yet checked.

**Mathlib at the pinned commit (`0df444a`, v4.33.1), confirmed present**
- `log_add_one_le_harmonic`, `harmonic_le_one_add_log`
  (`NumberTheory/Harmonic/Bounds.lean`) — for ShareBounds.
- `eulerMascheroniConstant` and `tendsto_harmonic_sub_log`
  (`NumberTheory/Harmonic/EulerMascheroni.lean`).
- Chebyshev bounds: `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge`,
  `Chebyshev.pi_le_log4_mul_div`, `Chebyshev.pi_ge`
  (`NumberTheory/Chebyshev.lean`).
- Abel summation (`NumberTheory/AbelSummation.lean`).
- `not_summable_one_div_on_primes` (`NumberTheory/SumPrimeReciprocals.lean`).
- Dirichlet's theorem: `Nat.forall_exists_prime_gt_and_modEq`
  (`NumberTheory/LSeries/PrimesInAP.lean`).
- `DirichletCharacter.LFunction_apply_one_ne_zero`
  (`NumberTheory/LSeries/Nonvanishing.lean`) — for GermainCriterion.
- Not in Mathlib: Mertens' theorems, the prime number theorem (use PNT+).

**Papers**
- Lehmer, *The distribution of totatives*, Canad. J. Math. 7 (1955) —
  even splits, symmetry, spread bounds, closed forms. For: LehmerSplit,
  SurvivorSymmetry, SpreadBounds, LehmerExcess, UniformSubdivision.
- Germain, *The distribution of totatives*, Canad. Math. Bull. 48 (2005) —
  exact criterion via odd characters. For: GermainCriterion.
- Codecà and Nair, *Extremal values of Δ(x, N)*, Canad. Math. Bull. 41
  (1998) — largest gap from the proportional share; cites Vijayaraghavan
  (1951), Erdős (1958, 1960), Suryanarayana. For: LargestGap and the
  column-imbalance question. Its primorial conjecture must be read from
  the original.
- Grob and Schmitt, arXiv:1905.03117 (2019); Grob, arXiv:2107.06950 (2021)
  — residue-vector presentation, twin survivor counts.
- Birdsey and Schay, arXiv:1906.09220 (2019) — twin share and the
  one-correction heuristic. For: TwinShare, BirdseySchay.
- Pritchard (1981, 1982) — the wheel sieve and the next-prime-square
  ceiling.
- The full verified list, with links, is in the project's prior-work
  references document on claude.ai.

**Tier 1: elementary, and they strengthen existing nodes**
- **Done (node `LehmerSplit`, 2026-11-04).** **Lehmer's even split, general form** (Lehmer 1955, Thm 4). If one wheel
  leaves remainder 1 on division by a chosen number of intervals, the
  survivors of the cycle split evenly across that many equal intervals
  (endpoints rounded down). `uniform_subdivision` becomes the special case
  of the rotating prime minus one intervals. Checked.
- **Done (node `LehmerSplit`).** **Column form of Lehmer's split.** With wheels 2 and 3 frozen, if some
  wheel leaves remainder 1 on division by the least common multiple of 6
  and the number of intervals, each column splits evenly too. Checked.
- **Done (node `SurvivorSymmetry`, 2026-11-04).** **Mirror symmetry** (Lehmer 1955, Thm 1; Grob and Schmitt 2019, Thm 2).
  A position survives exactly when its reflection in the cycle survives.
  (The interval-by-interval form needs exact endpoints; with rounded-down
  endpoints it fails, as the test showed.)
- **Done (node `SpreadBounds`; rests on `Sawtooth`).** **Spread bound** (Lehmer 1955, Thms 9-10). Any two equal intervals'
  survivor counts differ by at most two to the number of wheels. Checked.
- **Done (node `SpreadBounds`; rests on `Sawtooth`'s column count).** **Column-imbalance bound.** With wheels 2 and 3 frozen, the two columns'
  survivor counts up to any point differ by at most two to the number of
  remaining wheels. Proof by inclusion-exclusion with the column sign.
  Checked.
- **Done (node `ColumnAction`; proved directly, no overlap needed).** **Column action of a wheel.** Multiplying by a prime keeps the 6n-1 and
  6n+1 columns in place if it leaves remainder 1 on division by 6, and
  swaps them if it leaves remainder 5. (The lemma behind both column forms;
  check overlap with `ColumnStructure` first.)

**Tier 2: elementary but longer**
- **Divisibility case of the even split** (Lehmer 1955, Thm 2): if the
  square of the number of intervals divides the modulus, the split is even.
  Only applies to moduli with repeated factors, so outside pure wheel
  cycles; low priority.
- **Done (node `LehmerExcess`; rests on `Sawtooth`).** Proved in the form of Codecà and Nair 1998, Thm 2 (read from the paper). **Lehmer's closed form for 6n-1-type wheels** (Lehmer 1955, Thm 8; not yet checked against Lehmer): when
  every wheel leaves remainder one less than the number of intervals, the
  excess in the first intervals has an exact formula. The 6n-1 side of
  Lehmer's picture, and the natural partner to `uniform_subdivision_minus_side`.
- **Adding one wheel at most doubles the largest gap** (Codecà and Nair
  1998, Thm 1(i), read from the paper): for a squarefree cycle length above
  1 and a new prime not dividing it, the largest gap between the survivor
  count and its proportional share, after adding the prime, is at most twice
  the old one minus one over the new prime. Needs rational numbers. Planned
  in node `LargestGap` over three sessions: (1) the largest gap as a maximum
  over survivor positions, proved equal to their supremum over real
  fractions; (2) their inequalities (7) and (8) by the neighbouring-survivor
  argument; (3) the case split that gives Thm 1(i). Their identity (I) is
  `UniformSubdivision.one_wheel_removed` written as a gap.

**Tier 3: needs heavier Mathlib**
- **Mean-square identity** (Codecà and Nair 1998, Thm 3(i); moved up from
  Tier 2 on 2026-11-04): the average squared gap over the survivor positions
  is one twelfth of two to the number of wheels times the coprime share,
  plus one sixth. The proof integrates the squared gap over the cycle (their
  Thm 4(v), via Franel's formula for integrals of products of sawtooth
  functions), so it needs real integration.
- **Done (node `GermainCriterion`, 2026-11-05; standard axioms only): the "if" half for two wheels, `two_wheel_split_of_remainders`, rests on `Sawtooth`. Analytic input built the same day: L(chi, 0) != 0 for odd primitive chi (Mathlib only), and the weighted residue sum is nonzero, resting on `HurwitzZetaZero` (Apostol Thm 12.13; Mathlib stops short of s = 0, so the network proves it). The character transform (Germain's (3.1), in remainder form, no sawtooth needed) built the same day. Germain's (3.2) for characters that are not primitive built the same day, through Mathlib's LFunction_changeLevel at s = 0. The inversion over characters (3.3) and Germain's Proposition 3.1 (residues coprime to the number of parts) built the same day, through Mathlib's character orthogonality. Cor 3.2 (every residue, wheels only) built the same day. Prop 2.1 (c), (d), (e) built the same day in remainder form ((a) and (b) concern repeated primes, which the network's cycle never has); also recorded that Germain's Theorem 1.1 as printed fails for the wheel 2 with 2 parts, where no odd character exists. Germain's Theorem 1.1 for distinct prime wheels with a wheel not dividing the number of parts built the same day in survivor form (`germain_theorem`, rests on `Sawtooth` and `HurwitzZetaZero`), by dropping the dividing wheels one at a time (`split_iff_nondividing_wheels`). The "only if" half, Erdős's conjecture (Hall-Shiu), built the same day by Cor 1.4 proof (ii) (`two_wheel_remainders_of_split`), with character separation through odd characters (`eq_one_of_odd_characters`); Cor 1.4 in full is `two_wheel_split_iff`. Both rest on `Sawtooth` and `HurwitzZetaZero`, and so on Mathlib alone. Note: Hall-Shiu's ordering-of-residues theorem is false as stated for composite moduli (8 parts, residues 1, 3, 5); Germain's Cor 1.4 checked against 120,660 direct cases.** **Germain's exact criterion** (Germain 2005, Thm 1.1): the survivors
  split evenly across a given number of equal intervals exactly when every
  odd Dirichlet character for that number takes the value 1 at some wheel.
  The proof uses the nonvanishing of Dirichlet L-functions at 1; check
  what Mathlib provides before scoping.
  Staged in three: (1) the sawtooth identity, now node `Sawtooth`;
  (2) the character transform and the "if" direction; (3) the "only if"
  direction, first with nonzero constants for odd characters as a named
  hypothesis.

**From Birdsey and Schay (arXiv:1906.09220, 2019)**
- **Done (node `TwinShare`; rests on `SurvivorCount` only).** **Twin share of the cycle** (Tier 1). Among all survivors of a cycle, the
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

**Survivor share bounds (Tier 1)** — done (node `ShareBounds`; rests on `SurvivorCount`).
- **The survivor share shrinks at least like one over the logarithm.**
  After the wheels up to a given prime, the share of the cycle that
  survives is at most one over the logarithm of that prime plus one.
  Proof: the reciprocal of the share expands into a sum over all numbers
  built from those primes, which includes every number up to the last
  wheel, so it is at least the harmonic sum; Mathlib's
  `log_add_one_le_harmonic` bounds that below by the logarithm. Also
  forces infinitely many primes (link to `Infinitude`). Checked for
  wheels up to 200,000.
- **The twin share shrinks at least like one over the logarithm squared.**
  The share of the cycle surviving the twin pattern is at most twice the
  square of the bound above, since each twin factor is at most the square
  of the plain one. Checked for wheels up to 200,000.

**From DeepMind's formal-conjectures (statements there, proofs not in it)**
- **Done (node `InadmissibleOccurrences`).** **Inadmissible patterns sit next to their blocking wheel** (Tier 1). If
  an offset pattern covers every position on some wheel, then every
  starting point where all members are prime has that wheel's prime as a
  member, so the pattern occurs only finitely often. Corollary: the
  prime-gap block 2, 4, 2, 4, 2 occurs only once, at 5, 7, 11, 13, 17, 19
  (offsets 0, 2, 6, 8, 12, 14 cover every position on the wheel of size
  5). This is `OeisA1223.conjecture` in formal-conjectures, listed as
  solved with the proof hosted elsewhere. Builds on `Admissibility`.
- **Done (node `GapCertificate`, 2026-11-05; standard axioms only): also refutes de Polignac's 1849 guess.** **The Lacampagne-Selfridge counterexample** (Tier 2; Erdos Problem 854).
  For the wheels up to 13 (cycle 30030), the gaps between consecutive
  survivors take every even value up to the largest gap, 22, except 20.
  Erdos had expected every even value up to the largest gap to appear.
  Checked numerically; the smaller cycles 30, 210 and 2310 and the next
  one, 510510, miss no even value. Needs a certificate-style proof as in
  `ShieldCertificates`, since `native_decide` would add an extra axiom and
  plain `decide` is likely too slow at 5,760 survivors. Also includes the
  easy fact that every gap is even.
- **Done in part (node `BlockingRuns`, 2026-11-04; standard axioms only): the first claim, longest blocked run = largest survivor gap − 1, rests on `CRT`.** **Blocking runs and the largest survivor gap** (Tier 2; Erdos Problem
  687, Green's Open Problem 46). Choosing one blocked position on each
  wheel up to a prime is the same as covering a run of consecutive
  numbers by one residue class per prime. The longest run that can be
  covered is one less than the largest gap between survivors of the
  cycle. Proof: a setting of the wheels is a shift of the cycle (Chinese
  Remainder Theorem). formal-conjectures already proves the easy bound
  that a covered run is shorter than the cycle
  (`Erdos687.lt_primorial_of_isCoveredByResidues`). The quadratic bound on
  Jacobsthal's function itself was proved, with Lean, by OpenAI in
  September 2026 (cited in `ErdosProblems/970.lean`); cite it, do not
  redo it.

**From PrimeNumberTheoremAnd (PNT+)**
- **Done (node `CeilingOvershoot`, 2026-11-06; standard axioms only): a step
  from `MertensThird.mertens_third` and `PrimeNumberTheorem.prime_number_theorem`,
  both stated in Lean and taken as named hypotheses pointing at PNT+.
  `MertensThird` holds the error-term form as the outside claim and proves
  the limit form from it.** **The overshoot at the ceiling** (Tier 2). With the wheels up to the
  square root of a bound, the survivor share times the bound, divided by
  the number of primes up to the bound, tends to twice e to the minus
  Euler's constant (about 1.1229). A short step from two results PNT+
  proves with no `sorry`: Mertens' third theorem (`E₃.bound''` in
  `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`, with error of order one
  over the logarithm squared) and the prime number theorem
  (`chebyshev_asymptotic` in `Consequences.lean`). PNT+ builds on Lean
  v4.35.0 and this repository on v4.33.1, so take the two results as
  cited hypotheses pointing at PNT+, following the network's pattern,
  rather than adding PNT+ as a dependency.
- PNT+ also proves Mertens' first and second theorems, so the elementary
  share bounds above are not the only route; they remain useful because
  they hold for every wheel with explicit constants.

**Open question (not a formalization target yet)**
- How large the column imbalance can get as wheels are added. Computed up
  to the wheel at 23 (maxima 2, 3, 5, 8, 12, 18); the untwisted analogue is
  studied by Codecà and Nair 1998 and grows at a similar rate. No paper on
  the column version found so far.
