# Brocard's conjecture in wheel terms — where each idea meets a known method

Brocard's conjecture: between the squares of two consecutive primes (from 3
on) there are at least four primes. It is open. In this network it appears in
[`GapConjectures`](nodes/GapConjectures.md) as a conjecture that would follow
from a survivor bound nobody has proved.

On 2026-11-11 the conjecture was worked through in wheel terms, starting from
Geoffrey Fischer's own picture of it. Three of his ideas turned out, within a
step or two, to be methods the sieve literature already has under other
names. This page records each idea in its own words first, then the standard
name, then what is the same and what is different, so that a reader (and any
later session) knows which parts of the road are already mapped.

Nothing on this page is a proof of Brocard's conjecture. The exact statements
below are plain logic; the one step that would finish the argument (called
Step C here) is open.

## The picture

- **Window:** the numbers strictly between the base prime's square and the
  next prime's square.
- **Slots (columns):** the window numbers on the 6n−1 and 6n+1 columns
  (wheels 2 and 3 are left out).
- **Wheels (rows):** the primes from 5 up to the base prime, each locked at
  its position at the base prime's square. A wheel puts a mark in every slot
  it divides.
- **Total row:** the number of marks in each slot. A slot totals zero exactly
  when it is prime, because every composite below the next prime's square has
  a wheel as a factor. Brocard's conjecture is therefore: the total row always
  has four or more zeros.
- **Wheel kinds:** *small* (the wheel's square is at most the window length),
  *medium* (not small, and the wheel's cube is below the next prime's
  square), *large* (the rest).
- **Leftover slot:** a slot no small wheel marks.
- **Lone mark:** a mark that is the only one in its slot.

## The three ideas and their standard names

### 1. The grid — Legendre's sieve

**The idea.** Roll every wheel out in its own row across the window, mark
where it blocks, add up each column, and count the zeros.

**Standard name.** The sieve of Eratosthenes on the window, counted the way
Legendre counted it: zeros = slots − marks + meetings of two wheels −
meetings of three + …, an alternating sum over sets of wheels. Stopping the
sum early gives a guaranteed minimum or maximum (Brun's method).

**The same.** The grid is the sieve; the alternating count is Legendre's
formula. At base prime 101: 135 − 133 + 56 − 17 = 41, and the next term
(+1) gives the true 42.

**Different here.** The wheels are locked at their exact positions at the
square, so every term is an exact count for this one window, where the
published method uses a proportional share plus an error. Tests found no
counting advantage from the square start (real windows ranked the same as
random windows of the same length), and the alternating sum can only be made
rigid for the small wheels.

**In the network.** [`BrunPureSieve`](nodes/BrunPureSieve.md) (the
alternating sum, exact when carried all the way, and its early-stopping
inequalities), [`SurvivorCount`](nodes/SurvivorCount.md),
[`ShieldCertificates`](nodes/ShieldCertificates.md) (zero means prime below
the next prime's square).

### 2. Lone marks — Buchstab's identity

**The idea.** Cover the medium and large rows. The slots still at zero are
the leftover slots. Uncover the rows again: a leftover slot is either still
zero (a prime), or it is blocked. Among the blocked ones, those blocked by a
single wheel carry a lone mark, and that wheel times a prime partner is the
slot.

**Standard name.** Buchstab's identity: the survivors of the small wheels
equal the primes plus, for each larger wheel, the positions it is the first
to block. In the window it reads

> leftover slots = primes + one-wheel labels + two-wheel labels,

and the one-wheel labels are exactly the lone marks in the medium and large
rows.

**The same.** The identity itself. It balanced exactly for every base prime
from 5 to 1,300 (at 101: 70 = 42 + 28 + 0; at 1,019: 543 = 290 + 247 + 6).

**Different here.** Each blocked leftover slot has exactly one label (unique
factorization), each wheel's partners form one unbroken run of consecutive
numbers, and that run is shorter than the wheel itself. So the window fails
exactly when the labels number at least the leftover count minus three
(Step B, true for every prime, not only twins). What is missing is Step C: a
ceiling on the labels of at most the leftover count minus four.

**In the network.** [`BuchstabIdentity`](nodes/BuchstabIdentity.md) proves
the identity for any finite sets of prime wheels. Step B is not yet a node.

### 3. The medium-wheel split — the factor-shape split of Harman's sieve

**The idea.** Sort the wheels by size against the window (small, medium,
large) and sort the blocked leftover slots by which wheels can lead them. No
leftover slot has four prime factors, so each is a prime, one wheel times a
prime, or two wheels times a prime; and only a medium wheel can be the
smallest factor of a three-factor slot.

**Standard name.** Harman's sieve: apply Buchstab's identity repeatedly,
split the result into pieces by the sizes of the prime factors, give a count
for the pieces that can be counted, and drop (with the right sign) the pieces
that cannot. Baker, Harman and Pintz used it to show that every window longer
than about the 0.525 power of its starting point holds a prime.

**The same.** The split by factor shape and by the size of the smallest
factor.

**Different here.** Harman's sieve has asymptotic counts for some pieces and
loses a known fraction on the rest; here every piece is exact for the one
window but none has a ceiling yet. The medium wheels cannot be dropped as
negligible: their share of the leftover slots grows (0% at 101, 9.4% at
1,019, 16.9% at 1,000,037).

**In the network.** [`AlmostPrimeWindow`](nodes/AlmostPrimeWindow.md) is the
two-factor case (all wheels below a cutoff, window up to the cutoff's cube);
[`ParityBarrier`](nodes/ParityBarrier.md) says why counting by sieve data
alone cannot separate the pieces.

## Where this leaves the Brocard work

- The road taken so far is the standard one. That is useful to know, not a
  failure: the exact statements (zero means prime, the three slot kinds, the
  identity, Step B) are correct and could become a node feeding
  `GapConjectures`.
- The published methods stop short of Brocard. A Brocard window is about the
  0.5 power of its starting point. Baker, Harman and Pintz (2001) reach
  0.525; a 2023 preprint of Runbo Li claims 0.52 by the same sieve. Even the
  Riemann Hypothesis does not quite reach 0.5.
- The one thing in the picture the published methods do not use is the fixed
  position of every wheel at the square. The tests so far show it gives exact
  positions but no extra primes, so a proof along this road would have to
  work as well for ordinary windows of the same length.
- Position-free ceilings for Step C are known to fail (the best possible
  ceiling from partner-range lengths alone stops working near base prime
  2,000). Whether a ceiling that uses the positions can work is not known.

## The window in formulas (2026-11-14)

On 2026-11-14 the window was worked through again, starting from Geoffrey
Fischer's multiplication-table picture: once the square is fixed, every mark
in the window is a wheel times a row, and the rows are numbers that came
before the window.

**The mark formula.** A wheel at a given distance below the base prime marks
the window at steps 1, 2, 3 and so on. Each mark is the square of (base prime
plus step) minus the square of (distance plus step). The mark is inside the
window exactly when twice the step times the wheel lies strictly between the
distance squared and the distance squared plus the window length. Standard
name: the difference of two squares (Fermat's factorization identity).

**The collision rule.** Two different wheels share a slot only at a multiple
of their product, and the remaining factor is at least 5. So two wheels whose
product is at least a fifth of the next prime's square never share a slot.
Standard name: one term of Legendre's formula.

**Three levels of wheel**, counting each blocked slot under its smallest
wheel. *Large* (cube at least the next prime's square): a mark is new exactly
when its row is prime. *Middle* (above the square root of the next prime,
cube below its square): new exactly when the row is a prime or a product of
two primes each at least the wheel. *Small* (up to the square root of the
next prime): the rest. Standard name: Buchstab's identity with the
factor-shape split of item 3 above, now with exact cutoffs.

These three are checked in Lean in
[`BrocardWindow`](nodes/BrocardWindow.md).

**The cycling-only prediction.** Keep only the shared-slot terms whose cycle
fits inside the window, each at its forced value. For twin primes the sum
collapses to a third of the window length times the sum of the reciprocals of
the primes between the base prime and the window length (plus a small Möbius
sum, minus one). Tested on all 2,992 twin windows with base prime from 11 to
300,000: the prediction exceeded the true count of primes only at bases 29
and 41 (by less than a twentieth of one prime); from 59 on it is always low,
and above 100,000 it is 86 to 89 percent of the true count. This is a test,
not a proof. That the true count stays near the prediction in every window
is open; a guaranteed floor of any fixed fraction would give Brocard's
conjecture from an explicit base prime on. Planned as
[`BrocardPrediction`](nodes/BrocardPrediction.md).

**Where wheel counting stops.** A shared-slot count is forced only when the
product of the wheels is well below the window length. For the large wheels
near the base prime nothing is forced: asking whether a mark is wasted is the
same as asking whether its row is prime (the parity barrier,
[`ParityBarrier`](nodes/ParityBarrier.md)).

The arrangement by distance and step and the cycling-only prediction are
original to this project (Geoffrey Fischer, 2026-11-14); the identities and
the explicit estimates behind the prediction's size are not.

## Working rule recorded with these notes

When an idea is explored: test it on its own terms first and say whether it
holds; then name the known method it resembles, as a translation the author
can refuse; and keep "this is known to fail" separate from "no way to make it
work has been found".

## Sources

- Legendre's sieve: <https://en.wikipedia.org/wiki/Legendre_sieve>
- Buchstab's identity: K. Ford, *Sieve Methods Lecture Notes* (Spring 2023),
  Lemma 3.8, <https://mail.ford126.web.illinois.edu/sieve2023.pdf>
- Harman's sieve: G. Harman, *Prime-Detecting Sieves*, London Mathematical
  Society Monographs 33, Princeton University Press, 2007.
- R. C. Baker, G. Harman, J. Pintz, "The difference between consecutive
  primes, II", Proc. London Math. Soc. (3) 83 (2001) 532–562,
  <https://doi.org/10.1112/plms/83.3.532>
- R. Li, "The number of primes in short intervals and numerical calculations
  for Harman's sieve" (preprint), <https://arxiv.org/abs/2308.04458>
- Brocard's conjecture: <https://en.wikipedia.org/wiki/Brocard%27s_conjecture>
- Fermat's factorization method:
  <https://en.wikipedia.org/wiki/Fermat%27s_factorization_method>
- J. B. Rosser, L. Schoenfeld, "Approximate formulas for some functions of
  prime numbers", Illinois J. Math. 6 (1962) 64–94 (Theorem 5).
- O. Ramaré's explicit bound on the sum of μ(n)/n, as recorded in H. A.
  Helfgott, "The ternary Goldbach problem", <https://arxiv.org/abs/1501.05438>,
  equation (2.21).
- O. Ramaré, S. Zuniga-Alterman, "From explicit estimates for the primes to
  explicit estimates for the Möbius function II",
  <https://arxiv.org/abs/2408.05969>

The window picture, the wheel and slot kinds, the labels and Step B are
original to this project (Geoffrey Fischer, 2026-11-11); the three methods
named above are not.
