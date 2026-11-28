/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Nat.ModEq

/-!
# CollatzHub — the Collatz map seen from the 6n-2 hub

Geo's picture of the Collatz (3x+1) map on the columns of the 6n±1 wheel.
Every odd step of the Collatz map lands on a number of the form 6n-2, the
**hub**. Followed from the hub until it returns to the hub, the map takes one
of three loops, decided by n:

* n even: through the 6n-1 column and back, the hub index grows by 3/2
  (the **bad loop**);
* n leaving remainder 1 on division by 4: through 6n+2 and 6n+1 and back,
  the index is multiplied by about 3/4;
* n leaving remainder 3 on division by 4: through 6n+2 straight back, the
  index is multiplied by about 1/4.

So the Collatz map becomes the **hub map** on the index n:
n ↦ 3n/2, (3n+1)/4 or (n+1)/4. The Collatz conjecture says every positive
index reaches the fixed point 1 (the 4-2-1 cycle is the hub 4 = 6·1-2).

Proved here, about this map:

* the three loops really are the Collatz map (`hub_step_tracks_collatz`);
* a run of bad loops from 2^k·m ends exactly at 3^k·m (`run_formula`);
* **exit pairing**: when 3^k·m leaves remainder 1 on division by 4, the run
  from 2^(k+1)·m and the run from 2^k·m meet one loop after they end
  (`exit_pairing`);
* the three backward links: the ladder 4v-1 (in hub values, times 4), the run
  entry 2v/3 and the branch entry (4v-1)/3, are the only ways into a value
  (`predecessors_complete`), the ladder cycles through the remainders on
  division by 3 (`ladder_entry`, `ladder_cycle`), and the run-exit pair is
  built into the ladder (`pairing_is_ladder`);
* only a bad loop can raise the index, so every peak ends a run
  (`up_only_on_bad_loop`), and every number climbing to a peak divisible by 3
  passes through two thirds of it (`funnel_trunk`);
* in every block of four consecutive indices the next indices add up to
  exactly one less than the block (`fair_block`): the exact form of the
  "fair game" average.

The conjecture itself is stated, never claimed (`collatz_hub_form`).

Proofs: `RNSSolutions/CollatzHub.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.CollatzHub

/-- One step of the Collatz map: halve an even number, send an odd number `x`
to `3x + 1`. -/
def col (x : Nat) : Nat := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The hub map on the index `n` of the hub value `6n - 2`: the index after
one loop from the hub back to the hub. -/
def hubStep (n : Nat) : Nat :=
  if n % 2 = 0 then 3 * n / 2
  else if n % 4 = 1 then (3 * n + 1) / 4
  else (n + 1) / 4

/-- The hub map applied `k` times. -/
def hubIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => hubIter k (hubStep n)

/-- **The three loops are the Collatz map.** For every index `n` at least 1,
following the Collatz map from the hub value `6n - 2`: if `n` is even, two
steps reach `6 · hubStep n - 2`; if `n` leaves remainder 1 on division by 4,
three steps do; if `n` leaves remainder 3, two steps do. -/
def hub_step_tracks_collatz : Prop :=
  ∀ n : Nat, 1 ≤ n →
    (n % 2 = 0 → col (col (6 * n - 2)) = 6 * hubStep n - 2) ∧
    (n % 4 = 1 → col (col (col (6 * n - 2))) = 6 * hubStep n - 2) ∧
    (n % 4 = 3 → col (col (6 * n - 2)) = 6 * hubStep n - 2)

/-- **The run formula.** Starting from `2^k · m`, `k` steps of the hub map
(each a bad loop) end at `3^k · m`. -/
def run_formula : Prop :=
  ∀ k m : Nat, hubIter k (2 ^ k * m) = 3 ^ k * m

/-- **Exit pairing.** If `3^k · m` leaves remainder 1 on division by 4, the
run from `2^(k+1) · m` and the run from `2^k · m` land on the same index one
loop after their runs end. -/
def exit_pairing : Prop :=
  ∀ k m : Nat, (3 ^ k * m) % 4 = 1 →
    hubIter (k + 2) (2 ^ (k + 1) * m) = hubIter (k + 1) (2 ^ k * m)

/-- **The three backward links are the only ones.** If the hub map sends `u`
to `v`, then `u` is the ladder rung `4v - 1`, or `v` is divisible by 3 and
`u` is two thirds of `v` (the run entry), or `v` leaves remainder 1 on
division by 3 and `3u = 4v - 1` (the branch entry). -/
def predecessors_complete : Prop :=
  ∀ u v : Nat, hubStep u = v →
    u = 4 * v - 1 ∨ (v % 3 = 0 ∧ 3 * u = 2 * v) ∨ (v % 3 = 1 ∧ 3 * u = 4 * v - 1)

/-- **The ladder.** For every index `v` at least 1, the rung `4v - 1` drops
into `v` in one loop, and its hub value is exactly 4 times the hub value of
`v`. -/
def ladder_entry : Prop :=
  ∀ v : Nat, 1 ≤ v → hubStep (4 * v - 1) = v ∧ 6 * (4 * v - 1) - 2 = 4 * (6 * v - 2)

/-- **The ladder cycles through the remainders on division by 3.** Each rung
leaves remainder one less (on division by 3) than the rung below it. -/
def ladder_cycle : Prop :=
  ∀ v : Nat, 1 ≤ v → (4 * v - 1) % 3 = (v + 2) % 3

/-- **Run entry.** The even index `2j` takes the bad loop to `3j`, so every
multiple of 3 is entered from two thirds of itself. -/
def run_entry : Prop :=
  ∀ j : Nat, hubStep (2 * j) = 3 * j

/-- **The exit pair is built into the ladder.** For every `j`, the branch
entry `4j + 1` reaches `3j + 1` in one loop, and its double `8j + 2` reaches
the same `3j + 1` in two (a bad loop to the next ladder rung, then down it). -/
def pairing_is_ladder : Prop :=
  ∀ j : Nat, hubStep (4 * j + 1) = 3 * j + 1 ∧ hubIter 2 (8 * j + 2) = 3 * j + 1

/-- **Only the bad loop goes up.** If one step of the hub map makes an index
larger, the index was even: every peak is the end of a run. -/
def up_only_on_bad_loop : Prop :=
  ∀ n : Nat, n < hubStep n → n % 2 = 0

/-- **The trunk of a funnel.** If a peak `P` (at least 1) is divisible by 3,
the only smaller index stepping onto it is two thirds of it: every number
that climbs to `P` without passing it goes through `2P/3`. -/
def funnel_trunk : Prop :=
  ∀ u P : Nat, 1 ≤ P → P % 3 = 0 → hubStep u = P → u < P → 3 * u = 2 * P

/-- **The fair block.** For every `k`, the hub map sends the four indices
`4k, 4k+1, 4k+2, 4k+3` to four indices adding up to exactly one less than
they do. -/
def fair_block : Prop :=
  ∀ k : Nat,
    hubStep (4 * k) + hubStep (4 * k + 1) + hubStep (4 * k + 2) + hubStep (4 * k + 3) + 1 =
      4 * k + (4 * k + 1) + (4 * k + 2) + (4 * k + 3)

/-- **The Collatz conjecture in hub form** (open; stated, never claimed): every
index at least 1 reaches the fixed point 1 under the hub map. -/
def collatz_hub_form : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ k : Nat, hubIter k n = 1

end RNS.CollatzHub

/-! ## The counting formula

A mountain is counted by walking up a value's ladder: each rung counts once,
plus everything entering it by a run entry (rung divisible by 3) or a branch
entry (rung leaving remainder 1 on division by 3). The two claims below are
that recursion: one link of it (`counting_step`) and where it stops
(`count_zero_at_ceiling`). Unrolled along the ladder (whose rungs grow by a
factor of 4), they give the ladder sum. -/

namespace RNS.CollatzHub

/-- `u` reaches `v` under the hub map with every index along the way, `v`
included, below the ceiling `B`. -/
abbrev reachesBelow (B u v : Nat) : Prop :=
  ∃ k, hubIter k u = v ∧ ∀ j ≤ k, hubIter j u < B

open Classical in
/-- The tree of `v` below the ceiling `B`: every index that reaches `v`
without ever reaching `B`. -/
noncomputable def ancBelow (B v : Nat) : Finset Nat :=
  (Finset.range B).filter (fun u => reachesBelow B u v)

/-- **The counting formula, one link.** For an index `v` below the ceiling
`B` that is not on a cycle (the hub map never brings it back to itself), the
size of its tree below `B` is 1 (itself), plus the tree of its ladder rung
`4v - 1`, plus the tree of its run entry `2v/3` if `v` is divisible by 3, plus
the tree of its branch entry `(4v - 1)/3` if `v` leaves remainder 1 on
division by 3. -/
def counting_step : Prop :=
  ∀ B v : Nat, v < B → (∀ k, hubIter (k + 1) v ≠ v) →
    (ancBelow B v).card =
      1 + (ancBelow B (4 * v - 1)).card
        + (if v % 3 = 0 then (ancBelow B (2 * v / 3)).card else 0)
        + (if v % 3 = 1 then (ancBelow B ((4 * v - 1) / 3)).card else 0)

/-- **Where the count stops.** At or above the ceiling a value's tree below
the ceiling is empty, so the ladder sum ends at the last rung below `B`. -/
def count_zero_at_ceiling : Prop :=
  ∀ B v : Nat, B ≤ v → (ancBelow B v).card = 0

end RNS.CollatzHub

/-! ## The unrolled ladder sum

Walking the counting formula up the ladder: a mountain's size is a sum over
the ladder rungs below the ceiling, each rung counting itself plus its run
entry's tree or its branch entry's tree. -/

namespace RNS.CollatzHub

/-- Rung `i` of the ladder above `v`: `v`, then `4v - 1`, then `4(4v - 1) - 1`,
and so on. -/
def rung : Nat → Nat → Nat
  | v, 0 => v
  | v, i + 1 => rung (4 * v - 1) i

/-- What one ladder rung `r` adds to the count below the ceiling `B`: the rung
itself, plus the tree of its run entry `2r/3` if `r` is divisible by 3, plus
the tree of its branch entry `(4r - 1)/3` if `r` leaves remainder 1 on division
by 3. -/
noncomputable def rungCount (B r : Nat) : Nat :=
  1 + (if r % 3 = 0 then (ancBelow B (2 * r / 3)).card else 0)
    + (if r % 3 = 1 then (ancBelow B ((4 * r - 1) / 3)).card else 0)

/-- **The ladder is powers of 4 in hub values.** For an index `v` at least 1,
the hub value of rung `i` is `4^i` times the hub value of `v`. -/
def rung_hub_value : Prop :=
  ∀ v i : Nat, 1 ≤ v → 6 * rung v i - 2 = 4 ^ i * (6 * v - 2)

/-- **The ladder sum.** For an index `v` not on a cycle whose first `L` ladder
rungs lie below the ceiling `B` and whose rung `L` does not, the size of its
tree below `B` is the sum, over those `L` rungs, of what each rung adds. -/
def ladder_sum : Prop :=
  ∀ B v L : Nat, (∀ i < L, rung v i < B) → B ≤ rung v L →
    (∀ k, hubIter (k + 1) v ≠ v) →
    (ancBelow B v).card = (Finset.range L).sum (fun i => rungCount B (rung v i))

end RNS.CollatzHub

/-! ## Smaller peaks inside a mountain -/

namespace RNS.CollatzHub

/-- **The smaller peaks of a mountain.** Take the tree of any `v` below a
ceiling `B` (a mountain when `v` is two thirds of its peak). A member `q` ends a
run inside it (it is odd and some even member steps onto it by a bad loop)
exactly when `q` leaves remainder 3 on division by 6. So the smaller peaks of a
mountain are counted by its members leaving remainder 3 on division by 6. -/
def sub_peak_rule : Prop :=
  ∀ B v q : Nat, q ∈ ancBelow B v →
    (q % 6 = 3 ↔ (q % 2 = 1 ∧ ∃ u ∈ ancBelow B v, u % 2 = 0 ∧ hubStep u = q))

end RNS.CollatzHub

/-! ## Free steps of the staircase -/

namespace RNS.CollatzHub

/-- **Free steps.** A record peak (the end of a run, an odd index) leaving
remainder 5 on division by 16 is beaten three loops later (a three-quarter drop,
then two bad loops: `16j + 5` reaches `27j + 9`), and one leaving remainder 13
is beaten two loops later (a three-quarter drop, then one bad loop: `16j + 13`
reaches `18j + 15`). So a peak ending in 5 or 13 on division by 16 is never a
final peak. -/
def free_step : Prop :=
  ∀ j : Nat, hubIter 3 (16 * j + 5) = 27 * j + 9 ∧ hubIter 2 (16 * j + 13) = 18 * j + 15

end RNS.CollatzHub

/-! ## Blocks of ones in the row number -/

namespace RNS.CollatzHub

/-- **The block hand-off.** Write a `6n+1` number whose row `n` ends in a block
of at least three binary ones as `48A − 5` (here `n + 1 = 8A`). Up, halve, up,
halve, halve (five steps) take it to `54A − 5`, the `6n+1` number of the row
whose `n + 1` is `9A`: nine eighths as big, with three fewer ones at the end. -/
def block_handoff : Prop :=
  ∀ A : Nat, 0 < A → col^[5] (48 * A - 5) = 54 * A - 5

/-- **The block chain.** If the row's `n + 1` is `2^(3t + L) · m`, then `t`
hand-offs (`5t` steps) take its `6n+1` number to the `6n+1` number of the row
whose `n + 1` is `9^t · 2^L · m`. -/
def block_chain : Prop :=
  ∀ t L m : Nat, 0 < m →
    col^[5 * t] (6 * (2 ^ (3 * t + L) * m) - 5) = 6 * (9 ^ t * (2 ^ L * m)) - 5

/-- **Blocks of ones that settle their row.** Take a row whose `n` ends in a 0
followed by a block of ones (`n + 1` is a power of 2 times an odd `m`). With
2, 5, 8, 11 or 14 ones (`3t + 2`, `t` at most 4) its `6n+1` number is below
itself after `5t + 6` steps, and with 3 or 6 ones (`3t`, `t` = 1 or 2) after
`5t + 3` steps, whatever the higher digits are. -/
def block_of_ones_drops : Prop :=
  ∀ t m : Nat, m % 2 = 1 →
    (t ≤ 4 → col^[5 * t + 6] (6 * (2 ^ (3 * t + 2) * m) - 5) < 6 * (2 ^ (3 * t + 2) * m) - 5) ∧
    (1 ≤ t → t ≤ 2 → col^[5 * t + 3] (6 * (2 ^ (3 * t) * m) - 5) < 6 * (2 ^ (3 * t) * m) - 5)

end RNS.CollatzHub

/-! ## One-drop mountains -/

namespace RNS.CollatzHub

/-- **The climb formula, step by step.** From `2^j · a − 1`, `j` climbs (up, then
halve, `2j` steps) end at `3^j · a − 1`: each climb turns one factor of 2 into a
factor of 3. -/
def climb_formula : Prop :=
  ∀ j a : Nat, col^[2 * j] (2 ^ j * a - 1) = 3 ^ j * a - 1

/-- **Halving down.** `h` halvings take `2^h · c` to `c`. -/
def halving_formula : Prop :=
  ∀ h c : Nat, col^[h] (2 ^ h * c) = c

/-- **One-drop mountains.** A number `2^j · m − 1` climbs to `3^j · m − 1`. If that
top is `2^h · c` (that is, `3^j · m = 2^h · c + 1`), the next `h` steps halve it to
`c`; and when `3^j · m + 2^h ≤ 2^(j+h) · m` (the halvings outweigh the
climb), `c` is below the start: the mountain meets the tide in a single drop.
The condition `3^j · m = 2^h · c + 1` says that the last `h` binary digits of `m`
are those of the 2-adic number `1/3^j`, a repeating pattern. -/
def one_drop_tide : Prop :=
  ∀ j h m c : Nat, 3 ^ j * m = 2 ^ h * c + 1 → 3 ^ j * m + 2 ^ h ≤ 2 ^ (j + h) * m →
    col^[2 * j + h] (2 ^ j * m - 1) = c ∧ c < 2 ^ j * m - 1

end RNS.CollatzHub

/-! ## Building a mountain block by block -/

namespace RNS.CollatzHub

/-- **One block.** A number `2^j · m − 1` climbs `j` times and drops `d` halvings,
landing on `c`, whenever its top `3^j · m − 1` is `2^d · c`: `2j + d` steps. -/
def block_step : Prop :=
  ∀ j d m c : Nat, 3 ^ j * m = 2 ^ d * c + 1 → col^[2 * j + d] (2 ^ j * m - 1) = c

/-- **Where a block lands.** If `3^j · m + 2^d = 2^(d + j₂) · m₂ + 1`, the block
(climb `j`, drop `d`) lands on `2^(j₂) · m₂ − 1`: the start of the next block, a
number with `j₂` trailing binary ones (when `m₂` is odd). -/
def block_landing : Prop :=
  ∀ j d j₂ m m₂ : Nat, 0 < m₂ → 3 ^ j * m + 2 ^ d = 2 ^ (d + j₂) * m₂ + 1 →
    col^[2 * j + d] (2 ^ j * m - 1) = 2 ^ j₂ * m₂ - 1

/-- **A new block's ending is built from the previous one.** Two starts `m` and
`m'` that satisfy the same block equation `3^j · m + E = 2^D · m₂` (with
`E = 2^d − 1`, `D = d + j₂` for a block landing as above) agree in their last
`D + t` binary digits exactly when their landing points `m₂` and `m₂'` agree in
their last `t`. So the ending that makes the whole mountain is the ending for the
first block, `D` digits, followed by the next block's ending carried back through
the block: no digit is lost or left free, because 3 is odd. -/
def block_ending_lift : Prop :=
  ∀ j D E t m m' m₂ m₂' : Nat, 3 ^ j * m + E = 2 ^ D * m₂ → 3 ^ j * m' + E = 2 ^ D * m₂' →
    (m ≡ m' [MOD 2 ^ (D + t)] ↔ m₂ ≡ m₂' [MOD 2 ^ t])

/-- **Two blocks in a row.** A climb `j`, drop `d` landing on `2^(j₂) · m₂ − 1`,
followed by a climb `j₂`, drop `d₂` landing on `c`, takes `(2j + d) + (2j₂ + d₂)`
steps from `2^j · m − 1` to `c`. -/
def two_blocks : Prop :=
  ∀ j d j₂ d₂ m m₂ c : Nat, 0 < m₂ → 3 ^ j * m + 2 ^ d = 2 ^ (d + j₂) * m₂ + 1 →
    3 ^ j₂ * m₂ = 2 ^ d₂ * c + 1 →
    col^[(2 * j₂ + d₂) + (2 * j + d)] (2 ^ j * m - 1) = c

end RNS.CollatzHub

/-! ## The cycle equation -/

namespace RNS.CollatzHub

/-- The shape of the first `n` steps from `x`: `true` for an odd step (up), `false`
for a halving. -/
def parityWord (x : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => (x % 2 == 1) :: parityWord (col x) n

/-- Number of odd steps in a shape. -/
def oddCount : List Bool → Nat
  | [] => 0
  | true :: w => oddCount w + 1
  | false :: w => oddCount w

/-- Number of halvings in a shape. -/
def halvingCount : List Bool → Nat
  | [] => 0
  | true :: w => halvingCount w
  | false :: w => halvingCount w + 1

/-- The constant `c` of a shape, built from the order of its steps alone. -/
def shapeConst : List Bool → Nat
  | [] => 0
  | true :: w => 3 ^ oddCount w + shapeConst w
  | false :: w => 2 * shapeConst w

/-- **Where a shape lands.** After any `n` steps, with `U` odd steps and `K`
halvings in its shape, `2^K` times the number reached is `3^U · x + c`, where `c`
depends only on the order of the steps. -/
def shape_landing : Prop :=
  ∀ n x : Nat, 2 ^ halvingCount (parityWord x n) * col^[n] x =
    3 ^ oddCount (parityWord x n) * x + shapeConst (parityWord x n)

/-- **The cycle equation.** If `n` steps bring `x` back to itself, then
`(2^K − 3^U) · x = c` for its shape: the start of a cycle is the fraction
`c / (2^K − 3^U)`, so a cycle of a given shape exists only if that fraction is a
whole number. -/
def cycle_equation : Prop :=
  ∀ n x : Nat, col^[n] x = x →
    (2 ^ halvingCount (parityWord x n) - 3 ^ oddCount (parityWord x n)) * x =
      shapeConst (parityWord x n)

/-- **Testing a shape.** The known loop 1 → 4 → 2 → 1, gone round twice, has shape
up, halve, halve, up, halve, halve, with `c = 7` and `2^4 − 3^2 = 7`: start 1.
The shape climb 2, drop 3 (up, halve, up, halve, halve, halve) has `c = 5`, and
`5/7` is not whole, so no number has that shape as a cycle. -/
def cycle_shape_tests : Prop :=
  shapeConst [true, false, false, true, false, false] = 7 ∧
  shapeConst [true, false, true, false, false, false] = 5 ∧
  ∀ x : Nat, parityWord x 6 = [true, false, true, false, false, false] → col^[6] x ≠ x

end RNS.CollatzHub

/-! ## Shadows of the negative cycles -/

namespace RNS.CollatzHub

/-- **The −17 hand-off.** On the negative numbers the map has the cycle
−17 → −50 → −25 → … → −17 (7 odd steps, 11 halvings). A positive number that
agrees with −17 in its last 11 binary digits, `2048 y − 17`, follows that cycle's
18 steps once and lands on `2187 y − 17`: it grows by 2187/2048 and keeps agreeing
with −17 in 11 fewer digits. (The climb formula is the same thing for −1, ×3/2 per
digit, and the block hand-off for −5, ×9/8 per three digits.) -/
def neg17_handoff : Prop :=
  ∀ y : Nat, 0 < y → col^[18] (2048 * y - 17) = 2187 * y - 17

/-- **The −17 chain.** `t` hand-offs: `2048^t · y − 17` reaches `2187^t · y − 17`
after `18 t` steps. -/
def neg17_chain : Prop :=
  ∀ t y : Nat, 0 < y → col^[18 * t] (2048 ^ t * y - 17) = 2187 ^ t * y - 17

end RNS.CollatzHub
