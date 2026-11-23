/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.FieldSizeTimes.Conclusions
import Mathlib.RingTheory.Coprime.Basic

/-!
# TightFromBlockedRun — a run of blocked numbers makes a tight lonely runner

Take the consecutive speeds 1 up to one less than the number of runners. They
are tight: some time gives every runner exactly one part (one over the number
of runners) of a lap of room, and no time gives more (Dirichlet's pigeonhole,
`consecutive_covered`). Now speed up one of them, the runner of speed `r`, to
`m` times its speed. If every number from (number of runners − r) up to
m × (number of runners − r) − 1 shares a factor with `r` (a run of positions
blocked by the wheels of `r`, `blocked_run`), the new set is still tight
(`single_acceleration_tight`). The proof replaces one runner at a time
(`one_step_replacement`, Goddyn and Wong's Lemma 3.2): at a time when only the
sped-up runner could have been close, either a smaller wheel of `r` takes its
place, or an unchanged runner whose speed is the inverse remainder for `r`
does, and the run of blocked numbers is exactly what keeps such a runner
unchanged. A blocked run is shorter than the speed that blocks it
(`blocked_run_short`), which keeps the sped-up runner off the fence post at the
time one over the number of runners.

Goddyn and Wong 2006, Theorem 2.1 (sufficiency) and Lemma 3.2, at times that
are fractions. "Never strictly lonely" here means: at every fractional time some
runner is at most one part of a lap from the start.

Proof: `RNSSolutions/TightFromBlockedRun.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.TightFromBlockedRun

open RNS.PileUpLock

/-- The point `y / M` of a lap is **at most `1 / n` of a lap from the start**. -/
def near (n M : ℕ) (y : ℤ) : Prop :=
  (n : ℤ) * (y % (M : ℤ)) ≤ M ∨ (n : ℤ) * ((M : ℤ) - y % (M : ℤ)) ≤ M

/-- **Never strictly lonely**: at every time that is a fraction, some speed in
`V` is at most `1 / n` of a lap from the start. -/
def never_strictly_lonely (n : ℕ) (V : Finset ℤ) : Prop :=
  ∀ M : ℕ, 0 < M → ∀ k : ℤ, ∃ v ∈ V, near n M (v * k)

/-- **A blocked run**: every number from `lo` to `hi` shares a factor with `r`
(is blocked by one of the wheels of `r`). -/
def blocked_run (r lo hi : ℤ) : Prop :=
  ∀ b : ℤ, lo ≤ b → b ≤ hi → Int.gcd r b ≠ 1

/-- The consecutive speeds `1, …, n - 1` with the speed `r` replaced by `m * r`. -/
def accelerated (n : ℕ) (r m : ℤ) : Finset ℤ :=
  insert (m * r) ((Finset.Icc (1 : ℤ) ((n : ℤ) - 1)).erase r)

/-- **The consecutive speeds are never strictly lonely** (Dirichlet). -/
def consecutive_covered : Prop :=
  ∀ n : ℕ, 2 ≤ n → never_strictly_lonely n (Finset.Icc (1 : ℤ) ((n : ℤ) - 1))

/-- **One-step replacement** (Goddyn and Wong, Lemma 3.2). If a speed set is
never strictly lonely, then so is the set with `r` replaced by `m * r`,
provided each `r / p` (for a prime wheel `p` of `r`) is in the new set, and each
remainder `q` sharing no factor with `r` is the remainder of some speed of the
new set between `m * (n - r)` and `n + r`. -/
def one_step_replacement : Prop :=
  ∀ (n : ℕ) (X : Finset ℤ) (r m : ℤ), 2 ≤ n → 1 ≤ r → r ≤ n → 2 ≤ m →
    never_strictly_lonely n X →
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ r → r / p ∈ insert (m * r) (X.erase r)) →
    (∀ q : ℤ, IsCoprime q r → ∃ b ∈ insert (m * r) (X.erase r),
      m * (n - r) ≤ b ∧ b ≤ n + r ∧ r ∣ b - q) →
    never_strictly_lonely n (insert (m * r) (X.erase r))

/-- **A blocked run is shorter than the speed blocking it**: any `r` consecutive
numbers include one leaving remainder 1 for `r`. -/
def blocked_run_short : Prop :=
  ∀ r lo hi : ℤ, 1 ≤ r → blocked_run r lo hi → hi - lo + 1 ≤ r - 1

/-- **A blocked run gives a tight set** (Goddyn and Wong, Theorem 2.1,
sufficiency). If the numbers from `n - r` to `m * (n - r) - 1` are all blocked by
the wheels of `r`, then the consecutive speeds with `r` sped up to `m * r` are
`n - 1` distinct speeds, lonely at the time `1 / n`, and never strictly lonely. -/
def single_acceleration_tight : Prop :=
  ∀ (n : ℕ) (r m : ℤ), 2 ≤ n → 1 ≤ r → r ≤ (n : ℤ) - 1 → 2 ≤ m →
    blocked_run r ((n : ℤ) - r) (m * ((n : ℤ) - r) - 1) →
    (accelerated n r m).card = n - 1 ∧ lonely_at (accelerated n r m) n 1 ∧
      never_strictly_lonely n (accelerated n r m)

end RNS.TightFromBlockedRun
