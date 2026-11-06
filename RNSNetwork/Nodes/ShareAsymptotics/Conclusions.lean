/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MertensThird.Conclusions
import RNSNetwork.Nodes.TwinConstant.Conclusions

/-!
# ShareAsymptotics — how fast the survivor and twin shares of the cycle shrink

Take the wheels up to `n` and their combined cycle. `ShareBounds` shows the
share of the cycle that survives is at most one over the logarithm of the
bound, and the twin share at most twice the square of that. Here are the true
rates, from Mertens' third theorem:

* the survivor share times the logarithm of `n` tends to e to the minus
  Euler's constant (about 0.5615), so the `ShareBounds` bound is sharp up to
  that factor;
* the twin share times the logarithm of `n` squared tends to twice the odd
  twin product (the product over the odd primes of one minus one over the
  prime minus 1, squared; about 0.6602) times e to the minus twice Euler's
  constant, about 0.4162.

Numerically, at `n` a million: 0.56144 (limit 0.56146) and 0.41618 (limit
0.41621).

Proof: `RNSSolutions/ShareAsymptotics.lean`. Rests on `SurvivorCount`,
`TwinShare` and `MertensThird`. Metadata: `formalization.yaml`.
-/

namespace RNS.ShareAsymptotics

open Filter Topology

/-- The factor of the odd twin product at `n`: one minus one over (`n` minus 1)
squared at an odd prime, 1 otherwise. -/
noncomputable def odd_twin_factor (n : ℕ) : ℝ :=
  if n.Prime ∧ n ≠ 2 then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1

/-- The odd twin product, over the odd primes, of one minus one over (the
prime minus 1) squared (about 0.6602; half the classical twin-prime constant). -/
noncomputable def odd_twin_product : ℝ := ∏' n : ℕ, odd_twin_factor n

/-- **The survivor share's rate.** With the wheels up to `n`, the share of the
cycle that survives, times the logarithm of `n`, tends to e to the minus
Euler's constant. -/
def survivor_share_asymptotic : Prop :=
  Tendsto (fun n : ℕ => ((wheel_survivors_gen {0} (n + 1)).card : ℝ) /
      (primorial_modulus (n + 1) : ℝ) * Real.log n)
    atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

/-- **The twin share's rate.** With the wheels up to `n`, the twin share of the
cycle, times the logarithm of `n` squared, tends to twice the odd twin product
times e to the minus Euler's constant, squared. -/
def twin_share_asymptotic : Prop :=
  Tendsto (fun n : ℕ => ((wheel_survivors (n + 1)).card : ℝ) /
      (primorial_modulus (n + 1) : ℝ) * Real.log n ^ 2)
    atTop (𝓝 (2 * odd_twin_product * Real.exp (-Real.eulerMascheroniConstant) ^ 2))

/-- **The odd twin product, linked.** Twice the odd twin product is the
classical twin-prime constant of `TwinConstant` (about 1.3203), which that node
proves equal to the Hardy–Littlewood constant of the twin pattern. -/
def odd_twin_product_eq_classical : Prop :=
  2 * odd_twin_product = RNS.TwinConstant.twin_prime_classical_constant

/-- **The twin share's rate, with the classical constant.** With the wheels up
to `n`, the twin share of the cycle times the logarithm of `n` squared tends to
the twin-prime constant times e to the minus Euler's constant, squared. -/
def twin_share_asymptotic_classical : Prop :=
  Tendsto (fun n : ℕ => ((wheel_survivors (n + 1)).card : ℝ) /
      (primorial_modulus (n + 1) : ℝ) * Real.log n ^ 2)
    atTop (𝓝 (RNS.TwinConstant.twin_prime_classical_constant *
      Real.exp (-Real.eulerMascheroniConstant) ^ 2))

end RNS.ShareAsymptotics
