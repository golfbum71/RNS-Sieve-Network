/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ShareAsymptotics.Conclusions

/-!
# PolyaCutoff — the wheels that give the Hardy–Littlewood constant exactly

`ShareAsymptotics` shows that with the wheels up to `n` the survivor share of
an admissible pattern, times the logarithm of `n` to the number of offsets,
tends to the Hardy–Littlewood constant times e to minus Euler's constant per
offset. Pólya's observation: stop the wheels earlier, at the range `x` to the
power e to minus Euler's constant (about 0.56). The logarithm of the largest
wheel is then e to minus Euler's constant times the logarithm of the range,
the factors cancel, and the share times the logarithm of the range to the
number of offsets tends to the Hardy–Littlewood constant itself, with no
correction. Compare `CeilingOvershoot`, where wheels up to the square root
overshoot. Banks, Ford and Tao build their random model of the primes at this
cutoff.

Proof: `RNSSolutions/PolyaCutoff.lean`. Rests on `ShareAsymptotics`
(`pattern_share_asymptotic`). Metadata: `formalization.yaml`.
-/

namespace RNS.PolyaCutoff

open Filter Topology

/-- **Pólya's cutoff.** For a nonempty admissible pattern, with the wheels up
to the integer part of `x` to the power e to minus Euler's constant, the share
of the cycle surviving the pattern times the logarithm of `x` to the number of
offsets tends to the pattern's Hardy–Littlewood constant. -/
def polya_cutoff_share : Prop :=
  ∀ T : Finset ℕ, is_admissible T → 1 ≤ T.card →
    Tendsto (fun x : ℕ =>
        ((wheel_survivors_gen T (⌊(x : ℝ) ^ Real.exp (-Real.eulerMascheroniConstant)⌋₊ + 1)).card : ℝ)
          / (primorial_modulus (⌊(x : ℝ) ^ Real.exp (-Real.eulerMascheroniConstant)⌋₊ + 1) : ℝ)
          * Real.log x ^ T.card)
      atTop (𝓝 (hardy_littlewood_constant T))

end RNS.PolyaCutoff
