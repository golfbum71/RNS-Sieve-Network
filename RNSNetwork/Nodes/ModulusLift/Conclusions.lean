/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PileUpLock.Conclusions

/-!
# ModulusLift — a check passed at one cycle carries up to every multiple of it

The residue sieve of the record proofs works modulus by modulus. A list of
speeds is good at a denominator when some time with that denominator is lonely.
A good time with one denominator is also a good time with any multiple of it
(stretch the numerator by the same factor), and whether a list is good depends
only on the speeds' remainders. So a list whose remainders were already good at
a smaller cycle never needs checking at a larger cycle built on it
(`bad_lists_lift`); likewise a list whose all-but-one share a factor with the
smaller cycle still shares it with the larger one (`proper_lifts`). This is the
same climb as rotating one more wheel into the combined cycle.

Trakulthongchai 2026, Definition 6 and Lemma 7 (arXiv 2511.22427), the sieve
that took the record to nine and ten runners. Uses only the vocabulary of
`PileUpLock`.

Proof: `RNSSolutions/ModulusLift.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.ModulusLift

open RNS.PileUpLock

/-- A list (multiset) of speeds is **good at the denominator `d`** for a field
of `n` runners when some time with denominator `d` puts every speed at least
`1 / n` of a lap from the start. -/
def good_at (n d : ℕ) (R : Multiset ℤ) : Prop :=
  ∃ t : ℤ, ∀ r ∈ R, far n d (r * t)

/-- **Stretching the cycle.** The point `c * y` of a lap of `c * d` parts is the
same place as the point `y` of a lap of `d` parts. -/
def far_scale : Prop :=
  ∀ (n d c : ℕ) (y : ℤ), 0 < c → (far n (c * d) ((c : ℤ) * y) ↔ far n d y)

/-- **Good at a cycle, good at every multiple.** -/
def good_lifts : Prop :=
  ∀ (n d d' : ℕ) (R : Multiset ℤ), 0 < d' → d ∣ d' → good_at n d R → good_at n d' R

/-- **Only remainders matter for being good.** -/
def good_residues : Prop :=
  ∀ (n d : ℕ) (R : Multiset ℤ), good_at n d (R.map (fun r => r % (d : ℤ))) ↔ good_at n d R

/-- **Bad lists at a larger cycle lie over bad lists at the smaller.** If the
remainders of a list for the cycle `d` are good, so are its remainders for any
multiple `d'` of `d`. -/
def bad_lists_lift : Prop :=
  ∀ (n d d' : ℕ) (R : Multiset ℤ), 0 < d' → d ∣ d' →
    good_at n d (R.map (fun r => r % (d : ℤ))) → good_at n d' (R.map (fun r => r % (d' : ℤ)))

/-- **A shared factor with the cycle carries up.** If a number shares a factor
with the cycle `d`, it shares one with every multiple of `d`. -/
def proper_lifts : Prop :=
  ∀ (A : ℤ) (d d' : ℕ), d ∣ d' → Int.gcd A d ≠ 1 → Int.gcd A d' ≠ 1

end RNS.ModulusLift
