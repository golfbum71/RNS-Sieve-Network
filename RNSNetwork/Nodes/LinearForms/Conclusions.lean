/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# LinearForms — Dickson's conjecture gives Sophie Germain primes

Admissibility so far handles only shift patterns, where every member is the
starting number plus an offset. A Sophie Germain prime needs a number and
twice it plus one to be prime together: two linear forms with different
slopes. This node extends admissibility to finite systems of linear forms,
shows the Sophie Germain pair passes it, and so derives infinitely many
Sophie Germain primes from Dickson's conjecture.

**Dickson's conjecture is open.** It is stated below and appears only as the
hypothesis of a claim.

Proof: `RNSSolutions/LinearForms.lean`; rests on no other node. Metadata:
`formalization.yaml`.

Source of record: `rns_sieve_6_parts_J_K.lean`, Part K.
-/

namespace RNS.LinearForms

/-- The linear form `(a, b)`, meaning `a·n + b`, is blocked at remainder `r`
modulo `p` when it is divisible by `p` whenever the starting number leaves
remainder `r`. -/
def form_blocked_at (ℓ : Nat × Nat) (p r : Nat) : Prop :=
  (ℓ.1 * r + ℓ.2) % p = 0

/-- A finite system of linear forms is admissible when, at every prime, some
remainder leaves every form unblocked. -/
def is_admissible_lin (L : Finset (Nat × Nat)) : Prop :=
  ∀ p, p.Prime → ∃ r < p, ∀ ℓ ∈ L, ¬ form_blocked_at ℓ p r

/-- **Dickson's conjecture** (open, never claimed): an admissible finite
system of linear forms with positive leading coefficients is simultaneously
prime infinitely often. -/
def LinearForms_conjecture : Prop :=
  ∀ L : Finset (Nat × Nat), (∀ ℓ ∈ L, 0 < ℓ.1) → is_admissible_lin L →
    {n : Nat | ∀ ℓ ∈ L, (ℓ.1 * n + ℓ.2).Prime}.Infinite

/-- The Sophie Germain conjecture (open): infinitely many Sophie Germain
primes. -/
def sophie_germain_conjecture : Prop :=
  {p : Nat | sophie_germain p}.Infinite

/-- The Sophie Germain system: the forms `n` (as `1·n + 0`) and `2n + 1`. -/
def sophieGermainSystem : Finset (Nat × Nat) := {(1, 0), (2, 1)}

/-- **The Sophie Germain pair is admissible.** -/
def sophieGermainSystem_admissible : Prop :=
  is_admissible_lin sophieGermainSystem

/-- **Dickson's conjecture would give infinitely many Sophie Germain
primes.** -/
def sophie_germain_of_LinearForms_conjecture : Prop :=
  LinearForms_conjecture → sophie_germain_conjecture

end RNS.LinearForms
