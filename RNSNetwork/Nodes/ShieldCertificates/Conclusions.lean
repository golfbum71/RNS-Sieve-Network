/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# ShieldCertificates — certifying primes, and why prime runs stop

If a set of wheels covers every prime up to the square root of the ceiling,
surviving them proves primality: for single numbers, evenly spaced runs in
either direction, and offset patterns. Conversely, a wheel that does not
divide the spacing must block one term of any run as long as the wheel
itself; that caps the length of real prime runs and forces the
Lagrange–Waring condition on them. Between a cutoff and its square, a number
is prime exactly when no wheel below the cutoff divides it.

Proof: `RNSSolutions/ShieldCertificates.lean`. The certificate and window
claims assume `SquareRootShield.square_root_shield`; the two Lagrange–Waring
claims for real prime runs assume `Admissibility.ap_offsets_admissible_iff`;
the other obstruction claims rest on no other node. Metadata:
`formalization.yaml`.

Source of record: `rns_sieve_6.lean`, "Shield Certificates" sections.
-/

namespace RNS.ShieldCertificates

/-- **The shield certificate.** If a finite set of wheels contains every
prime whose square is at most the ceiling, then a number from 2 up to the
ceiling that no smaller wheel in the set divides is prime. -/
def prime_of_shield_cover : Prop :=
  ∀ (X n : Nat) (P : Finset Nat), 2 ≤ n → n ≤ X →
    (∀ q, q.Prime → q * q ≤ X → q ∈ P) → (∀ q ∈ P, q < n → ¬ q ∣ n) → n.Prime

/-- **The active wheels cover the ceiling.** When the ceiling is below the
square of the bound, every prime whose square is at most the ceiling is one
of the active wheels. -/
def active_primes_cover : Prop :=
  ∀ X L : Nat, X < L * L → ∀ q, q.Prime → q * q ≤ X → q ∈ active_primes L

/-- **The certificate for any finite family of numbers.** -/
def family_prime_of_shield_cover : Prop :=
  ∀ (ι : Type) (s : Finset ι) (f : ι → Nat) (X : Nat) (P : Finset Nat),
    (∀ q, q.Prime → q * q ≤ X → q ∈ P) → (∀ i ∈ s, 2 ≤ f i) → (∀ i ∈ s, f i ≤ X) →
    (∀ i ∈ s, ∀ q ∈ P, q < f i → ¬ q ∣ f i) → ∀ i ∈ s, (f i).Prime

/-- **Certifying a forward run** (a, a plus the spacing, …), given its last
term is within the ceiling. -/
def forward_ap_prime_of_active_shield : Prop :=
  ∀ a d k X L : Nat, X < L * L → a + (k - 1) * d ≤ X →
    (∀ i ∈ Finset.range k, 2 ≤ a + i * d) →
    (∀ i ∈ Finset.range k, ∀ q ∈ active_primes L, q < a + i * d → ¬ q ∣ a + i * d) →
    ∀ i ∈ Finset.range k, (a + i * d).Prime

/-- **Certifying a backward run** (a, a minus the spacing, …), given its first
term is within the ceiling. -/
def backward_ap_prime_of_active_shield : Prop :=
  ∀ a d k X L : Nat, X < L * L → a ≤ X →
    (∀ i ∈ Finset.range k, 2 ≤ a - i * d) →
    (∀ i ∈ Finset.range k, ∀ q ∈ active_primes L, q < a - i * d → ¬ q ∣ a - i * d) →
    ∀ i ∈ Finset.range k, (a - i * d).Prime

/-- **Certifying an offset pattern** (a starting number plus each offset). -/
def tuple_prime_of_active_shield : Prop :=
  ∀ (n X L : Nat) (T : Finset Nat), X < L * L →
    (∀ t ∈ T, 2 ≤ n + t) → (∀ t ∈ T, n + t ≤ X) →
    (∀ t ∈ T, ∀ q ∈ active_primes L, q < n + t → ¬ q ∣ n + t) →
    ∀ t ∈ T, (n + t).Prime

/-- **The wheel obstruction.** A prime wheel that does not divide the spacing
divides some term among any run at least as long as the wheel. -/
def ap_hits_wheel : Prop :=
  ∀ a d k q : Nat, q.Prime → ¬ q ∣ d → q ≤ k → ∃ i ∈ Finset.range k, q ∣ a + i * d

/-- **Run-length bound.** An all-prime forward run starting above a prime
wheel that does not divide the spacing is shorter than that wheel. -/
def ap_prime_run_length_lt_of_lt_start : Prop :=
  ∀ a d k q : Nat, q.Prime → ¬ q ∣ d → q < a →
    (∀ i ∈ Finset.range k, (a + i * d).Prime) → k < q

/-- **Lagrange–Waring, for actual prime runs.** If an all-prime forward run
starts above its own length, every prime up to that length divides the
spacing. -/
def ap_prime_run_forces_divisibility : Prop :=
  ∀ a d k : Nat, k < a → (∀ i ∈ Finset.range k, (a + i * d).Prime) →
    ∀ p, p.Prime → p ≤ k → p ∣ d

/-- **The two-way window.** From the cutoff up to just below its square, a
number is prime exactly when no prime below the cutoff divides it. -/
def window_prime_iff : Prop :=
  ∀ cutoff n : Nat, cutoff ≤ n → n < cutoff * cutoff →
    (n.Prime ↔ ∀ q ∈ active_primes cutoff, ¬ q ∣ n)

/-- **The two-way window for twin pairs.** -/
def window_twin_iff : Prop :=
  ∀ cutoff n : Nat, cutoff ≤ n → n + 2 < cutoff * cutoff →
    ((n.Prime ∧ (n + 2).Prime) ↔
      ((∀ q ∈ active_primes cutoff, ¬ q ∣ n) ∧ (∀ q ∈ active_primes cutoff, ¬ q ∣ n + 2)))

/-- **The wheel obstruction, backward.** -/
def backward_ap_hits_wheel : Prop :=
  ∀ top step count q : Nat, q.Prime → ¬ q ∣ step → q ≤ count →
    (count - 1) * step ≤ top → ∃ i ∈ Finset.range count, q ∣ top - i * step

/-- **Run-length bound, backward.** -/
def backward_ap_prime_run_length_lt_of_above : Prop :=
  ∀ top step count q : Nat, q.Prime → ¬ q ∣ step → q < top - (count - 1) * step →
    (∀ i ∈ Finset.range count, (top - i * step).Prime) → count < q

/-- **Lagrange–Waring, backward.** -/
def backward_ap_prime_run_forces_divisibility : Prop :=
  ∀ top step count : Nat, count < top - (count - 1) * step →
    (∀ i ∈ Finset.range count, (top - i * step).Prime) →
    ∀ p, p.Prime → p ≤ count → p ∣ step

end RNS.ShieldCertificates
