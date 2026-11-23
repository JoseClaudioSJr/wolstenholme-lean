/-
The definition `IsWolstenholmePrime` and the theorem statements `wolstenholme_theorem`,
`wolstenholme_harmonic` and `wolstenholme_bernoulli` are copied verbatim from
google-deepmind/formal-conjectures, file `FormalConjectures/Wikipedia/WolstenholmePrime.lean`
(commit 2207c54d0d).

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
module

public import Mathlib

@[expose] public section

/-!
# Wolstenholme primes: the advertised statements

This is the statement surface of the Palomar submission: it imports only Mathlib, and every
theorem is stated with `sorry`. The proofs are in `FormalConjecturesCheck.lean` (the Solution
module), which imports the development in `WolstenholmeHarmonic.lean`.

Throughout, `C(2p−1, p−1)` is `(2 * p - 1).choose (p - 1)`, `H_{p−1} = 1 + 1/2 + ⋯ + 1/(p−1)`
is Mathlib's `harmonic (p - 1)`, and `B_k` is a Bernoulli number. Mathlib's `bernoulli'` has
`B₁ = +1/2` and `bernoulli` has `B₁ = −1/2`; they agree at every even index, in particular at
`p − 3` for odd `p`.
-/

namespace WolstenholmePrime

/-- **Wolstenholme's theorem** (1862): for every prime `p > 3`,
`C(2p−1, p−1) ≡ 1 (mod p³)`. -/
theorem wolstenholme_theorem (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  sorry

/-- A **Wolstenholme prime** is a prime `p > 7` with `C(2p−1, p−1) ≡ 1 (mod p⁴)`, i.e. one for
which Wolstenholme's congruence holds one power of `p` further. (The only known ones are 16843
and 2124679.) -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

/-- **Harmonic characterization**: `p` is a Wolstenholme prime iff `p > 7` is prime and `p³`
divides the numerator of `H_{p−1}`. -/
theorem wolstenholme_harmonic (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num := by
  sorry

/-- **Bernoulli characterization**: `p` is a Wolstenholme prime iff `p > 7` is prime and `p`
divides the numerator of `B_{p−3}`. -/
theorem wolstenholme_bernoulli (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑p ∣ (bernoulli' (p - 3)).num := by
  sorry

/-- **Glaisher's congruence** (1900): for every prime `p ≥ 5`,
`3·(1 + 1/2² + ⋯ + 1/(p−1)²) ≡ 2p·B_{p−3} (mod p²)`, stated as: `p²` divides the numerator of
`3·Σ_{k=1}^{p−1} 1/k² − 2p·B_{p−3}`. -/
theorem glaisher (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ((p ^ 2 : ℕ) : ℤ) ∣
      (3 * ∑ k ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 - 2 * p * bernoulli (p - 3)).num := by
  sorry

end WolstenholmePrime
