/-
The three definitions below are copied verbatim from google-deepmind/formal-conjectures, file
`FormalConjectures/Wikipedia/RegularPrimes.lean` (commit 2207c54d0d).

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).

The two theorems are new: they reduce FC's `infinitude_of_irregularprimes` to Kummer's criterion
(in fact to its easy direction), using Jensen's theorem from `Jensen.lean`.
-/
import Jensen

open scoped NumberField

variable (p : ℕ)

namespace RegularPrimes

/-- A natural prime number `p` is regular if `p` is coprime with the order of the class group
of the `p`-th cyclotomic field. -/
noncomputable def IsRegularPrime [Fact p.Prime] : Prop :=
  p.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField p ℚ)

/-- The set of regular primes. -/
def regularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), @IsRegularPrime p ⟨hp⟩ }

/-- The set of irregular primes. -/
def irregularPrimes : Set ℕ := { p | ∃ (hp : Nat.Prime p), ¬ @IsRegularPrime p ⟨hp⟩ }

/-- FC's `infinitude_of_irregularprimes`, assuming only the easy direction of Kummer's criterion:
if `p` divides the numerator of some `B_k` (`k` even, `2 ≤ k ≤ p − 3`), then `p` is irregular. -/
theorem infinitude_of_irregularprimes_of_kummer
    (hK : ∀ (p : ℕ) [Fact p.Prime],
      (∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num) →
        ¬ IsRegularPrime p) :
    irregularPrimes.Infinite :=
  WolstenholmeHarmonic.jensen_bernoulli.mono fun p hp => ⟨hp.1, @hK p ⟨hp.1⟩ hp.2⟩

/-- FC's `infinitude_of_irregularprimes` follows from FC's `isRegularPrime_iff_Bernoulli`
(Kummer's criterion). -/
theorem infinitude_of_irregularprimes_of_iff
    (hK : ∀ (p : ℕ) [Fact p.Prime], IsRegularPrime p ↔
      ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num) :
    irregularPrimes.Infinite :=
  infinitude_of_irregularprimes_of_kummer fun p hp ⟨k, hk, hev, hdvd⟩ hreg =>
    (@hK p hp).1 hreg k hk hev hdvd

end RegularPrimes
