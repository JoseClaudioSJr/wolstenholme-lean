/-
The definition and the two theorem statements below are copied verbatim from
google-deepmind/formal-conjectures, file
`FormalConjectures/Wikipedia/WolstenholmePrime.lean` (commit 2207c54d0d).

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).

Only the proofs (one line each, referring to `WolstenholmeHarmonic`) are new.
-/
import WolstenholmeHarmonic

namespace WolstenholmePrime

def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

theorem wolstenholme_harmonic (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num :=
  WolstenholmeHarmonic.wolstenholme_harmonic p

theorem wolstenholme_bernoulli (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑p ∣ (bernoulli' (p - 3)).num :=
  WolstenholmeHarmonic.wolstenholme_bernoulli p

end WolstenholmePrime
