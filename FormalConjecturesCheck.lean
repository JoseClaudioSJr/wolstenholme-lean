/-
The definition and the three theorem statements below are copied verbatim from
google-deepmind/formal-conjectures, file
`FormalConjectures/Wikipedia/WolstenholmePrime.lean` (commit 2207c54d0d).

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).

Only the proofs (short, referring to `WolstenholmeHarmonic`) are new.
-/
import WolstenholmeHarmonic

namespace WolstenholmePrime

theorem wolstenholme_theorem (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  have := Fact.mk hp
  have h5 : 5 ≤ p := by
    by_contra hc
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp (by decide)
  exact WolstenholmeHarmonic.wolstenholme_theorem_mod_p_cube h5

def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

theorem wolstenholme_harmonic (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num :=
  WolstenholmeHarmonic.wolstenholme_harmonic p

theorem wolstenholme_bernoulli (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑p ∣ (bernoulli' (p - 3)).num :=
  WolstenholmeHarmonic.wolstenholme_bernoulli p

end WolstenholmePrime
