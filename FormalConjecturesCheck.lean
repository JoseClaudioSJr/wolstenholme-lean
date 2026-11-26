/-
The definition and the three theorem statements below are copied verbatim from
google-deepmind/formal-conjectures, file
`FormalConjectures/Wikipedia/WolstenholmePrime.lean` (commit 2207c54d0d).

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).

Only the proofs (short, referring to `WolstenholmeHarmonic`) and the statement `glaisher` are new.
This file is the `Solution` module of the Palomar submission (see `Challenge.lean`).
-/
module

public import WolstenholmeHarmonic

@[expose] public section

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

/-- `Σ_{k=1}^{n} 1/k² = harmonic2 n`. -/
theorem sum_Icc_one_div_sq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2 = WolstenholmeHarmonic.harmonic2 n := by
  induction n with
  | zero => simp [WolstenholmeHarmonic.harmonic2]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, WolstenholmeHarmonic.harmonic2_succ]
    push_cast
    ring

/-- **Glaisher's congruence** (1900): `3·H_{p−1,2} ≡ 2p·B_{p−3} (mod p²)` for primes `p ≥ 5`. -/
theorem glaisher (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ((p ^ 2 : ℕ) : ℤ) ∣
      (3 * ∑ k ∈ Finset.Icc 1 (p - 1), (1 : ℚ) / (k : ℚ) ^ 2 - 2 * p * bernoulli (p - 3)).num := by
  have := Fact.mk hp
  rw [sum_Icc_one_div_sq]
  exact WolstenholmeHarmonic.glaisher h5

end WolstenholmePrime
