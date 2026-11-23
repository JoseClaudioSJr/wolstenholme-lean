import Kummer

/-!
# Jensen's theorem: infinitely many irregular primes (Bernoulli form)

The analytic input — `|B_{2k}| > 1` for large `k` — comes from Euler's formula for `ζ(2k)`
(`hasSum_zeta_nat`) and `(2π)ⁿ/n! → 0`. Everything else is in `Kummer.lean`.
-/

open Filter Topology

namespace WolstenholmeHarmonic

/-- `|B_{2k}| > 1` for all large `k`. -/
theorem one_lt_abs_bernoulli : ∃ K, ∀ k ≥ K, 1 < |bernoulli (2 * k)| :=
  one_lt_abs_bernoulli_of Real.pi Real.pi_pos (fun _ hk => hasSum_zeta_nat hk)
    (FloorSemiring.tendsto_pow_div_factorial_atTop _)

/-- **Jensen (1915).** Infinitely many primes `p` divide the numerator of some Bernoulli number
`B_k` with `k` even and `2 ≤ k ≤ p − 3`. By Kummer's criterion these are exactly the irregular
primes (see `RegularPrimesCheck.lean`). -/
theorem jensen_bernoulli :
    {p : ℕ | p.Prime ∧
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num}.Infinite :=
  infinite_bernoulli_irregular one_lt_abs_bernoulli

end WolstenholmeHarmonic
