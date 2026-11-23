/-
The two definitions and the statement `erdos_291.variants.steinerberger_generalization` below are
copied verbatim from google-deepmind/formal-conjectures, file
`FormalConjectures/ErdosProblems/291.lean` (commit 2207c54d0d).

Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (see LICENSE).

The proof is new.
-/
module

public import Kummer

@[expose] public section

/-!
# Erdős Problem 291: Steinerberger's criterion

Write `L_n = lcm(1, …, n)` and `1 + 1/2 + ⋯ + 1/n = a_n / L_n`. For a prime `p ≤ n`, with
`e = ⌊log_p n⌋` and `k = ⌊n / pᵉ⌋` (the leading digit of `n` in base `p`):

    p ∣ gcd(a_n, L_n)  ⇔  p ∣ num(1 + 1/2 + ⋯ + 1/k).

Proof. `L_n = pᵉ·L'` with `p ∤ L'`. In `a_n = Σ_{j ≤ n} L_n / j`, the terms with `pᵉ ∤ j` are
divisible by `p`, and the terms `j = pᵉ·m` (`1 ≤ m ≤ k`) equal `L'/m`. So
`a_n ≡ L'·Σ_{m ≤ k} 1/m (mod p)`, and `p ∣ L_n`.
-/

open Finset WolstenholmeHarmonic

namespace Erdos291

/--
$L_n$ is the least common multiple of $\{1,\ldots,n\}$.
-/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

/--
$a_n$ is defined by $\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

/-- If `p^(v+1) ∤ j` but `p^(v+1) ∣ j·c`, then `p ∣ c`. -/
theorem dvd_of_pow_succ_dvd_mul {p v j c : ℕ} (hp : p.Prime) (hj0 : j ≠ 0) (hc0 : c ≠ 0)
    (hj : ¬ p ^ (v + 1) ∣ j) (h : p ^ (v + 1) ∣ j * c) : p ∣ c := by
  by_contra hc
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hj0 hc0), Nat.factorization_mul hj0 hc0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hc, add_zero] at h
  exact hj ((hp.pow_dvd_iff_le_factorization hj0).2 h)

/-- `L n > 0`. -/
theorem L_pos (n : ℕ) : 0 < L n := by
  rw [Nat.pos_iff_ne_zero, L, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, rfl⟩
  simp at hx

/-- Every `j ∈ [1, n]` divides `L n`. -/
theorem dvd_L {n j : ℕ} (hj : j ∈ Icc 1 n) : j ∣ L n := by
  unfold L
  exact Finset.dvd_lcm (f := fun x ↦ x) hj

/-- **Steinerberger's criterion** (the Formal Conjectures statement). -/
theorem erdos_291.variants.steinerberger_generalization (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num := by
  intro k
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hn0 : n ≠ 0 := by have := hp.two_le; omega
  -- `e = ⌊log_p n⌋ ≥ 1`, `pᵉ ≤ n < p^(e+1)`, `1 ≤ k < p`
  obtain ⟨e', he'⟩ : ∃ e', Nat.log p n = e' + 1 :=
    ⟨Nat.log p n - 1, by have := Nat.log_pos hp1 hpn; omega⟩
  have hpe : p ^ (e' + 1) ≤ n := he' ▸ Nat.pow_log_le_self p hn0
  have hne : n < p ^ (e' + 1 + 1) := he' ▸ Nat.lt_pow_succ_log_self hp1 n
  have hpe0 : 0 < p ^ (e' + 1) := pow_pos hp.pos _
  have hk : k = n / p ^ (e' + 1) := by simp only [k, he']
  have hk1 : 1 ≤ k := by rw [hk]; exact (Nat.le_div_iff_mul_le hpe0).2 (by simpa using hpe)
  have hkp : k < p := by
    rw [hk]
    refine (Nat.div_lt_iff_lt_mul hpe0).2 ?_
    rw [← pow_succ']; exact hne
  -- `L n = pᵉ·L'`
  have hLpos := L_pos n
  obtain ⟨L', hL'⟩ : p ^ (e' + 1) ∣ L n :=
    dvd_L (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hpe0.ne', hpe⟩)
  have hpL : p ∣ L n := by rw [hL']; exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  -- `p ∤ L'`: otherwise every `j ≤ n` would divide `L n / p`
  have hL'p : ¬ p ∣ L' := by
    rintro ⟨c, rfl⟩
    have hdiv : p ^ (e' + 1 + 1) ∣ L n := ⟨c, by rw [hL', pow_succ]; ring⟩
    have hall : ∀ j ∈ Icc 1 n, j ∣ L n / p := by
      intro j hj
      obtain ⟨d, hd⟩ := dvd_L hj
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.1 hj).1; omega
      have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; omega
      have hjn : ¬ p ^ (e' + 1 + 1) ∣ j := fun h => by
        have := Nat.le_of_dvd (by omega) h
        have := (Finset.mem_Icc.1 hj).2
        omega
      obtain ⟨d', rfl⟩ := dvd_of_pow_succ_dvd_mul hp hj0 hd0 hjn (hd ▸ hdiv)
      rw [hd, show j * (p * d') = p * (j * d') by ring, Nat.mul_div_cancel_left _ hp.pos]
      exact dvd_mul_right j d'
    have hLd : L n ∣ L n / p := Finset.lcm_dvd (f := fun x ↦ x) hall
    have hpos : 0 < L n / p := Nat.div_pos (Nat.le_of_dvd hLpos hpL) hp.pos
    have := Nat.le_of_dvd hpos hLd
    have := Nat.div_lt_self hLpos hp1
    omega
  -- `a n ≡ L'·Σ_{m ≤ k} 1/m (mod p)`
  have key : ((a n : ℕ) : ZMod p) = (L' : ZMod p) * ∑ m ∈ Icc 1 k, (m : ZMod p)⁻¹ := by
    unfold a
    rw [Nat.cast_sum, ← Finset.sum_filter_add_sum_filter_not (Icc 1 n) (fun j => p ^ (e' + 1) ∣ j)]
    -- terms with `pᵉ ∤ j` vanish
    have h0 : ∑ j ∈ (Icc 1 n).filter (fun j => ¬ p ^ (e' + 1) ∣ j),
        ((L n / j : ℕ) : ZMod p) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      obtain ⟨d, hd⟩ := dvd_L hj.1
      have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.1 hj.1).1; omega
      have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; omega
      have hpd : p ∣ d := dvd_of_pow_succ_dvd_mul hp hj0 hd0 hj.2 (hd ▸ ⟨L', hL'⟩)
      rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hj0), ZMod.natCast_eq_zero_iff]
      exact hpd
    rw [h0, add_zero, Finset.mul_sum]
    -- terms `j = pᵉ·m`, `1 ≤ m ≤ k`, equal `L'/m`
    refine Finset.sum_nbij' (fun j => j / p ^ (e' + 1)) (fun m => p ^ (e' + 1) * m) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjn⟩, m, rfl⟩ := hj
      rw [Finset.mem_Icc, Nat.mul_div_cancel_left _ hpe0, hk]
      refine ⟨?_, (Nat.le_div_iff_mul_le hpe0).2 (by rw [mul_comm]; exact hjn)⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hj1
      · exact hm
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hpe0.ne' (by omega))
      · have := (Nat.le_div_iff_mul_le hpe0).1 (hk ▸ hm.2)
        rw [mul_comm]; exact this
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact Nat.mul_div_cancel' hj.2
    · intro m _
      exact Nat.mul_div_cancel_left _ hpe0
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjn⟩, m, rfl⟩ := hj
      rw [Nat.mul_div_cancel_left _ hpe0]
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at hj1
        · exact hm
      have hmk : m ≤ k := by
        rw [hk]; exact (Nat.le_div_iff_mul_le hpe0).2 (by rw [mul_comm]; exact hjn)
      have hm0 : (m : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        intro h; have := Nat.le_of_dvd (by omega) h; omega
      -- `m ∣ L'`, since `pᵉ·m ∣ pᵉ·L'`
      obtain ⟨q, hq⟩ : m ∣ L' := by
        have h := dvd_L (n := n) (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2
          (mul_ne_zero hpe0.ne' (by omega)), hjn⟩)
        rw [hL'] at h
        exact Nat.dvd_of_mul_dvd_mul_left hpe0 h
      rw [hL', Nat.mul_div_mul_left _ _ hpe0, hq, Nat.mul_div_cancel_left _ (by omega),
        Nat.cast_mul, mul_comm (m : ZMod p), mul_assoc, mul_inv_cancel₀ hm0, mul_one]
  -- the harmonic sum `H_k` reduces to `Σ_{m ≤ k} m⁻¹` in `ZMod p`
  have hcop : ∀ i ∈ Icc 1 k, Nat.Coprime ((1 : ℚ) / i).den p := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    rw [one_div, Rat.inv_natCast_den, if_neg (by omega)]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
  have hH : ratToZMod p (∑ i ∈ Icc 1 k, (1 : ℚ) / i) = ∑ m ∈ Icc 1 k, (m : ZMod p)⁻¹ := by
    rw [ratToZMod_sum _ _ hcop]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [one_div, ratToZMod_inv_natCast _ (by
      have := hcop i hi
      rwa [one_div, Rat.inv_natCast_den, if_neg (by have := (Finset.mem_Icc.1 hi).1; omega)]
        at this)]
  have hden : ¬ p ∣ (∑ i ∈ Icc 1 k, (1 : ℚ) / i).den :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_den_sum _ _ hcop).symm
  have hL'0 : (L' : ZMod p) ≠ 0 := by rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact hL'p
  rw [Nat.dvd_gcd_iff, and_iff_left hpL, ← ZMod.natCast_eq_zero_iff, key,
    ← ratToZMod_prime_eq_zero_iff _ hden, hH, mul_eq_zero, or_iff_right hL'0]

end Erdos291
