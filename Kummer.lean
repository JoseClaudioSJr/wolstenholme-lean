module

public import WolstenholmeHarmonic

@[expose] public section

/-!
# Kummer's congruence (weak form) and Jensen's theorem on irregular primes

Building on the `ZMod (p^2)` machinery of `WolstenholmeHarmonic`:

* `sum_pow_eq_p_mul_bernoulli`: `∑_{k=1}^{p-1} k^n ≡ p·B_n (mod p²)` for even `n ≥ 2` with
  `(p − 1) ∤ n` and `p ≥ 5` (Faulhaber + von Staudt–Clausen, for every such `n`, not only `n < p`);
* `voronoi_sq` / `voronoi_mod_p`: Voronoi's congruence
  `(aⁿ − 1)·B_n ≡ n·a^{n−1}·∑_{k=1}^{p-1} ⌊ak/p⌋·k^{n−1} (mod p)`;
* `kummer_dvd`: if `p ∤ n`, `(p − 1) ∤ n` and `p ∣ B_n`, then `p ∣ B_{n mod (p−1)}`
  (the case of Kummer's congruence used by Jensen);
* `dvd_den_bernoulli`: if `(p − 1) ∣ 2k` (`k ≥ 1`), then `p` divides the denominator of `B_{2k}`;
* `exists_irregular_gt` / `infinite_bernoulli_irregular`: Jensen's argument, given that
  `|B_{2k}| > 1` for large `k`;
* `one_lt_abs_bernoulli_of`: that growth, from Euler's formula for `ζ(2k)` (with `π` abstracted;
  the instance with `π` is in `Jensen.lean`).
-/

open Finset

namespace WolstenholmeHarmonic

section Kummer

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `q ≠ p`, the denominator of `1/q` is prime to `pᵃ`. -/
theorem coprime_den_one_div_prime (a : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    Nat.Coprime ((1 : ℚ) / q).den (p ^ a) := by
  have hp : p.Prime := Fact.out
  rw [one_div, Rat.inv_natCast_den, if_neg hq.ne_zero]
  exact Nat.Coprime.pow_right a ((Nat.coprime_primes hq hp).2 hqp)

/-- von Staudt–Clausen, written as an identity. -/
theorem bernoulli_two_mul_eq (k : ℕ) : ∃ z : ℤ, bernoulli (2 * k) = (z : ℚ) -
    ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  exact ⟨z, by rw [hz]; ring⟩

/-- `p` does not divide the denominator of `B_n` when `(p − 1) ∤ n` (von Staudt–Clausen). -/
theorem bernoulli_den_coprime_of_not_dvd (a : ℕ) {n : ℕ} (hn : ¬ (p - 1) ∣ n) :
    Nat.Coprime (bernoulli n).den (p ^ a) := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · obtain ⟨z, hz⟩ := bernoulli_two_mul_eq k
    have hn2 : n = 2 * k := by omega
    rw [hn2, hz, sub_eq_add_neg]
    refine coprime_den_add (coprime_den_intCast z) ?_
    rw [Rat.neg_den]
    refine coprime_den_sum _ _ fun q hq => ?_
    rw [Finset.mem_filter] at hq
    refine coprime_den_one_div_prime a hq.2.1 fun hqp => hn ?_
    rw [hn2, ← hqp]
    exact hq.2.2
  · rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1]; simp
    · have : n = 1 := by obtain ⟨j, hj⟩ := hodd; omega
      subst this
      have hp2 : p ≠ 2 := fun h => hn (by rw [h])
      rw [bernoulli_one,
        show (-1 / 2 : ℚ) = ((-1 : ℤ) : ℚ) * ((1 : ℚ) / ((2 : ℕ) : ℚ)) by push_cast; ring]
      exact coprime_den_mul (coprime_den_intCast _)
        (coprime_den_one_div_prime a Nat.prime_two (Ne.symm hp2))

/-- The same, as non-divisibility. -/
theorem bernoulli_den_not_dvd {n : ℕ} (hn : ¬ (p - 1) ∣ n) : ¬ p ∣ (bernoulli n).den := by
  have hp : p.Prime := Fact.out
  have h := bernoulli_den_coprime_of_not_dvd (p := p) 1 hn
  rw [pow_one] at h
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_comm.1 h)

/-- `p·B_i` is always `p`-integral (the denominator of `B_i` is squarefree). -/
theorem coprime_den_p_mul_bernoulli (a : ℕ) (hp3 : 3 ≤ p) (i : ℕ) :
    Nat.Coprime ((p : ℚ) * bernoulli i).den (p ^ a) := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | hodd
  · obtain ⟨z, hz⟩ := bernoulli_two_mul_eq k
    rw [show i = 2 * k by omega, hz, mul_sub, sub_eq_add_neg, Finset.mul_sum]
    refine coprime_den_add (coprime_den_mul (coprime_den_natCast p) (coprime_den_intCast z)) ?_
    rw [Rat.neg_den]
    refine coprime_den_sum _ _ fun q hq => ?_
    rw [Finset.mem_filter] at hq
    by_cases hqp : q = p
    · rw [hqp, mul_one_div_cancel (by exact_mod_cast hp.ne_zero)]
      simp
    · exact coprime_den_mul (coprime_den_natCast p) (coprime_den_one_div_prime a hq.2.1 hqp)
  · rcases Nat.lt_or_ge 1 i with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1, mul_zero]; simp
    · have : i = 1 := by obtain ⟨j, hj⟩ := hodd; omega
      subst this
      rw [bernoulli_one, show (p : ℚ) * (-1 / 2) = ((-(p : ℤ) : ℤ) : ℚ) * ((1 : ℚ) / ((2 : ℕ) : ℚ))
        by push_cast; ring]
      exact coprime_den_mul (coprime_den_intCast _)
        (coprime_den_one_div_prime a Nat.prime_two (by omega))

/-- Valuation bound: for `m ≥ 3` and `p ≥ 5`, `p^(m−3)/m` is `p`-integral. -/
theorem coprime_den_pow_div (a : ℕ) (hp5 : 5 ≤ p) {m : ℕ} (hm : 3 ≤ m) :
    Nat.Coprime (((p : ℚ) ^ (m - 3)) / (m : ℚ)).den (p ^ a) := by
  have hp : p.Prime := Fact.out
  obtain ⟨e, m', hm', rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.one_lt.ne'
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm
  -- `e + 3 ≤ p^e·m'`: `p^e ≥ 5^e ≥ e + 3` for `e ≥ 1`.
  have he : e + 3 ≤ p ^ e * m' := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using hm
    · have h1 : e + 3 ≤ 5 ^ e := by
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        have : d < 5 ^ d := Nat.lt_pow_self (by norm_num)
        rw [pow_succ]; omega
      calc e + 3 ≤ 5 ^ e := h1
        _ ≤ p ^ e := Nat.pow_le_pow_left hp5 e
        _ ≤ p ^ e * m' := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm'0)
  obtain ⟨N, hN⟩ : ∃ N, p ^ e * m' - 3 = e + N := by
    generalize p ^ e * m' = M at he ⊢
    exact ⟨M - 3 - e, by omega⟩
  rw [hN]
  have hpe : (p : ℚ) ^ (e + N) / ((p ^ e * m' : ℕ) : ℚ) =
      ((p ^ N : ℕ) : ℚ) * ((1 : ℚ) / ((m' : ℕ) : ℚ)) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'0
    push_cast
    rw [pow_add]
    field_simp
  rw [hpe]
  refine coprime_den_mul (coprime_den_natCast _) ?_
  rw [one_div, Rat.inv_natCast_den, if_neg hm'0]
  exact Nat.Coprime.pow_right a ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm'))

/-- **Faulhaber mod `p²`.** `∑_{k=1}^{p-1} kⁿ ≡ p·B_n (mod p²)` for even `n ≥ 2` with
`(p − 1) ∤ n` and `p ≥ 5`. Every Faulhaber term other than `p·B_n` is `p²` times a
`p`-integral number. -/
theorem sum_pow_eq_p_mul_bernoulli (hp5 : 5 ≤ p) {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n)
    (hnd : ¬ (p - 1) ∣ n) :
    ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n =
      (p : ZMod (p ^ 2)) * ratToZMod (p ^ 2) (bernoulli n) := by
  have hp : p.Prime := Fact.out
  have hF := sum_range_pow p n
  -- left side: drop `k = 0`, cast
  have hL : ∑ k ∈ range p, (k : ℚ) ^ n = ((∑ i ∈ range (p - 1), (i + 1) ^ n : ℕ) : ℚ) := by
    have h := Finset.sum_range_succ' (fun k => (k : ℚ) ^ n) (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    rw [h, Nat.cast_zero, zero_pow (by omega), add_zero]
    push_cast
    rfl
  rw [hL] at hF
  rw [show (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n) =
      ((∑ i ∈ range (p - 1), (i + 1) ^ n : ℕ) : ZMod (p ^ 2)) by push_cast; rfl,
    ← ratToZMod_natCast (m := p ^ 2), hF]
  -- the Faulhaber terms `t i`, and `u i` with `t i = p²·u i` for `i < n`
  set t : ℕ → ℚ := fun i =>
    bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1) with ht_def
  set u : ℕ → ℚ := fun i =>
    bernoulli i * (n.choose i : ℚ) * (p : ℚ) ^ (n - 1 - i) / ((n + 1 - i : ℕ) : ℚ) with hu_def
  have ht : ∀ i ∈ range n, t i = ((p ^ 2 : ℕ) : ℚ) * u i := by
    intro i hi
    have hi' := mem_range.1 hi
    have hc := Nat.choose_mul_succ_eq n i
    have hcQ : (n.choose i : ℚ) * ((n : ℚ) + 1) =
        ((n + 1).choose i : ℚ) * ((n + 1 - i : ℕ) : ℚ) := by exact_mod_cast hc
    have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
    have hm0 : ((n + 1 - i : ℕ) : ℚ) ≠ 0 := by
      have : n + 1 - i ≠ 0 := by omega
      exact_mod_cast this
    simp only [ht_def, hu_def]
    rw [show (p : ℚ) ^ (n + 1 - i) = (p : ℚ) ^ 2 * (p : ℚ) ^ (n - 1 - i) by
      rw [← pow_add]; congr 1; omega]
    field_simp
    push_cast
    linear_combination (-(bernoulli i * (p : ℚ) ^ 2)) * hcQ
  have hu : ∀ i ∈ range n, Nat.Coprime (u i).den (p ^ 2) := by
    intro i hi
    have hi' := mem_range.1 hi
    simp only [hu_def]
    rcases Nat.lt_or_ge (i + 1) n with hlt | hge
    · -- `m = n + 1 − i ≥ 3`: `u i = (p·B_i)·C(n,i)·(p^(m−3)/m)`
      have hm3 : 3 ≤ n + 1 - i := by omega
      have heq : bernoulli i * (n.choose i : ℚ) * (p : ℚ) ^ (n - 1 - i) /
          ((n + 1 - i : ℕ) : ℚ) = ((p : ℚ) * bernoulli i) * (n.choose i : ℚ) *
            ((p : ℚ) ^ (n + 1 - i - 3) / ((n + 1 - i : ℕ) : ℚ)) := by
        rw [show n - 1 - i = (n + 1 - i - 3) + 1 by omega, pow_succ]
        ring
      rw [heq]
      exact coprime_den_mul (coprime_den_mul (coprime_den_p_mul_bernoulli 2 (by omega) i)
        (coprime_den_natCast _)) (coprime_den_pow_div 2 hp5 hm3)
    · -- `i = n − 1`: `m = 2`, and `B_{n−1}` is `p`-integral (`n − 1` is odd)
      have hi1 : i = n - 1 := by omega
      have hodd : ¬ (p - 1) ∣ i := by
        intro h
        obtain ⟨r, hr⟩ := (even_iff_two_dvd.1 (hp.even_sub_one (by omega))).trans h
        obtain ⟨j, hj⟩ := hn
        omega
      have heq : bernoulli i * (n.choose i : ℚ) * (p : ℚ) ^ (n - 1 - i) /
          ((n + 1 - i : ℕ) : ℚ) = bernoulli i * (n.choose i : ℚ) * ((1 : ℚ) / ((2 : ℕ) : ℚ)) := by
        rw [show n - 1 - i = 0 by omega, show n + 1 - i = 2 by omega, pow_zero]
        ring
      rw [heq]
      exact coprime_den_mul (coprime_den_mul (bernoulli_den_coprime_of_not_dvd 2 hodd)
        (coprime_den_natCast _)) (coprime_den_one_div_prime 2 Nat.prime_two (by omega))
  have htc : ∀ i ∈ range n, Nat.Coprime (t i).den (p ^ 2) := by
    intro i hi
    rw [ht i hi]
    exact coprime_den_mul (coprime_den_natCast _) (hu i hi)
  have ht0 : ∀ i ∈ range n, ratToZMod (p ^ 2) (t i) = 0 := by
    intro i hi
    rw [ht i hi, ratToZMod_mul _ _ (coprime_den_natCast _) (hu i hi), ratToZMod_natCast,
      Nat.cast_pow, natCast_sq_self, zero_mul]
  have htn : t n = (p : ℚ) * bernoulli n := by
    have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
    simp only [ht_def]
    rw [Nat.choose_succ_self_right, show n + 1 - n = 1 by omega, pow_one]
    push_cast
    field_simp
  have hBc := bernoulli_den_coprime_of_not_dvd (p := p) 2 hnd
  have htnc : Nat.Coprime (t n).den (p ^ 2) := by
    rw [htn]; exact coprime_den_mul (coprime_den_natCast _) hBc
  change ratToZMod (p ^ 2) (∑ i ∈ range (n + 1), t i) = _
  rw [Finset.sum_range_succ, ratToZMod_add' _ _ (coprime_den_sum _ _ htc) htnc,
    ratToZMod_sum _ _ htc, Finset.sum_eq_zero ht0, zero_add, htn,
    ratToZMod_mul _ _ (coprime_den_natCast _) hBc, ratToZMod_natCast]

/-- Multiplication by `a` (prime to `p`) permutes `1, …, p−1` modulo `p`. -/
theorem sum_range_mul (a : ℕ) (ha : ¬ p ∣ a) {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ range (p - 1), g (i + 1) = ∑ i ∈ range (p - 1), g (a * (i + 1) % p) := by
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact ha
  rw [sum_range_succ_eq_sum_units g, sum_range_succ_eq_sum_units (fun k => g (a * k % p))]
  refine (Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 (a : ZMod p) ha0)) _ _ (fun u => ?_)).symm
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0, ZMod.val_mul, ZMod.val_natCast]
  rw [Nat.mod_mul_mod]

/-- **Voronoi's congruence mod `p²`** (no Bernoulli numbers yet): with `k·a = r_k + p·⌊ka/p⌋`,
`(aⁿ − 1)·∑ kⁿ ≡ n·p·a^{n−1}·∑ ⌊ka/p⌋·k^{n−1} (mod p²)`. -/
theorem voronoi_sq (a n : ℕ) (ha : ¬ p ∣ a) :
    ((a : ZMod (p ^ 2)) ^ n - 1) * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n =
      (n : ZMod (p ^ 2)) * p * (a : ZMod (p ^ 2)) ^ (n - 1) * ∑ i ∈ range (p - 1),
        ((a * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (n - 1) := by
  -- termwise: `(ak mod p)ⁿ = aⁿkⁿ − n·p·a^{n−1}·⌊ak/p⌋·k^{n−1}` in `ZMod p²`
  have hterm : ∀ k : ℕ, ((a * k % p : ℕ) : ZMod (p ^ 2)) ^ n =
      (a : ZMod (p ^ 2)) ^ n * (k : ZMod (p ^ 2)) ^ n
      - (n : ZMod (p ^ 2)) * p * (a : ZMod (p ^ 2)) ^ (n - 1) *
        (((a * k / p : ℕ) : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) ^ (n - 1)) := by
    intro k
    have hdiv : ((a * k % p : ℕ) : ZMod (p ^ 2)) =
        (a : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) + -((p : ZMod (p ^ 2)) *
          ((a * k / p : ℕ) : ZMod (p ^ 2))) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (Nat.mod_add_div (a * k) p)
      simp only [Nat.cast_add, Nat.cast_mul] at this
      linear_combination this
    have hε : (-((p : ZMod (p ^ 2)) * ((a * k / p : ℕ) : ZMod (p ^ 2)))) ^ 2 = 0 := by
      linear_combination ((a * k / p : ℕ) : ZMod (p ^ 2)) ^ 2 * natCast_sq_self (p := p)
    rw [hdiv, add_pow_of_sq_eq_zero _ _ hε, mul_pow, mul_pow]
    ring
  have hperm := sum_range_mul (p := p) a ha (fun k => ((k : ZMod (p ^ 2))) ^ n)
  have hS : ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n =
      (a : ZMod (p ^ 2)) ^ n * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n
      - (n : ZMod (p ^ 2)) * p * (a : ZMod (p ^ 2)) ^ (n - 1) * ∑ i ∈ range (p - 1),
        ((a * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (n - 1) := by
    calc ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n
        = ∑ i ∈ range (p - 1), ((a * (i + 1) % p : ℕ) : ZMod (p ^ 2)) ^ n := hperm
      _ = ∑ i ∈ range (p - 1), ((a : ZMod (p ^ 2)) ^ n * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ n
            - (n : ZMod (p ^ 2)) * p * (a : ZMod (p ^ 2)) ^ (n - 1) *
              (((a * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (n - 1))) :=
          Finset.sum_congr rfl fun i _ => hterm (i + 1)
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination -hS

/-- If `p·X = 0` in `ZMod p²`, then `X ≡ 0 (mod p)`. -/
theorem castHom_eq_zero_of_p_mul (X : ZMod (p ^ 2)) (h : (p : ZMod (p ^ 2)) * X = 0) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) X = 0 := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  rw [← ZMod.natCast_zmod_val X, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h
  exact Nat.dvd_of_mul_dvd_mul_left hp.pos (by rw [← pow_two]; exact h)

/-- **Voronoi's congruence mod `p`.** For even `n ≥ 2` with `(p − 1) ∤ n`, `p ≥ 5`, `p ∤ a`:
`(aⁿ − 1)·B_n ≡ n·a^{n−1}·∑_{k=1}^{p−1} ⌊ak/p⌋·k^{n−1} (mod p)`. -/
theorem voronoi_mod_p (hp5 : 5 ≤ p) (a : ℕ) (ha : ¬ p ∣ a) {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n)
    (hnd : ¬ (p - 1) ∣ n) :
    ((a : ZMod p) ^ n - 1) * ratToZMod p (bernoulli n) =
      (n : ZMod p) * (a : ZMod p) ^ (n - 1) * ∑ i ∈ range (p - 1),
        ((a * (i + 1) / p : ℕ) : ZMod p) * ((i + 1 : ℕ) : ZMod p) ^ (n - 1) := by
  have hV := voronoi_sq (p := p) a n ha
  rw [sum_pow_eq_p_mul_bernoulli hp5 hn hn2 hnd] at hV
  have hX : (p : ZMod (p ^ 2)) * (((a : ZMod (p ^ 2)) ^ n - 1) * ratToZMod (p ^ 2) (bernoulli n) -
      (n : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (n - 1) * ∑ i ∈ range (p - 1),
        ((a * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (n - 1)) = 0 := by
    linear_combination hV
  have h0 := castHom_eq_zero_of_p_mul _ hX
  simp only [map_sub, map_mul, map_pow, map_one, map_natCast, map_sum] at h0
  rw [castHom_ratToZMod _ _ (bernoulli_den_coprime_of_not_dvd 2 hnd)] at h0
  linear_combination h0

/-- A `p`-integral rational vanishes in `ZMod p` iff `p` divides its numerator. -/
theorem ratToZMod_prime_eq_zero_iff (q : ℚ) (hq : ¬ p ∣ q.den) :
    ratToZMod p q = 0 ↔ (p : ℤ) ∣ q.num := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime q.den p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hq)
  have hu : IsUnit ((q.den : ZMod p)⁻¹) := by
    rw [← ZMod.coe_unitOfCoprime q.den hcop, ZMod.inv_coe_unit]
    exact Units.isUnit _
  unfold ratToZMod
  rw [hu.mul_left_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Kummer's congruence, in the form used by Jensen.** Let `p ≥ 5`, `n ≥ 2` even with
`p ∤ n` and `(p − 1) ∤ n`. If `p ∣ B_n`, then `p ∣ B_k` for `k = n mod (p − 1)`. -/
theorem kummer_dvd (hp5 : 5 ≤ p) {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) (hnd : ¬ (p - 1) ∣ n)
    (hpn : ¬ p ∣ n) (hB : (p : ℤ) ∣ (bernoulli n).num) :
    (p : ℤ) ∣ (bernoulli (n % (p - 1))).num := by
  have hp : p.Prime := Fact.out
  set k := n % (p - 1) with hk
  have hp1 : Even (p - 1) := hp.even_sub_one (by omega)
  have hk0 : k ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hklt : k < p - 1 := Nat.mod_lt _ (by omega)
  obtain ⟨q, hq⟩ : ∃ q, n = k + (p - 1) * q := ⟨n / (p - 1), (Nat.mod_add_div n (p - 1)).symm⟩
  have hkev : Even k := by
    rw [hq, Nat.even_add] at hn
    exact hn.2 (hp1.mul_right _)
  have hk2 : 2 ≤ k := by obtain ⟨j, hj⟩ := hkev; omega
  have hkd : ¬ (p - 1) ∣ k := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  -- a generator `g` of `(ZMod p)ˣ`; `a` is a natural-number lift
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  set a := (g : ZMod p).val with ha_def
  have hga : ((a : ℕ) : ZMod p) = g := ZMod.natCast_zmod_val _
  have hga0 : (a : ZMod p) ≠ 0 := by rw [hga]; exact g.ne_zero
  have ha : ¬ p ∣ a := by
    intro h
    exact hga0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  -- Fermat: exponents only matter mod `p − 1`
  have hferm : ∀ x : ZMod p, x ≠ 0 → ∀ j, x ^ (j + (p - 1) * q) = x ^ j := by
    intro x hx j
    rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]
  have e1 : (a : ZMod p) ^ n = (a : ZMod p) ^ k := by rw [hq]; exact hferm _ hga0 k
  have e2 : (a : ZMod p) ^ (n - 1) = (a : ZMod p) ^ (k - 1) := by
    rw [show n - 1 = k - 1 + (p - 1) * q by omega]; exact hferm _ hga0 _
  have e3 : ∑ i ∈ range (p - 1),
      ((a * (i + 1) / p : ℕ) : ZMod p) * ((i + 1 : ℕ) : ZMod p) ^ (n - 1) =
      ∑ i ∈ range (p - 1),
        ((a * (i + 1) / p : ℕ) : ZMod p) * ((i + 1 : ℕ) : ZMod p) ^ (k - 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have h0 : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd (by omega) h; omega
    rw [show n - 1 = k - 1 + (p - 1) * q by omega, hferm _ h0]
  have hak : (a : ZMod p) ^ k ≠ 1 := by
    intro h
    have hgk : g ^ k = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, ← hga]; exact h)
    have := orderOf_dvd_of_pow_eq_one hgk
    rw [hg] at this
    exact hkd this
  have Vn := voronoi_mod_p hp5 a ha hn hn2 hnd
  have Vk := voronoi_mod_p hp5 a ha hkev hk2 hkd
  have hBn : ratToZMod p (bernoulli n) = 0 :=
    (ratToZMod_prime_eq_zero_iff _ (bernoulli_den_not_dvd hnd)).2 hB
  rw [hBn, mul_zero, e2, e3] at Vn
  have hn0 : (n : ZMod p) ≠ 0 := by rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact hpn
  have hG : (a : ZMod p) ^ (k - 1) * ∑ i ∈ range (p - 1),
      ((a * (i + 1) / p : ℕ) : ZMod p) * ((i + 1 : ℕ) : ZMod p) ^ (k - 1) = 0 := by
    have h := Vn.symm
    rw [mul_assoc] at h
    exact (mul_eq_zero.1 h).resolve_left hn0
  rw [mul_assoc, hG, mul_zero] at Vk
  have hBk : ratToZMod p (bernoulli k) = 0 := (mul_eq_zero.1 Vk).resolve_left (sub_ne_zero.2 hak)
  exact (ratToZMod_prime_eq_zero_iff _ (bernoulli_den_not_dvd hkd)).1 hBk

/-- Arithmetic of `k = n mod (p − 1)` for even `n` with `(p − 1) ∤ n`: `k` is even and
`2 ≤ k ≤ p − 3`. -/
theorem mod_sub_one_facts (hp5 : 5 ≤ p) {n : ℕ} (hn : Even n) (hnd : ¬ (p - 1) ∣ n) :
    Even (n % (p - 1)) ∧ 2 ≤ n % (p - 1) ∧ n % (p - 1) ≤ p - 3 := by
  have hp : p.Prime := Fact.out
  have hp1 : Even (p - 1) := hp.even_sub_one (by omega)
  have hk0 : n % (p - 1) ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hklt : n % (p - 1) < p - 1 := Nat.mod_lt _ (by omega)
  have hkev : Even (n % (p - 1)) := by
    have h := Nat.mod_add_div n (p - 1)
    rw [← h, Nat.even_add] at hn
    exact hn.2 (hp1.mul_right _)
  obtain ⟨j, hj⟩ := hkev
  obtain ⟨d, hd⟩ := hp1
  exact ⟨⟨j, hj⟩, by omega, by omega⟩

/-- **von Staudt–Clausen, denominator form.** If `k ≥ 1` and `(p − 1) ∣ 2k`, then `p` divides the
denominator of `B_{2k}`. -/
theorem dvd_den_bernoulli {k : ℕ} (hk : 0 < k) (hpk : (p - 1) ∣ 2 * k) :
    p ∣ (bernoulli (2 * k)).den := by
  have hp : p.Prime := Fact.out
  by_contra hnd
  obtain ⟨z, hz⟩ := bernoulli_two_mul_eq k
  set F := (range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) with hF
  have hpF : p ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp, hpk⟩
    have := Nat.le_of_dvd (by omega) hpk
    omega
  have hsplit := Finset.add_sum_erase F (fun q => (1 : ℚ) / q) hpF
  -- `1 + p·B + Σ_{q ≠ p} p/q = p·z`
  have key : 1 + (p : ℚ) * bernoulli (2 * k) + ∑ q ∈ F.erase p, (p : ℚ) * ((1 : ℚ) / q) =
      (p : ℚ) * z := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [← Finset.mul_sum, hz, ← hsplit]
    field_simp
    ring
  have hq1 : ∀ q ∈ F.erase p, Nat.Coprime ((1 : ℚ) / q).den p := by
    intro q hq
    rw [Finset.mem_erase, hF, Finset.mem_filter] at hq
    have := coprime_den_one_div_prime (p := p) 1 hq.2.2.1 hq.1
    rwa [pow_one] at this
  have hq' : ∀ q ∈ F.erase p, Nat.Coprime ((p : ℚ) * ((1 : ℚ) / q)).den p := fun q hq =>
    coprime_den_mul (coprime_den_natCast p) (hq1 q hq)
  have hBc : Nat.Coprime (bernoulli (2 * k)).den p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have hone : Nat.Coprime (1 : ℚ).den p := by simp
  have e0 : ratToZMod p (1 + (p : ℚ) * bernoulli (2 * k) +
      ∑ q ∈ F.erase p, (p : ℚ) * ((1 : ℚ) / q)) = 1 := by
    rw [ratToZMod_add' _ _ (coprime_den_add hone (coprime_den_mul (coprime_den_natCast p) hBc))
        (coprime_den_sum _ _ hq'),
      ratToZMod_add' _ _ hone (coprime_den_mul (coprime_den_natCast p) hBc),
      ratToZMod_sum _ _ hq',
      Finset.sum_eq_zero (fun q hq => by
        rw [ratToZMod_mul _ _ (coprime_den_natCast p) (hq1 q hq), ratToZMod_natCast,
          ZMod.natCast_self, zero_mul]),
      ratToZMod_mul _ _ (coprime_den_natCast p) hBc, ratToZMod_natCast, ZMod.natCast_self,
      zero_mul, add_zero, add_zero]
    simpa using ratToZMod_natCast (m := p) 1
  have e1 : ratToZMod p ((p : ℚ) * z) = 0 := by
    rw [ratToZMod_mul _ _ (coprime_den_natCast p) (coprime_den_intCast z), ratToZMod_natCast,
      ZMod.natCast_self, zero_mul]
  have h := congrArg (ratToZMod p) key
  rw [e0, e1] at h
  exact one_ne_zero h

end Kummer

section Jensen

/-- **Jensen's theorem (1915), Bernoulli form, assuming `|B_{2k}| > 1` for all large `k`.**
For every `P` there is a prime `p > P` that divides the numerator of some `B_k` with `k` even,
`2 ≤ k ≤ p − 3` (an *irregular* prime in the sense of Kummer's criterion).

Proof (Jensen): let `M = ∏_{q ≤ P, q prime} (q − 1)` and `n = 2·2^K·M`. Since `|B_n| > 1`, the
numerator of `B_n` has a prime factor `p`. By von Staudt–Clausen, `(p − 1) ∤ n`, so `p > P`; also
`p ∤ n`. Kummer's congruence moves `p ∣ B_n` down to `p ∣ B_{n mod (p−1)}`. -/
theorem exists_irregular_gt (hgrowth : ∃ K, ∀ k ≥ K, 1 < |bernoulli (2 * k)|) (P : ℕ) :
    ∃ p, P < p ∧ p.Prime ∧
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num := by
  obtain ⟨K, hK⟩ := hgrowth
  set P' := max P 4 with hP'
  set M := ∏ q ∈ (range (P' + 1)).filter Nat.Prime, (q - 1) with hM
  have hM0 : 0 < M := Finset.prod_pos fun q hq => by
    have := (mem_filter.1 hq).2.two_le; omega
  set m := 2 ^ K * M with hm
  have hKm : K ≤ m := le_trans (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    (Nat.le_mul_of_pos_right _ hM0)
  have hm0 : 0 < m := Nat.mul_pos (by positivity) hM0
  set n := 2 * m with hn
  have hB := hK m hKm
  -- the numerator of `B_n` is not `±1`, so it has a prime factor `p`
  have hnum : (bernoulli n).num.natAbs ≠ 1 := by
    intro h1
    have hden : (1 : ℚ) ≤ ((bernoulli n).den : ℚ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (bernoulli n).den_nz
    have habs : |((bernoulli n).num : ℚ)| = 1 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, h1]; simp
    have : |bernoulli n| ≤ 1 := by
      rw [← Rat.num_div_den (bernoulli n), abs_div, habs,
        abs_of_pos (by linarith : (0 : ℚ) < ((bernoulli n).den : ℚ)), div_le_one (by linarith)]
      exact hden
    linarith
  obtain ⟨p, hp, hpnum⟩ := Nat.exists_prime_and_dvd hnum
  have : Fact p.Prime := ⟨hp⟩
  have hpnum' : (p : ℤ) ∣ (bernoulli n).num := Int.ofNat_dvd_left.2 hpnum
  -- `p` does not divide the denominator (numerator and denominator are coprime)
  have hnotden : ¬ p ∣ (bernoulli n).den := fun h => by
    have := Nat.dvd_gcd hpnum h
    rw [(bernoulli n).reduced.gcd_eq_one] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  -- hence `(p − 1) ∤ n`
  have hnd : ¬ (p - 1) ∣ n := fun h => hnotden (dvd_den_bernoulli hm0 h)
  -- hence `p > P'`: every prime `q ≤ P'` has `(q − 1) ∣ M ∣ n`
  have hP'p : P' < p := by
    by_contra hle
    replace hle := not_lt.1 hle
    apply hnd
    have hmem : p ∈ (range (P' + 1)).filter Nat.Prime :=
      mem_filter.2 ⟨mem_range.2 (by omega), hp⟩
    exact (Finset.dvd_prod_of_mem _ hmem).trans
      ((Dvd.intro_left _ rfl : M ∣ m).trans (Dvd.intro_left _ rfl))
  have hp5 : 5 ≤ p := by omega
  -- `p ∤ n`: the prime factors of `n = 2·2^K·M` are `2` and divisors of `q − 1`, `q ≤ P'`
  have hpn : ¬ p ∣ n := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 h3
      have hq' := mem_filter.1 hq
      have := hq'.2.two_le
      have := Nat.le_of_dvd (by omega) hpq
      have := mem_range.1 hq'.1
      omega
  have hnev : Even n := ⟨m, by omega⟩
  have hkum := kummer_dvd hp5 hnev (by omega) hnd hpn hpnum'
  obtain ⟨hkev, hk2, hk3⟩ := mod_sub_one_facts hp5 hnev hnd
  refine ⟨p, by omega, hp, n % (p - 1), Finset.mem_Icc.2 ⟨hk2, hk3⟩, hkev, ?_⟩
  rwa [← bernoulli_eq_bernoulli'_of_ne_one (by omega)]

/-- **Jensen's theorem, Bernoulli form** (given the growth of `|B_{2k}|`): infinitely many primes
`p` divide the numerator of some `B_k`, `k` even, `2 ≤ k ≤ p − 3`. -/
theorem infinite_bernoulli_irregular (hgrowth : ∃ K, ∀ k ≥ K, 1 < |bernoulli (2 * k)|) :
    {p : ℕ | p.Prime ∧
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num}.Infinite :=
  Set.infinite_of_forall_exists_gt fun P => by
    obtain ⟨p, hP, hp, hk⟩ := exists_irregular_gt hgrowth P
    exact ⟨p, ⟨hp, hk⟩, hP⟩

end Jensen

section Growth

open Filter Topology Nat

/-- `|B_{2k}| > 1` for all large `k`, from Euler's formula `ζ(2k) = (−1)^{k+1} 2^{2k−1} π^{2k}
B_{2k}/(2k)!` (stated for an arbitrary `x > 0` in place of `π`), `ζ(2k) ≥ 1` and
`(2x)ⁿ/n! → 0`. -/
theorem one_lt_abs_bernoulli_of (x : ℝ) (hx : 0 < x)
    (hS : ∀ k : ℕ, k ≠ 0 → HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * x ^ (2 * k) * bernoulli (2 * k) / (2 * k)!))
    (ht : Tendsto (fun n : ℕ => (2 * x) ^ n / (n ! : ℝ)) atTop (𝓝 0)) :
    ∃ K, ∀ k ≥ K, 1 < |bernoulli (2 * k)| := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds one_pos))
  refine ⟨N + 1, fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by omega
  -- `ζ(2k) ≥ 1` (the `n = 1` term)
  have h1 : (1 : ℝ) ≤ (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * x ^ (2 * k) *
      bernoulli (2 * k) / (2 * k)! := by
    have := le_hasSum (hS k hk0) 1 (fun j _ => by positivity)
    simpa using this
  have hx' : (2 * x) ^ (2 * k) / ((2 * k)! : ℝ) < 1 := hN (2 * k) (by omega)
  set B : ℝ := ((bernoulli (2 * k) : ℚ) : ℝ) with hB
  set F : ℝ := ((2 * k)! : ℝ) with hF
  set c : ℝ := (2 : ℝ) ^ (2 * k - 1) * x ^ (2 * k) with hc
  have hF0 : 0 < F := by positivity
  have hc0 : 0 < c := by positivity
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ]; ring
  have hpow : (2 * x) ^ (2 * k) = 2 * c := by
    rw [mul_pow, h2, hc]; ring
  -- `F ≤ c·|B|`
  have hFle : F ≤ c * |B| := by
    have h1' : F ≤ c * ((-1 : ℝ) ^ (k + 1) * B) := by
      have := (le_div_iff₀ hF0).1 h1
      linarith
    have : (-1 : ℝ) ^ (k + 1) * B ≤ |B| := by
      calc (-1 : ℝ) ^ (k + 1) * B ≤ |(-1 : ℝ) ^ (k + 1) * B| := le_abs_self _
        _ = |B| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    nlinarith
  -- `2c < F`
  have hlt : 2 * c < F := by
    rw [← hpow]; exact (div_lt_one hF0).1 hx'
  have hB2 : 2 < |B| := by nlinarith
  have : (1 : ℝ) < |B| := by linarith
  rw [hB] at this
  exact_mod_cast this

end Growth

end WolstenholmeHarmonic
