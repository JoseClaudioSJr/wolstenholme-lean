import Mathlib

/-!
# Wolstenholme primes via harmonic numbers and Bernoulli numbers

Proofs of the two textbook characterisations stated in Formal Conjectures
(`FormalConjectures/Wikipedia/WolstenholmePrime.lean`). A prime `p > 7` is a
*Wolstenholme prime* if `C(2p−1, p−1) ≡ 1 (mod p⁴)`.

* `wolstenholme_harmonic`  : Wolstenholme  ⇔  `p³ ∣ num(H_{p−1})`,  `H_{p−1} = Σ_{k<p} 1/k`.
* `wolstenholme_bernoulli` : Wolstenholme  ⇔  `p ∣ num(B_{p−3})`.

A human-readable proof, with no Lean, is in `PROOF.md`.

## Notation

* `invK m i = 1/(i+1)` in `ZMod m`. Indices run over `i ∈ range (p−1)`,
  i.e. `k = i + 1 = 1, …, p−1`.
* `S m p j = Σ_k k^{−j}` in `ZMod m` (power sums of inverses); `S₁` is `H_{p−1}` reduced mod `m`,
  and `S₂` is `H_{p−1,2} = Σ 1/k²` reduced mod `m`.
* `E m p j` = j-th elementary symmetric function of the `1/k`, in `ZMod m`.
* `ratToZMod m q = num(q) · den(q)⁻¹` in `ZMod m`, the reduction of a rational whose
  denominator is a unit mod `m`. It turns statements about the rationals `H_{p−1}`
  and `B_{p−3}` into statements in `ZMod pⁿ`.

## Layout

1. **Layer 1 (any commutative semiring).** Newton-type identities: `(Σa)² = Σa² + 2e₂`,
   `(Σa)³ + 2Σa³ = 3(Σa)(Σa²) + 6e₃`, and `∏(1 + c·aᵢ) = 1 + c·e₁ + c²·e₂ + c³·e₃` when `c⁴ = 0`.
2. **Layer 2 (any `m`).** `ratToZMod` is additive and multiplicative, commutes with sums and with
   reduction `ZMod n → ZMod m`, and detects divisibility of numerators.
3. **Bridge (`ZMod pⁿ`).** Units, reduction of power sums, "`p·x = 0` iff `x ≡ 0` one level down",
   and `C(2p−1, p−1) = ∏ (1 + p/k)`.
4. **Part I.** For every prime `p ≥ 5`, `C(2p−1, p−1) − 1 ≡ 2p·H_{p−1} (mod p⁴)`:
   * `harmonic_sum_pow_mod`: `S_j ≡ 0 (mod p)` when `p − 1 ∤ j` (`FiniteField.sum_pow_units`);
   * `binomial_product_expansion`: `C = 1 + pS₁ + p²e₂ + p³e₃` in `ZMod p⁴`;
   * `harmonic_pairing`: `p(2S₁ + pS₂) = 0` (pairing `k ↔ p − k`);
   * `binomial_harmonic_congruence`, then `wolstenholme_core` and `wolstenholme_harmonic`.
5. **Part II** (no Kummer congruence, which Mathlib lacks):
   * Step A `sum_pow_p_sub_three`: `Σ k^{p−3} ≡ p·B_{p−3} (mod p²)` (Faulhaber, von Staudt–Clausen);
   * Step B `three_S_two_eq`: `3·H_{p−1,2} ≡ 2·Σ k^{p−3} (mod p²)` (doubling `k ↦ 2k mod p`);
   * `wolstenholme_bernoulli_core`, then `wolstenholme_bernoulli`.

Toolchain: Lean v4.33.1, Mathlib 0df444a3 (as in Formal Conjectures). No `sorry`; both final
theorems depend only on [propext, Classical.choice, Quot.sound]. `IsWolstenholmePrime` here is a
verbatim copy of the Formal Conjectures definition; `FormalConjecturesCheck.lean` applies both
theorems to the original statements.
-/

open Finset

namespace WolstenholmeHarmonic

/-- Verbatim copy of the Formal Conjectures definition. -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

/-! ## Objects in `ZMod m` -/

/-- `invK m i = (i+1)⁻¹` in `ZMod m`; for `i ∈ range (p-1)` this is `1/k`, `k = 1, …, p-1`. -/
def invK (m i : ℕ) : ZMod m := ((i + 1 : ℕ) : ZMod m)⁻¹

/-- Power sum `S_j = ∑_{k=1}^{p-1} k^{-j}` in `ZMod m`. -/
def S (m p j : ℕ) : ZMod m := ∑ i ∈ range (p - 1), invK m i ^ j

/-- Elementary symmetric function `e_j(1/1, …, 1/(p-1))` in `ZMod m`. -/
def E (m p j : ℕ) : ZMod m :=
  ∑ t ∈ (range (p - 1)).powersetCard j, ∏ i ∈ t, invK m i

/-- Reduction of a rational into `ZMod m` (meaningful when `q.den` is a unit mod `m`). -/
def ratToZMod (m : ℕ) (q : ℚ) : ZMod m := (q.num : ZMod m) * ((q.den : ZMod m))⁻¹

/-! ## Layer 1 — generic symmetric-function identities (any commutative semiring) -/

section Generic

/-- `(∑ aᵢ)² = ∑ aᵢ² + 2·e₂(a)`, for any finite family in a commutative semiring. -/
theorem sum_sq_eq_sum_sq_add_two_mul_E2
    {α R : Type*} [CommSemiring R]
    (s : Finset α) (a : α → R) :
    (∑ i ∈ s, a i) ^ 2 =
      (∑ i ∈ s, a i ^ 2) + 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i := by
  classical
  -- Induction on `s`. Adding a new element `x`, the 2-subsets of `insert x s` are the 2-subsets
  -- of `s` plus the sets `{x, i}` with `i ∈ s`; the latter contribute the cross term `a x · Σ a`.
  induction s using Finset.induction_on with
  | empty => rw [Finset.powersetCard_eq_empty.2 (by simp)]; simp
  | insert x s hx ih =>
    -- The two families of subsets are disjoint (only the second contains `x`) …
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert x)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ht'
      exact hx ((Finset.mem_powersetCard.1 ht).1 (Finset.mem_insert_self x u))
    -- … and `t ↦ insert x t` is injective on subsets of `s` (undo it with `erase x`).
    have hinj : Set.InjOn (insert x) ((s.powersetCard 1 : Finset (Finset α)) : Set (Finset α)) := by
      intro u hu v hv huv
      have hxu : x ∉ u := fun h => hx ((Finset.mem_powersetCard.1 hu).1 h)
      have hxv : x ∉ v := fun h => hx ((Finset.mem_powersetCard.1 hv).1 h)
      rw [← Finset.erase_insert hxu, ← Finset.erase_insert hxv]
      exact congrArg (fun w => Finset.erase w x) huv
    -- The new pairs `{x, i}` sum to `a x · Σ_{i∈s} a i`.
    have hcross : ∑ t ∈ s.powersetCard 1, ∏ i ∈ insert x t, a i = a x * ∑ i ∈ s, a i := by
      rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hxi : x ∉ ({i} : Finset α) := by
        rw [Finset.mem_singleton]; rintro rfl; exact hx hi
      simp [Finset.prod_insert hxi]
    -- Expand `(a x + Σ a)²` and use the induction hypothesis for `(Σ a)²`.
    rw [Finset.powersetCard_succ_insert hx 1, Finset.sum_union hdisj, Finset.sum_image hinj,
      hcross, Finset.sum_insert hx, Finset.sum_insert hx, add_sq, ih]
    ring

/-- `(∑ aᵢ)³ + 2·∑ aᵢ³ = 3·(∑ aᵢ)(∑ aᵢ²) + 6·e₃(a)` (Newton, degree 3, no subtraction). -/
theorem sum_cube_add_two_sum_cube_eq
    {α R : Type*} [CommSemiring R]
    (s : Finset α) (a : α → R) :
    (∑ i ∈ s, a i) ^ 3 + 2 * ∑ i ∈ s, a i ^ 3 =
      3 * (∑ i ∈ s, a i) * (∑ i ∈ s, a i ^ 2) + 6 * ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.powersetCard_eq_empty.2 (by simp)]; simp
  | insert x s hx ih =>
    -- Same induction as for the square. New 3-subsets are `{x} ∪ t` with `t` a 2-subset of `s`,
    -- contributing `a x · e₂(s)`; the degree-2 identity `(Σa)² = Σa² + 2e₂` closes the cross term.
    have h2 := sum_sq_eq_sum_sq_add_two_mul_E2 s a
    have hdisj : Disjoint (s.powersetCard 3) ((s.powersetCard 2).image (insert x)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ht'
      exact hx ((Finset.mem_powersetCard.1 ht).1 (Finset.mem_insert_self x u))
    have hinj : Set.InjOn (insert x) ((s.powersetCard 2 : Finset (Finset α)) : Set (Finset α)) := by
      intro u hu v hv huv
      have hxu : x ∉ u := fun h => hx ((Finset.mem_powersetCard.1 hu).1 h)
      have hxv : x ∉ v := fun h => hx ((Finset.mem_powersetCard.1 hv).1 h)
      rw [← Finset.erase_insert hxu, ← Finset.erase_insert hxv]
      exact congrArg (fun w => Finset.erase w x) huv
    have hcross : ∑ t ∈ s.powersetCard 2, ∏ i ∈ insert x t, a i
        = a x * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hxt : x ∉ t := fun h => hx ((Finset.mem_powersetCard.1 ht).1 h)
      rw [Finset.prod_insert hxt]
    rw [Finset.powersetCard_succ_insert hx 2, Finset.sum_union hdisj, Finset.sum_image hinj,
      hcross, Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    set A := ∑ i ∈ s, a i
    set B := ∑ i ∈ s, a i ^ 2
    set C := ∑ i ∈ s, a i ^ 3
    set e2 := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i
    set e3 := ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, a i
    -- With A = Σa, B = Σa², C = Σa³ over `s`: expand, then substitute `A² = B + 2e₂` and the
    -- induction hypothesis `A³ + 2C = 3AB + 6e₃`.
    calc (a x + A) ^ 3 + 2 * (a x ^ 3 + C)
        = 3 * a x ^ 3 + 3 * a x ^ 2 * A + 3 * a x * A ^ 2 + (A ^ 3 + 2 * C) := by ring
      _ = 3 * a x ^ 3 + 3 * a x ^ 2 * A + 3 * a x * (B + 2 * e2) + (3 * A * B + 6 * e3) := by
          rw [h2, ih]
      _ = 3 * (a x + A) * (a x ^ 2 + B) + 6 * (e3 + a x * e2) := by ring

/-- Recursion `e_{k+1}(s ∪ {x}) = e_{k+1}(s) + a x · e_k(s)`. -/
theorem esum_succ_insert {α R : Type*} [CommSemiring R] [DecidableEq α] {x : α}
    {s : Finset α} (hx : x ∉ s) (a : α → R) (k : ℕ) :
    ∑ t ∈ (insert x s).powersetCard (k + 1), ∏ i ∈ t, a i =
      ∑ t ∈ s.powersetCard (k + 1), ∏ i ∈ t, a i + a x * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i := by
  have hdisj : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ht'
    exact hx ((Finset.mem_powersetCard.1 ht).1 (Finset.mem_insert_self x u))
  have hinj : Set.InjOn (insert x) ((s.powersetCard k : Finset (Finset α)) : Set (Finset α)) := by
    intro u hu v hv huv
    have hxu : x ∉ u := fun h => hx ((Finset.mem_powersetCard.1 hu).1 h)
    have hxv : x ∉ v := fun h => hx ((Finset.mem_powersetCard.1 hv).1 h)
    rw [← Finset.erase_insert hxu, ← Finset.erase_insert hxv]
    exact congrArg (fun w => Finset.erase w x) huv
  rw [Finset.powersetCard_succ_insert hx k, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have hxt : x ∉ t := fun h => hx ((Finset.mem_powersetCard.1 ht).1 h)
  rw [Finset.prod_insert hxt]

/-- `∏ (1 + c·aᵢ) = 1 + c·e₁ + c²·e₂ + c³·e₃` whenever `c⁴ = 0`. -/
theorem prod_one_add_mul_of_pow_four_eq_zero {α R : Type*} [CommRing R]
    (s : Finset α) (a : α → R) (c : R) (hc : c ^ 4 = 0) :
    ∏ i ∈ s, (1 + c * a i) =
      1 + c * ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, a i
        + c ^ 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i
        + c ^ 3 * ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, a i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.powersetCard_eq_empty.2 (by simp), Finset.powersetCard_eq_empty.2 (by simp),
      Finset.powersetCard_eq_empty.2 (by simp)]
    simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, ih, esum_succ_insert hx a 0, esum_succ_insert hx a 1,
      esum_succ_insert hx a 2, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]
    linear_combination (a x * ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, a i) * hc

/-- `e₁(a) = ∑ aᵢ`: summing over one-element subsets is the plain sum. -/
theorem sum_powersetCard_one {α R : Type*} [CommSemiring R] (s : Finset α) (a : α → R) :
    ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, a i = ∑ i ∈ s, a i := by
  rw [Finset.powersetCard_one, Finset.sum_map]
  simp

end Generic

/-! ## Pure algebra: Newton identities (no primality needed) -/

section Newton

/-- `2·e₂ = S₁² − S₂`. -/
theorem two_mul_E_two (m p : ℕ) : 2 * E m p 2 = S m p 1 ^ 2 - S m p 2 := by
  have h := sum_sq_eq_sum_sq_add_two_mul_E2 (range (p - 1)) (invK m)
  simp only [S, E, pow_one]
  rw [h]; ring

/-- `6·e₃ = S₁³ − 3·S₁·S₂ + 2·S₃`. -/
theorem six_mul_E_three (m p : ℕ) :
    6 * E m p 3 = S m p 1 ^ 3 - 3 * S m p 1 * S m p 2 + 2 * S m p 3 := by
  have h := sum_cube_add_two_sum_cube_eq (range (p - 1)) (invK m)
  simp only [S, E, pow_one] at *
  linear_combination -h

end Newton

/-! ## Layer 2 — reduction of rationals into `ZMod m` (generic `m`) -/

section RatBridge
variable {m : ℕ}

/-- `ratToZMod q · den = num`. -/
theorem ratToZMod_mul_den (q : ℚ) (hq : Nat.Coprime q.den m) :
    ratToZMod m q * q.den = q.num := by
  unfold ratToZMod
  rw [mul_assoc, mul_comm _ ((q.den : ZMod m)), ZMod.coe_mul_inv_eq_one _ hq, mul_one]

/-- Characterization: if `q · d = a` with `d` a unit mod `m`, then `ratToZMod q · d = a`. -/
theorem ratToZMod_mul_of_eq (q : ℚ) (hq : Nat.Coprime q.den m) (d : ℕ) (a : ℤ)
    (h : q * d = a) : ratToZMod m q * d = a := by
  have hu : IsUnit ((q.den : ZMod m)) := (ZMod.unitOfCoprime _ hq).isUnit
  have hz : (q.num : ℚ) * d = a * q.den := by
    rw [← Rat.mul_den_eq_num, mul_right_comm, h]
  have hz' : q.num * (d : ℤ) = a * (q.den : ℤ) := by exact_mod_cast hz
  apply hu.mul_left_cancel
  have := congrArg (fun z : ℤ => (z : ZMod m)) hz'
  simp only [Int.cast_mul, Int.cast_natCast] at this
  calc (q.den : ZMod m) * (ratToZMod m q * d) = (ratToZMod m q * q.den) * d := by ring
    _ = q.num * d := by rw [ratToZMod_mul_den q hq]
    _ = a * q.den := this
    _ = q.den * a := by ring

/-- `ratToZMod` is additive on rationals whose denominators (and that of the sum) are units
mod `m`. -/
theorem ratToZMod_add (a b : ℚ) (ha : Nat.Coprime a.den m) (hb : Nat.Coprime b.den m)
    (hab : Nat.Coprime (a + b).den m) :
    ratToZMod m (a + b) = ratToZMod m a + ratToZMod m b := by
  have hu : IsUnit (((a.den * b.den : ℕ) : ZMod m)) :=
    (ZMod.unitOfCoprime _ (Nat.Coprime.mul_left ha hb)).isUnit
  apply hu.mul_left_cancel
  have h : (a + b) * ((a.den * b.den : ℕ) : ℚ) = a.num * b.den + b.num * a.den := by
    push_cast
    rw [add_mul, ← Rat.mul_den_eq_num a, ← Rat.mul_den_eq_num b]
    ring
  have h1 := ratToZMod_mul_of_eq (a + b) hab (a.den * b.den) (a.num * b.den + b.num * a.den)
    (by exact_mod_cast h)
  have ha' := ratToZMod_mul_den a ha
  have hb' := ratToZMod_mul_den b hb
  push_cast at h1 ⊢
  linear_combination h1 - (b.den : ZMod m) * ha' - (a.den : ZMod m) * hb'

/-- `1/k` reduces to the inverse of `k` in `ZMod m` when `k` is prime to `m`. -/
theorem ratToZMod_inv_natCast (k : ℕ) (hk : Nat.Coprime k m) :
    ratToZMod m ((k : ℚ)⁻¹) = (k : ZMod m)⁻¹ := by
  have hk0 : k ≠ 0 ∨ m = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · right; simpa using hk
    · left; omega
  have hden : Nat.Coprime ((k : ℚ)⁻¹).den m := by
    rw [Rat.inv_natCast_den]; split_ifs
    · exact Nat.coprime_one_left m
    · exact hk
  have hu : IsUnit ((k : ZMod m)) := (ZMod.unitOfCoprime _ hk).isUnit
  apply hu.mul_left_cancel
  rw [ZMod.coe_mul_inv_eq_one _ hk, mul_comm]
  rcases hk0 with hk0 | rfl
  · have := ratToZMod_mul_of_eq ((k : ℚ)⁻¹) hden k 1 
      (by push_cast; exact inv_mul_cancel₀ (by exact_mod_cast hk0))
    simpa using this
  · exact Subsingleton.elim _ _

/-- Reduction `ZMod n → ZMod m` sends `(i+1)⁻¹` to `(i+1)⁻¹` when `i+1` is a unit mod `n`. -/
theorem castHom_invK {m n : ℕ} (h : m ∣ n) (i : ℕ) (hc : Nat.Coprime (i + 1) n) :
    ZMod.castHom h (ZMod m) (invK n i) = invK m i := by
  have h1 : ((i + 1 : ℕ) : ZMod n) * invK n i = 1 := ZMod.coe_mul_inv_eq_one _ hc
  have h2 := congrArg (ZMod.castHom h (ZMod m)) h1
  rw [map_mul, map_natCast, map_one] at h2
  exact (ZMod.inv_eq_of_mul_eq_one m _ _ h2).symm

/-- Reduction `ZMod n → ZMod m` sends the power sum `S_j` to `S_j`, provided every
`k = 1, …, p−1` is a unit mod `n`. -/
theorem castHom_S_gen {m n : ℕ} (h : m ∣ n) (p j : ℕ)
    (hc : ∀ i ∈ range (p - 1), Nat.Coprime (i + 1) n) :
    ZMod.castHom h (ZMod m) (S n p j) = S m p j := by
  unfold S
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_pow, castHom_invK h i (hc i hi)]


/-- Rationals whose denominator is prime to `m` are closed under addition. -/
theorem coprime_den_add {a b : ℚ} (ha : Nat.Coprime a.den m) (hb : Nat.Coprime b.den m) :
    Nat.Coprime (a + b).den m :=
  Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (Nat.Coprime.mul_left ha hb)

/-- Rationals whose denominator is prime to `m` are closed under multiplication. -/
theorem coprime_den_mul {a b : ℚ} (ha : Nat.Coprime a.den m) (hb : Nat.Coprime b.den m) :
    Nat.Coprime (a * b).den m :=
  Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (Nat.Coprime.mul_left ha hb)

/-- An integer has denominator `1`, hence prime to every `m`. -/
theorem coprime_den_intCast (z : ℤ) : Nat.Coprime (z : ℚ).den m := by simp

/-- A natural number has denominator `1`, hence prime to every `m`. -/
theorem coprime_den_natCast (n : ℕ) : Nat.Coprime (n : ℚ).den m := by simp

/-- Rationals whose denominator is prime to `m` are closed under finite sums. -/
theorem coprime_den_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, Nat.Coprime (f i).den m) : Nat.Coprime (∑ i ∈ s, f i).den m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact coprime_den_add (h x (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Additivity of `ratToZMod`; the condition on the denominator of the sum is derived. -/
theorem ratToZMod_add' (a b : ℚ) (ha : Nat.Coprime a.den m) (hb : Nat.Coprime b.den m) :
    ratToZMod m (a + b) = ratToZMod m a + ratToZMod m b :=
  ratToZMod_add a b ha hb (coprime_den_add ha hb)

/-- `ratToZMod` is multiplicative on rationals whose denominators are units mod `m`. -/
theorem ratToZMod_mul (a b : ℚ) (ha : Nat.Coprime a.den m) (hb : Nat.Coprime b.den m) :
    ratToZMod m (a * b) = ratToZMod m a * ratToZMod m b := by
  have hu : IsUnit (((a.den * b.den : ℕ) : ZMod m)) :=
    (ZMod.unitOfCoprime _ (Nat.Coprime.mul_left ha hb)).isUnit
  apply hu.mul_left_cancel
  have h : (a * b) * ((a.den * b.den : ℕ) : ℚ) = a.num * b.num := by
    push_cast
    rw [← Rat.mul_den_eq_num a, ← Rat.mul_den_eq_num b]
    ring
  have h1 := ratToZMod_mul_of_eq (a * b) (coprime_den_mul ha hb) (a.den * b.den) (a.num * b.num)
    (by exact_mod_cast h)
  have ha' := ratToZMod_mul_den a ha
  have hb' := ratToZMod_mul_den b hb
  push_cast at h1 ⊢
  linear_combination h1 - (ratToZMod m b * (b.den : ZMod m)) * ha' - (a.num : ZMod m) * hb'

/-- `ratToZMod` sends an integer to its residue class. -/
theorem ratToZMod_intCast (z : ℤ) : ratToZMod m (z : ℚ) = z := by
  have := ratToZMod_mul_of_eq (m := m) (z : ℚ) (coprime_den_intCast z) 1 z (by simp)
  simpa using this

/-- `ratToZMod` sends a natural number to its residue class. -/
theorem ratToZMod_natCast (n : ℕ) : ratToZMod m (n : ℚ) = n := by
  have := ratToZMod_intCast (m := m) (n : ℤ)
  simpa using this

/-- `ratToZMod` commutes with finite sums of rationals whose denominators are units mod `m`. -/
theorem ratToZMod_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, Nat.Coprime (f i).den m) :
    ratToZMod m (∑ i ∈ s, f i) = ∑ i ∈ s, ratToZMod m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ratToZMod_natCast (m := m) 0
  | insert x s hx ih =>
    have hs : ∀ i ∈ s, Nat.Coprime (f i).den m := fun i hi => h i (mem_insert_of_mem hi)
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      ratToZMod_add' _ _ (h x (mem_insert_self _ _)) (coprime_den_sum s f hs), ih hs]

/-- Reduction `ZMod n → ZMod m` is compatible with `ratToZMod`. -/
theorem castHom_ratToZMod {m n : ℕ} (h : m ∣ n) (q : ℚ) (hq : Nat.Coprime q.den n) :
    ZMod.castHom h (ZMod m) (ratToZMod n q) = ratToZMod m q := by
  unfold ratToZMod
  rw [map_mul, map_intCast]
  congr 1
  have h1 : ((q.den : ZMod n)) * (q.den : ZMod n)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one _ hq
  have h2 := congrArg (ZMod.castHom h (ZMod m)) h1
  rw [map_mul, map_natCast, map_one] at h2
  exact (ZMod.inv_eq_of_mul_eq_one m _ _ h2).symm

end RatBridge

/-! ## Bridge ℚ ↔ `ZMod (p^n)` (reusable) -/

section Bridge

variable {p : ℕ} [Fact p.Prime]

/-- Every `k = i + 1 ≤ p − 1` is prime to `pᵃ`. -/
theorem coprime_succ_pow {a : ℕ} : ∀ i ∈ range (p - 1), Nat.Coprime (i + 1) (p ^ a) := by
  intro i hi
  have hp : p.Prime := Fact.out
  have := mem_range.1 hi
  refine Nat.Coprime.pow_right a ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  intro hd; have := Nat.le_of_dvd (Nat.succ_pos i) hd; omega

/-- The denominator of `H_n` divides `n!`. -/
theorem harmonic_den_dvd_factorial (n : ℕ) : (harmonic n).den ∣ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, Nat.factorial_succ]
    refine (Rat.add_den_dvd _ _).trans ?_
    rw [Rat.inv_natCast_den, if_neg (Nat.succ_ne_zero n), mul_comm]
    exact Nat.mul_dvd_mul_left _ ih

/-- (B1) The denominator of `H_{p-1}` is prime to `p` (it divides `(p-1)!`). -/
theorem harmonic_den_not_dvd : ¬ p ∣ (harmonic (p - 1)).den := by
  have hp : p.Prime := Fact.out
  intro h
  have := (Nat.Prime.dvd_factorial hp).1 (h.trans (harmonic_den_dvd_factorial (p - 1)))
  have := hp.two_le
  omega

/-- (B2) A rational whose denominator is prime to `p` vanishes in `ZMod (p^n)`
iff `p^n` divides its numerator. -/
theorem ratToZMod_eq_zero_iff (n : ℕ) (q : ℚ) (hq : ¬ p ∣ q.den) :
    ratToZMod (p ^ n) q = 0 ↔ ((p ^ n : ℕ) : ℤ) ∣ q.num := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime q.den (p ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hq))
  have hu : IsUnit ((q.den : ZMod (p ^ n))⁻¹) := by
    rw [← ZMod.coe_unitOfCoprime q.den hcop, ZMod.inv_coe_unit]
    exact Units.isUnit _
  unfold ratToZMod
  rw [hu.mul_left_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Partial harmonic sums `H_k`, `k ≤ p − 1`, reduce to `∑ 1/k` in `ZMod (p^n)`. -/
theorem ratToZMod_harmonic_le (n : ℕ) :
    ∀ k, k ≤ p - 1 → ratToZMod (p ^ n) (harmonic k) = ∑ i ∈ range k, invK (p ^ n) i := by
  have hp : p.Prime := Fact.out
  have cop : ∀ d, ¬ p ∣ d → Nat.Coprime d (p ^ n) := fun d hd =>
    Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hd))
  have hden : ∀ k, k ≤ p - 1 → ¬ p ∣ (harmonic k).den := by
    intro k hk h
    have := (Nat.Prime.dvd_factorial hp).1 (h.trans (harmonic_den_dvd_factorial k))
    have := hp.two_le
    omega
  intro k
  induction k with
  | zero => intro _; simp [ratToZMod]
  | succ k ih =>
    intro hk
    have hk1 : ¬ p ∣ (k + 1) := by
      intro h; have := Nat.le_of_dvd (Nat.succ_pos k) h; omega
    rw [harmonic_succ, ratToZMod_add _ _ (cop _ (hden k (by omega))) ?_ ?_, ih (by omega),
      Finset.sum_range_succ, ratToZMod_inv_natCast _ (cop _ hk1)]
    · rfl
    · rw [Rat.inv_natCast_den, if_neg (Nat.succ_ne_zero k)]; exact cop _ hk1
    · rw [← harmonic_succ]; exact cop _ (hden (k + 1) hk)

/-- (B3) `H_{p-1}` reduces to the power sum `S₁`. -/
theorem ratToZMod_harmonic (n : ℕ) :
    ratToZMod (p ^ n) (harmonic (p - 1)) = S (p ^ n) p 1 := by
  rw [ratToZMod_harmonic_le n (p - 1) le_rfl]
  simp only [S, pow_one]

/-- (B4) Reduction `ZMod (p^a) → ZMod (p^b)` commutes with the power sums. -/
theorem castHom_S {a b : ℕ} (hab : b ≤ a) (j : ℕ) :
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)) (S (p ^ a) p j) = S (p ^ b) p j :=
  castHom_S_gen _ p j coprime_succ_pow

/-- (B5) Reduction `ZMod (p^a) → ZMod p` commutes with the power sums. -/
theorem castHom_S_one {a : ℕ} (ha : a ≠ 0) (j : ℕ) :
    ZMod.castHom (dvd_pow_self p ha) (ZMod p) (S (p ^ a) p j) = S p p j :=
  castHom_S_gen _ p j coprime_succ_pow

/-- (B6) In `ZMod p⁴`, multiplying by `p` kills exactly the kernel of reduction mod `p³`. -/
theorem natCast_mul_eq_zero_iff (x : ZMod (p ^ 4)) :
    (p : ZMod (p ^ 4)) * x = 0 ↔
      ZMod.castHom (pow_dvd_pow p (by norm_num : 3 ≤ 4)) (ZMod (p ^ 3)) x = 0 := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ 4) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  have key : p * p ^ 3 ∣ p * x.val ↔ p ^ 3 ∣ x.val := Nat.mul_dvd_mul_iff_left hp.pos
  rwa [← pow_succ'] at key

/-- If `x ≡ 0 (mod p)` in `ZMod (p^n)`, then `x = p·y`. -/
theorem exists_eq_p_mul {n : ℕ} (hn : n ≠ 0) (x : ZMod (p ^ n))
    (hx : ZMod.castHom (dvd_pow_self p hn) (ZMod p) x = 0) :
    ∃ y : ZMod (p ^ n), x = p * y := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_mul]⟩

/-- (B7) If `x ≡ 0 (mod p)` then `p^k · x = 0` in `ZMod p^(k+1)`. Used with `k = 2, 3`. -/
theorem pow_mul_eq_zero_of_castHom {k : ℕ} (x : ZMod (p ^ (k + 1)))
    (hx : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) x = 0) :
    (p : ZMod (p ^ (k + 1))) ^ k * x = 0 := by
  obtain ⟨y, rfl⟩ := exists_eq_p_mul (Nat.succ_ne_zero k) x hx
  rw [← mul_assoc, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- (B8) The binomial coefficient as a product of units. -/
theorem choose_cast_eq_prod (n : ℕ) :
    (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ n)) =
      ∏ i ∈ range (p - 1), (1 + (p : ZMod (p ^ n)) * invK (p ^ n) i) := by
  have hp : p.Prime := Fact.out
  have hcop := coprime_succ_pow (p := p) (a := n)
  have hfact : Nat.Coprime (p - 1).factorial (p ^ n) := by
    rw [Nat.factorial_eq_prod_range_add_one]
    exact Nat.Coprime.prod_left hcop
  have hu : IsUnit (((p - 1).factorial : ℕ) : ZMod (p ^ n)) :=
    (ZMod.unitOfCoprime _ hfact).isUnit
  -- (p−1)!·C(2p−1, p−1) = (p+1)(p+2)⋯(2p−1) = ∏ (k + p), and (k + p) = k·(1 + p/k).
  -- Cancel the unit (p−1)! = ∏ k on both sides.
  apply hu.mul_left_cancel
  have h1 : (p - 1).factorial * (2 * p - 1).choose (p - 1) = ∏ i ∈ range (p - 1), (p + 1 + i) := by
    rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose,
      show p + (p - 1) = 2 * p - 1 by omega]
  rw [← Nat.cast_mul, h1, Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hinv : ((i + 1 : ℕ) : ZMod (p ^ n)) * invK (p ^ n) i = 1 :=
    ZMod.coe_mul_inv_eq_one _ (hcop i hi)
  push_cast at hinv ⊢
  linear_combination (-(p : ZMod (p ^ n))) * hinv

omit [Fact p.Prime] in
/-- `p⁴ = 0` in `ZMod p⁴`. -/
theorem natCast_pow_four : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- `6` is a unit in `ZMod p⁴` for `p ≥ 5`. -/
theorem six_isUnit (hp5 : 5 ≤ p) : IsUnit (6 : ZMod (p ^ 4)) := by
  have hp : p.Prime := Fact.out
  have h6 : Nat.Coprime 6 (p ^ 4) := by
    refine Nat.Coprime.pow_right 4 ?_
    rw [show (6 : ℕ) = 2 * 3 by rfl]
    exact Nat.Coprime.mul_left
      ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
      ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
  simpa using (ZMod.isUnit_iff_coprime 6 (p ^ 4)).2 h6

/-- `2` is a unit in `ZMod p⁴` for odd `p`. -/
theorem two_isUnit (hp5 : 5 ≤ p) : IsUnit (2 : ZMod (p ^ 4)) := by
  have h2 : Nat.Coprime 2 (p ^ 4) :=
    Nat.Coprime.pow_right 4
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (by omega))
  simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 4)).2 h2

end Bridge

/-! ## The mathematics -/

section Math

variable {p : ℕ} [Fact p.Prime]

/-- (1) Power sums of inverses vanish mod `p` unless `(p-1) ∣ j`.
Proof idea: `k ↦ k⁻¹` permutes `(ZMod p)ˣ`, then `FiniteField.sum_pow_units`. -/
theorem harmonic_sum_pow_mod {j : ℕ} (hj : ¬ (p - 1) ∣ j) : S p p j = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hne : ∀ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro i hi h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (Nat.succ_pos i) h
    have := mem_range.1 hi
    omega
  -- reindex k = i + 1 over the units of ZMod p
  have h1 : S p p j = ∑ u : (ZMod p)ˣ, ((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ j := by
    unfold S invK
    refine Finset.sum_bij' (fun i hi => Units.mk0 _ (hne i hi))
      (fun u _ => (u : ZMod p).val - 1) (fun _ _ => mem_univ _) ?_ ?_ ?_ ?_
    · intro u _
      have hv := ZMod.val_lt (u : ZMod p)
      have h0 : (u : ZMod p).val ≠ 0 := by
        rw [ne_eq, ZMod.val_eq_zero]; exact u.ne_zero
      rw [mem_range]; omega
    · intro i hi
      have := mem_range.1 hi
      simp only [Units.val_mk0, ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · intro u _
      have h0 : (u : ZMod p).val ≠ 0 := by
        rw [ne_eq, ZMod.val_eq_zero]; exact u.ne_zero
      ext
      simp only [Units.val_mk0]
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), ZMod.natCast_zmod_val]
    · intro i hi
      simp [Units.val_inv_eq_inv_val]
  -- `u ↦ u⁻¹` permutes the units, so the sum of `(u⁻¹)^j` equals the sum of `u^j` …
  have h2 : ∑ u : (ZMod p)ˣ, ((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ j
      = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ j :=
    Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
  rw [h1, h2]
  -- … which is `0` by `FiniteField.sum_pow_units`, since `(p − 1) ∤ j`.
  have := FiniteField.sum_pow_units (K := ZMod p) j
  simpa [ZMod.card, hj] using this

omit [Fact p.Prime] in
/-- (2) Expansion of the product up to order `p³` (the `p⁴` terms vanish in `ZMod p⁴`),
via the generic `prod_one_add_mul_of_pow_four_eq_zero`. -/
theorem binomial_product_expansion :
    ∏ i ∈ range (p - 1), (1 + (p : ZMod (p ^ 4)) * invK (p ^ 4) i) =
      1 + (p : ZMod (p ^ 4)) * S (p ^ 4) p 1 + (p : ZMod (p ^ 4)) ^ 2 * E (p ^ 4) p 2
        + (p : ZMod (p ^ 4)) ^ 3 * E (p ^ 4) p 3 := by
  rw [prod_one_add_mul_of_pow_four_eq_zero _ _ _ natCast_pow_four, sum_powersetCard_one]
  simp only [S, E, pow_one]

/-- `S₁ ≡ 0` and `S₃ ≡ 0 (mod p)`, written as divisibility by `p` in `ZMod p⁴`. -/
theorem S_one_eq_p_mul (hp5 : 5 ≤ p) :
    ∃ y : ZMod (p ^ 4), S (p ^ 4) p 1 = (p : ZMod (p ^ 4)) * y := by
  refine exists_eq_p_mul (by norm_num) _ ?_
  rw [castHom_S_one (by norm_num) 1]
  exact harmonic_sum_pow_mod (fun h => by have := Nat.le_of_dvd one_pos h; omega)

/-- `S₃ ≡ 0 (mod p)`, written as `S₃ = p·y` in `ZMod p⁴` (uses `p ≥ 5`, so `p − 1 ∤ 3`). -/
theorem S_three_eq_p_mul (hp5 : 5 ≤ p) :
    ∃ y : ZMod (p ^ 4), S (p ^ 4) p 3 = (p : ZMod (p ^ 4)) * y := by
  refine exists_eq_p_mul (by norm_num) _ ?_
  rw [castHom_S_one (by norm_num) 3]
  exact harmonic_sum_pow_mod (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)

/-- (3) Pairing `k ↔ p − k`: `2·H ≡ −p·H₂ (mod p³)`, stated after multiplying by `p`.
Proof: with `x = 1/k`, `y = 1/(p−k)`: `x + y = p·x·y`, hence
`p(x+y) + p²x² = −p³x³ + p⁴x³y`; summing (and `∑ y = ∑ x` by reflection) gives `−p³·S₃ = 0`. -/
theorem harmonic_pairing (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 4)) * (2 * S (p ^ 4) p 1 + (p : ZMod (p ^ 4)) * S (p ^ 4) p 2) = 0 := by
  have hcop := coprime_succ_pow (p := p) (a := 4)
  obtain ⟨y3, h3⟩ := S_three_eq_p_mul hp5
  set P : ZMod (p ^ 4) := (p : ZMod (p ^ 4)) with hP
  have hP4 : P ^ 4 = 0 := by rw [hP]; exact natCast_pow_four
  -- Write x = 1/k and y = 1/(p−k) for k = i + 1. Plan:
  --   (1) Σ y = Σ x = S₁ (reflection k ↦ p − k);
  --   (2) x + y = p·x·y, since k + (p − k) = p;
  --   (3) hence p(x+y) + p²x² = −p³x³ + p⁴(x³y), a polynomial identity given (2);
  --   (4) summing: p(2S₁ + pS₂) = −p³S₃ + 0, and S₃ = p·y₃ makes this −p⁴y₃ = 0.
  have hrefl : ∑ i ∈ range (p - 1), invK (p ^ 4) (p - 1 - 1 - i) = S (p ^ 4) p 1 := by
    simp only [S, pow_one]
    exact Finset.sum_range_reflect (invK (p ^ 4)) (p - 1)
  have hxy : ∀ i ∈ range (p - 1),
      invK (p ^ 4) i + invK (p ^ 4) (p - 1 - 1 - i)
        = P * invK (p ^ 4) i * invK (p ^ 4) (p - 1 - 1 - i) := by
    intro i hi
    have hi' := mem_range.1 hi
    have h1 : ((i + 1 : ℕ) : ZMod (p ^ 4)) * invK (p ^ 4) i = 1 :=
      ZMod.coe_mul_inv_eq_one _ (hcop i hi)
    have hmem : p - 1 - 1 - i ∈ range (p - 1) := mem_range.2 (by omega)
    have h2 : ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 4)) * invK (p ^ 4) (p - 1 - 1 - i) = 1 :=
      ZMod.coe_mul_inv_eq_one _ (hcop _ hmem)
    have h4 : ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 4)) = P - ((i + 1 : ℕ) : ZMod (p ^ 4)) := by
      rw [hP, show p - 1 - 1 - i + 1 = p - (i + 1) by omega, Nat.cast_sub (by omega)]
    rw [h4] at h2
    linear_combination (-(invK (p ^ 4) i)) * h2 - (invK (p ^ 4) (p - 1 - 1 - i)) * h1
  -- step (3), termwise
  have key : ∀ i ∈ range (p - 1),
      P * (invK (p ^ 4) i + invK (p ^ 4) (p - 1 - 1 - i)) + P ^ 2 * invK (p ^ 4) i ^ 2
        = -(P ^ 3 * invK (p ^ 4) i ^ 3)
          + P ^ 4 * (invK (p ^ 4) i ^ 3 * invK (p ^ 4) (p - 1 - 1 - i)) := by
    intro i hi
    linear_combination (P + P ^ 2 * invK (p ^ 4) i + P ^ 3 * invK (p ^ 4) i ^ 2) * hxy i hi
  have hS1 : ∑ i ∈ range (p - 1), invK (p ^ 4) i = S (p ^ 4) p 1 := by simp only [S, pow_one]
  calc P * (2 * S (p ^ 4) p 1 + P * S (p ^ 4) p 2)
      = ∑ i ∈ range (p - 1), (P * (invK (p ^ 4) i + invK (p ^ 4) (p - 1 - 1 - i))
          + P ^ 2 * invK (p ^ 4) i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
          hrefl, hS1]
        simp only [S]
        ring
    _ = ∑ i ∈ range (p - 1), (-(P ^ 3 * invK (p ^ 4) i ^ 3)
          + P ^ 4 * (invK (p ^ 4) i ^ 3 * invK (p ^ 4) (p - 1 - 1 - i))) :=
        Finset.sum_congr rfl key
    _ = -(P ^ 3 * S (p ^ 4) p 3)
          + P ^ 4 * ∑ i ∈ range (p - 1), invK (p ^ 4) i ^ 3 * invK (p ^ 4) (p - 1 - 1 - i) := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl
    _ = 0 := by
        rw [h3]
        linear_combination
          (-y3 + ∑ i ∈ range (p - 1), invK (p ^ 4) i ^ 3 * invK (p ^ 4) (p - 1 - 1 - i)) * hP4

/-- `p²·S₁² = 0` in `ZMod p⁴`, because `S₁ ≡ 0 (mod p)`. -/
theorem p_sq_mul_S_one_sq (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 2 * S (p ^ 4) p 1 ^ 2 = 0 := by
  obtain ⟨y, hy⟩ := S_one_eq_p_mul hp5
  rw [hy]
  linear_combination y ^ 2 * natCast_pow_four (p := p)

/-- `p³·e₃ = 0` in `ZMod p⁴`, because `e₃ ≡ 0 (mod p)`. -/
theorem p_cube_mul_E_three (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 3 * E (p ^ 4) p 3 = 0 := by
  obtain ⟨y1, h1⟩ := S_one_eq_p_mul hp5
  obtain ⟨y3, h3⟩ := S_three_eq_p_mul hp5
  apply (six_isUnit hp5).mul_left_cancel
  have h6 := six_mul_E_three (p ^ 4) p
  rw [h1, h3] at h6
  rw [mul_zero]
  linear_combination (p : ZMod (p ^ 4)) ^ 3 * h6
    + (p ^ 2 * y1 ^ 3 - 3 * y1 * S (p ^ 4) p 2 + 2 * y3) * natCast_pow_four (p := p)

/-- (4) Main congruence: `C(2p−1, p−1) − 1 ≡ 2p·H_{p−1} (mod p⁴)`. -/
theorem binomial_harmonic_congruence (hp5 : 5 ≤ p) :
    (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 4)) - 1 =
      2 * (p : ZMod (p ^ 4)) * S (p ^ 4) p 1 := by
  -- C − 1 = p·S₁ + p²·e₂ + p³·e₃ (product expansion). Multiply by 2 and use
  -- 2e₂ = S₁² − S₂ (Newton), p²S₁² = 0, p³e₃ = 0 and p²S₂ = −2p·S₁ (pairing):
  -- 2(C − 1) = 2pS₁ + p²S₁² − p²S₂ + 2p³e₃ = 2pS₁ + 2pS₁ = 2·(2pS₁).
  rw [choose_cast_eq_prod, binomial_product_expansion]
  apply (two_isUnit hp5).mul_left_cancel
  have newton2 := two_mul_E_two (p ^ 4) p
  have hS1sq := p_sq_mul_S_one_sq hp5
  have hE3 := p_cube_mul_E_three hp5
  have hpair := harmonic_pairing hp5
  linear_combination (p : ZMod (p ^ 4)) ^ 2 * newton2 + hS1sq + 2 * hE3 - hpair

/-- (5) The core equivalence, for primes `p ≥ 5`. -/
theorem wolstenholme_core (hp5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔ ((p ^ 3 : ℕ) : ℤ) ∣ (harmonic (p - 1)).num := by
  -- C ≡ 1 (mod p⁴)  ⇔  2p·S₁ = 0 in ZMod p⁴        (main congruence)
  --                 ⇔  p·S₁ = 0                     (2 is a unit)
  --                 ⇔  S₁ = 0 in ZMod p³            (multiplying by p)
  --                 ⇔  H_{p−1} ≡ 0 in ZMod p³       (S₁ is the reduction of H_{p−1})
  --                 ⇔  p³ ∣ num H_{p−1}             (its denominator is prime to p)
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, ← sub_eq_zero,
    binomial_harmonic_congruence hp5, mul_assoc, (two_isUnit hp5).mul_right_eq_zero,
    natCast_mul_eq_zero_iff, castHom_S (by norm_num : 3 ≤ 4) 1, ← ratToZMod_harmonic 3,
    ratToZMod_eq_zero_iff 3 _ harmonic_den_not_dvd]

end Math

/-! ## The Formal Conjectures statement -/

/-- **Part I, final statement** (Formal Conjectures `wolstenholme_harmonic`): `p` is a Wolstenholme
prime iff `p > 7`, `p` is prime and `p³` divides the numerator of `H_{p−1}`. -/
theorem wolstenholme_harmonic (p : ℕ) :
    IsWolstenholmePrime p ↔ (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num := by
  unfold IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hpr, hmod⟩
    have := Fact.mk hpr
    exact ⟨h7, hpr, (wolstenholme_core (by omega)).1 hmod⟩
  · rintro ⟨h7, hpr, hdvd⟩
    have := Fact.mk hpr
    exact ⟨h7, hpr, (wolstenholme_core (by omega)).2 hdvd⟩


/-! ## Part II — `wolstenholme_bernoulli`

Route (no Kummer congruence, which Mathlib lacks):
* Step A (Faulhaber + von Staudt–Clausen): `∑_{k<p} k^{p-3} ≡ p·B_{p-3} (mod p²)`.
* Step B (doubling `k ↦ 2k mod p`): `3·H_{p-1,2} ≡ 2·∑_{k<p} k^{p-3} (mod p²)`.
* With the pairing lemma: `p⁴ ∣ C(2p-1,p-1) - 1 ⇔ p³ ∣ H ⇔ p² ∣ H₂ ⇔ p ∣ B_{p-3}`.
-/

section BernoulliPart

variable {p : ℕ} [Fact p.Prime]

/-- Reindex `k = 1, …, p−1` by the units of `ZMod p`. -/
theorem sum_range_succ_eq_sum_units {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ range (p - 1), g (i + 1) = ∑ u : (ZMod p)ˣ, g (u : ZMod p).val := by
  have hp : p.Prime := Fact.out
  have hne : ∀ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro i hi h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (Nat.succ_pos i) h
    have := mem_range.1 hi
    omega
  -- Bijection `i ↦ unit (i+1)`, with inverse `u ↦ val u − 1`. The four goals: the inverse lands in
  -- `range (p−1)`, the two maps are mutually inverse, and the summands agree.
  refine Finset.sum_bij' (fun i hi => Units.mk0 _ (hne i hi))
    (fun u _ => (u : ZMod p).val - 1) (fun _ _ => mem_univ _) ?_ ?_ ?_ ?_
  · intro u _
    have hv := ZMod.val_lt (u : ZMod p)
    have h0 : (u : ZMod p).val ≠ 0 := by
      rw [ne_eq, ZMod.val_eq_zero]; exact u.ne_zero
    rw [mem_range]; omega
  · intro i hi
    have := mem_range.1 hi
    simp only [Units.val_mk0, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro u _
    have h0 : (u : ZMod p).val ≠ 0 := by
      rw [ne_eq, ZMod.val_eq_zero]; exact u.ne_zero
    ext
    simp only [Units.val_mk0]
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), ZMod.natCast_zmod_val]
  · intro i hi
    have := mem_range.1 hi
    simp only [Units.val_mk0, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- Doubling permutes `1, …, p−1` modulo `p`. -/
theorem sum_range_double (hp3 : 3 ≤ p) {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ range (p - 1), g (i + 1) = ∑ i ∈ range (p - 1), g (2 * (i + 1) % p) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [sum_range_succ_eq_sum_units g,
    sum_range_succ_eq_sum_units (fun k => g (2 * k % p))]
  refine (Fintype.sum_equiv (Equiv.mulLeft (Units.mk0 2 h2)) _ _ (fun u => ?_)).symm
  have h2p : (2 : ZMod p).val = 2 := by
    rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [Equiv.coe_mulLeft, Units.val_mul, Units.val_mk0, ZMod.val_mul, h2p]

omit [Fact p.Prime] in
/-- `p² = 0` in `ZMod p²`. -/
theorem natCast_sq_self : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- If `z ≡ 0 (mod p)`, then `p·z = 0` in `ZMod p²`. This is how facts that only hold mod `p`
(Fermat's little theorem) are used under a factor `p`. -/
theorem mul_eq_zero_of_castHom_two (z : ZMod (p ^ 2))
    (hz : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) z = 0) :
    (p : ZMod (p ^ 2)) * z = 0 := by
  obtain ⟨y, rfl⟩ := exists_eq_p_mul two_ne_zero z hz
  rw [← mul_assoc, ← sq, natCast_sq_self, zero_mul]

/-- Any `0 < r < p` is prime to `pᵃ`. -/
theorem coprime_of_pos_lt {r : ℕ} (a : ℕ) (h0 : 0 < r) (hr : r < p) : Nat.Coprime r (p ^ a) := by
  have hp : p.Prime := Fact.out
  refine Nat.Coprime.pow_right a ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_))
  intro h; have := Nat.le_of_dvd h0 h; omega

/-- `(A + ε)^n = A^n + n·A^(n-1)·ε` when `ε² = 0`. -/
theorem add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (A ε : R) (hε : ε ^ 2 = 0) (n : ℕ) :
    (A + ε) ^ n = A ^ n + n * A ^ (n - 1) * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      linear_combination ((n + 1 : R) * A ^ n) * hε

omit [Fact p.Prime] in
/-- Doubling, termwise, for `k⁻²`:  `4·r⁻² = k⁻² + p·f·k⁻³` where `2k = r + p f`. -/
theorem inv_sq_double (k f r : ℕ) (hrk : (r : ZMod (p ^ 2)) = 2 * k - p * f)
    (hk : Nat.Coprime k (p ^ 2)) (hr : Nat.Coprime r (p ^ 2)) :
    4 * ((r : ZMod (p ^ 2))⁻¹) ^ 2 =
      ((k : ZMod (p ^ 2))⁻¹) ^ 2 + p * f * ((k : ZMod (p ^ 2))⁻¹) ^ 3 := by
  have E1 : (r : ZMod (p ^ 2)) * (r : ZMod (p ^ 2))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one _ hr
  have E2 : (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one _ hk
  have E3 := natCast_sq_self (p := p)
  set xr := (r : ZMod (p ^ 2))⁻¹
  set xk := (k : ZMod (p ^ 2))⁻¹
  rw [hrk] at E1
  set P := (p : ZMod (p ^ 2))
  set F := (f : ZMod (p ^ 2))
  linear_combination (2 * xr + xk + P * F * xk * (xr + xk)) * (xk * E1 - 2 * xr * E2)
    + (F ^ 2 * xk ^ 2 * xr * (xr + xk)) * E3

omit [Fact p.Prime] in
/-- Doubling, termwise, for `k^(p-3)`. -/
theorem pow_double (n k f r : ℕ) (hrk : (r : ZMod (p ^ 2)) = 2 * k - p * f) :
    (r : ZMod (p ^ 2)) ^ n =
      (2 * k : ZMod (p ^ 2)) ^ n - n * (2 * k : ZMod (p ^ 2)) ^ (n - 1) * (p * f) := by
  have hε : (-(p * f : ZMod (p ^ 2))) ^ 2 = 0 := by
    linear_combination (f : ZMod (p ^ 2)) ^ 2 * natCast_sq_self (p := p)
  rw [hrk, sub_eq_add_neg, add_pow_of_sq_eq_zero _ _ hε]
  ring

/-- `3` is a unit in `ZMod p²` for `p ≥ 5`. -/
theorem three_isUnit_sq (hp5 : 5 ≤ p) : IsUnit (3 : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  have h3 : Nat.Coprime 3 (p ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
  simpa using (ZMod.isUnit_iff_coprime 3 (p ^ 2)).2 h3

/-- Step B: `3·H_{p-1,2} ≡ 2·∑_{k=1}^{p-1} k^{p-3} (mod p²)`, via `k ↦ 2k mod p` (no Kummer). -/
theorem three_S_two_eq (hp5 : 5 ≤ p) :
    3 * S (p ^ 2) p 2 = 2 * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3) := by
  have hp : p.Prime := Fact.out
  have hP2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := natCast_sq_self
  have hdiv : ∀ i ∈ range (p - 1), ((2 * (i + 1) % p : ℕ) : ZMod (p ^ 2)) =
      2 * ((i + 1 : ℕ) : ZMod (p ^ 2)) - p * ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) := by
    intro i _
    have h' : ((2 * (i + 1) % p : ℕ) : ZMod (p ^ 2)) + p * ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2))
        = 2 * ((i + 1 : ℕ) : ZMod (p ^ 2)) := by
      have := congrArg (Nat.cast : ℕ → ZMod (p ^ 2)) (Nat.mod_add_div (2 * (i + 1)) p)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat] at this
      exact this
    linear_combination h'
  have hrpos : ∀ i ∈ range (p - 1), 0 < 2 * (i + 1) % p := by
    intro i hi
    have := mem_range.1 hi
    rw [Nat.pos_iff_ne_zero]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 (Nat.dvd_of_mod_eq_zero h) with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (Nat.succ_pos i) h2; omega
  have hkcop : ∀ i ∈ range (p - 1), Nat.Coprime (i + 1) (p ^ 2) := coprime_succ_pow
  have hrcop : ∀ i ∈ range (p - 1), Nat.Coprime (2 * (i + 1) % p) (p ^ 2) :=
    fun i hi => coprime_of_pos_lt 2 (hrpos i hi) (Nat.mod_lt _ hp.pos)
  -- Notation: k = i + 1, r = 2k mod p, f = ⌊2k/p⌋, so 2k = r + p·f; doubling permutes 1, …, p−1.
  -- F = Σ f/k³,  G = Σ f·k^{p−4},  T = Σ k^{p−3}.
  -- (A) `3·S₂ = p·F`: sum 4/r² = 1/k² + p·f/k³ over k; Σ 1/r² = Σ 1/k² = S₂.
  have hA : 3 * S (p ^ 2) p 2 = (p : ZMod (p ^ 2)) * ∑ i ∈ range (p - 1),
      ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 := by
    have hperm := sum_range_double (p := p) (by omega) (fun k => ((k : ZMod (p ^ 2))⁻¹) ^ 2)
    have hS : S (p ^ 2) p 2 = ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 := rfl
    have h4 : 4 * S (p ^ 2) p 2 = S (p ^ 2) p 2 + (p : ZMod (p ^ 2)) * ∑ i ∈ range (p - 1),
        ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 := by
      calc 4 * S (p ^ 2) p 2
          = ∑ i ∈ range (p - 1), 4 * (((2 * (i + 1) % p : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 := by
            rw [hS, hperm, Finset.mul_sum]
        _ = ∑ i ∈ range (p - 1), ((((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2
              + p * ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2))
                * (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3) :=
            Finset.sum_congr rfl fun i hi =>
              inv_sq_double _ _ _ (hdiv i hi) (hkcop i hi) (hrcop i hi)
        _ = _ := by
            rw [Finset.sum_add_distrib, ← hS, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    linear_combination h4
  -- (B) the same permutation on `k^(p-3)`: r^{p−3} = (2k)^{p−3} − (p−3)(2k)^{p−4}·p·f,
  --     so T = 2^{p−3}·T − (p−3)·2^{p−4}·p·G.
  have hB : ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3) =
      2 ^ (p - 3) * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)
        - ((p - 3 : ℕ) : ZMod (p ^ 2)) * 2 ^ (p - 4) * p * ∑ i ∈ range (p - 1),
          ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 4) := by
    have hperm := sum_range_double (p := p) (by omega) (fun k => ((k : ZMod (p ^ 2))) ^ (p - 3))
    calc ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)
        = ∑ i ∈ range (p - 1), ((2 * (i + 1) % p : ℕ) : ZMod (p ^ 2)) ^ (p - 3) := hperm
      _ = ∑ i ∈ range (p - 1), (2 ^ (p - 3) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)
            - (((p - 3 : ℕ) : ZMod (p ^ 2)) * 2 ^ (p - 4) * p) *
              (((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 4))) :=
          Finset.sum_congr rfl fun i hi => by
            rw [pow_double (p - 3) _ _ _ (hdiv i hi), show p - 3 - 1 = p - 4 by omega,
              mul_pow, mul_pow]
            ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Fermat facts mod p, lifted as "p·(·) = 0" in ZMod p²:
  --   p·(2^{p−1} − 1) = 0,   T = p·t (since T ≡ 0 mod p),   p·G = p·F (k^{p−4} ≡ k^{−3}).
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h2F : (p : ZMod (p ^ 2)) * (2 ^ (p - 1) - 1) = 0 := by
    apply mul_eq_zero_of_castHom_two
    rw [map_sub, map_pow, map_ofNat, map_one, ZMod.pow_card_sub_one_eq_one h2, sub_self]
  have hT0 : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
      (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)) = 0 := by
    rw [map_sum]
    simp only [map_pow, map_natCast]
    rw [sum_range_succ_eq_sum_units (fun k => ((k : ZMod p)) ^ (p - 3))]
    simp only [ZMod.natCast_zmod_val]
    classical
    have := FiniteField.sum_pow_units (K := ZMod p) (p - 3)
    have hnd : ¬ (p - 1) ∣ (p - 3) := fun h => by
      have := Nat.le_of_dvd (by omega) h; omega
    simpa [ZMod.card, hnd] using this
  obtain ⟨t, ht⟩ := exists_eq_p_mul two_ne_zero _ hT0
  have hGF : (p : ZMod (p ^ 2)) * (∑ i ∈ range (p - 1),
      ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 4)
      - ∑ i ∈ range (p - 1),
      ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3) = 0 := by
    apply mul_eq_zero_of_castHom_two
    rw [map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := mem_range.1 hi
    have hinv := castHom_invK (dvd_pow_self p two_ne_zero) i (hkcop i hi)
    simp only [invK] at hinv
    rw [map_mul, map_mul, map_pow, map_pow, hinv]
    simp only [map_natCast]
    rw [← mul_sub]
    have hk0 : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff _ p).1 h
      have := Nat.le_of_dvd (Nat.succ_pos i) this; omega
    have hferm := ZMod.pow_card_sub_one_eq_one hk0
    have : ((i + 1 : ℕ) : ZMod p) ^ (p - 4) = (((i + 1 : ℕ) : ZMod p)⁻¹) ^ 3 := by
      rw [← mul_inv_eq_one₀ (pow_ne_zero 3 (inv_ne_zero hk0)), inv_pow, inv_inv, ← pow_add,
        show p - 4 + 3 = p - 1 by omega, hferm]
    rw [this, sub_self, mul_zero]
  have hc : ((p - 3 : ℕ) : ZMod (p ^ 2)) = p - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have e1 : (2 : ZMod (p ^ 2)) ^ (p - 1) = 4 * 2 ^ (p - 3) := by
    rw [show p - 1 = (p - 3) + 2 by omega, pow_add]; ring
  have e2 : (2 : ZMod (p ^ 2)) ^ (p - 1) = 8 * 2 ^ (p - 4) := by
    rw [show p - 1 = (p - 4) + 3 by omega, pow_add]; ring
  set T := ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)
  set G := ∑ i ∈ range (p - 1),
      ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 4)
  set F := ∑ i ∈ range (p - 1),
      ((2 * (i + 1) / p : ℕ) : ZMod (p ^ 2)) * (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3
  set P := (p : ZMod (p ^ 2))
  set c := ((p - 3 : ℕ) : ZMod (p ^ 2))
  -- Combine: 8T = 2·2^{p−1}·T − c·2^{p−1}·p·G; then 2^{p−1}T = T and c·2^{p−1}·p = −3p
  -- (c = p − 3, p² = 0) give 6T = 3pG = 3pF = 9S₂. Cancel the unit 3: 2T = 3S₂.
  have s1 : 8 * T = 2 * 2 ^ (p - 1) * T - c * 2 ^ (p - 1) * P * G := by
    linear_combination 8 * hB - 2 * T * e1 + c * P * G * e2
  have s2 : 2 ^ (p - 1) * T = T := by
    rw [ht]; linear_combination t * h2F
  have s3 : c * 2 ^ (p - 1) * P * G = -3 * P * G := by
    rw [hc]; linear_combination (P - 3) * G * h2F + G * hP2
  have s4 : 3 * (3 * S (p ^ 2) p 2 - 2 * T) = 0 := by
    linear_combination 3 * hA - 3 * hGF - (s1 + 2 * s2 - s3)
  rw [(three_isUnit_sq hp5).mul_right_eq_zero, sub_eq_zero] at s4
  exact s4

/-- `p` does not divide the denominator of `B_i` for `i < p − 1` (von Staudt–Clausen). -/
theorem bernoulli_den_coprime (a : ℕ) {i : ℕ} (hi : i < p - 1) :
    Nat.Coprime (bernoulli i).den (p ^ a) := by
  have hp : p.Prime := Fact.out
  have h2 := hp.two_le
  -- Cases: `i = 0` (B₀ = 1); `i = 2k ≥ 2` (von Staudt–Clausen); `i` odd ≥ 3 (Bᵢ = 0); `i = 1`
  -- (B₁ = −1/2).
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have : i = 0 := by omega
      subst this; simp
    -- von Staudt–Clausen: `B_{2k} = z − Σ 1/q` over primes `q` with `q − 1 ∣ 2k`. Each such `q`
    -- is `≤ 2k + 1 < p`, so every `1/q` has denominator prime to `p`.
    · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
      have hi2 : i = 2 * k := by omega
      subst hi2
      have hB : bernoulli (2 * k) = (z : ℚ) +
          -(∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q) := by
        rw [hz]; ring
      rw [hB]
      refine coprime_den_add (coprime_den_intCast z) ?_
      rw [Rat.neg_den]
      refine coprime_den_sum _ _ fun q hq => ?_
      rw [Finset.mem_filter, Finset.mem_range] at hq
      rw [one_div, Rat.inv_natCast_den, if_neg hq.2.1.ne_zero]
      exact coprime_of_pos_lt a hq.2.1.pos (by omega)
  · rcases Nat.lt_or_ge 1 i with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1]; simp
    -- `B₁ = −1/2`, and `2` is prime to `p`.
    · have : i = 1 := by obtain ⟨j, hj⟩ := hodd; omega
      subst this
      rw [bernoulli_one, show (-1 / 2 : ℚ) = ((-1 : ℤ) : ℚ) * ((2 : ℕ) : ℚ)⁻¹ by push_cast; ring]
      refine coprime_den_mul (coprime_den_intCast _) ?_
      rw [Rat.inv_natCast_den, if_neg two_ne_zero]
      exact coprime_of_pos_lt a (by norm_num) (by omega)

/-- Step A (Faulhaber + von Staudt): `∑_{k=1}^{p-1} k^{p-3} ≡ p·B_{p-3} (mod p²)`. -/
theorem sum_pow_p_sub_three (hp5 : 5 ≤ p) :
    ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3) =
      (p : ZMod (p ^ 2)) * ratToZMod (p ^ 2) (bernoulli (p - 3)) := by
  have hp : p.Prime := Fact.out
  -- Faulhaber (`sum_range_pow`) with `n = p`, exponent `p − 3`:
  -- `Σ_{k<p} k^{p−3} = Σ_{i ≤ p−3} Bᵢ · C(p−2, i) · p^{p−2−i} / (p−2)`.
  -- We reduce both sides mod p².
  have hF := sum_range_pow p (p - 3)
  rw [show p - 3 + 1 = p - 2 by omega] at hF
  -- left side: drop `k = 0`, cast
  have hd : ((p - 3 : ℕ) : ℚ) + 1 = ((p - 2 : ℕ) : ℚ) := by
    rw [show p - 2 = (p - 3) + 1 by omega]; push_cast; ring
  rw [hd] at hF
  have hL : ∑ k ∈ range p, (k : ℚ) ^ (p - 3) =
      ((∑ i ∈ range (p - 1), (i + 1) ^ (p - 3) : ℕ) : ℚ) := by
    have h := Finset.sum_range_succ' (fun k => (k : ℚ) ^ (p - 3)) (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    rw [h, Nat.cast_zero, zero_pow (by omega), add_zero]
    push_cast
    rfl
  rw [hL] at hF
  rw [show (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3)) =
      ((∑ i ∈ range (p - 1), (i + 1) ^ (p - 3) : ℕ) : ZMod (p ^ 2)) by push_cast; rfl,
    ← ratToZMod_natCast (m := p ^ 2), hF]
  -- right side: termwise. The last Faulhaber term (i = p − 3) is p·B_{p−3}; every other term
  -- carries p^{p−2−i} with exponent ≥ 2, which is 0 in ZMod p². All denominators are prime to p.
  have hden : ∀ i ∈ range (p - 2), Nat.Coprime
      (bernoulli i * ((p - 2).choose i : ℚ) * (p : ℚ) ^ (p - 2 - i) / ((p - 2 : ℕ) : ℚ)).den
        (p ^ 2) := by
    intro i hi
    have hi' := mem_range.1 hi
    rw [div_eq_mul_inv]
    refine coprime_den_mul (coprime_den_mul (coprime_den_mul
      (bernoulli_den_coprime 2 (by omega)) (coprime_den_natCast _)) ?_) ?_
    · rw [← Nat.cast_pow]; exact coprime_den_natCast _
    · rw [Rat.inv_natCast_den, if_neg (by omega)]
      exact coprime_of_pos_lt 2 (by omega) (by omega)
  have hcop2 : Nat.Coprime (p - 2) (p ^ 2) := coprime_of_pos_lt 2 (by omega) (by omega)
  have hterm : ∀ i ∈ range (p - 2), ratToZMod (p ^ 2)
      (bernoulli i * ((p - 2).choose i : ℚ) * (p : ℚ) ^ (p - 2 - i) / ((p - 2 : ℕ) : ℚ)) =
        ratToZMod (p ^ 2) (bernoulli i) * ((p - 2).choose i : ZMod (p ^ 2)) *
          (p : ZMod (p ^ 2)) ^ (p - 2 - i) * ((p - 2 : ℕ) : ZMod (p ^ 2))⁻¹ := by
    intro i hi
    have hi' := mem_range.1 hi
    have hBi := bernoulli_den_coprime (p := p) 2 (i := i) (by omega)
    rw [div_eq_mul_inv, ← Nat.cast_pow,
      ratToZMod_mul _ _ (coprime_den_mul (coprime_den_mul hBi (coprime_den_natCast _))
        (coprime_den_natCast _)) (by rw [Rat.inv_natCast_den, if_neg (by omega)]; exact hcop2),
      ratToZMod_mul _ _ (coprime_den_mul hBi (coprime_den_natCast _)) (coprime_den_natCast _),
      ratToZMod_mul _ _ hBi (coprime_den_natCast _), ratToZMod_natCast, ratToZMod_natCast,
      ratToZMod_inv_natCast _ hcop2, Nat.cast_pow]
  -- Split off the last term `i = p − 3`, where `C(p−2, p−3) = p − 2` cancels the denominator,
  -- leaving `p·B_{p−3}`. All other terms vanish because they carry `p²`.
  rw [ratToZMod_sum _ _ hden, Finset.sum_congr rfl hterm,
    show range (p - 2) = range (p - 3 + 1) by congr 1; omega, Finset.sum_range_succ,
    Finset.sum_eq_zero (fun i hi => by
      have hi' := mem_range.1 hi
      have h0 : (p : ZMod (p ^ 2)) ^ (p - 2 - i) = 0 := by
        rw [show p - 2 - i = 2 + (p - 4 - i) by omega, pow_add, natCast_sq_self, zero_mul]
      rw [h0, mul_zero, zero_mul]), zero_add,
    show p - 2 - (p - 3) = 1 by omega, pow_one,
    show (p - 2).choose (p - 3) = p - 2 by
      rw [show p - 3 = p - 2 - 1 by omega, Nat.choose_symm (by omega : 1 ≤ p - 2),
        Nat.choose_one_right]]
  have hu := ZMod.coe_mul_inv_eq_one (p - 2) hcop2
  linear_combination (ratToZMod (p ^ 2) (bernoulli (p - 3)) * p) * hu

omit [Fact p.Prime] in
/-- In `ZMod p^(n+1)`, `p·x = 0` iff `x ≡ 0 (mod pⁿ)`. -/
theorem natCast_mul_eq_zero_iff_pow (hp0 : 0 < p) {n : ℕ} (x : ZMod (p ^ (n + 1))) :
    (p : ZMod (p ^ (n + 1))) * x = 0 ↔
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x = 0 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp0.ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  have key : p * p ^ n ∣ p * x.val ↔ p ^ n ∣ x.val := Nat.mul_dvd_mul_iff_left hp0
  rwa [← pow_succ'] at key

/-- `2` is a unit in `ZMod pᵃ` for `p ≥ 5`. -/
theorem two_isUnit_pow (hp5 : 5 ≤ p) (a : ℕ) : IsUnit (2 : ZMod (p ^ a)) := by
  have hp : p.Prime := Fact.out
  have h2 : Nat.Coprime 2 (p ^ a) :=
    Nat.Coprime.pow_right a ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  simpa using (ZMod.isUnit_iff_coprime 2 (p ^ a)).2 h2

/-- Core equivalence for `wolstenholme_bernoulli`. -/
theorem wolstenholme_bernoulli_core (hp5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔ (p : ℤ) ∣ (bernoulli (p - 3)).num := by
  have hp : p.Prime := Fact.out
  rw [wolstenholme_core hp5, ← ratToZMod_eq_zero_iff 3 _ harmonic_den_not_dvd,
    ratToZMod_harmonic]
  -- pairing, reduced mod p³: 2·S₁ + p·S₂ = 0
  have hpair3 : 2 * S (p ^ 3) p 1 + (p : ZMod (p ^ 3)) * S (p ^ 3) p 2 = 0 := by
    have h := harmonic_pairing hp5
    rw [natCast_mul_eq_zero_iff] at h
    rw [map_add, map_mul, map_mul, map_ofNat, map_natCast, castHom_S (by norm_num : 3 ≤ 4) 1,
      castHom_S (by norm_num : 3 ≤ 4) 2] at h
    exact h
  have step1 : S (p ^ 3) p 1 = 0 ↔ (p : ZMod (p ^ 3)) * S (p ^ 3) p 2 = 0 := by
    constructor
    · intro h; linear_combination hpair3 - 2 * h
    · intro h
      have h2 : 2 * S (p ^ 3) p 1 = 0 := by linear_combination hpair3 - h
      exact ((two_isUnit_pow hp5 3).mul_right_eq_zero).1 h2
  rw [step1, natCast_mul_eq_zero_iff_pow hp.pos (n := 2), castHom_S (by norm_num) 2]
  -- `S₂ ≡ 0 (mod p²)` iff `T ≡ 0`  (Step B: 3S₂ = 2T, with 2 and 3 units);
  -- then `T = p·B_{p−3}` (Step A), and `p·B ≡ 0 (mod p²)` iff `B ≡ 0 (mod p)`.
  have hB := three_S_two_eq hp5
  have step2 : S (p ^ 2) p 2 = 0 ↔
      ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3) = 0 := by
    constructor
    · intro h
      have : 2 * ∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 2)) ^ (p - 3) = 0 := by
        rw [← hB, h, mul_zero]
      exact ((two_isUnit_pow hp5 2).mul_right_eq_zero).1 this
    · intro h
      have : 3 * S (p ^ 2) p 2 = 0 := by rw [hB, h, mul_zero]
      exact ((three_isUnit_sq hp5).mul_right_eq_zero).1 this
  rw [step2, sum_pow_p_sub_three hp5, natCast_mul_eq_zero_iff_pow hp.pos (n := 1),
    castHom_ratToZMod _ _ (bernoulli_den_coprime 2 (by omega)),
    ratToZMod_eq_zero_iff 1 _ (fun h => by
      have := bernoulli_den_coprime (p := p) 1 (i := p - 3) (by omega)
      rw [pow_one] at this
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 ((Nat.coprime_comm).1 this) h), pow_one]

/-- The Formal Conjectures statement `wolstenholme_bernoulli`. -/
theorem wolstenholme_bernoulli (p : ℕ) :
    IsWolstenholmePrime p ↔ (p > 7) ∧ Nat.Prime p ∧ ↑p ∣ (bernoulli' (p - 3)).num := by
  unfold IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hpr, hmod⟩
    have := Fact.mk hpr
    refine ⟨h7, hpr, ?_⟩
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
    exact (wolstenholme_bernoulli_core (by omega)).1 hmod
  · rintro ⟨h7, hpr, hdvd⟩
    have := Fact.mk hpr
    refine ⟨h7, hpr, ?_⟩
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega)] at hdvd
    exact (wolstenholme_bernoulli_core (by omega)).2 hdvd

end BernoulliPart

end WolstenholmeHarmonic
