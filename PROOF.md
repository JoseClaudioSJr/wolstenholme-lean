# The proof, without Lean

This is a self-contained mathematical account of what `WolstenholmeHarmonic.lean` (Parts I and II)
and `Kummer.lean`, `Jensen.lean`, `RegularPrimesCheck.lean` (Part III) prove. Each step names the
Lean declaration that formalizes it, so the two can be read side by side. None of the results are
new; see the references in the README.

Throughout Parts I and II, `p ≥ 5` is a prime. (The Formal Conjectures statements assume `p > 7`,
which is stronger.) Part III states its hypotheses on `p` lemma by lemma.

## Notation

- `H_{p−1} = Σ_{k=1}^{p−1} 1/k` and `H_{p−1,2} = Σ_{k=1}^{p−1} 1/k²` are rational numbers.
- For `k = 1, …, p−1`, the integer `k` is a unit modulo every power of `p`. In `ℤ/pⁿ` we write
  `x_k = k⁻¹` and use the power sums `S_j = Σ_{k=1}^{p−1} x_k^j` and the elementary symmetric
  functions `e_j = e_j(x_1, …, x_{p−1})`. (Lean: `invK`, `S`, `E`.)
- **Reduction of rationals.** If `q = a/b` with `p ∤ b`, then `q mod pⁿ` means `a·b⁻¹` in `ℤ/pⁿ`
  (Lean: `ratToZMod`). It is additive and multiplicative, and it commutes with reduction from
  `ℤ/pⁿ` to `ℤ/pᵐ` for `m ≤ n`. Also, `q ≡ 0 (mod pⁿ)` holds exactly when `pⁿ` divides the
  numerator of `q`.
- **Denominators.** The denominator of `H_n` divides `n!`, so `H_{p−1} mod pⁿ = S₁`.
  (Lean: `harmonic_den_dvd_factorial`, `ratToZMod_harmonic`.) Likewise the denominator of
  `H_{n,2}` divides `(n!)²`, so `H_{p−1,2} mod pⁿ = S₂` (Lean: `harmonic2`,
  `harmonic2_den_dvd`, `ratToZMod_harmonic2`).
- **Wolstenholme primes.** `p` is a Wolstenholme prime when `C := C(2p−1, p−1) ≡ 1 (mod p⁴)`.

## Part I: `C − 1 ≡ 2p·H_{p−1} (mod p⁴)`, hence `wolstenholme_harmonic`

**Lemma 1 (power sums; `harmonic_sum_pow_mod`).** If `p − 1 ∤ j`, then `S_j ≡ 0 (mod p)`.

*Proof.* Modulo `p`, the map `k ↦ k⁻¹` permutes `(ℤ/p)ˣ`, so `S_j ≡ Σ_{u ∈ (ℤ/p)ˣ} u^j`. Let `g` be
a generator of `(ℤ/p)ˣ`. Since `p − 1 ∤ j`, we have `g^j ≠ 1`. Multiplying the sum by `g^j` only
permutes its terms, so `(g^j − 1)·Σ u^j = 0`, and therefore `Σ u^j = 0`. ∎

(In Lean, the last step is Mathlib's `FiniteField.sum_pow_units`, applied after the substitution
`u ↦ u⁻¹`.)

In particular `S₁ ≡ S₂ ≡ S₃ ≡ 0 (mod p)`, because `p − 1 ≥ 4`.

**Lemma 2 (product form; `choose_cast_eq_prod`).**
`C(2p−1, p−1) = ∏_{k=1}^{p−1} (p+k)/k = ∏_{k=1}^{p−1} (1 + p·x_k)` in `ℤ/pⁿ`.

This holds because `(p−1)!·C(2p−1, p−1) = (p+1)(p+2)⋯(2p−1)`, and `(p−1)!` is a unit.

**Lemma 3 (expansion; `binomial_product_expansion`).** In `ℤ/p⁴`,

    C = 1 + p·S₁ + p²·e₂ + p³·e₃.

Expanding the product gives `Σ_j p^j e_j`, and every term with `j ≥ 4` is zero because `p⁴ = 0`.
Also `e₁ = S₁`. In Lean this is the generic identity `∏(1 + c·aᵢ) = 1 + c·e₁ + c²·e₂ + c³·e₃`,
valid whenever `c⁴ = 0`.

**Lemma 4 (Newton identities; `two_mul_E_two`, `six_mul_E_three`).** In any commutative ring,

    2e₂ = S₁² − S₂,        6e₃ = S₁³ − 3S₁S₂ + 2S₃.

Consequently, in `ℤ/p⁴`:

- `p²S₁² = 0`. Indeed `S₁ = p·y` by Lemma 1, so `p²S₁² = p⁴y² = 0`.
- `p³e₃ = 0`. Indeed `6e₃ ≡ 0 (mod p)`, and `6` is a unit, so `e₃ ≡ 0 (mod p)`.

(Lean: `p_sq_mul_S_one_sq`, `p_cube_mul_E_three`.)

**Lemma 5 (pairing; `harmonic_pairing`).** `p·(2S₁ + p·S₂) = 0` in `ℤ/p⁴`.

*Proof.* Write `x = x_k` and `y = x_{p−k}`. From `1/k + 1/(p−k) = p/(k(p−k))` we get

    x + y = p·x·y.                                                        (∗)

Then

    p(x + y) + p²x² = p²x(y + x) = p³x²y,

using `(∗)` for the second equality. Using `(∗)` again in the form `y = −x + pxy` gives
`x²y = −x³ + p·x³y`, so

    p(x + y) + p²x² = −p³x³ + p⁴(⋯).

Now sum over `k`. Since `k ↦ p − k` permutes `1, …, p−1`, we have `Σ y = Σ x = S₁`, so the left
side sums to `2pS₁ + p²S₂`. The right side sums to `−p³S₃`. By Lemma 1, `S₃ = p·y₃`, so
`p³S₃ = p⁴y₃ = 0`. ∎

**Theorem A (`binomial_harmonic_congruence`).** `C − 1 ≡ 2p·S₁ (mod p⁴)`.

*Proof.* By Lemmas 3 and 4,

    2(C − 1) = 2pS₁ + p²(S₁² − S₂) + 2p³e₃ = 2pS₁ − p²S₂.

By Lemma 5, `−p²S₂ = 2pS₁`, so `2(C − 1) = 4pS₁`. Cancel the unit `2`. ∎

**Corollary (`wolstenholme_core`, `wolstenholme_harmonic`).** The following are equivalent:
`C ≡ 1 (mod p⁴)`; `2pS₁ ≡ 0 (mod p⁴)`; `S₁ ≡ 0 (mod p³)`; `p³ ∣ num(H_{p−1})`.

The last equivalence uses the notation section: `H_{p−1} mod p³ = S₁`.

**Corollary (Wolstenholme, 1862; `harmonic_num_dvd_sq`, `wolstenholme_theorem_mod_p_cube`).**
`H_{p−1} ≡ 0 (mod p²)` and `C ≡ 1 (mod p³)`.

*Proof.* Reduce Lemma 5 to `ℤ/p³`, which gives `2S₁ + p·S₂ ≡ 0`. Since `S₂ = p·y` by Lemma 1,
`2p·S₁ = −p³y ≡ 0 (mod p³)`, so `p·S₁ ≡ 0 (mod p³)`, that is, `S₁ ≡ 0 (mod p²)`. Theorem A
reduced mod `p³` then gives `C − 1 ≡ 2p·S₁ ≡ 0`. ∎

## Part II: `p⁴ ∣ C − 1 ⇔ p ∣ num(B_{p−3})`, hence `wolstenholme_bernoulli`

**Step 0 (from Lemma 5).** Reducing Lemma 5 from `ℤ/p⁴` to `ℤ/p³` gives `2S₁ + p·S₂ ≡ 0 (mod p³)`.
Hence

    S₁ ≡ 0 (mod p³)  ⇔  p·S₂ ≡ 0 (mod p³)  ⇔  S₂ ≡ 0 (mod p²),

In terms of rationals: `p³ ∣ num(H_{p−1})` if and only if `p² ∣ num(H_{p−1,2})`
(`harmonic_iff_harmonic2`).

Mathlib has no Kummer congruence, so the usual route from here to `B_{p−3}` is not available.
Steps A and B below replace it.

Let `T = Σ_{k=1}^{p−1} k^{p−3}`.

**Step A: `T ≡ p·B_{p−3} (mod p²)` (Faulhaber; `sum_pow_p_sub_three`).** With `m = p − 3`,
Faulhaber's formula (Mathlib's `sum_range_pow`) reads

    Σ_{k=0}^{p−1} k^m = (1/(m+1)) · Σ_{i=0}^{m} C(m+1, i) · Bᵢ · p^{m+1−i}.

- **The term `i = m`.** Since `C(m+1, m) = m + 1`, this term equals `p·B_{p−3}`.
- **The terms `i < m`.** Each carries `p^{m+1−i}` with `m + 1 − i ≥ 2`. Its denominator is prime
  to `p`:
  - `m + 1 = p − 2` is prime to `p`.
  - `Bᵢ` has denominator prime to `p` for every `i < p − 1` (`bernoulli_den_coprime`). For even
    `i ≥ 2`, von Staudt–Clausen writes `Bᵢ` as an integer minus `Σ 1/q` over primes `q` with
    `q − 1 ∣ i`, and every such `q` satisfies `q ≤ i + 1 < p`. Also `B₀ = 1`, `B₁ = −1/2`, and
    `Bᵢ = 0` for odd `i ≥ 3`.
  
  So these terms vanish modulo `p²`. ∎

**Step B: `3·S₂ ≡ 2·T (mod p²)` (doubling; `three_S_two_eq`).** For `k = 1, …, p−1`, write

    2k = r_k + p·f_k,    1 ≤ r_k ≤ p−1,    f_k = ⌊2k/p⌋ ∈ {0, 1}.

Because `2` is invertible mod `p`, the map `k ↦ r_k` permutes `1, …, p−1`. This holds for every
odd prime `p` (`sum_range_double`, `p ≥ 3`).
So any sum of `g(k)` over `k` equals the sum of `g(r_k)`. Apply this to two choices of `g`,
working in `ℤ/p²`:

1. **`g(k) = k⁻²`.** In general, if `k, r, f` are natural numbers with `r ≡ 2k − p·f (mod p²)`
   and `k`, `r` prime to `p`, then `1/r = (1/(2k))·(1 + p·f/(2k))` in `ℤ/p²`, hence

       4/r² ≡ 1/k² + p·f/k³  (mod p²)                    (`inv_sq_double`)

   Apply this to `r_k`, `f_k`, sum over `k`, and get `4S₂ = S₂ + p·F`, where `F = Σ f_k/k³`
   (Lean: `Fz`). Therefore

       3·S₂ ≡ p·F  (mod p²).                              (B1, `three_S_two_eq_p_F`)

2. **`g(k) = k^{p−3}`.** In general, if `r ≡ 2k − p·f (mod p²)`, then for every exponent `n`

       r^n ≡ (2k)^n − n·(2k)^{n−1}·p·f  (mod p²)        (`pow_double`)

   because `(p·f)² = 0` stops the binomial expansion after two terms. Take `n = p − 3`.

   Summing over `k`, with `T = Σ k^{p−3}` (Lean: `Tz`) and `G = Σ f_k·k^{p−4}`:

       T = 2^{p−3}·T − (p−3)·2^{p−4}·p·G.

   Multiply by 8 and use three facts, each a consequence of Fermat's little theorem:
   - `p·2^{p−1} ≡ p`;
   - `T ≡ 0 (mod p)` (Lemma 1, applied to the units), so `2^{p−1}·T ≡ T`;
   - `p·k^{p−4} ≡ p·k^{−3}`, so `p·G ≡ p·F`.
   
   Together with `(p−3)·p ≡ −3p`, this gives `8T ≡ 2T + 3p·F`, that is, `6T ≡ 3p·F`. Cancelling
   the unit `3`:

       2·T ≡ p·F  (mod p²).                               (B2, `two_T_eq_p_F`)

Eliminating `F` between (B1) and (B2) gives `3·S₂ ≡ 2·T (mod p²)`. ∎

**Assembly (`wolstenholme_bernoulli_core`).** Since `2` and `3` are units mod `p`, the following
are equivalent:

- `C ≡ 1 (mod p⁴)`;
- `S₁ ≡ 0 (mod p³)` (Part I);
- `S₂ ≡ 0 (mod p²)` (Step 0);
- `T ≡ 0 (mod p²)` (Step B);
- `p·B_{p−3} ≡ 0 (mod p²)` (Step A);
- `B_{p−3} ≡ 0 (mod p)`;
- `p ∣ num(B_{p−3})`, because the denominator of `B_{p−3}` is prime to `p`.

**Conventions.** The Formal Conjectures statement uses Mathlib's `bernoulli'` (with `B₁ = +1/2`).
It agrees with `bernoulli` at every index `≠ 1`, in particular at `p − 3`.

## Remarks

- Steps A and B together give Glaisher's congruence `3·H_{p−1,2} ≡ 2p·B_{p−3} (mod p²)`, that is,
  `H_{p−1,2} ≡ (2/3)·p·B_{p−3}` (Lean: `glaisher`, stated as `p² ∣ num(3H_{p−1,2} − 2p·B_{p−3})`).
- Combined with (B1), it gives the classical `F ≡ 2B_{p−3} (mod p)` for the Voronoi–Lerch-type
  sum `F = Σ ⌊2k/p⌋/k³` (Lean: `voronoiF`, `voronoiF_mod_p`).
- Every step works in `ℤ/pⁿ`, and rationals enter only through the reduction map. This is why
  the Lean file separates a generic layer for reducing rationals from the number theory.

## Part III: Kummer's congruence (weak form) and Jensen's theorem

Here `p` is a prime, `B_n` is Mathlib's `bernoulli n` (`B₁ = −1/2`), and "`q` is `p`-integral"
means that `p` does not divide the denominator of the rational `q`. In this part the exponent `n`
may be much larger than `p`.

**Lemma III.1** (`bernoulli_den_coprime_of_not_dvd`). If `(p − 1) ∤ n`, then `B_n` is `p`-integral.

*Proof.* For odd `n ≥ 3`, `B_n = 0`. For `n = 1`, `(p − 1) ∤ 1` forces `p ≠ 2`, and `B₁ = −1/2`.
For `n = 2k`, von Staudt–Clausen gives `B_n = z − Σ 1/q` with `z ∈ ℤ`, over the primes `q` with
`(q − 1) ∣ n`; `p` is not among them, so every `1/q` is `p`-integral. ∎

**Lemma III.2** (`coprime_den_p_mul_bernoulli`, `p ≥ 3`). `p·B_i` is `p`-integral for every `i`.

*Proof.* The same cases. For `i = 2k`, `p·B_i = pz − Σ p/q`, and `p/q` equals `1` if `q = p`
and is `p`-integral otherwise. ∎

**Lemma III.3** (`coprime_den_pow_div`, `p ≥ 5`). For `m ≥ 3`, `p^{m−3}/m` is `p`-integral.

*Proof.* Write `m = pᵉ·m'` with `p ∤ m'`. If `e ≥ 1`, then `e + 3 ≤ 5ᵉ ≤ pᵉ ≤ m`; if `e = 0`, then
`e + 3 ≤ m` by hypothesis. So `p^{m−3}/m = p^{m−3−e}/m'`. ∎

**Proposition III.4** (`sum_pow_eq_p_mul_bernoulli`). Let `p ≥ 5` and let `n ≥ 2` be even with
`(p − 1) ∤ n`. Then `Σ_{k=1}^{p−1} kⁿ ≡ p·B_n (mod p²)`.

*Proof.* Faulhaber (`sum_range_pow`): `Σ_{k<p} kⁿ = Σ_{i=0}^{n} t_i` with
`t_i = B_i·C(n+1, i)·p^{n+1−i}/(n+1)`. The last term is `t_n = p·B_n`, and `B_n` is
`p`-integral by Lemma III.1. For `i < n`, the identity `C(n, i)·(n+1) = C(n+1, i)·(n+1−i)` gives
`t_i = p²·u_i` with `u_i = B_i·C(n, i)·p^{n−1−i}/(n+1−i)`, and `u_i` is `p`-integral:

- if `i = n − 1`, then `u_i = B_{n−1}·C(n, n−1)/2`; here `n − 1` is odd and `p − 1` is even, so
  `(p − 1) ∤ (n − 1)` and Lemma III.1 applies;
- if `i ≤ n − 2`, then `m = n + 1 − i ≥ 3` and `u_i = (p·B_i)·C(n, i)·(p^{m−3}/m)`, which is
  `p`-integral by Lemmas III.2 and III.3.

Reducing mod `p²` kills every `t_i` with `i < n`. ∎

**Lemma III.5** (`sum_range_mul`). If `p ∤ a`, then `k ↦ ak mod p` permutes `1, …, p−1`.

**Proposition III.6** (`voronoi_sq`). If `p ∤ a`, then for every `n`, in `ℤ/p²`,

    (aⁿ − 1)·Σ_{k=1}^{p−1} kⁿ = n·p·a^{n−1}·Σ_{k=1}^{p−1} ⌊ak/p⌋·k^{n−1}.

*Proof.* Write `ak = r_k + p·f_k` with `r_k = ak mod p` and `f_k = ⌊ak/p⌋`. Since `(p·f_k)² ≡ 0`,
`r_kⁿ = (ak − p f_k)ⁿ ≡ aⁿkⁿ − n·a^{n−1}k^{n−1}·p·f_k (mod p²)`. Sum over `k`; by Lemma III.5 the
left side sums to `Σ kⁿ`. ∎

**Theorem III.7** (`voronoi_mod_p`, Voronoi's congruence). Let `p ≥ 5`, `p ∤ a`, and `n ≥ 2` even
with `(p − 1) ∤ n`. Then

    (aⁿ − 1)·B_n ≡ n·a^{n−1}·Σ_{k=1}^{p−1} ⌊ak/p⌋·k^{n−1}   (mod p).

*Proof.* Substitute Proposition III.4 into Proposition III.6: `p·X ≡ 0 (mod p²)` with `X` the
difference of the two sides, so `X ≡ 0 (mod p)` (`castHom_eq_zero_of_p_mul`). ∎

**Theorem III.8** (`kummer_dvd`, the case of Kummer's congruence used by Jensen). Let `p ≥ 5` and
let `n ≥ 2` be even with `(p − 1) ∤ n` and `p ∤ n`. If `p ∣ num(B_n)`, then `p ∣ num(B_k)` for
`k = n mod (p − 1)`. Moreover `k` is even and `2 ≤ k ≤ p − 3` (`mod_sub_one_facts`).

*Proof.* Let `g` generate `(ℤ/p)ˣ`, so `g` has order `p − 1`, and let `a` be an integer lift of
`g`. Theorem III.7 applies to `n` and to `k`. Write `n = k + (p − 1)q`; by Fermat, `aⁿ ≡ aᵏ`,
`a^{n−1} ≡ a^{k−1}` and `j^{n−1} ≡ j^{k−1}` for `1 ≤ j ≤ p−1`, so the two right-hand sums agree;
call it `G`. Since `B_n ≡ 0` and `p ∤ n`, Theorem III.7 for `n` gives `a^{k−1}·G ≡ 0`; then
Theorem III.7 for `k` gives `(aᵏ − 1)·B_k ≡ 0`. Finally `aᵏ ≢ 1`, because `(p − 1) ∤ k`. ∎

**Lemma III.9** (`dvd_den_bernoulli`). If `k ≥ 1` and `(p − 1) ∣ 2k`, then `p` divides the
denominator of `B_{2k}`.

*Proof.* Here `p` is one of the primes in von Staudt–Clausen, so
`1 + p·B_{2k} + Σ_{q ≠ p} p/q = p·z`. If `B_{2k}` were `p`-integral, reducing mod `p` would give
`1 ≡ 0`. ∎

**Lemma III.10** (`one_lt_abs_bernoulli`). `|B_{2k}| > 1` for all large `k`.

*Proof.* Euler's formula (Mathlib's `hasSum_zeta_nat`) gives
`ζ(2k) = (−1)^{k+1}·2^{2k−1}·π^{2k}·B_{2k}/(2k)!`, and `ζ(2k) ≥ 1` (its first term is 1). Hence
`|B_{2k}| ≥ (2k)!/(2^{2k−1}π^{2k}) = 2·(2k)!/(2π)^{2k}`, which exceeds `2` once
`(2π)^{2k}/(2k)! < 1` (`FloorSemiring.tendsto_pow_div_factorial_atTop`). The argument is written
for an arbitrary `x > 0` in place of `π` in `one_lt_abs_bernoulli_of`. ∎

**Theorem III.11** (Jensen, 1915; `exists_irregular_gt`, `infinite_bernoulli_irregular`,
`jensen_bernoulli`). For every `P` there is a prime `p > P` and an even `k` with `2 ≤ k ≤ p − 3`
such that `p ∣ num(B_k)`. In particular there are infinitely many such primes.

*Proof.* Let `M = ∏_{q ≤ max(P, 4), q prime} (q − 1)` and `n = 2·2ᴷ·M`, with `K` from
Lemma III.10 (so `n/2 ≥ K`). Since `|B_n| > 1`, the numerator of `B_n` is not `±1`; let `p` be a
prime factor of it.

- `p` does not divide the denominator of `B_n` (numerator and denominator are coprime), so
  `(p − 1) ∤ n` by Lemma III.9.
- Hence `p > max(P, 4)`: every prime `q ≤ max(P, 4)` has `(q − 1) ∣ M ∣ n`. In particular
  `p ≥ 5`.
- `p ∤ n`: the prime factors of `n` are `2` and the prime factors of the numbers `q − 1`, all
  smaller than `p`.

Theorem III.8 then gives `p ∣ num(B_k)` for `k = n mod (p − 1)`, with `k` even and
`2 ≤ k ≤ p − 3`; and `bernoulli' k = bernoulli k` since `k ≠ 1`. ∎

**Corollary III.12** (`infinitude_of_irregularprimes_of_kummer`,
`infinitude_of_irregularprimes_of_iff`). With the Formal Conjectures definitions (`p` is regular
when it is prime to the class number of `ℚ(ζ_p)`): if every prime `p` dividing some `num(B_k)`,
`k` even, `2 ≤ k ≤ p − 3`, is irregular, then there are infinitely many irregular primes. In
particular this follows from Kummer's criterion as stated in Formal Conjectures
(`isRegularPrime_iff_Bernoulli`).

*What is not proved.* The hypothesis of Corollary III.12 (the easy direction of Kummer's
criterion) is not proved here; it needs the analytic class number formula for `ℚ(ζ_p)`. So the
Formal Conjectures statement `infinitude_of_irregularprimes` is reduced to Kummer's criterion, not
proved outright.
