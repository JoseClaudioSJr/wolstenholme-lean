# The proof, without Lean

This is a self-contained mathematical account of what `WolstenholmeHarmonic.lean` proves. Each
step names the Lean declaration that formalizes it, so the two can be read side by side. None of
the results are new; see the references in the README.

Throughout, `p ≥ 5` is a prime. (The Formal Conjectures statements assume `p > 7`, which is
stronger.)

## Notation

- `H_{p−1} = Σ_{k=1}^{p−1} 1/k` and `H_{p−1,2} = Σ_{k=1}^{p−1} 1/k²` are rational numbers.
- For `k = 1, …, p−1`, the integer `k` is a unit modulo every power of `p`. In `ℤ/pⁿ` we write
  `x_k = k⁻¹` and use the power sums `S_j = Σ_{k=1}^{p−1} x_k^j` and the elementary symmetric
  functions `e_j = e_j(x_1, …, x_{p−1})`. (Lean: `invK`, `S`, `E`.)
- **Reduction of rationals.** If `q = a/b` with `p ∤ b`, then `q mod pⁿ` means `a·b⁻¹` in `ℤ/pⁿ`
  (Lean: `ratToZMod`). It is additive and multiplicative, and it commutes with reduction from
  `ℤ/pⁿ` to `ℤ/pᵐ` for `m ≤ n`. Also, `q ≡ 0 (mod pⁿ)` holds exactly when `pⁿ` divides the
  numerator of `q`.
- **Denominators.** The denominator of `H_n` divides `n!`, so `H_{p−1} mod pⁿ = S₁` and
  `H_{p−1,2} mod pⁿ = S₂`. (Lean: `harmonic_den_dvd_factorial`, `ratToZMod_harmonic`.)
- **Wolstenholme primes.** `p` is a Wolstenholme prime when `C := C(2p−1, p−1) ≡ 1 (mod p⁴)`.

## Part I: `C − 1 ≡ 2p·H_{p−1} (mod p⁴)`, hence `wolstenholme_harmonic`

**Lemma 1 (power sums; `harmonic_sum_pow_mod`).** If `p − 1 ∤ j`, then `S_j ≡ 0 (mod p)`.

*Proof.* Modulo `p`, the map `k ↦ k⁻¹` permutes `(ℤ/p)ˣ`, so `S_j ≡ Σ_{u ∈ (ℤ/p)ˣ} u^j`. Let `g` be
a generator of `(ℤ/p)ˣ`. Since `p − 1 ∤ j`, we have `g^j ≠ 1`. Multiplying the sum by `g^j` only
permutes its terms, so `(g^j − 1)·Σ u^j = 0`, and therefore `Σ u^j = 0`. ∎

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

## Part II: `p⁴ ∣ C − 1 ⇔ p ∣ num(B_{p−3})`, hence `wolstenholme_bernoulli`

**Step 0 (from Lemma 5).** Reducing Lemma 5 from `ℤ/p⁴` to `ℤ/p³` gives `2S₁ + p·S₂ ≡ 0 (mod p³)`.
Hence

    S₁ ≡ 0 (mod p³)  ⇔  p·S₂ ≡ 0 (mod p³)  ⇔  S₂ ≡ 0 (mod p²),

that is, `p³ ∣ num(H_{p−1})` if and only if `p² ∣ num(H_{p−1,2})`.

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

Because `2` is invertible mod `p`, the map `k ↦ r_k` permutes `1, …, p−1` (`sum_range_double`).
So any sum of `g(k)` over `k` equals the sum of `g(r_k)`. Apply this to two choices of `g`,
working in `ℤ/p²`:

1. **`g(k) = k⁻²`.** From `r_k = 2k − p·f_k` we get
   `1/r_k = (1/(2k))·(1 + p·f_k/(2k))`, hence

       4/r_k² = 1/k² + p·f_k/k³                         (`inv_sq_double`)

   Summing over `k`: `4S₂ = S₂ + p·F`, where `F = Σ f_k/k³`. Therefore

       3·S₂ ≡ p·F  (mod p²).                                              (B1)

2. **`g(k) = k^{p−3}`.** Since `(p·f_k)² = 0`, the binomial expansion stops after two terms:

       r_k^{p−3} = (2k)^{p−3} − (p−3)·(2k)^{p−4}·p·f_k        (`pow_double`)

   Summing over `k`, with `G = Σ f_k·k^{p−4}`:

       T = 2^{p−3}·T − (p−3)·2^{p−4}·p·G.

   Multiply by 8 and use three facts, each a consequence of Fermat's little theorem:
   - `p·2^{p−1} ≡ p`;
   - `T ≡ 0 (mod p)` (Lemma 1, applied to the units), so `2^{p−1}·T ≡ T`;
   - `p·k^{p−4} ≡ p·k^{−3}`, so `p·G ≡ p·F`.
   
   Together with `(p−3)·p ≡ −3p`, this gives `8T ≡ 2T + 3p·F`, that is, `6T ≡ 3p·F`. Cancelling
   the unit `3`:

       2·T ≡ p·F  (mod p²).                                               (B2)

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

- Steps A and B together recover Glaisher's congruence `H_{p−1,2} ≡ (2/3)·p·B_{p−3} (mod p²)`.
  The weighted sum `F = Σ ⌊2k/p⌋/k³` is of the Voronoi–Lerch type. From (B1) one also gets the
  classical `F ≡ 2B_{p−3} (mod p)`.
- Every step works in `ℤ/pⁿ`, and rationals enter only through the reduction map. This is why
  the Lean file separates a generic layer for reducing rationals from the number theory.
